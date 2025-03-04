//! Generate one ROM per machine from all declared functions

use std::{collections::HashMap, iter::repeat, ops::ControlFlow};

use ast::{
    asm_analysis::{
        utils::{previsit_expression_in_statement_mut, previsit_expression_mut},
        Batch, FunctionStatement, Incompatible, IncompatibleSet, Machine, PilBlock, Rom,
    },
    parsed::{
        asm::{Param, ParamList},
        Expression,
    },
};
use number::FieldElement;

use crate::{
    common::{input_at, instruction_flag, output_at, RESET_NAME, RETURN_NAME},
    utils::{
        parse_function_statement, parse_instruction_definition, parse_pil_statement,
        parse_register_declaration,
    },
};

/// Substitute all visited columns inside expressions of `s`
/// This *only* applies to expressions, so for example identifiers in the left hand side of statements are not substituted
/// This is fine in this case since inputs are only present in expressions
fn substitute_name_in_statement_expressions<T>(
    s: &mut FunctionStatement<T>,
    substitution: &HashMap<String, String>,
) -> ControlFlow<()> {
    fn substitute<T>(
        e: &mut Expression<T>,
        substitution: &HashMap<String, String>,
    ) -> ControlFlow<()> {
        previsit_expression_mut(e, &mut |e| {
            if let Expression::PolynomialReference(r) = e {
                if let Some(v) = substitution.get(r.name()).cloned() {
                    *r.name_mut() = v;
                }
            };
            ControlFlow::Continue::<()>(())
        });
        ControlFlow::Continue(())
    }

    previsit_expression_in_statement_mut(s, &mut |e| substitute(e, substitution))
}

/// Pad the arguments in the `return` statements with zeroes to match the maximum number of outputs
fn pad_return_arguments<T: FieldElement>(s: &mut FunctionStatement<T>, output_count: usize) {
    if let FunctionStatement::Return(ret) = s {
        ret.values = std::mem::take(&mut ret.values)
            .into_iter()
            .chain(repeat(Expression::Number(T::from(0))))
            .take(output_count)
            .collect();
    };
}

pub fn generate_machine_rom<T: FieldElement>(
    mut machine: Machine<T>,
) -> (Machine<T>, Option<Rom<T>>) {
    if !machine.has_pc() {
        // do nothing, there is no rom to be generated
        (machine, None)
    } else {
        let function_id = "_function_id";

        let pc = machine.pc().unwrap();

        // add the necessary embedded instructions
        let embedded_instructions = [
            parse_instruction_definition(&format!(
                "instr _jump_to_operation {{ {pc}' = {function_id} }}",
            )),
            parse_instruction_definition(&format!(
                "instr {RESET_NAME} {{ {} }}",
                machine
                    .write_registers()
                    .map(|r| format!("{}' = 0", r.name))
                    .collect::<Vec<_>>()
                    .join(", ")
            )),
            parse_instruction_definition(&format!("instr _loop {{ {pc}' = {pc} }}")),
        ];

        machine.instructions.extend(embedded_instructions);

        // generate the rom
        // the functions are already batched, we just batch the dispatcher manually here

        let mut rom: Vec<Batch<T>> = vec![];

        // add the beginning of the dispatcher
        rom.extend(vec![
            Batch::from(vec![
                parse_function_statement("_start::"),
                parse_function_statement(&format!("{RESET_NAME};")),
            ])
            .reason(IncompatibleSet::from(Incompatible::Unimplemented)),
            Batch::from(vec![parse_function_statement("_jump_to_operation;")])
                .reason(IncompatibleSet::from(Incompatible::Label)),
        ]);

        // the number of inputs is the max of the number of inputs needed in each function
        let input_count = machine
            .functions
            .iter()
            .map(|o| o.params.inputs.params.len())
            .max()
            .unwrap_or(0);
        let output_count = machine
            .functions
            .iter()
            .map(|o| {
                o.params
                    .outputs
                    .as_ref()
                    .map(|o| o.params.len())
                    .unwrap_or(0)
            })
            .max()
            .unwrap_or(0);
        // create one read-only register for each input
        let input_assignment_registers_declarations = (0..input_count)
            .map(|i| parse_register_declaration::<T>(&format!("reg {}[@r];", input_at(i))));

        // create one assignment register for each output
        let output_assignment_registers_declarations = (0..output_count)
            .map(|i| parse_register_declaration::<T>(&format!("reg {}[<=];", output_at(i))));

        machine.registers.extend(
            input_assignment_registers_declarations.chain(output_assignment_registers_declarations),
        );

        // add each function, setting the function_id to the current position in the ROM
        for function in machine.functions.iter_mut() {
            function.id = Some(T::from(rom.len() as u64));

            // create substitution map from declared input to the hidden witness columns
            let input_substitution = function
                .params
                .inputs
                .params
                .iter()
                .enumerate()
                .map(|(index, param)| (param.name.clone(), input_at(index)))
                .collect();

            function.params.inputs.params = function
                .params
                .inputs
                .params
                .iter()
                .enumerate()
                .map(|(i, _)| Param {
                    name: input_at(i),
                    ty: None,
                })
                .collect();
            function.params.outputs = function.params.outputs.clone().map(|outputs| ParamList {
                params: outputs
                    .params
                    .into_iter()
                    .enumerate()
                    .map(|(i, _)| Param {
                        name: output_at(i),
                        ty: None,
                    })
                    .collect(),
            });

            // substitute the names in the operation body and extend the return arguments
            for s in function.body.statements.iter_mut() {
                substitute_name_in_statement_expressions(s, &input_substitution);
                pad_return_arguments(s, output_count);
            }

            let mut batches: Vec<_> = std::mem::take(&mut function.body.statements)
                .into_iter_batches()
                .collect();
            // modify the first batch to include the label just for debugging purposes, it's always possible to batch it so it's free
            batches
                .first_mut()
                .expect("function should have at least one statement as it must return")
                .statements
                .insert(
                    0,
                    parse_function_statement(&format!("_{}::", function.name)),
                );

            // modify the last batch to be caused by the coming label
            let last = batches
                .last_mut()
                .expect("function should have at least one statement as it must return");
            last.set_reason(IncompatibleSet::from(Incompatible::Label));

            rom.extend(batches);
        }

        // add the sink which can be used to fill the rest of the table
        let sink_id = T::from(rom.len() as u64);

        rom.extend(vec![Batch::from(vec![
            parse_function_statement("_sink::"),
            parse_function_statement("_loop;"),
        ])]);

        // TODO: the following is necessary because of witgen, it can be removed once witgen can call the infinite loop itself
        // we get the location of the sink so that witgen jumps to it after the first call is done
        // this constrains the VM to being able to execute only one call, which will be fixed in the future
        let latch = instruction_flag(RETURN_NAME);
        let sigma = "_sigma";
        let first_step = "_romgen_first_step";

        machine.constraints.push(PilBlock {
            start: 0,
            statements: vec![
                // inject the function_id
                parse_pil_statement(&format!("col witness {function_id}")),
                // declare `_sigma` as the sum of the latch, will be 0 and then 1 after the end of the first call
                parse_pil_statement(&format!("col witness {sigma}")),
                parse_pil_statement(&format!("col fixed {first_step} = [1] + [0]*")),
                parse_pil_statement(&format!(
                    "{sigma}' = (1 - {first_step}') * ({sigma} + {latch})"
                )),
                // once `_sigma` is 1, constrain `_function_id` to the label of the sink
                parse_pil_statement(&format!("{sigma} * ({function_id} - {sink_id}) = 0")),
            ],
        });
        ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

        machine.function_id = Some(function_id.into());

        (
            machine,
            Some(Rom {
                statements: rom.into_iter().collect(),
            }),
        )
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use number::Bn254Field;
    use pretty_assertions::assert_eq;

    // generate the rom from source. Note that only type checking is applied before this.
    fn generate_rom_str<T: FieldElement>(
        src: &str,
    ) -> BTreeMap<String, (Machine<T>, Option<Rom<T>>)> {
        let parsed = parser::parse_asm(None, src).unwrap();
        let checked = type_check::check(parsed).unwrap();
        checked
            .machines
            .into_iter()
            .map(|(name, m)| (name, generate_machine_rom(m)))
            .collect()
    }

    use super::*;

    #[test]
    fn empty() {
        let vm = r#"
            machine VM {
                reg pc[@pc];
            }
        "#;

        let res = generate_rom_str::<Bn254Field>(vm);

        assert_eq!(
            res.get("VM")
                .unwrap()
                .1
                .as_ref()
                .unwrap()
                .statements
                .to_string()
                .replace('\t', "    "),
            r#"
_start::
_reset;
// END BATCH Unimplemented
_jump_to_operation;
// END BATCH Label
_sink::
_loop;
// END BATCH
"#
            .replace('\t', "    ")
            .trim()
        );
    }

    #[test]
    fn identity() {
        let vm = r#"
            machine VM {
                reg pc[@pc];

                function identity x: field -> field {
                    return x;
                }
            }
        "#;

        let res = generate_rom_str::<Bn254Field>(vm);

        assert_eq!(
            res.get("VM")
                .unwrap()
                .1
                .as_ref()
                .unwrap()
                .statements
                .to_string()
                .replace('\t', "    "),
            r#"
_start::
_reset;
// END BATCH Unimplemented
_jump_to_operation;
// END BATCH Label
_identity::
return _input_0;
// END BATCH Label
_sink::
_loop;
// END BATCH
"#
            .replace('\t', "    ")
            .trim()
        );
    }

    #[test]
    fn vm() {
        let vm = r#"
            machine VM {

                reg pc[@pc];
                reg X[<=];
                reg Y[<=];
                reg Z[<=];
                reg A;
                reg B;

                instr assert_zero X {
                    X = 0
                }

                instr add X, Y -> Z { X + Y = Z }

                function f_add x: field, y: field -> field {
                    A <=Z= add(x, y);
                    return A;
                }

                function f_assert_zero x: field {
                    assert_zero x;
                    return;
                }
            }
        "#;

        let res = generate_rom_str::<Bn254Field>(vm);

        assert_eq!(
            res.get("VM")
                .unwrap()
                .1
                .as_ref()
                .unwrap()
                .statements
                .to_string()
                .replace('\t', "    "),
            r#"
_start::
_reset;
// END BATCH Unimplemented
_jump_to_operation;
// END BATCH Label
_f_add::
A <=Z= add(_input_0, _input_1);
// END BATCH
return A;
// END BATCH Label
_f_assert_zero::
assert_zero _input_0;
// END BATCH
return 0;
// END BATCH Label
_sink::
_loop;
// END BATCH
"#
            .replace('\t', "    ")
            .trim()
        );
    }
}
