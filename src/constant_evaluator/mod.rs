use std::collections::HashMap;

use crate::analyzer::{Analyzed, BinaryOperator, ConstantNumberType, Expression, UnaryOperator};

/// Generates the constant polynomial values for all constant polynomials
/// that are defined (and not just declared).
/// @returns the values (in source order) and the degree of the polynomials.
pub fn generate(
    analyzed: &Analyzed,
) -> (Vec<(&String, Vec<ConstantNumberType>)>, ConstantNumberType) {
    let mut degree = None;
    let mut other_constants = HashMap::new();
    for (poly, value) in analyzed.constant_polys_in_source_order() {
        if let Some(value) = value {
            if let Some(degree) = degree {
                assert!(degree == poly.degree);
            } else {
                degree = Some(poly.degree);
            }
            let values = generate_values(analyzed, poly.degree, value, &other_constants);
            other_constants.insert(&poly.absolute_name, values);
        }
    }
    let mut values = Vec::new();
    for (poly, _) in analyzed.constant_polys_in_source_order() {
        if let Some(v) = other_constants.get_mut(&poly.absolute_name) {
            values.push((&poly.absolute_name, std::mem::take(v)));
        };
    }
    (values, degree.unwrap_or_default())
}

fn generate_values(
    analyzed: &Analyzed,
    degree: ConstantNumberType,
    body: &Expression,
    other_constants: &HashMap<&String, Vec<ConstantNumberType>>,
) -> Vec<ConstantNumberType> {
    (0..degree)
        .map(|i| {
            Evaluator {
                analyzed,
                variables: &[i],
                other_constants,
            }
            .evaluate(body)
        })
        .collect()
}

struct Evaluator<'a> {
    analyzed: &'a Analyzed,
    other_constants: &'a HashMap<&'a String, Vec<ConstantNumberType>>,
    variables: &'a [ConstantNumberType],
}

impl<'a> Evaluator<'a> {
    fn evaluate(&self, expr: &Expression) -> ConstantNumberType {
        match expr {
            Expression::Constant(name) => self.analyzed.constants[name],
            Expression::PolynomialReference(_) => todo!(),
            Expression::LocalVariableReference(i) => self.variables[*i as usize],
            Expression::PublicReference(_) => todo!(),
            Expression::Number(n) => *n,
            Expression::BinaryOperation(left, op, right) => {
                self.evaluate_binary_operation(left, op, right)
            }
            Expression::UnaryOperation(op, expr) => self.evaluate_unary_operation(op, expr),
            Expression::FunctionCall(name, args) => {
                let arg_values = args.iter().map(|a| self.evaluate(a)).collect::<Vec<_>>();
                assert!(arg_values.len() == 1);
                self.other_constants[name][arg_values[0] as usize]
            }
        }
    }

    fn evaluate_binary_operation(
        &self,
        left: &Expression,
        op: &BinaryOperator,
        right: &Expression,
    ) -> ConstantNumberType {
        let left = self.evaluate(left);
        let right = self.evaluate(right);
        match op {
            BinaryOperator::Add => left + right,
            BinaryOperator::Sub => left - right,
            BinaryOperator::Mul => left * right,
            BinaryOperator::Div => {
                if left == 0 {
                    0
                } else {
                    left / right
                }
            }
            BinaryOperator::Pow => {
                assert!(right <= u32::MAX.into());
                left.pow(right as u32)
            }
            BinaryOperator::Mod => left % right,
            BinaryOperator::BinaryAnd => left & right,
            BinaryOperator::BinaryOr => left | right,
            BinaryOperator::ShiftLeft => left << right,
            BinaryOperator::ShiftRight => left >> right,
        }
    }

    fn evaluate_unary_operation(
        &self,
        op: &UnaryOperator,
        expr: &Expression,
    ) -> ConstantNumberType {
        let v = self.evaluate(expr);
        match op {
            UnaryOperator::Plus => v,
            UnaryOperator::Minus => -v,
        }
    }
}

#[cfg(test)]
mod test {
    use crate::analyzer::analyze_string;

    use super::generate;

    #[test]
    pub fn test_last() {
        let src = r#"
            constant %N = 8;
            namespace F(%N);
            pol constant LAST(i) { 1 - (i - (%N - 1)) / (i - (%N - 1)) };
        "#;
        let analyzed = analyze_string(src);
        let (constants, degree) = generate(&analyzed);
        assert_eq!(degree, 8);
        assert_eq!(
            constants,
            vec![(&"F.LAST".to_string(), vec![0, 0, 0, 0, 0, 0, 0, 1])]
        );
    }

    #[test]
    pub fn test_counter() {
        let src = r#"
            constant %N = 8;
            namespace F(%N);
            pol constant EVEN(i) { 2 * (i - 1) };
        "#;
        let analyzed = analyze_string(src);
        let (constants, degree) = generate(&analyzed);
        assert_eq!(degree, 8);
        assert_eq!(
            constants,
            vec![(&"F.EVEN".to_string(), vec![-2, 0, 2, 4, 6, 8, 10, 12])]
        );
    }

    #[test]
    pub fn test_macro() {
        let src = r#"
            constant %N = 8;
            namespace F(%N);
            macro minus_one(X) { X - 1 };
            pol constant EVEN(i) { 2 * minus_one(i) };
        "#;
        let analyzed = analyze_string(src);
        let (constants, degree) = generate(&analyzed);
        assert_eq!(degree, 8);
        assert_eq!(
            constants,
            vec![(&"F.EVEN".to_string(), vec![-2, 0, 2, 4, 6, 8, 10, 12])]
        );
    }

    #[test]
    pub fn test_macro_double() {
        let src = r#"
            constant %N = 12;
            namespace F(%N);
            macro is_nonzero(X) { X / X };
            macro is_zero(X) { 1 - is_nonzero(X) };
            macro is_one(X) { is_zero(1 - X) };
            macro is_equal(A, B) { is_zero(A - B) };
            macro ite(C, T, F) { is_one(C) * T + is_zero(C) * F };
            pol constant TEN(i) { ite(is_equal(i, 10), 1, 0) };
        "#;
        let analyzed = analyze_string(src);
        let (constants, degree) = generate(&analyzed);
        assert_eq!(degree, 12);
        assert_eq!(
            constants,
            vec![(
                &"F.TEN".to_string(),
                [[0; 10].to_vec(), [1, 0].to_vec()].concat()
            )]
        );
    }

    #[test]
    pub fn test_poly_call() {
        let src = r#"
            constant %N = 10;
            namespace F(%N);
            col fixed seq(i) { i };
            col fixed doub(i) { seq((2 * i) % %N) + 1 };
            col fixed half_nibble(i) { i & 0x7 };
            col fixed doubled_half_nibble(i) { half_nibble(i / 2) };
        "#;
        let analyzed = analyze_string(src);
        let (constants, degree) = generate(&analyzed);
        assert_eq!(degree, 10);
        assert_eq!(constants.len(), 4);
        assert_eq!(
            constants[0],
            (&"F.seq".to_string(), (0..=9i128).collect::<Vec<_>>())
        );
        assert_eq!(
            constants[1],
            (
                &"F.doub".to_string(),
                [1i128, 3, 5, 7, 9, 1, 3, 5, 7, 9].to_vec()
            )
        );
        assert_eq!(
            constants[2],
            (
                &"F.half_nibble".to_string(),
                [0i128, 1, 2, 3, 4, 5, 6, 7, 0, 1].to_vec()
            )
        );
        assert_eq!(
            constants[3],
            (
                &"F.doubled_half_nibble".to_string(),
                [0i128, 0, 1, 1, 2, 2, 3, 3, 4, 4].to_vec()
            )
        );
    }
}
