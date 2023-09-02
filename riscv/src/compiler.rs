use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
};

use asm_utils::{
    ast::{BinaryOpKind, UnaryOpKind},
    data_parser::{self, DataValue},
    parser::parse_asm,
    reachability,
};
use itertools::Itertools;

use crate::disambiguator;
use crate::parser::RiscParser;
use crate::{Argument, Expression, Statement};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Register {
    value: u8,
}

pub fn machine_decls() -> Vec<&'static str> {
    vec![
        r#"
// ================= binary/bitwise instructions =================

machine Binary(latch, function_id) {

    degree 262144;

    function and<0> A, B -> C {
    }

    function or<1> A, B -> C {
    }

    function xor<2> A, B -> C {
    }

    constraints{
        col witness function_id;

        macro is_nonzero(X) { match X { 0 => 0, _ => 1, } };
        macro is_zero(X) { 1 - is_nonzero(X) };

        col fixed latch(i) { is_zero((i % 4) - 3) };
        col fixed FACTOR(i) { 1 << (((i + 1) % 4) * 8) };

        col fixed P_A(i) { i % 256 };
        col fixed P_B(i) { (i >> 8) % 256 };
        col fixed P_operation(i) { (i / (256 * 256)) % 3 };
        col fixed P_C(i) {
            match P_operation(i) {
                0 => P_A(i) & P_B(i),
                1 => P_A(i) | P_B(i),
                2 => P_A(i) ^ P_B(i),
            } & 0xff
        };

        col witness A_byte;
        col witness B_byte;
        col witness C_byte;

        col witness A;
        col witness B;
        col witness C;

        A' = A * (1 - latch) + A_byte * FACTOR;
        B' = B * (1 - latch) + B_byte * FACTOR;
        C' = C * (1 - latch) + C_byte * FACTOR;

        {function_id', A_byte, B_byte, C_byte} in {P_operation, P_A, P_B, P_C};
    }
}
"#,
        r#"
// ================= shift instructions =================

machine Shift(latch, function_id) {
    degree 262144;

    function shl<0> A, B -> C {
    }

    function shr<1> A, B -> C {
    }

    constraints{
        col witness function_id;

        col fixed latch(i) { is_zero((i % 4) - 3) };
        col fixed FACTOR_ROW(i) { (i + 1) % 4 };
        col fixed FACTOR(i) { 1 << (((i + 1) % 4) * 8) };

        col fixed P_A(i) { i % 256 };
        col fixed P_B(i) { (i / 256) % 32 };
        col fixed P_ROW(i) { (i / (256 * 32)) % 4 };
        col fixed P_operation(i) { (i / (256 * 32 * 4)) % 2 };
        col fixed P_C(i) {
            match P_operation(i) {
                0 => (P_A(i) << (P_B(i) + (P_ROW(i) * 8))),
                1 => (P_A(i) << (P_ROW(i) * 8)) >> P_B(i),
            } & 0xffffffff
        };

        col witness A_byte;
        col witness C_part;

        col witness A;
        col witness B;
        col witness C;

        A' = A * (1 - latch) + A_byte * FACTOR;
        (B' - B) * (1 - latch) = 0;
        C' = C * (1 - latch) + C_part;

        // TODO this way, we cannot prove anything that shifts by more than 31 bits.
        {function_id', A_byte, B', FACTOR_ROW, C_part} in {P_operation, P_A, P_B, P_ROW, P_C};
    }
}
"#,
        r#"
// ================= bls_arith instructions =================
// Implements the Arith for BLS12_381 curve.
//
// This code was extracted from: https://github.com/puma314/blspil/blob/main/pil
// and adapted to powdr-pil.

machine BLS12_381(latch, function_id) {

	degree 65536;

	function arith<0> a_0, a_1, a_2, a_3, a_4, a_5,
						a_6, a_7, a_8, a_9, a_10, a_11,
						a_12, a_13, a_14, a_15, a_16, a_17,
						a_18, a_19, a_20, a_21, a_22, a_23,
						b_0, b_1, b_2, b_3, b_4, b_5,
						b_6, b_7, b_8, b_9, b_10, b_11,
						b_12, b_13, b_14, b_15, b_16, b_17,
						b_18, b_19, b_20, b_21, b_22, b_23,
						c_0, c_1, c_2, c_3, c_4, c_5,
						c_6, c_7, c_8, c_9, c_10, c_11,
						c_12, c_13, c_14, c_15, c_16, c_17,
						c_18, c_19, c_20, c_21, c_22, c_23,
						d_0, d_1, d_2, d_3, d_4, d_5,
						d_6, d_7, d_8, d_9, d_10, d_11,
						d_12, d_13, d_14, d_15, d_16, d_17,
						d_18, d_19, d_20, d_21, d_22, d_23,
						e_0, e_1, e_2, e_3, e_4, e_5,
						e_6, e_7, e_8, e_9, e_10, e_11,
						e_12, e_13, e_14, e_15, e_16, e_17,
						e_18, e_19, e_20, e_21, e_22, e_23 -> eq {
	}

	constraints {
		col witness function_id;
		col fixed latch = [1]*;

		/*
			Equations:
			EQ: a * b + c = d * P + e
		*/
		col fixed BYTE2(i) { i & 0xffff };
		// 1 if CLK==0 and 0 if CLK!=0
		col fixed CLK_0 = [1] + [0]*;
		col fixed CLK_1 = [1] + [0]*;
		col fixed CLK_2 = [1] + [0]*;
		col fixed CLK_3 = [1] + [0]*;
		col fixed CLK_4 = [1] + [0]*;
		col fixed CLK_5 = [1] + [0]*;
		col fixed CLK_6 = [1] + [0]*;
		col fixed CLK_7 = [1] + [0]*;
		col fixed CLK_8 = [1] + [0]*;
		col fixed CLK_9 = [1] + [0]*;
		col fixed CLK_10 = [1] + [0]*;
		col fixed CLK_11 = [1] + [0]*;
		col fixed CLK_12 = [1] + [0]*;
		col fixed CLK_13 = [1] + [0]*;
		col fixed CLK_14 = [1] + [0]*;
		col fixed CLK_15 = [1] + [0]*;
		col fixed CLK_16 = [1] + [0]*;
		col fixed CLK_17 = [1] + [0]*;
		col fixed CLK_18 = [1] + [0]*;
		col fixed CLK_19 = [1] + [0]*;
		col fixed CLK_20 = [1] + [0]*;
		col fixed CLK_21 = [1] + [0]*;
		col fixed CLK_22 = [1] + [0]*;
		col fixed CLK_23 = [1] + [0]*;
		col fixed CLK_24 = [1] + [0]*;
		col fixed CLK_25 = [1] + [0]*;
		col fixed CLK_26 = [1] + [0]*;
		col fixed CLK_27 = [1] + [0]*;
		col fixed CLK_28 = [1] + [0]*;
		col fixed CLK_29 = [1] + [0]*;
		col fixed CLK_30 = [1] + [0]*;
		col fixed CLK_31 = [1] + [0]*;
		col fixed CLK_32 = [1] + [0]*;
		col fixed CLK_33 = [1] + [0]*;
		col fixed CLK_34 = [1] + [0]*;
		col fixed CLK_35 = [1] + [0]*;
		col fixed CLK_36 = [1] + [0]*;
		col fixed CLK_37 = [1] + [0]*;
		col fixed CLK_38 = [1] + [0]*;
		col fixed CLK_39 = [1] + [0]*;
		col fixed CLK_40 = [1] + [0]*;
		col fixed CLK_41 = [1] + [0]*;
		col fixed CLK_42 = [1] + [0]*;
		col fixed CLK_43 = [1] + [0]*;
		col fixed CLK_44 = [1] + [0]*;
		col fixed CLK_45 = [1] + [0]*;
		col fixed CLK_46 = [1] + [0]*;
		col fixed CLK_47 = [1] + [0]*;

		/*
		pol commit a[24];
		pol commit b[24];
		pol commit c[24];
		pol commit d[24];
		pol commit e[24];
		*/
		pol commit a_0;
		pol commit a_1;
		pol commit a_2;
		pol commit a_3;
		pol commit a_4;
		pol commit a_5;
		pol commit a_6;
		pol commit a_7;
		pol commit a_8;
		pol commit a_9;
		pol commit a_10;
		pol commit a_11;
		pol commit a_12;
		pol commit a_13;
		pol commit a_14;
		pol commit a_15;
		pol commit a_16;
		pol commit a_17;
		pol commit a_18;
		pol commit a_19;
		pol commit a_20;
		pol commit a_21;
		pol commit a_22;
		pol commit a_23;

		pol commit b_0;
		pol commit b_1;
		pol commit b_2;
		pol commit b_3;
		pol commit b_4;
		pol commit b_5;
		pol commit b_6;
		pol commit b_7;
		pol commit b_8;
		pol commit b_9;
		pol commit b_10;
		pol commit b_11;
		pol commit b_12;
		pol commit b_13;
		pol commit b_14;
		pol commit b_15;
		pol commit b_16;
		pol commit b_17;
		pol commit b_18;
		pol commit b_19;
		pol commit b_20;
		pol commit b_21;
		pol commit b_22;
		pol commit b_23;

		pol commit c_0;
		pol commit c_1;
		pol commit c_2;
		pol commit c_3;
		pol commit c_4;
		pol commit c_5;
		pol commit c_6;
		pol commit c_7;
		pol commit c_8;
		pol commit c_9;
		pol commit c_10;
		pol commit c_11;
		pol commit c_12;
		pol commit c_13;
		pol commit c_14;
		pol commit c_15;
		pol commit c_16;
		pol commit c_17;
		pol commit c_18;
		pol commit c_19;
		pol commit c_20;
		pol commit c_21;
		pol commit c_22;
		pol commit c_23;

		pol commit d_0;
		pol commit d_1;
		pol commit d_2;
		pol commit d_3;
		pol commit d_4;
		pol commit d_5;
		pol commit d_6;
		pol commit d_7;
		pol commit d_8;
		pol commit d_9;
		pol commit d_10;
		pol commit d_11;
		pol commit d_12;
		pol commit d_13;
		pol commit d_14;
		pol commit d_15;
		pol commit d_16;
		pol commit d_17;
		pol commit d_18;
		pol commit d_19;
		pol commit d_20;
		pol commit d_21;
		pol commit d_22;
		pol commit d_23;

		pol commit e_0;
		pol commit e_1;
		pol commit e_2;
		pol commit e_3;
		pol commit e_4;
		pol commit e_5;
		pol commit e_6;
		pol commit e_7;
		pol commit e_8;
		pol commit e_9;
		pol commit e_10;
		pol commit e_11;
		pol commit e_12;
		pol commit e_13;
		pol commit e_14;
		pol commit e_15;
		pol commit e_16;
		pol commit e_17;
		pol commit e_18;
		pol commit e_19;
		pol commit e_20;
		pol commit e_21;
		pol commit e_22;
		pol commit e_23;

		/****
		* LATCH POLS: a,b,c,d,e
		*****/
		a_0' * (1-CLK_47) = a_0 * (1-CLK_47);
		a_1' * (1-CLK_47) = a_1 * (1-CLK_47);
		a_2' * (1-CLK_47) = a_2 * (1-CLK_47);
		a_3' * (1-CLK_47) = a_3 * (1-CLK_47);
		a_4' * (1-CLK_47) = a_4 * (1-CLK_47);
		a_5' * (1-CLK_47) = a_5 * (1-CLK_47);
		a_6' * (1-CLK_47) = a_6 * (1-CLK_47);
		a_7' * (1-CLK_47) = a_7 * (1-CLK_47);
		a_8' * (1-CLK_47) = a_8 * (1-CLK_47);
		a_9' * (1-CLK_47) = a_9 * (1-CLK_47);
		a_10' * (1-CLK_47) = a_10 * (1-CLK_47);
		a_11' * (1-CLK_47) = a_11 * (1-CLK_47);
		a_12' * (1-CLK_47) = a_12 * (1-CLK_47);
		a_13' * (1-CLK_47) = a_13 * (1-CLK_47);
		a_14' * (1-CLK_47) = a_14 * (1-CLK_47);
		a_15' * (1-CLK_47) = a_15 * (1-CLK_47);
		a_16' * (1-CLK_47) = a_16 * (1-CLK_47);
		a_17' * (1-CLK_47) = a_17 * (1-CLK_47);
		a_18' * (1-CLK_47) = a_18 * (1-CLK_47);
		a_19' * (1-CLK_47) = a_19 * (1-CLK_47);
		a_20' * (1-CLK_47) = a_20 * (1-CLK_47);
		a_21' * (1-CLK_47) = a_21 * (1-CLK_47);
		a_22' * (1-CLK_47) = a_22 * (1-CLK_47);
		a_23' * (1-CLK_47) = a_23 * (1-CLK_47);

		b_0' * (1-CLK_47) = b_0 * (1-CLK_47);
		b_1' * (1-CLK_47) = b_1 * (1-CLK_47);
		b_2' * (1-CLK_47) = b_2 * (1-CLK_47);
		b_3' * (1-CLK_47) = b_3 * (1-CLK_47);
		b_4' * (1-CLK_47) = b_4 * (1-CLK_47);
		b_5' * (1-CLK_47) = b_5 * (1-CLK_47);
		b_6' * (1-CLK_47) = b_6 * (1-CLK_47);
		b_7' * (1-CLK_47) = b_7 * (1-CLK_47);
		b_8' * (1-CLK_47) = b_8 * (1-CLK_47);
		b_9' * (1-CLK_47) = b_9 * (1-CLK_47);
		b_10' * (1-CLK_47) = b_10 * (1-CLK_47);
		b_11' * (1-CLK_47) = b_11 * (1-CLK_47);
		b_12' * (1-CLK_47) = b_12 * (1-CLK_47);
		b_13' * (1-CLK_47) = b_13 * (1-CLK_47);
		b_14' * (1-CLK_47) = b_14 * (1-CLK_47);
		b_15' * (1-CLK_47) = b_15 * (1-CLK_47);
		b_16' * (1-CLK_47) = b_16 * (1-CLK_47);
		b_17' * (1-CLK_47) = b_17 * (1-CLK_47);
		b_18' * (1-CLK_47) = b_18 * (1-CLK_47);
		b_19' * (1-CLK_47) = b_19 * (1-CLK_47);
		b_20' * (1-CLK_47) = b_20 * (1-CLK_47);
		b_21' * (1-CLK_47) = b_21 * (1-CLK_47);
		b_22' * (1-CLK_47) = b_22 * (1-CLK_47);
		b_23' * (1-CLK_47) = b_23 * (1-CLK_47);

		c_0' * (1-CLK_47) = c_0 * (1-CLK_47);
		c_1' * (1-CLK_47) = c_1 * (1-CLK_47);
		c_2' * (1-CLK_47) = c_2 * (1-CLK_47);
		c_3' * (1-CLK_47) = c_3 * (1-CLK_47);
		c_4' * (1-CLK_47) = c_4 * (1-CLK_47);
		c_5' * (1-CLK_47) = c_5 * (1-CLK_47);
		c_6' * (1-CLK_47) = c_6 * (1-CLK_47);
		c_7' * (1-CLK_47) = c_7 * (1-CLK_47);
		c_8' * (1-CLK_47) = c_8 * (1-CLK_47);
		c_9' * (1-CLK_47) = c_9 * (1-CLK_47);
		c_10' * (1-CLK_47) = c_10 * (1-CLK_47);
		c_11' * (1-CLK_47) = c_11 * (1-CLK_47);
		c_12' * (1-CLK_47) = c_12 * (1-CLK_47);
		c_13' * (1-CLK_47) = c_13 * (1-CLK_47);
		c_14' * (1-CLK_47) = c_14 * (1-CLK_47);
		c_15' * (1-CLK_47) = c_15 * (1-CLK_47);
		c_16' * (1-CLK_47) = c_16 * (1-CLK_47);
		c_17' * (1-CLK_47) = c_17 * (1-CLK_47);
		c_18' * (1-CLK_47) = c_18 * (1-CLK_47);
		c_19' * (1-CLK_47) = c_19 * (1-CLK_47);
		c_20' * (1-CLK_47) = c_20 * (1-CLK_47);
		c_21' * (1-CLK_47) = c_21 * (1-CLK_47);
		c_22' * (1-CLK_47) = c_22 * (1-CLK_47);
		c_23' * (1-CLK_47) = c_23 * (1-CLK_47);

		d_0' * (1-CLK_47) = d_0 * (1-CLK_47);
		d_1' * (1-CLK_47) = d_1 * (1-CLK_47);
		d_2' * (1-CLK_47) = d_2 * (1-CLK_47);
		d_3' * (1-CLK_47) = d_3 * (1-CLK_47);
		d_4' * (1-CLK_47) = d_4 * (1-CLK_47);
		d_5' * (1-CLK_47) = d_5 * (1-CLK_47);
		d_6' * (1-CLK_47) = d_6 * (1-CLK_47);
		d_7' * (1-CLK_47) = d_7 * (1-CLK_47);
		d_8' * (1-CLK_47) = d_8 * (1-CLK_47);
		d_9' * (1-CLK_47) = d_9 * (1-CLK_47);
		d_10' * (1-CLK_47) = d_10 * (1-CLK_47);
		d_11' * (1-CLK_47) = d_11 * (1-CLK_47);
		d_12' * (1-CLK_47) = d_12 * (1-CLK_47);
		d_13' * (1-CLK_47) = d_13 * (1-CLK_47);
		d_14' * (1-CLK_47) = d_14 * (1-CLK_47);
		d_15' * (1-CLK_47) = d_15 * (1-CLK_47);
		d_16' * (1-CLK_47) = d_16 * (1-CLK_47);
		d_17' * (1-CLK_47) = d_17 * (1-CLK_47);
		d_18' * (1-CLK_47) = d_18 * (1-CLK_47);
		d_19' * (1-CLK_47) = d_19 * (1-CLK_47);
		d_20' * (1-CLK_47) = d_20 * (1-CLK_47);
		d_21' * (1-CLK_47) = d_21 * (1-CLK_47);
		d_22' * (1-CLK_47) = d_22 * (1-CLK_47);
		d_23' * (1-CLK_47) = d_23 * (1-CLK_47);

		e_0' * (1-CLK_47) = e_0 * (1-CLK_47);
		e_1' * (1-CLK_47) = e_1 * (1-CLK_47);
		e_2' * (1-CLK_47) = e_2 * (1-CLK_47);
		e_3' * (1-CLK_47) = e_3 * (1-CLK_47);
		e_4' * (1-CLK_47) = e_4 * (1-CLK_47);
		e_5' * (1-CLK_47) = e_5 * (1-CLK_47);
		e_6' * (1-CLK_47) = e_6 * (1-CLK_47);
		e_7' * (1-CLK_47) = e_7 * (1-CLK_47);
		e_8' * (1-CLK_47) = e_8 * (1-CLK_47);
		e_9' * (1-CLK_47) = e_9 * (1-CLK_47);
		e_10' * (1-CLK_47) = e_10 * (1-CLK_47);
		e_11' * (1-CLK_47) = e_11 * (1-CLK_47);
		e_12' * (1-CLK_47) = e_12 * (1-CLK_47);
		e_13' * (1-CLK_47) = e_13 * (1-CLK_47);
		e_14' * (1-CLK_47) = e_14 * (1-CLK_47);
		e_15' * (1-CLK_47) = e_15 * (1-CLK_47);
		e_16' * (1-CLK_47) = e_16 * (1-CLK_47);
		e_17' * (1-CLK_47) = e_17 * (1-CLK_47);
		e_18' * (1-CLK_47) = e_18 * (1-CLK_47);
		e_19' * (1-CLK_47) = e_19 * (1-CLK_47);
		e_20' * (1-CLK_47) = e_20 * (1-CLK_47);
		e_21' * (1-CLK_47) = e_21 * (1-CLK_47);
		e_22' * (1-CLK_47) = e_22 * (1-CLK_47);
		e_23' * (1-CLK_47) = e_23 * (1-CLK_47);

		/****
		* RANGE CHECK A,B,C,Q
		*****/
		a_0*CLK_0 + a_1*CLK_1 + a_2*CLK_2 + a_3*CLK_3 + a_4*CLK_4 + a_5*CLK_5 + a_6*CLK_6 + a_7*CLK_7
			+ a_8*CLK_8 + a_9*CLK_9 + a_10*CLK_10 + a_11*CLK_11 + a_12*CLK_12 + a_13*CLK_13 + a_14*CLK_14 + a_15*CLK_15
			+ a_16*CLK_16 + a_17*CLK_17 + a_18*CLK_18 + a_19*CLK_19 + a_20*CLK_20 + a_21*CLK_21 + a_22*CLK_22 + a_23*CLK_23
			+ b_0*CLK_24 + b_1*CLK_25 + b_2*CLK_26 + b_3*CLK_27 + b_4*CLK_28 + b_5*CLK_29 + b_6*CLK_30 + b_7*CLK_31
			+ b_8*CLK_32 + b_9*CLK_33 + b_10*CLK_34 + b_11*CLK_35 + b_12*CLK_36 + b_13*CLK_37 + b_14*CLK_38 + b_15*CLK_39
			+ b_16*CLK_40 + b_17*CLK_41 + b_18*CLK_42 + b_19*CLK_43 + b_20*CLK_44 + b_21*CLK_45 + b_22*CLK_46 + b_23*CLK_47 in BYTE2;
			c_0*CLK_0 + c_1*CLK_1 + c_2*CLK_2 + c_3*CLK_3 + c_4*CLK_4 + c_5*CLK_5 + c_6*CLK_6 + c_7*CLK_7
			+ c_8*CLK_8 + c_9*CLK_9 + c_10*CLK_10 + c_11*CLK_11 + c_12*CLK_12 + c_13*CLK_13 + c_14*CLK_14 + c_15*CLK_15
			+ c_16*CLK_16 + c_17*CLK_17 + c_18*CLK_18 + c_19*CLK_19 + c_20*CLK_20 + c_21*CLK_21 + c_22*CLK_22 + c_23*CLK_23
			+ d_0*CLK_24 + d_1*CLK_25 + d_2*CLK_26 + d_3*CLK_27 + d_4*CLK_28 + d_5*CLK_29 + d_6*CLK_30 + d_7*CLK_31
			+ d_8*CLK_32 + d_9*CLK_33 + d_10*CLK_34 + d_11*CLK_35 + d_12*CLK_36 + d_13*CLK_37 + d_14*CLK_38 + d_15*CLK_39
			+ d_16*CLK_40 + d_17*CLK_41 + d_18*CLK_42 + d_19*CLK_43 + d_20*CLK_44 + d_21*CLK_45 + d_22*CLK_46 + d_23*CLK_47 in BYTE2;
			e_0*CLK_0 + e_1*CLK_1 + e_2*CLK_2 + e_3*CLK_3 + e_4*CLK_4 + e_5*CLK_5 + e_6*CLK_6 + e_7*CLK_7
			+ e_8*CLK_8 + e_9*CLK_9 + e_10*CLK_10 + e_11*CLK_11 + e_12*CLK_12 + e_13*CLK_13 + e_14*CLK_14 + e_15*CLK_15
			+ e_16*CLK_16 + e_17*CLK_17 + e_18*CLK_18 + e_19*CLK_19 + e_20*CLK_20 + e_21*CLK_21 + e_22*CLK_22 + e_23*CLK_23 in BYTE2;

		/*******
		* EQ: A * B + C = D * P + E
		*******/
		/*
		pol eq_0 =
			(a[0] * b[0] - 43691 * d[0])
			+ c[0] - e[0];
		*/
		col witness eq_0;
		col witness eq_1;
		col witness eq_2;
		col witness eq_3;
		col witness eq_4;
		col witness eq_5;
		col witness eq_6;
		col witness eq_7;
		col witness eq_8;
		col witness eq_9;
		col witness eq_10;
		col witness eq_11;
		col witness eq_12;
		col witness eq_13;
		col witness eq_14;
		col witness eq_15;
		col witness eq_16;
		col witness eq_17;
		col witness eq_18;
		col witness eq_19;
		col witness eq_20;
		col witness eq_21;
		col witness eq_22;
		col witness eq_23;
		col witness eq_24;
		col witness eq_25;
		col witness eq_26;
		col witness eq_27;
		col witness eq_28;
		col witness eq_29;
		col witness eq_30;
		col witness eq_31;
		col witness eq_32;
		col witness eq_33;
		col witness eq_34;
		col witness eq_35;
		col witness eq_36;
		col witness eq_37;
		col witness eq_38;
		col witness eq_39;
		col witness eq_40;
		col witness eq_41;
		col witness eq_42;
		col witness eq_43;
		col witness eq_44;
		col witness eq_45;
		col witness eq_46;
		col witness eq_47;

		eq_0 =
			(a_0 * b_0 - 43691 * d_0)
			+ c_0 - e_0;

		eq_1 =
			(a_0 * b_1 - 43691 * d_1) +
			(a_1 * b_0 - 65535 * d_0)
			+ c_1 - e_1;
		eq_2 =
			(a_0 * b_2 - 43691 * d_2) +
			(a_1 * b_1 - 65535 * d_1) +
			(a_2 * b_0 - 65535 * d_0)
			+ c_2 - e_2;
		eq_3 =
			(a_0 * b_3 - 43691 * d_3) +
			(a_1 * b_2 - 65535 * d_2) +
			(a_2 * b_1 - 65535 * d_1) +
			(a_3 * b_0 - 47614 * d_0)
			+ c_3 - e_3;
		eq_4 =
			(a_0 * b_4 - 43691 * d_4) +
			(a_1 * b_3 - 65535 * d_3) +
			(a_2 * b_2 - 65535 * d_2) +
			(a_3 * b_1 - 47614 * d_1) +
			(a_4 * b_0 - 65535 * d_0)
			+ c_4 - e_4;
		eq_5 =
			(a_0 * b_5 - 43691 * d_5) +
			(a_1 * b_4 - 65535 * d_4) +
			(a_2 * b_3 - 65535 * d_3) +
			(a_3 * b_2 - 47614 * d_2) +
			(a_4 * b_1 - 65535 * d_1) +
			(a_5 * b_0 - 45395 * d_0)
			+ c_5 - e_5;
		eq_6 =
			(a_0 * b_6 - 43691 * d_6) +
			(a_1 * b_5 - 65535 * d_5) +
			(a_2 * b_4 - 65535 * d_4) +
			(a_3 * b_3 - 47614 * d_3) +
			(a_4 * b_2 - 65535 * d_2) +
			(a_5 * b_1 - 45395 * d_1) +
			(a_6 * b_0 - 65534 * d_0)
			+ c_6 - e_6;
		eq_7 =
			(a_0 * b_7 - 43691 * d_7) +
			(a_1 * b_6 - 65535 * d_6) +
			(a_2 * b_5 - 65535 * d_5) +
			(a_3 * b_4 - 47614 * d_4) +
			(a_4 * b_3 - 65535 * d_3) +
			(a_5 * b_2 - 45395 * d_2) +
			(a_6 * b_1 - 65534 * d_1) +
			(a_7 * b_0 - 7851 * d_0)
			+ c_7 - e_7;
		eq_8 =
			(a_0 * b_8 - 43691 * d_8) +
			(a_1 * b_7 - 65535 * d_7) +
			(a_2 * b_6 - 65535 * d_6) +
			(a_3 * b_5 - 47614 * d_5) +
			(a_4 * b_4 - 65535 * d_4) +
			(a_5 * b_3 - 45395 * d_3) +
			(a_6 * b_2 - 65534 * d_2) +
			(a_7 * b_1 - 7851 * d_1) +
			(a_8 * b_0 - 63012 * d_0)
			+ c_8 - e_8;
		eq_9 =
			(a_0 * b_9 - 43691 * d_9) +
			(a_1 * b_8 - 65535 * d_8) +
			(a_2 * b_7 - 65535 * d_7) +
			(a_3 * b_6 - 47614 * d_6) +
			(a_4 * b_5 - 65535 * d_5) +
			(a_5 * b_4 - 45395 * d_4) +
			(a_6 * b_3 - 65534 * d_3) +
			(a_7 * b_2 - 7851 * d_2) +
			(a_8 * b_1 - 63012 * d_1) +
			(a_9 * b_0 - 63152 * d_0)
			+ c_9 - e_9;
		eq_10 =
			(a_0 * b_10 - 43691 * d_10) +
			(a_1 * b_9 - 65535 * d_9) +
			(a_2 * b_8 - 65535 * d_8) +
			(a_3 * b_7 - 47614 * d_7) +
			(a_4 * b_6 - 65535 * d_6) +
			(a_5 * b_5 - 45395 * d_5) +
			(a_6 * b_4 - 65534 * d_4) +
			(a_7 * b_3 - 7851 * d_3) +
			(a_8 * b_2 - 63012 * d_2) +
			(a_9 * b_1 - 63152 * d_1) +
			(a_10 * b_0 - 53920 * d_0)
			+ c_10 - e_10;
		eq_11 =
			(a_0 * b_11 - 43691 * d_11) +
			(a_1 * b_10 - 65535 * d_10) +
			(a_2 * b_9 - 65535 * d_9) +
			(a_3 * b_8 - 47614 * d_8) +
			(a_4 * b_7 - 65535 * d_7) +
			(a_5 * b_6 - 45395 * d_6) +
			(a_6 * b_5 - 65534 * d_5) +
			(a_7 * b_4 - 7851 * d_4) +
			(a_8 * b_3 - 63012 * d_3) +
			(a_9 * b_2 - 63152 * d_2) +
			(a_10 * b_1 - 53920 * d_1) +
			(a_11 * b_0 - 26416 * d_0)
			+ c_11 - e_11;
		eq_12 =
			(a_0 * b_12 - 43691 * d_12) +
			(a_1 * b_11 - 65535 * d_11) +
			(a_2 * b_10 - 65535 * d_10) +
			(a_3 * b_9 - 47614 * d_9) +
			(a_4 * b_8 - 65535 * d_8) +
			(a_5 * b_7 - 45395 * d_7) +
			(a_6 * b_6 - 65534 * d_6) +
			(a_7 * b_5 - 7851 * d_5) +
			(a_8 * b_4 - 63012 * d_4) +
			(a_9 * b_3 - 63152 * d_3) +
			(a_10 * b_2 - 53920 * d_2) +
			(a_11 * b_1 - 26416 * d_1) +
			(a_12 * b_0 - 4799 * d_0)
			+ c_12 - e_12;
		eq_13 =
			(a_0 * b_13 - 43691 * d_13) +
			(a_1 * b_12 - 65535 * d_12) +
			(a_2 * b_11 - 65535 * d_11) +
			(a_3 * b_10 - 47614 * d_10) +
			(a_4 * b_9 - 65535 * d_9) +
			(a_5 * b_8 - 45395 * d_8) +
			(a_6 * b_7 - 65534 * d_7) +
			(a_7 * b_6 - 7851 * d_6) +
			(a_8 * b_5 - 63012 * d_5) +
			(a_9 * b_4 - 63152 * d_4) +
			(a_10 * b_3 - 53920 * d_3) +
			(a_11 * b_2 - 26416 * d_2) +
			(a_12 * b_1 - 4799 * d_1) +
			(a_13 * b_0 - 62341 * d_0)
			+ c_13 - e_13;
		eq_14 =
			(a_0 * b_14 - 43691 * d_14) +
			(a_1 * b_13 - 65535 * d_13) +
			(a_2 * b_12 - 65535 * d_12) +
			(a_3 * b_11 - 47614 * d_11) +
			(a_4 * b_10 - 65535 * d_10) +
			(a_5 * b_9 - 45395 * d_9) +
			(a_6 * b_8 - 65534 * d_8) +
			(a_7 * b_7 - 7851 * d_7) +
			(a_8 * b_6 - 63012 * d_6) +
			(a_9 * b_5 - 63152 * d_5) +
			(a_10 * b_4 - 53920 * d_4) +
			(a_11 * b_3 - 26416 * d_3) +
			(a_12 * b_2 - 4799 * d_2) +
			(a_13 * b_1 - 62341 * d_1) +
			(a_14 * b_0 - 19332 * d_0)
			+ c_14 - e_14;
		eq_15 =
			(a_0 * b_15 - 43691 * d_15) +
			(a_1 * b_14 - 65535 * d_14) +
			(a_2 * b_13 - 65535 * d_13) +
			(a_3 * b_12 - 47614 * d_12) +
			(a_4 * b_11 - 65535 * d_11) +
			(a_5 * b_10 - 45395 * d_10) +
			(a_6 * b_9 - 65534 * d_9) +
			(a_7 * b_8 - 7851 * d_8) +
			(a_8 * b_7 - 63012 * d_7) +
			(a_9 * b_6 - 63152 * d_6) +
			(a_10 * b_5 - 53920 * d_5) +
			(a_11 * b_4 - 26416 * d_4) +
			(a_12 * b_3 - 4799 * d_3) +
			(a_13 * b_2 - 62341 * d_2) +
			(a_14 * b_1 - 19332 * d_1) +
			(a_15 * b_0 - 25719 * d_0)
			+ c_15 - e_15;
		eq_16 =
			(a_0 * b_16 - 43691 * d_16) +
			(a_1 * b_15 - 65535 * d_15) +
			(a_2 * b_14 - 65535 * d_14) +
			(a_3 * b_13 - 47614 * d_13) +
			(a_4 * b_12 - 65535 * d_12) +
			(a_5 * b_11 - 45395 * d_11) +
			(a_6 * b_10 - 65534 * d_10) +
			(a_7 * b_9 - 7851 * d_9) +
			(a_8 * b_8 - 63012 * d_8) +
			(a_9 * b_7 - 63152 * d_7) +
			(a_10 * b_6 - 53920 * d_6) +
			(a_11 * b_5 - 26416 * d_5) +
			(a_12 * b_4 - 4799 * d_4) +
			(a_13 * b_3 - 62341 * d_3) +
			(a_14 * b_2 - 19332 * d_2) +
			(a_15 * b_1 - 25719 * d_1) +
			(a_16 * b_0 - 44247 * d_0)
			+ c_16 - e_16;
		eq_17 =
			(a_0 * b_17 - 43691 * d_17) +
			(a_1 * b_16 - 65535 * d_16) +
			(a_2 * b_15 - 65535 * d_15) +
			(a_3 * b_14 - 47614 * d_14) +
			(a_4 * b_13 - 65535 * d_13) +
			(a_5 * b_12 - 45395 * d_12) +
			(a_6 * b_11 - 65534 * d_11) +
			(a_7 * b_10 - 7851 * d_10) +
			(a_8 * b_9 - 63012 * d_9) +
			(a_9 * b_8 - 63152 * d_8) +
			(a_10 * b_7 - 53920 * d_7) +
			(a_11 * b_6 - 26416 * d_6) +
			(a_12 * b_5 - 4799 * d_5) +
			(a_13 * b_4 - 62341 * d_4) +
			(a_14 * b_3 - 19332 * d_3) +
			(a_15 * b_2 - 25719 * d_2) +
			(a_16 * b_1 - 44247 * d_1) +
			(a_17 * b_0 - 17227 * d_0)
			+ c_17 - e_17;
		eq_18 =
			(a_0 * b_18 - 43691 * d_18) +
			(a_1 * b_17 - 65535 * d_17) +
			(a_2 * b_16 - 65535 * d_16) +
			(a_3 * b_15 - 47614 * d_15) +
			(a_4 * b_14 - 65535 * d_14) +
			(a_5 * b_13 - 45395 * d_13) +
			(a_6 * b_12 - 65534 * d_12) +
			(a_7 * b_11 - 7851 * d_11) +
			(a_8 * b_10 - 63012 * d_10) +
			(a_9 * b_9 - 63152 * d_9) +
			(a_10 * b_8 - 53920 * d_8) +
			(a_11 * b_7 - 26416 * d_7) +
			(a_12 * b_6 - 4799 * d_6) +
			(a_13 * b_5 - 62341 * d_5) +
			(a_14 * b_4 - 19332 * d_4) +
			(a_15 * b_3 - 25719 * d_3) +
			(a_16 * b_2 - 44247 * d_2) +
			(a_17 * b_1 - 17227 * d_1) +
			(a_18 * b_0 - 42934 * d_0)
			+ c_18 - e_18;
		eq_19 =
			(a_0 * b_19 - 43691 * d_19) +
			(a_1 * b_18 - 65535 * d_18) +
			(a_2 * b_17 - 65535 * d_17) +
			(a_3 * b_16 - 47614 * d_16) +
			(a_4 * b_15 - 65535 * d_15) +
			(a_5 * b_14 - 45395 * d_14) +
			(a_6 * b_13 - 65534 * d_13) +
			(a_7 * b_12 - 7851 * d_12) +
			(a_8 * b_11 - 63012 * d_11) +
			(a_9 * b_10 - 63152 * d_10) +
			(a_10 * b_9 - 53920 * d_9) +
			(a_11 * b_8 - 26416 * d_8) +
			(a_12 * b_7 - 4799 * d_7) +
			(a_13 * b_6 - 62341 * d_6) +
			(a_14 * b_5 - 19332 * d_5) +
			(a_15 * b_4 - 25719 * d_4) +
			(a_16 * b_3 - 44247 * d_3) +
			(a_17 * b_2 - 17227 * d_2) +
			(a_18 * b_1 - 42934 * d_1) +
			(a_19 * b_0 - 19227 * d_0)
			+ c_19 - e_19;
		eq_20 =
			(a_0 * b_20 - 43691 * d_20) +
			(a_1 * b_19 - 65535 * d_19) +
			(a_2 * b_18 - 65535 * d_18) +
			(a_3 * b_17 - 47614 * d_17) +
			(a_4 * b_16 - 65535 * d_16) +
			(a_5 * b_15 - 45395 * d_15) +
			(a_6 * b_14 - 65534 * d_14) +
			(a_7 * b_13 - 7851 * d_13) +
			(a_8 * b_12 - 63012 * d_12) +
			(a_9 * b_11 - 63152 * d_11) +
			(a_10 * b_10 - 53920 * d_10) +
			(a_11 * b_9 - 26416 * d_9) +
			(a_12 * b_8 - 4799 * d_8) +
			(a_13 * b_7 - 62341 * d_7) +
			(a_14 * b_6 - 19332 * d_6) +
			(a_15 * b_5 - 25719 * d_5) +
			(a_16 * b_4 - 44247 * d_4) +
			(a_17 * b_3 - 17227 * d_3) +
			(a_18 * b_2 - 42934 * d_2) +
			(a_19 * b_1 - 19227 * d_1) +
			(a_20 * b_0 - 59034 * d_0)
			+ c_20 - e_20;
		eq_21 =
			(a_0 * b_21 - 43691 * d_21) +
			(a_1 * b_20 - 65535 * d_20) +
			(a_2 * b_19 - 65535 * d_19) +
			(a_3 * b_18 - 47614 * d_18) +
			(a_4 * b_17 - 65535 * d_17) +
			(a_5 * b_16 - 45395 * d_16) +
			(a_6 * b_15 - 65534 * d_15) +
			(a_7 * b_14 - 7851 * d_14) +
			(a_8 * b_13 - 63012 * d_13) +
			(a_9 * b_12 - 63152 * d_12) +
			(a_10 * b_11 - 53920 * d_11) +
			(a_11 * b_10 - 26416 * d_10) +
			(a_12 * b_9 - 4799 * d_9) +
			(a_13 * b_8 - 62341 * d_8) +
			(a_14 * b_7 - 19332 * d_7) +
			(a_15 * b_6 - 25719 * d_6) +
			(a_16 * b_5 - 44247 * d_5) +
			(a_17 * b_4 - 17227 * d_4) +
			(a_18 * b_3 - 42934 * d_3) +
			(a_19 * b_2 - 19227 * d_2) +
			(a_20 * b_1 - 59034 * d_1) +
			(a_21 * b_0 - 14719 * d_0)
			+ c_21 - e_21;
		eq_22 =
			(a_0 * b_22 - 43691 * d_22) +
			(a_1 * b_21 - 65535 * d_21) +
			(a_2 * b_20 - 65535 * d_20) +
			(a_3 * b_19 - 47614 * d_19) +
			(a_4 * b_18 - 65535 * d_18) +
			(a_5 * b_17 - 45395 * d_17) +
			(a_6 * b_16 - 65534 * d_16) +
			(a_7 * b_15 - 7851 * d_15) +
			(a_8 * b_14 - 63012 * d_14) +
			(a_9 * b_13 - 63152 * d_13) +
			(a_10 * b_12 - 53920 * d_12) +
			(a_11 * b_11 - 26416 * d_11) +
			(a_12 * b_10 - 4799 * d_10) +
			(a_13 * b_9 - 62341 * d_9) +
			(a_14 * b_8 - 19332 * d_8) +
			(a_15 * b_7 - 25719 * d_7) +
			(a_16 * b_6 - 44247 * d_6) +
			(a_17 * b_5 - 17227 * d_5) +
			(a_18 * b_4 - 42934 * d_4) +
			(a_19 * b_3 - 19227 * d_3) +
			(a_20 * b_2 - 59034 * d_2) +
			(a_21 * b_1 - 14719 * d_1) +
			(a_22 * b_0 - 4586 * d_0)
			+ c_22 - e_22;
		eq_23 =
			(a_0 * b_23 - 43691 * d_23) +
			(a_1 * b_22 - 65535 * d_22) +
			(a_2 * b_21 - 65535 * d_21) +
			(a_3 * b_20 - 47614 * d_20) +
			(a_4 * b_19 - 65535 * d_19) +
			(a_5 * b_18 - 45395 * d_18) +
			(a_6 * b_17 - 65534 * d_17) +
			(a_7 * b_16 - 7851 * d_16) +
			(a_8 * b_15 - 63012 * d_15) +
			(a_9 * b_14 - 63152 * d_14) +
			(a_10 * b_13 - 53920 * d_13) +
			(a_11 * b_12 - 26416 * d_12) +
			(a_12 * b_11 - 4799 * d_11) +
			(a_13 * b_10 - 62341 * d_10) +
			(a_14 * b_9 - 19332 * d_9) +
			(a_15 * b_8 - 25719 * d_8) +
			(a_16 * b_7 - 44247 * d_7) +
			(a_17 * b_6 - 17227 * d_6) +
			(a_18 * b_5 - 42934 * d_5) +
			(a_19 * b_4 - 19227 * d_4) +
			(a_20 * b_3 - 59034 * d_3) +
			(a_21 * b_2 - 14719 * d_2) +
			(a_22 * b_1 - 4586 * d_1) +
			(a_23 * b_0 - 6657 * d_0)
			+ c_23 - e_23;
		eq_24 =
			(a_1 * b_23 - 65535 * d_23) +
			(a_2 * b_22 - 65535 * d_22) +
			(a_3 * b_21 - 47614 * d_21) +
			(a_4 * b_20 - 65535 * d_20) +
			(a_5 * b_19 - 45395 * d_19) +
			(a_6 * b_18 - 65534 * d_18) +
			(a_7 * b_17 - 7851 * d_17) +
			(a_8 * b_16 - 63012 * d_16) +
			(a_9 * b_15 - 63152 * d_15) +
			(a_10 * b_14 - 53920 * d_14) +
			(a_11 * b_13 - 26416 * d_13) +
			(a_12 * b_12 - 4799 * d_12) +
			(a_13 * b_11 - 62341 * d_11) +
			(a_14 * b_10 - 19332 * d_10) +
			(a_15 * b_9 - 25719 * d_9) +
			(a_16 * b_8 - 44247 * d_8) +
			(a_17 * b_7 - 17227 * d_7) +
			(a_18 * b_6 - 42934 * d_6) +
			(a_19 * b_5 - 19227 * d_5) +
			(a_20 * b_4 - 59034 * d_4) +
			(a_21 * b_3 - 14719 * d_3) +
			(a_22 * b_2 - 4586 * d_2) +
			(a_23 * b_1 - 6657 * d_1);
		eq_25 =
			(a_2 * b_23 - 65535 * d_23) +
			(a_3 * b_22 - 47614 * d_22) +
			(a_4 * b_21 - 65535 * d_21) +
			(a_5 * b_20 - 45395 * d_20) +
			(a_6 * b_19 - 65534 * d_19) +
			(a_7 * b_18 - 7851 * d_18) +
			(a_8 * b_17 - 63012 * d_17) +
			(a_9 * b_16 - 63152 * d_16) +
			(a_10 * b_15 - 53920 * d_15) +
			(a_11 * b_14 - 26416 * d_14) +
			(a_12 * b_13 - 4799 * d_13) +
			(a_13 * b_12 - 62341 * d_12) +
			(a_14 * b_11 - 19332 * d_11) +
			(a_15 * b_10 - 25719 * d_10) +
			(a_16 * b_9 - 44247 * d_9) +
			(a_17 * b_8 - 17227 * d_8) +
			(a_18 * b_7 - 42934 * d_7) +
			(a_19 * b_6 - 19227 * d_6) +
			(a_20 * b_5 - 59034 * d_5) +
			(a_21 * b_4 - 14719 * d_4) +
			(a_22 * b_3 - 4586 * d_3) +
			(a_23 * b_2 - 6657 * d_2);
		eq_26 =
			(a_3 * b_23 - 47614 * d_23) +
			(a_4 * b_22 - 65535 * d_22) +
			(a_5 * b_21 - 45395 * d_21) +
			(a_6 * b_20 - 65534 * d_20) +
			(a_7 * b_19 - 7851 * d_19) +
			(a_8 * b_18 - 63012 * d_18) +
			(a_9 * b_17 - 63152 * d_17) +
			(a_10 * b_16 - 53920 * d_16) +
			(a_11 * b_15 - 26416 * d_15) +
			(a_12 * b_14 - 4799 * d_14) +
			(a_13 * b_13 - 62341 * d_13) +
			(a_14 * b_12 - 19332 * d_12) +
			(a_15 * b_11 - 25719 * d_11) +
			(a_16 * b_10 - 44247 * d_10) +
			(a_17 * b_9 - 17227 * d_9) +
			(a_18 * b_8 - 42934 * d_8) +
			(a_19 * b_7 - 19227 * d_7) +
			(a_20 * b_6 - 59034 * d_6) +
			(a_21 * b_5 - 14719 * d_5) +
			(a_22 * b_4 - 4586 * d_4) +
			(a_23 * b_3 - 6657 * d_3);
		eq_27 =
			(a_4 * b_23 - 65535 * d_23) +
			(a_5 * b_22 - 45395 * d_22) +
			(a_6 * b_21 - 65534 * d_21) +
			(a_7 * b_20 - 7851 * d_20) +
			(a_8 * b_19 - 63012 * d_19) +
			(a_9 * b_18 - 63152 * d_18) +
			(a_10 * b_17 - 53920 * d_17) +
			(a_11 * b_16 - 26416 * d_16) +
			(a_12 * b_15 - 4799 * d_15) +
			(a_13 * b_14 - 62341 * d_14) +
			(a_14 * b_13 - 19332 * d_13) +
			(a_15 * b_12 - 25719 * d_12) +
			(a_16 * b_11 - 44247 * d_11) +
			(a_17 * b_10 - 17227 * d_10) +
			(a_18 * b_9 - 42934 * d_9) +
			(a_19 * b_8 - 19227 * d_8) +
			(a_20 * b_7 - 59034 * d_7) +
			(a_21 * b_6 - 14719 * d_6) +
			(a_22 * b_5 - 4586 * d_5) +
			(a_23 * b_4 - 6657 * d_4);
		eq_28 =
			(a_5 * b_23 - 45395 * d_23) +
			(a_6 * b_22 - 65534 * d_22) +
			(a_7 * b_21 - 7851 * d_21) +
			(a_8 * b_20 - 63012 * d_20) +
			(a_9 * b_19 - 63152 * d_19) +
			(a_10 * b_18 - 53920 * d_18) +
			(a_11 * b_17 - 26416 * d_17) +
			(a_12 * b_16 - 4799 * d_16) +
			(a_13 * b_15 - 62341 * d_15) +
			(a_14 * b_14 - 19332 * d_14) +
			(a_15 * b_13 - 25719 * d_13) +
			(a_16 * b_12 - 44247 * d_12) +
			(a_17 * b_11 - 17227 * d_11) +
			(a_18 * b_10 - 42934 * d_10) +
			(a_19 * b_9 - 19227 * d_9) +
			(a_20 * b_8 - 59034 * d_8) +
			(a_21 * b_7 - 14719 * d_7) +
			(a_22 * b_6 - 4586 * d_6) +
			(a_23 * b_5 - 6657 * d_5);
		eq_29 =
			(a_6 * b_23 - 65534 * d_23) +
			(a_7 * b_22 - 7851 * d_22) +
			(a_8 * b_21 - 63012 * d_21) +
			(a_9 * b_20 - 63152 * d_20) +
			(a_10 * b_19 - 53920 * d_19) +
			(a_11 * b_18 - 26416 * d_18) +
			(a_12 * b_17 - 4799 * d_17) +
			(a_13 * b_16 - 62341 * d_16) +
			(a_14 * b_15 - 19332 * d_15) +
			(a_15 * b_14 - 25719 * d_14) +
			(a_16 * b_13 - 44247 * d_13) +
			(a_17 * b_12 - 17227 * d_12) +
			(a_18 * b_11 - 42934 * d_11) +
			(a_19 * b_10 - 19227 * d_10) +
			(a_20 * b_9 - 59034 * d_9) +
			(a_21 * b_8 - 14719 * d_8) +
			(a_22 * b_7 - 4586 * d_7) +
			(a_23 * b_6 - 6657 * d_6);
		eq_30 =
			(a_7 * b_23 - 7851 * d_23) +
			(a_8 * b_22 - 63012 * d_22) +
			(a_9 * b_21 - 63152 * d_21) +
			(a_10 * b_20 - 53920 * d_20) +
			(a_11 * b_19 - 26416 * d_19) +
			(a_12 * b_18 - 4799 * d_18) +
			(a_13 * b_17 - 62341 * d_17) +
			(a_14 * b_16 - 19332 * d_16) +
			(a_15 * b_15 - 25719 * d_15) +
			(a_16 * b_14 - 44247 * d_14) +
			(a_17 * b_13 - 17227 * d_13) +
			(a_18 * b_12 - 42934 * d_12) +
			(a_19 * b_11 - 19227 * d_11) +
			(a_20 * b_10 - 59034 * d_10) +
			(a_21 * b_9 - 14719 * d_9) +
			(a_22 * b_8 - 4586 * d_8) +
			(a_23 * b_7 - 6657 * d_7);
		eq_31 =
			(a_8 * b_23 - 63012 * d_23) +
			(a_9 * b_22 - 63152 * d_22) +
			(a_10 * b_21 - 53920 * d_21) +
			(a_11 * b_20 - 26416 * d_20) +
			(a_12 * b_19 - 4799 * d_19) +
			(a_13 * b_18 - 62341 * d_18) +
			(a_14 * b_17 - 19332 * d_17) +
			(a_15 * b_16 - 25719 * d_16) +
			(a_16 * b_15 - 44247 * d_15) +
			(a_17 * b_14 - 17227 * d_14) +
			(a_18 * b_13 - 42934 * d_13) +
			(a_19 * b_12 - 19227 * d_12) +
			(a_20 * b_11 - 59034 * d_11) +
			(a_21 * b_10 - 14719 * d_10) +
			(a_22 * b_9 - 4586 * d_9) +
			(a_23 * b_8 - 6657 * d_8);
		eq_32 =
			(a_9 * b_23 - 63152 * d_23) +
			(a_10 * b_22 - 53920 * d_22) +
			(a_11 * b_21 - 26416 * d_21) +
			(a_12 * b_20 - 4799 * d_20) +
			(a_13 * b_19 - 62341 * d_19) +
			(a_14 * b_18 - 19332 * d_18) +
			(a_15 * b_17 - 25719 * d_17) +
			(a_16 * b_16 - 44247 * d_16) +
			(a_17 * b_15 - 17227 * d_15) +
			(a_18 * b_14 - 42934 * d_14) +
			(a_19 * b_13 - 19227 * d_13) +
			(a_20 * b_12 - 59034 * d_12) +
			(a_21 * b_11 - 14719 * d_11) +
			(a_22 * b_10 - 4586 * d_10) +
			(a_23 * b_9 - 6657 * d_9);
		eq_33 =
			(a_10 * b_23 - 53920 * d_23) +
			(a_11 * b_22 - 26416 * d_22) +
			(a_12 * b_21 - 4799 * d_21) +
			(a_13 * b_20 - 62341 * d_20) +
			(a_14 * b_19 - 19332 * d_19) +
			(a_15 * b_18 - 25719 * d_18) +
			(a_16 * b_17 - 44247 * d_17) +
			(a_17 * b_16 - 17227 * d_16) +
			(a_18 * b_15 - 42934 * d_15) +
			(a_19 * b_14 - 19227 * d_14) +
			(a_20 * b_13 - 59034 * d_13) +
			(a_21 * b_12 - 14719 * d_12) +
			(a_22 * b_11 - 4586 * d_11) +
			(a_23 * b_10 - 6657 * d_10);
		eq_34 =
			(a_11 * b_23 - 26416 * d_23) +
			(a_12 * b_22 - 4799 * d_22) +
			(a_13 * b_21 - 62341 * d_21) +
			(a_14 * b_20 - 19332 * d_20) +
			(a_15 * b_19 - 25719 * d_19) +
			(a_16 * b_18 - 44247 * d_18) +
			(a_17 * b_17 - 17227 * d_17) +
			(a_18 * b_16 - 42934 * d_16) +
			(a_19 * b_15 - 19227 * d_15) +
			(a_20 * b_14 - 59034 * d_14) +
			(a_21 * b_13 - 14719 * d_13) +
			(a_22 * b_12 - 4586 * d_12) +
			(a_23 * b_11 - 6657 * d_11);
		eq_35 =
			(a_12 * b_23 - 4799 * d_23) +
			(a_13 * b_22 - 62341 * d_22) +
			(a_14 * b_21 - 19332 * d_21) +
			(a_15 * b_20 - 25719 * d_20) +
			(a_16 * b_19 - 44247 * d_19) +
			(a_17 * b_18 - 17227 * d_18) +
			(a_18 * b_17 - 42934 * d_17) +
			(a_19 * b_16 - 19227 * d_16) +
			(a_20 * b_15 - 59034 * d_15) +
			(a_21 * b_14 - 14719 * d_14) +
			(a_22 * b_13 - 4586 * d_13) +
			(a_23 * b_12 - 6657 * d_12);
		eq_36 =
			(a_13 * b_23 - 62341 * d_23) +
			(a_14 * b_22 - 19332 * d_22) +
			(a_15 * b_21 - 25719 * d_21) +
			(a_16 * b_20 - 44247 * d_20) +
			(a_17 * b_19 - 17227 * d_19) +
			(a_18 * b_18 - 42934 * d_18) +
			(a_19 * b_17 - 19227 * d_17) +
			(a_20 * b_16 - 59034 * d_16) +
			(a_21 * b_15 - 14719 * d_15) +
			(a_22 * b_14 - 4586 * d_14) +
			(a_23 * b_13 - 6657 * d_13);
		eq_37 =
			(a_14 * b_23 - 19332 * d_23) +
			(a_15 * b_22 - 25719 * d_22) +
			(a_16 * b_21 - 44247 * d_21) +
			(a_17 * b_20 - 17227 * d_20) +
			(a_18 * b_19 - 42934 * d_19) +
			(a_19 * b_18 - 19227 * d_18) +
			(a_20 * b_17 - 59034 * d_17) +
			(a_21 * b_16 - 14719 * d_16) +
			(a_22 * b_15 - 4586 * d_15) +
			(a_23 * b_14 - 6657 * d_14);
		eq_38 =
			(a_15 * b_23 - 25719 * d_23) +
			(a_16 * b_22 - 44247 * d_22) +
			(a_17 * b_21 - 17227 * d_21) +
			(a_18 * b_20 - 42934 * d_20) +
			(a_19 * b_19 - 19227 * d_19) +
			(a_20 * b_18 - 59034 * d_18) +
			(a_21 * b_17 - 14719 * d_17) +
			(a_22 * b_16 - 4586 * d_16) +
			(a_23 * b_15 - 6657 * d_15);
		eq_39 =
			(a_16 * b_23 - 44247 * d_23) +
			(a_17 * b_22 - 17227 * d_22) +
			(a_18 * b_21 - 42934 * d_21) +
			(a_19 * b_20 - 19227 * d_20) +
			(a_20 * b_19 - 59034 * d_19) +
			(a_21 * b_18 - 14719 * d_18) +
			(a_22 * b_17 - 4586 * d_17) +
			(a_23 * b_16 - 6657 * d_16);
		eq_40 =
			(a_17 * b_23 - 17227 * d_23) +
			(a_18 * b_22 - 42934 * d_22) +
			(a_19 * b_21 - 19227 * d_21) +
			(a_20 * b_20 - 59034 * d_20) +
			(a_21 * b_19 - 14719 * d_19) +
			(a_22 * b_18 - 4586 * d_18) +
			(a_23 * b_17 - 6657 * d_17);
		eq_41 =
			(a_18 * b_23 - 42934 * d_23) +
			(a_19 * b_22 - 19227 * d_22) +
			(a_20 * b_21 - 59034 * d_21) +
			(a_21 * b_20 - 14719 * d_20) +
			(a_22 * b_19 - 4586 * d_19) +
			(a_23 * b_18 - 6657 * d_18);
		eq_42 =
			(a_19 * b_23 - 19227 * d_23) +
			(a_20 * b_22 - 59034 * d_22) +
			(a_21 * b_21 - 14719 * d_21) +
			(a_22 * b_20 - 4586 * d_20) +
			(a_23 * b_19 - 6657 * d_19);
		eq_43 =
			(a_20 * b_23 - 59034 * d_23) +
			(a_21 * b_22 - 14719 * d_22) +
			(a_22 * b_21 - 4586 * d_21) +
			(a_23 * b_20 - 6657 * d_20);
		eq_44 =
			(a_21 * b_23 - 14719 * d_23) +
			(a_22 * b_22 - 4586 * d_22) +
			(a_23 * b_21 - 6657 * d_21);
		eq_45 =
			(a_22 * b_23 - 4586 * d_23) +
			(a_23 * b_22 - 6657 * d_22);
		eq_46 =
			(a_23 * b_23 - 6657 * d_23);
		eq_47 = 0;

		col witness eq;
		eq = eq_0*CLK_0 + eq_1*CLK_1 + eq_2*CLK_2 + eq_3*CLK_3 + eq_4*CLK_4 + eq_5*CLK_5 + eq_6*CLK_6 + eq_7*CLK_7
			+ eq_8*CLK_8 + eq_9*CLK_9 + eq_10*CLK_10 + eq_11*CLK_11 + eq_12*CLK_12 + eq_13*CLK_13 + eq_14*CLK_14 + eq_15*CLK_15
			+ eq_16*CLK_16 + eq_17*CLK_17 + eq_18*CLK_18 + eq_19*CLK_19 + eq_20*CLK_20 + eq_21*CLK_21 + eq_22*CLK_22 + eq_23*CLK_23
			+ eq_24*CLK_24 + eq_25*CLK_25 + eq_26*CLK_26 + eq_27*CLK_27 + eq_28*CLK_28 + eq_29*CLK_29 + eq_30*CLK_30 + eq_31*CLK_31
			+ eq_32*CLK_32 + eq_33*CLK_33 + eq_34*CLK_34 + eq_35*CLK_35 + eq_36*CLK_36 + eq_37*CLK_37 + eq_38*CLK_38 + eq_39*CLK_39
			+ eq_40*CLK_40 + eq_41*CLK_41 + eq_42*CLK_42 + eq_43*CLK_43 + eq_44*CLK_44 + eq_45*CLK_45 + eq_46*CLK_46 + eq_47*CLK_47;

		// pol commit carry;
		col fixed carry = [0]*;

		// TODO fix carry
		// eq + carry = carry' * 2**16;

		eq * carry = 0;  // REMOVE

		// NOTE: non complete PIL, missing implement carry range check
   }
}
"#,
    ]
}

impl Register {
    pub fn new(value: u8) -> Self {
        Self { value }
    }

    pub fn is_zero(&self) -> bool {
        self.value == 0
    }
}

impl asm_utils::ast::Register for Register {}

impl fmt::Display for Register {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "x{}", self.value)
    }
}

#[derive(Clone, Copy, Debug)]
pub enum FunctionKind {
    HiDataRef,
    LoDataRef,
}

impl asm_utils::ast::FunctionOpKind for FunctionKind {}

impl fmt::Display for FunctionKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FunctionKind::HiDataRef => write!(f, "%hi"),
            FunctionKind::LoDataRef => write!(f, "%lo"),
        }
    }
}

#[derive(Default)]
pub struct Risc {}

impl asm_utils::compiler::Compiler for Risc {
    /// Compiles riscv assembly to POWDR assembly. Adds required library routines.
    fn compile(mut assemblies: BTreeMap<String, String>) -> String {
        // stack grows towards zero
        let stack_start = 0x10000;
        // data grows away from zero
        let data_start = 0x10100;

        assert!(assemblies
            .insert("__runtime".to_string(), runtime().to_string())
            .is_none());

        // TODO remove unreferenced files.
        let (mut statements, file_ids) = disambiguator::disambiguate(
            assemblies
                .into_iter()
                .map(|(name, contents)| (name, parse_asm(RiscParser::default(), &contents)))
                .collect(),
        );
        let (mut objects, mut object_order) = data_parser::extract_data_objects(&statements);
        assert_eq!(objects.keys().len(), object_order.len());

        // Reduce to the code that is actually reachable from main
        // (and the objects that are referred from there)
        reachability::filter_reachable_from("__runtime_start", &mut statements, &mut objects);

        // Replace dynamic references to code labels
        replace_dynamic_label_references(&mut statements, &objects);

        // Remove the riscv asm stub function, which is used
        // for compilation, and will not be called.
        statements = replace_coprocessor_stubs(statements).collect::<Vec<_>>();

        // Sort the objects according to the order of the names in object_order.
        // With the single exception: If there is large object, put that at the end.
        // The idea behind this is that there might be a single gigantic object representing the heap
        // and putting that at the end should keep memory addresses small.
        let mut large_objects = objects
            .iter()
            .filter(|(_name, data)| data.iter().map(|d| d.size()).sum::<usize>() > 0x2000);
        if let (Some((heap, _)), None) = (large_objects.next(), large_objects.next()) {
            let heap_pos = object_order.iter().position(|o| o == heap).unwrap();
            object_order.remove(heap_pos);
            object_order.push(heap.clone());
        };
        let sorted_objects = object_order
            .into_iter()
            .filter_map(|n| {
                let value = objects.get_mut(&n).map(std::mem::take);
                value.map(|v| (n, v))
            })
            .collect::<Vec<_>>();
        let (data_code, data_positions) = store_data_objects(&sorted_objects, data_start);

        riscv_machine(
            &machine_decls(),
            &preamble(),
            &[("binary", "Binary"), ("shift", "Shift")],
            file_ids
                .into_iter()
                .map(|(id, dir, file)| format!("debug file {id} {} {};", quote(&dir), quote(&file)))
                .chain(["call __data_init;".to_string()])
                .chain(call_every_submachine())
                .chain([
                    format!("// Set stack pointer\nx2 <=X= {stack_start};"),
                    "call __runtime_start;".to_string(),
                    "return;".to_string(), // This is not "riscv ret", but "return from powdr asm function".
                ])
                .chain(
                    substitute_symbols_with_values(statements, &data_positions)
                        .into_iter()
                        .flat_map(process_statement),
                )
                .chain(["// This is the data initialization routine.\n__data_init::".to_string()])
                .chain(data_code)
                .chain(["// This is the end of the data initialization routine.\nret;".to_string()])
                .collect(),
        )
    }
}

/// Replace certain patterns of references to code labels by
/// special instructions. We ignore any references to data objects
/// because they will be handled differently.
fn replace_dynamic_label_references(
    statements: &mut Vec<Statement>,
    data_objects: &BTreeMap<String, Vec<DataValue>>,
) {
    /*
    Find patterns of the form
    lui	a0, %hi(LABEL)
    addi	s10, a0, %lo(LABEL)
    -
    turn this into the pseudo-riscv-instruction
    load_dynamic s10, LABEL
    which is then turned into

    s10 <== load_label(LABEL)

    It gets more complicated by the fact that sometimes, labels
    and debugging directives occur between the two statements
    matching that pattern...
    */
    let instruction_indices = statements
        .iter()
        .enumerate()
        .filter_map(|(i, s)| match s {
            Statement::Instruction(_, _) => Some(i),
            _ => None,
        })
        .collect::<Vec<_>>();

    let mut to_delete = BTreeSet::default();
    for (i1, i2) in instruction_indices.into_iter().tuple_windows() {
        if let Some(r) =
            replace_dynamic_label_reference(&statements[i1], &statements[i2], data_objects)
        {
            to_delete.insert(i1);
            statements[i2] = r;
        }
    }

    let mut i = 0;
    statements.retain(|_| (!to_delete.contains(&i), i += 1).0);
}

fn replace_dynamic_label_reference(
    s1: &Statement,
    s2: &Statement,
    data_objects: &BTreeMap<String, Vec<DataValue>>,
) -> Option<Statement> {
    let Statement::Instruction(instr1, args1) = s1 else {
        return None;
    };
    let Statement::Instruction(instr2, args2) = s2 else {
        return None;
    };
    if instr1.as_str() != "lui" || instr2.as_str() != "addi" {
        return None;
    };
    let [Argument::Register(r1), Argument::Expression(Expression::FunctionOp(FunctionKind::HiDataRef, expr1))] =
        &args1[..]
    else {
        return None;
    };
    // Maybe should try to reduce expr1 and expr2 before comparing deciding it is a pure symbol?
    let Expression::Symbol(label1) = expr1.as_ref() else {
        return None;
    };
    let [Argument::Register(r2), Argument::Register(r3), Argument::Expression(Expression::FunctionOp(FunctionKind::LoDataRef, expr2))] =
        &args2[..]
    else {
        return None;
    };
    let Expression::Symbol(label2) = expr2.as_ref() else {
        return None;
    };
    if r1 != r3 || label1 != label2 || data_objects.contains_key(label1) {
        return None;
    }
    Some(Statement::Instruction(
        "load_dynamic".to_string(),
        vec![
            Argument::Register(*r2),
            Argument::Expression(Expression::Symbol(label1.clone())),
        ],
    ))
}

fn remove_matching_and_next<I: Iterator, F>(iter: I, predicate: F) -> impl Iterator<Item = I::Item>
where
    F: Fn(&I::Item) -> bool,
{
    iter.scan(false, move |filter_next, item| {
        let mut filter_current = *filter_next;
        *filter_next = predicate(&item);
        // if the predicate says this line should be filtered, then
        // the next one should be filtered as well.
        filter_current |= *filter_next;
        Some((filter_current, item))
    })
    .filter_map(|(filter, statement)| (!filter).then_some(statement))
}

fn replace_coprocessor_stubs(
    statements: impl IntoIterator<Item = Statement>,
) -> impl Iterator<Item = Statement> {
    let stub_names: Vec<&str> = COPROCESSOR_SUBSTITUTIONS
        .iter()
        .map(|(name, _)| *name)
        .collect();

    remove_matching_and_next(statements.into_iter(), move |statement| -> bool {
        matches!(&statement, Statement::Label(label) if stub_names.contains(&label.as_str()))
    })
}

fn store_data_objects<'a>(
    objects: impl IntoIterator<Item = &'a (String, Vec<DataValue>)> + Copy,
    mut memory_start: u32,
) -> (Vec<String>, BTreeMap<String, u32>) {
    memory_start = ((memory_start + 7) / 8) * 8;
    let mut current_pos = memory_start;
    let mut positions = BTreeMap::new();
    for (name, data) in objects.into_iter() {
        // TODO check if we need to use multiples of four.
        let size: u32 = data
            .iter()
            .map(|d| next_multiple_of_four(d.size()) as u32)
            .sum();
        positions.insert(name.clone(), current_pos);
        current_pos += size;
    }

    let code = objects
        .into_iter()
        .filter(|(_, data)| !data.is_empty())
        .flat_map(|(name, data)| {
            let mut object_code = vec![];
            let mut pos = positions[name];
            for item in data {
                match &item {
                    DataValue::Zero(_length) => {
                        // We can assume memory to be zero-initialized,
                        // so we do nothing.
                    }
                    DataValue::Direct(bytes) => {
                        for i in (0..bytes.len()).step_by(4) {
                            let v = (0..4)
                                .map(|j| {
                                    (bytes.get(i + j).cloned().unwrap_or_default() as u32)
                                        << (j * 8)
                                })
                                .reduce(|a, b| a | b)
                                .unwrap();
                            // We can assume memory to be zero-initialized.
                            if v != 0 {
                                object_code.extend([
                                    format!("addr <=X= 0x{:x};", pos + i as u32),
                                    format!("mstore 0x{v:x};"),
                                ]);
                            }
                        }
                    }
                    DataValue::Reference(sym) => {
                        object_code.push(format!("addr <=X= 0x{pos:x};"));
                        if let Some(p) = positions.get(sym) {
                            object_code.push(format!("mstore 0x{p:x};"));
                        } else {
                            // code reference
                            // TODO should be possible without temporary
                            object_code.extend([
                                format!("tmp1 <== load_label({});", escape_label(sym)),
                                "mstore tmp1;".to_string(),
                            ]);
                        }
                    }
                    DataValue::Offset(_, _) => {
                        unimplemented!()

                        /*
                        object_code.push(format!("addr <=X= 0x{pos:x};"));

                        I think this solution should be fine but hard to say without
                        an actual code snippet that uses it.

                        // TODO should be possible without temporary
                        object_code.extend([
                            format!("tmp1 <== load_label({});", escape_label(a)),
                            format!("tmp2 <== load_label({});", escape_label(b)),
                            // TODO check if registers match
                            "mstore wrap(tmp1 - tmp2);".to_string(),
                        ]);
                        */
                    }
                }
                pos += item.size() as u32;
            }
            if let Some(first_line) = object_code.first_mut() {
                *first_line = format!("// data {name}\n") + first_line;
            }
            object_code
        })
        .collect();
    (code, positions)
}

fn call_every_submachine() -> Vec<String> {
    // TODO This is a hacky snippet to ensure that every submachine in the RISCV machine
    // is called at least once. This is needed for witgen until it can do default blocks
    // automatically.
    // https://github.com/powdr-labs/powdr/issues/548
    vec![
        "x10 <== and(x10, x10);".to_string(),
        "x10 <== shl(x10, x10);".to_string(),
        "x10 <=X= 0;".to_string(),
    ]
}

fn next_multiple_of_four(x: usize) -> usize {
    ((x + 3) / 4) * 4
}

fn substitute_symbols_with_values(
    mut statements: Vec<Statement>,
    data_positions: &BTreeMap<String, u32>,
) -> Vec<Statement> {
    for s in &mut statements {
        let Statement::Instruction(_name, args) = s else {
            continue;
        };
        for arg in args {
            arg.post_visit_expressions_mut(&mut |expression| match expression {
                Expression::Number(_) => {}
                Expression::Symbol(symb) => {
                    if let Some(pos) = data_positions.get(symb) {
                        *expression = Expression::Number(*pos as i64)
                    }
                }
                Expression::UnaryOp(op, subexpr) => {
                    if let Expression::Number(num) = subexpr.as_ref() {
                        let result = match op {
                            UnaryOpKind::Negation => -num,
                        };
                        *expression = Expression::Number(result);
                    };
                }
                Expression::BinaryOp(op, subexprs) => {
                    if let (Expression::Number(a), Expression::Number(b)) =
                        (&subexprs[0], &subexprs[1])
                    {
                        let result = match op {
                            BinaryOpKind::Or => a | b,
                            BinaryOpKind::Xor => a ^ b,
                            BinaryOpKind::And => a & b,
                            BinaryOpKind::LeftShift => a << b,
                            BinaryOpKind::RightShift => a >> b,
                            BinaryOpKind::Add => a + b,
                            BinaryOpKind::Sub => a - b,
                            BinaryOpKind::Mul => a * b,
                            BinaryOpKind::Div => a / b,
                            BinaryOpKind::Mod => a % b,
                        };
                        *expression = Expression::Number(result);
                    }
                }
                Expression::FunctionOp(op, subexpr) => {
                    if let Expression::Number(num) = subexpr.as_ref() {
                        let result = match op {
                            FunctionKind::HiDataRef => num >> 12,
                            FunctionKind::LoDataRef => num & 0xfff,
                        };
                        *expression = Expression::Number(result);
                    };
                }
            });
        }
    }
    statements
}

fn riscv_machine(
    machines: &[&str],
    preamble: &str,
    submachines: &[(&str, &str)],
    program: Vec<String>,
) -> String {
    format!(
        r#"
{}
machine Main {{
{}

{}

    function main {{
{}
    }}
}}    
"#,
        machines.join("\n"),
        submachines
            .iter()
            .map(|(instance, ty)| format!("\t\t{} {};", ty, instance))
            .collect::<Vec<_>>()
            .join("\n"),
        preamble,
        program
            .into_iter()
            .map(|line| format!("\t\t{line}"))
            .collect::<Vec<_>>()
            .join("\n")
    )
}

fn preamble() -> String {
    r#"
    degree 262144;
    reg pc[@pc];
    reg X[<=];
    reg Y[<=];
    reg Z[<=];
    reg tmp1;
    reg tmp2;
    reg tmp3;
"#
    .to_string()
        + &(0..32)
            .map(|i| format!("\t\treg x{i};\n"))
            .collect::<Vec<_>>()
            .concat()
        + r#"
    reg addr;

    constraints {
        x0 = 0;
    }

    constraints{
    // ============== iszero check for X =======================
        col witness XInv;
        col witness XIsZero;
        XIsZero = 1 - X * XInv;
        XIsZero * X = 0;
        XIsZero * (1 - XIsZero) = 0;

    // =============== read-write memory =======================
        // Read-write memory. Columns are sorted by m_addr and
        // then by m_step. m_change is 1 if and only if m_addr changes
        // in the next row.
        col witness m_addr;
        col witness m_step;
        col witness m_change;
        col witness m_value;
        // If we have an operation at all (needed because this needs to be a permutation)
        col witness m_op;
        // If the operation is a write operation.
        col witness m_is_write;
        col witness m_is_read;

        // positive numbers (assumed to be much smaller than the field order)
        col fixed POSITIVE(i) { i + 1 };
        col fixed FIRST = [1] + [0]*;
        col fixed LAST(i) { FIRST(i + 1) };
        col fixed STEP(i) { i };

        m_change * (1 - m_change) = 0;

        // if m_change is zero, m_addr has to stay the same.
        (m_addr' - m_addr) * (1 - m_change) = 0;

        // Except for the last row, if m_change is 1, then m_addr has to increase,
        // if it is zero, m_step has to increase.
        (1 - LAST) { m_change * (m_addr' - m_addr) + (1 - m_change) * (m_step' - m_step) } in POSITIVE;

        m_op * (1 - m_op) = 0;
        m_is_write * (1 - m_is_write) = 0;
        m_is_read * (1 - m_is_read) = 0;
        // m_is_write can only be 1 if m_op is 1.
        m_is_write * (1 - m_op) = 0;
        m_is_read * (1 - m_op) = 0;
        m_is_read * m_is_write = 0;


        // If the next line is a read and we stay at the same address, then the
        // value cannot change.
        (1 - m_is_write') * (1 - m_change) * (m_value' - m_value) = 0;

        // If the next line is a read and we have an address change,
        // then the value is zero.
        (1 - m_is_write') * m_change * m_value' = 0;
    }

    // ============== memory instructions ==============

    instr mstore X { { addr, STEP, X } is m_is_write { m_addr, m_step, m_value } }
    instr mload -> X { { addr, STEP, X } is m_is_read { m_addr, m_step, m_value } }

    // ============== control-flow instructions ==============

    instr jump l: label { pc' = l }
    instr load_label l: label -> X { X = l }
    instr jump_dyn X { pc' = X }
    instr jump_and_link_dyn X { pc' = X, x1' = pc + 1 }
    instr call l: label { pc' = l, x1' = pc + 1 }
    // TODO x6 actually stores some relative address, but only part of it.
    instr tail l: label { pc' = l, x6' = l }
    instr ret { pc' = x1 }

    instr branch_if_nonzero X, l: label { pc' = (1 - XIsZero) * l + XIsZero * (pc + 1) }
    instr branch_if_zero X, l: label { pc' = XIsZero * l + (1 - XIsZero) * (pc + 1) }

    // input X is required to be the difference of two 32-bit unsigend values.
    // i.e. -2**32 < X < 2**32
    instr branch_if_positive X, l: label {
        X + 2**32 - 1 = X_b1 + X_b2 * 0x100 + X_b3 * 0x10000 + X_b4 * 0x1000000 + wrap_bit * 2**32,
        pc' = wrap_bit * l + (1 - wrap_bit) * (pc + 1)
    }
    // input X is required to be the difference of two 32-bit unsigend values.
    // i.e. -2**32 < X < 2**32
    instr is_positive X -> Y {
        X + 2**32 - 1 = X_b1 + X_b2 * 0x100 + X_b3 * 0x10000 + X_b4 * 0x1000000 + wrap_bit * 2**32,
        Y = wrap_bit
    }

    // ================= logical instructions =================

    instr is_equal_zero X -> Y { Y = XIsZero }
    instr is_not_equal_zero X -> Y { Y = 1 - XIsZero }

    // ================= coprocessor substitution instructions =================

    instr poseidon Y, Z -> X {
        // Dummy code, to be replaced with actual poseidon code.
        X = 0
    }

    // ================= binary/bitwise instructions =================

    instr and Y, Z -> X = binary.and

    instr or Y, Z -> X = binary.or

    instr xor Y, Z -> X = binary.xor

    // ================= shift instructions =================

    instr shl Y, Z -> X = shift.shl

    instr shr Y, Z -> X = shift.shr

    // ================== wrapping instructions ==============

    // Wraps a value in Y to 32 bits.
    // Requires 0 <= Y < 2**33
    instr wrap Y -> X { Y = X + wrap_bit * 2**32, X = X_b1 + X_b2 * 0x100 + X_b3 * 0x10000 + X_b4 * 0x1000000 }
    // Requires -2**32 <= Y < 2**32
    instr wrap_signed Y -> X { Y + 2**32 = X + wrap_bit * 2**32, X = X_b1 + X_b2 * 0x100 + X_b3 * 0x10000 + X_b4 * 0x1000000 }
    constraints{
        col fixed bytes(i) { i & 0xff };
        col witness X_b1;
        col witness X_b2;
        col witness X_b3;
        col witness X_b4;
        { X_b1 } in { bytes };
        { X_b2 } in { bytes };
        { X_b3 } in { bytes };
        { X_b4 } in { bytes };
        col witness wrap_bit;
        wrap_bit * (1 - wrap_bit) = 0;
    }

    // Input is a 32 bit unsigned number. We check the 7th bit and set all higher bits to that value.
    instr sign_extend_byte Y -> X {
        // wrap_bit is used as sign_bit here.
        Y = Y_7bit + wrap_bit * 0x80 + X_b2 * 0x100 + X_b3 * 0x10000 + X_b4 * 0x1000000,
        X = Y_7bit + wrap_bit * 0xffffff80
    }
    constraints{
        col fixed seven_bit(i) { i & 0x7f };
        col witness Y_7bit;
        { Y_7bit } in { seven_bit };
    }

    // Input is a 32 but unsigned number (0 <= Y < 2**32) interpreted as a two's complement numbers.
    // Returns a signed number (-2**31 <= X < 2**31).
    instr to_signed Y -> X {
        // wrap_bit is used as sign_bit here.
        Y = X_b1 + X_b2 * 0x100 + X_b3 * 0x10000 + Y_7bit * 0x1000000 + wrap_bit * 0x80000000,
        X = Y - wrap_bit * 2**32
    }

    // ======================= assertions =========================

    instr fail { 1 = 0 }

    // Removes up to 16 bits beyond 32
    // TODO is this really safe?
    instr wrap16 Y -> X { Y = Y_b5 * 2**32 + Y_b6 * 2**40 + X, X = X_b1 + X_b2 * 0x100 + X_b3 * 0x10000 + X_b4 * 0x1000000 }
    constraints {
        col witness Y_b5;
        col witness Y_b6;
        col witness Y_b7;
        col witness Y_b8;
        { Y_b5 } in { bytes };
        { Y_b6 } in { bytes };
        { Y_b7 } in { bytes };
        { Y_b8 } in { bytes };

        col witness remainder; 

        col witness REM_b1;
        col witness REM_b2;
        col witness REM_b3;
        col witness REM_b4;
        { REM_b1 } in { bytes };
        { REM_b2 } in { bytes };
        { REM_b3 } in { bytes };
        { REM_b4 } in { bytes };
    }

    // implements Z = Y / X, stores remainder in `remainder`.
    instr divu Y, X -> Z {
        // Y is the known dividend
        // X is the known divisor
        // Z is the unknown quotient
        // main division algorithm;
        // if X is zero, remainder is set to dividend, as per RISC-V specification:
        X * Z + remainder = Y,

        // remainder >= 0:
        remainder = REM_b1 + REM_b2 * 0x100 + REM_b3 * 0x10000 + REM_b4 * 0x1000000,

        // remainder < divisor, conditioned to X not being 0:
        (1 - XIsZero) * (X - remainder - 1 - Y_b5 - Y_b6 * 0x100 - Y_b7 * 0x10000 - Y_b8 * 0x1000000) = 0,

        // in case X is zero, we set quotient according to RISC-V specification
        XIsZero * (Z - 0xffffffff) = 0,

        // quotient is 32 bits:
        Z = X_b1 + X_b2 * 0x100 + X_b3 * 0x10000 + X_b4 * 0x1000000
    }

    // Removes up to 32 bits beyond 32
    // TODO is this really safe?
    instr mul Y, Z -> X {
        Y * Z = X + Y_b5 * 2**32 + Y_b6 * 2**40 + Y_b7 * 2**48 + Y_b8 * 2**56,
        X = X_b1 + X_b2 * 0x100 + X_b3 * 0x10000 + X_b4 * 0x1000000
    }
    // implements (Y * Z) >> 32
    instr mulhu Y, Z -> X {
        Y * Z = X * 2**32 + Y_b5 + Y_b6 * 0x100 + Y_b7 * 0x10000 + Y_b8 * 0x1000000,
        X = X_b1 + X_b2 * 0x100 + X_b3 * 0x10000 + X_b4 * 0x1000000
    }
"#
}

fn runtime() -> &'static str {
    r#"
.globl __udivdi3@plt
.globl __udivdi3
.set __udivdi3@plt, __udivdi3

.globl memcpy@plt
.globl memcpy
.set memcpy@plt, memcpy

.globl memmove@plt
.globl memmove
.set memmove@plt, memmove

.globl memset@plt
.globl memset
.set memset@plt, memset

.globl memcmp@plt
.globl memcmp
.set memcmp@plt, memcmp

.globl bcmp@plt
.globl bcmp
.set bcmp@plt, bcmp

.globl strlen@plt
.globl strlen
.set strlen@plt, strlen

.globl __rust_alloc
.set __rust_alloc, __rg_alloc

.globl __rust_dealloc
.set __rust_dealloc, __rg_dealloc

.globl __rust_realloc
.set __rust_realloc, __rg_realloc

.globl __rust_alloc_zeroed
.set __rust_alloc_zeroed, __rg_alloc_zeroed

.globl __rust_alloc_error_handler
.set __rust_alloc_error_handler, __rg_oom

.globl poseidon_coprocessor
poseidon_coprocessor:
    ret
"#
}

fn process_statement(s: Statement) -> Vec<String> {
    match &s {
        Statement::Label(l) => vec![format!("{}::", escape_label(l))],
        Statement::Directive(directive, args) => match (directive.as_str(), &args[..]) {
            (
                ".loc",
                [Argument::Expression(Expression::Number(file)), Argument::Expression(Expression::Number(line)), Argument::Expression(Expression::Number(column)), ..],
            ) => {
                vec![format!("  debug loc {file} {line} {column};")]
            }
            (".file", _) => {
                // We ignore ".file" directives because they have been extracted to the top.
                vec![]
            }
            _ if directive.starts_with(".cfi_") => vec![],
            _ => panic!(
                "Leftover directive in code: {directive} {}",
                args.iter().map(|s| s.to_string()).join(", ")
            ),
        },
        Statement::Instruction(instr, args) => process_instruction(instr, args)
            .into_iter()
            .map(|s| "  ".to_string() + &s)
            .collect(),
    }
}

fn quote(s: &str) -> String {
    // TODO more things to quote
    format!("\"{}\"", s.replace('\\', "\\\\").replace('\"', "\\\""))
}

fn escape_label(l: &str) -> String {
    // TODO make this proper
    l.replace('.', "_dot_").replace('/', "_slash_")
}

fn argument_to_number(x: &Argument) -> u32 {
    if let Argument::Expression(expr) = x {
        expression_to_number(expr)
    } else {
        panic!("Expected numeric expression, got {x}")
    }
}

fn expression_to_number(expr: &Expression) -> u32 {
    if let Expression::Number(n) = expr {
        *n as u32
    } else {
        panic!("Constant expression could not be fully resolved to a number during preprocessing: {expr}");
    }
}

fn argument_to_escaped_symbol(x: &Argument) -> String {
    if let Argument::Expression(Expression::Symbol(symb)) = x {
        escape_label(symb)
    } else {
        panic!("Expected a symbol, got {x}");
    }
}

fn r(args: &[Argument]) -> Register {
    match args {
        [Argument::Register(r1)] => *r1,
        _ => panic!(),
    }
}

fn rri(args: &[Argument]) -> (Register, Register, u32) {
    match args {
        [Argument::Register(r1), Argument::Register(r2), n] => (*r1, *r2, argument_to_number(n)),
        _ => panic!(),
    }
}

fn rrr(args: &[Argument]) -> (Register, Register, Register) {
    match args {
        [Argument::Register(r1), Argument::Register(r2), Argument::Register(r3)] => (*r1, *r2, *r3),
        _ => panic!(),
    }
}

fn ri(args: &[Argument]) -> (Register, u32) {
    match args {
        [Argument::Register(r1), n] => (*r1, argument_to_number(n)),
        _ => panic!(),
    }
}

fn rr(args: &[Argument]) -> (Register, Register) {
    match args {
        [Argument::Register(r1), Argument::Register(r2)] => (*r1, *r2),
        _ => panic!(),
    }
}

fn rrl(args: &[Argument]) -> (Register, Register, String) {
    match args {
        [Argument::Register(r1), Argument::Register(r2), l] => {
            (*r1, *r2, argument_to_escaped_symbol(l))
        }
        _ => panic!(),
    }
}

fn rl(args: &[Argument]) -> (Register, String) {
    match args {
        [Argument::Register(r1), l] => (*r1, argument_to_escaped_symbol(l)),
        _ => panic!(),
    }
}

fn rro(args: &[Argument]) -> (Register, Register, u32) {
    match args {
        [Argument::Register(r1), Argument::RegOffset(r2, off)] => {
            (*r1, *r2, expression_to_number(off))
        }
        _ => panic!(),
    }
}

fn only_if_no_write_to_zero(statement: String, reg: Register) -> Vec<String> {
    only_if_no_write_to_zero_vec(vec![statement], reg)
}

fn only_if_no_write_to_zero_vec(statements: Vec<String>, reg: Register) -> Vec<String> {
    if reg.is_zero() {
        vec![]
    } else {
        statements
    }
}

static COPROCESSOR_SUBSTITUTIONS: &[(&str, &str)] =
    &[("poseidon_coprocessor", "x10 <== poseidon(x10, x11);")];

fn try_coprocessor_substitution(label: &str) -> Option<String> {
    COPROCESSOR_SUBSTITUTIONS
        .iter()
        .find(|(l, _)| *l == label)
        .map(|&(_, subst)| subst.to_string())
}

fn process_instruction(instr: &str, args: &[Argument]) -> Vec<String> {
    match instr {
        // load/store registers
        "li" => {
            let (rd, imm) = ri(args);
            only_if_no_write_to_zero(format!("{rd} <=X= {imm};"), rd)
        }
        // TODO check if it is OK to clear the lower order bits
        "lui" => {
            let (rd, imm) = ri(args);
            only_if_no_write_to_zero(format!("{rd} <=X= {};", imm << 12), rd)
        }
        "la" => {
            let (rd, addr) = ri(args);
            only_if_no_write_to_zero(format!("{rd} <=X= {};", addr), rd)
        }
        "mv" => {
            let (rd, rs) = rr(args);
            only_if_no_write_to_zero(format!("{rd} <=X= {rs};"), rd)
        }

        // Arithmetic
        "add" => {
            let (rd, r1, r2) = rrr(args);
            only_if_no_write_to_zero(format!("{rd} <== wrap({r1} + {r2});"), rd)
        }
        "addi" => {
            let (rd, rs, imm) = rri(args);
            only_if_no_write_to_zero(format!("{rd} <== wrap({rs} + {imm});"), rd)
        }
        "sub" => {
            let (rd, r1, r2) = rrr(args);
            only_if_no_write_to_zero(format!("{rd} <== wrap_signed({r1} - {r2});"), rd)
        }
        "neg" => {
            let (rd, r1) = rr(args);
            only_if_no_write_to_zero(format!("{rd} <== wrap_signed(0 - {r1});"), rd)
        }
        "mul" => {
            let (rd, r1, r2) = rrr(args);
            only_if_no_write_to_zero(format!("{rd} <== mul({r1}, {r2});"), rd)
        }
        "mulhu" => {
            let (rd, r1, r2) = rrr(args);
            only_if_no_write_to_zero(format!("{rd} <== mulhu({r1}, {r2});"), rd)
        }
        "divu" => {
            let (rd, r1, r2) = rrr(args);
            only_if_no_write_to_zero(format!("{rd} <=Z= divu({r1}, {r2});"), rd)
        }

        // bitwise
        "xor" => {
            let (rd, r1, r2) = rrr(args);
            only_if_no_write_to_zero(format!("{rd} <== xor({r1}, {r2});"), rd)
        }
        "xori" => {
            let (rd, r1, imm) = rri(args);
            only_if_no_write_to_zero(format!("{rd} <== xor({r1}, {imm});"), rd)
        }
        "and" => {
            let (rd, r1, r2) = rrr(args);
            only_if_no_write_to_zero(format!("{rd} <== and({r1}, {r2});"), rd)
        }
        "andi" => {
            let (rd, r1, imm) = rri(args);
            only_if_no_write_to_zero(format!("{rd} <== and({r1}, {imm});"), rd)
        }
        "or" => {
            let (rd, r1, r2) = rrr(args);
            only_if_no_write_to_zero(format!("{rd} <== or({r1}, {r2});"), rd)
        }
        "ori" => {
            let (rd, r1, imm) = rri(args);
            only_if_no_write_to_zero(format!("{rd} <== or({r1}, {imm});"), rd)
        }
        "not" => {
            let (rd, rs) = rr(args);
            only_if_no_write_to_zero(format!("{rd} <== wrap_signed(-{rs} - 1);"), rd)
        }

        // shift
        "slli" => {
            let (rd, rs, amount) = rri(args);
            assert!(amount <= 31);
            only_if_no_write_to_zero_vec(
                if amount <= 16 {
                    vec![format!("{rd} <== wrap16({rs} * {});", 1 << amount)]
                } else {
                    vec![
                        format!("tmp1 <== wrap16({rs} * {});", 1 << 16),
                        format!("{rd} <== wrap16(tmp1 * {});", 1 << (amount - 16)),
                    ]
                },
                rd,
            )
        }
        "sll" => {
            let (rd, r1, r2) = rrr(args);
            only_if_no_write_to_zero_vec(
                vec![
                    format!("tmp1 <== and({r2}, 0x1f);"),
                    format!("{rd} <== shl({r1}, tmp1);"),
                ],
                rd,
            )
        }
        "srli" => {
            // logical shift right
            let (rd, rs, amount) = rri(args);
            assert!(amount <= 31);
            only_if_no_write_to_zero(format!("{rd} <== shr({rs}, {amount});"), rd)
        }
        "srl" => {
            // logical shift right
            let (rd, r1, r2) = rrr(args);
            only_if_no_write_to_zero_vec(
                vec![
                    format!("tmp1 <== and({r2}, 0x1f);"),
                    format!("{rd} <== shr({r1}, tmp1);"),
                ],
                rd,
            )
        }
        "srai" => {
            // arithmetic shift right
            // TODO see if we can implement this directly with a machine.
            // Now we are using the equivalence
            // a >>> b = (a >= 0 ? a >> b : ~(~a >> b))
            let (rd, rs, amount) = rri(args);
            assert!(amount <= 31);
            only_if_no_write_to_zero_vec(
                vec![
                    format!("tmp1 <== to_signed({rs});"),
                    format!("tmp1 <== is_positive(0 - tmp1);"),
                    format!("tmp1 <=X= tmp1 * 0xffffffff;"),
                    // Here, tmp1 is the full bit mask if rs is negative
                    // and zero otherwise.
                    format!("{rd} <== xor(tmp1, {rs});"),
                    format!("{rd} <== shr({rd}, {amount});"),
                    format!("{rd} <== xor(tmp1, {rd});"),
                ],
                rd,
            )
        }

        // comparison
        "seqz" => {
            let (rd, rs) = rr(args);
            only_if_no_write_to_zero(format!("{rd} <=Y= is_equal_zero({rs});"), rd)
        }
        "snez" => {
            let (rd, rs) = rr(args);
            only_if_no_write_to_zero(format!("{rd} <=Y= is_not_equal_zero({rs});"), rd)
        }
        "slti" => {
            let (rd, rs, imm) = rri(args);
            only_if_no_write_to_zero_vec(
                vec![
                    format!("tmp1 <== to_signed({rs});"),
                    format!("{rd} <=Y= is_positive({} - tmp1);", imm as i32),
                ],
                rd,
            )
        }
        "slt" => {
            let (rd, r1, r2) = rrr(args);
            vec![
                format!("tmp1 <== to_signed({r1});"),
                format!("tmp2 <== to_signed({r2});"),
                format!("{rd} <=Y= is_positive(tmp2 - tmp1);"),
            ]
        }
        "sltiu" => {
            let (rd, rs, imm) = rri(args);
            only_if_no_write_to_zero(format!("{rd} <=Y= is_positive({imm} - {rs});"), rd)
        }
        "sltu" => {
            let (rd, r1, r2) = rrr(args);
            only_if_no_write_to_zero(format!("{rd} <=Y= is_positive({r2} - {r1});"), rd)
        }
        "sgtz" => {
            let (rd, rs) = rr(args);
            vec![
                format!("tmp1 <== to_signed({rs});"),
                format!("{rd} <=Y= is_positive(tmp1);"),
            ]
        }

        // branching
        "beq" => {
            let (r1, r2, label) = rrl(args);
            vec![format!("branch_if_zero {r1} - {r2}, {label};")]
        }
        "beqz" => {
            let (r1, label) = rl(args);
            vec![format!("branch_if_zero {r1}, {label};")]
        }
        "bgeu" => {
            let (r1, r2, label) = rrl(args);
            // TODO does this fulfill the input requirements for branch_if_positive?
            vec![format!("branch_if_positive {r1} - {r2} + 1, {label};")]
        }
        "bgez" => {
            let (r1, label) = rl(args);
            vec![
                format!("tmp1 <== to_signed({r1});"),
                format!("branch_if_positive tmp1 + 1, {label};"),
            ]
        }
        "bltu" => {
            let (r1, r2, label) = rrl(args);
            vec![format!("branch_if_positive {r2} - {r1}, {label};")]
        }
        "blt" => {
            let (r1, r2, label) = rrl(args);
            // Branch if r1 < r2 (signed).
            // TODO does this fulfill the input requirements for branch_if_positive?
            vec![
                format!("tmp1 <== to_signed({r1});"),
                format!("tmp2 <== to_signed({r2});"),
                format!("branch_if_positive tmp2 - tmp1, {label};"),
            ]
        }
        "bge" => {
            let (r1, r2, label) = rrl(args);
            // Branch if r1 >= r2 (signed).
            // TODO does this fulfill the input requirements for branch_if_positive?
            vec![
                format!("tmp1 <== to_signed({r1});"),
                format!("tmp2 <== to_signed({r2});"),
                format!("branch_if_positive tmp1 - tmp2 + 1, {label};"),
            ]
        }
        "bltz" => {
            // branch if 2**31 <= r1 < 2**32
            let (r1, label) = rl(args);
            vec![format!("branch_if_positive {r1} - 2**31 + 1, {label};")]
        }

        "blez" => {
            // branch less or equal zero
            let (r1, label) = rl(args);
            vec![
                format!("tmp1 <== to_signed({r1});"),
                format!("branch_if_positive -tmp1 + 1, {label};"),
            ]
        }
        "bgtz" => {
            // branch if 0 < r1 < 2**31
            let (r1, label) = rl(args);
            vec![
                format!("tmp1 <== to_signed({r1});"),
                format!("branch_if_positive tmp1, {label};"),
            ]
        }
        "bne" => {
            let (r1, r2, label) = rrl(args);
            vec![format!("branch_if_nonzero {r1} - {r2}, {label};")]
        }
        "bnez" => {
            let (r1, label) = rl(args);
            vec![format!("branch_if_nonzero {r1}, {label};")]
        }

        // jump and call
        "j" => {
            if let [label] = args {
                vec![format!("jump {};", argument_to_escaped_symbol(label))]
            } else {
                panic!()
            }
        }
        "jr" => {
            let rs = r(args);
            vec![format!("jump_dyn {rs};")]
        }
        "jal" => {
            let (_rd, _label) = rl(args);
            todo!();
        }
        "jalr" => {
            // TODO there is also a form that takes more arguments
            let rs = r(args);
            vec![format!("jump_and_link_dyn {rs};")]
        }
        "call" | "tail" => {
            // Depending on what symbol is called, the call is replaced by a
            // powdr asm call, or a call to a coprocessor if a special function
            // has been recognized.
            assert_eq!(args.len(), 1);
            let label = &args[0];
            let replacement = match label {
                Argument::Expression(Expression::Symbol(l)) => try_coprocessor_substitution(l),
                _ => None,
            };
            match (replacement, instr) {
                (Some(replacement), "call") => vec![replacement],
                (Some(replacement), "tail") => vec![replacement, "ret;".to_string()],
                (Some(_), _) => panic!(),
                (None, _) => vec![format!("{instr} {};", argument_to_escaped_symbol(label))],
            }
        }
        "ecall" => {
            assert!(args.is_empty());
            vec!["x10 <=X= ${ (\"input\", x10) };".to_string()]
        }
        "ebreak" => {
            assert!(args.is_empty());
            // This is using x0 on purpose, because we do not want to introduce
            // nondeterminism with this.
            vec!["x0 <=X= ${ (\"print_char\", x10) };\n".to_string()]
        }
        "ret" => {
            assert!(args.is_empty());
            vec!["ret;".to_string()]
        }

        // memory access
        "lw" => {
            let (rd, rs, off) = rro(args);
            // TODO we need to consider misaligned loads / stores
            only_if_no_write_to_zero_vec(
                vec![
                    format!("addr <== wrap({rs} + {off});"),
                    format!("{rd} <== mload();"),
                ],
                rd,
            )
        }
        "lb" => {
            // load byte and sign-extend. the memory is little-endian.
            let (rd, rs, off) = rro(args);
            only_if_no_write_to_zero_vec(
                vec![
                    format!("tmp1 <== wrap({rs} + {off});"),
                    "addr <== and(tmp1, 0xfffffffc);".to_string(),
                    "tmp2 <== and(tmp1, 0x3);".to_string(),
                    format!("{rd} <== mload();"),
                    format!("{rd} <== shr({rd}, 8 * tmp2);"),
                    format!("{rd} <== sign_extend_byte({rd});"),
                ],
                rd,
            )
        }
        "lbu" => {
            // load byte and zero-extend. the memory is little-endian.
            let (rd, rs, off) = rro(args);
            only_if_no_write_to_zero_vec(
                vec![
                    format!("tmp1 <== wrap({rs} + {off});"),
                    "addr <== and(tmp1, 0xfffffffc);".to_string(),
                    "tmp2 <== and(tmp1, 0x3);".to_string(),
                    format!("{rd} <== mload();"),
                    format!("{rd} <== shr({rd}, 8 * tmp2);"),
                    format!("{rd} <== and({rd}, 0xff);"),
                ],
                rd,
            )
        }
        "lhu" => {
            // Load two bytes and zero-extend.
            // Assumes the address is a multiple of two.
            let (rd, rs, off) = rro(args);
            only_if_no_write_to_zero_vec(
                vec![
                    format!("tmp1 <== wrap({rs} + {off});"),
                    "addr <== and(tmp1, 0xfffffffc);".to_string(),
                    "tmp2 <== and(tmp1, 0x3);".to_string(),
                    format!("{rd} <== mload();"),
                    format!("{rd} <== shr({rd}, 8 * tmp2);"),
                    format!("{rd} <== and({rd}, 0x0000ffff);"),
                ],
                rd,
            )
        }
        "sw" => {
            let (r1, r2, off) = rro(args);
            vec![
                format!("addr <== wrap({r2} + {off});"),
                format!("mstore {r1};"),
            ]
        }
        "sh" => {
            // store half word (two bytes)
            // TODO this code assumes it is at least aligned on
            // a two-byte boundary

            let (rs, rd, off) = rro(args);
            vec![
                format!("tmp1 <== wrap({rd} + {off});"),
                "addr <== and(tmp1, 0xfffffffc);".to_string(),
                "tmp2 <== and(tmp1, 0x3);".to_string(),
                "tmp1 <== mload();".to_string(),
                "tmp3 <== shl(0xffff, 8 * tmp2);".to_string(),
                "tmp3 <== xor(tmp3, 0xffffffff);".to_string(),
                "tmp1 <== and(tmp1, tmp3);".to_string(),
                format!("tmp3 <== and({rs}, 0xffff);"),
                "tmp3 <== shl(tmp3, 8 * tmp2);".to_string(),
                "tmp1 <== or(tmp1, tmp3);".to_string(),
                "mstore tmp1;".to_string(),
            ]
        }
        "sb" => {
            // store byte
            let (rs, rd, off) = rro(args);
            vec![
                format!("tmp1 <== wrap({rd} + {off});"),
                "addr <== and(tmp1, 0xfffffffc);".to_string(),
                "tmp2 <== and(tmp1, 0x3);".to_string(),
                "tmp1 <== mload();".to_string(),
                "tmp3 <== shl(0xff, 8 * tmp2);".to_string(),
                "tmp3 <== xor(tmp3, 0xffffffff);".to_string(),
                "tmp1 <== and(tmp1, tmp3);".to_string(),
                format!("tmp3 <== and({rs}, 0xff);"),
                "tmp3 <== shl(tmp3, 8 * tmp2);".to_string(),
                "tmp1 <== or(tmp1, tmp3);".to_string(),
                "mstore tmp1;".to_string(),
            ]
        }
        "nop" => vec![],
        "unimp" => vec!["fail;".to_string()],

        // Special instruction that is inserted to allow dynamic label references
        "load_dynamic" => {
            let (rd, label) = rl(args);
            only_if_no_write_to_zero(format!("{rd} <== load_label({label});"), rd)
        }

        _ => {
            panic!("Unknown instruction: {instr}");
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_remove_matching_and_next_integers() {
        assert_eq!(
            remove_matching_and_next([0, 1, 2, 0, 2, 0, 0, 3, 2, 1].iter(), |&&i| { i == 0 })
                .copied()
                .collect::<Vec<_>>(),
            vec![2, 2, 1]
        );
    }

    #[test]
    fn test_remove_matching_and_next_strings() {
        assert_eq!(
            remove_matching_and_next(
                [
                    "croissant",
                    "pain au chocolat",
                    "chausson aux pommes",
                    "croissant" // corner case: if the label is at the end of the program
                ]
                .iter(),
                |&&s| { s == "croissant" }
            )
            .copied()
            .collect::<Vec<_>>(),
            vec!["chausson aux pommes"]
        );
    }
}
