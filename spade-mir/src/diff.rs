use rustc_hash::FxHashMap as HashMap;
use spade_common::id_tracker::ExprID;

use crate::{Entity, MirInput, Register, Statement, ValueName};

macro_rules! check {
    ($cond:expr) => {
        if !($cond) {
            return false;
        }
    };
}

/// Functions for diffing and comparing mir code while ignoring exact variable IDs

pub struct VarMap {
    pub expr_map: HashMap<ExprID, ExprID>,
    pub expr_map_rev: HashMap<ExprID, ExprID>,
    pub name_map: HashMap<u64, u64>,
    pub name_map_rev: HashMap<u64, u64>,
}

impl Default for VarMap {
    fn default() -> Self {
        Self::new()
    }
}

impl VarMap {
    pub fn new() -> Self {
        Self {
            expr_map: HashMap::default(),
            expr_map_rev: HashMap::default(),
            name_map: HashMap::default(),
            name_map_rev: HashMap::default(),
        }
    }

    pub fn map_expr(&mut self, lhs: ExprID, rhs: ExprID) {
        self.expr_map.insert(lhs, rhs);
        self.expr_map_rev.insert(rhs, lhs);
    }

    pub fn map_name(&mut self, lhs: u64, rhs: u64) {
        self.name_map.insert(lhs, rhs);
        self.name_map_rev.insert(rhs, lhs);
    }

    fn try_update_name(&mut self, lhs: &ValueName, rhs: &ValueName) -> Result<(), ()> {
        // Update the name if both are the same kind
        match (lhs, rhs) {
            (ValueName::Named(i1, n1, _), ValueName::Named(i2, n2, _)) => {
                if n1 != n2 {
                    Err(())
                } else {
                    self.map_name(*i1, *i2);
                    Ok(())
                }
            }
            (ValueName::Expr(i1), ValueName::Expr(i2)) => {
                self.map_expr(*i1, *i2);
                Ok(())
            }
            _ => Err(()),
        }
    }

    fn compare_name(
        &self,
        (lhs_id, lhs_name): (&u64, &str),
        (rhs_id, rhs_name): (&u64, &str),
    ) -> bool {
        if lhs_name != rhs_name {
            return false;
        }

        self.name_map
            .get(lhs_id)
            .map(|v| rhs_id == v)
            .unwrap_or(false)
    }

    fn compare_exprs(&self, lhs: ExprID, rhs: ExprID) -> bool {
        self.expr_map.get(&lhs).map(|v| v == &rhs).unwrap_or(false)
    }

    pub fn compare_vals(&self, lhs: &ValueName, rhs: &ValueName) -> bool {
        match (lhs, rhs) {
            (ValueName::Named(i1, n1, _), ValueName::Named(i2, n2, _)) => {
                self.compare_name((i1, n1), (i2, n2))
            }
            (ValueName::Expr(i1), ValueName::Expr(i2)) => self.compare_exprs(*i1, *i2),
            _ => false,
        }
    }
}

/// Compare statements, if they match, add the new mapping to the mapping table
fn compare_statements(s1: &Statement, s2: &Statement, var_map: &mut VarMap) -> bool {
    macro_rules! check_name {
        ($lhs:expr, $rhs:expr) => {
            if !var_map.compare_vals($lhs, $rhs) {
                return false;
            }
        };
    }
    match (s1, s2) {
        (Statement::Binding(b1), Statement::Binding(b2)) => {
            // Compare the types and operators

            if b1.ty != b2.ty {
                return false;
            }
            if b1.operator != b2.operator {
                return false;
            }
            if b1.operands.len() != b2.operands.len() {
                return false;
            }
            // Check the params
            for (n1, n2) in b1.operands.iter().zip(b2.operands.iter()) {
                check_name!(n1, n2)
            }

            true
        }
        (Statement::Register(r1), Statement::Register(r2)) => {
            let Register {
                name: _,
                ty: ty1,
                clock: clock1,
                reset: reset1,
                initial: initial1,
                value: value1,
                loc: _,
                traced: _,
            } = &r1;
            let Register {
                name: _,
                ty: ty2,
                clock: clock2,
                reset: reset2,
                initial: initial2,
                value: value2,
                loc: _,
                traced: _,
            } = &r2;
            if ty1 != ty2 {
                return false;
            }

            check_name!(value1, value2);
            check_name!(clock1, clock2);

            match (reset1, reset2) {
                (Some((t1, v1)), Some((t2, v2))) => {
                    check_name!(t1, t2);
                    check_name!(v1, v2);
                }
                (None, None) => {}
                _ => return false,
            }

            match (initial1, initial2) {
                (Some(l), Some(r)) => {
                    if l != r {
                        return false;
                    }
                }
                (None, None) => {}
                _ => return false,
            }

            true
        }
        (Statement::Constant(_, t1, v1), Statement::Constant(_, t2, v2)) => {
            if t1 != t2 {
                return false;
            }
            if v1 != v2 {
                return false;
            }
            true
        }
        (Statement::Assert(v1), Statement::Assert(v2)) => {
            check_name!(v1, v2);
            true
        }
        (
            Statement::Set {
                target: tl,
                value: vl,
            },
            Statement::Set {
                target: tr,
                value: vr,
            },
        ) => {
            check_name!(tl, tr);
            check_name!(vl, vr);
            true
        }
        (
            Statement::WalTrace {
                name: n1,
                val: v1,
                suffix: s1,
                ty: ty1,
            },
            Statement::WalTrace {
                name: n2,
                val: v2,
                suffix: s2,
                ty: ty2,
            },
        ) => {
            check_name!(n1, n2);
            check_name!(v1, v2);
            if s1 != s2 {
                return false;
            }
            if ty1 != ty2 {
                return false;
            }
            true
        }
        _ => false,
    }
}

fn populate_var_map(
    stmts1: &[Statement],
    stmts2: &[Statement],
    var_map: &mut VarMap,
) -> Result<(), ()> {
    // Check if two names can be the same by comparing the string names of ValueName::Named.
    // If they are the same, merge them and return true
    stmts1
        .iter()
        .zip(stmts2.iter())
        .try_for_each(|(s1, s2)| match (s1, s2) {
            (Statement::Binding(b1), Statement::Binding(b2)) => {
                var_map.try_update_name(&b1.name, &b2.name)
            }
            (Statement::Register(r1), Statement::Register(r2)) => {
                var_map.try_update_name(&r1.name, &r2.name)
            }
            (Statement::Constant(e1, _, _), Statement::Constant(e2, _, _)) => {
                var_map.try_update_name(&ValueName::Expr(*e1), &ValueName::Expr(*e2))
            }
            (Statement::WalTrace { .. }, Statement::WalTrace { .. }) => Ok(()),
            (Statement::Assert(_), Statement::Assert(_)) => Ok(()),
            (Statement::Set { .. }, Statement::Set { .. }) => Ok(()),
            _ => Err(()),
        })
}

pub fn compare_entity(e1: &Entity, e2: &Entity, var_map: &mut VarMap) -> bool {
    check!(e1.name == e2.name);
    check!(e1.output_type == e2.output_type);

    for (
        MirInput {
            name: n1,
            val_name: vn1,
            ty: t1,
            no_mangle: nm1,
        },
        MirInput {
            name: n2,
            val_name: vn2,
            ty: t2,
            no_mangle: nm2,
        },
    ) in e1.inputs.iter().zip(e2.inputs.iter())
    {
        check!(nm1 == nm2);
        check!(n1 == n2);
        check!(var_map.try_update_name(vn1, vn2).is_ok());
        check!(t1 == t2);
    }

    if populate_var_map(&e1.statements, &e2.statements, var_map).is_err() {
        return false;
    }

    for (s1, s2) in e1.statements.iter().zip(e2.statements.iter()) {
        check!(compare_statements(s1, s2, var_map))
    }
    check!(e1.statements.len() == e2.statements.len());

    check!(var_map.compare_vals(&e1.output, &e2.output));

    true
}

#[cfg(test)]
mod statement_comparison_tests {
    use super::*;

    use crate::{statement, types::Type, ConstantValue};

    use crate as spade_mir;

    #[test]
    fn identical_bindings_update_expr_map() {
        let mut map = VarMap::new();

        map.map_expr(ExprID(1), ExprID(2));
        map.map_name(2, 3);

        let lhs = statement!(e(0); Type::int(5); Add; e(1), n(2, "test"));
        let rhs = statement!(e(3); Type::int(5); Add; e(2), n(3, "test"));

        populate_var_map(&vec![lhs.clone()], &vec![rhs.clone()], &mut map).unwrap();
        assert!(compare_statements(&lhs, &rhs, &mut map));

        assert!(map.compare_exprs(ExprID(0), ExprID(3)))
    }

    #[test]
    fn identical_bindings_update_name_map() {
        let mut map = VarMap::new();

        map.map_expr(ExprID(1), ExprID(2));
        map.map_name(2, 3);

        let lhs = statement!(n(0, "a"); Type::int(5); Add; e(1), n(2, "test"));
        let rhs = statement!(n(3, "a"); Type::int(5); Add; e(2), n(3, "test"));

        populate_var_map(&vec![lhs.clone()], &vec![rhs.clone()], &mut map).unwrap();
        assert!(compare_statements(&lhs, &rhs, &mut map));

        assert!(map.compare_name((&0, "a"), (&3, "a")))
    }

    #[test]
    fn identical_bindings_with_differing_string_name_diff() {
        let mut map = VarMap::new();

        map.map_expr(ExprID(1), ExprID(2));
        map.map_name(2, 3);

        let lhs = statement!(n(0, "a"); Type::int(5); Add; e(1), n(2, "test"));
        let rhs = statement!(n(3, "b"); Type::int(5); Add; e(2), n(3, "test"));

        assert!(populate_var_map(&vec![lhs.clone()], &vec![rhs.clone()], &mut map).is_err());
    }

    #[test]
    fn bindings_with_mismatched_types_are_different() {
        let mut map = VarMap::new();

        map.map_expr(ExprID(1), ExprID(1));
        map.map_expr(ExprID(2), ExprID(2));

        let lhs = statement!(e(0); Type::int(5); Add; e(1), e(2));
        let rhs = statement!(e(3); Type::int(4); Add; e(1), e(2));

        populate_var_map(&vec![lhs.clone()], &vec![rhs.clone()], &mut map).unwrap();

        assert!(!compare_statements(&lhs, &rhs, &mut map));
    }

    #[test]
    fn bindings_with_mismatched_operators_are_different() {
        let mut map = VarMap::new();

        map.map_expr(ExprID(1), ExprID(1));
        map.map_expr(ExprID(2), ExprID(2));

        let lhs = statement!(e(0); Type::int(5); Add; e(1), e(2));
        let rhs = statement!(e(3); Type::int(5); Select; e(1), e(2));

        populate_var_map(&vec![lhs.clone()], &vec![rhs.clone()], &mut map).unwrap();

        assert!(!compare_statements(&lhs, &rhs, &mut map));
    }

    #[test]
    fn bindings_with_mismatched_operands_are_different() {
        let mut map = VarMap::new();

        map.map_expr(ExprID(1), ExprID(1));
        map.map_expr(ExprID(2), ExprID(2));

        let lhs = statement!(e(0); Type::int(5); Add; e(2), e(1));
        let rhs = statement!(e(3); Type::int(5); Add; e(1), e(2));

        populate_var_map(&vec![lhs.clone()], &vec![rhs.clone()], &mut map).unwrap();

        assert!(!compare_statements(&lhs, &rhs, &mut map));
    }

    #[test]
    fn bindings_with_unmapped_names_are_different() {
        let mut map = VarMap::new();

        map.map_expr(ExprID(1), ExprID(1));
        map.map_expr(ExprID(2), ExprID(2));

        let lhs = statement!(e(0); Type::int(5); Add; e(2), e(1));
        let rhs = statement!(e(3); Type::int(5); Add; e(1), e(3));

        populate_var_map(&vec![lhs.clone()], &vec![rhs.clone()], &mut map).unwrap();

        assert!(!compare_statements(&lhs, &rhs, &mut map));
    }

    // Register tests
    #[test]
    fn identical_registers_with_reset_do_not_diff() {
        let mut map = VarMap::new();

        map.map_expr(ExprID(1), ExprID(1));
        map.map_expr(ExprID(2), ExprID(2));
        map.map_expr(ExprID(3), ExprID(3));
        map.map_expr(ExprID(4), ExprID(4));

        let lhs = statement!(reg e(0); Type::int(5); clock(e(2)); reset(e(3), e(4)); e(1));
        let rhs = statement!(reg e(5); Type::int(5); clock(e(2)); reset(e(3), e(4)); e(1));

        populate_var_map(&vec![lhs.clone()], &vec![rhs.clone()], &mut map).unwrap();

        assert!(compare_statements(&lhs, &rhs, &mut map));
    }

    #[test]
    fn identical_registers_with_reset_do_not_diff_and_update_names() {
        let mut map = VarMap::new();

        map.map_expr(ExprID(1), ExprID(1));
        map.map_expr(ExprID(2), ExprID(2));
        map.map_expr(ExprID(3), ExprID(3));
        map.map_expr(ExprID(4), ExprID(4));

        let lhs = statement!(reg e(0); Type::int(5); clock(e(2)); reset(e(3), e(4)); e(1));
        let rhs = statement!(reg e(5); Type::int(5); clock(e(2)); reset(e(3), e(4)); e(1));

        populate_var_map(&vec![lhs.clone()], &vec![rhs.clone()], &mut map).unwrap();

        assert!(compare_statements(&lhs, &rhs, &mut map));

        assert!(map.compare_exprs(ExprID(0), ExprID(5)));
    }

    #[test]
    fn identical_registers_update_name_table() {
        let mut map = VarMap::new();

        map.map_expr(ExprID(1), ExprID(1));
        map.map_expr(ExprID(2), ExprID(2));
        map.map_expr(ExprID(3), ExprID(3));
        map.map_expr(ExprID(4), ExprID(4));

        let lhs = statement!(reg n(0, "test"); Type::int(5); clock(e(2)); reset(e(3), e(4)); e(1));
        let rhs = statement!(reg n(5, "test"); Type::int(5); clock(e(2)); reset(e(3), e(4)); e(1));

        populate_var_map(&vec![lhs.clone()], &vec![rhs.clone()], &mut map).unwrap();

        assert!(compare_statements(&lhs, &rhs, &mut map));

        assert!(map.compare_name((&0, "test"), (&5, "test")));
    }

    #[test]
    fn mismatched_register_clocks_causes_a_diff() {
        let mut map = VarMap::new();

        map.map_expr(ExprID(1), ExprID(1));
        map.map_expr(ExprID(2), ExprID(2));
        map.map_expr(ExprID(3), ExprID(3));
        map.map_expr(ExprID(4), ExprID(4));

        let lhs = statement!(reg e(0); Type::int(5); clock(e(3)); reset(e(3), e(4)); e(1));
        let rhs = statement!(reg e(0); Type::int(5); clock(e(2)); reset(e(3), e(4)); e(1));

        populate_var_map(&vec![lhs.clone()], &vec![rhs.clone()], &mut map).unwrap();

        assert!(!compare_statements(&lhs, &rhs, &mut map));
    }

    #[test]
    fn mismatched_register_reset_trig_causes_a_diff() {
        let mut map = VarMap::new();

        map.map_expr(ExprID(1), ExprID(1));
        map.map_expr(ExprID(2), ExprID(2));
        map.map_expr(ExprID(3), ExprID(3));
        map.map_expr(ExprID(4), ExprID(4));

        let lhs = statement!(reg e(0); Type::int(5); clock(e(3)); reset(e(3), e(4)); e(1));
        let rhs = statement!(reg e(0); Type::int(5); clock(e(3)); reset(e(2), e(4)); e(1));

        populate_var_map(&vec![lhs.clone()], &vec![rhs.clone()], &mut map).unwrap();

        assert!(!compare_statements(&lhs, &rhs, &mut map));
    }

    #[test]
    fn mismatched_register_value_causes_diff() {
        let mut map = VarMap::new();

        map.map_expr(ExprID(1), ExprID(1));
        map.map_expr(ExprID(2), ExprID(2));
        map.map_expr(ExprID(3), ExprID(3));
        map.map_expr(ExprID(4), ExprID(4));

        let lhs = statement!(reg e(0); Type::int(5); clock(e(2)); reset(e(3), e(4)); e(1));
        let rhs = statement!(reg e(0); Type::int(5); clock(e(2)); reset(e(3), e(5)); e(1));

        populate_var_map(&vec![lhs.clone()], &vec![rhs.clone()], &mut map).unwrap();

        assert!(!compare_statements(&lhs, &rhs, &mut map));
    }

    #[test]
    fn identical_registers_with_mismatched_value_diff() {
        let mut map = VarMap::new();

        map.map_expr(ExprID(1), ExprID(1));
        map.map_expr(ExprID(2), ExprID(2));
        map.map_expr(ExprID(3), ExprID(3));
        map.map_expr(ExprID(4), ExprID(4));

        let lhs = statement!(reg e(0); Type::int(5); clock(e(2)); reset(e(3), e(4)); e(1));
        let rhs = statement!(reg e(0); Type::int(5); clock(e(2)); reset(e(3), e(4)); e(2));

        populate_var_map(&vec![lhs.clone()], &vec![rhs.clone()], &mut map).unwrap();

        assert!(!compare_statements(&lhs, &rhs, &mut map));
    }

    #[test]
    fn identical_registers_with_mismatched_initial_diff() {
        let mut map = VarMap::new();

        map.map_expr(ExprID(1), ExprID(1));
        map.map_expr(ExprID(2), ExprID(2));
        map.map_expr(ExprID(3), ExprID(3));
        map.map_expr(ExprID(4), ExprID(4));

        let lhs = statement!(reg e(0); Type::int(5); clock(e(2)); reset(e(3), e(4)) initial(vec![statement!(e(0); Type::Bool; Alias; e(3))]); e(1));
        let rhs = statement!(reg e(0); Type::int(5); clock(e(2)); reset(e(3), e(4)) initial(vec![statement!(e(0); Type::Bool; Alias; e(2))]); e(1));

        populate_var_map(&vec![lhs.clone()], &vec![rhs.clone()], &mut map).unwrap();

        assert!(!compare_statements(&lhs, &rhs, &mut map));
    }

    #[test]
    fn identical_registers_with_initial_is_different_from_without() {
        let mut map = VarMap::new();

        map.map_expr(ExprID(1), ExprID(1));
        map.map_expr(ExprID(2), ExprID(2));
        map.map_expr(ExprID(3), ExprID(3));
        map.map_expr(ExprID(4), ExprID(4));

        let lhs = statement!(reg e(0); Type::int(5); clock(e(2)); reset(e(3), e(4)); e(1));
        let rhs = statement!(reg e(0); Type::int(5); clock(e(2)); reset(e(3), e(4)) initial(vec![statement!(e(0); Type::Bool; Alias; e(2))]); e(1));

        populate_var_map(&vec![lhs.clone()], &vec![rhs.clone()], &mut map).unwrap();

        assert!(!compare_statements(&lhs, &rhs, &mut map));
    }

    #[test]
    fn missing_register_causes_a_diff() {
        let mut map = VarMap::new();

        map.map_expr(ExprID(1), ExprID(1));
        map.map_expr(ExprID(2), ExprID(2));
        map.map_expr(ExprID(3), ExprID(3));
        map.map_expr(ExprID(4), ExprID(4));

        let lhs = statement!(reg e(0); Type::int(5); clock(e(2)); reset(e(3), e(4)); e(1));
        let rhs = statement!(reg e(0); Type::int(5); clock(e(2)); e(1));

        populate_var_map(&vec![lhs.clone()], &vec![rhs.clone()], &mut map).unwrap();

        assert!(!compare_statements(&lhs, &rhs, &mut map));
    }

    #[test]
    fn mismatched_types_causes_register_diff() {
        let mut map = VarMap::new();

        map.map_expr(ExprID(1), ExprID(1));
        map.map_expr(ExprID(2), ExprID(2));
        map.map_expr(ExprID(3), ExprID(3));
        map.map_expr(ExprID(4), ExprID(4));

        let lhs = statement!(reg e(0); Type::int(6); clock(e(2)); reset(e(3), e(4)); e(1));
        let rhs = statement!(reg e(5); Type::int(5); clock(e(2)); reset(e(3), e(4)); e(1));

        populate_var_map(&vec![lhs.clone()], &vec![rhs.clone()], &mut map).unwrap();

        assert!(!compare_statements(&lhs, &rhs, &mut map));
    }

    // Constants

    #[test]
    fn identical_constants_match() {
        let mut map = VarMap::new();

        let lhs = statement!(const 0; Type::int(5); ConstantValue::int(10));
        let rhs = statement!(const 0; Type::int(5); ConstantValue::int(10));

        populate_var_map(&vec![lhs.clone()], &vec![rhs.clone()], &mut map).unwrap();

        assert!(compare_statements(&lhs, &rhs, &mut map));
    }

    #[test]
    fn identical_constants_update_expressions() {
        let mut map = VarMap::new();

        let lhs = statement!(const 0; Type::int(5); ConstantValue::int(10));
        let rhs = statement!(const 1; Type::int(5); ConstantValue::int(10));

        populate_var_map(&vec![lhs.clone()], &vec![rhs.clone()], &mut map).unwrap();

        assert!(compare_statements(&lhs, &rhs, &mut map));

        assert!(map.compare_exprs(ExprID(0), ExprID(1)));
    }

    #[test]
    fn constant_type_mismatch_diff() {
        let mut map = VarMap::new();

        let lhs = statement!(const 0; Type::int(6); ConstantValue::int(10));
        let rhs = statement!(const 0; Type::int(5); ConstantValue::int(10));

        populate_var_map(&vec![lhs.clone()], &vec![rhs.clone()], &mut map).unwrap();

        assert!(!compare_statements(&lhs, &rhs, &mut map));
    }

    #[test]
    fn constant_value_mismatch_diff() {
        let mut map = VarMap::new();

        let lhs = statement!(const 0; Type::int(5); ConstantValue::int(11));
        let rhs = statement!(const 0; Type::int(5); ConstantValue::int(10));

        populate_var_map(&vec![lhs.clone()], &vec![rhs.clone()], &mut map).unwrap();

        assert!(!compare_statements(&lhs, &rhs, &mut map));
    }

    #[test]
    fn constant_value_type_mismatch_diff() {
        let mut map = VarMap::new();

        let lhs = statement!(const 0; Type::int(5); ConstantValue::Bool(false));
        let rhs = statement!(const 0; Type::int(5); ConstantValue::int(10));

        populate_var_map(&vec![lhs.clone()], &vec![rhs.clone()], &mut map).unwrap();

        assert!(!compare_statements(&lhs, &rhs, &mut map));
    }
}

#[cfg(test)]
mod entity_comparison_tests {
    use super::*;

    use crate as spade_mir;
    use crate::{entity, Type};

    #[test]
    fn identical_entities_have_no_diff() {
        let mut var_map = VarMap::new();
        var_map.map_name(1, 1);
        let lhs = entity!("pong"; ("_i_clk", n(0, "clk"), Type::Bool) -> Type::int(6); {
        } => n(1, "value"));
        let rhs = entity!("pong"; ("_i_clk", n(0, "clk"), Type::Bool) -> Type::int(6); {
        } => n(1, "value"));

        assert!(compare_entity(&lhs, &rhs, &mut var_map));
    }

    #[test]
    fn names_are_mapped_for_inputs() {
        let mut var_map = VarMap::new();
        var_map.map_name(1, 1);

        let lhs = entity!("pong"; ("_i_clk", n(0, "clk"), Type::Bool) -> Type::int(6); {
        } => n(1, "value"));
        let rhs = entity!("pong"; ("_i_clk", n(2, "clk"), Type::Bool) -> Type::int(6); {
        } => n(1, "value"));

        assert!(compare_entity(&lhs, &rhs, &mut var_map));

        assert!(var_map.compare_name((&0, "clk"), (&2, "clk")));
    }

    #[test]
    fn mismatched_name_causes_diff() {
        let mut var_map = VarMap::new();
        var_map.map_name(1, 1);

        let lhs = entity!("pong"; ("_i_clk", n(0, "clk"), Type::Bool) -> Type::int(6); {
        } => n(1, "value"));
        let rhs = entity!("not_pong"; ("_i_clk", n(0, "clk"), Type::Bool) -> Type::int(6); {
        } => n(1, "value"));

        assert!(!compare_entity(&lhs, &rhs, &mut var_map));
    }

    #[test]
    fn input_types_must_match() {
        let mut var_map = VarMap::new();
        var_map.map_name(1, 1);

        let lhs = entity!("pong"; ("_i_clk", n(0, "clk"), Type::Bool) -> Type::int(6); {
        } => n(1, "value"));
        let rhs = entity!("pong"; ("_i_clk", n(0, "clk"), Type::int(6)) -> Type::int(6); {
        } => n(1, "value"));

        assert!(!compare_entity(&lhs, &rhs, &mut var_map));
    }

    #[test]
    fn input_name_mismatch() {
        let mut var_map = VarMap::new();
        var_map.map_name(1, 1);

        let lhs = entity!("pong"; ("_i_clk", n(0, "clk"), Type::Bool) -> Type::int(6); {
        } => n(1, "value"));
        let rhs = entity!("pong"; ("_i_not_clk", n(0, "clk"), Type::int(6)) -> Type::int(6); {
        } => n(1, "value"));

        assert!(!compare_entity(&lhs, &rhs, &mut var_map));
    }

    #[test]
    fn input_value_name_mismatch() {
        let mut var_map = VarMap::new();
        var_map.map_name(1, 1);

        let lhs = entity!("pong"; ("_i_clk", n(0, "clk"), Type::Bool) -> Type::int(6); {
        } => n(1, "value"));
        let rhs = entity!("pong"; ("_i_clk", n(0, "not_clk"), Type::int(6)) -> Type::int(6); {
        } => n(1, "value"));

        assert!(!compare_entity(&lhs, &rhs, &mut var_map));
    }

    #[test]
    fn output_type_mismatch_causes_diff() {
        let mut var_map = VarMap::new();
        var_map.map_name(1, 1);

        let lhs = entity!("pong"; ("_i_clk", n(0, "clk"), Type::Bool) -> Type::int(7); {
        } => n(1, "value"));
        let rhs = entity!("pong"; ("_i_clk", n(0, "clk"), Type::Bool) -> Type::int(6); {
        } => n(1, "value"));

        assert!(!compare_entity(&lhs, &rhs, &mut var_map));
    }

    #[test]
    fn output_name_mismatches_are_caught() {
        let mut var_map = VarMap::new();
        var_map.map_name(1, 1);

        let lhs = entity!("pong"; ("_i_clk", n(0, "clk"), Type::Bool) -> Type::int(6); {
        } => e(1));
        let rhs = entity!("pong"; ("_i_clk", n(0, "clk"), Type::Bool) -> Type::int(6); {
        } => e(2));

        assert!(!compare_entity(&lhs, &rhs, &mut var_map));
    }

    #[test]
    fn mismatched_statements_cause_diff() {
        let mut var_map = VarMap::new();
        var_map.map_name(1, 1);

        let lhs = entity!("pong"; ("_i_clk", n(0, "clk"), Type::Bool) -> Type::int(6); {
            (e(0); Type::int(6); Add; n(1, "value"))
        } => n(1, "value"));
        let rhs = entity!("pong"; ("_i_clk", n(0, "clk"), Type::Bool) -> Type::int(6); {
            (e(0); Type::int(7); Add; n(1, "value"))
        } => n(1, "value"));

        assert!(!compare_entity(&lhs, &rhs, &mut var_map));
    }

    #[test]
    fn mismatched_statement_counts_diff() {
        let mut var_map = VarMap::new();
        var_map.map_name(1, 1);

        let lhs = entity!("pong"; ("_i_clk", n(0, "clk"), Type::Bool) -> Type::int(6); {
            (e(0); Type::int(6); Add; n(1, "value"));
            (e(0); Type::int(6); Add; n(1, "value"))
        } => n(1, "value"));
        let rhs = entity!("pong"; ("_i_clk", n(0, "clk"), Type::Bool) -> Type::int(6); {
            (e(0); Type::int(6); Add; n(1, "value"))
        } => n(1, "value"));

        assert!(!compare_entity(&lhs, &rhs, &mut var_map));
    }
}
