use num::ToPrimitive;

use spade_common::id_tracker::ExprIdTracker;

use crate::{types::Type, Binding, Operator, Register, Statement, ValueName};

use super::MirPass;

pub struct SplitCompoundRegs {}

impl MirPass for SplitCompoundRegs {
    fn name(&self) -> &'static str {
        "split_compound_regs"
    }

    fn transform_statements(
        &self,
        stmts: &[Statement],
        expr_idtracker: &mut ExprIdTracker,
    ) -> Vec<Statement> {
        stmts
            .iter()
            .flat_map(|stmt| match stmt {
                Statement::Register(reg) => split_compound_reg(reg, expr_idtracker),
                other => vec![other.clone()],
            })
            .collect()
    }
}

fn generate_split_code(
    reg: &Register,
    members: &Vec<Type>,
    expr_idtracker: &mut ExprIdTracker,
) -> Vec<Statement> {
    let (reg_names, split_stmts): (Vec<_>, Vec<_>) = members
        .iter()
        .enumerate()
        .map(|(i, member)| {
            let split_name = ValueName::Expr(expr_idtracker.next());
            let reg_name = ValueName::Expr(expr_idtracker.next());
            let split_stmt = Statement::Binding(Binding {
                name: split_name.clone(),
                operator: Operator::IndexTuple(i as u64, members.clone()),
                operands: vec![reg.value.clone()],
                ty: member.clone(),
                loc: None,
            });

            let reg_stmts = split_compound_reg(
                &Register {
                    name: reg_name.clone(),
                    ty: member.clone(),
                    clock: reg.clock.clone(),
                    reset: reg.reset.clone(),
                    initial: None,
                    value: split_name.clone(),
                    loc: None,
                    traced: None,
                },
                expr_idtracker,
            );

            let split_stmts = vec![split_stmt]
                .into_iter()
                .chain(reg_stmts)
                .collect::<Vec<_>>();

            (reg_name, split_stmts)
        })
        .unzip();

    let new_compound = Statement::Binding(Binding {
        name: reg.name.clone(),
        operator: Operator::ConstructTuple,
        operands: reg_names,
        ty: reg.ty.clone(),
        loc: None,
    });

    split_stmts
        .into_iter()
        .flatten()
        .chain(vec![new_compound])
        .collect()
}

fn split_compound_reg(reg: &Register, expr_idtracker: &mut ExprIdTracker) -> Vec<Statement> {
    if reg.initial.is_some() {
        return vec![Statement::Register(reg.clone())];
    }

    match &reg.ty {
        Type::Int(_)
        | Type::UInt(_)
        | Type::Bool
        | Type::InOut(_)
        | Type::Enum(_)
        | Type::Backward(_)
        | Type::Memory { .. } => vec![Statement::Register(reg.clone())],
        Type::Tuple(members) => generate_split_code(reg, members, expr_idtracker),
        Type::Struct(members) => generate_split_code(
            reg,
            &members.iter().map(|(_, ty)| ty.clone()).collect(),
            expr_idtracker,
        ),
        // NOTE: Arrays are currently split as if they were tuples. This means that
        // things will be a bit weird in the MIR, but it does make codegen for all this
        // much easier as it doesn't require generating array indices as runtime constants.
        Type::Array { inner, length } => {
            if let Some(length) = length.to_usize() {
                generate_split_code(
                    reg,
                    &(0..(length)).map(|_| *inner.clone()).collect::<_>(),
                    expr_idtracker,
                )
            } else {
                vec![Statement::Register(reg.clone())]
            }
        }
    }
}

#[cfg(test)]
mod test {
    use colored::Colorize;

    use spade_common::id_tracker::ExprIdTracker;

    use super::SplitCompoundRegs;
    use crate::passes::MirPass;
    use crate::{self as spade_mir, assert_same_mir};
    use crate::{entity, types::Type};

    #[test]
    fn splitting_tuple_works() {
        let members = vec![Type::int(4), Type::int(8)];
        let ty = Type::Tuple(vec![Type::int(4), Type::int(8)]);

        let before = entity!("pong"; ("_i_clk", n(0, "clk"), Type::Bool, "val", n(2, "val"), ty.clone()) -> Type::int(6); {
            (reg n(1, "value"); ty.clone(); clock (n(0, "clk")); n(2, "val"));
        } => n(1, "value"));

        let pass = SplitCompoundRegs {};
        let mut after = before.clone();
        after.statements =
            pass.transform_statements(&before.statements, &mut ExprIdTracker::new_at(100));

        let expected = entity!("pong"; ("_i_clk", n(0, "clk"), Type::Bool, "val", n(2, "val"), ty.clone()) -> Type::int(6); {
            (e(10); Type::int(4); IndexTuple((0, members.clone())); n(2, "val"));
            (reg e(11); Type::int(4); clock (n(0, "clk")); e(10));
            (e(20); Type::int(8); IndexTuple((1, members.clone())); n(2, "val"));
            (reg e(21); Type::int(8); clock (n(0, "clk")); e(20));

            (n(1, "value"); ty; ConstructTuple; e(11), e(21));
        } => n(1, "value"));

        assert_same_mir!(&after, &expected);
    }

    #[test]
    fn splitting_struct_works() {
        let members = vec![Type::int(4), Type::int(8)];
        let ty = Type::Struct(vec![
            ("a".to_string(), Type::int(4)),
            ("b".to_string(), Type::int(8)),
        ]);

        let before = entity!("pong"; ("_i_clk", n(0, "clk"), Type::Bool, "val", n(2, "val"), ty.clone()) -> Type::int(6); {
            (reg n(1, "value"); ty.clone(); clock (n(0, "clk")); n(2, "val"));
        } => n(1, "value"));

        let pass = SplitCompoundRegs {};
        let mut after = before.clone();
        after.statements =
            pass.transform_statements(&before.statements, &mut ExprIdTracker::new_at(100));

        let expected = entity!("pong"; ("_i_clk", n(0, "clk"), Type::Bool, "val", n(2, "val"), ty.clone()) -> Type::int(6); {
            (e(10); Type::int(4); IndexTuple((0, members.clone())); n(2, "val"));
            (reg e(11); Type::int(4); clock (n(0, "clk")); e(10));
            (e(20); Type::int(8); IndexTuple((1, members.clone())); n(2, "val"));
            (reg e(21); Type::int(8); clock (n(0, "clk")); e(20));

            (n(1, "value"); ty; ConstructTuple; e(11), e(21));
        } => n(1, "value"));

        assert_same_mir!(&after, &expected);
    }

    #[test]
    fn splitting_compound_compounds_works() {
        let inner_members = vec![Type::int(4), Type::int(8)];
        let inner_ty = Type::Tuple(inner_members.clone());
        let members = vec![Type::int(4), inner_ty.clone()];
        let ty = Type::Tuple(members.clone());

        let before = entity!("pong"; ("_i_clk", n(0, "clk"), Type::Bool, "val", n(2, "val"), ty.clone()) -> Type::int(6); {
            (reg n(1, "value"); ty.clone(); clock (n(0, "clk")); n(2, "val"));
        } => n(1, "value"));

        let pass = SplitCompoundRegs {};
        let mut after = before.clone();
        after.statements =
            pass.transform_statements(&before.statements, &mut ExprIdTracker::new_at(100));

        let expected = entity!("pong"; ("_i_clk", n(0, "clk"), Type::Bool, "val", n(2, "val"), ty.clone()) -> Type::int(6); {
            (e(10); Type::int(4); IndexTuple((0, members.clone())); n(2, "val"));
            (reg e(11); Type::int(4); clock (n(0, "clk")); e(10));
            (e(20); inner_ty.clone(); IndexTuple((1, members.clone())); n(2, "val"));

            (e(30); Type::int(4); IndexTuple((0, inner_members.clone())); e(20));
            (reg e(31); Type::int(4); clock (n(0, "clk")); e(30));
            (e(40); Type::int(8); IndexTuple((1, inner_members.clone())); e(20));
            (reg e(41); Type::int(8); clock (n(0, "clk")); e(40));

            (e(21); inner_ty; ConstructTuple; e(31), e(41));

            (n(1, "value"); ty; ConstructTuple; e(11), e(21));
        } => n(1, "value"));

        assert_same_mir!(&after, &expected);
    }
}
