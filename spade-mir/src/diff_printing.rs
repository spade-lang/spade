/// Utilities for printing the difference between two mir blocks with their var mappings.
///
/// Names are formatted as e(<left hand side> | <right hand side>) and the corresponding name is
/// looked up from the specified hash map depending on which side we're printing. This allows some
/// nice text-based diffs, but does require the use of quite a few generic parameters since we need
/// to either look up names in a hash map, or just use the given name.
use std::collections::HashMap;

use crate::{diff::VarMap, Entity};
use crate::{Binding, Register, Statement, ValueName};

pub fn translate_expr(
    name: u64,
    lhs_trans: &impl Fn(u64) -> Option<u64>,
    rhs_trans: &impl Fn(u64) -> Option<u64>,
) -> String {
    let lhs = lhs_trans(name)
        .map(|n| format!("{}", n))
        .unwrap_or_else(|| "?".to_string());
    let rhs = rhs_trans(name)
        .map(|n| format!("{}", n))
        .unwrap_or_else(|| "?".to_string());

    format!("e({}|{})", lhs, rhs)
}

pub fn translate_name(
    (id, name): (u64, &str),
    lhs_trans: &impl Fn(u64) -> Option<u64>,
    rhs_trans: &impl Fn(u64) -> Option<u64>,
) -> String {
    let lhs = lhs_trans(id)
        .map(|i| format!("{}", i))
        .unwrap_or_else(|| "?".to_string());
    let rhs = rhs_trans(id)
        .map(|i| format!("{}", i))
        .unwrap_or_else(|| "?".to_string());

    format!("n({}|{}, {})", lhs, rhs, name)
}

pub struct NameTranslator<F, G>
where
    F: Fn(u64) -> Option<u64>,
    G: Fn(u64) -> Option<u64>,
{
    expr: F,
    name: G,
}

pub fn identity_name_translator(
) -> NameTranslator<impl Fn(u64) -> Option<u64>, impl Fn(u64) -> Option<u64>> {
    NameTranslator {
        expr: Some,
        name: Some,
    }
}

pub fn map_name_translator(
    expr: HashMap<u64, u64>,
    name: HashMap<u64, u64>,
) -> NameTranslator<impl Fn(u64) -> Option<u64>, impl Fn(u64) -> Option<u64>> {
    NameTranslator {
        expr: move |x| expr.get(&x).cloned(),
        name: move |x| name.get(&x).cloned(),
    }
}

pub fn translate_val_name<LF, LG, RF, RG>(
    name: &ValueName,
    lhs_trans: &NameTranslator<LF, LG>,
    rhs_trans: &NameTranslator<RF, RG>,
) -> String
where
    LF: Fn(u64) -> Option<u64>,
    LG: Fn(u64) -> Option<u64>,
    RF: Fn(u64) -> Option<u64>,
    RG: Fn(u64) -> Option<u64>,
{
    match name {
        ValueName::Named(id, n) => translate_name((*id, n), &lhs_trans.name, &rhs_trans.name),
        ValueName::Expr(id) => translate_expr(*id, &lhs_trans.expr, &rhs_trans.expr),
    }
}

pub fn translate_statement<LF, LG, RF, RG>(
    statement: &Statement,
    lhs_trans: &NameTranslator<LF, LG>,
    rhs_trans: &NameTranslator<RF, RG>,
) -> String
where
    LF: Fn(u64) -> Option<u64>,
    LG: Fn(u64) -> Option<u64>,
    RF: Fn(u64) -> Option<u64>,
    RG: Fn(u64) -> Option<u64>,
{
    match statement {
        Statement::Binding(Binding {
            name,
            operator,
            operands,
            ty,
            loc: _,
        }) => {
            let name = translate_val_name(name, lhs_trans, rhs_trans);
            let operands = operands
                .iter()
                .map(|op| translate_val_name(op, lhs_trans, rhs_trans))
                .collect::<Vec<_>>()
                .join(",");

            format!("{}: {} <- {}({})", name, ty, operator, operands)
        }
        Statement::Register(Register {
            name,
            ty,
            clock,
            reset,
            value,
            loc: _,
        }) => {
            let name = translate_val_name(name, lhs_trans, rhs_trans);
            let clock = translate_val_name(clock, lhs_trans, rhs_trans);
            let reset = reset
                .as_ref()
                .map(|(trig, val)| {
                    let trig = translate_val_name(trig, lhs_trans, rhs_trans);
                    let val = translate_val_name(val, lhs_trans, rhs_trans);
                    format!(" reset ({}, {})", trig, val)
                })
                .unwrap_or_else(|| "".to_string());
            let value = translate_val_name(value, lhs_trans, rhs_trans);

            format!("reg {}: {} clock {}{} {}", name, ty, clock, reset, value)
        }
        Statement::Constant(name, ty, value) => {
            let name = translate_expr(*name, &lhs_trans.expr, &rhs_trans.expr);

            format!("const {}: {} = {}", name, ty, value)
        }
        Statement::Assert(value) => {
            let value = translate_val_name(value, lhs_trans, rhs_trans);
            format!("assert {value}")
        }
        Statement::Set { target, value } => {
            let value = translate_val_name(value, lhs_trans, rhs_trans);
            let target = translate_val_name(target, lhs_trans, rhs_trans);
            format!("set {target} = {value}")
        }
    }
}

pub fn translate_entity<LF, LG, RF, RG>(
    entity: &Entity,
    lhs_trans: &NameTranslator<LF, LG>,
    rhs_trans: &NameTranslator<RF, RG>,
) -> String
where
    LF: Fn(u64) -> Option<u64>,
    LG: Fn(u64) -> Option<u64>,
    RF: Fn(u64) -> Option<u64>,
    RG: Fn(u64) -> Option<u64>,
{
    let Entity {
        name,
        inputs,
        output,
        output_type,
        statements,
    } = entity;

    let inputs = inputs
        .iter()
        .map(|(name, val_name, ty)| {
            let val_name = translate_val_name(val_name, lhs_trans, rhs_trans);

            format!("({}, {}: {})", name, val_name, ty)
        })
        .collect::<Vec<_>>()
        .join(",");

    let output = translate_val_name(output, lhs_trans, rhs_trans);

    let statements = statements
        .iter()
        .map(|s| translate_statement(s, lhs_trans, rhs_trans))
        .map(|s| format!("    {}", s))
        .collect::<Vec<_>>()
        .join("\n");

    indoc::formatdoc!(
        r#"entity {}({}) -> {} {{
            {}
        }} => {}"#,
        name,
        inputs,
        output_type,
        statements,
        output
    )
}

/// Returns string versions of lhs and rhs with the variable mapping `map`
pub fn translated_strings(lhs: &Entity, rhs: &Entity, map: &VarMap) -> (String, String) {
    let lhs_string = translate_entity(
        lhs,
        &identity_name_translator(),
        &map_name_translator(map.expr_map.clone(), map.name_map.clone()),
    );

    let rhs_string = translate_entity(
        rhs,
        &map_name_translator(map.expr_map_rev.clone(), map.name_map_rev.clone()),
        &identity_name_translator(),
    );

    (lhs_string, rhs_string)
}
