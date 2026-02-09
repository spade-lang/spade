use itertools::Itertools;
/// Utilities for printing the difference between two mir blocks with their var mappings.
///
/// Names are formatted as e(<left hand side> | <right hand side>) and the corresponding name is
/// looked up from the specified hash map depending on which side we're printing. This allows some
/// nice text-based diffs, but does require the use of quite a few generic parameters since we need
/// to either look up names in a hash map, or just use the given name.
use rustc_hash::FxHashMap as HashMap;
use spade_common::id_tracker::ExprID;

use crate::{diff::VarMap, Entity};
use crate::{Binding, MirInput, Register, Statement, ValueName};

pub fn translate_expr(
    name: ExprID,
    lhs_trans: &impl Fn(ExprID) -> Option<ExprID>,
    rhs_trans: &impl Fn(ExprID) -> Option<ExprID>,
) -> String {
    let lhs = lhs_trans(name)
        .map(|n| format!("{}", n.0))
        .unwrap_or_else(|| "?".to_string());
    let rhs = rhs_trans(name)
        .map(|n| format!("{}", n.0))
        .unwrap_or_else(|| "?".to_string());

    format!("({}|{})", lhs, rhs)
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
    F: Fn(ExprID) -> Option<ExprID>,
    G: Fn(u64) -> Option<u64>,
{
    expr: F,
    name: G,
}

pub fn identity_name_translator(
) -> NameTranslator<impl Fn(ExprID) -> Option<ExprID>, impl Fn(u64) -> Option<u64>> {
    NameTranslator {
        expr: Some,
        name: Some,
    }
}

pub fn map_name_translator(
    expr: HashMap<ExprID, ExprID>,
    name: HashMap<u64, u64>,
) -> NameTranslator<impl Fn(ExprID) -> Option<ExprID>, impl Fn(u64) -> Option<u64>> {
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
    LF: Fn(ExprID) -> Option<ExprID>,
    LG: Fn(u64) -> Option<u64>,
    RF: Fn(ExprID) -> Option<ExprID>,
    RG: Fn(u64) -> Option<u64>,
{
    match name {
        ValueName::Named(id, n, _) => translate_name((*id, n), &lhs_trans.name, &rhs_trans.name),
        ValueName::Expr(id) => translate_expr(*id, &lhs_trans.expr, &rhs_trans.expr),
    }
}

pub fn translate_statement<LF, LG, RF, RG>(
    statement: &Statement,
    lhs_trans: &NameTranslator<LF, LG>,
    rhs_trans: &NameTranslator<RF, RG>,
) -> String
where
    LF: Fn(ExprID) -> Option<ExprID>,
    LG: Fn(u64) -> Option<u64>,
    RF: Fn(ExprID) -> Option<ExprID>,
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
            initial,
            value,
            loc: _,
            traced,
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
            let initial = initial
                .as_ref()
                .map(|i| {
                    format!(
                        " initial ({})",
                        i.iter().map(|v| format!("{v}").to_string()).join("; ")
                    )
                })
                .unwrap_or_else(|| "".to_string());
            let value = translate_val_name(value, lhs_trans, rhs_trans);
            let traced = if let Some(traced) = traced {
                format!(
                    "traced({})",
                    translate_val_name(traced, lhs_trans, rhs_trans)
                )
            } else {
                "".to_string()
            };

            format!("{traced}reg {name}: {ty} clock {clock}{reset}{initial} {value}",)
        }
        Statement::Constant(name, ty, value) => {
            let name = translate_val_name(name, &lhs_trans, &rhs_trans);

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
        Statement::WalTrace {
            name,
            val,
            suffix,
            ty,
        } => {
            let name = translate_val_name(name, lhs_trans, rhs_trans);
            let val = translate_val_name(val, lhs_trans, rhs_trans);
            format!("wal_trace ({name}, {val}, '{suffix}', {ty})")
        }
        Statement::Error => {
            format!("Error")
        }
    }
}

pub fn translate_entity<LF, LG, RF, RG>(
    entity: &Entity,
    lhs_trans: &NameTranslator<LF, LG>,
    rhs_trans: &NameTranslator<RF, RG>,
) -> String
where
    LF: Fn(ExprID) -> Option<ExprID>,
    LG: Fn(u64) -> Option<u64>,
    RF: Fn(ExprID) -> Option<ExprID>,
    RG: Fn(u64) -> Option<u64>,
{
    let Entity {
        name,
        inputs,
        output,
        output_type,
        statements,
        verilog_attr_groups: _,
        inline: _,
    } = entity;

    let inputs = inputs
        .iter()
        .map(
            |MirInput {
                 name,
                 val_name,
                 ty,
                 no_mangle,
             }| {
                let val_name = translate_val_name(val_name, lhs_trans, rhs_trans);

                format!(
                    "({}{name}, {val_name}: {ty})",
                    no_mangle.map(|_| "#[no_mangle]").unwrap_or("")
                )
            },
        )
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
