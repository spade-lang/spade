use spade_common::error_reporting::{CodeBundle, CompilationError};
#[cfg(test)]
use spade_hir_lowering::generate_entity;
#[cfg(test)]
use spade_testutil::{parse_typecheck_module_body, ParseTypececkResult};
#[cfg(test)]
use spade_typeinference::ProcessedItem;

mod hir_lowering;
mod typeinference;

pub trait ResultExt<T> {
    fn report_failure(self, code: &str) -> T;
}
impl<T> ResultExt<T> for spade_hir_lowering::Result<T> {
    fn report_failure(self, code: &str) -> T {
        match self {
            Ok(t) => t,
            Err(e) => {
                let code_bundle = CodeBundle::new(code.to_string());
                e.report(&code_bundle, false);
                panic!("Compilation error")
            }
        }
    }
}

#[macro_export]
macro_rules! build_entity {
    ($code:expr) => {{
        let (processed, mut symtab, mut idtracker, item_list) = parse_typecheck_entity($code);
        let result = generate_entity(
            &processed.entity,
            &mut symtab,
            &mut idtracker,
            &processed.type_state,
            &item_list,
        )
        .map_err(|e| {
            print!(
                "{}",
                spade_typeinference::format_trace_stack(&processed.type_state.trace_stack)
            );
            e
        })
        .report_failure($code);
        result
    }};
}

/// Builds mutliple entities and types from a source string. If any pipelines or other
/// non-entities or types are included in $code, this panics
#[cfg(test)]
fn build_items(code: &str) -> Vec<spade_mir::Entity> {
    let ParseTypececkResult {
        items_with_types,
        item_list,
        mut symtab,
        mut idtracker,
    } = parse_typecheck_module_body(code);

    // TODO: This is copied from the above code, so it is fairly general. Perhaps
    // we should macroify it
    let mut result = vec![];
    for processed in items_with_types.executables {
        match processed {
            ProcessedItem::Entity(processed) => {
                result.push(
                    generate_entity(
                        &processed.entity,
                        &mut symtab,
                        &mut idtracker,
                        &processed.type_state,
                        &item_list,
                    )
                    .map_err(|e| {
                        spade_typeinference::format_trace_stack(&processed.type_state.trace_stack);
                        e
                    })
                    .report_failure(code),
                );
            }
            ProcessedItem::EnumInstance => {}
            _ => panic!("expected an entity"),
        }
    }

    result
}

/// Builds mutliple entities and types from a source string, then compares the resulting
/// entities. $expected should be a vector of mir entities. If any pipelines or other
/// non-entities or types are included in $code, this panics
#[macro_export]
macro_rules! build_and_compare_entities {
    ($code:expr, $expected:expr) => {
        let result = build_items($code);

        assert_eq!(
            $expected.len(),
            result.len(),
            "Expected {} entities, found {}",
            $expected.len(),
            result.len()
        );

        for (exp, res) in $expected.into_iter().zip(result.into_iter()) {
            assert_same_mir!(&res, &exp);
        }
    };
}
