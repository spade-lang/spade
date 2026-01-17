use spade_common::location_info::WithLocation;
use spade_common::name::Path;
use spade_common::num_ext::InfallibleToBigInt;
use spade_types::{ConcreteType, PrimitiveType};

use crate::build_artifacts;

macro_rules! test_hierarchical_lookup {
    ($name:ident, $code:expr, $path:expr, $expected:expr) => {
        #[test]
        fn $name() {
            let code = $code;

            let artefacts = build_artifacts(code, false);

            let main = artefacts
                .state
                .symtab
                .symtab()
                .lookup_unit(&Path::from_strs(&["main"]).nowhere(), true)
                .unwrap()
                .0;

            assert_eq!(
                artefacts
                    .state
                    .type_of_hierarchical_value(
                        &main,
                        &$path.iter().map(|s| s.to_string()).collect::<Vec<_>>()
                    )
                    .unwrap(),
                $expected
            )
        }
    };
}

macro_rules! snapshot_hierarchical_lookup_error {
    ($name:ident, $code:expr, $path:expr) => {
        #[test]
        fn $name() {
            let code = $code;

            let artefacts = build_artifacts(code, false);

            let main = artefacts
                .state
                .symtab
                .symtab()
                .lookup_unit(&Path::from_strs(&["main"]).nowhere(), true)
                .unwrap()
                .0;


            let err = artefacts
                .state
                .type_of_hierarchical_value(
                    &main,
                    &$path.iter().map(|s| s.to_string()).collect::<Vec<_>>()
                )
                .map_err(|r| format!("{r:#}"));

            insta::with_settings!({
                // FIXME: Why can't we set 'description => source' here?
                omit_expression => true,
            }, {
                insta::assert_snapshot!(format!(
                    "{}\n\n{}",
                    code,
                    err.unwrap_err()
                ));
            });
        }
    };
}

test_hierarchical_lookup! { type_of_hierarchical_sub_sub_value_is_found,
    r#"
        fn sub_sub() -> bool {
            let x: int<10> = 0;
            false
        }

        fn sub() -> bool {
            sub_sub()
        }

        fn main() -> bool {
            let inner = sub();
            inner
        }
    "#,
    ["sub_0", "sub_sub_0", "x"],
    ConcreteType::Single {
        base: PrimitiveType::Int,
        params: vec![ConcreteType::Integer(10u32.to_bigint())],
    }
}

test_hierarchical_lookup! { type_of_hierarchical_sub_value_is_found,
    r#"
        fn sub() -> bool {
            let x: int<10> = 0;
            false
        }

        fn main() -> bool {
            let inner = sub();
            inner
        }
    "#,
    ["sub_0", "x"],
    ConcreteType::Single {
        base: PrimitiveType::Int,
        params: vec![ConcreteType::Integer(10u32.to_bigint())],
    }
}

test_hierarchical_lookup! { type_of_hierarchical_root_value_is_found,
    r#"
        fn sub() -> bool {
            false
        }

        fn main() -> bool {
            let x: int<10> = 0;
            true
        }
    "#,
    ["x"],
    ConcreteType::Single {
        base: PrimitiveType::Int,
        params: vec![ConcreteType::Integer(10u32.to_bigint())],
    }
}

test_hierarchical_lookup! { type_of_hierarchical_pipeline_value_is_found,
    r#"
        fn sub() -> bool {
            false
        }

        pipeline(1) main(clk: clock) -> bool {
                let x: int<10> = 0;
            reg;
                false
        }
    "#,
    ["s1_x"],
    ConcreteType::Single {
        base: PrimitiveType::Int,
        params: vec![ConcreteType::Integer(10u32.to_bigint())],
    }
}

snapshot_hierarchical_lookup_error! { type_of_non_existent_value,
    r#"
        fn sub() -> bool {
            false
        }

        pipeline(1) main(clk: clock) -> bool {
                let x: int<10> = 0;
            reg;
                false
        }
    "#,
    ["s1_y"]
}

snapshot_hierarchical_lookup_error! { type_of_non_existent_module,
    r#"
        fn sub() -> bool {
            false
        }

        pipeline(1) main(clk: clock) -> bool {
                let x: int<10> = 0;
            reg;
                false
        }
    "#,
    ["not_a_module", "s1_y"]
}

snapshot_hierarchical_lookup_error! { type_of_non_existent_module_with_candidates,
    r#"
        fn sub() -> bool {
            false
        }

        pipeline(1) main(clk: clock) -> bool {
                let _ = sub();
                let x: int<10> = 0;
            reg;
                false
        }
    "#,
    ["not_a_module", "s1_y"]
}
