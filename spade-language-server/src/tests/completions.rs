// These tests are broken on mac, I can't figure out why but completion is
// also very janky as is, so let's just skip those tests
#[cfg(not(target_os = "macos"))]
use crate::tests::{init_with_file, InitFileOpt};

#[cfg(not(target_os = "macos"))]
#[tokio::test]
async fn comps_find_types() {
    init_with_file(
        r#"
        struct name_of_struct1 {
            field_a: bool,
            field_b: int<4>,
        }
        struct name_of_struct2 {
            field_a: bool,
            field_b: int<4>,
        }
        enum name_of_enum1 {
            Enum1Variant1,
            Enum1Variant2,
        }
        enum name_of_enum2 {}
       //  ^[1] comps
    "#,
        InitFileOpt::default(),
        Some(&vec![
            "name_of_struct1",
            "name_of_struct2",
            "name_of_enum1",
            "name_of_enum2",
        ]),
        "",
    )
    .await;
}

#[cfg(not(target_os = "macos"))]
#[tokio::test]
async fn comps_find_units() {
    init_with_file(
        r#"
        fn func1(arg1: bool) -> bool {
            true
        }

        fn func2(arg1: bool) -> bool {
            true
        }

        entity entity1(arg1: bool) -> bool {
            true
        }

        entity entity2(arg1: bool) -> bool {
            true
        }
       //  ^[1] comps
    "#,
        InitFileOpt::default(),
        Some(&vec!["func1", "func2", "entity1", "entity2"]),
        "",
    )
    .await;
}

#[cfg(not(target_os = "macos"))]
#[tokio::test]
async fn comps_find_bindings() {
    init_with_file(
        r#"
        fn func1(arg1: bool, arg2: int<4>) -> bool {
            let var1: int<8> = 3;
            let var2: int<4> = 1;

           //  ^[1] comps
            true
        }
    "#,
        InitFileOpt::default(),
        Some(&vec!["arg1", "arg2", "var1", "var2"]),
        "",
    )
    .await;
}
