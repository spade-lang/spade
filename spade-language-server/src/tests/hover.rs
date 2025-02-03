use crate::tests::{init_with_file, InitFileOpt};

#[tokio::test]
async fn hover_struct() {
    init_with_file(
        r#"
        struct NameOfStruct {
            field_a: bool,
            field_b: int<4>,
        }
        fn foo() -> bool {
            let s = NameOfStruct(false, 2);
                 //  ^[1] hover
            false
        }
    "#,
        InitFileOpt::default(),
        None,
        Some("(type) NameOfStruct"),
        "",
    )
    .await;
}

#[tokio::test]
async fn hover_binding() {
    init_with_file(
        r#"
        struct NameOfStruct {
            field_a: bool,
            field_b: int<4>,
        }
        fn foo() -> bool {
            let s = NameOfStruct(false, 2);

            let cow = s;
                  //  ^[1] hover
            false
        }
    "#,
        InitFileOpt::default(),
        None,
        Some("(variable) s: NameOfStruct"),
        "",
    )
    .await;
}

#[tokio::test]
async fn hover_unit() {
    init_with_file(
        r#"
        struct NameOfStruct {
            field_a: bool,
            field_b: int<4>,
        }
        fn foo() -> bool {
            let s = NameOfStruct(false, 2);

            let cow = s;
            false
        }

        fn bar() -> bool {
            foo()
         //  ^[1] hover
        }
    "#,
        InitFileOpt::default(),
        None,
        Some("(fn) foo -> bool"),
        "",
    )
    .await;
}

#[tokio::test]
async fn hover_field() {
    init_with_file(
        r#"
        struct NameOfStruct {
            field_a: bool,
            field_b: int<4>,
        }
        fn foo() -> bool {
            let s = NameOfStruct(false, 2);
            s.field_a
            //  ^[1] hover
        }
    "#,
        InitFileOpt::default(),
        None,
        Some("(field) NameOfStruct.field_a: bool"),
        "",
    )
    .await;
}
