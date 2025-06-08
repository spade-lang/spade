use crate::tests::{init_with_file, InitFileOpt};

#[tokio::test]
async fn integer_does_not_fit() {
    init_with_file(
        r#"
        fn top() -> int<2> {
            0b111
        //  ^^^^^[1] diagnostic: Integer value does not fit in int<2>
        }
    "#,
        InitFileOpt::default(),
        None,
        "",
    )
    .await;
}
