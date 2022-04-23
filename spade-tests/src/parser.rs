use crate::snapshot_error;

snapshot_error! {
    stage_outside_pipeline,
    "
    entity main(x: X) -> int<8> {
        reg;
    }
    "
}

snapshot_error!(
    expect_range_separator,
    r#"
    entity main() -> int<2> {
        let a: int<fits(4)> = 0
        a
    }
    "#
);

snapshot_error!(
    expect_range_separator_empty,
    r#"
    entity main() -> int<2> {
        let a: int<fits()> = 0
        a
    }
    "#
);

snapshot_error!(
    range_separator_missing_top,
    r#"
    entity main() -> int<2> {
        let a: int<fits(0..)> = 0
        a
    }
    "#
);

snapshot_error!(
    range_separator_missing_close,
    r#"
    entity main() -> int<2> {
        let a: int<fits(0..> = 0
        a
    }
    "#
);

snapshot_error!(
    range_separator_wrong_separator,
    r#"
    entity main() -> int<2> {
        let a: int<fits(0.=1)> = 0
        a
    }
    "#
);

// Disallow this since the fits(a..b)-syntax is parsed before generics are checked.
snapshot_error!(
    integer_ranges_disallow_generic_fits,
    r#"
    fn foo<fits>(a<fits>) -> bool {
        true
    }
    "#
);
