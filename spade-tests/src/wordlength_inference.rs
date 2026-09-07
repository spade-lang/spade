use crate::snapshot_inference_error;
use spade_wordlength_inference::InferMethod;

snapshot_inference_error!(
    simple_multiple_addition_aa,
    "AA",
    r#"
        fn f(a: int<4>) -> int<0> {
          a + a + a + a
        }
        entity main(clk: clock, rst: bool) -> int<0> { f(1) }
    "#
);

snapshot_inference_error!(
    simple_multiple_addition_ia,
    "IA",
    r#"
        fn f(a: int<4>) -> int<0> {
          a + a + a + a
        }
        entity main(clk: clock, rst: bool) -> int<0> { f(1) }
    "#
);

snapshot_inference_error!(
    simple_subtraction_aa,
    "AA",
    r#"
        fn f(a: int<4>) -> int<0> {
          a - a + 1
        }
        entity main(clk: clock, rst: bool) -> int<0> { f(1) }
    "#
);

snapshot_inference_error!(
    simple_subtraction_ia,
    "IA",
    r#"
        fn f(a: int<4>) -> int<0> {
          a - a + 1
        }
        entity main(clk: clock, rst: bool) -> int<0> { f(1) }
    "#
);

// NOTE: The generic parameters here make no sense, figure this out once we do wlinf again
/*
snapshot_inference_error!(
    multiple_generics_aa,
    "AA",
    r#"
        fn f<A, B>(a: int<a>, b: int<b>) -> int<b> {
          a + b
        }

        entity main(clk: clock, rst: bool) -> int<0> {
          let x: int<5> = f(0, 10);
          let y: int<5> = f(1, 10);
          0
        }
    "#
);

snapshot_inference_error!(
    multiple_generics_ia,
    "IA",
    r#"
        fn f<A, B>(a: int<a>, b: int<b>) -> int<b> {
          a + b
        }

        entity main(clk: clock, rst: bool) -> int<0> {
          let x: int<5> = f(0, 10);
          let y: int<5> = f(1, 10);
          0
        }
    "#
);

snapshot_inference_error!(
    multiple_generics_aaia,
    "IA",
    r#"
        fn f<A, B>(a: int<a>, b: int<b>) -> int<b> {
          a + b
        }

        entity main(clk: clock, rst: bool) -> int<0> {
          let x: int<5> = f(0, 10);
          let y: int<5> = f(1, 10);
          0
        }
    "#
);

*/

snapshot_inference_error!(
    multiplication_and_addition_aa,
    "AA",
    r#"
        fn f<A, B>(a: int<4>, b: int<4>) -> int<0> {
          a * b + a + b
        }
        entity main(clk: clock, rst: bool) -> int<0> { f(0, 0) }
    "#
);

snapshot_inference_error!(
    multiplication_and_addition_ia,
    "IA",
    r#"
        fn f<A, B>(a: int<4>, b: int<4>) -> int<0> {
          a * b + a + b
        }
        entity main(clk: clock, rst: bool) -> int<0> { f(0, 0) }
    "#
);

snapshot_inference_error!(
    ifs_aa,
    "AA",
    r#"
        fn f<A, B>(q: bool, a: int<0>, b: int<4>) -> int<0> {
            if q { a } else { a * b + b - b + 1 }
        }
        entity main(clk: clock, rst: bool) -> int<0> { f(false, 0, 0) }
    "#
);

snapshot_inference_error!(
    ifs_ia,
    "IA",
    r#"
        fn f<A, B>(q: bool, a: int<0>, b: int<4>) -> int<0> {
            if q { a } else { a * b + b - b + 1 }
        }
        entity main(clk: clock, rst: bool) -> int<0> { f(false, 0, 0) }
    "#
);

snapshot_inference_error!(
    inner_functions_aa,
    "AA",
    r#"
        fn g() -> int<3> { 0 }
        fn f<A, B>(a: int<2>) -> int<0> {
            g() + a
        }
        entity main(clk: clock, rst: bool) -> int<0> { f(0) }
    "#
);

snapshot_inference_error!(
    inner_functions_ia,
    "IA",
    r#"
        fn g() -> int<3> { 0 }
        fn f<A, B>(a: int<2>) -> int<0> {
            g() + a
        }
        entity main(clk: clock, rst: bool) -> int<0> { f(0) }
    "#
);

snapshot_inference_error!(
    wordlength_inference_aa,
    "AA",
    r#"
        fn p<N>(x: int<N>) -> int<N> { x }

        fn f(a: int<5>) -> int<7> {
          1 * p(a) + 1
        }

        entity main(clk: clock, rst: bool) -> int<7> {
          f(3)
        }
    "#
);

snapshot_inference_error!(
    wordlength_inference_ia,
    "IA",
    r#"
        fn p<N>(x: int<N>) -> int<N> { x }

        fn f(a: int<5>) -> int<7> {
          1 * p(a) + 1
        }

        entity main(clk: clock, rst: bool) -> int<7> {
          f(3)
        }
    "#
);

snapshot_inference_error!(
    if_conditions_are_visited_ia,
    "IA",
    r#"
        struct X { x: int<4>, }

        fn f(a: X) -> int<4> {
          let p = a.x;
          if 0 == trunc(p + 1) {
            0
          } else {
            0
          }
        }

        entity main(clk: clock, rst: bool) -> int<4> {
          f( X { x: 0 } )
        }
    "#
);

snapshot_inference_error!(
    if_conditions_are_visited_aa,
    "AA",
    r#"
        struct X { x: int<4>, }

        fn f(a: X) -> int<4> {
          let p = a.x;
          if 0 == trunc(p + 1) {
            0
          } else {
            0
          }
        }

        entity main(clk: clock, rst: bool) -> int<4> {
          f( X { x: 0 } )
        }
    "#
);

snapshot_inference_error!(
    simple_multiple_addition_aaia,
    "IA",
    r#"
        fn f(a: int<4>) -> int<0> {
          a + a + a + a
        }
        entity main(clk: clock, rst: bool) -> int<0> { f(1) }
    "#
);

snapshot_inference_error!(
    simple_subtraction_aaia,
    "IA",
    r#"
        fn f(a: int<4>) -> int<0> {
          a - a + 1
        }
        entity main(clk: clock, rst: bool) -> int<0> { f(1) }
    "#
);

snapshot_inference_error!(
    multiplication_and_addition_aaia,
    "IA",
    r#"
        fn f<A, B>(a: int<4>, b: int<4>) -> int<0> {
          a * b + a + b
        }
        entity main(clk: clock, rst: bool) -> int<0> { f(0, 0) }
    "#
);

snapshot_inference_error!(
    ifs_aaia,
    "IA",
    r#"
        fn f<A, B>(q: bool, a: int<0>, b: int<4>) -> int<0> {
            if q { a } else { a * b + b - b + 1 }
        }
        entity main(clk: clock, rst: bool) -> int<0> { f(false, 0, 0) }
    "#
);

snapshot_inference_error!(
    inner_functions_aaia,
    "IA",
    r#"
        fn g() -> int<3> { 0 }
        fn f<A, B>(a: int<2>) -> int<0> {
            g() + a
        }
        entity main(clk: clock, rst: bool) -> int<0> { f(0) }
    "#
);

snapshot_inference_error!(
    wordlength_inference_aaia,
    "IA",
    r#"
        fn p<N>(x: int<N>) -> int<N> { x }

        fn f(a: int<5>) -> int<7> {
          1 * p(a) + 1
        }

        entity main(clk: clock, rst: bool) -> int<7> {
          f(3)
        }
    "#
);

snapshot_inference_error!(
    if_conditions_are_visited_aaia,
    "AA",
    r#"
        struct X { x: int<4>, }

        fn f(a: X) -> int<4> {
          let p = a.x;
          if 0 == trunc(p + 1) {
            0
          } else {
            0
          }
        }

        entity main(clk: clock, rst: bool) -> int<4> {
          f( X { x: 0 } )
        }
    "#
);
