use snafu::Whatever;
use spade_marlin_macro::spade_marlin;

mod types;

use spade_marlin::prelude::*;

#[spade_marlin(top = "spade_marlin::add")]
struct Main;

#[test]
fn raw_verilator_interface() -> Result<(), Whatever> {
    let runtime = SpadeRuntime::new(Default::default())?;

    let mut main = Main::new_simple(&runtime)?;

    main.verilator.x_i = 5;
    main.verilator.y_i = 6;

    main.eval();

    assert_eq!(main.verilator.result_o, 11);

    Ok(())
}
