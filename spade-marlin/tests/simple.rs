use snafu::Whatever;
use spade_marlin_macro::spade_marlin;

mod types;

use spade_marlin::prelude::*;


#[test]
fn raw_verilator_interface() -> Result<(), Whatever> {
    #[spade_marlin(top = "spade_marlin::add")]
    struct Main;

    let runtime = SpadeRuntime::new(Default::default())?;

    let mut main = Main::new_simple(&runtime)?;

    main.i.x = 5u32.into();
    main.i.y = 6u32.into();

    main.eval();

    assert_eq!(main.verilator.result_o, 11);

    Ok(())
}



#[test]
fn option_out_works() -> Result<(), Whatever> {
    #[spade_marlin(top = "spade_marlin::option_out")]
    struct OptionOut;

    let runtime = SpadeRuntime::new(Default::default())?;

    let mut main = OptionOut::new_simple(&runtime)?;

    main.verilator.x_i = 10;
    main.verilator.valid_i = 1;

    main.eval();

    assert_eq!(main.i.result, Some(10u8.into()));

    main.verilator.valid_i = 0;

    main.eval();

    assert_eq!(main.i.result, None);

    Ok(())
}


#[test]
fn tuple_out_works() -> Result<(), Whatever> {
    #[spade_marlin(top = "spade_marlin::tuple_out")]
    struct TupleOut;

    let runtime = SpadeRuntime::new(Default::default())?;

    let mut main = TupleOut::new_simple(&runtime)?;

    main.verilator.x_i = 10;
    main.verilator.y_i = 1;

    main.eval();

    println!("Raw value from verilator: {:x}", main.verilator.result_o);

    assert_eq!(main.i.result, (10u8.into(), 1u8.into()));

    Ok(())
}

