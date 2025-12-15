use snafu::Whatever;
use spade_marlin_macro::spade_marlin;

mod types;

use spade_marlin::prelude::*;


mod u48_passthrough {
    use super::*;
    #[spade_marlin(top = "spade_marlin::u48_passthrough")]
    struct Uut;

    #[test]
    fn u48_passhtrough() -> Result<(), Whatever> {

        let runtime = SpadeRuntime::new(Default::default())?;

        let mut main = Uut::new_simple(&runtime)?;

        main.i.x = 0x1234_5678_9abc_u64.into();

        main.eval();

        assert_eq!(main.i.result, 0x1234_5678_9abc_u64);

        Ok(())
    }

}


#[test]
fn option_out_works() -> Result<(), Whatever> {
    #[spade_marlin(top = "spade_marlin::option_out")]
    struct OptionOut;

    let runtime = SpadeRuntime::new(Default::default())?;

    let mut main = OptionOut::new_simple(&runtime)?;

    main.i.x = 10u32.into();
    main.i.valid = true;

    main.eval();

    assert_eq!(main.i.result, Some(10u8.into()));

    main.i.valid = false;

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

    main.i.x = 10u32.into();
    main.i.y = 1u32.into();

    main.eval();

    println!("Raw value from verilator: {:x}", main.verilator.result_o);

    assert_eq!(main.i.result, (10u8.into(), 1u8.into()));

    Ok(())
}

