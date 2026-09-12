use snafu::Whatever;
use spade_marlin_macro::spade_marlin;

mod spade_types;

use spade_marlin::prelude::*;

use crate::spade_types::spade_types::spade_marlin::EnumOut;


mod u48_passthrough {
    use super::*;
    #[spade_marlin(top = "spade_marlin::u48_passthrough")]
    struct Uut;

    #[test]
    #[snafu::report]
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
#[snafu::report]
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
#[snafu::report]
fn option_in_works() -> Result<(), Whatever> {
    #[spade_marlin(top = "spade_marlin::option_passthrough")]
    struct Uut;
    let runtime = SpadeRuntime::new(Default::default())?;
    let mut main = Uut::new_simple(&runtime)?;

    main.i.input = Some(10u8.into());
    main.eval();
    assert_eq!(main.i.result, Some(10u8.into()));
    main.i.input = None;
    main.eval();
    assert_eq!(main.i.result, None);

    Ok(())
}


#[test]
#[snafu::report]
fn tuple_out_works() -> Result<(), Whatever> {
    #[spade_marlin(top = "spade_marlin::tuple_out")]
    struct TupleOut;

    let runtime = SpadeRuntime::new(Default::default())?;

    let mut main = TupleOut::new_simple(&runtime)?;

    main.i.x = 10u32.into();
    main.i.y = 1u32.into();

    main.eval();

    assert_eq!(main.i.result, (10u8.into(), 1u8.into()));

    Ok(())
}

#[test]
#[snafu::report]
fn enum_out_works() -> Result<(), Whatever> {
    #[spade_marlin(top = "spade_marlin::enum_out")]
    struct Uut;

    let runtime = SpadeRuntime::new(Default::default())?;

    let mut main = Uut::new_simple(&runtime)?;

    main.i.variant = 0u32.into();
    main.i.x = 1u32.into();
    main.i.y = 2u32.into();

    main.eval();
    assert_eq!(main.i.result, EnumOut::Zero {});
    main.i.variant = 1u32.into();
    main.eval();
    assert_eq!(main.i.result, EnumOut::One {x: 1u8.into()});

    main.i.variant = 2u32.into();
    main.eval();
    assert_eq!(main.i.result, EnumOut::Two {y: 2u8.into()});

    main.i.variant = 3u32.into();
    main.eval();
    assert_eq!(main.i.result, EnumOut::Three {x: 1u8.into(), y: 2u8.into()});

    Ok(())
}
