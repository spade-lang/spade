use num::BigUint;
use spade_lir as lir;
use spade_mir as mir;

pub(crate) trait TypeExt {
    fn lower(&self) -> (lir::Type, lir::Type);
}

impl TypeExt for mir::types::Type {
    fn lower(&self) -> (lir::Type, lir::Type) {
        match self {
            mir::types::Type::Int(_)
            | mir::types::Type::UInt(_)
            | mir::types::Type::Bool
            | mir::types::Type::Tuple(_)
            | mir::types::Type::Struct(_)
            | mir::types::Type::Array { .. }
            | mir::types::Type::Memory { .. }
            | mir::types::Type::Enum(_)
            | mir::types::Type::CopyView(_) => {
                (lir::Type::BitVector(self.size()), lir::Type::unit())
            }
            mir::types::Type::InOut(inner) => {
                let (fwd, back) = inner.lower();

                if back.size() != BigUint::ZERO {
                    panic!("Found an inout which was not a pure forward type");
                };
                (lir::Type::InOut(Box::new(fwd)), lir::Type::unit())
            }

            mir::types::Type::Backward(inner) => {
                let (fwd, back) = inner.lower();

                (back, fwd)
            }
        }
    }
}
