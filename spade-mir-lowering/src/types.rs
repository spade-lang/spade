use spade_lir as lir;
use spade_mir as mir;

pub(crate) trait TypeExt {
    fn lower(&self) -> (Option<lir::Type>, Option<lir::Type>);
}

impl TypeExt for mir::types::Type {
    fn lower(&self) -> (Option<lir::Type>, Option<lir::Type>) {
        match self {
            mir::types::Type::Int(_) |
            mir::types::Type::UInt(_) |
            mir::types::Type::Bool |
            mir::types::Type::Tuple(_) |
            mir::types::Type::Struct(_) |
            mir::types::Type::Array {..} |
            mir::types::Type::Memory {..} |
            mir::types::Type::Enum(_) |
            mir::types::Type::CopyView(_) => (Some(lir::Type::BitVector(self.size())), None),
            mir::types::Type::InOut(inner) => {
                let (Some(fwd), None) = inner.lower() else {
                    panic!("Found an inout which was not a pure forward type");
                };
                (Some(lir::Type::InOut(Box::new(fwd))), None)   
            },

            mir::types::Type::Backward(inner) => {
                let (fwd, back) = inner.lower();

                (back, fwd)
            },
        }
    }
}
