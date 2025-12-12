pub trait SpadeType : Default {
    fn size() -> usize;
    fn backward_size() -> usize;

    /// Update the value of this type based on the `bits`. The `start_bit` and `end_bit` parameters
    /// are the bit offsets at which this value starts in `bits`. `start_bit` must be respected, but
    /// `end_bit` can be ignored _if_ the type knows its own size. It is there for types like `uN` which
    /// do not know the size of their underlying Spade value
    fn update_value(
        &mut self,
        bit_offset: usize,
        bits: &[u32],
    );
}

fn get_unaligned_u32(bit_offset: usize, bits: &[u32]) -> u32 {
    let start_idx = bit_offset / 32;
    let shift_amount = bit_offset % 32;
    if shift_amount == 0 {
        bits[start_idx]
    } else {
        bits[start_idx] >> shift_amount | bits[start_idx + 1] << (32 - shift_amount)
    }
}

#[derive(PartialEq, Default, Debug)]
pub struct SpadeUint<const N: u64> {
    inner: u64,
}

impl<const N: u64> std::ops::Deref for SpadeUint<N> {
    type Target = u64;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<const N: u64> std::fmt::Display for SpadeUint<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.inner)
    }
}


impl<const N: u64> SpadeType for SpadeUint<N> {
    fn size() -> usize {
        N as usize
    }

    fn backward_size() -> usize {
        0
    }

    fn update_value(
        &mut self,
        bit_offset: usize,
        bits: &[u32],
    ) {
        let raw_inner = if N <= 32 {
            get_unaligned_u32(bit_offset, bits) as u64
        } else {
            get_unaligned_u32(bit_offset, bits) as u64 | (get_unaligned_u32(bit_offset + 32, bits) as u64) << 32
        };

        let mask = (1 << Self::size()) - 1;

        self.inner = raw_inner & mask
    }
}

macro_rules! uint_methods {
    ($ty:ty) => {
        impl<const N: u64> From<$ty> for SpadeUint<N> {
            fn from(value: $ty) -> Self {
                // TODO: Panic if the value does not fit
                SpadeUint::<N>{inner: value as u64}
            }
        }

        impl<const N: u64> PartialEq<$ty> for SpadeUint<N> {
            fn eq(&self, other: &$ty) -> bool {
                self.inner == *other as u64
            }
        }
    }
}
uint_methods!(u8);
uint_methods!(u16);
uint_methods!(u32);
uint_methods!(u64);


impl SpadeType for bool {
    fn size() -> usize {
        1
    }

    fn backward_size() -> usize {
        0
    }

    fn update_value(
        &mut self,
        bit_offset: usize,
        bits: &[u32],
    ) {
        *self = get_unaligned_u32(bit_offset, bits) | 1 == 1
    }
}

impl<T: SpadeType> SpadeType for Option<T> {
    fn size() -> usize {
        1 + T::size()
    }

    fn backward_size() -> usize {
        0
    }

    fn update_value(
        &mut self,
        bit_offset: usize,
        bits: &[u32],
    ) {
        if bit_offset > 32 {
            unimplemented!("Option with > 32 size is not supported")
        }
        let tag_offset = bit_offset + T::size();
        let tag = (bits[0] >> tag_offset) & 1 == 1;
        *self = if tag {
            let mut result = T::default();
            result.update_value(bit_offset, bits);
            Some(result)
        } else {
            None
        }
    }
}


