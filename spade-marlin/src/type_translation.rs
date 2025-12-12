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

/// Shifts value of the little endian vector `bits` `shift_amount` bits towards the little end
fn u32_shift_to_le(bits: &[u32], shift_amount: usize, out: &mut [u32]) {
    let word_shift_amount = shift_amount / 32;
    let subslice = &bits[word_shift_amount..];
    let sub_shift_amount = shift_amount % 32;

    if sub_shift_amount == 0 {
        out[0..subslice.len()].clone_from_slice(subslice);
    } else {
        for i in 0..subslice.len() {
            let extra = if i < subslice.len() - 1 {
                subslice[i + 1] << (32 - sub_shift_amount)
            } else {
                0
            };
            out[i] = subslice[i] >> sub_shift_amount | extra;
        } 
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
        // FIXME: I wonder if we could avoid this allocation somehow
        let mut buff = vec![0; N as usize];
        u32_shift_to_le(bits, bit_offset, &mut buff);

        let mask = (1u64 << N % 32) - 1;
        if N > 32 {
            self.inner = (((buff[1]) as u64) & mask) << 32 | buff[0] as u64;
            
        } else {
            self.inner = buff[0] as u64 & mask;
        }

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
        let mut buff = [0; 1];
        u32_shift_to_le(bits, bit_offset, &mut buff);
        *self = buff[0] & 1 == 1
    }
}

macro_rules! tuple_methods {
    // Recursion base case, we don't impl it for the unit type here
    (($first:ident)) => {};

    ( ( $first:ident, $($rest:ident),* ) ) => {
        tuple_methods!(# ($first, $($rest),*));
        tuple_methods!(( $($rest),* ));
    };

    (# ($($param:ident),*)) => {
        impl<$($param),*> SpadeType for ($($param),*)
        where $($param: SpadeType + Default),*
        {
            fn size() -> usize {
                $($param::size() +)* 0
            }

            fn backward_size() -> usize {
                $($param::backward_size() +)* 0
            }

            fn update_value(&mut self, mut bit_offset: usize, bits: &[u32]) {
                bit_offset = bit_offset + Self::size();
                #[allow(non_snake_case)]
                let ($($param),*) = self;
                $(
                    bit_offset -= $param::size();
                    $param.update_value(bit_offset, bits);
                )*
                let _ = bit_offset;
            }
        }
    };
}
tuple_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11));


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
        let mut buff = vec![0; Self::size()];
        u32_shift_to_le(bits, bit_offset + T::size(), &mut buff);
        *self = if buff[0] & 1 == 1 {
            let mut inner = T::default();
            inner.update_value(bit_offset, bits);
            Some(inner)
        } else {
            None
        }
    }
}



#[cfg(test)]
mod test {
    use super::*;
    #[test]
    fn u32_shift_right_test() {
        //  0x0000_000f 8000_0001 0000_0000
        let input = [0, 0x8000_0001, 0x0000_000f];

        let mut buff = [0; 3];

        //  0x0000_0000 000f_8000 0001_0000
        u32_shift_to_le(&input, 16, &mut buff);
        assert_eq!(buff, [0x0001_0000, 0x00f_8000, 0].as_slice());

        //  0x0000_0000 0000 000f 8000 0001
        u32_shift_to_le(&input, 32, &mut buff);
        assert_eq!(buff, [0x8000_0001, 0x0000_000f, 0].as_slice());

        //  0x0000_0000 0000 0007 C000 0000
        u32_shift_to_le(&input, 33, &mut buff);
        assert_eq!(buff, [0xC000_0000, 0x0000_007, 0].as_slice());
    }
}
