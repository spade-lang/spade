use crate::type_ext::IntoU32s;

pub trait SpadeType: Default {
    fn size() -> usize;
    fn backward_size() -> usize;

    /// Update the value of this type from the bits stored at `bit_offset`
    /// until `bit_offset + Self::size()` /// in `bits`. The caller must ensure
    /// that the total number of bits is at least `bit_offset + Self::size()`
    fn from_verilator_value(&mut self, bit_offset: usize, bits: &[u32]);

    /// Write the value of this type into `target` starting at `bit_offset`. The
    /// caller must ensure that the `target` has enough bits, and the implementor
    /// must ensure that only bits between `bit_offset` and `bit_offset` + `Self::size()`
    /// are affected.
    fn to_verilator_value(&self, bit_offset: usize, target: &mut [u32]);
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

fn u32_shift_to_be(bits: &[u32], shift_amount: usize, out: &mut [u32]) {
    let word_shift_amount = shift_amount / 32;
    for word in out.iter_mut() {
        *word = 0;
    }
    let sub_shift_amount = shift_amount % 32;
    let subslice = &mut out[word_shift_amount..];
    if sub_shift_amount != 0 {
        let mut remainder = 0;
        for word in 0..subslice.len() {
            subslice[word] |= remainder | (bits[word] << sub_shift_amount);
            remainder = bits[word] >> (32 - sub_shift_amount);
        }
    } else {
        for i in 0..(bits.len()) {
            if i + word_shift_amount >= out.len() {
                break;
            }
            out[i + word_shift_amount] = bits[i];
        }
    }
}

fn replace_in_u32s(source: &[u32], bit_offset: usize, width: usize, dest: &mut [u32]) {
    let masks = (0..(width / 32)).map(|_| !0u32).chain([((1u64 << width % 32) - 1) as u32]).collect::<Vec<_>>();
    let mut shift_buffer = vec![0; dest.len()];
    let mut mask_buffer = vec![0; dest.len()];
    u32_shift_to_be(source, bit_offset, &mut shift_buffer);
    u32_shift_to_be(&masks, bit_offset, &mut mask_buffer);

    for (i, (value, mask)) in shift_buffer.iter().zip(mask_buffer).enumerate() {
        dest[i] &= !mask;
        dest[i] |= value;
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

    fn from_verilator_value(&mut self, bit_offset: usize, bits: &[u32]) {
        // FIXME: I wonder if we could avoid this allocation somehow
        let mut buff = vec![0; N as usize];
        u32_shift_to_le(bits, bit_offset, &mut buff);

        // TODO: Test the extremes of this
        let mask = (1u64 << N % 32) - 1;
        if N > 32 {
            self.inner = (((buff[1]) as u64) & mask) << 32 | buff[0] as u64;
        } else {
            self.inner = buff[0] as u64 & mask;
        }
    }

    fn to_verilator_value(&self, bit_offset: usize, target: &mut [u32]) {
        let mut buffer = [0; 2];
        self.inner.populate_u32(&mut buffer);
        replace_in_u32s(&buffer, bit_offset, Self::size(), target);
    }
}

macro_rules! uint_methods {
    ($ty:ty) => {
        impl<const N: u64> From<$ty> for SpadeUint<N> {
            fn from(value: $ty) -> Self {
                // TODO: Panic if the value does not fit
                SpadeUint::<N> {
                    inner: value as u64,
                }
            }
        }

        impl<const N: u64> PartialEq<$ty> for SpadeUint<N> {
            fn eq(&self, other: &$ty) -> bool {
                self.inner == *other as u64
            }
        }
    };
}
uint_methods!(u8);
uint_methods!(u16);
uint_methods!(u32);
uint_methods!(u64);

#[derive(PartialEq, Default, Debug)]
pub struct SpadeInt<const N: u64> {
    inner: u64,
}

impl<const N: u64> SpadeType for SpadeInt<N> {
    fn size() -> usize {
        N as usize
    }

    fn backward_size() -> usize {
        0
    }

    fn from_verilator_value(&mut self, _bit_offset: usize, _bits: &[u32]) {
        todo!("from_verilator_value is not currently implemented for ints")
    }

    fn to_verilator_value(&self, _bit_offset: usize, _target: &mut [u32]) {
        todo!("to_verilator_value is not currently implemented for ints")
    }
}



impl SpadeType for bool {
    fn size() -> usize {
        1
    }

    fn backward_size() -> usize {
        0
    }

    fn from_verilator_value(&mut self, bit_offset: usize, bits: &[u32]) {
        let mut buff = [0; 1];
        u32_shift_to_le(bits, bit_offset, &mut buff);
        *self = buff[0] & 1 == 1
    }

    fn to_verilator_value(&self, bit_offset: usize, target: &mut [u32]) {
        let mask = 1 << bit_offset % 32;
        if *self {
            target[bit_offset / 32] |= mask
        } else {
            target[bit_offset / 32] &= !mask;
        }
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

            fn from_verilator_value(&mut self, mut bit_offset: usize, bits: &[u32]) {
                // Tuple packing has left hand element on the msb side
                bit_offset = bit_offset + Self::size();

                #[allow(non_snake_case)]
                let ($($param),*) = self;
                $(
                    bit_offset -= $param::size();
                    $param.from_verilator_value(bit_offset, bits);
                )*
                let _ = bit_offset;
            }

            fn to_verilator_value(&self, mut bit_offset: usize, target: &mut [u32]) {
                // Tuple packing has left hand element on the msb side
                bit_offset = bit_offset + Self::size();

                #[allow(non_snake_case)]
                let ($($param),*) = self;
                $(
                    bit_offset -= $param::size();
                    $param.to_verilator_value(bit_offset, target);
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

    fn from_verilator_value(&mut self, bit_offset: usize, bits: &[u32]) {
        let mut buff = vec![0; Self::size() / 32 + 1];
        u32_shift_to_le(bits, bit_offset + T::size(), &mut buff);
        *self = if buff[0] & 1 == 1 {
            let mut inner = T::default();
            inner.from_verilator_value(bit_offset, bits);
            Some(inner)
        } else {
            None
        }
    }

    fn to_verilator_value(&self, bit_offset: usize, target: &mut [u32]) {
        let valid_bit = bit_offset + T::size();
        let valid_word = valid_bit / 32;
        let valid_in_word = valid_bit % 32;
        match self {
            Some(val) => {
                val.to_verilator_value(bit_offset, target);
                target[valid_word] |= 1 << valid_in_word;
            },
            None => {
                target[valid_word] &= !(1 << valid_in_word);
            }
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

    #[test]
    fn u32_shift_left_test() {
        //  0x0000_000f 8000_0001 f000_0000
        let input = [0xf000_0000, 0x8000_0001, 0x0000_000f];

        let mut buff = [0; 3];

        //  0x000f_8000 0001_f000 0000_0000
        u32_shift_to_be(&input, 16, &mut buff);
        assert_eq!(buff, [0, 0x001_f000, 0x000f_8000].as_slice());

        //  0x8000_0001 f000_0000 0000_0000
        u32_shift_to_be(&input, 32, &mut buff);
        assert_eq!(buff, [0, 0xf000_0000, 0x8000_0001].as_slice());

        //  0x0000_0003 e000_0000 0000_0000
        u32_shift_to_be(&input, 33, &mut buff);
        assert_eq!(buff, [0, 0xe000_0000, 0x0000_0003].as_slice());
       
    }
}
