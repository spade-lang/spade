//! Verilator-defined types for C FFI.

/// From the Verilator documentation: "Data representing 'bit' of 1-8 packed
/// bits."
pub type CData = u8;

/// From the Verilator documentation: "Data representing 'bit' of 9-16
/// packed bits"
pub type SData = u16;

/// From the Verilator documentation: "Data representing 'bit' of 17-32
/// packed bits."
pub type IData = u32;

/// From the Verilator documentation: "Data representing 'bit' of 33-64
/// packed bits."
pub type QData = u64;

/// From the Verilator documentation: "Data representing one element of
/// WData array."
pub type EData = u32;

/// From the Verilator documentation: "Data representing >64 packed bits
/// (used as pointer)."
pub type WData = EData;


/// Fills the provided buffer with the value of the signal with msb first. The caller
/// is responsible for ensuring that the buffer is wide enough to fit all digits, otherwise
/// it panics
#[doc(hidden)]
pub trait IntoU32s {
    fn populate_u32(&self, buffer: &mut [u32]);
    fn update_from_u32(&mut self, buffer: &[u32]);
}

macro_rules! small_into {
    ($ty:ty) => {
        impl IntoU32s for $ty {
            fn populate_u32(&self, buffer: &mut [u32]) {
                buffer[0] = *self as u32;
            }

            fn update_from_u32(&mut self, buffer: &[u32]) {
                *self = buffer[0] as Self;
            }
        }
    }
}

small_into!(CData);
small_into!(SData);
small_into!(IData);

impl IntoU32s for QData {
    fn populate_u32(&self, buffer: &mut [u32]) {
        buffer[1] = (*self >> 32) as u32;
        buffer[0] = (*self) as u32;
    }
    fn update_from_u32(&mut self, buffer: &[u32]) {
        *self = (buffer[1] as u64) << 32 | buffer[0] as u64
    }
}


