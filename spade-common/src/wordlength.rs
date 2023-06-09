use num::{BigInt, Signed};

// TODO: rename to signed
pub fn range_to_wordlength(lo: &BigInt, hi: &BigInt) -> Option<u32> {
    // NOTE: This can be considerably more fancy, taking into account the range and working
    // from there - but I'm keeping things simple for now.
    for i in 1..2048 {
        let n = BigInt::from(2).pow(i);
        if hi.abs() < n && lo.abs() < n + BigInt::from(1) {
            return Some(i + 1);
        }
    }
    None
}

// TODO: rename to signed
pub fn wordlength_to_range(wl: u32) -> (BigInt, BigInt) {
    if wl < 1 {
        return (BigInt::from(0), BigInt::from(0));
    }
    let a = -BigInt::from(2).pow(wl - 1);
    let b = BigInt::from(2).pow(wl - 1) - BigInt::from(1);
    (a.clone().min(b.clone()), a.max(b))
}

#[cfg(test)]
mod test {
    use crate::{
        num_ext::InfallibleToBigInt,
        wordlength::{range_to_wordlength, wordlength_to_range},
    };

    fn maps_back_to_itself(lo: isize, hi: isize) {
        let lo = lo.to_bigint();
        let hi = hi.to_bigint();
        let wl = range_to_wordlength(&lo, &hi).expect("Couldn't find wordlength");
        let (out_lo, out_hi) = wordlength_to_range(wl);

        assert!(
            out_lo <= lo && hi <= out_hi,
            "{hi}..{lo} => wl: {wl} => {out_lo}..{out_hi} - this mapping isn't correct!"
        );
    }

    #[test]
    fn a_bunch_of_ranges_to_wordlength_to_range() {
        for x in -100..100 {
            for y in -100..100 {
                maps_back_to_itself(y.min(x), y.max(x));
            }
        }
    }
}
