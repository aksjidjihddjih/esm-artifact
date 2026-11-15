//! Fixed-width (1088-bit) unsigned integer: enough for a `b_k <= 1024`-bit record plus the `+1` of `l_w(r + 1)`.
use crate::util::ix;

pub const BIG_LIMBS: u32 = 17;
pub const BIG_BITS: u32 = 64 * BIG_LIMBS;

/// Little-endian 17 x u64. Values are always `< 2^1088`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Big {
    limbs: [u64; 17],
}

impl Default for Big {
    fn default() -> Self {
        Big::ZERO
    }
}

impl Big {
    pub const ZERO: Big = Big { limbs: [0; 17] };

    pub fn from_u64(x: u64) -> Big {
        let mut b = Big::ZERO;
        b.limbs[0] = x;
        b
    }

    /// Little-endian limbs; `None` if a non-zero limb does not fit.
    pub fn from_limbs_le(l: &[u64]) -> Option<Big> {
        let mut b = Big::ZERO;
        for (i, &x) in l.iter().enumerate() {
            if i < 17 {
                b.limbs[i] = x;
            } else if x != 0 {
                return None;
            }
        }
        Some(b)
    }

    pub fn is_zero(&self) -> bool {
        self.limbs.iter().all(|&x| x == 0)
    }

    /// Number of significant bits (0 for zero).
    pub fn bit_len(&self) -> u32 {
        let mut i: u32 = BIG_LIMBS;
        while i > 0 {
            i -= 1;
            let l = self.limbs[ix(i)];
            if l != 0 {
                return i * 64 + (64 - l.leading_zeros());
            }
        }
        0
    }

    pub fn bit(&self, i: u32) -> u8 {
        if i >= BIG_BITS {
            return 0;
        }
        ((self.limbs[ix(i / 64)] >> (i % 64)) & 1) as u8
    }

    pub fn set_bit(&mut self, i: u32) {
        if i < BIG_BITS {
            self.limbs[ix(i / 64)] |= 1u64 << (i % 64);
        }
    }

    pub fn xor(&self, o: &Big) -> Big {
        let mut r = Big::ZERO;
        let mut i: u32 = 0;
        while i < BIG_LIMBS {
            r.limbs[ix(i)] = self.limbs[ix(i)] ^ o.limbs[ix(i)];
            i += 1;
        }
        r
    }

    /// `self + 1` (wraps modulo 2^1088; unreachable for values below 2^1025).
    pub fn add_one(&self) -> Big {
        let mut r = *self;
        let mut i: u32 = 0;
        while i < BIG_LIMBS {
            let (v, c) = r.limbs[ix(i)].overflowing_add(1);
            r.limbs[ix(i)] = v;
            if !c {
                break;
            }
            i += 1;
        }
        r
    }

    pub fn to_u64(&self) -> Option<u64> {
        if self.limbs[1..].iter().all(|&x| x == 0) {
            Some(self.limbs[0])
        } else {
            None
        }
    }

    /// `true` iff the value is `< 2^w`.
    pub fn fits_bits(&self, w: u32) -> bool {
        self.bit_len() <= w
    }
}
