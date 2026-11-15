//! Exact integer primitives of the ESM specification over `N` (Lean `Nat`), with explicit-width types.
//!
//! Conventions (paper Sec. 3.1, `ESM_verified.lean`):
//!  * `monus(a, b) = max(a - b, 0)`            (saturating subtraction)
//!  * `div0(a, 0) = 0`                          (Lean/paper: floor(a / 0) = 0; Solidity would revert -> audit M2)
//!  * every `floor(x * y / z)` is ONE division over a 256-bit intermediate: no double rounding, no overflow.
use crate::big::Big;

/// `floor(log2 n)` for `n >= 1` (returns 0 for `n = 0`, outside the domain).
pub fn floor_log2(n: u64) -> u32 {
    if n == 0 {
        0
    } else {
        63 - n.leading_zeros()
    }
}

/// Elias-omega length: `l(1) = 1`, `l(n) = 1 + floor(log2 n) + l(floor(log2 n))`.
/// Iterative (no recursion). `n = 0` is outside the domain and returns 0.
pub fn elias_omega_len(n: u64) -> u64 {
    if n == 0 {
        return 0;
    }
    let mut total: u64 = 0;
    let mut x = n;
    while x > 1 {
        let k = floor_log2(x) as u64;
        total += 1 + k;
        x = k;
    }
    total + 1
}

/// Elias-omega length of a `Big` value `n >= 1` (returns 0 for zero).
pub fn elias_omega_len_big(n: &Big) -> u64 {
    let bl = n.bit_len();
    if bl == 0 {
        return 0;
    }
    if bl == 1 {
        return 1;
    }
    let k = (bl - 1) as u64; // floor(log2 n)
    1 + k + elias_omega_len(k)
}

#[inline]
pub fn monus(a: u128, b: u128) -> u128 {
    a.saturating_sub(b)
}

#[inline]
pub fn div0(a: u128, b: u128) -> u128 {
    if b == 0 {
        0
    } else {
        a / b
    }
}

/// `ceilDiv(a, b) = floor((a + b - 1) / b)` for `b >= 1`; `ceilDiv(a, 0) = 0` (Lean: `(a + 0 - 1) / 0 = 0`).
/// Computed as `a / b + [a mod b != 0]`, which cannot overflow.
#[inline]
pub fn ceil_div(a: u128, b: u128) -> u128 {
    if b == 0 {
        0
    } else {
        a / b + u128::from(a % b != 0)
    }
}

/// `clog2(x) = min { k : 2^k >= max(x, 1) }`.
pub fn clog2(x: u128) -> u32 {
    if x <= 1 {
        0
    } else {
        128 - (x - 1).leading_zeros()
    }
}

/// Shannon dictionary length (paper Eq. shannon_len), overflow-free form:
/// `l_E = max(1, clog2(ceilDiv(T, w)))` with `T = sum_m (W_E(m) + eps0) + eps0` and `w = W_E(u) + eps0 >= 1`.
/// Equals `min { k >= 1 : 2^k * w >= T }` by `ESM.shannon_len_ceilDiv_iff` (Lean, `w > 0`).
pub fn shannon_len(t: u128, w: u128) -> u32 {
    let k = clog2(ceil_div(t, w));
    if k < 1 {
        1
    } else {
        k
    }
}

/// 128 x 128 -> 256-bit product as `(hi, lo)`.
fn mul_wide(a: u128, b: u128) -> (u128, u128) {
    const M: u128 = (1u128 << 64) - 1;
    let (a0, a1) = (a & M, a >> 64);
    let (b0, b1) = (b & M, b >> 64);
    let p00 = a0 * b0;
    let p01 = a0 * b1;
    let p10 = a1 * b0;
    let p11 = a1 * b1;
    let mid = (p00 >> 64) + (p01 & M) + (p10 & M);
    let lo = (p00 & M) | ((mid & M) << 64);
    let hi = p11 + (p01 >> 64) + (p10 >> 64) + (mid >> 64);
    (hi, lo)
}

/// `floor((hi * 2^128 + lo) / d)`; `None` if the quotient needs more than 128 bits. Requires `d >= 1`.
fn div_wide(hi: u128, lo: u128, d: u128) -> Option<u128> {
    if hi == 0 {
        return Some(lo / d);
    }
    if hi >= d {
        return None;
    }
    let mut r = hi;
    let mut q: u128 = 0;
    let mut i: u32 = 128;
    while i > 0 {
        i -= 1;
        let carry = r >> 127;
        r = (r << 1) | ((lo >> i) & 1);
        q <<= 1;
        if carry == 1 || r >= d {
            r = r.wrapping_sub(d);
            q |= 1;
        }
    }
    Some(q)
}

/// `floor(a * b / c)` exactly over 256 bits. `c = 0` gives 0 (div0 semantics); `None` iff the quotient exceeds `u128`.
pub fn mul_div_floor(a: u128, b: u128, c: u128) -> Option<u128> {
    if c == 0 {
        return Some(0);
    }
    let (hi, lo) = mul_wide(a, b);
    div_wide(hi, lo, c)
}

/// `EscrowAlloc(B0, Phi0, d) = floor(B0 * d / Phi0)` (paper Eq. escrow_alloc). `None` only outside the frozen bounds.
pub fn escrow_alloc(b0: u128, phi0: u128, d: u128) -> Option<u128> {
    mul_div_floor(b0, d, phi0)
}

/// `R(x) = floor(gamma_bps * E_net * x / (10000 * Delta_tr))` (paper Eq. slot_royalty), a single division.
pub fn slot_royalty(gamma_bps: u128, e_net: u128, x: u128, delta_tr: u128) -> Option<u128> {
    let num = gamma_bps.checked_mul(e_net)?;
    let den = delta_tr.checked_mul(10_000)?;
    if den == 0 {
        return Some(0);
    }
    mul_div_floor(num, x, den)
}
