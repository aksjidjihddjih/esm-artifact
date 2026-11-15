//! Index helpers. This is the ONLY file where the platform-width integer type appears:
//! every public quantity in the crate is an explicit `u8/u32/u64/u128`.

#[inline]
pub(crate) fn ix(i: u32) -> usize {
    i as usize
}

/// Length of a slice as `u32` (saturating; callers bound lengths far below 2^32).
#[inline]
pub(crate) fn len32<T>(v: &[T]) -> u32 {
    match u32::try_from(v.len()) {
        Ok(x) => x,
        Err(_) => u32::MAX,
    }
}

/// `Vec` capacity hint from a `u32`.
#[inline]
pub(crate) fn cap(n: u32) -> usize {
    n as usize
}

/// Slot index from a `u64` hash position.
#[inline]
pub(crate) fn ix64(i: u64) -> usize {
    i as usize
}
