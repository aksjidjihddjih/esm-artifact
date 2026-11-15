//! Frozen parameters (mirror of `spec/params.toml`; `tests/params_sync.rs` enforces equality).

/// Per-record KAM step ceiling `T_max = 2^20`.
pub const T_MAX: u64 = 1 << 20;
/// Launch-profile cap on declared `delta` / `fuel_max` (`2^16`). Enforced by the protocol layer, see [`delta_in_profile`].
pub const DELTA_CAP_V1: u64 = 1 << 16;
/// Largest program length in bits.
pub const MAX_PROG_BITS: u32 = 65_536;
/// Largest de Bruijn index accepted by the parser: `idx > 255` is a syntax error (Step 2: a lookup costs `idx` hops but 1 step).
pub const MAX_DEBRUIJN_INDEX: u32 = 255;
/// Closure/environment arena cells granted per declared step (audit M5).
pub const KAM_HEAP_PER_STEP: u64 = 16;
/// Largest dataset size `n_k` and record width `b_k` (`Phi_0 <= 2^40`).
pub const MAX_N_K: u64 = 1 << 30;
pub const MAX_B_K: u32 = 1 << 10;
/// Minted-supply cap `2^96 - 1` (smallest-unit tokens).
pub const MINT_CAP: u128 = (1u128 << 96) - 1;
pub const MAX_CITED_AXIOMS: u32 = 16;
pub const MAX_RBF_SPONSORS: u32 = 10;
/// Fixed MST header (paper Sec. 3.1).
pub const C_HDR: u64 = 33;

pub const N_COM: u64 = 100;
pub const N_DELAY: u64 = 20;
pub const N_REV: u64 = 180;
pub const N_BATCH: u64 = 300;
pub const N_EPOCH: u64 = 49_800;
pub const N_LOCK: u64 = 50_000;

pub const EPSILON_BPS: u64 = 500;
pub const GAMMA_BPS: u64 = 2000;
pub const BETA_D_BPS: u64 = 1000;
pub const KAPPA_BPS: u64 = 7000;
pub const SIGMA_COL_BPS: u64 = 10_000;
pub const SIGMA_DICT_BPS: u64 = 10_000;
pub const M_CAP_BPS: u64 = 20_000;

/// `true` iff `delta` respects the v1 launch profile (`1 <= delta <= DELTA_CAP_V1`).
pub fn delta_in_profile(delta: u64) -> bool {
    delta >= 1 && delta <= DELTA_CAP_V1
}
