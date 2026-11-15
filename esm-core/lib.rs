//! `esm-core`: deterministic, dependency-free (`no_std` + `alloc`) verification core of the
//! Epistemic State Machine. The same crate is compiled as a zkVM (rv32im) guest and as a host library;
//! every quantity has an explicit width, there is no floating point, no `HashMap`, no threads, no `unsafe`.
//!
//! * [`primitives`] exact integer arithmetic (`monus`, `div0`, `ceil_div`, 256-bit `mul_div_floor`, `l_w`, ...)
//! * [`blc`]        Tromp BLC arena, strict parser / encoder
//! * [`kam`]        totalized, bounded call-by-name KAM and the Scott bit-list decoder
//! * [`mst`]        sparse/dense residual lengths and the Counted Merkle Sum Tree (injectable [`mst::Hasher`])
//! * [`bohm`]       `T6` bounded coinductive Bohm-tree beta-eta check under a single fuel budget
#![no_std]
#![forbid(unsafe_code)]

extern crate alloc;

pub mod big;
pub mod blc;
pub mod bohm;
pub mod kam;
pub mod mst;
pub mod params;
pub mod primitives;
mod util;

pub use big::Big;
pub use blc::{Arena, BlcError, EsmError, Node};
pub use primitives::{
    ceil_div, clog2, div0, elias_omega_len, escrow_alloc, floor_log2, monus, mul_div_floor, shannon_len, slot_royalty,
};
