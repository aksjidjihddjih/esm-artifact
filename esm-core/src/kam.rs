//! Totalized, bounded call-by-name Krivine Abstract Machine (canonical `U_BLC^{T_max}`).
//!
//! Step accounting (paper Sec. 3.1(ii), identical to `esm_exp1_2.kam_whnf`): one step per application push,
//! per beta-pop and per de Bruijn lookup; the (budget+1)-th step is refused BEFORE it is performed.
//!
//! Totalization: step ceiling exceeded, non-bit output, open term, list too short, unparseable program,
//! decoder marker applied to arguments, or arena exhaustion  =>  `y_hat = 0^{b_k}`, `steps = delta`, `ok = false`.
//! Nothing in this module panics on any input.
use alloc::vec::Vec;

use crate::big::Big;
use crate::blc::{parse_blc, Arena, BlcError, EsmError, Node};
use crate::params::{KAM_HEAP_PER_STEP, MAX_B_K, T_MAX};
use crate::util::{cap, ix, len32};

pub const NIL: u32 = u32::MAX;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fallback {
    /// more than `budget` steps would be needed
    StepCeiling,
    /// non-bit output, open term, short list, or marker applied to arguments
    NonBit,
    /// closure/environment arena (or term arena) exhausted (audit M5)
    Heap,
}

impl From<BlcError> for Fallback {
    fn from(_: BlcError) -> Self {
        Fallback::Heap
    }
}

/// Bounded closure / environment-cell arena.
pub struct Heap {
    clos: Vec<(u32, u32)>,
    envs: Vec<(u32, u32)>,
    allocs: u64,
    limit: u64,
}

impl Heap {
    pub fn new(limit: u64) -> Heap {
        Heap { clos: Vec::new(), envs: Vec::new(), allocs: 0, limit }
    }

    /// Cells allocated so far.
    pub fn allocs(&self) -> u64 {
        self.allocs
    }

    fn alloc_clo(&mut self, term: u32, env: u32) -> Result<u32, Fallback> {
        if self.allocs >= self.limit {
            return Err(Fallback::Heap);
        }
        self.allocs += 1;
        self.clos.push((term, env));
        Ok(len32(&self.clos) - 1)
    }

    fn alloc_env(&mut self, clo: u32, parent: u32) -> Result<u32, Fallback> {
        if self.allocs >= self.limit {
            return Err(Fallback::Heap);
        }
        self.allocs += 1;
        self.envs.push((clo, parent));
        Ok(len32(&self.envs) - 1)
    }

    #[inline]
    fn clo(&self, id: u32) -> (u32, u32) {
        self.clos[ix(id)]
    }

    #[inline]
    fn env(&self, id: u32) -> (u32, u32) {
        self.envs[ix(id)]
    }
}

/// Call-by-name KAM to weak head normal form. Returns `(term, env, steps)` of the resulting closure.
pub fn kam_whnf(
    arena: &Arena,
    heap: &mut Heap,
    term0: u32,
    env0: u32,
    budget: u64,
) -> Result<(u32, u32, u64), Fallback> {
    let mut stack: Vec<u32> = Vec::new();
    let (mut term, mut env) = (term0, env0);
    let mut steps: u64 = 0;
    loop {
        match arena.node(term) {
            Node::App(f, a) => {
                if steps >= budget {
                    return Err(Fallback::StepCeiling);
                }
                steps += 1;
                let c = heap.alloc_clo(a, env)?;
                stack.push(c);
                term = f;
            }
            Node::Lam(b) => {
                let c = match stack.pop() {
                    None => return Ok((term, env, steps)),
                    Some(c) => c,
                };
                if steps >= budget {
                    return Err(Fallback::StepCeiling);
                }
                steps += 1;
                env = heap.alloc_env(c, env)?;
                term = b;
            }
            Node::Mark(_) => {
                if !stack.is_empty() {
                    return Err(Fallback::NonBit);
                }
                return Ok((term, env, steps));
            }
            Node::Var(i) => {
                if steps >= budget {
                    return Err(Fallback::StepCeiling);
                }
                steps += 1;
                let mut e = env;
                let mut k: u32 = 0;
                while k < i {
                    if e == NIL {
                        return Err(Fallback::NonBit); // open term: unbound de Bruijn index
                    }
                    e = heap.env(e).1;
                    k += 1;
                }
                if e == NIL {
                    return Err(Fallback::NonBit);
                }
                let (c, _) = heap.env(e);
                let (t2, e2) = heap.clo(c);
                term = t2;
                env = e2;
            }
        }
    }
}

struct Markers {
    sel_head: u32,
    sel_tail: u32,
    mk0: u32,
    mk1: u32,
    mkend: u32,
}

fn markers(a: &mut Arena) -> Result<Markers, Fallback> {
    let v1 = a.var(1)?;
    let l1 = a.lam(v1)?;
    let sel_head = a.lam(l1)?; // \h.\t.h
    let v0 = a.var(0)?;
    let l0 = a.lam(v0)?;
    let sel_tail = a.lam(l0)?; // \h.\t.t
    Ok(Markers {
        sel_head,
        sel_tail,
        mk0: a.mk(Node::Mark(0))?,
        mk1: a.mk(Node::Mark(1))?,
        mkend: a.mk(Node::Mark(2))?,
    })
}

/// Scott-encoded LSB-first bit list of `j` (`width` bits; bits at positions >= 64 are 0).
fn scott_list(a: &mut Arena, j: u64, width: u32) -> Result<u32, Fallback> {
    let v0 = a.var(0)?;
    let l = a.lam(v0)?;
    let mut t = a.lam(l)?; // nil = \c.\n.n
    let mut i = width;
    while i > 0 {
        i -= 1;
        let b = if i < 64 { (j >> i) & 1 } else { 0 };
        let vb = a.var(if b == 0 { 1 } else { 0 })?;
        let lb = a.lam(vb)?;
        let bit = a.lam(lb)?; // B0 = \a.\b.a , B1 = \a.\b.b
        let c1 = a.var(1)?;
        let ap1 = a.app(c1, bit)?;
        let ap2 = a.app(ap1, t)?;
        let inner = a.lam(ap2)?;
        t = a.lam(inner)?; // cons h t = \c.\n.c h t
    }
    Ok(t)
}

/// Lazily read `width` bits (LSB first) from a Scott list closure; returns `(value, steps)`.
fn decode_bits(
    a: &mut Arena,
    heap: &mut Heap,
    mk: &Markers,
    term: u32,
    env: u32,
    width: u32,
    budget: u64,
) -> Result<(Big, u64), Fallback> {
    let mut total: u64 = 0;
    let mut val = Big::ZERO;
    let (mut cur_t, mut cur_e) = (term, env);
    let mut i: u32 = 0;
    while i < width {
        let h1 = a.app(cur_t, mk.sel_head)?;
        let head = a.app(h1, mk.mkend)?;
        let (ht, he, s) = kam_whnf(a, heap, head, cur_e, budget - total)?;
        total += s;
        if let Node::Mark(_) = a.node(ht) {
            return Err(Fallback::NonBit); // list too short
        }
        let p1 = a.app(ht, mk.mk0)?;
        let probe = a.app(p1, mk.mk1)?;
        let (rt, _re, s) = kam_whnf(a, heap, probe, he, budget - total)?;
        total += s;
        let bit = match a.node(rt) {
            Node::Mark(0) => 0u8,
            Node::Mark(1) => 1u8,
            _ => return Err(Fallback::NonBit),
        };
        if bit == 1 {
            val.set_bit(i);
        }
        let t1 = a.app(cur_t, mk.sel_tail)?;
        let tail = a.app(t1, mk.mkend)?;
        let (nt, ne, s) = kam_whnf(a, heap, tail, cur_e, budget - total)?;
        total += s;
        cur_t = nt;
        cur_e = ne;
        i += 1;
    }
    Ok((val, total))
}

/// Result of the totalized evaluation of one record.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RunOutcome {
    /// `y_hat` (`width` bits), `0` on fallback
    pub value: Big,
    /// consumed steps; the full declared `delta` on fallback
    pub steps: u64,
    pub ok: bool,
}

/// Arena cells granted to one run: `KAM_HEAP_PER_STEP * (delta + width + 1)` (audit M5).
/// A run that stays within `delta` steps allocates at most `delta + 3 * width + 1` cells, so for in-spec
/// executions the guard is never reached; it exists to make resource exhaustion a deterministic fallback.
pub fn heap_limit(delta: u64, width: u32) -> u64 {
    KAM_HEAP_PER_STEP.saturating_mul(delta.saturating_add(width as u64).saturating_add(1))
}

fn run_inner(
    arena: &mut Arena,
    prog: u32,
    args: &[u32],
    j: u64,
    width: u32,
    delta: u64,
    heap_limit: u64,
) -> Result<(Big, u64), Fallback> {
    let mk = markers(arena)?;
    let mut t = prog;
    for &a in args {
        t = arena.app(t, a)?;
    }
    let sl = scott_list(arena, j, width)?;
    t = arena.app(t, sl)?;
    let mut heap = Heap::new(heap_limit);
    let (wt, we, s) = kam_whnf(arena, &mut heap, t, NIL, delta)?;
    let (v, s2) = decode_bits(arena, &mut heap, &mk, wt, we, width, delta - s)?;
    Ok((v, s + s2))
}

fn outcome(r: Result<(Big, u64), Fallback>, delta: u64) -> RunOutcome {
    match r {
        Ok((value, steps)) => RunOutcome { value, steps, ok: true },
        Err(_) => RunOutcome { value: Big::ZERO, steps: delta, ok: false },
    }
}

fn check_range(width: u32, delta: u64) -> Result<(), EsmError> {
    if delta < 1 || delta > T_MAX {
        return Err(EsmError::BadDelta);
    }
    if width < 1 || width > MAX_B_K {
        return Err(EsmError::BadWidth);
    }
    Ok(())
}

/// Canonical totalized evaluation of `prog args... (scott j)` (paper Sec. 3.1(ii)).
/// `Err` only for protocol-level range violations (`delta`, `width`); evaluation itself is total.
/// On a plain arena, every node created by the run is discarded afterwards.
pub fn run_program_total(
    arena: &mut Arena,
    prog: u32,
    args: &[u32],
    j: u64,
    width: u32,
    delta: u64,
) -> Result<RunOutcome, EsmError> {
    run_program_total_with_heap_limit(arena, prog, args, j, width, delta, heap_limit(delta, width))
}

/// Same as [`run_program_total`] with an explicit arena budget (test hook for the M5 guard).
pub fn run_program_total_with_heap_limit(
    arena: &mut Arena,
    prog: u32,
    args: &[u32],
    j: u64,
    width: u32,
    delta: u64,
    heap_limit: u64,
) -> Result<RunOutcome, EsmError> {
    check_range(width, delta)?;
    let base = arena.len();
    let r = run_inner(arena, prog, args, j, width, delta, heap_limit);
    arena.truncate(base);
    Ok(outcome(r, delta))
}

/// Evaluation over ARBITRARY bit strings: an unparseable program (or argument) also falls back to `0^{b_k}`.
/// `arg_bits` are BLC encodings of the closed argument terms applied before the record index.
pub fn run_bits_total(
    arena: &mut Arena,
    prog_bits: &[u8],
    arg_bits: &[&[u8]],
    j: u64,
    width: u32,
    delta: u64,
) -> Result<RunOutcome, EsmError> {
    check_range(width, delta)?;
    let base = arena.len();
    let fallback = RunOutcome { value: Big::ZERO, steps: delta, ok: false };
    let prog = match parse_blc(arena, prog_bits) {
        Ok(p) => p,
        Err(_) => {
            arena.truncate(base);
            return Ok(fallback);
        }
    };
    let mut args: Vec<u32> = Vec::with_capacity(cap(len32(arg_bits)));
    for ab in arg_bits {
        match parse_blc(arena, ab) {
            Ok(a) => args.push(a),
            Err(_) => {
                arena.truncate(base);
                return Ok(fallback);
            }
        }
    }
    let r = run_inner(arena, prog, &args, j, width, delta, heap_limit(delta, width));
    arena.truncate(base);
    Ok(outcome(r, delta))
}
