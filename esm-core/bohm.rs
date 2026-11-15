//! Bounded coinductive Bohm-tree beta-eta equivalence (`T6`), single joint fuel budget.
//!
//! Faithful port of `esm_exp1_2.{Fuel, hnf, bt_equiv, t6_check, stage2_redirect}`:
//!   fuel_total = kam + beta + nodes + work <= fuel_max <= T_max,
//! with the same charging rules (increment THEN check; bulk `touch` for the size/equality cost).
//! Differences from the reference are purely structural and never change a result or a counter:
//!  * terms are hash-consed, so `x == y` is id equality and the coinductive `seen` set is a set of id pairs;
//!  * `subst`/`shift`/`hnf`/`bt_equiv` use explicit stacks (no recursion, no recursion-limit artefacts);
//!  * a deterministic arena ceiling replaces Python's `RecursionError`/`MemoryError` (status `ResourceLimit`).
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use crate::blc::{tree_size, Arena, BlcError, EsmError, Node};
use crate::kam::{kam_whnf, Fallback, Heap, NIL};
use crate::params::KAM_HEAP_PER_STEP;

/// Why a metered computation stopped.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ex {
    /// the declared fuel ceiling was exceeded ("not established", never "equal")
    Exhausted,
    /// deterministic resource ceiling (arena / index overflow)
    Resource,
}

impl From<BlcError> for Ex {
    fn from(_: BlcError) -> Self {
        Ex::Resource
    }
}

/// Verification fuel: everything the verifier does is charged to ONE budget `cap`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fuel {
    pub cap: u64,
    /// KAM steps to evaluate `App(q, p_s)` to WHNF
    pub kam: u64,
    /// beta-reductions performed by `hnf`
    pub beta: u64,
    /// node comparisons
    pub nodes: u64,
    /// AST nodes touched by substitution / eta-shifting / equality+hashing
    pub work: u64,
    pub count_work: bool,
}

impl Fuel {
    pub fn new(cap: u64) -> Fuel {
        Fuel { cap, kam: 0, beta: 0, nodes: 0, work: 0, count_work: true }
    }

    /// Never exhausts (used for unmetered substitution, e.g. building clones in tests/tools).
    pub fn unmetered() -> Fuel {
        Fuel::new(u64::MAX)
    }

    pub fn total(&self) -> u64 {
        self.kam.saturating_add(self.beta).saturating_add(self.nodes).saturating_add(self.work)
    }

    pub fn remaining(&self) -> u64 {
        self.cap.saturating_sub(self.total())
    }

    fn check(&self) -> Result<(), Ex> {
        if self.total() > self.cap {
            Err(Ex::Exhausted)
        } else {
            Ok(())
        }
    }

    pub fn charge_kam(&mut self, n: u64) -> Result<(), Ex> {
        self.kam = self.kam.saturating_add(n);
        self.check()
    }

    pub fn beta_step(&mut self) -> Result<(), Ex> {
        self.beta = self.beta.saturating_add(1);
        self.check()
    }

    pub fn node(&mut self) -> Result<(), Ex> {
        self.nodes = self.nodes.saturating_add(1);
        self.check()
    }

    pub fn touch(&mut self, n: u64) -> Result<(), Ex> {
        if self.count_work {
            self.work = self.work.saturating_add(n);
            self.check()?;
        }
        Ok(())
    }
}

enum Fr {
    Enter(u32, u32),
    Lam,
    App,
}

/// De Bruijn shift: add `d` to every free index `>= c`. Charges one `work` unit per node visited.
pub fn shift(arena: &mut Arena, t: u32, d: u32, c0: u32, fuel: &mut Fuel) -> Result<u32, Ex> {
    let mut work: Vec<Fr> = Vec::new();
    let mut vals: Vec<u32> = Vec::new();
    work.push(Fr::Enter(t, c0));
    while let Some(fr) = work.pop() {
        match fr {
            Fr::Enter(id, c) => {
                fuel.touch(1)?;
                match arena.node(id) {
                    Node::Var(i) => {
                        if i >= c {
                            let ni = i.checked_add(d).ok_or(Ex::Resource)?;
                            vals.push(arena.mk(Node::Var(ni))?);
                        } else {
                            vals.push(id);
                        }
                    }
                    Node::Lam(b) => {
                        work.push(Fr::Lam);
                        work.push(Fr::Enter(b, c.checked_add(1).ok_or(Ex::Resource)?));
                    }
                    Node::App(f, a) => {
                        work.push(Fr::App);
                        work.push(Fr::Enter(a, c));
                        work.push(Fr::Enter(f, c));
                    }
                    Node::Mark(_) => vals.push(id),
                }
            }
            Fr::Lam => {
                let b = vals.pop().ok_or(Ex::Resource)?;
                vals.push(arena.mk(Node::Lam(b))?);
            }
            Fr::App => {
                let a = vals.pop().ok_or(Ex::Resource)?;
                let f = vals.pop().ok_or(Ex::Resource)?;
                vals.push(arena.mk(Node::App(f, a))?);
            }
        }
    }
    vals.pop().ok_or(Ex::Resource)
}

/// `t[j := s]` with the removed binder accounted for (standard de Bruijn beta substitution).
/// Charges one `work` unit per node of `t` visited, plus the shift cost of every inserted copy of `s`.
pub fn subst(arena: &mut Arena, t: u32, j0: u32, s: u32, fuel: &mut Fuel) -> Result<u32, Ex> {
    let mut work: Vec<Fr> = Vec::new();
    let mut vals: Vec<u32> = Vec::new();
    work.push(Fr::Enter(t, j0));
    while let Some(fr) = work.pop() {
        match fr {
            Fr::Enter(id, j) => {
                fuel.touch(1)?;
                match arena.node(id) {
                    Node::Var(i) => {
                        if i == j {
                            let sh = shift(arena, s, j, 0, fuel)?;
                            vals.push(sh);
                        } else if i > j {
                            vals.push(arena.mk(Node::Var(i - 1))?);
                        } else {
                            vals.push(id);
                        }
                    }
                    Node::Lam(b) => {
                        work.push(Fr::Lam);
                        work.push(Fr::Enter(b, j.checked_add(1).ok_or(Ex::Resource)?));
                    }
                    Node::App(f, a) => {
                        work.push(Fr::App);
                        work.push(Fr::Enter(a, j));
                        work.push(Fr::Enter(f, j));
                    }
                    Node::Mark(_) => vals.push(id),
                }
            }
            Fr::Lam => {
                let b = vals.pop().ok_or(Ex::Resource)?;
                vals.push(arena.mk(Node::Lam(b))?);
            }
            Fr::App => {
                let a = vals.pop().ok_or(Ex::Resource)?;
                let f = vals.pop().ok_or(Ex::Resource)?;
                vals.push(arena.mk(Node::App(f, a))?);
            }
        }
    }
    vals.pop().ok_or(Ex::Resource)
}

/// Normal-order head normal form: `(n binders, head variable index, arguments in application order)`.
/// Each beta step is charged to `fuel`. The argument spine is kept as a stack, so no term is rebuilt.
pub fn hnf(arena: &mut Arena, t: u32, fuel: &mut Fuel) -> Result<(u32, u32, Vec<u32>), Ex> {
    let mut n: u32 = 0;
    let mut args: Vec<u32> = Vec::new(); // last element = first argument
    let mut cur = t;
    loop {
        match arena.node(cur) {
            Node::App(f, a) => {
                args.push(a);
                cur = f;
            }
            Node::Lam(b) => match args.pop() {
                None => {
                    cur = b;
                    n = n.checked_add(1).ok_or(Ex::Resource)?;
                }
                Some(a0) => {
                    fuel.beta_step()?;
                    cur = subst(arena, b, 0, a0, fuel)?;
                }
            },
            Node::Var(i) => {
                args.reverse();
                return Ok((n, i, args));
            }
            Node::Mark(_) => return Err(Ex::Resource),
        }
    }
}

/// Bounded beta-eta (Bohm-tree) equivalence of two possibly open terms of a hash-consed arena.
/// Explicit stack, pre-order DFS identical to the recursive formulation; a pair already under comparison
/// counts as equal (greatest fixed point). Exhausting the fuel yields `Err(Exhausted)`, never "equal".
pub fn bt_equiv(
    arena: &mut Arena,
    a: u32,
    b: u32,
    fuel: &mut Fuel,
    seen: &mut BTreeSet<(u32, u32)>,
) -> Result<bool, Ex> {
    let mut stack: Vec<(u32, u32)> = Vec::new();
    stack.push((a, b));
    while let Some((x, y)) = stack.pop() {
        fuel.node()?;
        let rem = fuel.remaining().saturating_add(1);
        let sz = tree_size(arena, x, rem) + tree_size(arena, y, rem);
        fuel.touch(sz)?; // cost of the structural equality / hashing below
        if x == y {
            continue;
        }
        if !seen.insert((x, y)) {
            continue; // coinductive hypothesis (cycle closes)
        }
        let (n, mut h1, mut a1) = hnf(arena, x, fuel)?;
        let (m, mut h2, mut a2) = hnf(arena, y, fuel)?;
        if n < m {
            // eta-align: add m-n binders to the shorter side
            let d = m - n;
            h1 = h1.checked_add(d).ok_or(Ex::Resource)?;
            let mut na: Vec<u32> = Vec::new();
            for &u in &a1 {
                na.push(shift(arena, u, d, 0, fuel)?);
            }
            let mut i = d;
            while i > 0 {
                i -= 1;
                na.push(arena.mk(Node::Var(i))?);
            }
            a1 = na;
        } else if m < n {
            let d = n - m;
            h2 = h2.checked_add(d).ok_or(Ex::Resource)?;
            let mut na: Vec<u32> = Vec::new();
            for &u in &a2 {
                na.push(shift(arena, u, d, 0, fuel)?);
            }
            let mut i = d;
            while i > 0 {
                i -= 1;
                na.push(arena.mk(Node::Var(i))?);
            }
            a2 = na;
        }
        if h1 != h2 || a1.len() != a2.len() {
            return Ok(false);
        }
        let mut k = a1.len();
        while k > 0 {
            k -= 1;
            stack.push((a1[k], a2[k])); // first argument pair is popped (processed) first
        }
    }
    Ok(true)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum T6Status {
    Equal,
    NotEqual,
    /// declared budget exhausted (including KAM steps, open `q(p_s)`): `T6` NOT established
    FuelExhausted,
    /// deterministic arena ceiling (reference: `RecursionError` / `MemoryError`)
    ResourceLimit,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct T6Result {
    /// `Some(true)` / `Some(false)` when decided within the budget, `None` otherwise
    pub eq: Option<bool>,
    /// KAM steps of `q(p_s)` to WHNF (the `kam` counter when the check stopped early)
    pub kam: u64,
    pub fuel: Fuel,
    pub status: T6Status,
}

/// Decide `U(q(p_s)) =_{beta eta} p_i` under ONE declared budget `fuel_max` (`kam + beta + nodes + work <= fuel_max`).
/// The arena must be hash-consed and contain `p_s`, `q`, `p_i`.
pub fn t6_check(arena: &mut Arena, p_s: u32, q: u32, p_i: u32, fuel_max: u64) -> Result<T6Result, EsmError> {
    if !arena.is_interned() {
        return Err(EsmError::NotInterned);
    }
    let mut fuel = Fuel::new(fuel_max);
    let fin = |eq: Option<bool>, fuel: Fuel, status: T6Status| T6Result { eq, kam: fuel.kam, fuel, status };
    let qps = match arena.mk(Node::App(q, p_s)) {
        Ok(x) => x,
        Err(_) => return Ok(fin(None, fuel, T6Status::ResourceLimit)),
    };
    let mut heap = Heap::new(KAM_HEAP_PER_STEP.saturating_mul(fuel_max.saturating_add(1)));
    match kam_whnf(arena, &mut heap, qps, NIL, fuel_max) {
        Ok((_, _, steps)) => {
            if fuel.charge_kam(steps).is_err() {
                return Ok(fin(None, fuel, T6Status::FuelExhausted));
            }
        }
        Err(Fallback::Heap) => return Ok(fin(None, fuel, T6Status::ResourceLimit)),
        Err(_) => return Ok(fin(None, fuel, T6Status::FuelExhausted)),
    }
    let mut seen: BTreeSet<(u32, u32)> = BTreeSet::new();
    Ok(match bt_equiv(arena, qps, p_i, &mut fuel, &mut seen) {
        Ok(true) => fin(Some(true), fuel, T6Status::Equal),
        Ok(false) => fin(Some(false), fuel, T6Status::NotEqual),
        Err(Ex::Exhausted) => fin(None, fuel, T6Status::FuelExhausted),
        Err(Ex::Resource) => fin(None, fuel, T6Status::ResourceLimit),
    })
}

/// Protocol entry point: like [`t6_check`] but enforces `1 <= fuel_max <= T_max`.
pub fn t6_verify(arena: &mut Arena, p_s: u32, q: u32, p_i: u32, fuel_max: u64) -> Result<T6Result, EsmError> {
    if fuel_max < 1 || fuel_max > crate::params::T_MAX {
        return Err(EsmError::BadDelta);
    }
    t6_check(arena, p_s, q, p_i, fuel_max)
}

/// `L_red_new = |p_i| (-) (|q| + l_w(idx(v_s)))` (paper Eq. l_red_new).
pub fn l_red_new(p_i_len: u128, q_len: u128, idx_len: u128) -> u128 {
    crate::primitives::monus(p_i_len, q_len.saturating_add(idx_len))
}

/// Conditions (1), (2), (4) of `T6` on abstract state (Case A / Case B overwrite rule).
///  * `seq_s < seq_i`, `origin(v_s) = v_s`
///  * Case A (`origin(origin(v_i)) = origin(v_i)`): `L_new > L_red(v_i)` or (`L_new = L_red(v_i) >= 1` and `seq_s < seq(origin(v_i))`)
///  * Case B (orphaned origin): `L_new >= 1`
pub fn t6_accept(
    seq_s: u64,
    seq_i: u64,
    origin_s_is_root: bool,
    origin_i_is_rooted: bool,
    seq_origin_i: u64,
    l_red_i: u128,
    l_new: u128,
) -> bool {
    if !(seq_s < seq_i) || !origin_s_is_root {
        return false;
    }
    if origin_i_is_rooted {
        l_new > l_red_i || (l_new == l_red_i && l_red_i >= 1 && seq_s < seq_origin_i)
    } else {
        l_new >= 1
    }
}

/// Stage-2 redirect for one derivative (paper Eq. stage2_redirect): `(x_{i->s}, x_{i->i}, remaining R_cap)`.
pub fn stage2_redirect(a: u128, l_red: u128, r_cap: u128) -> (u128, u128, u128) {
    let x_is = a.min(l_red.min(r_cap));
    (x_is, a - x_is, r_cap - x_is)
}
