//! Tromp binary lambda calculus: de Bruijn terms in an arena, parser and encoder (all iterative).
//!
//! Encoding: `00 M` = lambda, `01 M N` = application, `1^(i+1) 0` = variable with de Bruijn index `i`.
//! Strict parsing: a program is accepted iff it is exactly one well-formed term occupying all bits
//! (no malformed variable, no trailing bits, at most `MAX_PROG_BITS` bits).
use alloc::vec::Vec;

use crate::params::{MAX_DEBRUIJN_INDEX, MAX_PROG_BITS};
use crate::util::{cap, ix, ix64, len32};

/// Hard ceiling on arena nodes (deterministic resource limit, never a panic).
pub const ARENA_LIMIT: u32 = 1 << 22;
const EMPTY: u32 = u32::MAX;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Node {
    Var(u32),
    Lam(u32),
    App(u32, u32),
    /// Opaque decoder marker (MK0 = 0, MK1 = 1, MKEND = 2). Never produced by the parser.
    Mark(u8),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BlcError {
    Empty,
    TooLong,
    Malformed,
    TrailingBits,
    BadSymbol,
    ArenaLimit,
    NotEncodable,
    /// a variable with de Bruijn index `> MAX_DEBRUIJN_INDEX`
    IndexTooLarge,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EsmError {
    /// declared step ceiling outside `1..=T_MAX`
    BadDelta,
    /// record width outside `1..=MAX_B_K`
    BadWidth,
    Blc(BlcError),
    /// operation requires a hash-consed arena
    NotInterned,
}

impl From<BlcError> for EsmError {
    fn from(e: BlcError) -> Self {
        EsmError::Blc(e)
    }
}

/// Node arena. `plain` arenas append blindly (used by the KAM, truncated after each run);
/// `interned` arenas hash-cons, so structural equality is id equality (used by the Bohm-tree verifier).
pub struct Arena {
    nodes: Vec<Node>,
    table: Vec<u32>,
    interned: bool,
}

fn mix(mut z: u64) -> u64 {
    z = z.wrapping_add(0x9E37_79B9_7F4A_7C15);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

fn node_hash(n: &Node) -> u64 {
    let (t, a, b): (u64, u32, u32) = match *n {
        Node::Var(i) => (1, i, 0),
        Node::Lam(b) => (2, b, 0),
        Node::App(f, a) => (3, f, a),
        Node::Mark(k) => (4, k as u32, 0),
    };
    mix(mix(t ^ mix(a as u64)) ^ (b as u64))
}

impl Arena {
    pub fn new_plain() -> Arena {
        Arena { nodes: Vec::new(), table: Vec::new(), interned: false }
    }

    pub fn new_interned() -> Arena {
        let mut table = Vec::new();
        table.resize(16, EMPTY);
        Arena { nodes: Vec::new(), table, interned: true }
    }

    pub fn is_interned(&self) -> bool {
        self.interned
    }

    pub fn len(&self) -> u32 {
        len32(&self.nodes)
    }

    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    #[inline]
    pub fn node(&self, id: u32) -> Node {
        self.nodes[ix(id)]
    }

    /// Drop every node with id `>= n` (plain arenas only; a no-op on interned arenas).
    pub fn truncate(&mut self, n: u32) {
        if !self.interned {
            self.nodes.truncate(ix(n));
        }
    }

    fn grow(&mut self) {
        let new_len = self.table.len() * 2;
        let mut t: Vec<u32> = Vec::new();
        t.resize(new_len, EMPTY);
        let mask = (new_len - 1) as u64;
        let mut id: u32 = 0;
        while id < self.len() {
            let mut s = node_hash(&self.nodes[ix(id)]) & mask;
            while t[ix64(s)] != EMPTY {
                s = (s + 1) & mask;
            }
            t[ix64(s)] = id;
            id += 1;
        }
        self.table = t;
    }

    /// Allocate (or, when interned, look up) a node.
    pub fn mk(&mut self, n: Node) -> Result<u32, BlcError> {
        if !self.interned {
            if self.len() >= ARENA_LIMIT {
                return Err(BlcError::ArenaLimit);
            }
            self.nodes.push(n);
            return Ok(self.len() - 1);
        }
        let mask = (self.table.len() - 1) as u64;
        let mut s = node_hash(&n) & mask;
        loop {
            let id = self.table[ix64(s)];
            if id == EMPTY {
                break;
            }
            if self.nodes[ix(id)] == n {
                return Ok(id);
            }
            s = (s + 1) & mask;
        }
        if self.len() >= ARENA_LIMIT {
            return Err(BlcError::ArenaLimit);
        }
        self.nodes.push(n);
        let id = self.len() - 1;
        self.table[ix64(s)] = id;
        if self.nodes.len() * 2 > self.table.len() {
            self.grow();
        }
        Ok(id)
    }

    pub fn var(&mut self, i: u32) -> Result<u32, BlcError> {
        self.mk(Node::Var(i))
    }
    pub fn lam(&mut self, b: u32) -> Result<u32, BlcError> {
        self.mk(Node::Lam(b))
    }
    pub fn app(&mut self, f: u32, a: u32) -> Result<u32, BlcError> {
        self.mk(Node::App(f, a))
    }
}

/// Parse a BLC program given as bits (one `0`/`1` per byte). Iterative; deterministic.
pub fn parse_blc(arena: &mut Arena, bits: &[u8]) -> Result<u32, BlcError> {
    enum Fr {
        Lam,
        AppFn,
        AppArg(u32),
    }
    let n = len32(bits);
    if n == 0 {
        return Err(BlcError::Empty);
    }
    if n > MAX_PROG_BITS {
        return Err(BlcError::TooLong);
    }
    if bits.iter().any(|&b| b > 1) {
        return Err(BlcError::BadSymbol);
    }
    let mut frames: Vec<Fr> = Vec::new();
    let mut p: u32 = 0;
    let root;
    'outer: loop {
        // read the head of one term
        if p + 1 < n && bits[ix(p)] == 0 && bits[ix(p + 1)] == 0 {
            frames.push(Fr::Lam);
            p += 2;
            continue;
        }
        if p + 1 < n && bits[ix(p)] == 0 && bits[ix(p + 1)] == 1 {
            frames.push(Fr::AppFn);
            p += 2;
            continue;
        }
        let mut ones: u32 = 0;
        while p < n && bits[ix(p)] == 1 {
            ones += 1;
            p += 1;
        }
        if ones == 0 || p >= n || bits[ix(p)] != 0 {
            return Err(BlcError::Malformed);
        }
        p += 1;
        if ones - 1 > MAX_DEBRUIJN_INDEX {
            return Err(BlcError::IndexTooLarge);
        }
        let mut val = arena.var(ones - 1)?;
        // reduce completed sub-terms
        loop {
            match frames.pop() {
                None => {
                    root = val;
                    break 'outer;
                }
                Some(Fr::Lam) => {
                    val = arena.lam(val)?;
                }
                Some(Fr::AppFn) => {
                    frames.push(Fr::AppArg(val));
                    break;
                }
                Some(Fr::AppArg(f)) => {
                    val = arena.app(f, val)?;
                }
            }
        }
    }
    if p != n {
        return Err(BlcError::TrailingBits);
    }
    Ok(root)
}

/// Append the BLC encoding of `t` (one bit per byte). Fails on decoder markers.
pub fn encode_blc(arena: &Arena, t: u32, out: &mut Vec<u8>) -> Result<(), BlcError> {
    let mut stack: Vec<u32> = Vec::new();
    stack.push(t);
    while let Some(id) = stack.pop() {
        match arena.node(id) {
            Node::Lam(b) => {
                out.push(0);
                out.push(0);
                stack.push(b);
            }
            Node::App(f, a) => {
                out.push(0);
                out.push(1);
                stack.push(a);
                stack.push(f);
            }
            Node::Var(i) => {
                let mut k: u32 = 0;
                while k <= i {
                    out.push(1);
                    k += 1;
                }
                out.push(0);
            }
            Node::Mark(_) => return Err(BlcError::NotEncodable),
        }
    }
    Ok(())
}

/// Encoded length in bits (no allocation of the bit string).
pub fn encoded_len(arena: &Arena, t: u32) -> Result<u64, BlcError> {
    let mut total: u64 = 0;
    let mut stack: Vec<u32> = Vec::new();
    stack.push(t);
    while let Some(id) = stack.pop() {
        match arena.node(id) {
            Node::Lam(b) => {
                total += 2;
                stack.push(b);
            }
            Node::App(f, a) => {
                total += 2;
                stack.push(a);
                stack.push(f);
            }
            Node::Var(i) => total += i as u64 + 2,
            Node::Mark(_) => return Err(BlcError::NotEncodable),
        }
    }
    Ok(total)
}

/// Structural equality (iterative; works on plain and interned arenas).
pub fn structural_eq(arena: &Arena, a: u32, b: u32) -> bool {
    let mut stack: Vec<(u32, u32)> = Vec::new();
    stack.push((a, b));
    while let Some((x, y)) = stack.pop() {
        if x == y {
            continue;
        }
        match (arena.node(x), arena.node(y)) {
            (Node::Var(i), Node::Var(j)) => {
                if i != j {
                    return false;
                }
            }
            (Node::Mark(i), Node::Mark(j)) => {
                if i != j {
                    return false;
                }
            }
            (Node::Lam(p), Node::Lam(q)) => stack.push((p, q)),
            (Node::App(f1, a1), Node::App(f2, a2)) => {
                stack.push((a1, a2));
                stack.push((f1, f2));
            }
            _ => return false,
        }
    }
    true
}

/// Node count of the TREE denoted by `t`, stopping as soon as it exceeds `limit` (returns `limit + 1` then).
/// Mirrors the reference `_size(t, limit)`: a huge term can never stall the verifier.
pub fn tree_size(arena: &Arena, t: u32, limit: u64) -> u64 {
    let mut n: u64 = 0;
    let mut stack: Vec<u32> = Vec::with_capacity(cap(16));
    stack.push(t);
    while let Some(id) = stack.pop() {
        n += 1;
        if n > limit {
            return n;
        }
        match arena.node(id) {
            Node::Lam(b) => stack.push(b),
            Node::App(f, a) => {
                stack.push(a);
                stack.push(f);
            }
            _ => {}
        }
    }
    n
}
