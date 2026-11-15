//! Counted Merkle Sum Tree (paper Sec. 3.1 / Appendix A): exact residual description length and node commitments.
//!
//! * `L_res = min(L_sparse, L_dense)`
//!   `L_sparse = l_w(k_err + 1) + C_HDR + sum_m (l_w(dj_m) + b_k)`   (`dj_1 = j_1 + 1`, `dj_m = j_m - j_{m-1}`)
//!   `L_dense  = C_HDR + sum_j l_w(r_j + 1)`                          (unsigned residual, `biject = id`)
//! * every node commits `(hash, sum of l_w(r_j + 1), count of non-zero residuals)`; the tree is padded to
//!   `2^clog2(n_k)` leaves with the canonical empty leaf. Hashing is injected via [`Hasher`] (keccak256 in
//!   production; the guest uses the zkVM precompile), so `esm-core` itself has no dependency.
use alloc::vec::Vec;

use crate::big::Big;
use crate::params::C_HDR;
use crate::util::ix64;
use crate::primitives::{clog2, elias_omega_len, elias_omega_len_big};

/// Exact residual description lengths.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ResLen {
    pub k_err: u64,
    pub sparse: u64,
    pub dense: u64,
    /// `min(sparse, dense)`
    pub l_res: u64,
    /// `l_w(k_err + 1) + C_HDR`
    pub header: u64,
}

/// Streaming accumulator (O(1) memory): feed the residual `r_j = y_j xor y_hat_j` in record order.
pub struct ResidualLen {
    b_k: u32,
    next_index: u64,
    last_nonzero: u64,
    have_last: bool,
    k_err: u64,
    gap_sum: u64,
    dense_sum: u64,
}

impl ResidualLen {
    pub fn new(b_k: u32) -> ResidualLen {
        ResidualLen { b_k, next_index: 0, last_nonzero: 0, have_last: false, k_err: 0, gap_sum: 0, dense_sum: 0 }
    }

    pub fn push(&mut self, r: &Big) {
        let j = self.next_index;
        self.next_index += 1;
        self.dense_sum += elias_omega_len_big(&r.add_one());
        if !r.is_zero() {
            let gap = if self.have_last { j - self.last_nonzero } else { j + 1 };
            self.gap_sum += elias_omega_len(gap) + self.b_k as u64;
            self.last_nonzero = j;
            self.have_last = true;
            self.k_err += 1;
        }
    }

    pub fn finish(&self) -> ResLen {
        let header = elias_omega_len(self.k_err + 1) + C_HDR;
        let sparse = header + self.gap_sum;
        let dense = C_HDR + self.dense_sum;
        ResLen { k_err: self.k_err, sparse, dense, l_res: if sparse < dense { sparse } else { dense }, header }
    }
}

/// Residual description length of a whole residual vector.
pub fn mst_residual_len(res: &[Big], b_k: u32) -> ResLen {
    let mut acc = ResidualLen::new(b_k);
    for r in res {
        acc.push(r);
    }
    acc.finish()
}

/// Hash injection point. All methods must be deterministic and collision resistant in production.
pub trait Hasher {
    /// commitment of a padding leaf
    fn empty(&self) -> [u8; 32];
    /// commitment of leaf `index` holding residual `residual` (`b_k` bits wide)
    fn leaf(&self, index: u64, residual: &Big, b_k: u32) -> [u8; 32];
    /// commitment of an internal node: must bind both child hashes, sums and counts
    fn node(&self, left: &MstNode, right: &MstNode) -> [u8; 32];
}

/// Counted Merkle Sum Tree node.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MstNode {
    pub hash: [u8; 32],
    /// sum of `l_w(r_j + 1)` over the subtree's leaves (padding leaves contribute 0)
    pub sum: u64,
    /// number of non-zero residuals in the subtree
    pub count: u64,
}

pub fn mst_empty_node<H: Hasher>(h: &H) -> MstNode {
    MstNode { hash: h.empty(), sum: 0, count: 0 }
}

pub fn mst_leaf<H: Hasher>(h: &H, index: u64, r: &Big, b_k: u32) -> MstNode {
    MstNode {
        hash: h.leaf(index, r, b_k),
        sum: elias_omega_len_big(&r.add_one()),
        count: u64::from(!r.is_zero()),
    }
}

pub fn mst_parent<H: Hasher>(h: &H, l: &MstNode, r: &MstNode) -> MstNode {
    MstNode { hash: h.node(l, r), sum: l.sum.saturating_add(r.sum), count: l.count.saturating_add(r.count) }
}

/// Tree depth `clog2(n_k)`.
pub fn mst_depth(n_k: u64) -> u32 {
    clog2(n_k as u128)
}

/// Root of the Counted MST over `residuals` (`O(log n)` memory). `n = 0` gives the empty node.
pub fn mst_root<H: Hasher>(h: &H, residuals: &[Big], b_k: u32) -> MstNode {
    let n = residuals.len() as u64;
    if n == 0 {
        return mst_empty_node(h);
    }
    let padded: u64 = 1u64 << mst_depth(n);
    let mut stack: Vec<(u32, MstNode)> = Vec::new();
    let mut j: u64 = 0;
    while j < padded {
        let leaf = if j < n { mst_leaf(h, j, &residuals[ix64(j)], b_k) } else { mst_empty_node(h) };
        let mut cur = (0u32, leaf);
        loop {
            match stack.last() {
                Some(&(lvl, left)) if lvl == cur.0 => {
                    stack.pop();
                    cur = (lvl + 1, mst_parent(h, &left, &cur.1));
                }
                _ => break,
            }
        }
        stack.push(cur);
        j += 1;
    }
    match stack.pop() {
        Some((_, root)) => root,
        None => mst_empty_node(h),
    }
}

/// Verify an `O(log n)` Merkle-sum path: `siblings[level]` is the sibling at `level` (leaf level first).
pub fn mst_verify_path<H: Hasher>(
    h: &H,
    leaf: &MstNode,
    index: u64,
    n_k: u64,
    siblings: &[MstNode],
    root: &MstNode,
) -> bool {
    if index >= n_k || siblings.len() as u64 != mst_depth(n_k) as u64 {
        return false;
    }
    let mut cur = *leaf;
    for (level, sib) in siblings.iter().enumerate() {
        cur = if (index >> level) & 1 == 0 { mst_parent(h, &cur, sib) } else { mst_parent(h, sib, &cur) };
    }
    cur == *root
}
