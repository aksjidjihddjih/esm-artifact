//! Counted Merkle Sum Tree: root commitment, sums/counts, and O(log n) path verification with an injected hasher.
mod common;
use common::*;
use esm_core::mst::*;
use esm_core::{Arena, Big};

/// Non-cryptographic 256-bit mixing hasher (test double for the keccak256 precompile hasher of the guest).
struct Toy;
fn mix(mut z: u64) -> u64 {
    z = z.wrapping_add(0x9E37_79B9_7F4A_7C15);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}
fn digest(words: &[u64]) -> [u8; 32] {
    let mut s = [0x0123_4567u64, 0x89AB_CDEF, 0xFEDC_BA98, 0x7654_3210];
    for &w in words {
        for l in 0..4 {
            s[l] = mix(s[l] ^ w.rotate_left(13 * l as u32 + 1) ^ (l as u64));
        }
    }
    let mut out = [0u8; 32];
    for (i, x) in s.iter().enumerate() {
        out[8 * i..8 * i + 8].copy_from_slice(&x.to_le_bytes());
    }
    out
}
fn words(h: &[u8; 32]) -> Vec<u64> {
    h.chunks(8).map(|c| u64::from_le_bytes(c.try_into().unwrap())).collect()
}
impl Hasher for Toy {
    fn empty(&self) -> [u8; 32] {
        digest(&[0xE])
    }
    fn leaf(&self, index: u64, r: &Big, b_k: u32) -> [u8; 32] {
        let mut w = vec![1, index, b_k as u64, r.bit_len() as u64];
        let mut i = 0;
        while i < r.bit_len() {
            let mut limb = 0u64;
            for k in 0..64 {
                limb |= (r.bit(i + k) as u64) << k;
            }
            w.push(limb);
            i += 64;
        }
        digest(&w)
    }
    fn node(&self, l: &MstNode, r: &MstNode) -> [u8; 32] {
        let mut w = vec![2];
        w.extend(words(&l.hash));
        w.extend([l.sum, l.count]);
        w.extend(words(&r.hash));
        w.extend([r.sum, r.count]);
        digest(&w)
    }
}

/// Full tree levels (leaf level first), padded with empty leaves.
fn levels(res: &[Big], b_k: u32) -> Vec<Vec<MstNode>> {
    let n = res.len() as u64;
    let padded = 1usize << mst_depth(n);
    let mut lvl: Vec<MstNode> = (0..padded).map(|j| if (j as u64) < n { mst_leaf(&Toy, j as u64, &res[j], b_k) } else { mst_empty_node(&Toy) }).collect();
    let mut all = vec![lvl.clone()];
    while lvl.len() > 1 {
        lvl = lvl.chunks(2).map(|p| mst_parent(&Toy, &p[0], &p[1])).collect();
        all.push(lvl.clone());
    }
    all
}

#[test]
fn root_sums_counts_match_residual_length_and_paths_verify() {
    let g = golden_lines();
    let rows = of_kind(&g, "MSTV");
    let mut checked_paths = 0;
    for l in rows.iter().take(60) {
        let bk: u32 = n(&l[1]);
        let res: Vec<Big> = l[8..].iter().map(|h| hex_big(h)).collect();
        let m = mst_residual_len(&res, bk);
        let root = mst_root(&Toy, &res, bk);
        // the root commits exactly the dense residual length (minus the fixed header) and the outlier count
        assert_eq!(root.sum + 33, m.dense, "root sum = dense payload");
        assert_eq!(root.count, m.k_err, "root count = k_err");
        let lv = levels(&res, bk);
        assert_eq!(lv.last().unwrap()[0], root, "streaming root == full-tree root");
        // every path verifies; tampering breaks it
        let nn = res.len() as u64;
        for &idx in &[0u64, nn / 2, nn - 1] {
            let leaf = mst_leaf(&Toy, idx, &res[idx as usize], bk);
            let sib: Vec<MstNode> = (0..lv.len() - 1).map(|k| lv[k][((idx >> k) ^ 1) as usize]).collect();
            assert!(mst_verify_path(&Toy, &leaf, idx, nn, &sib, &root));
            if !sib.is_empty() {
                let mut bad = sib.clone();
                bad[0].sum += 1;
                assert!(!mst_verify_path(&Toy, &leaf, idx, nn, &bad, &root), "tampered sum must fail");
                let mut bad = sib.clone();
                bad[sib.len() - 1].count += 1;
                assert!(!mst_verify_path(&Toy, &leaf, idx, nn, &bad, &root), "tampered count must fail");
                let forged = mst_leaf(&Toy, idx, &Big::from_u64(res[idx as usize].to_u64().unwrap_or(0) ^ 1), bk);
                assert!(!mst_verify_path(&Toy, &forged, idx, nn, &sib, &root), "forged leaf must fail");
                if nn > 1 {
                    assert!(!mst_verify_path(&Toy, &leaf, (idx + 1) % nn, nn, &sib, &root) || nn == 1 || res[idx as usize] == res[((idx + 1) % nn) as usize], "wrong index");
                }
            }
            checked_paths += 1;
        }
        assert!(!mst_verify_path(&Toy, &mst_empty_node(&Toy), nn, nn, &[], &root), "index out of range");
    }
    assert!(checked_paths >= 150);
    assert_eq!(mst_root(&Toy, &[], 16), mst_empty_node(&Toy));
    let _ = Arena::new_plain();
}

#[test]
fn benchmark_residuals_commit_the_paper_lengths() {
    // Benchmark 1: all-zero residual on 1024 records -> dense payload 1024 * l_w(1) = 1024, k_err = 0, L_res = 34 (sparse wins)
    let res = vec![Big::ZERO; 1024];
    let m = mst_residual_len(&res, 16);
    assert_eq!((m.k_err, m.l_res, m.sparse, m.header), (0, 34, 34, 34));
    let root = mst_root(&Toy, &res, 16);
    assert_eq!((root.sum, root.count), (1024, 0));
    assert_eq!(mst_depth(1024), 10);
    assert_eq!(mst_depth(1), 0);
    assert_eq!(mst_depth(1025), 11);
}
