/-! ================================================================
    Companion Lemma to ESM_verified.lean (1,111 lines, 53 theorems)
    Shannon dictionary code length l_E overflow-safe equivalence:
      T <= 2^k * w  <->  ceilDiv T w <= 2^k      (w > 0)
    In Solidity (uint256), l_E is computed via the RHS (comparing ceilDiv with 2^k).
    ================================================================ -/
namespace ESM

def ceilDiv (a b : Nat) : Nat :=
  (a + b - 1) / b

/-- [Lemma: Overflow-safe equivalence for Shannon dictionary code length]
    For w > 0, T <= 2^k * w is equivalent to ceilDiv T w <= 2^k. -/
theorem shannon_len_ceilDiv_iff (k w T : Nat) (hw : 0 < w) :
    T ≤ 2 ^ k * w ↔ ceilDiv T w ≤ 2 ^ k := by
  unfold ceilDiv
  have h1 : (T + w - 1) / w ≤ 2 ^ k ↔ (T + w - 1) / w < 2 ^ k + 1 :=
    Nat.lt_succ_iff.symm
  rw [h1, Nat.div_lt_iff_lt_mul hw]
  have h2 : (2 ^ k + 1) * w = 2 ^ k * w + w := by
    rw [Nat.add_mul, Nat.one_mul]
  rw [h2]
  omega

end ESM
