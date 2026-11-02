# Epistemic State Machine (ESM) — Mechanized Accounting & Empirical Artifact

This repository contains the formal verification artifact in Lean 4.22.0 and the self-contained Python 3 reference implementations accompanying the paper:

"Epistemic State Machine (ESM): MDL-Based Knowledge Discovery and Burn-Backed Citation Attribution with Mechanized Discrete Accounting"

## Repository Structure

1. ESM_verified.lean (1,111 lines, zero external dependencies, Init core only):
   Mechanizes all 53 lemmas and theorems (Tables 8 and 9 of Appendix A) covering discrete natural-number accounting, telescoping escrow superadditivity, the two-stage reservation waterfall, symmetric boundary puncture release, arithmetic supply conservation across 18 ledger transaction schemas, and the algebraic payoff-comparison bounds.
2. esm_exp1_2.py (Python 3 standard library only):
   Reference implementation of Tromp's Binary Lambda Calculus (BLC) parser/encoder, the totalized Krivine Abstract Machine (KAM) with Scott-encoded LSB-first bit-list I/O (MK0, MK1, MKEND), the Counted Merkle Sum Tree (MST) encoder, and the T_max-fuel-bounded coinductive Bohm-tree T6 equivalence verifier (reproducing Table 3 / Section 8.1 Benchmarks 1-4).
3. esm_exp2_sensitivity.py (Python 3 standard library only):
   Exact integer and rational verification suite reproducing all 25 cash-flow trajectory cells of Table 4 (Section 8.2) and all deterrence boundary / sensitivity cells of Table 5 (Section 8.3), including the exhaustive E_tr in [1, 20000] griefing scan.
4. esm_exp3_ablation.py (Python 3 standard library only):
   Subgame-perfect equilibrium (SPE) ablation across mechanisms M1-M4 (Tables 6 and 7 of Section 8.4), three-axis monotone bisection boundary sweeps (--sweeps), and multi-agent no-regret (Hedge) adaptive learning dynamics (--learning).
5. verify_appendix.py (Python 3 standard library only):
   Automated checker verifying that all 53 theorem names, start/end line numbers in Appendix A (Tables 8 and 9), total line count (1,111 lines), and zero-forbidden-token conditions match ESM_verified.lean exactly.

## Quick Reproduction

1. Lean 4 Verification (requires Lean 4.22.0):
   lean ESM_verified.lean

2. Python Benchmarks, Sensitivity, and Ablation Suites (Python 3.8+, stdlib only):
   python3 esm_exp1_2.py
   python3 esm_exp2_sensitivity.py
   python3 esm_exp3_ablation.py
   python3 verify_appendix.py