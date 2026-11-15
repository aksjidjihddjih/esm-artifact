#!/usr/bin/env python3
"""Verify spec/params.toml: derived relations, scale rule, bit-width / overflow bounds.
Exit code 0 = all checks pass.  Python >= 3.11 (tomllib)."""
import sys, tomllib, pathlib

p = tomllib.loads((pathlib.Path(__file__).parent / "params.toml").read_text(encoding="utf-8"))
t, b, pr, ov = p["time"], p["bounds"], p["protocol"], p["overflow_bits"]
fails = []
def check(name, cond):
    print(("PASS " if cond else "FAIL ") + name)
    if not cond: fails.append(name)

# ---- time / batch (C1, C5): 5x scale of the paper's (20, 10, 30) with N_epoch = 166 * N_batch
check("n_batch = n_com + n_delay + n_rev = 300", t["n_batch"] == t["n_com"] + t["n_delay"] + t["n_rev"] == 300)
check("n_epoch = 166 * n_batch = 49800", t["n_epoch"] == t["batches_per_epoch"] * t["n_batch"] == 49800)
check("total batch and lock scaled exactly 5x (60->300, 10000->50000)", (t["n_batch"], t["n_lock"]) == (5 * 60, 5 * 10000))
check("phases (n_com, n_delay, n_rev) = (100, 20, 180) as instructed", (t["n_com"], t["n_delay"], t["n_rev"]) == (100, 20, 180))
check("n_hold = n_batch and n_rev_t6 = n_rev (derived, review)", t["n_hold"] == t["n_batch"] and t["n_rev_t6"] == t["n_rev"])
check("proving window n_rev * 12 s = 36 min", t["n_rev"] * t["l1_block_seconds"] == 36 * 60)
check("randomness delay == time.n_delay", p["randomness"]["n_delay_l1_blocks"] == t["n_delay"])
# t_eff (Lean tEff_bounds is parametric in N_ep > 0): 2N <= t_eff - t_req < 3N for every t_req
N = t["n_epoch"]
ok = True
for t_req in list(range(0, 3 * N + 5, 977)) + [N - 1, N, N + 1, 10**9 + 7]:
    t_eff = N * ((t_req + 3 * N - 1) // N)
    ok &= (2 * N <= t_eff - t_req < 3 * N)
check("tEff bounds 2N <= t_eff - t_req < 3N (sampled)", ok)

# ---- bit widths
mint_cap = int(b["mint_cap"])
check("mint_cap = 2^96 - 1", mint_cap == 2**96 - 1 and b["mint_cap_bits"] == 96)
check("max_n_k = 2^30, max_b_k = 2^10, t_max = 2^20, delta_cap = 2^16",
      (b["max_n_k"], b["max_b_k"], b["t_max"], b["delta_cap_v1"]) == (2**30, 2**10, 2**20, 2**16))
check("max_phi0_bits = max_n_k * max_b_k = 2^40", b["max_phi0_bits"] == b["max_n_k"] * b["max_b_k"] == 2**40)
check("delta_cap_v1 <= t_max", b["delta_cap_v1"] <= b["t_max"])
check("max_prog_bits = 2^16, kam_heap_per_step = 16, |C_i| <= 16, K_rbf <= 10",
      (b["max_prog_bits"], b["kam_heap_per_step"], b["max_cited_axioms"], b["max_rbf_sponsors"]) == (2**16, 16, 16, 10))

check("max_debruijn_index = 255 (legit programs use <= 10)", b["max_debruijn_index"] == 255 and b["max_debruijn_index"] < b["max_prog_bits"])
check("delta_cap_v1 maintained at 2^16 (Step 2 decision)", b["delta_cap_v1"] == 65536)

check("max_tranches = 1024, max_debt_bits = 97 (2.0 x 2^96)", b["max_tranches"] == 1024 and b["max_debt_bits"] == 97 and 2 * (2**96 - 1) < 2**97)

# ---- protocol constants
check("bps constants", (pr["epsilon_bps"], pr["gamma_bps"], pr["beta_d_bps"], pr["kappa_bps"], pr["sigma_col_bps"],
                        pr["sigma_dict_bps"], pr["m_cap_bps"]) == (500, 2000, 1000, 7000, 10000, 10000, 20000))
check("every rate <= 10000 except m_cap_bps (2.0x)", all(pr[k] <= 10000 for k in
      ("epsilon_bps", "gamma_bps", "beta_d_bps", "kappa_bps", "sigma_col_bps", "sigma_dict_bps")) and pr["m_cap_bps"] == 20000)
# griefing constraint (paper Eq. griefing_constraint, Lean game lemma): kappa*sigma*10000 > (10000+Lambda)*gamma*(10000-eps), Lambda_bps in {0, 10000}
for lam in (0, 10000):
    check(f"griefing constraint Lambda_bps={lam}",
          pr["kappa_bps"] * pr["sigma_col_bps"] * 10000 > (10000 + lam) * pr["gamma_bps"] * (10000 - pr["epsilon_bps"]))
check("kappa*sigma/(10000+Lambda): 3500 > 1900 (paper baseline)",
      pr["kappa_bps"] * pr["sigma_col_bps"] // (10000 + 10000) == 3500 and pr["gamma_bps"] * (10000 - pr["epsilon_bps"]) // 10000 == 1900)

# ---- worst-case products fit uint256 and match the documented bit lengths
TOK, BIT, BPS, DEBT = 96, 40, 14, 97
expect = {"escrow_alloc": TOK + BIT, "delta_amort": BPS + TOK + BIT, "stage1_alloc": 2 * BIT, "slot_royalty": BPS + TOK + BIT,
          "paid_s": TOK + DEBT, "div_s": BPS + 2 * TOK, "safe_rem_escrow": TOK + BIT, "hold_absorb": TOK + BIT, "puncture_scale": 2 * BIT}
for k, v in expect.items():
    check(f"overflow_bits.{k} = {v} (< 256)", ov[k] == v and v < 256)
check("Shannon total (N<=2^32, W<2^110) fits 142 bits; ceilDiv form avoids 2^k*w", ov["shannon_total_bits"] == 32 + 110)
# concrete worst-case instances (exact integers)
M, D, G = mint_cap, 2**40 - 1, 10000
for name, val in {"EscrowAlloc B*d": M * D, "slot_royalty gamma*E*x": 20000 * M * D,
                  "paid_s R*D": M * (2 * M), "div_s phi*S*R": 20000 * M * M}.items():
    check(f"{name} < 2^256", val < 2**256)
check("paid_s uses D <= M_cap*b <= 2^97", 2 * M < 2**97)

# ---- policies from the audit
e = p["execution"]
check("single zkVM pipeline, no stylus, no jets, canonical steps", (e["verifier"], e["stylus"], e["jets"], e["canonical_steps"]) == ("zkvm", False, False, True))
check("single ERC-20 accounting asset WETH/18", (p["asset"]["mode"], p["asset"]["symbol"], p["asset"]["decimals"]) == ("single_erc20", "WETH", 18))
check("dataset DA is not blob based", p["da"]["blob_for_dataset"] is False)

print("\nALL PASS" if not fails else f"\n{len(fails)} FAILED: {fails}")
sys.exit(1 if fails else 0)
