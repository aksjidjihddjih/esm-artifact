#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""
ESM Empirical Suite -- Experiment 2: parameter sensitivity & deterrence-boundary verification
(self-contained, stdlib only, exact integer / rational arithmetic; no random numbers)

Boundary 1  Temporary-Reservation-Griefing:  Margin_bps and the integer S_burn^c - R_evade^max
Boundary 2  Pre-Reveal Grinding threshold f_grind and Post-Reveal watchtower rate q_detect^*
Boundary 3  Amortization recovery N_cite and RBF (2.0x debt) repayment N_repay

Modelling conventions (all taken from the paper's definitions):
  * S_tot = ceil(sigma*E_tr/10000);  worst-case (attacker-optimal) creator stake under leverage Lambda:
    S_c = ceil(S_tot*10000/(10000+Lambda_bps))                (S_uw <= Lambda*S_c)
  * slash with r_bps = 10000:  S_slash=S_c, S_hunter=floor((10000-kappa)*S_slash/10000), S_burn=S_slash-S_hunter
  * R_evade^max = floor(gamma * E_net / 10000),  E_net = E_tr - floor(eps*E_tr/10000)   (full-cap royalty, integer)
  * f_grind: smallest integer ppm f with  (1-f)^K * (a+b) <= a,  a=kappa*10000, b=(10000-eps)(10000+Lambda_bps)
    (expected forfeiture (1-p)*phi*S_c >= pass-through reward p*0.95*R_gross, p=(1-f)^K, S_c=R_gross/(1+Lambda);
     the unrevealed-commit forfeiture rate phi is set equal to kappa, as in the paper baseline 70%=70%)
  * q_detect^* = N/(N+L),  N=(1-eps)(1+Lambda),  L=1 (alpha=0) or kappa (alpha->1)
  * Boundary 3 uses the paper's Example (Phi0=1e6, B0=1e4, C_burn=950, L_axiom=1e5, l_E=10, DA fee 10, M_cap=20000)
"""
from fractions import Fraction

EPS, SIGMA = 500, 10000
LAMS = {0: "0", 10000: "1"}                       # Lambda_bps -> label

def cdiv(a: int, b: int) -> int:
    return -(-a // b)

def fr(q: Fraction, d: int = 4) -> str:
    """exact rounding of a Fraction to d decimals (half up), integer arithmetic only."""
    s = 10 ** d
    n = (q.numerator * s * 2 + q.denominator) // (q.denominator * 2)
    sign = "-" if n < 0 else ""
    n = abs(n)
    return f"{sign}{n // s}.{n % s:0{d}d}"

def hdr(title):
    print("\n" + "=" * 100 + f"\n{title}\n" + "=" * 100)

# ------------------------------------------------------------------ Boundary 1
def griefing(kappa, gamma, lam, E=10000, eps=EPS, sigma=SIGMA):
    margin = Fraction(kappa * sigma, 10000 + lam) - Fraction(gamma * (10000 - eps), 10000)
    s_tot = cdiv(sigma * E, 10000)
    s_c = cdiv(s_tot * 10000, 10000 + lam)
    s_hunter = (10000 - kappa) * s_c // 10000
    s_burn = s_c - s_hunter
    e_net = E - eps * E // 10000
    r_ev = gamma * e_net // 10000
    return margin, s_c, s_burn, r_ev

def boundary1(scan_max=20000):
    hdr("BOUNDARY 1: Temporary Reservation Griefing  (eps=500, sigma_col=10000, E_tr=10,000)")
    print("Margin = kappa*sigma/(10000+Lam) - gamma*(10000-eps)/10000   [bps];  deficit = S_burn^c - R_evade^max [tokens]")
    print(f"int-scan = #E_tr in [1,{scan_max}] where the integer inequality S_burn > R_evade FAILS\n")
    print(f"{'kappa':>6}{'gamma':>7}{'Lam':>4}{'Margin_bps':>12}{'S_c':>7}{'S_burn':>8}{'R_evade':>9}{'deficit':>9}  {'theory':<7}{'int-scan':>9}")
    notes = []
    for lam in LAMS:
        for kappa in (3000, 5000, 7000, 9000):
            for gamma in (1000, 2000, 3000, 4000):
                m, s_c, sb, rev = griefing(kappa, gamma, lam)
                fails = [E for E in range(1, scan_max + 1)
                         if not (griefing(kappa, gamma, lam, E)[2] > griefing(kappa, gamma, lam, E)[3])]
                bad = len(fails)
                if m > 0 and fails:
                    notes.append((kappa, gamma, LAMS[lam], int(m), fails[:5]))
                th = "HOLDS" if m > 0 else "BREAKS"
                ms = str(m.numerator) if m.denominator == 1 else fr(m, 1)
                print(f"{kappa:>6}{gamma:>7}{LAMS[lam]:>4}{ms:>12}{s_c:>7}{sb:>8}{rev:>9}{sb - rev:>9}  {th:<7}{bad:>9}")
    if notes:
        print("\nTheory HOLDS but integer rounding FAILS (non-strict tie/loss at tiny E_tr, thin margin only):")
        for k, g, l, mm, f in notes:
            print(f"  kappa={k} gamma={g} Lam={l} margin={mm} bps -> failing E_tr (first): {f}")
            E = f[0]; _, _, sb, rev = griefing(k, g, int(l) * 10000, E)
            print(f"     e.g. E_tr={E}: S_burn={sb}, R_evade={rev} (floor(eps*E/10000)={EPS*E//10000}, so E_net={E - EPS*E//10000})")
    else:
        print("\nNo integer-rounding failures in any theory-HOLDS cell.")
    print("\nCritical values (strict inequality kappa*sigma*10000 > (10000+Lam)*gamma*(10000-eps)):")
    print(f"{'kappa':>6} | {'gamma_max (Lam=0)':>18}{'gamma_max (Lam=1)':>19}")
    for kappa in (3000, 5000, 7000, 9000):
        g = [(kappa * SIGMA * 10000 - 1) // ((10000 + lam) * (10000 - EPS)) for lam in LAMS]
        print(f"{kappa:>6} | {g[0]:>18}{g[1]:>19}")
    print(f"\n{'gamma':>6} | {'kappa_min (Lam=0)':>18}{'kappa_min (Lam=1)':>19}")
    for gamma in (1000, 2000, 3000, 4000):
        k = [((10000 + lam) * gamma * (10000 - EPS)) // (SIGMA * 10000) + 1 for lam in LAMS]
        print(f"{gamma:>6} | {k[0]:>18}{k[1]:>19}")

# ------------------------------------------------------------------ Boundary 2
def f_grind_ppm(K, kappa, lam, eps=EPS):
    a, b = kappa * 10000, (10000 - eps) * (10000 + lam)
    lo, hi = 0, 10 ** 6
    while lo < hi:
        mid = (lo + hi) // 2
        if (10 ** 6 - mid) ** K * (a + b) <= 10 ** (6 * K) * a:
            hi = mid
        else:
            lo = mid + 1
    return lo

def q_star(kappa, lam, alpha_one, eps=EPS):
    N = Fraction((10000 - eps) * (10000 + lam), 10 ** 8)
    L = Fraction(kappa, 10000) if alpha_one else Fraction(1)
    return N / (N + L)

def boundary2():
    hdr("BOUNDARY 2: Grinding threshold f_grind and watchtower minimum inspection rate q_detect^*  (eps=500)")
    print("f_grind: smallest integer-ppm corruption fraction f at which spot-check forfeiture outweighs the pass-through reward")
    print("q^*(alpha=0): L_slash=1.00*S_c ;  q^*(alpha->1): L_slash=kappa*S_c  (worst case, conservative)\n")
    print(f"{'K_spot':>7}{'kappa':>7}{'Lam':>4}{'f_grind %':>12}{'f_grind ppm':>13}{'q*(a=0)':>10}{'q*(a->1)':>10}")
    for K in (16, 32, 64):
        for kappa in (5000, 7000, 9000):
            for lam in LAMS:
                ppm = f_grind_ppm(K, kappa, lam)
                print(f"{K:>7}{kappa:>7}{LAMS[lam]:>4}{ppm / 10 ** 4:>12.4f}{ppm:>13}"
                      f"{fr(q_star(kappa, lam, False)):>10}{fr(q_star(kappa, lam, True)):>10}")

# ------------------------------------------------------------------ Boundary 3
def royalty_stack(gamma, beta, eps=EPS, Phi0=10 ** 6, B0=10 ** 4, C=950, L_ax=10 ** 5, lE=10, Mcap=20000):
    d_amort = min(L_ax, 10000 * C * Phi0 // ((10000 - eps) * B0))
    saved = d_amort - lE
    E_tr = B0 * saved // Phi0
    E_net = E_tr - eps * E_tr // 10000
    R = gamma * E_net * saved // (10000 * saved)         # full-cap slot x = Delta_tr = saved
    R_anchor = beta * R // 10000
    return dict(E_tr=E_tr, E_net=E_net, R=R, R_net=R - R_anchor, D0=Mcap * C // 10000, C=C)

def boundary3():
    hdr("BOUNDARY 3: Amortization recovery N_cite and RBF 2.0x repayment N_repay")
    print("Paper example: Phi0=1e6, B0=1e4, eps=500, C_burn=950 (E_tr=999, E_net=950), l_E=10, DA fee 10, D0=2.0x950=1900")
    print("N_cite(formula)=ceil(1e8/(gamma*(10000-beta_D)));  integer: smallest N with N*R_net >= C (and >= C+10 with DA fee)")
    print("N_repay = smallest N with N*R_net >= D0.  Sponsor break-even N equals N_cite(int) (principal 950 recovered)\n")
    print(f"{'gamma':>6}{'beta_D':>8}{'R':>6}{'R_net':>7}{'N_cite(f)':>11}{'N_cite(int)':>12}{'N_cite(+DA)':>12}{'N_repay':>9}")
    for gamma in (1000, 1500, 2000, 2500, 3000):
        for beta in (500, 1000, 2000):
            s = royalty_stack(gamma, beta)
            nf = cdiv(10 ** 8, gamma * (10000 - beta))
            ni = cdiv(s["C"], s["R_net"]); nd = cdiv(s["C"] + 10, s["R_net"]); nr = cdiv(s["D0"], s["R_net"])
            print(f"{gamma:>6}{beta:>8}{s['R']:>6}{s['R_net']:>7}{nf:>11}{ni:>12}{nd:>12}{nr:>9}")

# ------------------------------------------------------------------ baseline reproduction checks
def baseline_checks():
    m, s_c, sb, rev = griefing(7000, 2000, 10000)
    assert m == 1600 and (s_c, sb, rev) == (5000, 3500, 1900)                 # 3500 bps > 1900 bps
    assert round(f_grind_ppm(32, 7000, 0) / 1e4, 3) == 2.644                 # paper: 2.644 %
    assert round(f_grind_ppm(32, 7000, 10000) / 1e4, 3) == 4.018             # paper: 4.018 %
    assert fr(q_star(7000, 0, True), 3) == "0.576" and fr(q_star(7000, 10000, True), 3) == "0.731"
    assert fr(q_star(7000, 0, False), 3) == "0.487" and fr(q_star(7000, 10000, False), 3) == "0.655"
    s = royalty_stack(2000, 1000)
    assert (s["E_tr"], s["E_net"], s["R"], s["R_net"], s["D0"]) == (999, 950, 190, 171, 1900)
    assert cdiv(10 ** 8, 2000 * 9000) == 6 and cdiv(1900, 171) == 12
    print("baseline reproduction checks (paper values): PASS")


# ------------------------------------------------------------------ TABLE 4 (Section 8.2): cash-flow trajectories, exact simulation
def table4():
    hdr("TABLE 4 (Section 8.2): multi-dataset cash-flow trajectories -- exact integer waterfall simulation (cumulative net profit, tokens)")
    Phi0, B0, gamma, beta_d, Mcap = 10 ** 6, 10 ** 4, 2000, 1000, 20000
    C, L_ax, lE, DAf = 950, 10 ** 5, 10, 10                      # amortization burn, axiom length, pointer bits, DA registration burn
    d_amort = min(L_ax, 10000 * C * Phi0 // ((10000 - EPS) * B0)); saved = d_amort - lE            # 100000 ; 99990
    E_tr = B0 * saved // Phi0; E_net = E_tr - EPS * E_tr // 10000                                  # 999 ; 950
    R = lambda x: gamma * E_net * x // (10000 * saved)           # royalty of a slot of x bits (Delta_tr = saved)
    anc = lambda r: beta_d * r // 10000                          # anchor rebate
    rnet = R(saved) - anc(R(saved)); D0 = Mcap * C // 10000      # 171 ; 1900
    assert (d_amort, saved, E_tr, E_net, R(saved), anc(R(saved)), rnet, D0) == (100000, 99990, 999, 950, 190, 19, 171, 1900)
    Ns = (1, 5, 6, 10, 15)
    # Strategy 1: one-shot lookup table on D_1 only (floor settlement), flat for every N
    s1 = [(10000 - EPS) * E_tr // 10000 - C - DAf for _ in Ns]
    # Strategy 2: self-funded author, general axiom cited at capacity in every dataset
    s2 = [-(C + DAf) + rnet * N for N in Ns]
    # Strategies 3 and 4: RBF sponsor repaid first (2.0x debt), then the author; DA fee of Alice covered by a grant
    debt, alice, spons, c3, c4 = D0, 0, 0, {}, {}
    for k in range(1, 16):
        pay = min(rnet, debt); debt -= pay; spons += pay; alice += rnet - pay
        c3[k], c4[k] = alice, spons - C
    s3, s4 = [c3[N] for N in Ns], [c4[N] for N in Ns]
    s4_da = [c4[N] - DAf for N in Ns]
    # Strategy 5: v_s backed by 855 burn + 10 DA; v_u RBF-financed; T6 reduction v_u -> v_s; Stage-2 slots with debt-following waterfall
    burn_s = 855
    d_s = min(L_ax, 10000 * burn_s * Phi0 // ((10000 - EPS) * B0)); L_red = L_ax - 10000          # 90000 ; 90000
    saved_s = d_s - lE                                                                              # 89990
    a = min(saved, saved)                                                                           # Saved(v_u) = Delta_tr = 99990
    x_us = min(a, min(L_red, saved_s)); x_uu = a - x_us                                             # 89990 ; 10000
    r1, r2 = R(x_us), R(x_uu); n1, n2 = r1 - anc(r1), r2 - anc(r2)                                  # 170,19 -> 153,18
    assert (d_s, saved_s, x_us, x_uu, r1, r2, n1, n2) == (90000, 89990, 89990, 10000, 170, 19, 153, 18)
    debt, att, c5 = D0, -(burn_s + DAf), {}
    for k in range(1, 16):
        p1 = min(n1, debt); debt -= p1; att += n1 - p1                 # redirected slot: royalty -> owner(v_s) after sponsor repayment
        p2 = min(n2, debt); debt -= p2; att += n2 - p2                 # retained slot  -> owner(v_u) after sponsor repayment
        c5[k] = att
    s5 = [c5[N] for N in Ns]
    paper = {1: [-11] * 5, 2: [-789, -105, 66, 750, 1605], 3: [0, 0, 0, 0, 665], 4: [-779, -95, 76, 760, 950], 5: [-865] * 4 + [-200]}
    got = {1: s1, 2: s2, 3: s3, 4: s4, 5: s5}
    names = {1: "1. Pre-Embedding Attacker (single-dataset lookup)", 2: "2. Self-Funded Honest Axiom Author",
             3: "3. Capital-Constrained Author Alice (RBF-financed)", 4: "4. RBF Burn Sponsor (950 burn, 2.0x cap = 1900)",
             5: "5. Single/Sybil T6 Attacker (RBF evasion)"}
    print(f"  per-dataset: E_tr = {E_tr}, E_net = {E_net}, R(full cap) = {R(saved)}, anchor = {anc(R(saved))}, R_net = {rnet}, D_0 = {D0};"
          f"  Strategy 5 slots: x_us = {x_us} (R {r1} -> {n1}), x_uu = {x_uu} (R {r2} -> {n2})")
    print(f"  {'Agent strategy':<52}" + "".join(f"{'N=' + str(n):>9}" for n in Ns))
    for k in (1, 2, 3, 4, 5):
        print(f"  {names[k]:<52}" + "".join(f"{x:>+9d}" if x else f"{0:>9d}" for x in got[k]))
        assert got[k] == paper[k], (k, got[k], paper[k])
    print(f"  {'   (4, if the sponsor also pays the 10-token DA fee)':<52}" + "".join(f"{x:>+9d}" for x in s4_da))
    assert s4_da == [-789, -105, 66, 750, 940]
    assert c3[12] - c3[11] == 152 and c3[11] == 0 and cdiv(D0, rnet) == 12                          # Alice retains 152 on dataset 12
    assert cdiv(10 ** 8, 2000 * 9000) == 6 and s2[1] < 0 < s2[2]                                  # N_cite = 6: N=5 negative, N=6 positive
    print("  Table 4: all 25 cells reproduced from the integer pipeline and equal to the manuscript: PASS")

# ------------------------------------------------------------------ TABLE 5 (Section 8.3): exact cells asserted against the manuscript
def table5_check():
    hdr("TABLE 5 (Section 8.3): every printed cell recomputed and asserted against the manuscript")
    gmax = lambda k, lam: (k * SIGMA * 10000 - 1) // ((10000 + lam) * (10000 - EPS))
    kmin = lambda g, lam: ((10000 + lam) * g * (10000 - EPS)) // (SIGMA * 10000) + 1
    assert [gmax(k, 0) for k in (3000, 5000, 7000, 9000)] == [3157, 5263, 7368, 9473]
    assert [gmax(k, 10000) for k in (3000, 5000, 7000, 9000)] == [1578, 2631, 3684, 4736]
    assert [kmin(g, 0) for g in (1000, 2000, 3000, 4000)] == [951, 1901, 2851, 3801]
    assert [kmin(g, 10000) for g in (1000, 2000, 3000, 4000)] == [1901, 3801, 5701, 7601]
    m, s_c, sb, rev = griefing(7000, 2000, 10000); assert m == 1600 and (sb, rev) == (3500, 1900)
    bad = sum(1 for E in range(1, 20001) if not griefing(7000, 2000, 10000, E)[2] > griefing(7000, 2000, 10000, E)[3])
    assert bad == 0                                                                                  # "0 / 20k" at the baseline
    pct = lambda ppm: f"{(ppm + 5) // 10 / 1000:.3f}"
    assert [pct(f_grind_ppm(K, 7000, 0)) for K in (16, 32, 64)] == ["5.218", "2.644", "1.331"]
    assert [pct(f_grind_ppm(K, 7000, 10000)) for K in (16, 32, 64)] == ["7.874", "4.018", "2.030"]
    assert [fr(q_star(k, 0, True)) for k in (5000, 7000, 9000)] == ["0.6552", "0.5758", "0.5135"]
    assert [fr(q_star(k, 10000, True)) for k in (5000, 7000, 9000)] == ["0.7917", "0.7308", "0.6786"]
    assert (fr(q_star(7000, 0, False)), fr(q_star(7000, 10000, False))) == ("0.4872", "0.6552")
    rn = [royalty_stack(g, 1000)["R_net"] for g in (1000, 1500, 2000, 2500, 3000)]
    nc = [cdiv(10 ** 8, g * 9000) for g in (1000, 1500, 2000, 2500, 3000)]
    nr = [cdiv(1900, x) for x in rn]
    assert rn == [86, 128, 171, 214, 257] and nc == [12, 8, 6, 5, 4] and nr == [23, 15, 12, 9, 8]
    s_ = royalty_stack(2500, 2000); assert cdiv(950, s_["R_net"]) == 5 and cdiv(960, s_["R_net"]) == 6   # the single (+DA) shift
    print("  1a gamma_max, 1b kappa_min, 2a f_grind, 2b q_detect*, 3 R_net / N_cite / N_repay and the 0/20k scan: all cells equal the manuscript: PASS")
    print("  tables verified automatically by this script: Table 4 (Section 8.2), Table 5 (Section 8.3)")

if __name__ == "__main__":
    baseline_checks()
    boundary1(); boundary2(); boundary3()
    table4(); table5_check()
