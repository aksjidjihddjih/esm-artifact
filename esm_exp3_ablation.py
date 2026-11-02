#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""
ESM Empirical Suite -- Experiment 4: mechanism ablation with rational agents
(self-contained, stdlib only, exact integer / Fraction arithmetic, deterministic)

Mechanisms compared on the SAME stream of N identical datasets (Benchmark-3 type: Phi0=16384, B=10000, L_res=750):
  M1   Hutter-style single-shot prize : winner-takes-prize; NO axiom registry, amortization, royalties or protocol burn
  M2   naive citation market          : citation + royalties, exemption is FREE (no pre-burn)            -> pre-embedding vulnerable
  M3   burn-backed amortization       : exemption bought by burn (Eq. delta_amort), NO T6                 -> clone theft of low-burn roots
  M4-  ESM core                       : burn-backed amortization + T6 reduction & Stage-2 redirect (no RBF financing)
  M4   ESM full                       : M4- + RBF sponsor financing with the Universal 2.0x debt-following waterfall

Agents (integer-token payoffs; best responses by exhaustive enumeration over finite action sets):
  H  honest root-axiom author (publishes v_s, |p_s|=85 bits, development cost 20, own burn <= budget)   [Stackelberg leader]
  Q  clone plagiarist (copies v_s: exact copy 85 bits or padded 103 bits; chooses its own burn)
  P  pre-embedding attacker (knows dataset D_1 in advance; registers a 16,400-bit lookup axiom; chooses its burn)
  R  recipe proposers (per dataset: cite a registered axiom or inline; maximize E_net - royalties; lowest Phi wins the prize)
  W  watchtower (submits T6 against a clone iff B_finder - g_T6 - c_search > 0)
  S  RBF sponsor (funds part of the root's burn iff its 2.0x debt claim repays at least the principal)
Solution concept: subgame-perfect. H moves first; (Q,P) play a simultaneous Nash subgame (ties broken in the attackers' favour);
R, W, S respond optimally. Parameters are the paper's baseline (eps=500, gamma=2000, beta_D=1000, kappa=7000, B_finder=6, S_audit=20)
or ASSUMPTIONS of this stylized model (gas 1 token/tx, axiom development cost 20, DA fee ceil(1e-4*bits), g_T6=3, c_search=1).

Welfare W = V * S_true - real_costs with V = B/Phi0 tokens per bit. S_true = true corpus-level saving in bits (each distinct axiom
CONTENT counted once, lookup tables in full). Burns, escrow, royalties are TRANSFERS; real costs = development, gas, DA, watchtower work.
"""
from fractions import Fraction

PHI0, B = 16384, 10000
V = Fraction(B, PHI0)
EPS, GAMMA, BETA_D = 500, 2000, 1000
ELL_E, L_RES = 4, 750
WRAP, INLINE = 68, 145                       # w3 recipe code (48+3+17);  standalone recipe with p_s inlined (126+2+17)
ROOT = 85                                    # |p_s|
LOOK_SIZE, LOOK_CODE, LOOK_RES = 16400, 24, 34
DA = lambda bits: -(-bits // 10000)

# Tunable assumptions (the sweeps of Experiment 4b move these).  Baseline = the values used throughout Section 8.4.
BASE = dict(c_dev=20, g_tx=1, know=PHI0, s_audit=20, c_search=1, c_step_fuel=1)
def make_pr(**kw):
    """know = number of D_1 bits known to the pre-embedding attacker P in advance (p_know = know / Phi0);
    g_T6 = 2*g_tx + c_step*fuel_max  with  c_step*fuel_max = c_step_fuel tokens (baseline 1 => g_T6 = 3 at g_tx = 1);
    B_finder = floor(0.30 * S_audit); the clone owner loses S_audit - B_finder when reduced."""
    d = dict(BASE); d.update(kw)
    d["g_t6"] = 2 * d["g_tx"] + d["c_step_fuel"]
    d["b_finder"] = 3000 * d["s_audit"] // 10000
    d["audit_burn"] = d["s_audit"] - d["b_finder"]
    d["look_size"] = d["know"] + 16                       # lookup table of the known bits + 16-bit loader
    d["look_res"] = 34 + (PHI0 - d["know"])               # recipe residual: 34-bit header + the unknown bits at 1 bit/bit
    return d
PR0 = make_pr()
def pr_key(pr): return tuple(sorted(pr.items()))

MECH = {
    "M1  Hutter single-shot":       dict(eps=0,   gamma=0,     amort="none", t6=False, rbf=False),
    "M2  naive citation (free)":    dict(eps=EPS, gamma=GAMMA, amort="free", t6=False, rbf=False),
    "M3  burn amortization, no T6": dict(eps=EPS, gamma=GAMMA, amort="burn", t6=False, rbf=False),
    "M4- ESM core (burn + T6)":     dict(eps=EPS, gamma=GAMMA, amort="burn", t6=True,  rbf=False),
    "M4  ESM full (+RBF)":          dict(eps=EPS, gamma=GAMMA, amort="burn", t6=True,  rbf=True),
}

def escrow(phi):   d = PHI0 - phi; return B * d // PHI0 if d > 0 else 0
def e_net(E, eps): return E - eps * E // 10000
def roy(En, x, dtr): return GAMMA * En * x // (10000 * dtr) if dtr > 0 else 0
def dam(m, size, burn):
    if m["amort"] == "none": return 0
    if m["amort"] == "free": return size
    return min(size, 10000 * burn * PHI0 // ((10000 - EPS) * B))

def play(m, N, H=None, Q=None, P=None, rbf=0, tie="root", pr=PR0):
    """H: None | own burn; Q: None | (size, burn); P: None | burn; rbf: sponsor burn on the root (only if m['rbf']).
    tie: how recipe proposers break EXACT payoff ties between the root and a clone ('root' = earlier registration, 'clone' = adversarial)."""
    rbf = rbf if (m["rbf"] and H is not None) else 0
    ax, t6_done, p_won = {}, False, False
    if H is not None:
        b = H + rbf; ax["s"] = dict(owner="H", size=ROOT, burn=b, delta=dam(m, ROOT, b), origin="s", Lred=0)
    if Q is not None and "s" in ax:
        sz, bn = Q; ax["q"] = dict(owner="Q", size=sz, burn=bn, delta=dam(m, sz, bn), origin="q", Lred=0)
        if m["t6"] and pr["b_finder"] - pr["g_t6"] - pr["c_search"] > 0:   # W submits T6 with the identity adapter (|q| + l_w(idx) = 5 bits)
            ax["q"].update(origin="s", Lred=max(sz - 5, 0)); t6_done = True
    if P is not None:
        ax["p"] = dict(owner="P", size=pr["look_size"], burn=P, delta=dam(m, pr["look_size"], P), origin="p", Lred=0)
    gross = dict(H=0, Q=0, P=0); debt = 2 * rbf; repaid = 0; pP = 0
    A = dict(E=0, En=0, R=0, reb=0, prop=0, save=0, dev=0, gas=0, eburn=0, recv=0)
    used = {}
    for k in range(1, N + 1):
        notax = [a for a in (("q", "s") if tie == "clone" else ("s", "q")) if a in ax]; opts = []
        if m["amort"] != "none":
            for aid in notax:
                v = ax[aid]; phi = WRAP + (v["size"] - v["delta"]) + ELL_E + L_RES
                E = escrow(phi); En = e_net(E, m["eps"]); dtr = PHI0 - phi
                a = min(max(v["delta"] - ELL_E, 0), dtr)
                if m["t6"] and v["origin"] != aid:
                    r = ax[v["origin"]]; cap = max(r["delta"] - ELL_E, 0); x1 = min(a, v["Lred"], cap)
                    slots = [(r["owner"], x1), (v["owner"], a - x1)]
                else: slots = [(v["owner"], a)]
                rs = [(o, roy(En, x, dtr) if m["gamma"] else 0) for o, x in slots]
                opts.append(dict(kind=aid, phi=phi, E=E, En=En, rs=rs, dev=0, own=WRAP + ELL_E + L_RES,
                                 pay=En - sum(r for _, r in rs) - pr["g_tx"]))
        phi = INLINE + L_RES; E = escrow(phi); En = e_net(E, m["eps"]); dev = 0 if notax else pr["c_dev"]
        opts.append(dict(kind="inline", phi=phi, E=E, En=En, rs=[], dev=dev, own=INLINE + L_RES, pay=En - pr["g_tx"] - dev))
        win = max(opts, key=lambda o: o["pay"])                # ties: earlier option (root, clone, inline)
        if k == 1 and "p" in ax:
            v = ax["p"]; phiP = LOOK_CODE + (v["size"] - v["delta"]) + (ELL_E if m["amort"] != "none" else 0) + pr["look_res"]
            if phiP < win["phi"]:
                E = escrow(phiP); En = e_net(E, m["eps"]); dtr = PHI0 - phiP
                a = min(max(v["delta"] - ELL_E, 0), dtr) if m["amort"] != "none" else 0
                R = roy(En, a, dtr) if m["gamma"] else 0
                win = dict(kind="p", phi=phiP, E=E, En=En, rs=[("P", R)], dev=0, own=LOOK_CODE + ELL_E + pr["look_res"], pay=En - R - pr["g_tx"])
                p_won = True; pP = En - R - pr["g_tx"]
        A["E"] += win["E"]; A["En"] += win["En"]; A["eburn"] += win["E"] - win["En"]; A["gas"] += pr["g_tx"]; A["dev"] += win["dev"]
        A["save"] += PHI0 - win["own"]; A["recv"] += win["En"] - sum(r for _, r in win["rs"])
        if win["kind"] != "p": A["prop"] += win["pay"]
        for o, R in win["rs"]:
            reb = BETA_D * R // 10000; net = R - reb; A["R"] += R; A["reb"] += reb
            if o == "H" and debt > 0:                           # Universal debt-following: root-bound royalties repay the sponsor first
                pay = min(net, debt); debt -= pay; repaid += pay; net -= pay
            gross[o] += net
        if win["kind"] in ("s", "q"): used.setdefault("NOT", set()).add(win["kind"])
        if win["kind"] == "p": used.setdefault("LOOK", set()).add("p")
    axbits = (min(ax[a]["size"] for a in used["NOT"]) if "NOT" in used else 0) + (pr["look_size"] if "LOOK" in used else 0)
    S_true = A["save"] - axbits
    ob = dict(H=H or 0, Q=(Q[1] if "q" in ax else 0), P=(P or 0))
    pay = dict(H=0, Q=0, P=0)
    if H is not None: pay["H"] = gross["H"] - ob["H"] - DA(ROOT) - pr["g_tx"] - pr["c_dev"]
    if "q" in ax:     pay["Q"] = gross["Q"] - ob["Q"] - DA(ax["q"]["size"]) - pr["g_tx"] - (pr["audit_burn"] if t6_done else 0)
    if "p" in ax:     pay["P"] = gross["P"] + pP - ob["P"] - DA(pr["look_size"]) - pr["g_tx"]
    # conservation checks
    assert A["E"] == A["En"] + A["eburn"]
    assert A["En"] == A["recv"] + A["R"]
    assert A["R"] == A["reb"] + sum(gross.values()) + repaid
    nreg = len(ax); dev_paid = A["dev"] + (pr["c_dev"] if H is not None else 0)
    gas = A["gas"] + pr["g_tx"] * nreg + (pr["g_t6"] if t6_done else 0)
    da = sum(DA(v["size"]) for v in ax.values()); search = pr["c_search"] if t6_done else 0
    real = dev_paid + gas + da + search
    Wf = V * S_true - real
    burned = A["eburn"] + sum(ob.values()) + rbf + (pr["audit_burn"] if t6_done else 0)
    return dict(pay=pay, S_true=S_true, W=Wf, E=A["E"], sponsor=(repaid - rbf) if rbf else 0, rbf=rbf, t6=t6_done, p_won=p_won,
                H_gross=gross["H"] + repaid, H_roy=gross["H"], Q_roy=gross["Q"], prop=A["prop"] + pP, burned=burned, ax=ax,
                wt=(pr["b_finder"] - pr["g_t6"] - pr["c_search"]) if t6_done else 0)

# ------------------------------------------------------------------ equilibrium
Q_SIZES = (85, 103)
def grids(m, pr=PR0):
    qb = (0, 12, 25, 50, 60, 100) if m["amort"] == "burn" else (0,)
    pb = tuple(sorted({0} | {x * pr["know"] // PHI0 for x in (1000, 5000, 9500)})) if m["amort"] == "burn" else (0,)
    return [None] + [(s, b) for s in Q_SIZES for b in qb], [None] + list(pb)

def attackers(m, N, h, r, tie="root", pr=PR0):
    Qs, Ps = grids(m, pr)
    if h is None: Qs = [None]
    R = {(q, p): play(m, N, h, q, p, r, tie, pr) for q in Qs for p in Ps}
    ne = [(q, p) for q in Qs for p in Ps
          if R[q, p]["pay"]["Q"] >= max(R[q2, p]["pay"]["Q"] for q2 in Qs)
          and R[q, p]["pay"]["P"] >= max(R[q, p2]["pay"]["P"] for p2 in Ps)]
    q, p = max(ne, key=lambda k: R[k]["pay"]["Q"] + R[k]["pay"]["P"])      # attackers' favourite NE (ties: first listed)
    return q, p, R

def margins(m, N, h, r, tie, pr=PR0):
    """Best payoff of a SUCCESSFUL attack at (h, r): Q captures royalty (>0) / P wins D_1; None if no such attack exists."""
    Qs, Ps = grids(m, pr)
    qs = [play(m, N, h, q, None, r, tie, pr) for q in Qs[1:]] if h is not None else []
    ps = [play(m, N, h, None, p, r, tie, pr) for p in Ps[1:]]
    bq = [x["pay"]["Q"] for x in qs if x["Q_roy"] > 0]; bp = [x["pay"]["P"] for x in ps if x["p_won"]]
    return (max(bq) if bq else None), (max(bp) if bp else None)

def spe(m, N, budget, tie="root", pr=PR0):
    Hs = [None] + [b for b in ((0,) if m["amort"] != "burn" else (0, 6, 12, 25, 50, 60)) if b <= budget]
    cands = []
    for h in Hs:
        for r in ((0, 20, 38, 50) if (m["rbf"] and h is not None) else (0,)):
            q, p, R = attackers(m, N, h, r, tie, pr)
            res = R[q, p]
            if r and res["sponsor"] < 0: continue                              # sponsor would not fund
            cands.append((res["pay"]["H"], res["W"], -len(cands), h, r, q, p, R))
    best = max(cands, key=lambda c: (c[0], c[1], c[2]))
    _, _, _, h, r, q, p, R = best
    res = R[q, p]
    bq, bp = margins(m, N, h, r, tie, pr)
    return dict(h=h, r=r, q=q, p=p, res=res, best_Q=bq, best_P=bp)

def fa(x): return "none" if x is None else str(x)
def fm(x, w): return "no attack" if x is None else str(x)

def report(budget, label, N, tie="root"):
    print("\n" + "=" * 118)
    print(f"SCENARIO {label}:  N = {N} datasets, honest author's capital budget = {budget} tokens")
    print("=" * 118)
    rows = []
    for name, m in MECH.items():
        s = spe(m, N, budget, tie); r = s["res"]
        rows.append((name, s))
        print(f"\n{name}")
        print(f"  equilibrium: H publishes with own burn = {fa(s['h'])}" + (f" + sponsor burn {s['r']}" if s["r"] else "")
              + f" | Q clone = {fa(s['q'])} | P lookup burn = {fa(s['p'])}" + (" (P wins D_1)" if r["p_won"] else "")
              + (" | W submits T6" if r["t6"] else ""))
        print(f"  welfare W = {int(round(r['W']))} tokens  (S_true = {r['S_true']} bits, V*S_true = {int(round(V * r['S_true']))}, "
              f"real costs = {int(round(V * r['S_true'] - r['W']))});   funders pay sum E_tr = {r['E']};   tokens burned = {r['burned']}")
        print(f"  original author: royalties received = {r['H_gross']} (after sponsor repayment {r['H_roy']}),  NET = {r['pay']['H']}"
              + (f";   sponsor net = {r['sponsor']}" if s['r'] else ""))
        print(f"  attackers: Q net = {r['pay']['Q']},  P net = {r['pay']['P']}   (extraction = {max(r['pay']['Q'],0) + max(r['pay']['P'],0)});"
              f"   watchtower net = {r['wt']}")
        print(f"  best SUCCESSFUL attack vs this equilibrium (deterrence margin): clone captures royalty -> Q net {fm(s['best_Q'], 0)};  "
              f"lookup wins D_1 -> P net {fm(s['best_P'], 0)}")
    print("\n  " + "-" * 114)
    print(f"  {'mechanism':<30}{'W (tokens)':>12}{'S_true':>9}{'author NET':>12}{'author roy.':>12}{'Q net':>8}{'P net':>8}{'bestQ win':>10}{'bestP win':>10}")
    for name, s in rows:
        r = s["res"]
        print(f"  {name:<30}{int(round(r['W'])):>12}{r['S_true']:>9}{r['pay']['H']:>12}{r['H_gross']:>12}{r['pay']['Q']:>8}{r['pay']['P']:>8}"
              f"{fm(s['best_Q'], 0):>10}{fm(s['best_P'], 0):>10}")
    return rows

def committed(h, N=12, tie="root"):
    print("\n" + "=" * 118)
    print(f"COUNTERFACTUAL: the capital-constrained author publishes anyway (own burn {h}); attackers best-respond   [N = {N}, tie-break: {tie}]")
    print("=" * 118)
    print(f"  {'mechanism':<30}{'Q action':>16}{'Q net':>8}{'P net':>8}{'author roy.':>12}{'author NET':>11}{'sponsor':>9}{'W':>9}")
    for name, m in MECH.items():
        r_opts = (0, 38) if m["rbf"] else (0,)
        hh = h if m["amort"] == "burn" else 0                       # burning is pointless without burn-backed amortization
        for rr in r_opts:
            q, p, R = attackers(m, N, hh, rr, tie); x = R[q, p]
            tag = name + (f" [sponsor 38]" if rr else "")
            print(f"  {tag:<30}{fa(q):>16}{x['pay']['Q']:>8}{x['pay']['P']:>8}{x['H_gross']:>12}{x['pay']['H']:>11}{(x['sponsor'] if rr else 0):>9}{int(round(x['W'])):>9}")

def sensitivity():
    print("\n" + "=" * 118)
    print("SENSITIVITY TO THE NUMBER OF DATASETS N   (author NET / total attacker extraction / welfare W)")
    print("=" * 118)
    for budget, label in ((100, "S1 well-funded author"), (12, "S2 capital-constrained author")):
        print(f"\n  {label} (budget {budget})")
        print(f"  {'mechanism':<30}" + "".join(f"{'N=' + str(n):>26}" for n in (6, 12, 24)))
        for name, m in MECH.items():
            cells = []
            for n in (6, 12, 24):
                r = spe(m, n, budget)["res"]
                cells.append(f"{r['pay']['H']:>6} /{max(r['pay']['Q'],0)+max(r['pay']['P'],0):>5} /{int(round(r['W'])):>8}")
            print(f"  {name:<30}" + "".join(f"{c:>26}" for c in cells))

def checks():
    m3 = MECH["M3  burn amortization, no T6"]
    assert dam(m3, 85, 50) == 85 and dam(m3, 85, 12) == 20 and dam(m3, LOOK_SIZE, 9500) == 16384
    r = play(m3, 12, 50)                                  # honest baseline == Benchmark 3: E_tr = 9498 per dataset, R(81) = 9
    assert r["E"] == 12 * 9498 and r["H_gross"] == 12 * 9 and r["S_true"] == 12 * (PHI0 - 72 - L_RES) - ROOT
    assert play(MECH["M1  Hutter single-shot"], 12)["S_true"] == 12 * (PHI0 - INLINE - L_RES)
    # regression checks of the headline results (N = 12)
    m2, m4m, m4 = MECH["M2  naive citation (free)"], MECH["M4- ESM core (burn + T6)"], MECH["M4  ESM full (+RBF)"]
    assert play(m2, 12, 0, None, 0)["pay"]["P"] == 9271                                    # free pre-embedding extraction
    assert play(m3, 12, 12, None, 9500)["p_won"] and play(m3, 12, 12, None, 9500)["pay"]["P"] == -238   # burn-backed: Lemma 4.1
    q, p, R = attackers(m3, 12, 12, 0); assert (q, R[q, p]["pay"]["Q"], R[q, p]["H_gross"]) == ((103, 60), 58, 0)       # clone theft
    q, p, R = attackers(m4m, 12, 12, 0); assert (q, R[q, p]["pay"]["Q"], R[q, p]["H_gross"]) == ((103, 60), 32, 12)     # T6 partial
    q, p, R = attackers(m4, 12, 12, 38); assert q is None and R[q, p]["sponsor"] == 38 and R[q, p]["pay"]["H"] == -2    # + RBF
    assert spe(m3, 12, 100, "clone")["h"] is None and spe(m4m, 12, 100, "clone")["h"] == 50   # T6 removes tie-break dependence
    print("model sanity checks: PASS")


# ====================================================================================== robustness sweeps (Experiment 4b)
N1, N2, N3, N4m, N4 = list(MECH)
_SPE = {}
def spe_c(name, N, budget, tie, pr):
    key = (name, N, budget, tie, pr_key(pr))
    if key not in _SPE: _SPE[key] = spe(MECH[name], N, budget, tie, pr)
    return _SPE[key]

def last_true(f, lo, hi):
    """Largest x in [lo, hi] with f(x) true, f monotone (true...true false...false); None if f(lo) is false."""
    if not f(lo): return None
    if f(hi): return hi
    while hi - lo > 1:
        mid = (lo + hi) // 2
        lo, hi = (mid, hi) if f(mid) else (lo, mid)
    return lo

def first_true(f, lo, hi):
    """Smallest x in [lo, hi] with f(x) true, f monotone (false...false true...true); None if f(hi) is false."""
    if not f(hi): return None
    if f(lo): return lo
    while hi - lo > 1:
        mid = (lo + hi) // 2
        lo, hi = (lo, mid) if f(mid) else (mid, hi)
    return hi

def verdicts(pr, N=12):
    """The four claims of Section 8.4 evaluated at the parameter point `pr`."""
    v = {}
    s = spe_c(N2, N, 100, "root", pr)
    v["m2_P"], v["m2_win"] = s["res"]["pay"]["P"], s["res"]["p_won"]
    v["det"] = {nm: (spe_c(nm, N, 100, "root", pr)["res"]["pay"]["P"], spe_c(nm, N, 100, "root", pr)["best_P"]) for nm in (N3, N4m, N4)}
    v["s1_pub_M3"] = spe_c(N3, N, 100, "root", pr)["h"] is not None
    v["s3"] = {nm: (spe_c(nm, N, 100, "clone", pr)["h"] is not None, spe_c(nm, N, 100, "clone", pr)["res"]["pay"]["H"]) for nm in (N3, N4m, N4)}
    q, p, R = attackers(MECH[N4], N, 12, 38, "root", pr); x = R[q, p]
    v["cf"] = (x["pay"]["Q"], x["pay"]["H"], x["sponsor"], q)
    v["pub24"] = {nm: spe_c(nm, 24, 12, "root", pr)["h"] is not None for nm in (N4m, N4)}
    v["w_profit"] = pr["b_finder"] - pr["g_t6"] - pr["c_search"]
    # claims
    v["c1"] = v["m2_P"] > 0
    v["c2"] = all(pn == 0 and (bp is None or bp < 0) for pn, bp in v["det"].values())
    v["c3"] = v["s1_pub_M3"] and (not v["s3"][N3][0]) and v["s3"][N4m][0] and v["s3"][N4][0]
    v["c4a"] = v["cf"][3] is None and v["cf"][2] >= 0
    v["c4b"] = v["pub24"][N4] and not v["pub24"][N4m]
    return v

def yn(b): return "Y" if b else "n"
def sgn(pub, net): return f"{net:+d}{'*' if pub else ' '}"

def sweep_table(title, label, points, mk):
    print("\n" + "=" * 124)
    print(title)
    print("=" * 124)
    print("  claims:  (1) M2 pre-embedding exploited   (2) M3/M4-/M4 deter it   (3) S3: M3 collapses while M4-/M4 stay robust   "
          "(4a) M4 sponsor excludes clone   (4b) publication recovered at N=24 only by M4")
    print("  '*' = the author publishes in equilibrium.   T6 = watchtower profit B_finder - g_T6 - c_search (T6 is submitted iff > 0)")
    print(f"  {label:>8} | {'M2 P net':>8} {'best P win':>10} | {'S3 author net: M3 / M4- / M4':^32} | {'cf: Q net / author / sponsor':^28} | "
          f"{'N=24 pub':^9} | {'T6':>3} | claims 1 2 3 4a 4b")
    rows = []
    for pt in points:
        pr = mk(pt); v = verdicts(pr)
        bp = [b for _, b in v["det"].values() if b is not None]
        bps = "no win" if not bp else str(max(bp))
        s3 = " / ".join(f"{sgn(*v['s3'][nm]):>5}" for nm in (N3, N4m, N4))
        cf = f"{v['cf'][0]:>5} / {v['cf'][1]:>5} / {v['cf'][2]:>4}"
        pub = f"{yn(v['pub24'][N4m])} / {yn(v['pub24'][N4])}"
        print(f"  {str(pt):>8} | {v['m2_P']:>8} {bps:>10} | {s3:^32} | {cf:^28} | {pub:^9} | {v['w_profit']:>3} |"
              f"      {yn(v['c1'])} {yn(v['c2'])} {yn(v['c3'])}  {yn(v['c4a'])}  {yn(v['c4b'])}")
        rows.append((pt, v))
    return rows

def min_s_audit(pr_kw):
    """Smallest S_audit for which the watchtower's T6 submission is profitable: floor(0.3*S) - g_T6 - c_search > 0."""
    for sa in range(1, 1000):
        p = make_pr(s_audit=sa, **pr_kw)
        if p["b_finder"] - p["g_t6"] - p["c_search"] > 0: return sa
    return None

def sweeps():
    print("\n" + "#" * 124)
    print("EXPERIMENT 4b: ROBUSTNESS / SENSITIVITY OF THE MECHANISM ABLATION   (N = 12 unless stated; baseline c_dev = 20, g_tx = 1, p_know = 1.00)")
    print("#" * 124)
    rowsA = sweep_table("SWEEP A: axiom development cost c_dev (tokens)", "c_dev", (5, 10, 20, 40, 80), lambda c: make_pr(c_dev=c))
    rowsB = sweep_table("SWEEP B: transaction gas g_tx (tokens); g_T6 = 2 g_tx + 1, S_audit = 20 (B_finder = 6)", "g_tx", (0, 1, 2, 5), lambda g: make_pr(g_tx=g))
    print("\n  S_audit repair of the T6 boundary (B_finder = floor(0.30 S_audit)):")
    print(f"  {'g_tx':>5} {'g_T6':>5} {'min S_audit':>12} {'B_finder':>9}   S3 outcome of M4- with S_audit = 20  ->  with the minimal S_audit")
    for g in (0, 1, 2, 5):
        sa = min_s_audit(dict(g_tx=g)); p20 = make_pr(g_tx=g); pm = make_pr(g_tx=g, s_audit=sa)
        a = spe_c(N4m, 12, 100, "clone", p20); b = spe_c(N4m, 12, 100, "clone", pm)
        print(f"  {g:>5} {p20['g_t6']:>5} {sa:>12} {pm['b_finder']:>9}   author {sgn(a['h'] is not None, a['res']['pay']['H']):>6} (W {int(round(a['res']['W']))})"
              f"  ->  author {sgn(b['h'] is not None, b['res']['pay']['H']):>6} (W {int(round(b['res']['W']))})")
    pk_rows = []
    print("\n" + "=" * 124)
    print("SWEEP C: attacker P's advance knowledge p_know = (known bits of D_1) / 16,384   (unknown bits must be coded raw by the recipe)")
    print("=" * 124)
    print(f"  {'p_know':>7} {'known b':>8} {'|p_P|':>7} {'Phi_P (M2)':>11} {'honest Phi':>11} | {'M2: P wins D_1':>14} {'M2 P net':>9} {'M2 W':>8} | "
          f"{'M3/M4: P can win':>16} {'best win':>9} {'SPE P net':>10}")
    for pk in (0.25, 0.50, 0.75, 1.00):
        know = int(round(pk * PHI0)); pr = make_pr(know=know)
        s2 = spe_c(N2, 12, 100, "root", pr); s3 = spe_c(N3, 12, 100, "root", pr)
        phiP = 24 + 0 + ELL_E + pr["look_res"]                       # free exemption: nothing unamortized
        print(f"  {pk:>7.2f} {know:>8} {pr['look_size']:>7} {phiP:>11} {822:>11} | {yn(s2['res']['p_won']):>14} {s2['res']['pay']['P']:>9} "
              f"{int(round(s2['res']['W'])):>8} | {yn(s3['best_P'] is not None):>16} {('no win' if s3['best_P'] is None else s3['best_P']):>9} "
              f"{s3['res']['pay']['P']:>10}")
    # ------------------------------------------------------------------ exact boundaries
    print("\n" + "=" * 124)
    print("EXACT BOUNDARIES (monotone bisection on the integer parameter, each verified against the closed form where one exists)")
    print("=" * 124)
    c1 = last_true(lambda c: spe_c(N3, 12, 100, "root", make_pr(c_dev=c))["h"] is not None, 0, 400)
    c3 = last_true(lambda c: spe_c(N4m, 12, 100, "clone", make_pr(c_dev=c))["h"] is not None, 0, 400)
    c4 = last_true(lambda c: spe_c(N4, 24, 12, "root", make_pr(c_dev=c))["h"] is not None, 0, 400)
    c4_12 = last_true(lambda c: spe_c(N4, 12, 12, "root", make_pr(c_dev=c))["h"] is not None, 0, 400)
    print(f"  c_dev : S1 publication (M3, M4-, M4)            holds iff c_dev <= {c1}   [closed form: royalties 108 - burn 50 - DA 1 - gas 1 = 56]")
    print(f"          S3 robustness of M4- / M4 (publishes)   holds iff c_dev <= {c3}")
    print(f"          dormant author, M4 + sponsor, N = 24    publishes iff c_dev <= {c4};   at N = 12 iff c_dev <= {c4_12}")
    g1 = last_true(lambda g: spe_c(N3, 12, 100, "root", make_pr(g_tx=g))["h"] is not None, 0, 200)
    g3 = last_true(lambda g: spe_c(N4m, 12, 100, "clone", make_pr(g_tx=g))["h"] is not None, 0, 200)
    gt = last_true(lambda g: make_pr(g_tx=g)["b_finder"] - make_pr(g_tx=g)["g_t6"] - make_pr(g_tx=g)["c_search"] > 0, 0, 200)
    g4 = last_true(lambda g: spe_c(N4, 24, 12, "root", make_pr(g_tx=g))["h"] is not None, 0, 200)
    print(f"  g_tx  : T6 profitable for the watchtower        iff g_tx <= {gt}   [closed form: 6 - (2 g_tx + 1) - 1 > 0]")
    print(f"          S3 robustness of M4- (publishes)        iff g_tx <= {g3}   (it equals the T6 boundary: beyond it M4- degrades to M3)")
    print(f"          S1 publication (M3)                     iff g_tx <= {g1};   dormant author, M4, N = 24: iff g_tx <= {g4}")
    k2 = first_true(lambda k: spe_c(N2, 12, 100, "root", make_pr(know=k))["res"]["p_won"], 0, PHI0)
    k3 = first_true(lambda k: spe_c(N3, 12, 100, "root", make_pr(know=k))["best_P"] is not None, 0, PHI0)
    print(f"  p_know: M2 pre-embedding exploit (P wins D_1)   iff known bits >= {k2}  (p_know >= {k2 / PHI0:.4f}); closed form 24+4+34+(16384-k) < 822")
    print(f"          M3/M4 attack can even win D_1           iff known bits >= {k3}  (p_know >= {k3 / PHI0:.4f}); there its best payoff stays negative")
    assert (c1, c3) == (56, 56) and gt == 1 and g3 == 1 and k2 == 15625
    # ---- (4b) needs M4- NOT to publish at N = 24: find where M4- starts / stops publishing
    pub4m = lambda c: spe_c(N4m, 24, 12, "root", make_pr(c_dev=c))["h"] is not None
    c4m = last_true(pub4m, 0, 400)
    print(f"          dormant author, M4- (T6 only), N = 24  publishes iff c_dev <= {c4m}  => claim (4b) holds for {c4m + 1} <= c_dev <= {c4}")
    # ---- robustness map
    allA = rowsA + rowsB
    ok = lambda key: all(v[key] for _, v in allA)
    sa = {g: min_s_audit(dict(g_tx=g)) for g in (2, 5)}
    print("\n" + "=" * 124)
    print("ROBUSTNESS MAP  (each axis varied alone, the others at baseline c_dev = 20, g_tx = 1, p_know = 1.00, S_audit = 20, N = 12)")
    print("=" * 124)
    print(f"  {'claim':<70}{'c_dev (tokens)':<20}{'g_tx (tokens)':<30}{'p_know'}")
    print(f"  {'(1) M2: free exemption is exploited by pre-embedding':<70}{'all tested 5..80' if ok('c1') else 'see table':<20}"
          f"{'all tested 0..5' if ok('c1') else 'see table':<30}{'>= ' + format(k2 / PHI0, '.4f')}")
    print(f"  {'(2) M3/M4-/M4: pre-embedding deterred (best winning payoff < 0)':<70}{'all tested 5..80' if ok('c2') else 'see table':<20}"
          f"{'all tested 0..5' if ok('c2') else 'see table':<30}{'all (cannot win below ' + format(k3 / PHI0, '.4f') + ')'}")
    print(f"  {'(3) S3: M3 collapses, M4-/M4 keep the publication equilibrium':<70}{'<= ' + str(c3):<20}{'<= ' + str(g3) + ' (S_audit = 20)':<30}{'n/a (independent)'}")
    print(f"  {'    ... T6 boundary repaired by raising S_audit to':<70}{'':<20}{'>= ' + str(sa[2]) + ' (g_tx=2), >= ' + str(sa[5]) + ' (g_tx=5)':<30}")
    print(f"  {'(4a) M4: sponsor co-financing excludes the clone (dormant author)':<70}{'all tested 5..80' if ok('c4a') else 'see table':<20}"
          f"{'all tested 0..5' if ok('c4a') else 'see table':<30}{'n/a (independent)'}")
    print(f"  {'(4b) publication recovered at N = 24 by M4 only (not by M4-)':<70}{str(c4m + 1) + '..' + str(c4):<20}{'0..' + str(g4):<30}{'n/a (independent)'}")
    assert ok("c1") and ok("c2") and ok("c4a") and (c4m, c4, g4) == (10, 126, 107)
    return dict(c1=c1, c3=c3, c4=c4, c4_12=c4_12, g1=g1, g3=g3, gt=gt, g4=g4, k2=k2, k3=k3, c4m=c4m)


# ====================================================================================== Experiment 4c: adaptive no-regret learning
import math, random

def build_game(mname, N, budget, tie="root", pr=PR0, rbf_choices=(0, 38)):
    """Payoff tensor G[h][q][p][w] = (u_H, u_Q, u_P, u_W, welfare) over the finite action sets of the four learning agents.
    H: None or (own burn, sponsor burn); Q: None or clone (size, burn); P: None or lookup burn; W: watch / ignore (only when the mechanism has T6).
    W earns B_finder - g_T6 - c_search iff it watches and a clone exists; a sponsor request that would lose money is declined."""
    m = MECH[mname]
    burns = [b for b in ((0,) if m["amort"] != "burn" else (0, 6, 12, 25, 50, 60)) if b <= budget]
    Hs = [None] + [(b, r) for b in burns for r in (rbf_choices if m["rbf"] else (0,))]
    Qs, Ps = grids(m, pr)
    Ws = ["watch", "ignore"] if m["t6"] else ["-"]
    G = [[[[None] * len(Ws) for _ in Ps] for _ in Qs] for _ in Hs]
    for ih, h in enumerate(Hs):
        for iq, q in enumerate(Qs):
            for ip, p in enumerate(Ps):
                for iw, w in enumerate(Ws):
                    mm = dict(m, t6=False) if w == "ignore" else m
                    if h is None: res = play(mm, N, None, None, p, 0, tie, pr)
                    else:
                        b, r = h
                        res = play(mm, N, b, q, p, r, tie, pr)
                        if r and res["sponsor"] < 0: res = play(mm, N, b, q, p, 0, tie, pr)
                    uW = res["wt"] if (w == "watch" and res["t6"]) else 0
                    G[ih][iq][ip][iw] = (res["pay"]["H"], res["pay"]["Q"], res["pay"]["P"], uW, float(res["W"]))
    return dict(G=G, Hs=Hs, Qs=Qs, Ps=Ps, Ws=Ws, t6=m["t6"])

def _softmax(lw):
    mx = max(lw); e = [math.exp(x - mx) for x in lw]; z = sum(e); return [x / z for x in e]

def _sample(p, rng):
    u = rng.random(); c = 0.0
    for i, x in enumerate(p):
        c += x
        if u < c: return i
    return len(p) - 1

def hedge(game, T, seed, eta, scale, cps):
    """Full-information Hedge (multiplicative weights) for the four agents: every agent starts uniform, an action profile is SAMPLED
    from the current mixed strategies each episode, and every agent updates all its weights with the payoff each of its actions
    would have earned against the others' sampled actions:  w_a <- w_a * exp(eta * u_a / scale).  Returns snapshots at `cps`."""
    G = game["G"]; sizes = (len(game["Hs"]), len(game["Qs"]), len(game["Ps"]), len(game["Ws"]))
    rng = random.Random(seed); lw = [[0.0] * n for n in sizes]; snaps = {}
    for t in range(1, T + 1):
        pr_ = [_softmax(x) for x in lw]
        act = [_sample(p, rng) for p in pr_]
        U = G[act[0]][act[1]][act[2]][act[3]]
        if t in cps: snaps[t] = (pr_, U[4])
        for i in range(4):
            for ai in range(sizes[i]):
                aa = list(act); aa[i] = ai
                lw[i][ai] += eta * G[aa[0]][aa[1]][aa[2]][aa[3]][i] / scale
    return snaps

def conditional_w(g):
    """Sequential / conditional watchtower: W observes the on-chain registry and submits T6 exactly when a clone has been registered
    (a strict best response, B_finder - g_T6 - c_search = +2 > 0).  Implemented by restricting W to the single action 'watch'."""
    G = g["G"]
    G2 = [[[[G[ih][iq][ip][0]] for ip in range(len(g["Ps"]))] for iq in range(len(g["Qs"]))] for ih in range(len(g["Hs"]))]
    return dict(g, G=G2, Ws=["watch"])

LEARN = dict(T=200, eta=0.3, scale=10.0, seeds=20, cps=(1, 25, 50, 100, 200))

def learn(mname, N, budget, tie="root", eta=None, pr=PR0, game=None):
    """Average Hedge dynamics over LEARN['seeds'] fixed seeds; returns mean probabilities / realized welfare at the checkpoints."""
    eta = LEARN["eta"] if eta is None else eta
    g = game or build_game(mname, N, budget, tie, pr)
    cps, S = LEARN["cps"], LEARN["seeds"]
    acc = {t: dict(H=0.0, Q=0.0, P=0.0, W=0.0, Wt=0.0) for t in cps}; Hp = [0.0] * len(g["Hs"])
    for seed in range(S):
        sn = hedge(g, LEARN["T"], seed, eta, LEARN["scale"], cps)
        for t in cps:
            p, Wt = sn[t]
            acc[t]["H"] += (1 - p[0][0]) / S; acc[t]["Q"] += (1 - p[1][0]) / S; acc[t]["P"] += (1 - p[2][0]) / S
            acc[t]["W"] += (p[3][0] / S if g["t6"] else 0.0); acc[t]["Wt"] += Wt / S
        for i, x in enumerate(sn[cps[-1]][0][0]): Hp[i] += x / S
    mode = max(range(len(Hp)), key=lambda i: Hp[i])
    return dict(traj=acc, H_mode=(g["Hs"][mode], Hp[mode]), t6=g["t6"])

def print_learning(title, mname, N, budget, tie, res):
    spe_r = spe_c(mname, N, budget, tie, PR0)["res"]
    print(f"\n  {title}   [N = {N}, author budget {budget}, tie-break: {tie};  SPE welfare W* = {int(round(spe_r['W']))}]")
    print(f"  {'episode t':>12}" + "".join(f"{t:>10}" for t in LEARN["cps"]))
    for key, lab in (("H", "H publishes"), ("Q", "Q clones"), ("P", "P pre-embeds"), ("W", "W watches")):
        vals = [res["traj"][t][key] for t in LEARN["cps"]]
        print(f"  {lab:>12}" + "".join(f"{('n/a' if (key == 'W' and not res['t6']) else format(v, '.4f')):>10}" for v in vals))
    print(f"  {'realized W_t':>12}" + "".join(f"{res['traj'][t]['Wt']:>10.0f}" for t in LEARN["cps"]))
    hm, hp = res["H_mode"]
    print(f"  H modal action at t = {LEARN['T']}: {hm} (mean prob {hp:.3f});   |W_{LEARN['T']} - W*| = {abs(res['traj'][LEARN['T']]['Wt'] - float(spe_r['W'])):.1f}")
    if res["traj"][LEARN["T"]]["H"] <= 0.01:
        print("  (note: once H stays out there is no root to copy, so Q's payoffs are identical for all its actions and its probability no longer moves)")

def learning():
    names = list(MECH); M2, M3, M4m, M4f = names[1], names[2], names[3], names[4]
    print("\n" + "#" * 124)
    print(f"EXPERIMENT 4c: ADAPTIVE LEARNING DYNAMICS (full-information Hedge / multiplicative weights; T = {LEARN['T']} episodes, {LEARN['seeds']} fixed seeds,"
          f" eta = {LEARN['eta']}, payoff scale {LEARN['scale']:.0f} tokens)")
    print("#" * 124)
    print("  Every agent (H author, Q clone plagiarist, P pre-embedding attacker, W watchtower) starts from the UNIFORM mixed strategy; probabilities below are")
    print("  means over seeds; W_t is the mean welfare of the sampled action profile. 'H publishes' = 1 - P(H stays out); 'W watches' only exists with T6.")
    R = {}
    print("\n" + "=" * 124 + "\nL1: well-funded author, favourable tie-break (the paper's baseline market)\n" + "=" * 124)
    for nm, lab in ((M2, "M2 naive citation (free)"), (M3, "M3 burn amortization, no T6"), (M4f, "M4 ESM full (+RBF)")):
        R[nm, "L1"] = learn(nm, 12, 100, "root"); print_learning(lab, nm, 12, 100, "root", R[nm, "L1"])
    print("\n" + "=" * 124 + "\nL2: the equilibrium boundaries of Section 8.4 reproduced by learning\n" + "=" * 124)
    L2 = ((M3, 12, 100, "clone", "S3 adversarial tie-break: M3"), (M4f, 12, 100, "clone", "S3 adversarial tie-break: M4"),
          (M4m, 24, 12, "root", "capital-constrained author, N = 24: M4- (T6 only)"), (M4f, 24, 12, "root", "capital-constrained author, N = 24: M4 (+RBF)"))
    for nm, N, bud, tie, lab in L2:
        R[nm, lab] = learn(nm, N, bud, tie); print_learning(lab, nm, N, bud, tie, R[nm, lab])
    LSEQ = "S3 adversarial tie-break: M4, SEQUENTIAL (conditional) watchtower"
    R[M4f, LSEQ] = learn(M4f, 12, 100, "clone", game=conditional_w(build_game(M4f, 12, 100, "clone")))
    print_learning(LSEQ, M4f, 12, 100, "clone", R[M4f, LSEQ])
    # learning-rate robustness (final state at t = T)
    print("\n" + "=" * 124 + "\nL3: robustness to the learning rate eta (state at t = T, L1 market)\n" + "=" * 124)
    print(f"  {'mechanism':<30}{'eta':>6}{'H publishes':>13}{'Q clones':>10}{'P pre-embeds':>14}{'W_T':>9}")
    LR = {}
    for nm in (M2, M4f):
        g = build_game(nm, 12, 100, "root")
        for eta in (0.1, 0.3, 1.0):
            r = learn(nm, 12, 100, "root", eta=eta, game=g); LR[nm, eta] = r; f = r["traj"][LEARN["T"]]
            print(f"  {nm:<30}{eta:>6}{f['H']:>13.4f}{f['Q']:>10.4f}{f['P']:>14.4f}{f['Wt']:>9.0f}")
    # ------------------------------------------------------------------ assertions (reproducible: fixed seeds)
    T = LEARN["T"]; f = lambda r: r["traj"][T]
    m2, m3, m4 = f(R[M2, "L1"]), f(R[M3, "L1"]), f(R[M4f, "L1"])
    assert m2["P"] >= 0.999 and m2["H"] >= 0.999 and abs(m2["Wt"] - 104345) < 1                      # M2: exploited, welfare drops to 104,345
    for x in (m3, m4):
        assert x["P"] <= 0.001 and x["Q"] <= 0.001 and x["H"] >= 0.999 and abs(x["Wt"] - 113894) < 1  # M3/M4: attacks decay to 0, H publishes
    assert R[M4f, "L1"]["H_mode"][0] == (50, 0) and R[M4f, "L1"]["H_mode"][1] >= 0.99
    assert 0.79 < R[M4f, "L1"]["traj"][1]["P"] < 0.81 and 0.49 < R[M2, "L1"]["traj"][1]["P"] < 0.51
    pk = [R[M4f, "L1"]["traj"][t]["P"] for t in LEARN["cps"]]; assert all(a >= b for a, b in zip(pk, pk[1:]))               # monotone decay
    rate = math.log(R[M4f, "L1"]["traj"][25]["P"] / R[M4f, "L1"]["traj"][50]["P"]) / 25                                    # fitted exponential rate
    print(f"\n  exponential decay of P's pre-embedding probability in M4 (L1): fitted rate between t = 25 and t = 50 is {rate:.4f} per episode; "
          f"theory for the slowest-decaying attack (a losing lookup costing 3 tokens): eta * 3 / scale = {LEARN['eta'] * 3 / LEARN['scale']:.4f}")
    assert 0.08 <= rate <= 0.095
    s3m3, s3m4 = f(R[M3, L2[0][4]]), f(R[M4f, L2[1][4]])
    assert s3m3["H"] <= 0.01 and abs(s3m3["Wt"] - 113193) < 1                                         # S3: M3 collapses
    assert s3m4["H"] >= 0.90 and s3m4["Wt"] > s3m3["Wt"] + 600 and s3m4["P"] <= 0.001                 # S3: M4 stays (near-)SPE
    d24m, d24f = f(R[M4m, L2[2][4]]), f(R[M4f, L2[3][4]])
    assert d24m["H"] <= 0.01 and abs(d24m["Wt"] - 226386) < 1 and d24f["H"] >= 0.999 and abs(d24f["Wt"] - 227861) < 1
    assert R[M4f, L2[3][4]]["H_mode"][0] == (12, 38)
    sq = f(R[M4f, LSEQ])                                                                              # sequential W: exact SPE convergence
    assert sq["H"] >= 0.9995 and sq["Q"] <= 0.0005 and sq["P"] <= 0.0005 and abs(sq["Wt"] - 113894) < 0.5
    assert R[M4f, LSEQ]["H_mode"][0] == (50, 0) and s3m4["Q"] > 0.01                                  # while the simultaneous-move W leaves a residual
    assert LR[M2, 0.3]["traj"][T]["P"] >= 0.999 and LR[M4f, 0.3]["traj"][T]["P"] <= 0.001 and LR[M4f, 0.3]["traj"][T]["Q"] <= 0.001
    assert LR[M4f, 1.0]["traj"][T]["H"] >= 0.999 and LR[M4f, 0.1]["traj"][T]["H"] >= 0.999
    print("\n  Experiment 4c assertions: PASS  (M2: P -> 1, welfare 104,345;  M3/M4 (L1): P, Q -> 0, H -> 1, welfare 113,894;  S3 and dormant-author boundaries reproduced;"
          "\n                                  sequential W in S3-M4: H = 1.000, Q = P = 0.000, W_200 = W* = 113,894)")


# ====================================================================================== manuscript Tables 6 and 7: every printed cell
PAPER6 = [   # Section 8.4, Table 6: S1 welfare | S1 author royalty / net | P net (best attack) | S3 author net | S3 welfare   (M1, M2, M3, M4-, M4)
    ["113,193", "0 / 0",      "0 (no winning attack)", "0",   "113,193"],
    ["104,345", "99 / +77",   "+9,271",                "0",   "103,708"],
    ["113,894", "108 / +36",  "0 (-238)",              "0",   "113,193"],
    ["113,894", "108 / +36",  "0 (-238)",              "+36", "113,894"],
    ["113,894", "108 / +36",  "0 (-238)",              "+36", "113,894"],
]
PAPER7 = [   # Section 8.4, Table 7: publishes (N=12) | clone Q net | author royalty / net | N=24 author net | N=24 welfare
    ["no",                   "0",              "0 / -22",  "0",    "226,386"],
    ["yes (free exemption)", "0 (P: +9,271)",  "99 / +77", "+185", "218,312"],
    ["no",                   "+58",            "0 / -34",  "0",    "226,386"],
    ["no",                   "+32",            "12 / -22", "0",    "226,386"],
    ["no (net -2)",          "0",              "108 / -2", "+106", "227,861"],
]

def tables67_check():
    sg = lambda x: "0" if x == 0 else f"{x:+d}"
    c6, c7 = [], []
    for nm, m in MECH.items():
        s1, s3 = spe_c(nm, 12, 100, "root", PR0), spe_c(nm, 12, 100, "clone", PR0)
        r1, r3 = s1["res"], s3["res"]
        p = f"{r1['pay']['P']:+,d}" if r1["pay"]["P"] > 0 else ("0 (no winning attack)" if s1["best_P"] is None else f"0 ({s1['best_P']})")
        c6.append([f"{int(round(r1['W'])):,}", f"{r1['H_gross']} / {sg(r1['pay']['H'])}", p, sg(r3["pay"]["H"]), f"{int(round(r3['W'])):,}"])
        pub = spe_c(nm, 12, 12, "root", PR0)["h"] is not None                                   # equilibrium of the capital-constrained author
        hh, rr = (12 if m["amort"] == "burn" else 0), (38 if m["rbf"] else 0)                    # publish-anyway counterfactual (sponsor 38 in M4)
        q, pp, R = attackers(m, 12, hh, rr, "root", PR0); x = R[q, pp]
        qcell = sg(x["pay"]["Q"]) + (f" (P: {x['pay']['P']:+,d})" if x["pay"]["P"] > 0 else "")
        pubcell = "yes (free exemption)" if (pub and m["amort"] == "free") else ("yes" if pub else ("no" if not rr else f"no (net {x['pay']['H']:+d})"))
        r24 = spe_c(nm, 24, 12, "root", PR0)["res"]
        c7.append([pubcell, qcell, f"{x['H_gross']} / {sg(x['pay']['H'])}", sg(r24["pay"]["H"]), f"{int(round(r24['W'])):,}"])
    bad = [(t, i, j, got, exp) for t, g, e in (("Table 6", c6, PAPER6), ("Table 7", c7, PAPER7))
           for i in range(5) for j in range(5) for got, exp in [(g[i][j], e[i][j])] if got != exp]
    assert not bad, bad
    print("\n  Table 6 and Table 7: all cells equal the manuscript: PASS   (2 tables x 5 mechanisms x 5 columns = 50 cells)")

if __name__ == "__main__":
    import sys
    checks()
    tables67_check()
    if "--learning" in sys.argv:
        learning(); sys.exit(0)
    if "--sweeps" not in sys.argv:
        report(100, "S1 (well-funded honest author)", 12)
        report(12, "S2 (capital-constrained / dormant honest author)", 12)
        committed(12)
        report(100, "S3 (well-funded author, ADVERSARIAL tie-break: proposers prefer the clone on exact ties)", 12, tie="clone")
        sensitivity()
    sweeps()
    if "--sweeps" not in sys.argv:
        learning()
