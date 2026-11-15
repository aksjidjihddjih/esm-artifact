#!/usr/bin/env python3
"""Pack the differential-test vectors for Foundry.
 * tags produced by Lean `#eval` of ESM_verified.lean (gen/lean_vectors.txt) are packed as they are;
 * the remaining tags (derived formulas that exist only inside theorem statements / the paper) come from an
   independent Python big-integer oracle written from the Lean text.
Every file is `abi.encode(uint256[])` of fixed-arity rows (list rows carry their own length)."""
import random, pathlib, collections
from decimal import Decimal, getcontext
getcontext().prec = 90
ROOT = pathlib.Path(__file__).resolve().parent.parent
V = ROOT / "vectors"; V.mkdir(exist_ok=True)
rows = collections.defaultdict(list)
for line in (ROOT / "gen/lean_vectors.txt").read_text().splitlines():
    t = line.split(); rows[t[0]].append([int(x) for x in t[1:]])

rng = random.Random(20260811)
TOK, BITS = 2**96 - 1, 2**40
def rnd(mx):
    k = rng.randrange(12)
    if k == 0: return 0
    if k == 1: return min(1, mx)
    if k == 2: return mx
    if k == 3: return max(mx - 1, 0)
    b = rng.choice([1, 3, 5, 8, 16, 24, 32, 48, 64, 96])
    return rng.getrandbits(b) % (mx + 1)
monus = lambda a, b: a - b if a > b else 0
def cdiv(a, b): return 0 if b == 0 else -(-a // b)
def clog2(x):
    k = 0
    while (1 << k) < max(x, 1): k += 1
    return k
N = 2500
for _ in range(N):
    T, w = rnd(2**128), max(rnd(2**100), 1)
    k = 1
    while (1 << k) * w < T: k += 1
    rows["SHAN"].append([T, w, k])                                    # min k>=1 with 2^k * w >= T  (the definition, by brute force)
    x = rnd(2**128); rows["CLOG"].append([x, clog2(x)])
    a, l, c = rnd(BITS), rnd(BITS), rnd(BITS)
    xi = min(a, l, c); rows["ST2"].append([a, l, c, xi, a - xi, c - xi])
    n = rng.randrange(0, 17)
    dtr = max(rnd(BITS), 1); xs = []; rest = dtr
    for _ in range(n):
        v = rng.randrange(0, rest + 1) if rng.random() < 0.8 else (rest if rng.random() < 0.5 else 0); xs.append(v); rest -= v
    eT, eps, gam, phi = rnd(TOK), rnd(10000), rnd(10000), rnd(10000)
    burn = eps * eT // 10000; net = eT - burn
    anc = sum(gam * net * x // (10000 * dtr) for x in xs); rem = monus(net, anc); guar = phi * rem // 10000
    rows["SETTLE"].append([eT, dtr, eps, gam, phi, n, *xs, burn, net, anc, rem, guar, rem - guar])
    Rx, beta, Dt, pd = rnd(TOK), rnd(10000), rnd(2**97), rnd(10000)
    St = rnd(2**60); Sb = rng.randrange(0, St + 1) if St else 0
    anchor = beta * Rx // 10000; rn = Rx - anchor; rbf = min(rn, Dt); rr = rn - rbf
    dic = 0 if St == 0 else pd * Sb * rr // (10000 * St)
    rows["SLOT4"].append([Rx, beta, Dt, pd, Sb, St, anchor, rbf, dic, rr - dic])
    Du, Ds = rnd(2**97), rnd(2**97)
    pu = min(rn, Du); ra = rn - pu; ps = min(ra, Ds); rm = ra - ps; dv = rnd(rm)
    rows["M1"].append([Rx, beta, Du, Ds, dv, anchor, pu, ps, dv, rm - dv])
    B, Phi = rnd(TOK), rnd(BITS)
    Ei, Ea, di, da = rnd(TOK), rnd(TOK), rnd(2**39), rnd(2**39)
    dri, dra, dun = rng.randrange(0, di + 1), rng.randrange(0, da + 1), rnd(BITS)
    escr = lambda d: 0 if Phi == 0 else B * d // Phi
    sr = lambda E, dt, dr: 0 if dt == 0 else min(E * dr // dt, escr(dr))
    eri, era = sr(Ei, di, dri), sr(Ea, da, dra); et = Ei + Ea; er = eri + era
    eu = min(monus(et, er), escr(dun)); rows["UNROLL"].append([B, Phi, Ei, Ea, di, da, dri, dra, dun, eri, era, eu, monus(monus(et, er), eu)])
    d = max(rnd(BITS), 1); r = rng.randrange(0, d + 1); base, xs_, xu_ = rnd(TOK), rnd(2**60), rnd(2**60)
    sym = monus(base + xs_ + xu_, (xs_ - xs_ * r // d) + (xu_ - xu_ * r // d))
    assert sym == base + xs_ * r // d + xu_ * r // d                  # the Lean lemma, re-checked on every vector
    rows["SYMREL"].append([base, xs_, xu_, r, d, sym, monus(base + xs_ + xu_, xu_ - xu_ * r // d)])
    rb, S, kap = rnd(10000), rnd(TOK), rnd(10000)
    sl = cdiv(rb * S, 10000); hu = (10000 - kap) * sl // 10000; rows["SLASH"].append([rb, S, kap, sl, hu, sl - hu])
    rows["REFUND"].append([S, 3000 * S // 10000])
    kp, sg, lam, ep = rnd(10000), max(rnd(10000), 1), rng.choice([0, 10000, rng.randrange(0, 20001)]), rnd(10000)
    num, den = kp * sg * 10000, (10000 + lam) * (10000 - ep)
    gmax = 0 if (num == 0 or den == 0) else (num - 1) // den
    if gmax: assert num > den * gmax and (num <= den * (gmax + 1))     # largest gamma satisfying the strict inequality
    rows["GMAX"].append([kp, sg, lam, ep, gmax])
    ga = rnd(10000); kmin = (10000 + lam) * ga * (10000 - ep) // (sg * 10000) + 1
    assert kmin * sg * 10000 > (10000 + lam) * ga * (10000 - ep) and (kmin - 1) * sg * 10000 <= (10000 + lam) * ga * (10000 - ep)
    rows["KMIN"].append([ga, sg, lam, ep, kmin])
for K in (1, 2, 8, 16, 32, 64, 128):
    for kap in (1000, 3000, 5000, 7000, 9000, 10000):
        for lam in (0, 5000, 10000, 20000):
            ratio = Decimal(kap) / (Decimal(kap) + Decimal(9500) * (10000 + lam) / 10000)
            lo, hi = 0, 10**9
            while lo < hi:
                mid = (lo + hi) // 2
                if (Decimal(1) - Decimal(mid) / Decimal(10**9)) ** K <= ratio: hi = mid
                else: lo = mid + 1
            rows["FGR"].append([K, kap, lam, lo])
for sl in (5000, 7000, 9000, 10000):
    for lam in (0, 10000):
        num = 9500 * (10000 + lam); den = sl * 10000 + num; rows["QDET"].append([sl, lam, (num * 10**6 + den // 2) // den])

def pack(words):
    out = (32).to_bytes(32, "big") + len(words).to_bytes(32, "big")
    for w in words:
        assert 0 <= w < 2**256, w; out += w.to_bytes(32, "big")
    return out
tot = 0
for tag, rs in sorted(rows.items()):
    flat = [w for r in rs for w in r]
    bad = [(i, r) for i, r in enumerate(rs) if any(w < 0 or w >= 2**256 for w in r)]
    if bad: raise SystemExit(f"BAD {tag} row {bad[0][0]}: {bad[0][1]}")
    (V / f"{tag}.bin").write_bytes(pack(flat)); tot += len(rs)
    print(f"{tag:8s} rows={len(rs):5d} words={len(flat)}")
print("total rows", tot)
