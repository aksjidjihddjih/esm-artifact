#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""
ESM Empirical Suite -- Experiment 1 (self-contained, stdlib only)

  * Elias-omega length, exact integer escrow / royalty primitives
  * Binary Lambda Calculus (Tromp) encoder / parser
  * Krivine Abstract Machine (call-by-name, step-counted, T_max ceiling)
  * Genuine BLC programs (written with a named-variable builder, compiled to
    de Bruijn) for Benchmarks 1-3, each VERIFIED against its law on all records
  * Counted-MST residual length computed from the REAL residual vector
  * Side-by-side comparison with the numbers currently printed in the paper

Canonical totalized evaluation (paper Sec. 3.1(ii)): run_program_total / run_bits_total fall back to
y_hat = 0^{b_k} when the proposer-declared step ceiling delta is exceeded (steps > delta), when the
output is not a width-b_k Scott bit-list, when the term is open, or when the bit-string does not parse.

Bit definition used by the decoder (Sec. 3.1): a term b is a bit iff, applied to two opaque arguments (MK0, MK1),
it reduces to the first (bit 0) or to the second (bit 1); end-of-list is detected by passing MKEND as the "nil"
argument. Any other result (a lambda, a stuck marker application, an open term) is a non-bit => fallback 0^{b_k}.

Benchmark 4 (Experiment 3): T6 syntactic reduction  U(q(p_s)) =_{beta eta} p_i  for two measured clones of v_s,
plus Stage-2 royalty redirection (Eqs. stage2_init_cap / stage2_redirect) on the Benchmark-3 tranche.

Usage:  python esm_exp1_2.py            (full run, n_k = 1024, incl. Benchmark 4)
        python esm_exp1_2.py --b4       (Benchmark 4 only)
        python esm_exp1.py --selftest (fast unit checks only)
        python esm_exp1.py --scaling  (runtime vs n_k = 256..4096)
"""
import sys, time, random
from dataclasses import dataclass
from typing import Optional, Tuple, List, Dict

T_MAX = 1 << 20

# ------------------------------------------------------------------ primitives
def floor_log2(n: int) -> int:
    assert n >= 1
    return n.bit_length() - 1

def elias_omega_len(n: int) -> int:
    """l_w(1)=1 ; l_w(n)=1+floor(log2 n)+l_w(floor(log2 n)) (paper Sec. 3.1)."""
    assert n >= 1
    if n == 1:
        return 1
    k = floor_log2(n)
    return 1 + k + elias_omega_len(k)

def escrow_alloc(B0: int, Phi0: int, d: int) -> int:
    return (B0 * d) // Phi0

def slot_royalty(gamma_bps: int, E_net: int, x: int, delta_tr: int) -> int:
    return (gamma_bps * E_net * x) // (10000 * delta_tr)

# ------------------------------------------------------------------ BLC terms
@dataclass(frozen=True)
class Var:
    idx: int
@dataclass(frozen=True)
class Lam:
    body: object
@dataclass(frozen=True)
class App:
    fn: object
    arg: object

def encode_blc(t) -> str:
    out: List[str] = []
    def go(u):
        if isinstance(u, Lam):
            out.append("00"); go(u.body)
        elif isinstance(u, App):
            out.append("01"); go(u.fn); go(u.arg)
        else:
            out.append("1" * (u.idx + 1) + "0")
    go(t)
    return "".join(out)

def parse_blc(bits: str):
    def go(p):
        if bits.startswith("00", p):
            b, q = go(p + 2); return Lam(b), q
        if bits.startswith("01", p):
            f, q = go(p + 2); a, r = go(q); return App(f, a), r
        n = 0
        while p < len(bits) and bits[p] == "1":
            n += 1; p += 1
        if n == 0 or p >= len(bits) or bits[p] != "0":
            raise ValueError("malformed BLC")
        return Var(n - 1), p + 1
    t, end = go(0)
    if end != len(bits):
        raise ValueError("trailing bits")
    return t

# ------------------------------------------- named-variable builder -> de Bruijn
@dataclass(frozen=True)
class NV:
    name: str
@dataclass(frozen=True)
class NL:
    name: str
    body: object
@dataclass(frozen=True)
class NA:
    fn: object
    arg: object

def V(n):
    return NV(n)
def L(*args):
    *names, body = args
    for n in reversed(names):
        body = NL(n, body)
    return body
def A(f, *args):
    for a in args:
        f = NA(f, a)
    return f

def to_db(t, ctx: Tuple[str, ...] = ()):
    if isinstance(t, NV):
        if t.name not in ctx:
            raise NameError(f"free variable {t.name}")
        return Var(ctx.index(t.name))          # ctx[0] = innermost binder
    if isinstance(t, NL):
        return Lam(to_db(t.body, (t.name,) + ctx))
    return App(to_db(t.fn, ctx), to_db(t.arg, ctx))

# ---------------------------------------------------- Krivine abstract machine
class EvalFallback(Exception):
    """Evaluation yields no valid b_k-bit output -> canonical fallback y_hat = 0^{b_k} applies."""
class StepCeilingExceeded(EvalFallback, RuntimeError):
    pass
class NonBitOutput(EvalFallback, AssertionError):
    pass

# env is a persistent linked list: None | (Closure, parent)
class Closure:
    __slots__ = ("term", "env")
    def __init__(self, term, env):
        self.term = term; self.env = env

def kam_whnf(clo: Closure, budget: int) -> Tuple[Closure, int]:
    """Call-by-name Krivine machine. One step per App-push, beta-pop, Var lookup."""
    stack: List[Closure] = []
    term, env = clo.term, clo.env
    steps = 0
    while True:
        if isinstance(term, App):
            if steps >= budget:                      # a (budget+1)-th step would be needed
                raise StepCeilingExceeded("KAM step ceiling exceeded")
            steps += 1
            stack.append(Closure(term.arg, env))
            term = term.fn
        elif isinstance(term, Lam):
            if not stack:
                return Closure(term, env), steps
            if steps >= budget:
                raise StepCeilingExceeded("KAM step ceiling exceeded")
            steps += 1
            env = (stack.pop(), env)
            term = term.body
        elif isinstance(term, Mark):
            if stack:
                raise NonBitOutput("decoder marker applied to arguments")
            return Closure(term, env), steps
        else:  # Var
            if steps >= budget:
                raise StepCeilingExceeded("KAM step ceiling exceeded")
            steps += 1
            try:
                e = env
                for _ in range(term.idx):
                    e = e[1]
                term, env = e[0].term, e[0].env
            except TypeError:                        # open term: unbound de Bruijn index
                raise NonBitOutput("unbound variable (open term)")

# ------------------------------------------------ Scott-encoded bit lists (LSB first)
@dataclass(frozen=True)
class Mark:
    """Opaque decoder marker (not a lambda term). A bit b is a term with  b MK0 MK1 ->* MK0 (bit 0) or MK1 (bit 1);
    MKEND is passed as the 'nil' argument when probing the head of a list, so end-of-list is detected exactly."""
    k: int
MK0, MK1, MKEND = Mark(0), Mark(1), Mark(2)
SEL_HEAD = Lam(Lam(Var(1)))         # \h.\t.h
SEL_TAIL = Lam(Lam(Var(0)))         # \h.\t.t

def _bit(b): return Lam(Lam(Var(1 if b == 0 else 0)))   # B0=\a.\b.a  B1=\a.\b.b
def scott_list(bits_lsb: List[int]):
    t = Lam(Lam(Var(0)))                                  # nil = \c.\n.n
    for b in reversed(bits_lsb):                          # cons h t = \c.\n.c h t
        t = Lam(Lam(App(App(Var(1), _bit(b)), t)))        # h,t closed => no shifting needed
    return t

def decode_bits(clo: Closure, width: int, budget: int) -> Tuple[int, int]:
    """Lazily read `width` bits (LSB first) from a Scott list closure; return (value, steps)."""
    total, val = 0, 0
    cur = clo
    for i in range(width):
        head = Closure(App(App(cur.term, SEL_HEAD), MKEND), cur.env)
        hb, s = kam_whnf(head, budget - total); total += s
        if isinstance(hb.term, Mark):
            raise NonBitOutput(f"list too short: ended at element {i} of {width}")
        probe = Closure(App(App(hb.term, MK0), MK1), hb.env)
        r, s = kam_whnf(probe, budget - total); total += s
        if isinstance(r.term, Mark) and r.term.k in (0, 1): bit = r.term.k
        else: raise NonBitOutput(f"decode failure at bit {i}: element is not a Scott bit")
        val |= bit << i
        tail = Closure(App(App(cur.term, SEL_TAIL), MKEND), cur.env)
        cur, s = kam_whnf(tail, budget - total); total += s
    return val, total

def run_program_total(prog, args: List[object], j: int, width: int = 16,
                     delta: int = T_MAX) -> Tuple[int, int, bool]:
    """Canonical totalized evaluation (paper Sec. 3.1(ii)); returns (y_hat, steps, ok).
    Per-record steps = WHNF steps + decoding steps, and must be <= delta (the declared ceiling, delta <= T_MAX).
    On ceiling excess / non-bit output / open term: (0, delta, False)  [y_hat = 0^{b_k}; a fallback record
    is charged the full declared ceiling delta -- the paper does not specify a step count for it]."""
    if not (1 <= delta <= T_MAX):
        raise ValueError("declared step ceiling must satisfy 1 <= delta <= T_MAX")
    try:
        t = prog
        for a in args:
            t = App(t, a)
        t = App(t, scott_list([(j >> i) & 1 for i in range(width)]))
        w, s = kam_whnf(Closure(t, None), delta)
        v, s2 = decode_bits(w, width, delta - s)
        return v, s + s2, True
    except EvalFallback:
        return 0, delta, False

def run_bits_total(bits: str, j: int, width: int = 16, delta: int = T_MAX) -> Tuple[int, int, bool]:
    """Totalized evaluation over ARBITRARY bit-strings: unparseable strings also give y_hat = 0^{b_k}."""
    try:
        prog = parse_blc(bits)
    except (ValueError, RecursionError):
        return 0, delta, False
    return run_program_total(prog, [], j, width, delta)

def run_program(prog, args: List[object], j: int, width: int = 16, delta: int = T_MAX) -> Tuple[int, int]:
    """(y_hat, steps) of the totalized evaluation (see run_program_total)."""
    v, s, _ = run_program_total(prog, args, j, width, delta)
    return v, s


# ------------------------------------------------------------- size optimizer
# Semantics-preserving size optimizer for named lambda terms (call-by-name safe).
#   1. beta-reduce one redex at a time (inlines lets / helpers) if the BLC encoding shrinks
#   2. eta-reduce  \x. f x -> f  (x not free in f)
#   3. hoist repeated CLOSED subterms into a shared top-level binding if it shrinks
import itertools

_c = itertools.count()
def _fresh(n): return n.split('#')[0] + '#' + str(next(_c))

def alpha(t, env=None):
    env = env or {}
    if isinstance(t, NV): return NV(env.get(t.name, t.name))
    if isinstance(t, NL):
        nn = _fresh(t.name); return NL(nn, alpha(t.body, {**env, t.name: nn}))
    return NA(alpha(t.fn, env), alpha(t.arg, env))

def fv(t):
    if isinstance(t, NV): return {t.name}
    if isinstance(t, NL): return fv(t.body) - {t.name}
    return fv(t.fn) | fv(t.arg)

def subst(t, name, val):
    if isinstance(t, NV): return alpha(val) if t.name == name else t
    if isinstance(t, NL): return NL(t.name, subst(t.body, name, val))
    return NA(subst(t.fn, name, val), subst(t.arg, name, val))

def bits(t): return len(encode_blc(to_db(t)))

def betas(t):
    """yield every term obtained by reducing exactly one beta-redex of t."""
    if isinstance(t, NA):
        if isinstance(t.fn, NL):
            yield subst(t.fn.body, t.fn.name, t.arg)
        for f in betas(t.fn): yield NA(f, t.arg)
        for a in betas(t.arg): yield NA(t.fn, a)
    elif isinstance(t, NL):
        for b in betas(t.body): yield NL(t.name, b)

def eta(t):
    if isinstance(t, NL):
        b = eta(t.body)
        if isinstance(b, NA) and isinstance(b.arg, NV) and b.arg.name == t.name and t.name not in fv(b.fn):
            return b.fn
        return NL(t.name, b)
    if isinstance(t, NA): return NA(eta(t.fn), eta(t.arg))
    return t

def closed_subterms(t, out):
    if not fv(t): out.append(t)
    if isinstance(t, NL): closed_subterms(t.body, out)
    elif isinstance(t, NA): closed_subterms(t.fn, out); closed_subterms(t.arg, out)

def key(t): return encode_blc(to_db(t))

def replace_closed(t, k, name):
    if not fv(t) and key(t) == k: return NV(name)
    if isinstance(t, NL): return NL(t.name, replace_closed(t.body, k, name))
    if isinstance(t, NA): return NA(replace_closed(t.fn, k, name), replace_closed(t.arg, k, name))
    return t

def hoists(t):
    subs = []; closed_subterms(t, subs)
    groups = {}
    for s in subs:
        if bits(s) >= 5: groups.setdefault(key(s), []).append(s)
    for k, g in groups.items():
        if len(g) >= 2:
            h = _fresh("hoist")
            yield A(NL(h, replace_closed(t, k, h)), alpha(g[0]))

def optimize(t, verbose=False, max_rounds=200):
    t = alpha(t); best = bits(t)
    for rnd in range(max_rounds):
        improved = False
        e = eta(t)
        if bits(e) < best: t, best, improved = e, bits(e), True
        cands = list(betas(t)) + list(hoists(t))
        scored = [(bits(c), i, c) for i, c in enumerate(cands)]
        scored.sort(key=lambda x: (x[0], x[1]))
        if scored and scored[0][0] < best:
            best, _, t = scored[0]; improved = True
        if verbose: print(f"round {rnd}: {best} bits")
        if not improved: break
    return t, best

def optimize_beam(t, width=8, patience=6, max_rounds=80):
    """Beam search over {beta, hoist, eta}; allows temporarily larger terms."""
    t = alpha(eta(alpha(t)))
    beam = [(bits(t), 0, t)]; best = beam[0]; stale = 0; seen = {key(t)}
    for rnd in range(max_rounds):
        cand = []
        for b, _, s in beam:
            for c in itertools.chain(betas(s), hoists(s)):
                c = eta(c); k = key(c)
                if k in seen: continue
                seen.add(k); cand.append((bits(c), len(cand), c))
        if not cand: break
        cand.sort(key=lambda x: (x[0], x[1]))
        beam = cand[:width]
        if beam[0][0] < best[0]: best = beam[0]; stale = 0
        else:
            stale += 1
            if stale >= patience: break
    return best[2], best[0]


# ------------------------------------------------------------- BLC programs
# All programs are written with named variables, then SIZE-OPTIMIZED automatically
# (beta-inlining, eta-reduction, hoisting of repeated closed subterms; beam search).
# Every optimized program is re-verified against its law, so optimization is semantics-checked.
def B0(): return L("a", "b", V("a"))          # bit 0 = \a.\b.a
def B1(): return L("a", "b", V("b"))          # bit 1 = \a.\b.b   (also used as nil)
def YC(): return L("f", A(L("x", A(V("f"), A(V("x"), V("x")))), L("x", A(V("f"), A(V("x"), V("x"))))))
def CONS(h, t): return A(L("h", "t", "c", "n", A(V("c"), V("h"), V("t"))), h, t)

def named_adder():
    """Ripple-carry adder on LSB-first Scott lists, parameter order (xs, ys, c); stops when xs ends."""
    xor = L("p", "q", A(V("p"), V("q"), A(V("q"), B1(), B0())))
    s = A(xor, A(xor, V("x"), V("y")), V("c"))
    m = A(V("x"), A(V("y"), B0(), V("c")), A(V("y"), V("c"), B1()))
    step = CONS(s, A(V("r"), V("xt"), V("yt"), m))
    return A(YC(), L("r", "xs", "ys", "c", A(V("xs"), L("x", "xt", A(V("ys"), L("y", "yt", step), B1())), B1())))

def named_bench1():
    """w1(x) = x + (cons 1 (x + 3))  =  3x + 7  (mod 2^16, truncated by the 16-bit input length)."""
    zeros = A(YC(), L("z", CONS(B0(), V("z"))))
    k3 = CONS(B1(), CONS(B1(), zeros))
    call = lambda xs, ys, c: A(V("add"), xs, ys, c)
    inner = CONS(B1(), call(V("x"), k3, B0()))
    return L("x", A(L("add", call(V("x"), inner, B0())), named_adder()))

def named_axiom_vs():
    """Axiom v_s : bitwise NOT over a Scott bit list."""
    notb = L("p", A(V("p"), B1(), B0()))
    return A(YC(), L("r", "xs", A(V("xs"), L("h", "t", CONS(A(notb, V("h")), A(V("r"), V("t")))), B1())))

def named_bench2_wrapper():
    """w2 = \\v.\\x. v x   (y_j = NOT16(j): the recipe is the axiom itself)"""
    return L("v", "x", A(V("v"), V("x")))

def named_bench3_wrapper():
    """w3 = \\v.\\x. cons 1 (tail (v x))   (y_j = NOT16(j) with LSB forced to 1)"""
    return L("v", "x", CONS(B1(), A(A(V("v"), V("x")), L("h", "t", V("t")), B1())))

_OPT_CACHE: Dict[str, object] = {}
def compiled(name, named_fn):
    """Optimize a named program (beam search) and compile to de Bruijn; memoized."""
    if name not in _OPT_CACHE:
        t, _ = optimize_beam(named_fn(), width=10, patience=5)
        _OPT_CACHE[name] = to_db(t)
    return _OPT_CACHE[name]

def prog_bench1():          return compiled("w1", named_bench1)
def prog_axiom_vs():        return compiled("vs", named_axiom_vs)
def prog_bench2_wrapper():  return compiled("w2", named_bench2_wrapper)
def prog_bench3_wrapper():  return compiled("w3", named_bench3_wrapper)

# ------------------------------------------------------------- Counted MST length
C_HDR = 33
def mst_residual_len(res: List[int], b_k: int = 16) -> Dict[str, int]:
    """Sparse and dense residual length (paper Sec. 3.1); returns all three numbers."""
    idxs = [j for j, r in enumerate(res) if r != 0]
    k = len(idxs)
    gaps = [idxs[0] + 1] + [idxs[m] - idxs[m - 1] for m in range(1, k)] if k else []
    sparse = elias_omega_len(k + 1) + C_HDR + sum(elias_omega_len(g) + b_k for g in gaps)
    dense = C_HDR + sum(elias_omega_len(r + 1) for r in res)      # biject = identity (unsigned)
    return {"k_err": k, "sparse": sparse, "dense": dense, "L_res": min(sparse, dense),
            "header": elias_omega_len(k + 1) + C_HDR}

# ------------------------------------------------------------- data generation
def make_data(law, n_k: int, k_err: int, seed: int, b_k: int = 16):
    """y_j = law(j) XOR noise_j, noise nonzero on exactly k_err seeded positions."""
    rng = random.Random(seed)
    pos = set(rng.sample(range(n_k), k_err))
    y, noise = [], []
    for j in range(n_k):
        e = rng.randrange(1, 1 << b_k) if j in pos else 0
        noise.append(e); y.append(law(j) ^ e)
    return y, noise

def measure(prog, args, data, b_k=16):
    """Run the program on EVERY record; return (max_steps, residual vector).
    Asserts that the residual is exactly the injected noise (=> program computes its law)."""
    y, noise = data
    max_steps, argmax, res = 0, 0, []
    for j, yj in enumerate(y):
        out, s, ok = run_program_total(prog, args, j, b_k)
        assert ok, f"record {j}: evaluation fell back to 0^b_k"
        if s > max_steps: max_steps, argmax = s, j
        res.append(yj ^ out)
    assert res == noise, "program does not compute its law on all records"
    # declared-ceiling semantics: delta = measured max must suffice; delta = max-1 must trigger the fallback
    assert run_program_total(prog, args, argmax, b_k, max_steps)[2], "delta = max steps must be accepted"
    assert not run_program_total(prog, args, argmax, b_k, max_steps - 1)[2], "delta = max steps - 1 must fall back"
    return max_steps, res

# ------------------------------------------------------------- experiment
PAPER = {  # numbers printed in Table 5 / Section 8.1 of the current manuscript (v14)
 1: dict(code=382, L_res=34,   Phi=416,  Delta=15968, steps=7457, E=9746),
 2: dict(code=109, L_res=1290, Phi=1399, Delta=14985, steps=904,  E=9146),
 3: dict(code=72,  L_res=750,  Phi=822,  Delta=15562, steps=911,  E=9498),
}
PAPER_B3_EXTRA = dict(E_net=9024, R=9)       # E_net after 5% burn and R(81) of Benchmark 3
LAW1 = lambda j: (3 * j + 7) & 0xFFFF
LAW2 = lambda j: (~j) & 0xFFFF
LAW3 = lambda j: (((~j) & 0xFFFF) | 1)

def selftest():
    assert [elias_omega_len(i) for i in (1, 2, 3, 4, 29, 52, 1420)] == [1, 3, 3, 6, 11, 12, 18]
    assert encode_blc(Lam(Var(0))) == "0010"
    assert encode_blc(Lam(Lam(Lam(App(Var(2), App(Var(1), Var(0))))))) == "0000000111100111010"
    for p in (prog_bench1(), prog_axiom_vs(), prog_bench2_wrapper(), prog_bench3_wrapper()):
        assert parse_blc(encode_blc(p)) == p
    p1, vs, w2, w3 = prog_bench1(), prog_axiom_vs(), prog_bench2_wrapper(), prog_bench3_wrapper()
    for j in (0, 1, 2, 7, 255, 1023, 5000, 65535):
        assert run_program(p1, [], j)[0] == LAW1(j), j
        assert run_program(w2, [vs], j)[0] == LAW2(j), j
        assert run_program(w3, [vs], j)[0] == LAW3(j), j
    # --- canonical totalized fallback (Sec. 3.1(ii)); all must give y_hat = 0^{b_k}, ok = False
    nil_t = Lam(Lam(Var(0)))
    omega = Lam(App(Var(0), Var(0)))
    cases = {
        "divergent (delta=10^4)":      (run_program_total(Lam(App(omega, omega)), [], 5, 16, 10_000), 10_000),
        "divergent (delta=T_MAX)":     (run_program_total(Lam(App(omega, omega)), [], 5), T_MAX),
        "empty output list":           (run_program_total(Lam(nil_t), [], 5), T_MAX),
        "partial list (2 of 16 bits)": (run_program_total(Lam(scott_list([1, 1])), [], 5), T_MAX),
        "non-bit head":                (run_program_total(Lam(Lam(Lam(App(App(Var(1), Lam(Lam(Lam(Var(0))))), nil_t)))), [], 5), T_MAX),
        "open term (unbound var)":     (run_program_total(Var(5), [], 5), T_MAX),
        "bit-string 1111110 (open)":   (run_bits_total("1111110", 5), T_MAX),
        "unparseable bit-strings":     (tuple(run_bits_total(b, 5) for b in ("", "0", "01", "1", "0101")), None),
    }
    for name, (res, dl) in cases.items():
        rs = res if name == "unparseable bit-strings" else (res,)
        for v, st, ok in rs:
            assert (v, ok) == (0, False), (name, v, st, ok)
            if dl is not None: assert st == dl, (name, st)
    # declared ceiling: steps == delta is accepted, steps == delta + 1 falls back ("exceeds delta" <=> steps > delta)
    v, st, ok = run_program_total(p1, [], 1023)
    assert ok and v == LAW1(1023)
    assert run_program_total(p1, [], 1023, 16, st) == (v, st, True)
    assert run_program_total(p1, [], 1023, 16, st - 1) == (0, st - 1, False)
    for bad in (0, T_MAX + 1):
        try: run_program_total(p1, [], 1, 16, bad); raise SystemExit("delta range not enforced")
        except ValueError: pass
    # --- behavioural bit definition: any term that reduces to its 1st/2nd argument is bit 0/1; others are rejected
    bit0_redex = Lam(Lam(App(Lam(Var(0)), Var(1))))             # \a.\b.(\x.x) a  ->  a  : behaves as bit 0
    cell = lambda h, t: Lam(Lam(App(App(Var(1), h), t)))
    lst = Lam(Lam(Var(0)))
    for _ in range(16): lst = cell(bit0_redex, lst)
    assert run_program_total(Lam(lst), [], 5)[0::2] == (0, True)
    bad = cell(Lam(Lam(Lam(Var(0)))), Lam(Lam(Var(0))))           # head \a.\b.\c.c is not a bit
    assert run_program_total(Lam(bad), [], 5)[0::2] == (0, False)
    print("selftest OK")

def run(n_k=1024, b_k=16, B0=10000, verbose_bits=True):
    Phi0 = n_k * b_k
    out = {}
    t0 = time.time()
    # ---- Benchmark 1
    w1 = prog_bench1(); w1_bits = encode_blc(w1)
    y1 = make_data(LAW1, n_k, 0, 1)
    st1, r1 = measure(w1, [], y1, b_k)
    m1 = mst_residual_len(r1, b_k)
    ref1, ld1 = 2, elias_omega_len(st1)
    code1 = len(w1_bits) + ref1 + ld1
    Phi1 = code1 + m1["L_res"]
    out[1] = dict(code=code1, L_res=m1["L_res"], Phi=Phi1, Delta=Phi0 - Phi1, steps=st1,
                  E=escrow_alloc(B0, Phi0, Phi0 - Phi1), detail=f"|w1|={len(w1_bits)} l_ref={ref1} l_delta={ld1} k_err={m1['k_err']}")
    # ---- axiom
    vs = prog_axiom_vs(); vs_bits = encode_blc(vs)
    # ---- Benchmark 2
    w2 = prog_bench2_wrapper(); w2_bits = encode_blc(w2)
    y2 = make_data(LAW2, n_k, 51, 2)
    st2, r2 = measure(w2, [vs], y2, b_k)
    m2 = mst_residual_len(r2, b_k)
    ref2, ld2 = 3, elias_omega_len(st2)
    code2 = len(w2_bits) + ref2 + ld2 + len(vs_bits)
    Phi2 = code2 + m2["L_res"]
    out[2] = dict(code=code2, L_res=m2["L_res"], Phi=Phi2, Delta=Phi0 - Phi2, steps=st2,
                  E=escrow_alloc(B0, Phi0, Phi0 - Phi2),
                  detail=f"|w2|={len(w2_bits)} l_ref={ref2} l_delta={ld2} L_axiom=|p_s|={len(vs_bits)} k_err={m2['k_err']} (sparse={m2['sparse']}, dense={m2['dense']})")
    # ---- Benchmark 3 (axiom fully amortized, l_E = 4)
    w3 = prog_bench3_wrapper(); w3_bits = encode_blc(w3)
    y3 = make_data(LAW3, n_k, 28, 3)
    st3, r3 = measure(w3, [vs], y3, b_k)
    m3 = mst_residual_len(r3, b_k)
    ref3, ld3, lE = 3, elias_omega_len(st3), 4
    code3 = len(w3_bits) + ref3 + ld3 + lE
    Phi3 = code3 + m3["L_res"]
    D3 = Phi0 - Phi3
    E3 = escrow_alloc(B0, Phi0, D3); En3 = E3 - (500 * E3) // 10000
    saved = len(vs_bits) - lE
    R3 = slot_royalty(2000, En3, saved, D3)
    out[3] = dict(code=code3, L_res=m3["L_res"], Phi=Phi3, Delta=D3, steps=st3, E=E3, E_net=En3, R=R3,
                  detail=f"|w3|={len(w3_bits)} l_ref={ref3} l_delta={ld3} l_E={lE} k_err={m3['k_err']}; E_net={En3} R({saved})={R3}")
    out["bits"] = dict(w1=w1_bits, vs=vs_bits, w2=w2_bits, w3=w3_bits)
    out["secs"] = time.time() - t0
    return out

def report(out, n_k=1024, b_k=16):
    Phi0 = n_k * b_k
    print(f"n_k={n_k} b_k={b_k} Phi0={Phi0}  (all outputs verified: y_j XOR out_j = injected noise only)\n")
    names = {1: "B1 linear congruence", 2: "B2 bit-inversion + 5% outliers", 3: "B3 amortized composite"}
    for k in (1, 2, 3):
        m, p = out[k], PAPER[k]
        print(f"[{names[k]}]  {m['detail']}")
        print(f"   {'':12s}{'code':>7}{'L_res':>8}{'Phi':>8}{'Delta':>8}{'steps':>8}{'E_tr':>8}")
        print(f"   {'measured':12s}{m['code']:>7}{m['L_res']:>8}{m['Phi']:>8}{m['Delta']:>8}{m['steps']:>8}{m['E']:>8}")
        print(f"   {'paper Tbl5':12s}{p['code']:>7}{p['L_res']:>8}{p['Phi']:>8}{p['Delta']:>8}{p['steps']:>8}{p['E']:>8}\n")
    cells = [(k, f) for k in (1, 2, 3) for f in PAPER[k]]
    okc = all(out[k][f] == PAPER[k][f] for k, f in cells) and all(out[3][f] == v for f, v in PAPER_B3_EXTRA.items())
    print(f"Table 5 reproduction vs manuscript ({len(cells)} cells + E_net, R(81)): {'PASS' if okc else 'FAIL'}\n")
    print("BLC bitstrings (for the appendix):")
    for k, v in out["bits"].items():
        print(f"  {k} ({len(v)} bits): {v}")
    print(f"\nwall time: {out['secs']:.1f}s")


# ============================================================= Experiment 3 / Benchmark 4: T6
# Syntactic Reduction Attribution (paper Def. T6): accept  T6(v_i, v_s, q, steps)  iff
#   (1) t_seq(v_s) < t_seq(v_i); (2) origin(v_s) = v_s; (3) U(q(p_s)) =_{beta eta} p_i within `steps` <= T_max;
#   (4) L_red_new = |p_i| (-) (|q| + l_w(idx(v_s))) satisfies the Case-A / Case-B overwrite rule.
# Condition (3) is decided here by a bounded Boehm-tree (coinductive) beta-eta comparison on de Bruijn terms:
# heads are reduced to head-normal form (normal order), eta-aligned, compared, and arguments compared recursively;
# a pair of terms already under comparison counts as equal (greatest fixed point), which makes the check terminate
# on recursive (Y-combinator) axioms whose literal beta-normal form does NOT exist (see literal_nf_attempt).
class FuelExhausted(Exception):
    pass

class Fuel:
    """Verification fuel for the T6 check. Everything the verifier does is charged to ONE budget and the TOTAL
        fuel_total = kam + beta + nodes + work
    is bounded by the submitter-declared ceiling cap (= fuel_max <= T_max):
    kam    : KAM steps needed to evaluate App(q, p_s) to WHNF
    beta   : beta-reductions performed by hnf
    nodes  : node comparisons (one per recursive/queued comparison of two sub-terms)
    work   : AST nodes touched by substitution / eta-shifting / syntactic equality+hashing (term-size cost)
    count_work=False restricts the charge to beta-steps (used only for the literal normal-form attempt)."""
    __slots__ = ("cap", "kam", "beta", "nodes", "work", "count_work")
    def __init__(self, cap, count_work=True):
        self.cap, self.kam, self.beta, self.nodes, self.work, self.count_work = cap, 0, 0, 0, 0, count_work
    @property
    def total(self): return self.kam + self.beta + self.nodes + self.work
    def charge_kam(self, n): self.kam += n; self._check()
    def remaining(self): return self.cap - self.total
    def _check(self):
        if self.total > self.cap: raise FuelExhausted
    def beta_step(self): self.beta += 1; self._check()
    def node(self): self.nodes += 1; self._check()
    def touch(self, n=1):
        if self.count_work: self.work += n; self._check()

def _shift(t, d, c=0, fuel=None):
    if fuel is not None: fuel.touch()
    if isinstance(t, Var): return Var(t.idx + d) if t.idx >= c else t
    if isinstance(t, Lam): return Lam(_shift(t.body, d, c + 1, fuel))
    return App(_shift(t.fn, d, c, fuel), _shift(t.arg, d, c, fuel))

def _subst(t, j, s_, fuel=None):
    """t[j := s_] with the removed binder accounted for (standard de Bruijn beta substitution)."""
    if fuel is not None: fuel.touch()
    if isinstance(t, Var):
        if t.idx == j: return _shift(s_, j, 0, fuel)
        return Var(t.idx - 1) if t.idx > j else t
    if isinstance(t, Lam): return Lam(_subst(t.body, j + 1, s_, fuel))
    return App(_subst(t.fn, j, s_, fuel), _subst(t.arg, j, s_, fuel))

def _spine(t):
    args = []
    while isinstance(t, App):
        args.append(t.arg); t = t.fn
    args.reverse()
    return t, args

def _apps(f, args):
    for a in args: f = App(f, a)
    return f

def _size(t, limit):
    """Iterative node count of t, stopping once it exceeds `limit` (so a huge term can never stall the verifier)."""
    n, stack = 0, [t]
    while stack:
        u = stack.pop(); n += 1
        if n > limit: return n
        if isinstance(u, Lam): stack.append(u.body)
        elif isinstance(u, App): stack.append(u.fn); stack.append(u.arg)
    return n

def hnf(t, fuel):
    """Normal-order head normal form: (n binders, head Var, args). Each beta step is charged to `fuel`."""
    n = 0
    while True:
        while isinstance(t, Lam):
            t = t.body; n += 1
        h, args = _spine(t)
        if isinstance(h, Lam):
            fuel.beta_step()
            t = _apps(_subst(h.body, 0, args[0], fuel), args[1:])
            continue
        return n, h, args

def bt_equiv(a, b, fuel, seen):
    """Bounded beta-eta (Boehm-tree) equivalence of two possibly open terms, ITERATIVE (explicit stack, no Python
    recursion), pre-order DFS identical to the recursive formulation. Every node comparison and every AST node touched
    is charged to `fuel`; exhausting T_max raises FuelExhausted (=> 'not established', never 'equal')."""
    stack = [(a, b)]
    while stack:
        x, y = stack.pop()
        fuel.node()
        rem = fuel.remaining() + 1
        fuel.touch(_size(x, rem) + _size(y, rem))        # cost of the structural equality / hashing below
        if x == y: continue
        key = (x, y)
        if key in seen: continue                         # coinductive hypothesis (cycle closes)
        seen.add(key)
        n, h1, a1 = hnf(x, fuel); m, h2, a2 = hnf(y, fuel)
        if n < m:                                        # eta-align: add m-n binders to the shorter side
            d = m - n; h1 = Var(h1.idx + d); a1 = [_shift(u, d, 0, fuel) for u in a1] + [Var(i) for i in range(d - 1, -1, -1)]
        elif m < n:
            d = n - m; h2 = Var(h2.idx + d); a2 = [_shift(u, d, 0, fuel) for u in a2] + [Var(i) for i in range(d - 1, -1, -1)]
        if h1 != h2 or len(a1) != len(a2): return False
        stack.extend(reversed(list(zip(a1, a2))))        # first argument pair is processed first (same order as recursion)
    return True

def beta_normal_form(t, fuel):
    n, h, args = hnf(t, fuel)
    body = h
    for a in args: body = App(body, beta_normal_form(a, fuel))
    for _ in range(n): body = Lam(body)
    return body

def literal_nf_attempt(t, fuel_units=20000):
    """Try the paper's literal condition (3): full beta-normal form. Returns (kind, detail, beta-steps used)."""
    old = sys.getrecursionlimit(); sys.setrecursionlimit(max(old, 60000))
    fuel = Fuel(fuel_units, count_work=False)
    try:
        nf = beta_normal_form(t, fuel)
        return "NF", len(encode_blc(nf)), fuel.beta
    except FuelExhausted:
        return "NONE", "fuel exhausted", fuel_units
    except RecursionError:
        return "NONE", "unbounded nesting (infinite unfolding)", fuel.beta
    finally:
        sys.setrecursionlimit(old)

def monus(a, b): return a - b if a > b else 0

def t6_check(p_s, q, p_i, fuel_max=T_MAX):
    """Decide condition (3) under ONE declared budget fuel_max (<= T_max):  kam + beta + nodes + work <= fuel_max.
    Returns (equal|None, KAM steps of q(p_s) -> WHNF, Fuel, status).
    equal = True/False when decided within the budget; None (=> T6 NOT established, transaction rejected) on fuel exhaustion
    (including KAM steps) or on any Python resource limit (RecursionError/MemoryError), so a hostile clone can neither crash nor
    stall the verifier."""
    fuel = Fuel(fuel_max)
    try:
        _, kam_steps = kam_whnf(Closure(App(q, p_s), None), fuel_max)
        fuel.charge_kam(kam_steps)
        eq = bt_equiv(App(q, p_s), p_i, fuel, set())
        return eq, kam_steps, fuel, ("equal" if eq else "not-equal")
    except (FuelExhausted, EvalFallback):
        fuel.kam = max(fuel.kam, 0)
        return None, fuel.kam, fuel, "fuel-exhausted"
    except (RecursionError, MemoryError):
        return None, fuel.kam, fuel, "resource-limit"

def fuel_boundary(p_s, q, p_i):
    """Exact acceptance boundary of the declared ceiling: fuel_max = fuel_total is accepted, fuel_max = fuel_total - 1 is rejected."""
    eq, _, f, st = t6_check(p_s, q, p_i)
    assert eq is True and st == "equal"
    need = f.total
    ok = t6_check(p_s, q, p_i, need); no = t6_check(p_s, q, p_i, need - 1)
    assert ok[0] is True and ok[3] == "equal", "fuel_max = fuel_total must be accepted"
    assert no[0] is None and no[3] == "fuel-exhausted", "fuel_max = fuel_total - 1 must be rejected"
    return need

def t6_accept(S, v_i, v_s, L_new):
    """Conditions (1), (2), (4) of T6 on the abstract state S = {seq, origin, L_red}; mutates S on acceptance."""
    if not S["seq"][v_s] < S["seq"][v_i]: return False
    if S["origin"][v_s] != v_s: return False
    o = S["origin"][v_i]
    if S["origin"][o] == o:                           # Case A
        ok = L_new > S["L_red"][v_i] or (L_new == S["L_red"][v_i] >= 1 and S["seq"][v_s] < S["seq"][o])
    else:                                             # Case B (orphaned origin)
        ok = L_new >= 1
    if ok:
        S["origin"][v_i] = v_s; S["L_red"][v_i] = L_new
    return ok

def stage2_redirect(a, L_red, R_cap):
    """Eq. stage2_redirect for one derivative: returns (x_{i->s}, x_{i->i}, remaining R_cap)."""
    x_is = min(a, min(L_red, R_cap))
    return x_is, a - x_is, R_cap - x_is

def burn_for_amortization(delta_bits, Phi, B, eps=500):
    """Smallest C with  floor(10000*C*Phi/((10000-eps)*B)) >= delta_bits  (inverse of Eq. delta_amort), asserted."""
    C = cdiv_int((10000 - eps) * B * delta_bits, 10000 * Phi)
    f = lambda c: 10000 * c * Phi // ((10000 - eps) * B)
    assert f(C) >= delta_bits and (C == 0 or f(C - 1) < delta_bits)
    return C

def cdiv_int(a, b): return -(-a // b)

def build_clones(p_s, w3):
    ident = Lam(Var(0))
    eta_p = Lam(App(p_s, Var(0)))                     # \y. p_s y   (p_s is closed: no shifting needed)
    p_iA = Lam(App(App(ident, eta_p), Var(0)))        # \z. ((\x.x) (\y. p_s y)) z   : identity-application + eta padding
    p_iB = _subst(w3.body, 0, p_s)                    # beta-form of (w3 p_s)         : \x. cons 1 (tail (p_s x))
    return ident, p_iA, w3, p_iB                      # adapters: q_A = \x.x ; q_B = w3  (eta-reduced form of \s. w3 s)

def recipe_phi(wrapper, p_i, law, k_err, seed, n_k, b_k, delta_amort, lE=4, ref=3):
    """Phi_local of a recipe `wrapper` that cites the clone axiom p_i with exemption `delta_amort` bits. The recipe is
    executed on EVERY record of the dataset (law + k_err seeded outliers, verified by measure()); L_res comes from the real
    residual vector; l_delta from the measured recipe-level maximum step count."""
    mx, res = measure(wrapper, [p_i], make_data(law, n_k, k_err, seed), b_k)
    m = mst_residual_len(res, b_k)
    ld = elias_omega_len(mx)
    code = len(encode_blc(wrapper)) + ref + ld
    unam = len(encode_blc(p_i)) - delta_amort
    return dict(wrap=len(encode_blc(wrapper)), steps=mx, ld=ld, code=code, unam=unam, lE=lE,
                L_res=m["L_res"], Phi=code + unam + lE + m["L_res"])

def fmt_fuel(f):
    tot = f"total {f.total} <= fuel_max" if f.total <= f.cap else f"fuel_max = {f.cap} EXHAUSTED"
    return f"kam={f.kam}, beta={f.beta}, nodes={f.nodes}, work={f.work} ({tot})"

def run_benchmark4(out, b_k=16, n_k=1024, lE_clone=4):
    p_s, w3 = prog_axiom_vs(), prog_bench3_wrapper()
    q_A, p_iA, q_B, p_iB = build_clones(p_s, w3)
    ps_bits = len(encode_blc(p_s)); idx_len = elias_omega_len(1)          # idx(v_s) = 1  => 1 bit
    d3, E_net, Phi0 = out[3]["Delta"], out[3]["E_net"], n_k * b_k          # Benchmark-3 tranche (counterfactual)
    saved_s = ps_bits - 4                                                  # Saved^(E)(v_s, D_3) = 85 - l_E(v_s)=81
    print("\n" + "=" * 100)
    print("BENCHMARK 4 (Experiment 3): T6 Syntactic Reduction & Stage-2 Royalty Redirection")
    print("=" * 100)
    print(f"root axiom v_s: |p_s| = {ps_bits} bits, idx(v_s) = 1 -> l_w(idx) = {idx_len} bit;  tranche = Benchmark 3 "
          f"(Delta_tr = {d3}, E_net = {E_net}, gamma = 2000 bps)")
    # literal condition (3) on the root axiom itself
    kind, why, used = literal_nf_attempt(p_s)
    kind_id, *_ = literal_nf_attempt(Lam(Var(0)), 100)
    print(f"literal beta-normal form of p_s : {kind} ({why}; {used} beta-steps)   [identity combinator: {kind_id}]")
    assert kind == "NONE" and kind_id == "NF"
    state = {"seq": {"v_s": 1, "A": 2, "B": 3}, "origin": {"v_s": "v_s", "A": "A", "B": "B"},
             "L_red": {"v_s": 0, "A": 0, "B": 0}}
    expect = {"A": dict(pi=103, q=4, L=98, a=99, x_is=81, x_ii=18, R_is=9, R_ii=2, beta=8, total=747),
              "B": dict(pi=126, q=48, L=77, a=122, x_is=77, x_ii=45, R_is=8, R_ii=5, beta=1, total=263)}
    rows = []
    for name, q, p_i, law in (("A", q_A, p_iA, LAW2), ("B", q_B, p_iB, LAW3)):
        title = ("Clone A: beta-eta padded clone  p_i = \\z.((\\x.x)(\\y.p_s y)) z ,  q_A = \\x.x" if name == "A"
                 else "Clone B: wrapped derivative clone  p_i = beta-form(w3 p_s) = \\x.cons 1 (tail (p_s x)),  q_B = w3")
        pi_len, q_len = len(encode_blc(p_i)), len(encode_blc(q))
        eq, kam_steps, fuel, status = t6_check(p_s, q, p_i)
        L_red = monus(pi_len, q_len + idx_len)
        # functional drop-in check: the clone computes its law on ALL records
        mx = 0
        for j in range(n_k):
            v, st, ok = run_program_total(p_i, [], j, b_k)
            assert ok and v == law(j), (name, j)
            mx = max(mx, st)
        accepted = eq is True and t6_accept(state, name, "v_s", L_red)
        # Stage 1 / Stage 2 on the Benchmark-3 tranche, clone assumed fully amortized with pointer l_E(v_i)
        a = (pi_len - lE_clone)                                            # Saved^(E)(v_i,D_3) (marginal; S_paid = 0)
        R_cap = saved_s                                                    # Saved^(E)(v_s,D_3) (-) S_paid = 81
        x_is, x_ii, cap_left = stage2_redirect(a, L_red, R_cap)
        R_is = slot_royalty(2000, E_net, x_is, d3); R_ii = slot_royalty(2000, E_net, x_ii, d3)
        R_a = slot_royalty(2000, E_net, a, d3); R_honest = slot_royalty(2000, E_net, saved_s, d3)
        C_min = burn_for_amortization(pi_len, Phi0, 10000)
        print(f"\n[{title}]")
        print(f"  |p_i| = {pi_len} bits   |q| = {q_len} bits   l_w(idx(v_s)) = {idx_len} bit   "
              f"L_red = {pi_len} (-) ({q_len}+{idx_len}) = {L_red} bits")
        print(f"  q(p_s): KAM steps to WHNF = {kam_steps}   check fuel: {fmt_fuel(fuel)}   "
              f"U(q(p_s)) =_beta-eta p_i : {eq} [{status}]")
        print(f"  T6 accepted (cond. 1,2,3 + Case A): {accepted}   -> origin(v_i) = {state['origin'][name]}, "
              f"L_red(v_i) = {state['L_red'][name]}")
        print(f"  drop-in check: clone computes its law on {n_k}/{n_k} records (max {mx} KAM steps)")
        print(f"  Stage 1: a_(i->i) = Saved(v_i) = {pi_len} - l_E({lE_clone}) = {a}      R_cap(v_s) = Saved(v_s) (-) S_paid = {R_cap}")
        print(f"  Stage 2: x_(i->s) = min({a}, {L_red}, {R_cap}) = {x_is}   x_(i->i) = {a} - {x_is} = {x_ii}   (R_cap left {cap_left})")
        print(f"  Royalty: R(x_(i->s)) = R({x_is}) = {R_is} tokens -> owner(v_s)   |   R(x_(i->i)) = R({x_ii}) = {R_ii} token(s) -> clone owner"
              f"   (honest citation of v_s: R({saved_s}) = {R_honest})")
        print(f"  clone economics: burn >= {C_min} tokens needed to amortize {pi_len} bits on D_3 vs retained royalty {R_ii} per citing dataset")
        e = expect[name]
        assert eq is True and accepted and status == "equal"
        assert fuel.beta == e["beta"] and fuel.total == e["total"] and fuel.total <= T_MAX
        assert (pi_len, q_len, L_red, a, x_is, x_ii, R_is, R_ii) == (e["pi"], e["q"], e["L"], e["a"], e["x_is"], e["x_ii"], e["R_is"], e["R_ii"])
        assert x_is + x_ii == a and x_is == min(a, L_red, R_cap) and x_is <= saved_s
        assert R_is + R_ii <= R_a                                          # floor superadditivity (Lemma 3.1 style)
        assert R_is <= R_honest                                            # the clone can never divert royalty away from v_s
        rows.append((name, x_is, R_is))
    assert rows[0][1] == saved_s and rows[0][2] == R_honest == 9           # Clone A: v_s keeps the full R(81) = 9
    # negative controls: a wrong adapter and an unrelated program must NOT verify
    n1, _, f1, st1 = t6_check(p_s, q_B, p_iA); n2, _, f2, st2 = t6_check(p_s, q_A, prog_bench1())
    n3 = t6_accept({"seq": {"v_s": 1, "A": 2}, "origin": {"v_s": "v_s", "A": "A"}, "L_red": {"v_s": 0, "A": 0}}, "A", "v_s", 0)
    print(f"\n[negative controls] wrong adapter (q=w3 vs Clone A): equal = {n1} ({f1.beta} beta-steps, total fuel {f1.total});  "
          f"unrelated program (q=id vs w1): equal = {n2} ({f2.beta} beta-steps, total fuel {f2.total});  "
          f"L_red = 0 rejected by Case A: accepted = {n3}")
    assert n1 is False and n2 is False and n3 is False and (f1.beta, f2.beta) == (6, 21) and (f1.total, f2.total) == (548, 5515)
    needA, needB = fuel_boundary(p_s, q_A, p_iA), fuel_boundary(p_s, q_B, p_iB)
    print("\n[declared-ceiling boundary]  joint metering: kam + beta + nodes + work <= fuel_max (accepted at equality, rejected one unit below)")
    print(f"  Clone A: fuel_max = {needA} -> True [equal];   fuel_max = {needA - 1} -> None [fuel-exhausted]")
    print(f"  Clone B: fuel_max = {needB} -> True [equal];   fuel_max = {needB - 1} -> None [fuel-exhausted]")
    assert (needA, needB) == (747, 263)

    # ------------------------------------------------------------------ (Moderate 1) recipe-level Phi_local of the clones
    id_wrap = prog_bench2_wrapper()                                        # \v.v  (4 bits)
    C_A, C_B, C_85 = (burn_for_amortization(103, Phi0, 10000), burn_for_amortization(126, Phi0, 10000),
                      burn_for_amortization(85, Phi0, 10000))
    print("\n[Recipe-level Phi_local when a downstream recipe cites the clone (measured: every record executed, L_res from the real residual)]")
    print(f"  full amortization needs burn C = {C_A} (4A, 103 bits) / {C_B} (4B, 126 bits);  Delta_amort = 85 (= |p_s|) needs C = {C_85}")
    print(f"  {'recipe':<28}{'|w|':>5}{'steps':>7}{'l_d':>5}{'code':>6}{'unamort':>9}{'l_E':>5}{'L_res':>7}{'Phi_local':>11}{'Delta':>8}{'E_tr':>7}   | Delta_amort=85: unamort / Phi")
    cases = [("4A cited by w3, on D_3", w3, p_iA, LAW3, 28, 3), ("4B cited by w_2=\\v.v, on D_3", id_wrap, p_iB, LAW3, 28, 3),
             ("4A cited by w_2=\\v.v, on D_2", id_wrap, p_iA, LAW2, 51, 2)]
    got = {}
    for label, wr, pi_, law, kerr, seed in cases:
        full = recipe_phi(wr, pi_, law, kerr, seed, n_k, b_k, len(encode_blc(pi_)))
        part = recipe_phi(wr, pi_, law, kerr, seed, n_k, b_k, 85)
        dl = Phi0 - full["Phi"]; Etr = escrow_alloc(10000, Phi0, dl)
        print(f"  {label:<28}{full['wrap']:>5}{full['steps']:>7}{full['ld']:>5}{full['code']:>6}{full['unam']:>9}{full['lE']:>5}"
              f"{full['L_res']:>7}{full['Phi']:>11}{dl:>8}{Etr:>7}   | {part['unam']:>3} / {part['Phi']}")
        got[label] = (full["steps"], full["Phi"], part["Phi"])
    assert got["4A cited by w3, on D_3"][:2] == (920, 822) and got["4A cited by w3, on D_3"][2] == 840
    assert got["4B cited by w_2=\\v.v, on D_3"][:2] == (911, 778) and got["4B cited by w_2=\\v.v, on D_3"][2] == 819
    assert got["4A cited by w3, on D_3"][1] == out[3]["Phi"]               # drop-in: same Phi as Benchmark 3 (822)
    print("  note: w_2 on Clone 4A computes y = NOT(j) (law of D_2), not D_3's law; 778 bits is the 4B/D_3 value.")

    # ------------------------------------------------------------------ (Moderate 2) soundness / completeness boundary
    base = to_db(named_axiom_vs())                                         # unoptimized reference form of v_s
    notb = lambda: L("p", A(V("p"), B1(), B0()))
    v1 = A(YC(), L("r", "xs", A(V("xs"), L("h", "t", CONS(A(notb(), V("h")), A(L("z", A(V("r"), V("z"))), V("t")))), B1())))
    g2 = L("r", "acc", "xs", A(V("xs"), L("h", "t", CONS(A(notb(), V("h")), A(V("r"), A(L("y", V("y")), V("acc")), V("t")))), B1()))
    v2 = L("xs", A(A(A(YC(), g2), L("w", V("w"))), V("xs")))
    print(f"\n[T6 soundness / completeness boundary]  root = unoptimized reference form of v_s (|p| = {len(encode_blc(base))} bits), q = identity")
    for label, t, want in (("internal eta-expansion of the recursive call (regular unfolding)", to_db(v1), True),
                           ("accumulating padding in an ignored accumulator (non-regular unfolding)", to_db(v2), None)):
        ok = True
        for j in range(n_k):
            v, st, okj = run_program_total(t, [], j, b_k)
            ok = ok and okj and v == LAW2(j)
        eq, ks, fuel, status = t6_check(base, q_A, t)
        print(f"  {label}")
        print(f"     |p_i| = {len(encode_blc(t))} bits, functionally identical on {n_k if ok else 0}/{n_k} records;  "
              f"U(q(p_s)) =_beta-eta p_i : {eq} [{status}]   {fmt_fuel(fuel)}")
        assert ok and eq is want and (status == "equal" if want else status in ("fuel-exhausted", "resource-limit"))
    print("  => the check is SOUND (never accepts a non-equivalent program: negative controls above) but INCOMPLETE:"
          "\n     a functionally identical clone whose unfolding never repeats is not established within T_max (false negative).")
    print("Benchmark 4 assertions: PASS")

def scaling():
    w1 = prog_bench1()
    print("n_k   total_ms   ms/record   max_steps")
    for n in (256, 1024, 4096):
        t = time.time(); mx = 0
        for j in range(n):
            v, s = run_program(w1, [], j % 65536)
            assert v == LAW1(j % 65536); mx = max(mx, s)
        el = (time.time() - t) * 1000
        print(f"{n:5d} {el:10.1f} {el/n:11.3f} {mx:11d}")

if __name__ == "__main__":
    if "--selftest" in sys.argv:
        selftest()
    elif "--scaling" in sys.argv:
        selftest(); scaling()
    elif "--b4" in sys.argv:
        selftest(); o = run(); run_benchmark4(o)
    else:
        selftest()
        o = run(); report(o); run_benchmark4(o)
