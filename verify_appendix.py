#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""
verify_appendix.py -- automatic check of Appendix A (Table 8 and Table 9) against ESM_verified.lean.  Self-contained (stdlib only).

  1. total number of lines of the Lean file                                  (1,111)
  2. forbidden tokens outside comments: sorry, admit, native_decide, axiom, unsafe, implemented_by, ofReduceBool   (0 each)
  3. exactly the 53 catalogued theorem/lemma declarations exist in the file (no extra, none missing)
  4. for each of the 53 theorems: name, first line and last line equal the catalogue (No, Name, Start, End)
  5. (if --tex is given or a paper is found next to the script) the catalogue equals the rows printed in the manuscript's Tables 8-9
  6. (if `lean` is on PATH or --lean is given) the axiom audit of Section 7.1: 2 axiom-free, 14 propext-only,
     32 propext+Quot.sound, 5 with three axioms, and nothing outside {propext, Classical.choice, Quot.sound}
Usage:  python verify_appendix.py [ESM_verified.lean] [--tex paper.tex] [--lean /path/to/lean] [--no-axioms] [-v]
Exit status 0 = PASS.
"""
import glob, os, re, shutil, subprocess, sys, tempfile

CATALOG = [   # (No, Name, StartLine, EndLine) = the 53 rows of Tables 8-9 of the manuscript
    (1, 'div_le_div_right', 9, 14), (2, 'add_div_le_div_add', 16, 24), (3, 'mul_bps_div_le', 26, 31),
    (4, 'escrowAlloc_mono', 33, 36), (5, 'escrowAlloc_superadd', 38, 42), (6, 'pool_lower_bound_ceil', 44, 71),
    (7, 'local_desc_ge_one', 73, 78), (8, 'syntactic_reduction_waterfall_valid', 83, 99), (9, 'capStep_conserves', 105, 111),
    (10, 'capFold_conserves', 113, 123), (11, 'capFold_general_bound', 125, 143), (12, 'sumDiv_le', 149, 154),
    (13, 'sumRoyalty_le_total', 160, 170), (14, 'settle_general_list_conserves', 172, 210), (15, 'slot_four_way_split_conserves', 212, 247),
    (16, 'tranche_unroll_conserves_and_bounds', 253, 302), (17, 'puncture_invariant_preserved', 304, 320), (18, 'single_data_pre_embedding_unprofitable', 328, 360),
    (19, 'rbf_lifetime_cap', 362, 367), (20, 'rbf_prorata_le_list', 369, 385), (21, 'tEff_bounds', 390, 397),
    (22, 'global_supply_invariant_preserved', 414, 423), (23, 'DataInv.pool_lower', 449, 461), (24, 'stepAdopt_preserves_inv', 471, 516),
    (25, 'stepPuncture_concrete_preserves_inv', 538, 584), (26, 'stepHoldExpire_concrete_preserves_inv', 599, 636), (27, 'stepSettleInit_preserves_inv', 645, 663),
    (28, 'stepSettleAbs_preserves_inv', 672, 690), (29, 'stage1_single_bounds', 697, 730), (30, 'stage1_list_sum_le_delta', 732, 755),
    (31, 'puncture_slot_scale_valid', 757, 783), (32, 'allTranches_sum_bounded', 801, 811), (33, 'stepAdoptList_preserves_inv', 841, 878),
    (34, 'stepSettleHead_preserves_inv', 889, 911), (35, 'branch01_T0_preserves', 913, 916), (36, 'branch02_commit_preserves', 918, 921),
    (37, 'branch03_adopt_preserves', 923, 926), (38, 'branch04_reject_preserves', 928, 931), (39, 'branch05_unrevealed_preserves', 933, 939),
    (40, 'branch06_07_puncture_preserves', 941, 945), (41, 'branch08a_uw_topup_preserves', 947, 950), (42, 'branch08b_hold_expire_preserves', 952, 955),
    (43, 'branch09_settle_preserves', 957, 961), (44, 'branch10_close_ok_preserves', 963, 966), (45, 'branch11_close_pen_preserves', 968, 974),
    (46, 'branch12_to_15_preserves', 976, 979), (47, 'release_symmetric', 984, 999), (48, 'old_rule_leaks', 1002, 1004),
    (49, 'm1_redirect_rbf_priority_conserves', 1013, 1039), (50, 'game_pre_embedding_strictly_dominated', 1044, 1055), (51, 'game_griefing_strictly_dominated', 1060, 1068),
    (52, 'game_watchtower_deterrence_equilibrium', 1074, 1087), (53, 'game_honest_citation_dominates_unamortized_clone', 1093, 1109),
]
EXPECTED_LINES = 1111
EXPECTED_AXIOMS = dict(none=2, propext=14, propext_quot=32, three=5)
AXIOM_FREE = {"old_rule_leaks", "game_griefing_strictly_dominated"}
FORBIDDEN = ["sorry", "admit", "native_decide", "axiom", "unsafe", "implemented_by", "ofReduceBool"]

def strip_comments(src):
    """Blank out `-- ...` and (nested) `/- ... -/` comments, keeping the line structure."""
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        two = src[i:i + 2]
        if depth == 0 and two == "--":
            while i < n and src[i] != "\n": out.append(" "); i += 1
        elif two == "/-":
            depth += 1; out.append("  "); i += 2
        elif depth > 0 and two == "-/":
            depth -= 1; out.append("  "); i += 2
        else:
            out.append(src[i] if (depth == 0 or src[i] == "\n") else " "); i += 1
    return "".join(out)

def end_of(lines, start):
    """Last line of the declaration beginning at 1-based line `start`: the block ends before a blank gap followed by an unindented line."""
    j = start
    while j < len(lines):
        if lines[j].strip() == "":
            k = j
            while k < len(lines) and lines[k].strip() == "": k += 1
            if k >= len(lines) or (lines[k] and not lines[k][0].isspace()): return j
        j += 1
    return len(lines)

def main(argv):
    fails, verbose = [], "-v" in argv
    args = [a for a in argv[1:] if not a.startswith("-")]
    opt = lambda f: argv[argv.index(f) + 1] if f in argv and argv.index(f) + 1 < len(argv) else None
    lean_path = next((a for a in args if a.endswith(".lean")), "ESM_verified.lean")
    tex_path = opt("--tex") or next(iter(sorted(glob.glob("Esm_V15_2_Paper*.tex"))[-1:]), None)
    src = open(lean_path, encoding="utf-8").read(); lines = src.split("\n")
    if lines and lines[-1] == "": lines = lines[:-1]
    def check(label, ok, detail=""):
        print(f"{'PASS' if ok else 'FAIL'}  {label}" + (f"   [{detail}]" if detail else ""))
        if not ok: fails.append(label)
    # 1. size
    check(f"1. {os.path.basename(lean_path)}: total lines = {len(lines)} (expected {EXPECTED_LINES})", len(lines) == EXPECTED_LINES)
    # 2. forbidden tokens outside comments
    code = strip_comments(src)
    hits = {t: len(re.findall(r"(?<![A-Za-z0-9_'.])" + re.escape(t) + r"(?![A-Za-z0-9_'])", code)) for t in FORBIDDEN}
    check(f"2. forbidden tokens outside comments ({', '.join(FORBIDDEN)})", all(v == 0 for v in hits.values()),
          "all 0" if all(v == 0 for v in hits.values()) else str({k: v for k, v in hits.items() if v}))
    # 3. declarations
    decls = {}
    for i, l in enumerate(lines, 1):
        m = re.match(r"^(theorem|lemma)\s+([^\s:({\[]+)", l)
        if m:
            decls.setdefault(m.group(2), i)
    names = [c[1] for c in CATALOG]
    extra, missing = sorted(set(decls) - set(names)), sorted(set(names) - set(decls))
    check(f"3. theorem/lemma declarations: {len(decls)} found, {len(CATALOG)} catalogued", not extra and not missing and len(decls) == 53,
          f"extra={extra} missing={missing}" if (extra or missing) else "")
    # 4. exact names / start / end
    bad = []
    for no, nm, a, b in CATALOG:
        s0 = decls.get(nm); e0 = end_of(lines, s0) if s0 else None
        if (s0, e0) != (a, b): bad.append((no, nm, (a, b), (s0, e0)))
        elif verbose: print(f"      {no:>2} {nm:<46}{a:>5}--{b:<5} ok")
    for t in bad: print("      MISMATCH", t)
    check("4. each of the 53 theorems: name, first line, last line equal the catalogue", not bad, f"{len(CATALOG) - len(bad)}/53 exact")
    ordered = all(CATALOG[i][3] < CATALOG[i + 1][2] for i in range(52)) and [c[0] for c in CATALOG] == list(range(1, 54))
    check("   catalogue numbered 1..53 with disjoint ascending line ranges", ordered)
    # 5. manuscript
    if tex_path and os.path.exists(tex_path):
        tex = open(tex_path, encoding="utf-8").read()
        rows = [(int(n), nm.replace("\\_", "_"), int(a), int(b)) for n, nm, a, b in
                re.findall(r"^(\d+) & \\texttt\{([^}]+)\} & (\d+)--(\d+) &", tex, re.M)]
        check(f"5. manuscript {os.path.basename(tex_path)}: Tables 8-9 list the same 53 rows", rows == CATALOG, f"{len(rows)} rows")
    else:
        print("5. manuscript .tex not found: SKIPPED (pass --tex paper.tex)")
    # 6. axiom audit
    lean_bin = opt("--lean") or shutil.which("lean")
    if "--no-axioms" in argv or not lean_bin:
        print("6. axiom audit: SKIPPED (" + ("--no-axioms" if "--no-axioms" in argv else "no `lean` on PATH; pass --lean /path/to/lean") + ")")
    else:
        r0 = subprocess.run([lean_bin, lean_path], capture_output=True, text=True, timeout=600)   # the UNMODIFIED file
        check("6a. `lean` compiles the unmodified file with 0 errors, 0 warnings, 0 output lines", r0.returncode == 0 and not (r0.stdout + r0.stderr).strip())
        ns = (re.search(r"^namespace\s+(\S+)", src, re.M) or [None, ""])[1]
        pre = (ns + ".") if ns else ""
        with tempfile.TemporaryDirectory() as d:
            f = os.path.join(d, "audit.lean")
            open(f, "w", encoding="utf-8").write(src.rstrip("\n") + "\n" + "".join(f"#print axioms {pre}{n}\n" for n in names))
            r = subprocess.run([lean_bin, f], capture_output=True, text=True, timeout=600)
        ents = re.split(r"\n(?='" + re.escape(pre) + ")", r.stdout.strip())
        res = {}
        for e in ents:
            m = re.match(r"'([^']+)' (does not depend on any axioms|depends on axioms: \[(.*?)\])", e, re.S)
            if m: res[m.group(1)[len(pre):]] = tuple(sorted(a.strip() for a in (m.group(3) or "").split(",") if a.strip()))
        cnt = dict(none=0, propext=0, propext_quot=0, three=0); other = set()
        for n, ax in res.items():
            other |= set(ax) - {"propext", "Classical.choice", "Quot.sound"}
            key = ("none" if not ax else "propext" if ax == ("propext",) else "propext_quot" if ax == ("Quot.sound", "propext") else
                   "three" if len(ax) == 3 else "other")
            if key in cnt: cnt[key] += 1
        free = {n for n, ax in res.items() if not ax}
        ok = (r.returncode == 0 and len(res) == 53 and cnt == EXPECTED_AXIOMS and not other and free == AXIOM_FREE)
        check("6b. axiom audit of all 53 theorems (Section 7.1: 2 / 14 / 32 / 5; only propext, Classical.choice, Quot.sound)", ok,
              f"axiom-free {cnt['none']}, propext {cnt['propext']}, propext+Quot.sound {cnt['propext_quot']}, three {cnt['three']}")
    print("verify_appendix: " + ("PASS" if not fails else "FAIL -> " + "; ".join(fails)))
    return 0 if not fails else 1

if __name__ == "__main__":
    sys.exit(main(sys.argv))
