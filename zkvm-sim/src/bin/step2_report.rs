//! Step 2 measurements: retired RV32IM instructions of esm-core (the zkVM-cycle proxy) for the workloads that matter.
use std::collections::BTreeMap;
use zkvm_sim::*;
use esm_core::blc::{encode_blc, Arena};

fn golden() -> Vec<Vec<String>> {
    let p = concat!(env!("CARGO_MANIFEST_DIR"), "/../spec/vectors/golden.txt");
    std::fs::read_to_string(p).unwrap().lines().filter(|l| !l.is_empty() && !l.starts_with('#')).map(|l| l.split_whitespace().map(String::from).collect()).collect()
}
fn bits(s: &str) -> Vec<u8> {
    s.bytes().map(|b| b - b'0').collect()
}
const BUDGET: u64 = 200_000_000_000;

fn secs(instr: u64, rate: f64) -> f64 {
    instr as f64 / rate
}

fn main() {
    let elf = load_guest();
    let g = golden();
    let prog: BTreeMap<String, Vec<u8>> = g.iter().filter(|l| l[0] == "PROG").map(|l| (l[1].clone(), bits(&l[2]))).collect();
    let mut md = String::new();
    macro_rules! out { ($($t:tt)*) => {{ let s = format!($($t)*); println!("{}", s); md.push_str(&s); md.push('\n'); }} }

    out!("# Step 2 measurements (RV32IM instructions retired = zkVM cycle proxy)\n");
    out!("Guest: esm-core compiled for riscv32im-unknown-none-elf, release, thin LTO, overflow-checks ON (shipped profile).");
    out!("Executed in `zkvm-sim`. No precompiles are modelled: MST hashing (keccak) is NOT included.\n");

    // ---------------------------------------------------------------- 1. benchmarks per record
    out!("## 1. Benchmarks 1-3, all 1024 records (parse + run, delta = T_MAX)\n");
    out!("| benchmark | max KAM steps | mean steps | mean instr/record | max instr/record | instr/step (mean) | instr/step at max-step record | parse+setup instr |");
    out!("|---|---|---|---|---|---|---|---|");
    let mut b1_instr: Vec<u64> = vec![];
    for (name, w, args) in [("1 (affine LCG)", "w1", vec![]), ("2 (NOT via axiom)", "w2", vec!["vs"]), ("3 (OR 1 via axiom)", "w3", vec!["vs"])] {
        let mut progs = vec![prog[w].clone()];
        let ai: Vec<u32> = args.iter().map(|a| { progs.push(prog[*a].clone()); (progs.len() - 1) as u32 }).collect();
        let cases: Vec<Case1> = (0..1024u64).map(|j| Case1 { prog: 0, args: ai.clone(), j, width: 16, delta: 1 << 20 }).collect();
        let run = run_mode1(&elf, &progs, &cases, BUDGET).unwrap();
        let setup = run_mode1(&elf, &progs, &[Case1 { prog: 0, args: ai.clone(), j: 0, width: 16, delta: 1 }], BUDGET).unwrap().results[0].instret;
        let (mut s_sum, mut i_sum, mut i_max, mut s_max, mut at_max) = (0u64, 0u64, 0u64, 0u64, 0u64);
        for r in &run.results {
            s_sum += r.steps as u64;
            i_sum += r.instret;
            if r.instret > i_max { i_max = r.instret; }
            if r.steps as u64 > s_max { s_max = r.steps as u64; at_max = r.instret; }
        }
        if name.starts_with('1') { b1_instr = run.results.iter().map(|r| r.instret).collect(); }
        out!("| {} | {} | {:.0} | {:.0} | {} | {:.1} | {:.1} | {} |", name, s_max, s_sum as f64 / 1024.0, i_sum as f64 / 1024.0, i_max, i_sum as f64 / s_sum as f64, at_max as f64 / s_max as f64, setup);
    }

    // ---------------------------------------------------------------- 2. K_spot = 32
    out!("\n## 2. One reveal = K_spot = 32 spot-checked records\n");
    let mut seed: u64 = 0x2545_F491_4F6C_DD1D;
    let mut pick = || { seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); ((seed >> 33) % 1024) as usize };
    let idx: Vec<usize> = (0..32).map(|_| pick()).collect();
    let spot1: u64 = idx.iter().map(|&i| b1_instr[i]).sum();
    let worst32: u64 = {
        let mut v = b1_instr.clone(); v.sort(); v.iter().rev().take(32).sum()
    };
    out!("| workload | instructions | time @1M cyc/s | @3.5M cyc/s | @10M cyc/s |");
    out!("|---|---|---|---|---|");
    for (label, n) in [("Benchmark 1, 32 random records (delta = 7457)", spot1), ("Benchmark 1, the 32 most expensive records", worst32)] {
        out!("| {} | {} | {:.1} s | {:.1} s | {:.1} s |", label, n, secs(n, 1e6), secs(n, 3.5e6), secs(n, 1e7));
    }

    // ---------------------------------------------------------------- 3. hostile divergent program
    out!("\n## 3. Adversarial: a diverging program declares delta (proposer pays its own proof, but the verifier-side cost bounds delta_cap)\n");
    let omega = {
        let mut a = Arena::new_plain();
        let v0 = a.var(0).unwrap(); let x = a.app(v0, v0).unwrap(); let om = a.lam(x).unwrap(); let oo = a.app(om, om).unwrap(); let t = a.lam(oo).unwrap();
        let mut b = vec![]; encode_blc(&a, t, &mut b).unwrap(); b
    };
    out!("| delta | instructions / record | instr per step | x32 records | time @3.5M cyc/s (x32) |");
    out!("|---|---|---|---|---|");
    for delta in [1u32 << 10, 1 << 16, 1 << 20] {
        let r = run_mode1(&elf, &[omega.clone()], &[Case1 { prog: 0, args: vec![], j: 5, width: 16, delta }], BUDGET).unwrap().results[0];
        assert_eq!((r.ok, r.steps), (0, delta));
        out!("| 2^{} | {} | {:.1} | {} | {:.0} s |", delta.trailing_zeros(), r.instret, r.instret as f64 / delta as f64, 32 * r.instret, secs(32 * r.instret, 3.5e6));
    }

    // ---------------------------------------------------------------- 4. de Bruijn lookup cost
    out!("\n## 4. Adversarial: de Bruijn lookups are charged 1 step but cost `index` pointer hops\n");
    let deep = |d: u32, k: u32| -> Vec<u8> {
        let mut a = Arena::new_plain();
        let (v0, v1) = (a.var(0).unwrap(), a.var(1).unwrap());
        let id = a.lam(v0).unwrap();
        let sel = { let l = a.lam(v0).unwrap(); a.lam(l).unwrap() };      // \a.\b.b
        let xx = a.app(v0, v0).unwrap();
        let _ = v1;
        let vk = a.var(k).unwrap();
        let g_body = { let t = a.app(vk, id).unwrap(); a.app(t, xx).unwrap() };   // k-th variable  Z  (x x)
        let g = a.lam(g_body).unwrap();
        let l = a.lam(xx).unwrap();
        let body = a.app(l, g).unwrap();                                           // (\x. x x) G
        let mut f = body;
        for _ in 0..d { f = a.lam(f).unwrap(); }
        let mut t = f;
        for i in 0..d { t = a.app(t, if i == 0 { sel } else { id }).unwrap(); }
        let t = a.lam(t).unwrap();
        let mut b = vec![]; encode_blc(&a, t, &mut b).unwrap(); b
    };
    // legitimate programs: largest de Bruijn index actually used
    {
        let mut a = Arena::new_plain();
        let mut worst = 0u32;
        let mut line = String::new();
        for n in ["w1", "vs", "w2", "w3", "pA", "pB", "base", "v1", "v2", "qA"] {
            let t = esm_core::blc::parse_blc(&mut a, &prog[n]).unwrap();
            let (mut st, mut mx) = (vec![t], 0u32);
            while let Some(id) = st.pop() {
                match a.node(id) { esm_core::Node::Var(i) => mx = mx.max(i), esm_core::Node::Lam(b) => st.push(b), esm_core::Node::App(f, x) => { st.push(f); st.push(x) } _ => {} }
            }
            worst = worst.max(mx);
            line += &format!("{n}:{mx} ");
        }
        out!("Largest de Bruijn index used by the benchmark / clone / axiom programs: **{}** ({}).\n", worst, line.trim());
    }
    out!("Construction: `(\\^D. (\\x.x x)(\\x. v_k Z (x x))) A_1 .. A_D`; v_k = Var(D) (hostile, D hops per lookup) or Var(1) (control). delta in {{40000, 65536}}; the marginal cost is measured in the loop phase only.\n");
    out!("| D (= index of the looked-up variable) | program bits | control instr/step | hostile instr/step | extra instr/step per unit of D |");
    out!("|---|---|---|---|---|");
    let mut last = (0.0, 0.0);
    for d in [10u32, 100, 255] {
        let mut m = vec![];
        let mut bitsn = 0;
        for k in [1u32, d] {
            let p = deep(d, k);
            bitsn = p.len();
            let mut v = vec![];
            for delta in [40_000u32, 65_536] {
                let r = run_mode1(&elf, &[p.clone()], &[Case1 { prog: 0, args: vec![], j: 5, width: 16, delta }], BUDGET).unwrap().results[0];
                assert_eq!((r.ok, r.steps), (0, delta));
                v.push(r.instret);
            }
            m.push((v[1] - v[0]) as f64 / 25_536.0);
        }
        out!("| {} | {} | {:.1} | {:.1} | {:.4} |", d, bitsn, m[0], m[1], (m[1] - m[0]) / d as f64);
        last = (m[0], m[1]);
    }
    out!("\nWith MAX_DEBRUIJN_INDEX = 255 the extra per-step cost is bounded by about 255 hops (<= {:.1} extra instr/step in this construction).", last.1 - last.0);
    let rejected = deep(7000, 7000);
    let r = run_mode1(&elf, &[rejected.clone()], &[Case1 { prog: 0, args: vec![], j: 5, width: 16, delta: 65_536 }], BUDGET).unwrap().results[0];
    out!("The former D = 7000 attack program ({} bits) is now a syntax error: it falls back after parsing only ({} instructions in total, ok = {}, steps = delta = {}).\n", rejected.len(), r.instret, r.ok, r.steps);

    // ---------------------------------------------------------------- 5. T6
    out!("\n## 5. T6 (bounded Bohm-tree equivalence), one check each\n");
    let names = ["vs", "qA", "pA", "w3", "pB", "base", "v1", "v2", "w1"];
    let progs: Vec<Vec<u8>> = names.iter().map(|n| prog[*n].clone()).collect();
    let id = |n: &str| names.iter().position(|x| *x == n).unwrap() as u32;
    let cases = [("Clone 4A (fuel 747)", "vs", "qA", "pA", 1u32 << 20), ("Clone 4B (fuel 263)", "vs", "w3", "pB", 1 << 20), ("dummy-accumulator clone v1 (fuel 2630)", "base", "qA", "v1", 1 << 20),
        ("negative control, unrelated program (fuel 5515)", "vs", "qA", "w1", 1 << 20), ("v2 EXHAUSTS fuel_max = 2^16", "base", "qA", "v2", 1 << 16), ("v2 EXHAUSTS fuel_max = 2^20", "base", "qA", "v2", 1 << 20)];
    let run = run_mode2(&elf, &progs, &cases.iter().map(|c| (id(c.1), id(c.2), id(c.3), c.4)).collect::<Vec<_>>(), BUDGET).unwrap();
    out!("| case | verdict | fuel used | instructions | instr per fuel unit | time @3.5M cyc/s |");
    out!("|---|---|---|---|---|---|");
    for (c, r) in cases.iter().zip(&run.results) {
        let used = r.kam as u64 + r.beta as u64 + r.nodes as u64 + r.work as u64;
        let v = ["not-equal", "equal", "undecided"][r.eq as usize];
        out!("| {} | {} | {} | {} | {:.1} | {:.2} s |", c.0, v, used, r.instret, r.instret as f64 / used.max(1) as f64, secs(r.instret, 3.5e6));
    }
    out!("\nHeap high-water of the T6 batch: {} KiB.", run.heap_high_water / 1024);

    std::fs::write(concat!(env!("CARGO_MANIFEST_DIR"), "/../step2_report.md"), md).unwrap();
}
