# Step 2 measurements (RV32IM instructions retired = zkVM cycle proxy)

Guest: esm-core compiled for riscv32im-unknown-none-elf, release, thin LTO, overflow-checks ON (shipped profile).
Executed in `zkvm-sim`. No precompiles are modelled: MST hashing (keccak) is NOT included.

## 1. Benchmarks 1-3, all 1024 records (parse + run, delta = T_MAX)

| benchmark | max KAM steps | mean steps | mean instr/record | max instr/record | instr/step (mean) | instr/step at max-step record | parse+setup instr |
|---|---|---|---|---|---|---|---|
| 1 (affine LCG) | 7457 | 4143 | 314170 | 516713 | 75.8 | 69.3 | 38619 |
| 2 (NOT via axiom) | 904 | 904 | 108966 | 109458 | 120.5 | 121.1 | 22405 |
| 3 (OR 1 via axiom) | 911 | 911 | 112090 | 112569 | 123.0 | 123.6 | 25180 |

## 2. One reveal = K_spot = 32 spot-checked records

| workload | instructions | time @1M cyc/s | @3.5M cyc/s | @10M cyc/s |
|---|---|---|---|---|
| Benchmark 1, 32 random records (delta = 7457) | 10048533 | 10.0 s | 2.9 s | 1.0 s |
| Benchmark 1, the 32 most expensive records | 12320458 | 12.3 s | 3.5 s | 1.2 s |

## 3. Adversarial: a diverging program declares delta (proposer pays its own proof, but the verifier-side cost bounds delta_cap)

| delta | instructions / record | instr per step | x32 records | time @3.5M cyc/s (x32) |
|---|---|---|---|---|
| 2^10 | 54689 | 53.4 | 1750048 | 1 s |
| 2^16 | 2077634 | 31.7 | 66484288 | 19 s |
| 2^20 | 32627012 | 31.1 | 1044064384 | 298 s |

## 4. Adversarial: de Bruijn lookups are charged 1 step but cost `index` pointer hops

Largest de Bruijn index used by the benchmark / clone / axiom programs: **10** (w1:10 vs:5 w2:0 w3:3 pA:5 pB:5 base:3 v1:4 v2:4 qA:0).

Construction: `(\^D. (\x.x x)(\x. v_k Z (x x))) A_1 .. A_D`; v_k = Var(D) (hostile, D hops per lookup) or Var(1) (control). delta in {40000, 65536}; the marginal cost is measured in the loop phase only.

| D (= index of the looked-up variable) | program bits | control instr/step | hostile instr/step | extra instr/step per unit of D |
|---|---|---|---|---|
| 10 | 122 | 32.2 | 32.4 | 0.0195 |
| 100 | 932 | 32.2 | 34.4 | 0.0217 |
| 255 | 2327 | 31.4 | 37.0 | 0.0218 |

With MAX_DEBRUIJN_INDEX = 255 the extra per-step cost is bounded by about 255 hops (<= 5.6 extra instr/step in this construction).
The former D = 7000 attack program (63032 bits) is now a syntax error: it falls back after parsing only (819202 instructions in total, ok = 0, steps = delta = 65536).


## 5. T6 (bounded Bohm-tree equivalence), one check each

| case | verdict | fuel used | instructions | instr per fuel unit | time @3.5M cyc/s |
|---|---|---|---|---|---|
| Clone 4A (fuel 747) | equal | 747 | 189548 | 253.7 | 0.05 s |
| Clone 4B (fuel 263) | equal | 263 | 66818 | 254.1 | 0.02 s |
| dummy-accumulator clone v1 (fuel 2630) | equal | 2630 | 582595 | 221.5 | 0.17 s |
| negative control, unrelated program (fuel 5515) | not-equal | 5515 | 1402299 | 254.3 | 0.40 s |
| v2 EXHAUSTS fuel_max = 2^16 | undecided | 65606 | 13366151 | 203.7 | 3.82 s |
| v2 EXHAUSTS fuel_max = 2^20 | undecided | 1048663 | 191873971 | 183.0 | 54.82 s |

Heap high-water of the T6 batch: 280 KiB.
