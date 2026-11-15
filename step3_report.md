# Step 3 report - ESMMath.sol / ESMAccounting.sol

## Result
* `forge test`: **88 tests passed, 0 failed** (54 theorem property tests x 3000 fuzz runs, 22 differential tests over **65,176** oracle rows,
  8 paper-table tests, 4 range/overflow tests). Solidity 0.8.28, `via_ir`, optimizer on, forge 1.5.1.
* **54 / 54** Lean theorems (53 original + `shannon_len_ceilDiv_iff`) have exactly one Solidity property test (matched by name, table below).
* Oracles: **Lean `#eval` of `ESM_verified.lean`** (35,000 rows: escrowAlloc, ceilDiv, calcRoyalty, safeRemEscrow, calcAmortGen, calcNetRewardGen, calcTEff,
  allocStage1Single, applyLedgerTx, stepAdopt, stepPunctureConcrete, stepHoldExpire, stepSettleInit/Abs on arbitrary - not necessarily invariant - states,
  boundary-heavy) and an independent **Python big-integer oracle** (30,176 rows) for quantities that only exist inside theorem statements or the paper
  (Shannon length, Stage 2, settlement, four-way split, M1, unroll, release, slash, closed forms).
* Ranges (frozen in `spec/params.toml`): tokens <= 2^96-1, bits <= 2^40, rates <= 20000 bps, lists <= 16 (tranches <= 1024). Every entry point checks its
  inputs (custom errors), so no intermediate product can exceed 2^256 (worst cases 136/150/151/193/206 bits; asserted in `Bounds.t.sol`).

## Theorem -> Solidity -> test (generated from the Lean file and the test file)
| # | Lean line | theorem | Solidity | Foundry test |
|---|---|---|---|---|
| 1 | 9 | `div_le_div_right` | div0 | `test_T01_div_le_div_right` |
| 2 | 16 | `add_div_le_div_add` | div0 | `test_T02_add_div_le_div_add` |
| 3 | 26 | `mul_bps_div_le` | div0 | `test_T03_mul_bps_div_le` |
| 4 | 33 | `escrowAlloc_mono` | escrowAlloc | `test_T04_escrowAlloc_mono` |
| 5 | 38 | `escrowAlloc_superadd` | escrowAlloc | `test_T05_escrowAlloc_superadd` |
| 6 | 44 | `pool_lower_bound_ceil` | ceilDiv | `test_T06_pool_lower_bound_ceil` |
| 7 | 73 | `local_desc_ge_one` | (plain arithmetic) | `test_T07_local_desc_ge_one` |
| 8 | 83 | `syntactic_reduction_waterfall_valid` | calcRoyalty / stage2Redirect | `test_T08_syntactic_reduction_waterfall_valid` |
| 9 | 105 | `capStep_conserves` | capStep | `test_T09_capStep_conserves` |
| 10 | 113 | `capFold_conserves` | capFold | `test_T10_capFold_conserves` |
| 11 | 125 | `capFold_general_bound` | capFold | `test_T11_capFold_general_bound` |
| 12 | 149 | `sumDiv_le` | div0 | `test_T12_sumDiv_le` |
| 13 | 160 | `sumRoyalty_le_total` | sumRoyalty | `test_T13_sumRoyalty_le_total` |
| 14 | 172 | `settle_general_list_conserves` | settleTranche | `test_T14_settle_general_list_conserves` |
| 15 | 212 | `slot_four_way_split_conserves` | slotFourWaySplit | `test_T15_slot_four_way_split_conserves` |
| 16 | 253 | `tranche_unroll_conserves_and_bounds` | trancheUnroll | `test_T16_tranche_unroll_conserves_and_bounds` |
| 17 | 304 | `puncture_invariant_preserved` | punctureFrontier | `test_T17_puncture_invariant_preserved` |
| 18 | 328 | `single_data_pre_embedding_unprofitable` | preEmbedding | `test_T18_single_data_pre_embedding_unprofitable` |
| 19 | 362 | `rbf_lifetime_cap` | (plain arithmetic) | `test_T19_rbf_lifetime_cap` |
| 20 | 369 | `rbf_prorata_le_list` | rbfProrata | `test_T20_rbf_prorata_le_list` |
| 21 | 390 | `tEff_bounds` | tEff | `test_T21_tEff_bounds` |
| 22 | 414 | `global_supply_invariant_preserved` | ledgerTx | `test_T22_global_supply_invariant_preserved` |
| 23 | 449 | `DataInv.pool_lower` | dataInv / poolLowerBound | `test_T23_DataInv_pool_lower` |
| 24 | 471 | `stepAdopt_preserves_inv` | stepAdopt / adopt | `test_T24_stepAdopt_preserves_inv` |
| 25 | 538 | `stepPuncture_concrete_preserves_inv` | stepPunctureConcrete / puncture | `test_T25_stepPuncture_concrete_preserves_inv` |
| 26 | 599 | `stepHoldExpire_concrete_preserves_inv` | stepHoldExpire / holdExpire | `test_T26_stepHoldExpire_concrete_preserves_inv` |
| 27 | 645 | `stepSettleInit_preserves_inv` | stepSettleInit / settleInit | `test_T27_stepSettleInit_preserves_inv` |
| 28 | 672 | `stepSettleAbs_preserves_inv` | stepSettleAbs / settleAbs | `test_T28_stepSettleAbs_preserves_inv` |
| 29 | 697 | `stage1_single_bounds` | stage1Alloc | `test_T29_stage1_single_bounds` |
| 30 | 732 | `stage1_list_sum_le_delta` | stage1List | `test_T30_stage1_list_sum_le_delta` |
| 31 | 757 | `puncture_slot_scale_valid` | slotScale / sAfter | `test_T31_puncture_slot_scale_valid` |
| 32 | 801 | `allTranches_sum_bounded` | allTranchesBounded | `test_T32_allTranches_sum_bounded` |
| 33 | 841 | `stepAdoptList_preserves_inv` | stepAdoptList | `test_T33_stepAdoptList_preserves_inv` |
| 34 | 889 | `stepSettleHead_preserves_inv` | stepSettleHead | `test_T34_stepSettleHead_preserves_inv` |
| 35 | 913 | `branch01_T0_preserves` | branchNN (ledgerTx pattern) | `test_T35_branch01_T0` |
| 36 | 918 | `branch02_commit_preserves` | branchNN (ledgerTx pattern) | `test_T36_branch02_commit` |
| 37 | 923 | `branch03_adopt_preserves` | branchNN (ledgerTx pattern) | `test_T37_branch03_adopt` |
| 38 | 928 | `branch04_reject_preserves` | branchNN (ledgerTx pattern) | `test_T38_branch04_reject` |
| 39 | 933 | `branch05_unrevealed_preserves` | branchNN (ledgerTx pattern) | `test_T39_branch05_unrevealed` |
| 40 | 941 | `branch06_07_puncture_preserves` | branchNN (ledgerTx pattern) | `test_T40_branch06_07_puncture` |
| 41 | 947 | `branch08a_uw_topup_preserves` | branchNN (ledgerTx pattern) | `test_T41_branch08a_uw_topup` |
| 42 | 952 | `branch08b_hold_expire_preserves` | branchNN (ledgerTx pattern) | `test_T42_branch08b_hold_expire` |
| 43 | 957 | `branch09_settle_preserves` | branchNN (ledgerTx pattern) | `test_T43_branch09_settle` |
| 44 | 963 | `branch10_close_ok_preserves` | branchNN (ledgerTx pattern) | `test_T44_branch10_close_ok` |
| 45 | 968 | `branch11_close_pen_preserves` | branchNN (ledgerTx pattern) | `test_T45_branch11_close_pen` |
| 46 | 976 | `branch12_to_15_preserves` | branchNN (ledgerTx pattern) | `test_T46_branch12_to_15` |
| 47 | 984 | `release_symmetric` | symmetricRelease | `test_T47_release_symmetric` |
| 48 | 1002 | `old_rule_leaks` | oldRuleRelease | `test_T48_old_rule_leaks` |
| 49 | 1013 | `m1_redirect_rbf_priority_conserves` | m1RedirectRbfPriority | `test_T49_m1_redirect_rbf_priority_conserves` |
| 50 | 1044 | `game_pre_embedding_strictly_dominated` | preEmbedding | `test_T50_game_pre_embedding_strictly_dominated` |
| 51 | 1060 | `game_griefing_strictly_dominated` | griefingScaled / gammaMax | `test_T51_game_griefing_strictly_dominated` |
| 52 | 1074 | `game_watchtower_deterrence_equilibrium` | (plain arithmetic) | `test_T52_game_watchtower_deterrence_equilibrium` |
| 53 | 1093 | `game_honest_citation_dominates_unamortized_clone` | honestCitation | `test_T53_game_honest_citation_dominates` |
| 54 | 1123 | `shannon_len_ceilDiv_iff` | shannonLen / clog2 / ceilDiv | `test_T54_shannon_len_ceilDiv_iff` |

## Tables 3-7 of the paper
| table | cells verified | notes |
|---|---|---|
| 3 (BLC benchmarks) | all arithmetic cells: code bits, L_res (input), Phi_local (full/partial), Delta and %, escrow, E_net, royalty R, Stage 2 (x_is, x_ii, R, L_red) for Benchmarks 1-3, 4A, 4B | steps and L_res are measured by esm-core (bit-exact against the Python reference in Step 1) and used as inputs |
| 4 (cash flow) | all 25 cells (5 strategies x N = 1, 5, 6, 10, 15) + the dataset-12 debt retirement (152) | run through `m1RedirectRbfPriority` / `calcRoyalty` / `preEmbedding` |
| 5 (sensitivity) | 1a gamma_max (8), 1b kappa_min (8), 2a f_grind (6 + 3-decimal forms), 2b q_detect (8), 3 R_net / N_cite / N_repay / N_cite(+DA) (20), integer scans over E_tr in [1, 20000] | see "definitions" below |
| 6, 7 (ablation equilibria) | only cells that follow from accounting identities: royalty 12 x 9 = 108 and 24 x 9 = 216, minimal burn 50, DA fee 1, nets +36 / +77 / -22 / -34 / -2 / +106, sponsor +38, phase boundary c_dev <= 56 | **NOT verified**: welfare W, P net, clone-Q payoffs, M2's royalty 99 / 207 and every equilibrium selection. They need the game solver `esm_exp3_ablation.py` (and `esm_exp2_sensitivity.py`), which were not among the delivered sources |

Definitions that had to be inferred (each reproduces the paper's printed numbers, which is the evidence for the inference):
* `f_grind` is certified on a 1e-6 grid: the smallest ppm with (1-f)^K <= kappa'/(kappa' + 0.95(1+Lambda)), i.e. `ceil(f * 1e6)`. All six appendix values
  (5.2180, 2.6440, 1.3309, 7.8739, 4.0177, 2.0295 %) match; plain rounding does not (4.0176).
* The integer scan uses `S_creator = ceil(sigma E_tr / (10000 + Lambda))`, `S_burn` from `slashSplit(10000, S_creator, kappa)` and
  `R_evade = floor(gamma (E_tr - floor(eps E_tr / 10000)) / 10000)`. It yields **0** violations at the baseline over E_tr in [1, 20000] and **exactly one** tie
  (E_tr = 10, S_burn = R_evade = 3) at the knife-edge parameters, the two facts stated in the paper; the three other natural variants reproduce at most one.

## Design notes and deviations
* Raw `step*` functions are the Lean definitions (total, `monus`); guarded entry points (`adopt`, `puncture`, `holdExpire`, `ledgerTx`, `branch*`) check the theorem
  hypotheses and revert (`Precondition(code)`), so a valid state cannot leave the invariant. `Bounds.t.sol` exercises 11 of those guards.
* `ListDataState` stores the tranche list with its Lean head at the END of the array (push/pop at the end).
* Every `a / 0` is `div0` (Lean: 0): a Solidity division panic is unreachable, so a zero denominator can never freeze settlement.
* `SupplyState`: the 12 Lean branch theorems map to 12 functions. Branches 06/07 and 12-15 are one Lean theorem each and are implemented as one function each
  (`branch0607Puncture`, `branch12to15`). The paper's "18 schemas" were not re-derived one by one.
* Not in this step: storage layout / access control / WETH transfers, the zkVM verifier adapter, the drand beacon. They wrap these pure functions.
