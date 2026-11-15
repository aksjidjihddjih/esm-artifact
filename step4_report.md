# Step 4 report - ESM.sol, registries, 18 ledger schemas, lifecycle test

## Result
* `forge test` (all suites): **94 tests passed, 0 failed** = 88 (Step 3) + 6 new (full lifecycle, fee-on-transfer rejection, mint cap round trip, guardian expiry, seed beacon, archive limits).
* `ESMIntegration.test_full_lifecycle_T0_to_T5` runs T0 -> T1 (commit, reveal, adopt, loser refund, unrevealed forfeit) -> T6 (Clone 4A, Clone 4B) -> RBF -> T2 (II-A, III)
  -> T3 (absorb, expiry) -> T4 (settlement, close) -> T5 (epochs) -> withdrawals. After EVERY step `supplyInvariant()` (wallets + locked + burned + redeemed = minted,
  user wallets + pools = wallets, token balance = minted - redeemed - flushed burn) and `dataInvariant(id)` (DataInv of every dataset) are asserted; at the end all
  18 schema counters (`branchHits`) are > 0 and the burned tokens sit at the dead address.
* Table 6 / Table 7 (and the exp2 baseline) were completed with the two experiment scripts you supplied: both run (exit 0) and pass their own 50-cell / baseline
  assertions; `ref-py/verify_paper_tables.py` additionally extracts every numeric cell of the two LaTeX tables and finds **60 / 60** of them (with sign) in the matching
  mechanism block of the script output. (This is a presence check per mechanism, not a positional one.)

## Contracts and sizes (EIP-170: 24,576 bytes runtime, EIP-3860: 49,152 bytes initcode)
| contract | runtime bytes | initcode bytes | runtime margin to 24,576 | initcode margin to 49,152 |
|---|---|---|---|---|
| ArchiveRegistry | 2,459 | 2,593 | 22,117 | 46,559 |
| ESM | 21,536 | 38,272 | 3,040 | 10,880 |
| ESMOps | 15,732 | 16,143 | 8,844 | 33,009 |
| SeedBeacon | 2,394 | 2,734 | 22,182 | 46,418 |
| VerifierRegistry | 1,849 | 2,021 | 22,727 | 47,131 |

The first monolithic `ESM.sol` was 31,183 bytes: over the limit. It is now `ESMStorage` (constants, state, shared helpers; abstract) + `ESM` (core) + `ESMOps`
(settlement, slashing, hold, close, RBF) reached by `delegatecall` forwarders with identical storage layout. `ESMOps` can only act when delegated (`NotDelegated`).

## The 18 ledger schemas
| id | schema | entry point | Step-3 ledger function | evidence |
|---|---|---|---|---|
| B1 | T0 register (lock B_k, S_k; burn eps_DA * Phi) | `registerDataset` | `branch01T0` | lifecycle |
| B2 | T1 phase 1 blind commit (lock S_c) | `commit(1, ..)` | `branch02Commit` | lifecycle |
| B3 | T1 phase 2 adopt (S_uw + S_audit locked; DA fee + C_amort burned) | `finalizeBatch` -> `_adopt` | `branch03Adopt` (+ reveal-lock release) | lifecycle |
| B4 | T1 phase 2 reject (S_c back, DA fee burned) | `finalizeBatch` -> `_reject` | `branch04Reject` | lifecycle (Carol: only 40 wei-units burned) |
| B5 | unrevealed forfeit (30 % back, 70 % burned) | `forfeitUnrevealed` | `branch05Unrevealed` | lifecycle (Dave) |
| B6 | T2 mode II-A full slash (30 % hunter / 70 % burn, recipe rolled back) | `revealSlash(mode 1)` | `branch0607Puncture` + `puncture` | lifecycle (Fay, dataset penalized) |
| B7 | T2 mode III partial puncture (time-invariant denominator, S_uw intact) | `revealSlash(mode 2)` | `branch0607Puncture` + `puncture` + `slotScale` | lifecycle (Erin, 40 of 100 bits) |
| B8a | T3 absorb top-up (dS_uw) | `topUpAbsorb` | `branch08aUwTopup` | lifecycle |
| B8b | T3 hold expiry (surplus released, un-absorbed bits rewind into B_rem) | `expireHold` | `branch08bHoldExpire` + `holdExpire` | lifecycle |
| B9 | T4 settle (eps burn, Stage 1/2 slots, 4-stage waterfall) | `settle` | `branch09Settle` + `settleTranche` + `m1RedirectRbfPriority` + `rbfProrata` | lifecycle |
| B10 | normal close (B_rem + S_k back) | `closeDataset` | `branch10CloseOk` | lifecycle (dataset 2) |
| B11 | penalized close (B_rem + 30 % S_k back, 70 % burned) | `closeDataset` | `branch11ClosePen` | lifecycle (dataset 1) |
| B12a | RBF sponsorship burn (<= 10 sponsors, >= ceil(B_target / 10), 2.0x debt) | `sponsorRBF` | `branch12to15` | lifecycle (Gina, Ivan) |
| B12b | dictionary stake lock | `stakeDict` | `branch12to15` | lifecycle (Hal, Ivy) |
| B12c | dictionary stake unlock after one epoch of grace | `requestUnstake` + `unstakeDict` | `branch12to15` | lifecycle (Ivy) |
| B13 | T5 epoch update, O(1) | `epochUpdate` | - (no ledger movement) | lifecycle: identical warm gas (< 3,000 difference) with 5 axioms / 2 stakers / 2 sponsors |
| B14 | T6 syntactic reduction (two-phase; B_finder = 30 % of S_audit) | `commit(3, ..)` + `revealReduction` | `branch0607Puncture` | lifecycle (Clone 4A: L_red = 98, Clone 4B: L_red = 77) |
| B15 | vault deposit / withdraw (balance-difference check) | `deposit`, `withdraw` | `branch12to15` (mint) / `redeemed` bucket | lifecycle + fee-on-transfer and mint-cap tests |

Front-running: T1 / T2 / T6 all use one commit-reveal: the commit hash contains `msg.sender`; a copied hash is rejected (`Duplicate`), a stolen reveal is rejected
(`BadReveal`), the zk public values contain the sender, so a proof cannot be reused by anyone else.

## Gas (forge `--gas-report`, lifecycle + focused tests; delegated functions are measured at their ESM entry point)
| function | min | avg | median | max | calls |
|---|---|---|---|---|---|
| `axiomCites` | 15775 | 15775 | 15775 | 15775 | 2 |
| `axiomCore` | 22953 | 22953 | 22953 | 22953 | 12 |
| `batchRoot` | 2721 | 2721 | 2721 | 2721 | 13 |
| `branchHits` | 2911 | 2911 | 2911 | 2911 | 18 |
| `btarget` | 12215 | 12215 | 12215 | 12215 | 1 |
| `claimDict` | 45939 | 45939 | 45939 | 45939 | 1 |
| `closeDataset` | 120270 | 121886 | 121886 | 123503 | 2 |
| `commit` | 29787 | 126597 | 121935 | 202544 | 14 |
| `dataInvariant` | 29262 | 29262 | 29262 | 29262 | 40 |
| `datasetCount` | 2552 | 2552 | 2552 | 2552 | 61 |
| `datasetData` | 36113 | 36113 | 36113 | 36113 | 5 |
| `debtOf` | 2933 | 2933 | 2933 | 2933 | 3 |
| `deposit` | 58217 | 103902 | 96844 | 187244 | 15 |
| `dictLen` | 14252 | 14327 | 14315 | 14416 | 3 |
| `epochUpdate` | 38653 | 57619 | 41453 | 92753 | 3 |
| `expireHold` | 207138 | 207138 | 207138 | 207138 | 1 |
| `finalizeBatch` | 494562 | 573887 | 494663 | 700392 | 5 |
| `flushBurn` | 79375 | 79375 | 79375 | 79375 | 1 |
| `flushedBurn` | 3140 | 3140 | 3140 | 3140 | 2 |
| `forfeitUnrevealed` | 94222 | 94222 | 94222 | 94222 | 1 |
| `phiActive` | 5509 | 5512 | 5512 | 5515 | 2 |
| `proposalHash` | 2555 | 2578 | 2555 | 2720 | 7 |
| `proposalPublicValues` | 22142 | 22169 | 22142 | 22307 | 6 |
| `registerDataset` | 328349 | 371325 | 371325 | 414302 | 2 |
| `requestUnstake` | 114951 | 114951 | 114951 | 114951 | 1 |
| `revealProposal` | 33724 | 287078 | 391434 | 479517 | 9 |
| `revealReduction` | 70154 | 119597 | 135757 | 152881 | 3 |
| `revealSlash` | 221634 | 241716 | 241716 | 261798 | 2 |
| `setPhiDict` | 49088 | 49088 | 49088 | 49088 | 1 |
| `settle` | 344973 | 344973 | 344973 | 344973 | 1 |
| `slashHash` | 2206 | 2206 | 2206 | 2206 | 2 |
| `sponsorRBF` | 153045 | 187251 | 187251 | 221458 | 2 |
| `stakeDict` | 113031 | 147231 | 147231 | 181431 | 2 |
| `supplyInvariant` | 23325 | 23325 | 23325 | 23325 | 24 |
| `t6Hash` | 1356 | 1356 | 1356 | 1356 | 3 |
| `topUpAbsorb` | 159823 | 159823 | 159823 | 159823 | 1 |
| `unstakeDict` | 85869 | 85869 | 85869 | 85869 | 1 |
| `wallet` | 3295 | 3295 | 3295 | 3295 | 30 |
| `withdraw` | 75650 | 86589 | 86878 | 103978 | 13 |

## Implementation parameters that the delivered sources do not fix (explicit choices, constructor / constants)
* `S_c` = 5 % of B_k^(0) (`commitCollateralBps`), `S_uw` = sigma_col x (escrow of the claimed reduction), `S_audit` = constructor value, `phi_guar` = constructor value
  (the guarantor is the proposer), `eps_0` (Shannon smoothing) = constructor value, `eps_DA` = wei per bit (constructor).
* Candidate / commit / unsettled-axiom caps: 8 / 64 per batch / 8 per dataset; launch-profile fuel cap `DELTA_CAP_V1 = 65536` for T6.
* Public-value layouts of the three zk programs (`proposalPublicValues`, T2 and T6 encodings in `ESM.sol` / `ESMOps.sol`) are the contract's convention: the
  esm-core guest must commit exactly those values. Tests use `MockVerifier`; `SP1VerifierAdapter` is written against the SP1 gateway interface and is untested
  against a real verifier.

## Simplifications and limits (read before relying on this)
* (Resolved in step 5, see `step5_report.md`) T2 used to be refused while an absorbed reservation (`dAbs`) was pending; the derivative-side reservation `xu`
  of `release_symmetric` used to be untracked; S_c used to be a fixed 5 % of B0 and the underwriter was always the proposer.
  Settlement splits the initial escrow between axioms proportionally to their remaining reduction.
* The dictionary dividend is paid from a pool with a MasterChef accumulator; stake counts immediately, the share parameter phi_dict and the Shannon weights follow the
  epoch (delayed activation / epoch-start snapshot). Dust of floor divisions stays in the pool (still counted as wallets).
* `withdraw` is outside the 12 Lean branches (Lean models `minted` as monotone): it is covered by the extended invariant with a `redeemed` bucket.
* Time is `_now()` = `block.number`; on Arbitrum override it with the L1 block number (params.toml `[time]`). No admin keys except the registry guardian (time limited).
* Not done: a security audit, formal verification of the Solidity (the Lean proofs cover the arithmetic that it calls, not the storage code), upgrade / migration
  path, front-end indexer, and an end-to-end run with the real SP1 / drand verifiers.
