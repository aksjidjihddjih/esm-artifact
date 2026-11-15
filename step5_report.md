# Step 5 - four spec-gap fixes + stateful invariant fuzzing

Scope: `contracts/` only (Lean, esm-core, zkvm-sim untouched). `forge test`: **104 tests pass** (94 of Steps 0-4 + 10 new: 6 gap tests, 1 scripted coverage test, 3 invariants).
Contract sizes (EIP-170 limit 24,576): `ESM` 23,721 B, `ESMOps` 16,237 B.

## 1. The four gaps

| # | Spec | Change |
|---|------|--------|
| 1 | Theorem 5.3 (3)(4): S_c caps the claimable escrow | `commit(kind, ref, h, sCreator)`; for T1 `sCreator >= ceil(commitCollateralBps * B0 / 10000)` (spam floor, `Rejected(18)`), kinds 2/3 must pass 0 (`Rejected(23)`). `ESMStorage._admission`: `E_tr <= 10000 (10000 + lambdaBps) S_c / (10000 sigma_col)` (Lambda = 0: `S_c >= E_tr`; Lambda = 1: `S_c >= ceil(E_tr/2)`), else `Rejected(19)`. Enforced at the reveal **and again when the batch winner is chosen** (`_eligible`): an inadmissible candidate is rejected with the normal refund path instead of reverting `finalizeBatch` (no batch DoS). New parameter `Params.lambdaBps` in {0, 10000}. |
| 2 | Lemma 6.1 `release_symmetric` on Mode III | New per-axiom Stage-1 counter `Axiom.sPaid` (charged `x` per citation slot at adoption, capped by the cited axiom's saving: `Rejected(22)`). Mode III: `u.sPaid = symmetricRelease(sPaid - x, xs, xu, dRem, dTr)` (the derivative loses delta-xs + delta-xu) **and** the root's `rootCapLeft += delta-xs`. Mode II-A releases the whole slot from both. Stored slots become `xs' + xu'` (xs, xu scaled separately, exactly the lemma). |
| 3 | Extension 2: external underwriter | `Reveal.underwriter` (0 = proposer) and `Reveal.suw <= Lambda S_c` (`Rejected(20)`). The underwriter must have called `setUnderwriterConsent(proposer, true)` (`Rejected(21)`); S_uw is locked from **its** wallet. `Axiom.underwriter` receives **R_guar** and the **S_uw refund** at settlement; a rejected candidate refunds S_uw to it; Mode II-A slashes S_c + S_uw as before. S_uw is now an explicit, optional co-stake (it used to be forced to sigma_col * E_tr). |
| 4 | T2 with `dAbs > 0` | The `Rejected(5)` guard is gone. `ESMAccounting.punctureInit` / `stepPunctureInit` unroll the **initial** window (`d_rem_init = d_init - d_unroll`, `d_rem_abs = d_abs`) through `M.trancheUnroll`, which `tranche_unroll_conserves_and_bounds` proves for every split with `d_rem_init + d_rem_abs + d_unroll = d_init + d_abs`; so DataInv holds as for `stepPunctureConcrete`, but the slashed axiom's bits leave the window they live in (the literal `stepPunctureConcrete` unrolls the absorbed window first, which would leave `sum dNew != dInit` and brick `settle`). `topUpAbsorb` is refused while an absorbed claim exists (one claimant, so `absClaimant/absSuw` cannot be overwritten). |

Tests: `test_gap1_*` (both Lambda), `test_gap2_*` (counters, root cap restored after II-A), `test_gap3_*`, `test_gap4_*` (T2 II-A/III with `dAbs > 0`, then settle).
The lifecycle test was adapted to the new API (explicit S_c, S_uw, a fully amortized clone that can be cited).

## 2. Stateful invariant fuzzing (`contracts/test/ESMInvariant.t.sol`)

`ESMHandler` (forge-std-free; `targetContracts()` returns it) exposes the 18 schemas with fuzzed arguments and random actors:
deposit, withdraw, registerDataset, commit, revealProposal, finalizeBatch, forfeitUnrevealed, revealReduction, sponsorRBF, stakeDict, requestUnstake,
unstakeDict, revealSlash (mode II-A / III), topUpAbsorb, expireHold, settle, closeDataset, epochUpdate; plus `advance`, `flushBurn`, `claimDict` and two composites
(`adoptAxiom` = commit+reveal+finalize, `slashAndAbsorb` = Mode III + top-up + hold expiry). It keeps its own monotone clock (the via-IR optimizer may reuse `block.number` across `roll`),
calls the protocol with low-level calls (a rejected action is a no-op) and deliberately builds inadmissible inputs (small S_c, S_uw > Lambda S_c, uncapped citations).

After every call sequence: `invariant_supplyConservation` (`esm.supplyInvariant()`: wallets + locked + burned + redeemed == minted **and** the ledger equals the real ERC-20 balance),
`invariant_allDatasetsValid` (`dataInvariant(k)` for all k + `B_rem >= ceil(B0 Phi_best / Phi0)`), `invariant_rootCapBounded` (`sPaid(v, D_k) <= deltaAmort(v, D_k)` for all axioms and datasets, plus `S_paid <= Saved <= Delta_amort`, `R_cap <= Saved`).
Config (`foundry.toml`): 256 runs x depth 128 = 32,768 calls per invariant, `fail_on_revert = false`; all three pass.

Anti-vacuity: `test_handler_reaches_every_schema` drives the handler through a scripted run and requires all 18 actions, both T2 modes, a T2 with `dAbs > 0` and an admission rejection to succeed.
In addition, during development each action was probed with a temporary "reached?" invariant (made to fail on first success): the fuzzer itself reached all 18 actions, both T2 modes, T2 with `dAbs > 0` and admission rejections (the probe file was removed).

## 3. Known limits
* Axioms are measured against their home dataset only (`sPaid(v, D_k) = 0` for k != home), as in Steps 0-4; a cross-dataset amortization model is not implemented.
* `Params.commitCollateralBps` is now only the spam floor of S_c; the economic lower bound is the Theorem 5.3 cap. S_uw is optional (it is no longer forced to sigma_col * E_tr), so the slashable collateral of a Lambda = 0 proposal is S_c >= E_tr only.
* ~0.3 % of the fuzzed calls revert inside the handler itself (not in the protocol); they are ignored (`fail_on_revert = false`).
* Still not done: audit, Solidity-level formal verification, real SP1/drand verifiers (see `step4_report.md`).
