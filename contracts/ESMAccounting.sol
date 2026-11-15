// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {ESMMath as M} from "./ESMMath.sol";

/// @title ESMAccounting
/// @notice `DataState` (T0..T4 transitions), list-based `ListDataState` and `SupplyState` (ledger transactions),
///         ported field for field and operation for operation from `ESM_verified.lean`.
/// @dev `step*` functions are the raw Lean definitions (total, with `monus`); the guarded entry points
///      (`adopt`, `puncture`, `holdExpire`, `settleInit`, `settleAbs`, branch functions) check the hypotheses of the
///      corresponding Lean theorem and revert otherwise, so a state that satisfies the invariant stays inside it.
library ESMAccounting {
    uint256 internal constant MAX_TRANCHES = 1024; // contract-level bound on the tranche list (Lean: unbounded List)

    error InvariantBroken(uint8 code);

    // ================================================================== DataState (12 fields)
    struct DataState {
        uint256 B0;
        uint256 Phi0;
        uint256 PhiBest;
        uint256 dInit;
        uint256 dAbs;
        uint256 dHold;
        uint256 dSettled;
        uint256 eInit;
        uint256 eAbs;
        uint256 eHold;
        uint256 eSettled;
        uint256 BRem;
    }

    function copy(DataState memory s) internal pure returns (DataState memory r) {
        r.B0 = s.B0;
        r.Phi0 = s.Phi0;
        r.PhiBest = s.PhiBest;
        r.dInit = s.dInit;
        r.dAbs = s.dAbs;
        r.dHold = s.dHold;
        r.dSettled = s.dSettled;
        r.eInit = s.eInit;
        r.eAbs = s.eAbs;
        r.eHold = s.eHold;
        r.eSettled = s.eSettled;
        r.BRem = s.BRem;
    }

    /// @dev frozen ranges: tokens < 2^96, bit quantities <= 2^40
    function checkBounds(DataState memory s) internal pure {
        M.tok(s.B0);
        M.tok(s.eInit);
        M.tok(s.eAbs);
        M.tok(s.eHold);
        M.tok(s.eSettled);
        M.tok(s.BRem);
        M.bt(s.Phi0);
        M.bt(s.PhiBest);
        M.bt(s.dInit);
        M.bt(s.dAbs);
        M.bt(s.dHold);
        M.bt(s.dSettled);
    }

    /// @dev DataInv: phi0_pos, best_ge_1, front_eq, init/abs/hold/set bounds, pool_cons (8 conjuncts, returned as a bitmask of FAILED ones)
    function invFailures(DataState memory s) internal pure returns (uint256 failed) {
        if (!(s.Phi0 > 0)) failed |= 1;
        if (!(s.PhiBest >= 1)) failed |= 2;
        if (s.PhiBest + (s.dInit + s.dAbs) + s.dHold + s.dSettled != s.Phi0) failed |= 4;
        if (s.eInit > M.escrowAlloc(s.B0, s.Phi0, s.dInit)) failed |= 8;
        if (s.eAbs > M.escrowAlloc(s.B0, s.Phi0, s.dAbs)) failed |= 16;
        if (s.eHold > M.escrowAlloc(s.B0, s.Phi0, s.dHold)) failed |= 32;
        if (s.eSettled > M.escrowAlloc(s.B0, s.Phi0, s.dSettled)) failed |= 64;
        if (s.BRem + s.eHold + (s.eInit + s.eAbs) + s.eSettled != s.B0) failed |= 128;
    }

    function dataInv(DataState memory s) internal pure returns (bool) {
        return invFailures(s) == 0;
    }

    /// @dev pool lower bound (DataInv.pool_lower): B_rem >= ceilDiv(B0 * Phi_best, Phi0)
    function poolLowerBound(DataState memory s) internal pure returns (uint256) {
        return M.ceilDiv(M.tok(s.B0) * M.bt(s.PhiBest), s.Phi0);
    }

    // ---- T3 adopt
    function stepAdopt(DataState memory s, uint256 phiNew, uint256 bNew) internal pure returns (DataState memory r) {
        r = copy(s);
        uint256 dNew = M.monus(s.PhiBest, phiNew);
        r.PhiBest = phiNew;
        r.dInit = s.dInit + dNew;
        r.eInit = s.eInit + bNew;
        r.BRem = M.monus(s.BRem, bNew);
    }

    /// @dev hypotheses of stepAdopt_preserves_inv: Phi_new >= 1, Phi_new < Phi_best, b_new <= EscrowAlloc(B0, Phi0, Phi_best - Phi_new)
    function adopt(DataState memory s, uint256 phiNew, uint256 bNew) internal pure returns (DataState memory r) {
        if (!(phiNew >= 1)) revert M.Precondition(21);
        if (!(phiNew < s.PhiBest)) revert M.Precondition(22);
        if (bNew > M.escrowAlloc(s.B0, s.Phi0, s.PhiBest - phiNew)) revert M.Precondition(23);
        r = stepAdopt(s, phiNew, bNew);
        checkBounds(r);
    }

    // ---- T2 puncture
    function stepPunctureConcrete(DataState memory s, uint256 dUnroll) internal pure returns (DataState memory r) {
        r = copy(s);
        uint256 dTotal = s.dInit + s.dAbs;
        uint256 dRem = M.monus(dTotal, dUnroll);
        uint256 dRemInit = M.min(s.dInit, dRem);
        uint256 dRemAbs = M.monus(dRem, dRemInit);
        uint256 eTotal = s.eInit + s.eAbs;
        uint256 eRemI = M.safeRemEscrow(s.B0, s.Phi0, s.eInit, s.dInit, dRemInit);
        uint256 eRemA = M.safeRemEscrow(s.B0, s.Phi0, s.eAbs, s.dAbs, dRemAbs);
        uint256 eRem = eRemI + eRemA;
        uint256 eUnroll = M.min(M.monus(eTotal, eRem), M.escrowAlloc(s.B0, s.Phi0, dUnroll));
        uint256 eDust = M.monus(M.monus(eTotal, eRem), eUnroll);
        r.dInit = dRemInit;
        r.dAbs = dRemAbs;
        r.dHold = s.dHold + dUnroll;
        r.eInit = eRemI;
        r.eAbs = eRemA;
        r.eHold = s.eHold + eUnroll;
        r.BRem = s.BRem + eDust;
    }

    /// @dev hypothesis of stepPuncture_concrete_preserves_inv: d_unroll <= d_init + d_abs
    function puncture(DataState memory s, uint256 dUnroll) internal pure returns (DataState memory r) {
        if (dUnroll > s.dInit + s.dAbs) revert M.Precondition(24);
        r = stepPunctureConcrete(s, dUnroll);
        checkBounds(r);
    }

    /// @dev T2 puncture of a tranche that lives in the INITIAL window (the slashed axiom's own reduction), with the absorbed window
    ///      untouched: d_rem_init = d_init - d_unroll, d_rem_abs = d_abs. `trancheUnroll` (tranche_unroll_conserves_and_bounds) is proved for every
    ///      split with d_rem_init + d_rem_abs + d_unroll = d_init + d_abs, so DataInv is preserved exactly as for `stepPunctureConcrete`
    ///      (which instead keeps the initial window first, i.e. unrolls the absorbed window first). Used by ESMOps so that an existing
    ///      absorbed reservation (d_abs > 0) can never shield a fraudulent axiom from T2.
    function stepPunctureInit(DataState memory s, uint256 dUnroll) internal pure returns (DataState memory r) {
        r = copy(s);
        uint256 dRemInit = M.monus(s.dInit, dUnroll);
        M.Unroll memory u = M.trancheUnroll(s.B0, s.Phi0, s.eInit, s.eAbs, s.dInit, s.dAbs, dRemInit, s.dAbs, dUnroll);
        r.dInit = dRemInit;
        r.dHold = s.dHold + dUnroll;
        r.eInit = u.eRemI;
        r.eAbs = u.eRemA;
        r.eHold = s.eHold + u.eUnroll;
        r.BRem = s.BRem + u.eDust;
    }

    /// @dev hypothesis: d_unroll <= d_init
    function punctureInit(DataState memory s, uint256 dUnroll) internal pure returns (DataState memory r) {
        if (dUnroll > s.dInit) revert M.Precondition(24);
        r = stepPunctureInit(s, dUnroll);
        checkBounds(r);
    }

    // ---- T4 hold expiry
    function stepHoldExpire(DataState memory s, uint256 dAbsAdd) internal pure returns (DataState memory r) {
        r = copy(s);
        uint256 dRewind = M.monus(s.dHold, dAbsAdd);
        uint256 eAbsAdd =
            s.dHold == 0 ? 0 : M.min((s.eHold * dAbsAdd) / s.dHold, M.escrowAlloc(s.B0, s.Phi0, dAbsAdd));
        uint256 eRet = M.monus(s.eHold, eAbsAdd);
        r.PhiBest = s.PhiBest + dRewind;
        r.dAbs = s.dAbs + dAbsAdd;
        r.dHold = 0;
        r.eAbs = s.eAbs + eAbsAdd;
        r.eHold = 0;
        r.BRem = s.BRem + eRet;
    }

    /// @dev hypothesis of stepHoldExpire_concrete_preserves_inv: d_abs_add <= d_hold
    function holdExpire(DataState memory s, uint256 dAbsAdd) internal pure returns (DataState memory r) {
        if (dAbsAdd > s.dHold) revert M.Precondition(25);
        r = stepHoldExpire(s, dAbsAdd);
        checkBounds(r);
    }

    // ---- settlement of the initial / absorbed reservations
    function stepSettleInit(DataState memory s) internal pure returns (DataState memory r) {
        r = copy(s);
        r.dInit = 0;
        r.dSettled = s.dSettled + s.dInit;
        r.eInit = 0;
        r.eSettled = s.eSettled + s.eInit;
    }

    function stepSettleAbs(DataState memory s) internal pure returns (DataState memory r) {
        r = copy(s);
        r.dAbs = 0;
        r.dSettled = s.dSettled + s.dAbs;
        r.eAbs = 0;
        r.eSettled = s.eSettled + s.eAbs;
    }

    function settleInit(DataState memory s) internal pure returns (DataState memory r) {
        r = stepSettleInit(s);
        checkBounds(r);
    }

    function settleAbs(DataState memory s) internal pure returns (DataState memory r) {
        r = stepSettleAbs(s);
        checkBounds(r);
    }

    // ================================================================== ListDataState (tranche list; head = LAST array element)
    struct Tranche {
        uint256 d;
        uint256 e;
    }

    struct ListDataState {
        uint256 B0;
        uint256 Phi0;
        uint256 PhiBest;
        Tranche[] tranches; // Lean `tr :: tl`  <->  array [.., tl.., tr]  (push / pop at the end)
        uint256 dHold;
        uint256 dSettled;
        uint256 eHold;
        uint256 eSettled;
        uint256 BRem;
    }

    function sumTrancheD(Tranche[] memory t) internal pure returns (uint256 s) {
        if (t.length > MAX_TRANCHES) revert M.ListTooLong(t.length);
        for (uint256 i = 0; i < t.length; ++i) s += t[i].d;
    }

    function sumTrancheE(Tranche[] memory t) internal pure returns (uint256 s) {
        if (t.length > MAX_TRANCHES) revert M.ListTooLong(t.length);
        for (uint256 i = 0; i < t.length; ++i) s += t[i].e;
    }

    function allTranchesBounded(uint256 B0, uint256 Phi0, Tranche[] memory t) internal pure returns (bool) {
        for (uint256 i = 0; i < t.length; ++i) {
            if (t[i].e > M.escrowAlloc(B0, Phi0, t[i].d)) return false;
        }
        return true;
    }

    function listDataInv(ListDataState memory s) internal pure returns (bool) {
        return s.Phi0 > 0 && s.PhiBest >= 1 && s.PhiBest + sumTrancheD(s.tranches) + s.dHold + s.dSettled == s.Phi0
            && allTranchesBounded(s.B0, s.Phi0, s.tranches) && s.eHold <= M.escrowAlloc(s.B0, s.Phi0, s.dHold)
            && s.eSettled <= M.escrowAlloc(s.B0, s.Phi0, s.dSettled)
            && s.BRem + s.eHold + sumTrancheE(s.tranches) + s.eSettled == s.B0;
    }

    function stepAdoptList(ListDataState memory s, uint256 phiNew, uint256 bNew)
        internal
        pure
        returns (ListDataState memory r)
    {
        if (s.tranches.length >= MAX_TRANCHES) revert M.ListTooLong(s.tranches.length + 1);
        r.B0 = s.B0;
        r.Phi0 = s.Phi0;
        r.PhiBest = phiNew;
        r.dHold = s.dHold;
        r.dSettled = s.dSettled;
        r.eHold = s.eHold;
        r.eSettled = s.eSettled;
        r.BRem = M.monus(s.BRem, bNew);
        r.tranches = new Tranche[](s.tranches.length + 1);
        for (uint256 i = 0; i < s.tranches.length; ++i) r.tranches[i] = s.tranches[i];
        r.tranches[s.tranches.length] = Tranche({d: M.monus(s.PhiBest, phiNew), e: bNew});
    }

    function stepSettleHead(ListDataState memory s) internal pure returns (ListDataState memory r) {
        r.B0 = s.B0;
        r.Phi0 = s.Phi0;
        r.PhiBest = s.PhiBest;
        r.dHold = s.dHold;
        r.dSettled = s.dSettled;
        r.eHold = s.eHold;
        r.eSettled = s.eSettled;
        r.BRem = s.BRem;
        uint256 n = s.tranches.length;
        if (n == 0) {
            r.tranches = new Tranche[](0);
            return r;
        }
        Tranche memory head = s.tranches[n - 1];
        r.tranches = new Tranche[](n - 1);
        for (uint256 i = 0; i + 1 < n; ++i) r.tranches[i] = s.tranches[i];
        r.dSettled = s.dSettled + head.d;
        r.eSettled = s.eSettled + head.e;
    }

    // ================================================================== SupplyState (global conservation)
    struct SupplyState {
        uint256 wallets;
        uint256 locked;
        uint256 burned;
        uint256 minted;
    }

    function supplyInv(SupplyState memory s) internal pure returns (bool) {
        return s.wallets + s.locked + s.burned == s.minted;
    }

    /// @dev applyLedgerTx s w_out w_in l_out l_in b_add m_add  (Lean `Nat` subtraction => monus), then the frozen mint cap
    function applyLedgerTx(
        SupplyState memory s,
        uint256 wOut,
        uint256 wIn,
        uint256 lOut,
        uint256 lIn,
        uint256 bAdd,
        uint256 mAdd
    ) internal pure returns (SupplyState memory r) {
        r.wallets = M.monus(s.wallets, wOut) + wIn;
        r.locked = M.monus(s.locked, lOut) + lIn;
        r.burned = s.burned + bAdd;
        r.minted = s.minted + mAdd;
        M.tok(r.minted); // minted bounds every other component through the invariant
        M.tok(r.wallets);
        M.tok(r.locked);
        M.tok(r.burned);
    }

    /// @dev global_supply_invariant_preserved: hypotheses w_out <= wallets, l_out <= locked, w_out + l_out + m_add = w_in + l_in + b_add
    function ledgerTx(
        SupplyState memory s,
        uint256 wOut,
        uint256 wIn,
        uint256 lOut,
        uint256 lIn,
        uint256 bAdd,
        uint256 mAdd
    ) internal pure returns (SupplyState memory r) {
        if (wOut > s.wallets) revert M.Precondition(31);
        if (lOut > s.locked) revert M.Precondition(32);
        if (wOut + lOut + mAdd != wIn + lIn + bAdd) revert M.Precondition(33);
        r = applyLedgerTx(s, wOut, wIn, lOut, lIn, bAdd, mAdd);
    }

    // ---- the 12 branch theorems (each is `ledgerTx` with the argument pattern of the Lean statement)
    function branch01T0(SupplyState memory s, uint256 B0, uint256 Sk, uint256 burnDa, uint256 fee)
        internal
        pure
        returns (SupplyState memory)
    {
        return ledgerTx(s, B0 + Sk + burnDa + fee, fee, 0, B0 + Sk, burnDa, 0);
    }

    function branch02Commit(SupplyState memory s, uint256 Sc, uint256 gTx) internal pure returns (SupplyState memory) {
        return ledgerTx(s, Sc + gTx, gTx, 0, Sc, 0, 0);
    }

    function branch03Adopt(SupplyState memory s, uint256 Sst, uint256 burnDa, uint256 Bam, uint256 fee)
        internal
        pure
        returns (SupplyState memory)
    {
        return ledgerTx(s, Sst + burnDa + Bam + fee, fee, 0, Sst, burnDa + Bam, 0);
    }

    function branch04Reject(SupplyState memory s, uint256 Sc, uint256 Sst, uint256 burnDa, uint256 fee)
        internal
        pure
        returns (SupplyState memory)
    {
        return ledgerTx(s, Sst + burnDa + fee, Sc + Sst + fee, Sc, 0, burnDa, 0);
    }

    /// @dev unrevealed commit: ref = floor(0.30 S_c) back to the wallet, the rest burned
    function branch05Unrevealed(SupplyState memory s, uint256 Sc) internal pure returns (SupplyState memory) {
        uint256 ref = M.refund30(Sc);
        return ledgerTx(s, 0, ref, Sc, 0, Sc - ref, 0);
    }

    function branch0607Puncture(SupplyState memory s, uint256 Scut, uint256 Spay, uint256 Sburn, uint256 fee)
        internal
        pure
        returns (SupplyState memory)
    {
        if (Spay + Sburn != Scut) revert M.Precondition(34);
        return ledgerTx(s, fee, Spay + fee, Scut, 0, Sburn, 0);
    }

    function branch08aUwTopup(SupplyState memory s, uint256 dSuw, uint256 gTx) internal pure returns (SupplyState memory) {
        return ledgerTx(s, dSuw + gTx, gTx, 0, dSuw, 0, 0);
    }

    function branch08bHoldExpire(SupplyState memory s, uint256 dSexcess) internal pure returns (SupplyState memory) {
        return ledgerTx(s, 0, dSexcess, dSexcess, 0, 0, 0);
    }

    function branch09Settle(SupplyState memory s, uint256 eTr, uint256 sUnlock, uint256 eBurn, uint256 payouts)
        internal
        pure
        returns (SupplyState memory)
    {
        if (eBurn + payouts != eTr) revert M.Precondition(35);
        return ledgerTx(s, 0, payouts + sUnlock, eTr + sUnlock, 0, eBurn, 0);
    }

    function branch10CloseOk(SupplyState memory s, uint256 bRem, uint256 Sk) internal pure returns (SupplyState memory) {
        return ledgerTx(s, 0, bRem + Sk, bRem + Sk, 0, 0, 0);
    }

    function branch11ClosePen(SupplyState memory s, uint256 bRem, uint256 Sk) internal pure returns (SupplyState memory) {
        uint256 ref = M.refund30(Sk);
        return ledgerTx(s, 0, bRem + ref, bRem + Sk, 0, Sk - ref, 0);
    }

    function branch12to15(SupplyState memory s, uint256 S_, uint256 lockOut, uint256 bBurn, uint256 mMint, uint256 fee)
        internal
        pure
        returns (SupplyState memory)
    {
        return ledgerTx(s, S_ + bBurn + fee, lockOut + mMint + fee, lockOut, S_, bBurn, mMint);
    }
}
