// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {ESMMath as M} from "./ESMMath.sol";
import {ESMAccounting as A} from "./ESMAccounting.sol";
import {IERC20, IVerifierRegistry, ISeedBeacon, IArchiveRegistry} from "./Interfaces.sol";
import {ESMStorage} from "./ESMStorage.sol";

/// @title ESMOps - settlement / slashing / hold / close / RBF module of ESM, executed through `delegatecall` from ESM (same storage layout)
/// @dev split out of ESM to stay below the EIP-170 limit (24,576 bytes). The reentrancy guard is taken by the ESM forwarder.
contract ESMOps is ESMStorage {
    address private immutable SELF = address(this);

    error NotDelegated();

    modifier onlyDelegated() {
        if (address(this) == SELF) revert NotDelegated();
        _;
    }

    constructor(IERC20 asset_, IVerifierRegistry v_, ISeedBeacon b_, IArchiveRegistry a_, uint256 genesis_)
        ESMStorage(asset_, v_, b_, a_, genesis_, Params(0, 0, 0, 0, 0, 0))
    {}

    // ================================================================== T2: [B6] mode II-A full slash / [B7] mode III partial puncture
    function revealSlash(RevealT2 calldata r) external onlyDelegated {
        bytes32 h = slashHash(msg.sender, r);
        Commit storage c = commits[h];
        uint256 t = _now();
        if (c.who != msg.sender || c.kind != 2 || c.revealed || c.ref != r.axiomId) revert BadReveal();
        if (t <= c.blk || t > c.blk + N_REV_T6) revert WrongPhase();
        Axiom storage a = ax[r.axiomId];
        if (!a.active || a.settled) revert BadAxiom();
        bytes memory pv = abi.encode(uint8(2), r.mode, r.axiomId, a.dataset, archive.rootOf(a.dataset), a.programHash, r.dUnroll, r.blameDataset, r.evidence, msg.sender);
        if (!verifiers.verify(2, r.vkVersion, pv, r.proof)) revert BadProof();
        c.revealed = true;
        if (r.mode == 1) _slashFull(r.axiomId, r.blameDataset);
        else if (r.mode == 2) _slashPartial(r.axiomId, r.dUnroll);
        else revert BadKind();
        _chk();
    }

    function _startHold(Dataset storage D) internal {
        if (D.holdStart == 0) D.holdStart = uint64(_now());
    }

    function _slashFull(uint32 aid, bool blame) internal {
        Axiom storage a = ax[aid];
        Dataset storage D = ds[a.dataset];
        uint256 total = a.sc + a.suw; // creator + underwriter collateral
        M.Slash memory sl = M.slashSplit(BPS, total, KAPPA_BPS); // 30 % to the hunter, 70 % burned
        A.SupplyState memory s = A.branch0607Puncture(supply, total, sl.hunter, sl.burn, 0);
        supply = A.ledgerTx(s, 0, a.saudit, a.saudit, 0, 0, 0); // the audit deposit goes back to the proposer
        _credit(msg.sender, sl.hunter);
        _credit(a.proposer, a.saudit);
        a.sc = 0;
        a.suw = 0;
        a.saudit = 0;
        uint256 dTr = a.dNew;
        D.d = A.punctureInit(D.d, dTr); // the whole tranche is rolled back into the hold window (an absorbed window d_abs > 0 is left alone)
        for (uint256 j = 0; j < a.citeIds.length; ++j) {
            if (a.citeRoot[j] != a.citeIds[j]) {
                Axiom storage ro = ax[a.citeRoot[j]];
                ro.rootCapLeft = M.symmetricRelease(ro.rootCapLeft, a.citeXis[j], 0, dTr, dTr); // r = d: release everything that was reserved
            }
            ax[a.citeIds[j]].sPaid -= a.citeBits[j]; // derivative-side counter: the whole slot (delta xs + delta xu) is released
            a.citeBits[j] = 0;
            a.citeXis[j] = 0;
        }
        a.dNew = 0;
        a.active = false;
        _removeUnsettled(D, aid);
        _startHold(D);
        if (blame) D.penalized = true;
        _hit(B6, aid, msg.sender, total);
    }

    function _slashPartial(uint32 aid, uint256 dUnroll) internal {
        Axiom storage a = ax[aid];
        Dataset storage D = ds[a.dataset];
        uint256 dTr = a.dNew;
        if (dUnroll < 1 || dUnroll >= dTr) revert Rejected(6);
        uint256 dRem = dTr - dUnroll;
        uint256 cut = M.min(a.sc, M.div0(a.sc0 * dUnroll, a.dNew0)); // time-invariant denominator: the INITIAL reduction; S_uw untouched
        M.Slash memory sl = M.slashSplit(BPS, cut, KAPPA_BPS);
        supply = A.branch0607Puncture(supply, cut, sl.hunter, sl.burn, 0);
        _credit(msg.sender, sl.hunter);
        a.sc -= cut;
        D.d = A.punctureInit(D.d, dUnroll);
        for (uint256 j = 0; j < a.citeIds.length; ++j) {
            uint256 x = a.citeBits[j];
            uint256 xs = a.citeXis[j]; // redirected to the root (== x for a directly cited root)
            uint256 xu = x - xs; // kept by the derivative
            uint256 xsNew = M.slotScale(xs, dRem, dTr);
            uint256 xuNew = M.slotScale(xu, dRem, dTr);
            Axiom storage u = ax[a.citeIds[j]];
            // release_symmetric: the derivative's S_paid = base + xs + xu drops by (delta xs + delta xu) = base + xs' + xu', no capacity leaks
            u.sPaid = M.symmetricRelease(u.sPaid - x, xs, xu, dRem, dTr);
            if (a.citeRoot[j] != a.citeIds[j]) ax[a.citeRoot[j]].rootCapLeft += xs - xsNew; // the root gets delta xs back
            a.citeBits[j] = xsNew + xuNew;
            a.citeXis[j] = xsNew;
        }
        a.dNew = dRem;
        _startHold(D);
        _hit(B7, aid, msg.sender, cut);
    }

    function _removeUnsettled(Dataset storage D, uint32 aid) internal {
        uint256 n = D.unsettled.length;
        for (uint256 i = 0; i < n; ++i) {
            if (D.unsettled[i] == aid) {
                D.unsettled[i] = D.unsettled[n - 1];
                D.unsettled.pop();
                return;
            }
        }
        revert InvariantBroken(2);
    }

    // ================================================================== T3: [B8A] absorb top-up / [B8B] hold expiry
    function topUpAbsorb(uint32 id, uint256 dAbsAdd) external onlyDelegated {
        Dataset storage D = ds[id];
        HoldClaim storage cl = claims[id];
        if (D.d.dHold == 0 || _now() >= D.holdStart + N_HOLD || cl.who != address(0) || D.d.dAbs != 0) revert Rejected(7); // one absorbed claim at a time
        if (dAbsAdd < 1 || dAbsAdd > D.d.dHold) revert Rejected(8);
        uint256 dSuw = (SIGMA_COL_BPS * M.escrowAlloc(D.d.B0, D.d.Phi0, dAbsAdd)) / BPS;
        supply = A.branch08aUwTopup(supply, dSuw, 0);
        _debit(msg.sender, dSuw);
        cl.who = msg.sender;
        cl.dAbs = dAbsAdd;
        cl.dSuw = dSuw;
        _hit(B8A, id, msg.sender, dSuw);
        _chk();
    }

    function expireHold(uint32 id) external onlyDelegated {
        Dataset storage D = ds[id];
        if (D.d.dHold == 0 || _now() < D.holdStart + N_HOLD) revert WrongPhase();
        HoldClaim memory cl = claims[id];
        A.DataState memory before = D.d;
        A.DataState memory after_ = A.holdExpire(before, cl.dAbs);
        uint256 eAbsAdd = after_.eAbs - before.eAbs;
        uint256 excess = M.monus(cl.dSuw, (SIGMA_COL_BPS * eAbsAdd) / BPS);
        supply = A.branch08bHoldExpire(supply, excess); // surplus collateral is released, un-absorbed bits rewind into B_rem
        if (cl.who != address(0)) {
            _credit(cl.who, excess);
            if (cl.dAbs > 0) {
                D.absClaimant = cl.who;
                D.absSuw = cl.dSuw - excess;
                D.absAt = uint64(_now());
            } else {
                _credit(cl.who, cl.dSuw - excess);
                supply = A.ledgerTx(supply, 0, cl.dSuw - excess, cl.dSuw - excess, 0, 0, 0);
            }
        }
        D.d = after_;
        D.holdStart = 0;
        delete claims[id];
        _hit(B8B, id, cl.who, excess);
        _chk();
    }

    // ================================================================== [B9] T4 settlement
    function settle(uint32 id) external onlyDelegated {
        Dataset storage D = ds[id];
        if (D.status != 1) revert BadDataset();
        A.DataState memory d = D.d;
        uint256 n = D.unsettled.length;
        uint256 t = _now();
        if (d.dHold != 0 || (n == 0 && d.dAbs == 0)) revert Rejected(10);
        uint256 sumD;
        for (uint256 i = 0; i < n; ++i) {
            Axiom storage a = ax[D.unsettled[i]];
            if (t < a.adoptedAt + N_LOCK) revert Rejected(11);
            sumD += a.dNew;
        }
        if (sumD != d.dInit) revert InvariantBroken(3);
        if (d.dAbs != 0 && t < D.absAt + N_LOCK) revert Rejected(12);
        uint256 burn;
        uint256 payouts;
        uint256 unlock;
        uint256 left = d.eInit;
        for (uint256 i = 0; i < n; ++i) {
            uint32 aid = D.unsettled[i];
            Axiom storage a = ax[aid];
            uint256 e = i + 1 == n ? left : (d.eInit * a.dNew) / sumD;
            left -= e;
            (uint256 b, uint256 p) = _settleAxiom(aid, e);
            burn += b;
            payouts += p;
            unlock += a.sc + a.suw + a.saudit;
            _credit(a.proposer, a.sc + a.saudit);
            _credit(a.underwriter, a.suw); // the co-stake goes back to the underwriter wallet
            a.sc = 0;
            a.suw = 0;
            a.saudit = 0;
            a.settled = true;
        }
        if (d.dAbs != 0) {
            M.Settle memory S = M.settleTranche(d.eAbs, d.dAbs, EPS_BPS, GAMMA_BPS, params.phiGuarBps, new uint256[](0));
            burn += S.burn;
            payouts += S.net;
            _credit(D.absClaimant, S.net + D.absSuw);
            unlock += D.absSuw;
            D.absSuw = 0;
        }
        delete D.unsettled;
        supply = A.branch09Settle(supply, d.eInit + d.eAbs, unlock, burn, payouts);
        d = A.settleInit(d);
        D.d = A.settleAbs(d);
        _hit(B9, id, msg.sender, payouts);
        _chk();
    }

    function _settleAxiom(uint32 aid, uint256 eTr) internal returns (uint256 burn, uint256 payout) {
        Axiom storage a = ax[aid];
        M.Settle memory S = M.settleTranche(eTr, a.dNew, EPS_BPS, GAMMA_BPS, params.phiGuarBps, a.citeBits);
        uint256 paid;
        for (uint256 j = 0; j < a.citeIds.length; ++j) {
            uint32 k = a.citeIds[j];
            uint32 o = ax[k].origin;
            uint256 x = a.citeBits[j];
            if (o == k) {
                paid += _slot(k, k, M.slotRoyalty(GAMMA_BPS, S.net, x, a.dNew), ax[k].proposer);
            } else {
                uint256 xis = a.citeXis[j];
                paid += _slot(k, o, M.slotRoyalty(GAMMA_BPS, S.net, xis, a.dNew), ax[o].proposer); // redirected to the root
                paid += _slot(k, o, M.slotRoyalty(GAMMA_BPS, S.net, x - xis, a.dNew), ax[k].proposer); // stays with the derivative
            }
        }
        _credit(a.underwriter, S.guar); // R_guar -> underwriter
        _credit(a.proposer, S.prop + (S.anc - paid)); // proposer share, plus floor dust
        return (S.burn, S.net);
    }

    /// @dev 4-stage waterfall of one royalty slot: anchor rebate -> debt-following 2.0x RBF repayment (derivative u first, then root s)
    ///      -> dictionary dividend -> owner remainder.
    function _slot(uint32 u, uint32 s, uint256 R, address ownerAddr) internal returns (uint256) {
        if (R == 0) return 0;
        uint256 du = debtOf[u];
        uint256 dsd = u == s ? 0 : debtOf[s];
        uint256 rem = M.m1RedirectRbfPriority(R, BETA_D_BPS, du, dsd, 0).owner;
        uint256 sst = stakeTotal[s];
        uint256 stot = M.max(sst, ax[s].bNew);
        uint256 bound = stot == 0 ? 0 : (_phiActive(s) * sst * rem) / (BPS * stot);
        M.M1 memory m = M.m1RedirectRbfPriority(R, BETA_D_BPS, du, dsd, bound);
        _credit(ds[ax[s].dataset].owner, m.anchor);
        uint256 dust = _repay(u, m.paidU);
        if (u != s) dust += _repay(s, m.paidS);
        if (m.divS > 0) {
            accPerStake[s] += (m.divS * 1e27) / sst;
            poolsTotal += m.divS;
        }
        _credit(ownerAddr, m.owner + dust);
        return R;
    }

    function _repay(uint32 u, uint256 amt) internal returns (uint256) {
        if (amt == 0) return 0;
        Sponsor[] storage sp = sponsors[u];
        uint256 n = sp.length;
        uint256[] memory debts = new uint256[](n);
        for (uint256 i = 0; i < n; ++i) debts[i] = sp[i].debt;
        uint256[] memory sh = M.rbfProrata(amt, debts);
        uint256 tot;
        for (uint256 i = 0; i < n; ++i) {
            sp[i].debt -= sh[i];
            tot += sh[i];
            _credit(sp[i].who, sh[i]);
        }
        debtOf[u] -= tot;
        return amt - tot;
    }

    // ================================================================== [B10] normal close / [B11] penalized close
    function closeDataset(uint32 id) external onlyDelegated {
        Dataset storage D = ds[id];
        if (D.status != 1) revert BadDataset();
        if (msg.sender != D.owner) revert NotOwner();
        A.DataState memory d = D.d;
        if (d.dInit != 0 || d.dAbs != 0 || d.dHold != 0 || D.unsettled.length != 0) revert Rejected(13);
        D.status = 2;
        if (D.penalized) {
            supply = A.branch11ClosePen(supply, d.BRem, D.sk); // B_rem + 30 % S_k back, 70 % S_k burned
            _credit(D.owner, d.BRem + M.refund30(D.sk));
            _hit(B11, id, msg.sender, d.BRem + D.sk);
        } else {
            supply = A.branch10CloseOk(supply, d.BRem, D.sk);
            _credit(D.owner, d.BRem + D.sk);
            _hit(B10, id, msg.sender, d.BRem + D.sk);
        }
        _chk();
    }

    // ================================================================== [B12A] RBF sponsorship burn
    function sponsorRBF(uint32 aid, uint256 amount) external onlyDelegated {
        Axiom storage a = ax[aid];
        if (!a.active || _now() < a.adoptedAt + N_LOCK) revert Rejected(14);
        uint256 target = btarget(aid);
        if (target == 0 || sponsors[aid].length >= MAX_RBF || amount < M.ceilDiv(target, MAX_RBF)) revert Rejected(15);
        supply = A.branch12to15(supply, 0, 0, amount, 0, 0); // burn from the sponsor's wallet
        _debit(msg.sender, amount);
        a.amortBurn += amount; // C_amort_burn grows immediately
        uint256 debt = (M_CAP_BPS * amount) / BPS; // 2.0x debt D_{u,s}^{(0)}
        sponsors[aid].push(Sponsor(msg.sender, debt));
        debtOf[aid] += debt;
        A.DataState storage d = ds[a.dataset].d;
        uint256 saved = M.savedNet(M.deltaAmort(a.lAxiom, a.amortBurn, d.B0, d.Phi0, BPS - EPS_BPS), a.lE0);
        a.rootCapLeft += saved - a.savedBits;
        a.savedBits = saved;
        _hit(B12A, aid, msg.sender, amount);
        _chk();
    }
}
