// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {ESMMath as M} from "./ESMMath.sol";
import {ESMAccounting as A} from "./ESMAccounting.sol";
import {IERC20, IVerifierRegistry, ISeedBeacon, IArchiveRegistry} from "./Interfaces.sol";
import {ESMStorage} from "./ESMStorage.sol";
import {ESMOps} from "./ESMOps.sol";

/// @title ESM - stateful Epistemic State Machine over a single ERC-20 accounting asset
/// @notice Core: vault [B15], registration [B1], commit [B2], reveal, adopt/reject [B3][B4], forfeiture [B5], dictionary stake [B12B][B12C],
///         epoch [B13], T6 [B14]. The remaining schemas ([B6]..[B12A]: slashing, hold, settlement, close, RBF) live in ESMOps and are reached
///         through `delegatecall` forwarders below; both share ESMStorage, so SupplyInv / DataInv are checked in one storage context.
contract ESM is ESMStorage {
    address public immutable ops;

    constructor(IERC20 asset_, IVerifierRegistry v_, ISeedBeacon b_, IArchiveRegistry a_, Params memory p_)
        ESMStorage(asset_, v_, b_, a_, block.number, p_)
    {
        ops = address(new ESMOps(asset_, v_, b_, a_, block.number));
    }

    function _fwd() internal {
        (bool ok, bytes memory ret) = ops.delegatecall(msg.data);
        if (!ok) {
            assembly {
                revert(add(ret, 32), mload(ret))
            }
        }
    }

    // ---- forwarders to the module (same ABI as the monolithic version)
    function revealSlash(RevealT2 calldata) external nonReentrant { _fwd(); }
    function topUpAbsorb(uint32, uint256) external nonReentrant { _fwd(); }
    function expireHold(uint32) external nonReentrant { _fwd(); }
    function settle(uint32) external nonReentrant { _fwd(); }
    function closeDataset(uint32) external nonReentrant { _fwd(); }
    function sponsorRBF(uint32, uint256) external nonReentrant { _fwd(); }

    function _lockFrom(address a, uint256 amt) internal {
        _debit(a, amt);
        supply = A.ledgerTx(supply, amt, 0, 0, amt, 0, 0);
    }

    function supplyInvariant() external view returns (bool) {
        A.SupplyState memory s = supply;
        return s.wallets + s.locked + s.burned + redeemed == s.minted && userWallets + poolsTotal == s.wallets
            && asset.balanceOf(address(this)) == s.minted - redeemed - flushedBurn;
    }

    function dataInvariant(uint32 id) external view returns (bool) {
        return A.dataInv(ds[id].d);
    }

    // ================================================================== [B15] vault
    function deposit(uint256 amount) external nonReentrant {
        uint256 b0 = asset.balanceOf(address(this));
        if (!asset.transferFrom(msg.sender, address(this), amount)) revert TransferFailed();
        if (asset.balanceOf(address(this)) - b0 != amount) revert BalanceDiff(); // fee-on-transfer / rebasing / hook tokens are rejected
        supply = A.branch12to15(supply, 0, 0, 0, amount, 0); // mint into the wallet bucket (minted < 2^96 enforced)
        _credit(msg.sender, amount);
        _hit(B15, 0, msg.sender, amount);
        _chk();
    }

    function withdraw(uint256 amount) external nonReentrant {
        _debit(msg.sender, amount);
        supply.wallets -= amount;
        redeemed += amount;
        _hit(B15, 0, msg.sender, amount);
        _chk();
        if (!asset.transfer(msg.sender, amount)) revert TransferFailed();
    }

    /// @notice permissionless: sends the burn counter's tokens to the dead address
    function flushBurn() external nonReentrant {
        uint256 amt = supply.burned - flushedBurn;
        flushedBurn += amt;
        if (!asset.transfer(DEAD, amt)) revert TransferFailed();
    }

    // ================================================================== [B1] T0 dataset registration
    function registerDataset(uint256 B0, uint256 Sk, bytes32 root, uint32 nK, uint16 bK, uint8 storageKind, bytes calldata uri)
        external
        nonReentrant
        returns (uint32 id)
    {
        if (B0 == 0) revert Rejected(1);
        id = ++datasetCount;
        uint256 phi0 = archive.register(id, root, nK, bK, storageKind, uri);
        uint256 burnDa = params.daFeePerBit * phi0;
        supply = A.branch01T0(supply, B0, Sk, burnDa, 0);
        _debit(msg.sender, B0 + Sk + burnDa);
        Dataset storage D = ds[id];
        D.owner = msg.sender;
        D.status = 1;
        D.sk = Sk;
        D.d.B0 = B0;
        D.d.Phi0 = phi0;
        D.d.PhiBest = phi0;
        D.d.BRem = B0;
        A.checkBounds(D.d);
        _hit(B1, id, msg.sender, B0 + Sk);
        _chk();
    }

    // ================================================================== [B2] blind commit (T1 / T2 / T6 share one front-running-proof mechanism)
    /// @param kind 1 = T1 proposal (ref = dataset), 2 = T2 slash (ref = axiom), 3 = T6 reduction (ref = derivative axiom)
    /// @param h    keccak256(abi.encode(msg.sender, ...)): the SENDER is bound inside the hash, so a copied hash is useless to anyone else
    /// @param sCreator creator collateral S_c locked by a T1 proposal (>= the spam-prevention minimum `commitCollateralBps` of B_k^(0)); it caps the
    ///        claimable escrow of the reveal: E_tr <= 10000 (10000 + Lambda_bps) S_c / (10000 sigma_col_bps) (Theorem 5.3 (3)(4)). Must be 0 for kinds 2 and 3.
    function commit(uint8 kind, uint32 ref, bytes32 h, uint256 sCreator) external nonReentrant {
        if (commits[h].who != address(0)) revert Duplicate();
        uint256 t = _now();
        uint32 b = uint32((t - genesis) / N_BATCH);
        Commit memory c = Commit(msg.sender, kind, ref, b, uint64(t), false, false, 0);
        if (kind == 1) {
            Dataset storage D = ds[ref];
            if (D.status != 1) revert BadDataset();
            if ((t - genesis) % N_BATCH >= N_COM) revert WrongPhase();
            if (++commitCount[ref][b] > MAX_COMMITS) revert TooMany();
            if (sCreator < M.ceilDiv(params.commitCollateralBps * D.d.B0, BPS)) revert Rejected(18); // below the spam-prevention minimum
            c.sc = sCreator;
            supply = A.branch02Commit(supply, sCreator, 0);
            _debit(msg.sender, sCreator);
            batchRoot[b] = keccak256(abi.encode(batchRoot[b], h));
            _hit(B2, ref, msg.sender, sCreator);
        } else if (kind == 2 || kind == 3) {
            if (!ax[ref].active) revert BadAxiom();
            if (sCreator != 0) revert Rejected(23);
        } else {
            revert BadKind();
        }
        commits[h] = c;
        emit Committed(h, msg.sender, kind, ref);
        _chk();
    }

    // ================================================================== T1 reveal (no ledger change beyond the reveal lock)
    struct Reveal {
        uint32 datasetId;
        uint32 batch;
        bytes32 programHash;
        uint256 progBits;
        uint256 phiLocal;
        uint256 lAxiom;
        uint256 cAmort;
        uint32[] citeIds;
        uint256[] citeBits;
        address underwriter; // co-staking underwriter; address(0) = the proposer itself
        uint256 suw; // S_uw <= Lambda S_c, locked from the underwriter's wallet
        bytes32 salt;
        uint32 vkVersion;
        bytes proof;
    }

    /// @notice an underwriter lets `proposer` lock `S_uw` from its wallet in a reveal that names it (revocable at any time)
    function setUnderwriterConsent(address proposer, bool ok) external {
        uwConsent[msg.sender][proposer] = ok;
    }

    function proposalHash(address who, Reveal calldata r) public pure returns (bytes32) {
        return keccak256(
            abi.encode(
                who, r.datasetId, r.batch, r.programHash, r.progBits, r.phiLocal, r.lAxiom, r.cAmort,
                keccak256(abi.encode(r.citeIds)), keccak256(abi.encode(r.citeBits)), r.underwriter, r.suw, r.salt
            )
        );
    }

    function proposalPublicValues(address who, Reveal calldata r) public view returns (bytes memory) {
        return abi.encode(
            uint8(1), r.datasetId, r.batch, beacon.seed(r.batch), archive.rootOf(r.datasetId), r.programHash, r.progBits, r.phiLocal, r.lAxiom,
            keccak256(abi.encode(r.citeIds, r.citeBits)), who
        );
    }

    function revealProposal(Reveal calldata r) external nonReentrant {
        bytes32 h = proposalHash(msg.sender, r);
        Commit storage c = commits[h];
        if (c.who != msg.sender || c.kind != 1 || c.revealed || c.ref != r.datasetId || c.batch != r.batch) revert BadReveal();
        uint256 start = genesis + uint256(r.batch) * N_BATCH;
        uint256 t = _now();
        if (t < start + N_COM + N_DELAY || t >= start + N_BATCH || !beacon.isReady(r.batch)) revert WrongPhase();
        if (!verifiers.verify(1, r.vkVersion, proposalPublicValues(msg.sender, r), r.proof)) revert BadProof();
        Dataset storage D = ds[r.datasetId];
        A.DataState memory d = D.d;
        if (r.phiLocal < 1 || r.phiLocal >= d.PhiBest || r.lAxiom < 1 || cands[r.datasetId][r.batch].length >= MAX_CAND) revert Rejected(2);
        if (r.citeIds.length != r.citeBits.length || r.citeIds.length > MAX_CITED) revert Rejected(3);
        uint256 dNew = d.PhiBest - r.phiLocal;
        uint256 sumBits;
        for (uint256 i = 0; i < r.citeIds.length; ++i) {
            if (!ax[r.citeIds[i]].active) revert BadAxiom();
            sumBits += r.citeBits[i];
        }
        if (sumBits > dNew) revert Rejected(4);
        uint8 code = _admission(M.escrowAlloc(d.B0, d.Phi0, dNew), c.sc, r.suw, r.citeIds, r.citeBits);
        if (code != 0) revert Rejected(code);
        address uw = r.underwriter == address(0) ? msg.sender : r.underwriter;
        if (uw != msg.sender && r.suw > 0 && !uwConsent[uw][msg.sender]) revert Rejected(21);
        uint256 suw = r.suw;
        uint256 lockP = params.sAudit + params.daFeePerBit * r.lAxiom + r.cAmort; // paid by the proposer
        uint256 lock = lockP + suw;
        _lockFrom(msg.sender, lockP);
        if (suw > 0) _lockFrom(uw, suw); // co-stake from the underwriter's wallet
        c.revealed = true;
        Cand storage cd = cands[r.datasetId][r.batch].push();
        cd.who = msg.sender;
        cd.uw = uw;
        cd.hash = h;
        cd.programHash = r.programHash;
        cd.progBits = r.progBits;
        cd.phiLocal = r.phiLocal;
        cd.lAxiom = r.lAxiom;
        cd.cAmort = r.cAmort;
        cd.lock = lock;
        cd.suw = suw;
        cd.sc = c.sc;
        cd.phiBestAtReveal = d.PhiBest;
        cd.citeIds = r.citeIds;
        cd.citeBits = r.citeBits;
        _chk();
    }

    // ================================================================== [B3] adopt / [B4] reject
    function finalizeBatch(uint32 id, uint32 batch) external nonReentrant {
        Dataset storage D = ds[id];
        if (D.status != 1) revert BadDataset();
        if (_now() < genesis + (uint256(batch) + 1) * N_BATCH) revert WrongPhase();
        if (finalized[id][batch]) revert Duplicate();
        finalized[id][batch] = true;
        Cand[] storage cs = cands[id][batch];
        uint256 best = type(uint256).max;
        uint256 bestPhi = type(uint256).max;
        if (D.unsettled.length < MAX_UNSETTLED) {
            for (uint256 i = 0; i < cs.length; ++i) {
                if (cs[i].phiBestAtReveal == D.d.PhiBest && cs[i].phiLocal < bestPhi && _eligible(D.d, cs[i])) {
                    best = i;
                    bestPhi = cs[i].phiLocal;
                }
            }
        }
        for (uint256 i = 0; i < cs.length; ++i) {
            if (i == best) _adopt(id, cs[i]);
            else _reject(cs[i]);
        }
        _chk();
    }

    /// @dev admission re-checked against the CURRENT state at adoption time (an earlier adoption may have used up a cited axiom's saving);
    ///      an inadmissible candidate is rejected (refund path) instead of reverting the whole batch
    function _eligible(A.DataState storage d, Cand storage c) internal view returns (bool) {
        uint256 e = M.escrowAlloc(d.B0, d.Phi0, d.PhiBest - c.phiLocal);
        return _admission(e, c.sc, c.suw, c.citeIds, c.citeBits) == 0;
    }

    function _adopt(uint32 id, Cand storage c) internal {
        Dataset storage D = ds[id];
        A.DataState memory d = D.d;
        uint256 dNew = d.PhiBest - c.phiLocal;
        uint256 bNew = M.escrowAlloc(d.B0, d.Phi0, dNew);
        D.d = A.adopt(d, c.phiLocal, bNew);
        uint256 sst = c.suw + params.sAudit;
        uint256 burnDa = params.daFeePerBit * c.lAxiom;
        A.SupplyState memory s = A.ledgerTx(supply, 0, c.lock, c.lock, 0, 0, 0); // release the reveal lock ...
        supply = A.branch03Adopt(s, sst, burnDa, c.cAmort, 0); // ... and apply Branch 3 (S_uw + S_audit locked, DA fee + C_amort burned)
        uint32 aid = ++axiomCount;
        Axiom storage a = ax[aid];
        a.proposer = c.who;
        a.underwriter = c.uw;
        a.dataset = id;
        a.adoptedAt = uint64(_now());
        a.seq = aid;
        a.origin = aid;
        a.active = true;
        a.programHash = c.programHash;
        a.progBits = c.progBits;
        a.phiLocal = c.phiLocal;
        a.lAxiom = c.lAxiom;
        a.dNew0 = dNew;
        a.dNew = dNew;
        a.bNew = bNew;
        a.sc0 = c.sc;
        a.sc = c.sc;
        a.suw = c.suw;
        a.saudit = params.sAudit;
        a.amortBurn = c.cAmort;
        a.lE0 = _dictLenWeight(0);
        a.savedBits = M.savedNet(M.deltaAmort(c.lAxiom, c.cAmort, d.B0, d.Phi0, BPS - EPS_BPS), a.lE0);
        a.rootCapLeft = a.savedBits;
        for (uint256 j = 0; j < c.citeIds.length; ++j) {
            uint32 k = c.citeIds[j];
            uint32 o = ax[k].origin;
            uint256 x = c.citeBits[j];
            uint256 xis = x;
            if (o != k) {
                (xis,,) = M.stage2Redirect(x, ax[k].lRed, ax[o].rootCapLeft); // Stage 2: cap the redirected bits by L_red and the root's remaining saving
                ax[o].rootCapLeft -= xis;
            }
            ax[k].sPaid += x; // Stage 1: the whole slot is charged against the cited axiom's own cap (admission guarantees sPaid <= savedBits)
            a.citeIds.push(k);
            a.citeBits.push(x);
            a.citeXis.push(xis);
            a.citeRoot.push(o);
        }
        D.unsettled.push(aid);
        _hit(B3, aid, c.who, c.lock);
    }

    function _reject(Cand storage c) internal {
        uint256 burnDa = params.daFeePerBit * c.lAxiom;
        A.SupplyState memory s = A.ledgerTx(supply, 0, c.lock, c.lock, 0, 0, 0);
        supply = A.branch04Reject(s, c.sc, 0, burnDa, 0); // S_c returned in full, only the DA fee is burned
        _credit(c.who, c.lock - c.suw - burnDa + c.sc);
        if (c.suw > 0) _credit(c.uw, c.suw); // the co-stake returns to the underwriter wallet
        commits[c.hash].settled = true;
        _hit(B4, 0, c.who, c.lock);
    }

    // ================================================================== [B5] unrevealed commit forfeiture
    function forfeitUnrevealed(bytes32 h) external nonReentrant {
        Commit storage c = commits[h];
        if (c.who == address(0) || c.kind != 1 || c.revealed || c.settled) revert BadReveal();
        if (_now() < genesis + (uint256(c.batch) + 1) * N_BATCH) revert WrongPhase();
        c.settled = true;
        uint256 ref = M.refund30(c.sc);
        supply = A.branch05Unrevealed(supply, c.sc); // 30 % back, 70 % burned forever
        _credit(c.who, ref);
        _hit(B5, c.ref, c.who, c.sc);
        _chk();
    }

    // ================================================================== [B12B] / [B12C] dictionary stake, delayed phi
    function _setWeight(uint32 aid, uint256 w) internal {
        Weight storage x = wt[aid];
        if (x.curEpoch < epoch) {
            x.prev = x.cur;
            x.curEpoch = uint64(epoch);
        }
        x.cur = uint128(w);
    }

    function _harvest(uint32 aid, address who) internal {
        UserStake storage u = userStake[aid][who];
        uint256 acc = (u.amount * accPerStake[aid]) / 1e27;
        if (acc > u.rewardDebt) {
            uint256 r = acc - u.rewardDebt;
            poolsTotal -= r;
            _credit(who, r);
        }
        u.rewardDebt = acc;
    }

    function stakeDict(uint32 aid, uint256 amount) external nonReentrant {
        if (!ax[aid].active) revert BadAxiom();
        _harvest(aid, msg.sender);
        supply = A.branch12to15(supply, amount, 0, 0, 0, 0); // wallet -> locked
        _debit(msg.sender, amount);
        UserStake storage u = userStake[aid][msg.sender];
        u.amount += amount;
        u.rewardDebt = (u.amount * accPerStake[aid]) / 1e27;
        stakeTotal[aid] += amount;
        totalWeight += amount;
        _setWeight(aid, stakeTotal[aid]);
        _hit(B12B, aid, msg.sender, amount);
        _chk();
    }

    /// @notice moves the caller's accumulated dictionary dividends from the pool to the caller's wallet
    function claimDict(uint32 aid) external nonReentrant {
        _harvest(aid, msg.sender);
        _chk();
    }

    function requestUnstake(uint32 aid, uint256 amount) external nonReentrant {
        _harvest(aid, msg.sender);
        UserStake storage u = userStake[aid][msg.sender];
        if (amount > u.amount) revert Insufficient(msg.sender, u.amount, amount);
        u.amount -= amount;
        u.rewardDebt = (u.amount * accPerStake[aid]) / 1e27;
        u.reqAmount += amount;
        u.reqEpoch = epoch;
        stakeTotal[aid] -= amount;
        totalWeight -= amount;
        _setWeight(aid, stakeTotal[aid]);
    }

    function unstakeDict(uint32 aid) external nonReentrant {
        UserStake storage u = userStake[aid][msg.sender];
        if (u.reqAmount == 0 || epoch < u.reqEpoch + 1) revert WrongPhase(); // one full epoch of grace
        uint256 amt = u.reqAmount;
        u.reqAmount = 0;
        supply = A.branch12to15(supply, 0, amt, 0, 0, 0); // locked -> wallet
        _credit(msg.sender, amt);
        _hit(B12C, aid, msg.sender, amt);
        _chk();
    }

    function setPhiDict(uint32 aid, uint16 bps) external {
        if (msg.sender != ax[aid].proposer || bps > SIGMA_DICT_BPS) revert NotOwner();
        PhiDict storage p = phiDict[aid];
        if (p.pendingEpoch != 0 && p.pendingEpoch <= epoch) p.active = p.pending;
        p.pending = bps;
        p.pendingEpoch = uint64(epoch + 1); // takes effect at the next epoch boundary
    }

    function phiActive(uint32 aid) external view returns (uint256) {
        return _phiActive(aid);
    }

    // ================================================================== [B13] T5 epoch boundary, O(1)
    /// @notice one storage write per boundary: weights are never iterated; per-axiom quantities are evaluated lazily from
    ///         (current, previous, epoch-of-change) records and the global snapshot `snapTotal`.
    function epochUpdate() external {
        uint256 e = epoch + 1;
        if (_now() < genesis + e * N_EPOCH) revert WrongPhase();
        epoch = e;
        snapTotal = totalWeight;
        _hit(B13, uint32(e), msg.sender, totalWeight);
    }

    function _weightAtEpochStart(uint32 aid) internal view returns (uint256) {
        Weight storage w = wt[aid];
        return w.curEpoch < epoch ? w.cur : w.prev;
    }

    /// @dev l_E(v) = Shannon dictionary length from the epoch-start snapshot, overflow-free ceilDiv form (Lean: shannon_len_ceilDiv_iff)
    function _dictLenWeight(uint256 w) internal view returns (uint256) {
        uint256 e0 = params.eps0;
        return M.shannonLen(snapTotal + e0 * (uint256(axiomCount) + 1), w + e0);
    }

    function dictLen(uint32 aid) external view returns (uint256) {
        return _dictLenWeight(_weightAtEpochStart(aid));
    }

    // ================================================================== [B14] T6 syntactic reduction (two-phase)
    struct RevealT6 {
        uint32 vi; // derivative
        uint32 vs; // claimed source
        uint256 qLen; // |q| of the reduction adapter
        uint256 idxLen; // l_w(idx(v_s))
        uint256 fuelMax;
        bytes32 salt;
        uint32 vkVersion;
        bytes proof;
    }

    function t6Hash(address who, RevealT6 calldata r) public pure returns (bytes32) {
        return keccak256(abi.encode(who, uint8(3), r.vi, r.vs, r.qLen, r.idxLen, r.fuelMax, r.salt));
    }

    function revealReduction(RevealT6 calldata r) external nonReentrant {
        bytes32 h = t6Hash(msg.sender, r);
        Commit storage c = commits[h];
        uint256 t = _now();
        if (c.who != msg.sender || c.kind != 3 || c.revealed || c.ref != r.vi) revert BadReveal();
        if (t <= c.blk || t > c.blk + N_REV_T6) revert WrongPhase();
        Axiom storage vi = ax[r.vi];
        Axiom storage vs = ax[r.vs];
        if (!vi.active || !vs.active || r.fuelMax < 1 || r.fuelMax > DELTA_CAP_V1) revert Rejected(16);
        bytes memory pv = abi.encode(uint8(3), r.vs, r.vi, vs.programHash, vi.programHash, vs.progBits, vi.progBits, r.qLen, r.idxLen, r.fuelMax, msg.sender);
        if (!verifiers.verify(3, r.vkVersion, pv, r.proof)) revert BadProof();
        c.revealed = true;
        uint256 lNew = M.monus(vi.progBits, r.qLen + r.idxLen); // L_red_new = |p_i| (-) (|q| + l_w(idx(v_s)))
        if (!_t6Accept(r.vs, r.vi, lNew)) revert Rejected(17);
        vi.origin = r.vs;
        vi.lRed = lNew;
        uint256 audit = vi.saudit;
        if (audit > 0) {
            M.Slash memory sl = M.slashSplit(BPS, audit, KAPPA_BPS); // B_finder = 30 % of S_audit, 70 % burned
            supply = A.branch0607Puncture(supply, audit, sl.hunter, sl.burn, 0);
            _credit(msg.sender, sl.hunter);
            vi.saudit = 0;
        }
        _hit(B14, r.vi, msg.sender, audit);
        _chk();
    }

    /// @dev conditions (1), (2), (4) of T6: strict precedence, origin(v_s) = v_s, and the Case A / Case B overwrite rule
    function _t6Accept(uint32 s, uint32 i, uint256 lNew) internal view returns (bool) {
        Axiom storage vs = ax[s];
        Axiom storage vi = ax[i];
        if (!(vs.seq < vi.seq) || vs.origin != s) return false;
        uint32 o = vi.origin;
        if (ax[o].origin == o) {
            return lNew > vi.lRed || (lNew == vi.lRed && vi.lRed >= 1 && vs.seq < ax[o].seq);
        }
        return lNew >= 1;
    }

    // ================================================================== views for tests / indexers
    function datasetData(uint32 id) external view returns (A.DataState memory d, address owner, uint8 status, bool penalized, uint256 sk, uint64 holdStart, uint256 unsettledCount) {
        Dataset storage D = ds[id];
        return (D.d, D.owner, D.status, D.penalized, D.sk, D.holdStart, D.unsettled.length);
    }

    function axiomCore(uint32 id)
        external
        view
        returns (address proposer, uint32 dataset, uint256 dNew, uint256 sc, uint256 suw, uint256 saudit, uint32 origin, uint256 lRed, uint256 rootCap, bool active, bool settled, uint256 amortBurn, uint256 saved)
    {
        Axiom storage a = ax[id];
        return (a.proposer, a.dataset, a.dNew, a.sc, a.suw, a.saudit, a.origin, a.lRed, a.rootCapLeft, a.active, a.settled, a.amortBurn, a.savedBits);
    }

    function axiomMeta(uint32 id) external view returns (bytes32 programHash, uint256 progBits, uint64 adoptedAt) {
        Axiom storage a = ax[id];
        return (a.programHash, a.progBits, a.adoptedAt);
    }

    function axiomExt(uint32 id) external view returns (address underwriter, uint256 sPaid_, uint256 saved, uint256 rootCapLeft, uint256 suw) {
        Axiom storage a = ax[id];
        return (a.underwriter, a.sPaid, a.savedBits, a.rootCapLeft, a.suw);
    }

    /// @notice Delta_amort(v, D_k): creditable description-length exemption of axiom v measured on dataset k
    function deltaAmort(uint32 aid, uint32 k) public view returns (uint256) {
        Axiom storage a = ax[aid];
        A.DataState storage d = ds[k].d;
        if (d.Phi0 == 0) return 0;
        return M.deltaAmort(a.lAxiom, a.amortBurn, d.B0, d.Phi0, BPS - EPS_BPS);
    }

    /// @notice S_paid(v, D_k): bits of v's own cap reserved by live citation slots (axioms are measured on their home dataset only)
    function sPaid(uint32 aid, uint32 k) public view returns (uint256) {
        return ax[aid].dataset == k ? ax[aid].sPaid : 0;
    }

    /// @notice reservation bookkeeping of one axiom: S_paid <= saved <= Delta_amort and the root's remaining cap never exceeds its saving
    function reservationInvariant(uint32 aid) external view returns (bool) {
        Axiom storage a = ax[aid];
        if (a.dataset == 0) return true;
        return sPaid(aid, a.dataset) <= deltaAmort(aid, a.dataset) && a.sPaid <= a.savedBits && a.savedBits <= deltaAmort(aid, a.dataset)
            && a.rootCapLeft <= a.savedBits;
    }

    function axiomCites(uint32 id) external view returns (uint32[] memory ids, uint256[] memory bits, uint256[] memory xis) {
        Axiom storage a = ax[id];
        return (a.citeIds, a.citeBits, a.citeXis);
    }

    function candidateCount(uint32 id, uint32 batch) external view returns (uint256) {
        return cands[id][batch].length;
    }

    function sponsorsOf(uint32 aid) external view returns (Sponsor[] memory) {
        return sponsors[aid];
    }

    function currentBatch() external view returns (uint256) {
        return (_now() - genesis) / N_BATCH;
    }
}
