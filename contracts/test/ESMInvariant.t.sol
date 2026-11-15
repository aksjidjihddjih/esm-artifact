// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {ESM} from "../src/ESM.sol";
import {ESMStorage} from "../src/ESMStorage.sol";
import {ESMAccounting as A} from "../src/ESMAccounting.sol";
import {ESMMath as M} from "../src/ESMMath.sol";
import {IERC20, IVerifierRegistry, ISeedBeacon, IArchiveRegistry} from "../src/Interfaces.sol";
import {VerifierRegistry, MockVerifier} from "../src/VerifierRegistry.sol";
import {SeedBeacon, MockDrand} from "../src/SeedBeacon.sol";
import {ArchiveRegistry} from "../src/ArchiveRegistry.sol";
import {MockWETH} from "./ESMIntegration.t.sol";

interface VmH {
    function roll(uint256) external;
    function prank(address) external;
    function getNonce(address) external view returns (uint64);
}

/// @notice Handler of the stateful invariant fuzzing. Every external function is one ledger schema (the 18 schemas of step4_report.md) called with
///         fuzzed arguments by a random actor. The handler keeps its own clock (cheatcode `roll`; never `block.number`, which the via-IR optimizer may
///         reuse across rolls), moves time forward only, and calls the protocol with low-level calls so that a rejected action is simply a no-op.
///         Actions pick valid-looking targets (open datasets, active axioms, pending proposals), but sometimes build inadmissible inputs on purpose
///         (S_c too small, S_uw > Lambda S_c, uncapped citations) so that the rejection paths are exercised as well.
contract ESMHandler {
    VmH internal constant cheats = VmH(address(uint160(uint256(keccak256("hevm cheat code")))));
    uint256 internal constant TOK = 10_000;
    uint256 internal constant N_BATCH = 300;
    uint256 internal constant N_LOCK = 50_000;
    uint256 internal constant N_HOLD = 300;
    uint256 internal constant N_EPOCH = 49_800;
    bytes32 internal constant VK1 = keccak256("esm-core/t1/v0");
    bytes32 internal constant VK2 = keccak256("esm-core/t2/v0");
    bytes32 internal constant VK3 = keccak256("esm-core/t6/v0");

    // action ids = the 18 schemas called by the fuzzer (index into `ok` / `tried`)
    uint8 internal constant DEPOSIT = 1;
    uint8 internal constant WITHDRAW = 2;
    uint8 internal constant REGISTER = 3;
    uint8 internal constant COMMIT = 4;
    uint8 internal constant REVEAL = 5;
    uint8 internal constant FINALIZE = 6;
    uint8 internal constant FORFEIT = 7;
    uint8 internal constant REDUCTION = 8;
    uint8 internal constant SPONSOR = 9;
    uint8 internal constant STAKE = 10;
    uint8 internal constant REQ_UNSTAKE = 11;
    uint8 internal constant UNSTAKE = 12;
    uint8 internal constant SLASH = 13;
    uint8 internal constant TOPUP = 14;
    uint8 internal constant EXPIRE = 15;
    uint8 internal constant SETTLE = 16;
    uint8 internal constant CLOSE = 17;
    uint8 internal constant EPOCH = 18;

    MockWETH public weth;
    ESM public esm;
    SeedBeacon internal beacon;
    ArchiveRegistry internal archive;
    uint256 public G;
    uint256 public clock;
    address[] internal actors;

    uint256[19] public ok; // successful executions per action id
    uint256[19] public tried;
    uint256 public okSlashII;
    uint256 public okSlashIII;
    uint256 public okSlashWithAbsorbed; // T2 executed while d_abs > 0
    uint256 public okAdmissionRejects; // reveals rejected by the S_c / S_uw / Stage-1 admission rule

    struct Prop {
        address who;
        uint32 dataset;
        uint32 batch;
        bytes32 programHash;
        uint256 progBits;
        uint256 phiLocal;
        uint256 lAxiom;
        uint256 cAmort;
        uint32[] citeIds;
        uint256[] citeBits;
        address uw;
        uint256 suw;
        bytes32 salt;
        bytes32 h;
        bool attempted; // reveal tried
        bool revealed;
        bool forfeited;
        bool finalized;
    }

    Prop[] internal props;
    mapping(uint32 => uint256) internal absAtLocal; // clock of the last successful hold expiry (the absorbed window starts maturing)
    uint256 internal nonce;

    constructor() {
        VerifierRegistry reg;
        MockVerifier mv = new MockVerifier();
        G = 1000;
        cheats.roll(G);
        clock = G;
        weth = new MockWETH();
        reg = new VerifierRegistry(address(this), G + 1_000_000_000);
        reg.addVersion(1, VK1, mv);
        reg.addVersion(2, VK2, mv);
        reg.addVersion(3, VK3, mv);
        beacon = new SeedBeacon(G, 120, address(this), new MockDrand(), 1000, 1);
        uint64 n = cheats.getNonce(address(this));
        address predicted = address(uint160(uint256(keccak256(abi.encodePacked(bytes1(0xd6), bytes1(0x94), address(this), bytes1(uint8(n + 1)))))));
        archive = new ArchiveRegistry(predicted);
        ESMStorage.Params memory p = ESMStorage.Params({daFeePerBit: 1, sAudit: 20 * TOK, commitCollateralBps: 500, phiGuarBps: 5000, eps0: TOK, lambdaBps: 10_000});
        esm = new ESM(IERC20(address(weth)), IVerifierRegistry(address(reg)), ISeedBeacon(address(beacon)), IArchiveRegistry(address(archive)), p);
        require(address(esm) == address(archive.esm()), "address prediction");
        beacon.bind(esm);
        for (uint256 i = 0; i < 6; ++i) {
            address a = address(uint160(0xA000 + i));
            actors.push(a);
            weth.mint(a, 1e12);
            cheats.prank(a);
            weth.approve(address(esm), type(uint256).max);
            cheats.prank(a);
            esm.deposit(1e12);
        }
    }

    // ================================================================== plumbing
    function _bound(uint256 x, uint256 lo, uint256 hi) internal pure returns (uint256) {
        if (hi <= lo) return lo;
        return lo + (x % (hi - lo + 1));
    }

    function _actor(uint256 seed) internal view returns (address) {
        return actors[seed % actors.length];
    }

    /// @dev time only moves forward; returns false when `t` already lies in the past
    function _at(uint256 t) internal returns (bool) {
        if (t < clock) return false;
        if (t > clock) {
            clock = t;
            cheats.roll(t);
        }
        return true;
    }

    /// @dev deadline style: advance to `t` unless it already lies in the past (then it is satisfied)
    function _reach(uint256 t) internal {
        if (t > clock) {
            clock = t;
            cheats.roll(t);
        }
    }

    function _call(uint8 id, address who, bytes memory data) internal returns (bool success, bytes memory ret) {
        tried[id]++;
        cheats.prank(who);
        (success, ret) = address(esm).call(data);
        if (success) ok[id]++;
    }

    function _salt() internal returns (bytes32) {
        return keccak256(abi.encode("salt", ++nonce));
    }

    function _ds(uint32 id) internal view returns (A.DataState memory d, address owner, uint8 status, uint64 holdStart) {
        (d, owner, status,,, holdStart,) = esm.datasetData(id);
    }

    function _openDataset(uint256 seed) internal view returns (uint32 id, bool found) {
        uint32 n = esm.datasetCount();
        for (uint256 i = 0; i < n; ++i) {
            uint32 c = uint32(((seed + i) % n) + 1);
            (, , uint8 st,) = _ds(c);
            if (st == 1) return (c, true);
        }
    }

    function _activeAxiom(uint256 seed, uint32 below) internal view returns (uint32 id, bool found) {
        uint32 n = below == 0 ? esm.axiomCount() : below - 1;
        for (uint256 i = 0; i < n; ++i) {
            uint32 c = uint32(((seed + i) % n) + 1);
            (,,,,,,,,, bool actv, bool settled,,) = esm.axiomCore(c);
            if (actv && !settled) return (c, true);
        }
    }

    // ================================================================== [B15] vault
    function deposit(uint256 aSeed, uint256 amt) external {
        address a = _actor(aSeed);
        amt = _bound(amt, 1, 1e10);
        weth.mint(a, amt);
        _call(DEPOSIT, a, abi.encodeCall(esm.deposit, (amt)));
    }

    function withdraw(uint256 aSeed, uint256 amt) external {
        address a = _actor(aSeed);
        uint256 w = esm.wallet(a) / 3;
        if (w == 0) return;
        _call(WITHDRAW, a, abi.encodeCall(esm.withdraw, (_bound(amt, 1, w))));
    }

    function flushBurn() external {
        cheats.prank(actors[0]);
        address(esm).call(abi.encodeCall(esm.flushBurn, ()));
    }

    function advance(uint256 blocks) external {
        _at(clock + _bound(blocks, 1, 450));
    }

    // ================================================================== [B1] T0
    function registerDataset(uint256 aSeed, uint256 b0, uint256 sk, uint256 shape) external {
        if (esm.datasetCount() >= 4) return;
        address a = _actor(aSeed);
        bytes32 root = keccak256(abi.encode("root", ++nonce));
        uint256 B0 = _bound(b0, 50 * TOK, 10_000 * TOK);
        uint256 Sk = _bound(sk, 0, 100 * TOK);
        if (shape % 2 == 0) _call(REGISTER, a, abi.encodeCall(esm.registerDataset, (B0, Sk, root, 1024, 16, 1, abi.encodePacked(root))));
        else _call(REGISTER, a, abi.encodeCall(esm.registerDataset, (B0, Sk, root, 16, 4, 2, new bytes(46))));
    }

    // ================================================================== [B2] T1 phase 1 (blind commit)
    function commit(uint256 aSeed, uint256 dSeed, uint256 phiSeed, uint256 ctrl) public {
        (uint32 id, bool found) = _openDataset(dSeed);
        if (!found) return;
        (A.DataState memory d,,,) = _ds(id);
        if (d.PhiBest < 2) return;
        // move into the commit window of the current (or next) batch
        uint256 rel = (clock - G) % N_BATCH;
        uint256 t = rel >= 100 ? clock + (N_BATCH - rel) + _bound(ctrl >> 40, 0, 60) : clock;
        if (!_at(t)) return;
        address who = _actor(aSeed);
        Prop memory p;
        p.who = who;
        p.dataset = id;
        p.batch = uint32((clock - G) / N_BATCH);
        p.lAxiom = _bound(ctrl >> 8, 1, 300);
        p.progBits = p.lAxiom;
        p.programHash = keccak256(abi.encode("prog", ++nonce));
        p.phiLocal = _bound(phiSeed, 1, d.PhiBest - 1);
        uint256 dNew = d.PhiBest - p.phiLocal;
        uint256 sel = (ctrl >> 16) % 3;
        p.cAmort = sel == 0 ? 0 : (sel == 1 ? 20 * TOK : 100 * TOK);
        p.salt = _salt();
        _cites(p, ctrl >> 24, dNew);
        // creator collateral: usually the smallest admissible S_c (ceil(E/2) at Lambda = 1), sometimes deliberately too small
        uint256 e = M.escrowAlloc(d.B0, d.Phi0, dNew);
        uint256 minSc = M.ceilDiv(500 * d.B0, 10_000);
        uint256 sc = M.max(minSc, M.ceilDiv(e, 2));
        uint256 kind = (ctrl >> 48) % 8;
        if (kind == 0) sc = minSc;
        else if (kind < 4) sc += _bound(ctrl >> 56, 0, 200 * TOK);
        uint256 suwKind = (ctrl >> 64) % 6;
        p.suw = suwKind == 0 ? 0 : (suwKind == 1 ? sc + 1 : _bound(ctrl >> 72, 0, sc));
        if ((ctrl >> 96) % 3 == 0) {
            p.uw = _actor(ctrl >> 100);
            if ((ctrl >> 120) % 4 != 0) {
                cheats.prank(p.uw);
                esm.setUnderwriterConsent(who, true);
            }
        }
        p.h = esm.proposalHash(who, _reveal(p));
        (bool success,) = _call(COMMIT, who, abi.encodeCall(esm.commit, (1, id, p.h, sc)));
        if (success) props.push(p);
    }

    function _cites(Prop memory p, uint256 seed, uint256 dNew) internal view {
        uint32 n = esm.axiomCount();
        if (n == 0 || seed % 3 == 0) {
            p.citeIds = new uint32[](0);
            p.citeBits = new uint256[](0);
            return;
        }
        uint256 k = 1 + (seed >> 4) % 2;
        uint32[] memory ids = new uint32[](k);
        uint256[] memory bits = new uint256[](k);
        uint256 used;
        uint256 m;
        for (uint256 i = 0; i < k; ++i) {
            (uint32 aid, bool f) = _activeAxiom(seed >> (8 + 8 * i), 0);
            if (!f) continue;
            (, uint256 sp, uint256 saved,,) = esm.axiomExt(aid);
            uint256 avail = saved > sp ? saved - sp : 0;
            uint256 room = dNew > used ? dNew - used : 0;
            uint256 x = _bound(seed >> (24 + 8 * i), 0, M.min(avail, room) + ((seed >> 40) % 7 == 0 ? 3 : 0)); // sometimes over the Stage-1 cap
            ids[m] = aid;
            bits[m] = x;
            used += x;
            ++m;
        }
        p.citeIds = new uint32[](m);
        p.citeBits = new uint256[](m);
        for (uint256 i = 0; i < m; ++i) {
            p.citeIds[i] = ids[i];
            p.citeBits[i] = bits[i];
        }
    }

    function _reveal(Prop memory p) internal pure returns (ESM.Reveal memory r) {
        r = ESM.Reveal({
            datasetId: p.dataset, batch: p.batch, programHash: p.programHash, progBits: p.progBits, phiLocal: p.phiLocal, lAxiom: p.lAxiom,
            cAmort: p.cAmort, citeIds: p.citeIds, citeBits: p.citeBits, underwriter: p.uw, suw: p.suw, salt: p.salt, vkVersion: 0, proof: ""
        });
    }

    // ================================================================== T1 phase 2 reveal
    function revealProposal(uint256 pSeed) public {
        uint256 n = props.length;
        for (uint256 i = 0; i < n; ++i) {
            Prop storage p = props[(pSeed + i) % n];
            if (p.attempted || p.finalized) continue;
            uint256 start = G + uint256(p.batch) * N_BATCH;
            uint256 t = clock >= start + 120 ? clock : start + 125;
            if (t >= start + N_BATCH) continue;
            if (!_at(t)) continue;
            p.attempted = true;
            if (!beacon.isReady(p.batch)) beacon.relaySeed(p.batch, keccak256(abi.encode("l1-randao", p.batch)));
            ESM.Reveal memory r = _reveal(p);
            r.proof = abi.encode(keccak256(abi.encode(VK1, esm.proposalPublicValues(p.who, r))));
            (bool success, bytes memory ret) = _call(REVEAL, p.who, abi.encodeCall(esm.revealProposal, (r)));
            if (success) p.revealed = true;
            else if (ret.length == 36 && bytes4(ret) == ESMStorage.Rejected.selector) {
                uint256 code = uint256(bytes32(_tail(ret)));
                if (code >= 19 && code <= 22) okAdmissionRejects++;
            }
            return;
        }
    }

    function _tail(bytes memory ret) internal pure returns (bytes memory t) {
        t = new bytes(32);
        for (uint256 i = 0; i < 32; ++i) t[i] = ret[4 + i];
    }

    // ================================================================== [B3]/[B4] batch finalization
    function finalizeBatch(uint256 pSeed) public {
        uint256 n = props.length;
        for (uint256 i = 0; i < n; ++i) {
            Prop storage p = props[(pSeed + i) % n];
            if (p.finalized || !p.revealed) continue;
            _reach(G + (uint256(p.batch) + 1) * N_BATCH);
            (bool success,) = _call(FINALIZE, actors[0], abi.encodeCall(esm.finalizeBatch, (p.dataset, p.batch)));
            if (success) {
                for (uint256 j = 0; j < n; ++j) {
                    if (props[j].dataset == p.dataset && props[j].batch == p.batch) props[j].finalized = true;
                }
            }
            return;
        }
    }

    // ================================================================== [B5] forfeiture of an unrevealed commit
    function forfeitUnrevealed(uint256 pSeed) external {
        uint256 n = props.length;
        for (uint256 i = 0; i < n; ++i) {
            Prop storage p = props[(pSeed + i) % n];
            if (p.revealed || p.forfeited) continue;
            _reach(G + (uint256(p.batch) + 1) * N_BATCH);
            (bool success,) = _call(FORFEIT, actors[1], abi.encodeCall(esm.forfeitUnrevealed, (p.h)));
            if (success) p.forfeited = true;
            return;
        }
    }

    // ================================================================== [B14] T6 reduction
    function revealReduction(uint256 aSeed, uint256 viSeed, uint256 vsSeed, uint256 q) external {
        (uint32 vi, bool f1) = _activeAxiom(viSeed, 0);
        if (!f1 || vi < 2) return;
        (uint32 vs, bool f2) = _activeAxiom(vsSeed, vi); // vs.seq < vi.seq
        if (!f2) return;
        address who = _actor(aSeed);
        (bytes32 hVs, uint256 bVs,) = esm.axiomMeta(vs);
        (bytes32 hVi, uint256 bVi,) = esm.axiomMeta(vi);
        ESM.RevealT6 memory r = ESM.RevealT6({
            vi: vi, vs: vs, qLen: _bound(q, 1, 12), idxLen: _bound(q >> 8, 1, 4), fuelMax: _bound(q >> 16, 1, 65_536), salt: _salt(), vkVersion: 0, proof: ""
        });
        (bool c,) = _call(REDUCTION, who, abi.encodeCall(esm.commit, (3, vi, esm.t6Hash(who, r), 0)));
        tried[REDUCTION]--; // the reveal is the schema; the blind commit is its first half
        if (c) ok[REDUCTION]--;
        if (!c) return;
        if (!_at(clock + 1)) return;
        r.proof = abi.encode(keccak256(abi.encode(VK3, abi.encode(uint8(3), vs, vi, hVs, hVi, bVs, bVi, r.qLen, r.idxLen, r.fuelMax, who))));
        _call(REDUCTION, who, abi.encodeCall(esm.revealReduction, (r)));
    }

    // ================================================================== [B12A] RBF sponsorship
    function sponsorRBF(uint256 aSeed, uint256 axSeed, uint256 amtSeed) external {
        (uint32 aid, bool f) = _activeAxiom(axSeed, 0);
        if (!f) return;
        (,, uint64 adoptedAt) = esm.axiomMeta(aid);
        _reach(uint256(adoptedAt) + N_LOCK);
        uint256 target = esm.btarget(aid);
        if (target == 0) return;
        uint256 amt = _bound(amtSeed, M.ceilDiv(target, 10), target);
        address who = _actor(aSeed);
        if (esm.wallet(who) < amt) return;
        _call(SPONSOR, who, abi.encodeCall(esm.sponsorRBF, (aid, amt)));
    }

    // ================================================================== [B12B] / [B12C] dictionary stake
    function stakeDict(uint256 aSeed, uint256 axSeed, uint256 amt) external {
        (uint32 aid, bool f) = _activeAxiom(axSeed, 0);
        if (!f) return;
        address who = _actor(aSeed);
        uint256 w = esm.wallet(who) / 4;
        if (w == 0) return;
        _call(STAKE, who, abi.encodeCall(esm.stakeDict, (aid, _bound(amt, 1, w))));
    }

    function requestUnstake(uint256 aSeed, uint256 axSeed, uint256 amt) external {
        uint32 n = esm.axiomCount();
        if (n == 0) return;
        address who = _actor(aSeed);
        for (uint256 i = 0; i < n; ++i) {
            uint32 aid = uint32(((axSeed + i) % n) + 1);
            (uint256 have,,,) = esm.userStake(aid, who);
            if (have > 0) {
                _call(REQ_UNSTAKE, who, abi.encodeCall(esm.requestUnstake, (aid, _bound(amt, 1, have))));
                return;
            }
        }
    }

    function unstakeDict(uint256 aSeed, uint256 axSeed) external {
        uint32 n = esm.axiomCount();
        if (n == 0) return;
        address who = _actor(aSeed);
        for (uint256 i = 0; i < n; ++i) {
            uint32 aid = uint32(((axSeed + i) % n) + 1);
            (,, uint256 req,) = esm.userStake(aid, who);
            if (req > 0) {
                _call(UNSTAKE, who, abi.encodeCall(esm.unstakeDict, (aid)));
                return;
            }
        }
    }

    function claimDict(uint256 aSeed, uint256 axSeed) external {
        uint32 n = esm.axiomCount();
        if (n == 0) return;
        cheats.prank(_actor(aSeed));
        address(esm).call(abi.encodeCall(esm.claimDict, (uint32((axSeed % n) + 1))));
    }

    // ================================================================== [B6]/[B7] T2: mode II-A (1) / mode III (2)
    function revealSlash(uint256 aSeed, uint256 axSeed, uint256 modeSeed, uint256 dSeed) public {
        (uint32 aid, bool f) = _activeAxiom(axSeed, 0);
        if (!f) return;
        address hunter = _actor(aSeed);
        (, uint32 dsId, uint256 dNew,,,,,,,,,,) = esm.axiomCore(aid);
        (bytes32 progHash,,) = esm.axiomMeta(aid);
        uint8 mode = modeSeed % 2 == 0 ? 1 : 2;
        uint256 dUnroll = 0;
        if (mode == 2) {
            if (dNew < 2) mode = 1;
            else dUnroll = _bound(dSeed, 1, dNew - 1);
        }
        bool blame = (dSeed >> 200) % 2 == 0 && mode == 1;
        ESMStorage.RevealT2 memory r = ESMStorage.RevealT2({axiomId: aid, mode: mode, dUnroll: dUnroll, blameDataset: blame, evidence: keccak256("Z_punct"), salt: _salt(), vkVersion: 0, proof: ""});
        (A.DataState memory before,,,) = _ds(dsId);
        (bool c,) = _call(SLASH, hunter, abi.encodeCall(esm.commit, (2, aid, esm.slashHash(hunter, r), 0)));
        tried[SLASH]--;
        if (c) ok[SLASH]--;
        if (!c) return;
        if (!_at(clock + 1)) return;
        r.proof = abi.encode(keccak256(abi.encode(VK2, abi.encode(uint8(2), mode, aid, dsId, archive.rootOf(dsId), progHash, dUnroll, blame, r.evidence, hunter))));
        (bool success,) = _call(SLASH, hunter, abi.encodeCall(esm.revealSlash, (r)));
        if (success) {
            if (mode == 1) okSlashII++;
            else okSlashIII++;
            if (before.dAbs > 0) okSlashWithAbsorbed++;
        }
    }

    // ================================================================== [B8A] absorb top-up / [B8B] hold expiry
    function topUpAbsorb(uint256 aSeed, uint256 dSeed, uint256 amt) public {
        (uint32 id, bool found) = _openDataset(dSeed);
        if (!found) return;
        (A.DataState memory d,,, uint64 hs) = _ds(id);
        if (d.dHold == 0 || clock >= uint256(hs) + N_HOLD) return;
        _call(TOPUP, _actor(aSeed), abi.encodeCall(esm.topUpAbsorb, (id, _bound(amt, 1, d.dHold))));
    }

    function expireHold(uint256 dSeed) public {
        uint32 n = esm.datasetCount();
        for (uint256 i = 0; i < n; ++i) {
            uint32 id = uint32(((dSeed + i) % n) + 1);
            (A.DataState memory d,,, uint64 hs) = _ds(id);
            if (d.dHold == 0) continue;
            _reach(uint256(hs) + N_HOLD);
            (bool success,) = _call(EXPIRE, actors[2], abi.encodeCall(esm.expireHold, (id)));
            if (success) absAtLocal[id] = clock;
            return;
        }
    }

    // ================================================================== [B9] T4 settlement
    function settle(uint256 dSeed) external {
        uint32 n = esm.datasetCount();
        for (uint256 i = 0; i < n; ++i) {
            uint32 id = uint32(((dSeed + i) % n) + 1);
            (A.DataState memory d,, uint8 st,) = _ds(id);
            if (st != 1 || d.dHold != 0 || (d.dInit == 0 && d.dAbs == 0)) continue;
            uint256 t = clock;
            uint32 an = esm.axiomCount();
            for (uint32 a = 1; a <= an; ++a) {
                (,,,,,,,,, bool actv, bool settled,,) = esm.axiomCore(a);
                (, uint32 ad,,,,,,,,,,,) = esm.axiomCore(a);
                if (ad != id || !actv || settled) continue;
                (,, uint64 at_) = esm.axiomMeta(a);
                t = M.max(t, uint256(at_) + N_LOCK);
            }
            if (d.dAbs != 0) t = M.max(t, absAtLocal[id] + N_LOCK);
            _reach(t);
            _call(SETTLE, actors[3], abi.encodeCall(esm.settle, (id)));
            return;
        }
    }

    // ================================================================== [B10]/[B11] close
    function closeDataset(uint256 dSeed) external {
        (uint32 id, bool found) = _openDataset(dSeed);
        if (!found) return;
        (, address owner,,) = _ds(id);
        _call(CLOSE, owner, abi.encodeCall(esm.closeDataset, (id)));
    }

    // ================================================================== [B13] T5 epoch boundary
    function epochUpdate() external {
        _reach(G + (esm.epoch() + 1) * N_EPOCH);
        _call(EPOCH, actors[4], abi.encodeCall(esm.epochUpdate, ()));
    }


    // ================================================================== composite actions (deepen the reachable state space; same checks as the atomic ones)
    /// @dev commit -> reveal -> finalize in one call: builds up the axiom DAG much faster than random interleaving of the three atomic steps
    function adoptAxiom(uint256 aSeed, uint256 dSeed, uint256 phiSeed, uint256 ctrl) external {
        uint256 before = props.length;
        commit(aSeed, dSeed, phiSeed, ctrl);
        if (props.length == before) return;
        revealProposal(before);
        finalizeBatch(before);
    }

    /// @dev Mode III puncture -> absorb top-up -> hold expiry: leaves an absorbed window d_abs > 0 behind (later T2s then run with d_abs > 0)
    function slashAndAbsorb(uint256 aSeed, uint256 axSeed, uint256 dSeed, uint256 amt) external {
        revealSlash(aSeed, axSeed, 1, dSeed);
        uint32 n = esm.datasetCount();
        for (uint32 id = 1; id <= n; ++id) {
            (A.DataState memory d,,, uint64 hs) = _ds(id);
            if (d.dHold == 0) continue;
            if (clock < uint256(hs) + N_HOLD) topUpAbsorb(aSeed, id - 1, amt);
            expireHold(id - 1);
        }
    }

    function proposalCount() external view returns (uint256) {
        return props.length;
    }
}

/// @notice Stateful invariant fuzzing of ESM (Foundry `invariant_*`, handler based; forge-std free: `targetContracts()` is the interface forge reads).
///         After ANY sequence of handler calls:
///         (1) SupplyInv: wallets + locked + burned + redeemed == minted AND the ledger equals the real ERC-20 balance of the contract;
///         (2) DataInv of every dataset: frontier partition identity + the pool lower bound B_rem >= ceil(B0 * Phi_best / Phi0);
///         (3) the reservation cap: S_paid(v, D_k) <= Delta_amort(v, D_k) for every axiom and dataset (plus the Stage-1/2 bookkeeping behind it).
contract ESMInvariant {
    ESMHandler internal h;
    ESM internal esm;

    function setUp() public {
        h = new ESMHandler();
        esm = h.esm();
    }

    function targetContracts() public view returns (address[] memory a) {
        a = new address[](1);
        a[0] = address(h);
    }

    function invariant_supplyConservation() public view {
        require(esm.supplyInvariant(), "SupplyInv: wallets + locked + burned + redeemed == minted == real balance");
    }

    function invariant_allDatasetsValid() public view {
        uint32 n = esm.datasetCount();
        for (uint32 k = 1; k <= n; ++k) {
            require(esm.dataInvariant(k), "DataInv (frontier partition identity)");
            (A.DataState memory d,,,,,,) = esm.datasetData(k);
            require(d.BRem >= M.ceilDiv(d.B0 * d.PhiBest, d.Phi0), "pool lower bound B_rem >= ceil(B0 Phi_best / Phi0)");
        }
    }

    function invariant_rootCapBounded() public view {
        uint32 na = esm.axiomCount();
        uint32 nd = esm.datasetCount();
        for (uint32 v = 1; v <= na; ++v) {
            for (uint32 k = 1; k <= nd; ++k) {
                require(esm.sPaid(v, k) <= esm.deltaAmort(v, k), "S_paid(v_s, D_k) <= Delta_amort(v_s, D_k)");
            }
            require(esm.reservationInvariant(v), "S_paid <= Saved <= Delta_amort and R_cap <= Saved");
        }
    }

    // ---------------------------------------------------------------- guard against a vacuous fuzzer: a scripted run must reach every schema
    function _drive() internal {
        // actors 0..5; seeds are only used to pick among a handful of entities
        h.registerDataset(0, 5_000 * 10_000, 50 * 10_000, 0); // dataset 1: 1024 x 16 bits
        h.registerDataset(1, 100 * 10_000, 10 * 10_000, 1); // dataset 2: 16 x 4 bits (closed normally later)
        h.deposit(0, 1e6);
        h.withdraw(0, 1e6);
        for (uint256 b = 0; b < 6; ++b) {
            h.commit(b, 0, 7 + 3 * b, (b << 8) | (b + 1) << 48 | uint256(0x5555) << 100); // admissible S_c; cites chosen from earlier axioms
            h.commit(b + 1, 0, 11 + b, (b << 16) | uint256(1) << 48);
            h.revealProposal(0);
            h.revealProposal(1);
            h.finalizeBatch(0);
            h.finalizeBatch(1);
        }
        h.commit(2, 0, 3, 1 << 48); // a commit that is never revealed -> forfeited
        h.forfeitUnrevealed(0);
        h.forfeitUnrevealed(1);
        h.forfeitUnrevealed(2);
        for (uint256 i = 0; i < 4; ++i) h.revealReduction(i, 7 + i, 3 + i, 5 + i);
        h.stakeDict(1, 1, 100 * 10_000);
        h.stakeDict(2, 1, 50 * 10_000);
        h.epochUpdate();
        h.requestUnstake(2, 1, 50 * 10_000);
        h.epochUpdate();
        h.unstakeDict(2, 1);
        h.claimDict(1, 1);
        for (uint256 i = 0; i < 3; ++i) h.sponsorRBF(i + 3, i, 99);
        h.revealSlash(0, 1, 1, 9); // III (odd mode seed)
        h.topUpAbsorb(1, 0, 20);
        h.expireHold(0);
        h.revealSlash(1, 2, 1, 5); // III while d_abs > 0
        h.revealSlash(2, 3, 0, 77); // II-A while d_abs > 0 (even mode seed)
        h.expireHold(0);
        h.settle(0);
        h.settle(1);
        h.closeDataset(0);
        h.closeDataset(1);
        h.flushBurn();
    }

    function test_handler_reaches_every_schema() public {
        _drive();
        require(esm.supplyInvariant(), "supply");
        string memory miss;
        for (uint8 b = 1; b <= 18; ++b) {
            if (h.ok(b) == 0) miss = string.concat(miss, " ", _s(b));
        }
        require(bytes(miss).length == 0, string.concat("handler actions never succeeded:", miss));
        require(h.okSlashII() > 0, "T2 mode II-A never succeeded");
        require(h.okSlashIII() > 0, "T2 mode III never succeeded");
        require(h.okSlashWithAbsorbed() > 0, "T2 never ran with d_abs > 0");
        require(h.okAdmissionRejects() > 0, "no admission rejection reached");
        for (uint8 b = 1; b <= 18; ++b) require(esm.branchHits(b) > 0, string.concat("ledger schema not exercised: ", _s(b)));
    }

    function _s(uint8 b) internal pure returns (string memory) {
        bytes memory o = new bytes(2);
        o[0] = bytes1(uint8(48 + b / 10));
        o[1] = bytes1(uint8(48 + b % 10));
        return string(o);
    }
}
