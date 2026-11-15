// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {ESM} from "../src/ESM.sol";
import {ESMStorage} from "../src/ESMStorage.sol";
import {ESMAccounting as A} from "../src/ESMAccounting.sol";
import {ESMMath as M} from "../src/ESMMath.sol";
import {IERC20, IVerifier, IVerifierRegistry, ISeedBeacon, IArchiveRegistry, IDrandVerifier} from "../src/Interfaces.sol";
import {VerifierRegistry, MockVerifier} from "../src/VerifierRegistry.sol";
import {SeedBeacon, MockDrand} from "../src/SeedBeacon.sol";
import {ArchiveRegistry} from "../src/ArchiveRegistry.sol";

interface VmX {
    function roll(uint256) external;
    function prank(address) external;
    function getNonce(address) external view returns (uint64);
}

contract MockWETH is IERC20 {
    mapping(address => uint256) public override balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;

    function mint(address to, uint256 a) external { balanceOf[to] += a; }
    function approve(address s, uint256 a) external returns (bool) { allowance[msg.sender][s] = a; return true; }
    function transfer(address to, uint256 a) external virtual returns (bool) { _mv(msg.sender, to, a); return true; }
    function transferFrom(address f, address to, uint256 a) external virtual returns (bool) {
        allowance[f][msg.sender] -= a;
        _mv(f, to, a);
        return true;
    }
    function _mv(address f, address to, uint256 a) internal virtual { balanceOf[f] -= a; balanceOf[to] += a; }
}

/// @dev 1 % fee-on-transfer token: must be rejected by the vault's balance-difference check
contract FeeToken is MockWETH {
    function _mv(address f, address to, uint256 a) internal override {
        balanceOf[f] -= a;
        balanceOf[to] += a - a / 100;
    }
}

/// @notice Full lifecycle T0 -> T1 -> T6 -> RBF -> T2 (II-A, III) -> T3 -> T4 -> T5 on one dataset (+ a second dataset for the normal close),
///         SupplyInv and DataInv are asserted after EVERY step. Amounts are in units of 1e-4 token (1 token = 10_000 units).
contract ESMIntegration {
    VmX internal constant cheats = VmX(address(uint160(uint256(keccak256("hevm cheat code")))));
    uint256 internal constant TOK = 10_000;
    uint256 internal constant S_C = 5_000 * TOK; // creator collateral: S_c >= ceil(E_tr / 2) holds for every E_tr <= B0 = 10,000 tokens (Lambda = 1)
    uint256 internal constant S_UW = 2_000 * TOK; // underwriter co-stake <= Lambda S_c
    bytes32 internal constant VK1 = keccak256("esm-core/t1/v0");
    bytes32 internal constant VK2 = keccak256("esm-core/t2/v0");
    bytes32 internal constant VK3 = keccak256("esm-core/t6/v0");

    MockWETH internal weth;
    VerifierRegistry internal reg;
    MockVerifier internal mv;
    SeedBeacon internal beacon;
    ArchiveRegistry internal archive;
    ESM internal esm;
    uint256 internal G;
    uint256 internal lam = 10_000; // underwriter leverage Lambda_bps of the deployed ESM

    address internal alice = _u(0xA11CE);
    address internal bob = _u(0xB0B);
    address internal carol = _u(0xCA401);
    address internal dave = _u(0xDA7E);
    address internal erin = _u(0xE41);
    address internal fay = _u(0xFA1);
    address internal frank = _u(0xF4A4);
    address internal gina = _u(0x61A);
    address internal ivan = _u(0x1AA);
    address internal hal = _u(0x4A1);
    address internal ivy = _u(0x1B1);
    address internal mallory = _u(0xBAD);
    address internal relayer = _u(0x7E1A7);

    bytes32[8] internal progHash;
    uint256[8] internal progBits;
    uint256[8] internal gasUsed;
    uint256 internal gi;

    function _u(uint256 n) internal pure returns (address) { return address(uint160(n)); }
    uint256 internal clk; // own clock: the via-IR optimizer may reuse `block.number` across cheatcode rolls inside one function
    function _roll(uint256 b) internal { clk = b; cheats.roll(b); }

    function _addr(address d, uint256 nonce) internal pure returns (address) {
        require(nonce < 128 && nonce > 0, "nonce");
        return address(uint160(uint256(keccak256(abi.encodePacked(bytes1(0xd6), bytes1(0x94), d, bytes1(uint8(nonce)))))));
    }

    function _inv(string memory where_) internal view {
        require(esm.supplyInvariant(), string.concat("SupplyInv broken after ", where_));
        for (uint32 i = 1; i <= esm.datasetCount(); ++i) require(esm.dataInvariant(i), string.concat("DataInv broken after ", where_));
    }

    // ---------------------------------------------------------------- deployment
    function _deploy() internal {
        G = block.number;
        clk = G;
        weth = new MockWETH();
        mv = new MockVerifier();
        reg = new VerifierRegistry(address(this), G + 1_000_000_000);
        reg.addVersion(1, VK1, mv);
        reg.addVersion(2, VK2, mv);
        reg.addVersion(3, VK3, mv);
        beacon = new SeedBeacon(G, 120, relayer, new MockDrand(), 1000, 1);
        uint64 n = cheats.getNonce(address(this));
        archive = new ArchiveRegistry(_addr(address(this), uint256(n) + 1));
        ESMStorage.Params memory p = ESMStorage.Params({daFeePerBit: 1, sAudit: 20 * TOK, commitCollateralBps: 500, phiGuarBps: 5000, eps0: TOK, lambdaBps: lam});
        esm = new ESM(IERC20(address(weth)), IVerifierRegistry(address(reg)), ISeedBeacon(address(beacon)), IArchiveRegistry(address(archive)), p);
        require(address(esm) == address(archive.esm()), "archive/esm address mismatch");
        beacon.bind(esm);
        address[12] memory us = [alice, bob, carol, dave, erin, fay, frank, gina, ivan, hal, ivy, mallory];
        for (uint256 i = 0; i < us.length; ++i) {
            weth.mint(us[i], 1e12);
            cheats.prank(us[i]);
            weth.approve(address(esm), type(uint256).max);
            cheats.prank(us[i]);
            esm.deposit(1e12);
        }
        _inv("deposits");
    }

    // ---------------------------------------------------------------- helpers: proposal flow
    function _mkReveal(address who, uint32 batch, uint256 idx, uint256 pBits, uint256 phi, uint256 lAx, uint256 cAm, uint32[] memory ids, uint256[] memory bits)
        internal
        returns (ESM.Reveal memory r, bytes32 h)
    {
        progHash[idx] = keccak256(abi.encode("prog", idx));
        progBits[idx] = pBits;
        r = ESM.Reveal({
            datasetId: 1, batch: batch, programHash: progHash[idx], progBits: pBits, phiLocal: phi, lAxiom: lAx, cAmort: cAm,
            citeIds: ids, citeBits: bits, underwriter: address(0), suw: S_UW, salt: keccak256(abi.encode(who, batch, phi)), vkVersion: 0, proof: ""
        });
        h = esm.proposalHash(who, r);
    }

    function _commit(address who, uint8 kind, uint32 ref, bytes32 h) internal {
        cheats.prank(who);
        esm.commit(kind, ref, h, kind == 1 ? S_C : 0);
    }

    function _seed(uint32 batch) internal {
        cheats.prank(relayer);
        beacon.relaySeed(batch, keccak256(abi.encode("l1-randao", batch)));
    }

    function _proof(bytes32 vk, bytes memory pv) internal pure returns (bytes memory) {
        return abi.encode(keccak256(abi.encode(vk, pv)));
    }

    function _reveal(address who, ESM.Reveal memory r) internal {
        r.proof = _proof(VK1, esm.proposalPublicValues(who, r));
        cheats.prank(who);
        esm.revealProposal(r);
    }

    function _expectRevert(address who, bytes memory data, bytes4 sel, string memory what) internal {
        cheats.prank(who);
        (bool ok, bytes memory ret) = address(esm).call(data);
        require(!ok, string.concat("expected revert: ", what));
        require(ret.length >= 4 && bytes4(ret) == sel, string.concat("wrong error: ", what));
    }

    /// @dev one adoption: commit -> seed -> reveal -> finalize (the only candidate wins)
    function _adoptOne(uint32 batch, address who, uint256 idx, uint256 pBits, uint256 phi, uint256 lAx, uint256 cAm, uint32[] memory ids, uint256[] memory bits) internal {
        uint256 S = G + uint256(batch) * 300;
        _roll(S + 5);
        (ESM.Reveal memory r, bytes32 h) = _mkReveal(who, batch, idx, pBits, phi, lAx, cAm, ids, bits);
        _commit(who, 1, 1, h);
        _roll(S + 120);
        _seed(batch);
        _roll(S + 125);
        _reveal(who, r);
        _roll(S + 300);
        uint256 g = gasleft();
        esm.finalizeBatch(1, batch);
        gasUsed[gi++] = g - gasleft();
        _inv("adopt");
    }

    function _reduce(address finder, uint32 vi, uint32 vs, uint256 qLen, uint256 idxLen, uint256 fuel) internal {
        ESM.RevealT6 memory r = ESM.RevealT6({vi: vi, vs: vs, qLen: qLen, idxLen: idxLen, fuelMax: fuel, salt: keccak256(abi.encode("t6", vi)), vkVersion: 0, proof: ""});
        _commit(finder, 3, vi, esm.t6Hash(finder, r));
        _roll(clk + 1);
        r.proof = _proof(VK3, abi.encode(uint8(3), vs, vi, progHash[vs], progHash[vi], progBits[vs], progBits[vi], qLen, idxLen, fuel, finder));
        cheats.prank(finder);
        esm.revealReduction(r);
        _inv("T6");
    }

    function _slash(address hunter, uint32 aid, uint8 mode, uint256 dUnroll, bool blame) internal {
        ESMStorage.RevealT2 memory r = ESMStorage.RevealT2({axiomId: aid, mode: mode, dUnroll: dUnroll, blameDataset: blame, evidence: keccak256("Z_punct"), salt: keccak256(abi.encode("t2", aid)), vkVersion: 0, proof: ""});
        _commit(hunter, 2, aid, esm.slashHash(hunter, r));
        _roll(clk + 1);
        (, uint32 ds_,,,,,,,,,,,) = esm.axiomCore(aid);
        r.proof = _proof(VK2, abi.encode(uint8(2), mode, aid, ds_, archive.rootOf(ds_), progHash[aid], dUnroll, blame, r.evidence, hunter));
        cheats.prank(hunter);
        esm.revealSlash(r);
        _inv("T2");
    }

    // ================================================================== the lifecycle
    function test_full_lifecycle_T0_to_T5() public {
        _deploy();
        uint32[] memory none = new uint32[](0);
        uint256[] memory nobits = new uint256[](0);

        // ---- [B1] T0: two datasets (Arweave id / IPFS CID locators), DA fee burned
        uint256 aliceBefore = esm.wallet(alice);
        cheats.prank(alice);
        uint32 d1 = esm.registerDataset(10_000 * TOK, 100 * TOK, keccak256("D1"), 1024, 16, 1, abi.encodePacked(keccak256("arweave-tx-D1")));
        cheats.prank(alice);
        uint32 d2 = esm.registerDataset(100 * TOK, 10 * TOK, keccak256("D2"), 16, 4, 2, new bytes(46));
        require(d1 == 1 && d2 == 2, "ids");
        require(aliceBefore - esm.wallet(alice) == 10_000 * TOK + 100 * TOK + 16384 + 100 * TOK + 10 * TOK + 64, "T0 payment = B0 + S_k + DA burn");
        (A.DataState memory st,,,,,,) = esm.datasetData(1);
        require(st.Phi0 == 16384 && st.PhiBest == 16384 && st.BRem == 10_000 * TOK, "T0 state");
        _inv("T0");

        // ---- [B2],[B3],[B4],[B5] batch 0: Bob wins, Carol is a valid non-winner, Dave never reveals; sender binding stops Mallory
        _roll(G + 5);
        uint256 carolStart = esm.wallet(carol);
        (ESM.Reveal memory rb, bytes32 hb) = _mkReveal(bob, 0, 1, 85, 1000, 85, 2 * 1e5 / 1, none, nobits); // C_amort_burn = 20 tokens
        (ESM.Reveal memory rc, bytes32 hc) = _mkReveal(carol, 0, 7, 70, 1500, 40, 0, none, nobits);
        (, bytes32 hd) = _mkReveal(dave, 0, 6, 60, 1200, 30, 0, none, nobits);
        _commit(bob, 1, 1, hb);
        _commit(carol, 1, 1, hc);
        _commit(dave, 1, 1, hd);
        _expectRevert(mallory, abi.encodeCall(esm.commit, (1, 1, hb, S_C)), ESMStorage.Duplicate.selector, "copied commit hash");
        _inv("commit");
        _roll(G + 110);
        _expectRevert(bob, abi.encodeCall(esm.commit, (1, 1, keccak256("late"), S_C)), ESMStorage.WrongPhase.selector, "commit after window");
        _roll(G + 119);
        rb.proof = hex"00";
        _expectRevert(bob, abi.encodeCall(esm.revealProposal, (rb)), ESMStorage.WrongPhase.selector, "reveal before the seed delay");
        _roll(G + 120);
        _seed(0);
        _roll(G + 125);
        _expectRevert(mallory, abi.encodeCall(esm.revealProposal, (rb)), ESMStorage.BadReveal.selector, "stolen reveal (sender binding)");
        rc.proof = abi.encode(bytes32(uint256(1))); // forged proof
        _expectRevert(carol, abi.encodeCall(esm.revealProposal, (rc)), ESMStorage.BadProof.selector, "forged proof");
        _reveal(bob, rb);
        _reveal(carol, rc);
        _inv("reveal");
        _roll(G + 300);
        uint256 carolBefore = esm.wallet(carol);
        esm.finalizeBatch(1, 0);
        _inv("batch 0");
        (address pr, uint32 dsx, uint256 dNew,,,,,,, bool actv,,,) = esm.axiomCore(1);
        require(pr == bob && dsx == 1 && dNew == 16384 - 1000 && actv, "winner = best Phi_local");
        uint256 sc = S_C;
        require(carolStart - esm.wallet(carol) == 40, "B4: loser gets S_c and the lock back, only the DA fee (l_axiom = 40 bits) is burned");
        require(esm.wallet(carol) > carolBefore, "loser refunded");
        uint256 daveBefore = esm.wallet(dave);
        esm.forfeitUnrevealed(hd);
        require(esm.wallet(dave) - daveBefore == (3000 * sc) / 10_000, "B5: 30 % refunded, 70 % burned");
        _inv("forfeit");

        // ---- batches 1-4: derivative clones (Carol = 4A, Dave = 4B), a citing axiom (Erin) and the axiom that will be slashed (Fay)
        _adoptOne(1, carol, 2, 103, 900, 103, 60 * TOK, none, nobits); // Clone 4A: fully amortized (C_min = 60 tokens), so it can be cited
        _adoptOne(2, dave, 3, 126, 800, 30, 0, none, nobits);
        uint256 saved1;
        (,,,,,,,,,,,, saved1) = esm.axiomCore(1);
        require(saved1 == M.savedNet(M.deltaAmort(85, 2e5, 10_000 * TOK, 16384, 9500), esm.dictLen(1) == 0 ? 0 : 1), "saving of the root");

        // ---- [B14] T6: Clone 4A (|p_i| = 103, |q| = 4) and Clone 4B (|p_i| = 126, |q| = 48); B_finder = 30 % of S_audit, 70 % burned
        _roll(G + 900 + 10);
        uint256 frankBefore = esm.wallet(frank);
        _reduce(frank, 2, 1, 4, 1, 747);
        (,,,,,, uint32 org2, uint256 lred2,,,,,) = esm.axiomCore(2);
        require(org2 == 1 && lred2 == 98, "Clone 4A: origin <- v_s, L_red = 103 - (4 + 1) = 98");
        require(esm.wallet(frank) - frankBefore == (3000 * 20 * TOK) / 10_000, "B_finder = 30 % of S_audit");
        _reduce(frank, 3, 1, 48, 1, 263);
        (,,,,,, uint32 org3, uint256 lred3,,,,,) = esm.axiomCore(3);
        require(org3 == 1 && lred3 == 77, "Clone 4B: L_red = 126 - (48 + 1) = 77");
        // a reduction needs strict temporal precedence and the launch-profile fuel cap
        {
            ESM.RevealT6 memory bad = ESM.RevealT6({vi: 2, vs: 3, qLen: 4, idxLen: 1, fuelMax: 747, salt: keccak256("rev"), vkVersion: 0, proof: ""});
            _commit(mallory, 3, 2, esm.t6Hash(mallory, bad));
            _roll(clk + 1);
            bad.proof = _proof(VK3, abi.encode(uint8(3), uint32(3), uint32(2), progHash[3], progHash[2], progBits[3], progBits[2], uint256(4), uint256(1), uint256(747), mallory));
            _expectRevert(mallory, abi.encodeCall(esm.revealReduction, (bad)), ESMStorage.Rejected.selector, "v_s must precede v_i");
        }

        // Erin cites the clone v_iA with 60 bits: Stage 2 caps the redirected bits by the root's remaining saving
        uint32[] memory ids = new uint32[](1);
        uint256[] memory bits = new uint256[](1);
        ids[0] = 2;
        bits[0] = 60;
        _adoptOne(3, erin, 4, 90, 700, 25, 0, ids, bits);
        (, uint256[] memory cb, uint256[] memory cx) = esm.axiomCites(4);
        require(cb[0] == 60 && cx[0] == saved1 - 0 || cx[0] <= 60, "stage 2 reservation");
        uint256 xisErin = cx[0];
        require(xisErin == M.min(60, M.min(98, saved1)), "Stage 2: x_{i->s} = min(a, L_red, R_cap)");
        _adoptOne(4, fay, 5, 80, 600, 22, 0, none, nobits);

        // ---- dictionary stake + delayed phi (before the first epoch boundary)
        _roll(G + 1900);
        cheats.prank(hal);
        esm.stakeDict(1, 100 * TOK);
        cheats.prank(ivy);
        esm.stakeDict(1, 50 * TOK);
        cheats.prank(bob);
        esm.setPhiDict(1, 10_000);
        require(esm.phiActive(1) == 0, "phi_dict is delayed to the next epoch");
        _inv("stake");

        // ---- [B13] T5: O(1) epoch updates
        uint256 lenBefore = esm.dictLen(1);
        _roll(G + 49_800);
        uint256 g1 = gasleft();
        esm.epochUpdate();
        g1 -= gasleft();
        require(esm.phiActive(1) == 10_000, "phi_dict active after the boundary");
        require(esm.dictLen(1) < lenBefore, "snapshot weights shorten the dictionary code");
        cheats.prank(ivy);
        esm.requestUnstake(1, 50 * TOK);

        // ---- [B12A] RBF sponsorship after N_LOCK (Bob's axiom was only partially amortized: 20 of ~49 tokens)
        _roll(G + 50_400);
        uint256 target = esm.btarget(1);
        require(target > 0 && target == M.ceilDiv(85 * 9500 * 10_000 * TOK, 10_000 * 16384) - 2e5, "B_target");
        cheats.prank(gina);
        esm.sponsorRBF(1, target / 2);
        cheats.prank(ivan);
        esm.sponsorRBF(1, target - target / 2);
        _inv("RBF");
        require(esm.debtOf(1) == (20_000 * (target / 2)) / 10_000 + (20_000 * (target - target / 2)) / 10_000, "2.0x debt");
        (,,,,,,,, uint256 capAfterRbf,,,, uint256 savedAfter) = esm.axiomCore(1);
        require(savedAfter == 84 && capAfterRbf == savedAfter - saved1 + (saved1 - xisErin), "RBF grows the saving: root cap tracks it");

        // ---- [B6] T2 mode II-A on Fay (training-data fraud, dataset blamed) and [B7] mode III on Erin (partial puncture)
        _roll(G + 50_500);
        (,,, uint256 scF, uint256 suwF,,,,,,,,) = esm.axiomCore(5);
        uint256 hunterBefore = esm.wallet(frank);
        _slash(frank, 5, 1, 0, true);
        require(esm.wallet(frank) - hunterBefore == (3000 * (scF + suwF)) / 10_000, "II-A: hunter gets 30 %, 70 % burned");
        (,, bool pen,,,,) = penFlag();
        require(pen, "dataset flagged penalized");
        uint256 capBefore3;
        (,,,,,,,, capBefore3,,,,) = esm.axiomCore(1);
        (,,, uint256 scE,,,,,,,,,) = esm.axiomCore(4);
        hunterBefore = esm.wallet(frank);
        _slash(frank, 4, 2, 40, false);
        (,, uint256 dNewE, uint256 scE2, uint256 suwE2,,,,,,,,) = esm.axiomCore(4);
        require(dNewE == 60 && suwE2 > 0, "II-A / III: remaining reduction, underwriter collateral untouched");
        uint256 cut = scE - scE2;
        require(cut > 0 && esm.wallet(frank) - hunterBefore == (3000 * cut) / 10_000, "III: cut proportional to the INITIAL reduction, hunter 30 %");
        (, uint256[] memory cb2, uint256[] memory cx2) = esm.axiomCites(4);
        require(cb2[0] == M.slotScale(xisErin, 60, 100) + M.slotScale(60 - xisErin, 60, 100) && cx2[0] == M.slotScale(xisErin, 60, 100), "slot scaled by d_rem / d_tr (xs and xu separately: release_symmetric)");
        (,,,,,,,, uint256 capAfter3,,,,) = esm.axiomCore(1);
        require(capAfter3 == capBefore3 + (xisErin - cx2[0]), "released reservation returns to the root's cap");
        (A.DataState memory h1,,,,,, uint256 uns) = esm.datasetData(1);
        require(h1.dHold == 100 + 40 && uns == 4, "hold window holds the rolled-back bits");

        // ---- [B8A] absorb top-up and [B8B] hold expiry
        cheats.prank(hal);
        esm.topUpAbsorb(1, 100);
        _inv("absorb");
        _roll(G + 50_810);
        esm.expireHold(1);
        _inv("hold expiry");
        (A.DataState memory h2,,,,,,) = esm.datasetData(1);
        require(h2.dHold == 0 && h2.dAbs == 100 && h2.PhiBest == h1.PhiBest + 40, "100 bits absorbed, 40 rewound");

        // ---- second epoch, then [B9] settlement with the 4-stage debt-following waterfall
        _roll(G + 99_600);
        uint256 g2 = gasleft();
        esm.epochUpdate();
        g2 -= gasleft();
        require(g1 < 150_000 && g2 < 150_000, "T5 epoch update gas is bounded");
        _roll(G + 50_810 + 50_000);
        uint256 aliceW = esm.wallet(alice);
        uint256 debtBefore = esm.debtOf(1);
        uint256 gs = gasleft();
        esm.settle(1);
        gs -= gasleft();
        _inv("settle");
        require(esm.wallet(alice) > aliceW, "anchor rebate paid to the data owner");
        require(esm.debtOf(1) < debtBefore, "root RBF debt repaid out of the derivative's royalty stream (debt following)");
        (A.DataState memory h3,,,,,,) = esm.datasetData(1);
        require(h3.dInit == 0 && h3.dAbs == 0 && h3.dSettled > 0 && h3.eSettled > 0, "settled");
        uint256 halBefore = esm.wallet(hal);
        cheats.prank(hal);
        esm.claimDict(1);
        _inv("claim");
        require(esm.wallet(hal) >= halBefore, "dictionary dividend claim");

        // ---- [B12C] unstake after the epoch grace, [B10]/[B11] closes
        cheats.prank(ivy);
        esm.unstakeDict(1);
        cheats.prank(alice);
        esm.closeDataset(1); // penalized: B_rem + 30 % S_k back
        cheats.prank(alice);
        esm.closeDataset(2); // normal
        _inv("close");

        // ---- T5 again with 5 axioms, 2 stakers, 2 sponsors and 2 datasets in the system: warm updates cost the same (no iteration)
        _roll(G + 149_400);
        uint256 g3 = gasleft();
        esm.epochUpdate();
        g3 -= gasleft();
        require((g2 > g3 ? g2 - g3 : g3 - g2) < 3000, "T5 epoch update is O(1): identical warm cost");
        gasUsed[gi++] = g1;
        gasUsed[gi++] = g2;
        gasUsed[gi++] = g3;
        // ---- [B15] everyone withdraws; every one of the 18 schemas ran at least once
        address[12] memory us = [alice, bob, carol, dave, erin, fay, frank, gina, ivan, hal, ivy, mallory];
        for (uint256 i = 0; i < us.length; ++i) {
            uint256 w = esm.wallet(us[i]);
            cheats.prank(us[i]);
            esm.withdraw(w);
        }
        esm.flushBurn();
        require(esm.supplyInvariant(), "SupplyInv after withdrawals + burn flush");
        require(weth.balanceOf(address(0xdEaD)) == esm.flushedBurn() && esm.flushedBurn() > 0, "burned tokens are irrecoverable");
        for (uint8 b = 1; b <= 18; ++b) require(esm.branchHits(b) > 0, string.concat("schema not exercised: ", _s(b)));
    }

    function penFlag() internal view returns (A.DataState memory d, address o, bool pen, uint256 sk, uint64 hs, uint256 ab, uint256 un) {
        uint8 stt;
        (d, o, stt, pen, sk, hs, un) = esm.datasetData(1);
        ab = stt;
    }

    function _s(uint8 b) internal pure returns (string memory) {
        bytes memory o = new bytes(2);
        o[0] = bytes1(uint8(48 + b / 10));
        o[1] = bytes1(uint8(48 + b % 10));
        return string(o);
    }

    // ================================================================== focused tests
    function test_vault_rejects_fee_on_transfer_token() public {
        FeeToken ft = new FeeToken();
        VerifierRegistry r2 = new VerifierRegistry(address(this), block.number + 100);
        SeedBeacon b2 = new SeedBeacon(block.number, 120, relayer, new MockDrand(), 1, 1);
        uint64 n = cheats.getNonce(address(this));
        ArchiveRegistry a2 = new ArchiveRegistry(_addr(address(this), uint256(n) + 1));
        ESM e2 = new ESM(IERC20(address(ft)), IVerifierRegistry(address(r2)), ISeedBeacon(address(b2)), IArchiveRegistry(address(a2)), ESMStorage.Params(1, 1, 500, 5000, 1, 0));
        ft.mint(address(this), 1000);
        ft.approve(address(e2), 1000);
        try e2.deposit(1000) { revert("fee-on-transfer token was accepted"); } catch (bytes memory e) { require(bytes4(e) == ESMStorage.BalanceDiff.selector, "wrong error"); }
        require(e2.supplyInvariant(), "nothing minted");
    }

    function test_vault_mint_cap_and_roundtrip() public {
        MockWETH w = new MockWETH();
        VerifierRegistry r2 = new VerifierRegistry(address(this), block.number + 100);
        SeedBeacon b2 = new SeedBeacon(block.number, 120, relayer, new MockDrand(), 1, 1);
        uint64 n = cheats.getNonce(address(this));
        ArchiveRegistry a2 = new ArchiveRegistry(_addr(address(this), uint256(n) + 1));
        ESM e2 = new ESM(IERC20(address(w)), IVerifierRegistry(address(r2)), ISeedBeacon(address(b2)), IArchiveRegistry(address(a2)), ESMStorage.Params(1, 1, 500, 5000, 1, 0));
        uint256 cap = (uint256(1) << 96) - 1;
        w.mint(address(this), cap + 5);
        w.approve(address(e2), type(uint256).max);
        e2.deposit(cap); // minted == 2^96 - 1 is accepted ...
        try e2.deposit(1) { revert("minted >= 2^96 accepted"); } catch (bytes memory e) { require(bytes4(e) == M.TokenRange.selector, "wrong error"); } // ... one more wei is not
        e2.withdraw(cap);
        require(e2.supplyInvariant() && w.balanceOf(address(e2)) == 0, "round trip");
    }

    function test_registry_guardian_is_time_limited_and_versions_are_immutable() public {
        VerifierRegistry r = new VerifierRegistry(address(this), block.number + 10);
        MockVerifier v = new MockVerifier();
        uint32 v0 = r.addVersion(1, VK1, v);
        bytes memory pv = abi.encode(uint256(7));
        require(r.verify(1, v0, pv, _proof(VK1, pv)), "valid proof");
        require(!r.verify(1, v0, pv, _proof(VK2, pv)), "proof for another program key");
        r.revokeVersion(1, v0);
        require(!r.verify(1, v0, pv, _proof(VK1, pv)), "revoked version");
        cheats.roll(block.number + 10);
        try r.addVersion(1, VK1, v) returns (uint32) { revert("guardian acted after expiry"); } catch (bytes memory e) { require(bytes4(e) == VerifierRegistry.GuardianExpired.selector, "wrong error"); }
    }

    function test_seed_beacon_sources_and_no_early_entropy() public {
        SeedBeacon b = new SeedBeacon(block.number, 120, relayer, new MockDrand(), 1000, 1);
        require(!b.isReady(0), "no entropy yet");
        cheats.prank(relayer);
        try b.relaySeed(0, keccak256("x")) { revert("early relay accepted"); } catch (bytes memory e) { require(bytes4(e) == SeedBeacon.TooEarly.selector, "wrong error"); }
        cheats.roll(block.number + 120);
        try b.relaySeed(0, keccak256("x")) { revert("non-relayer accepted"); } catch (bytes memory e) { require(bytes4(e) == SeedBeacon.NotRelayer.selector, "wrong error"); }
        bytes memory sig = abi.encode(uint256(1000), uint256(42)); // drand round 1000 is batch 0
        b.submitDrand(0, 1000, sig);
        require(b.isReady(0) && b.source(0) == 2, "drand entropy accepted once");
        try b.submitDrand(0, 1000, sig) { revert("second entropy accepted"); } catch (bytes memory e) { require(bytes4(e) == SeedBeacon.AlreadySet.selector, "wrong error"); }
    }

    function test_archive_registry_shape_limits() public {
        ArchiveRegistry a = new ArchiveRegistry(address(this));
        require(a.register(1, keccak256("r"), uint32(1) << 30, 1024, 1, abi.encodePacked(bytes32(0))) == uint256(1) << 40, "Phi0 = 2^40 at the caps");
        try a.register(2, keccak256("r"), (uint32(1) << 30) + 1, 8, 1, abi.encodePacked(bytes32(0))) returns (uint256) { revert("n_k > 2^30"); } catch (bytes memory e) { require(bytes4(e) == ArchiveRegistry.BadShape.selector, "e1"); }
        try a.register(3, keccak256("r"), 8, 1025, 1, abi.encodePacked(bytes32(0))) returns (uint256) { revert("b_k > 2^10"); } catch (bytes memory e) { require(bytes4(e) == ArchiveRegistry.BadShape.selector, "e2"); }
        try a.register(4, keccak256("r"), 8, 8, 1, hex"01") returns (uint256) { revert("short Arweave id"); } catch (bytes memory e) { require(bytes4(e) == ArchiveRegistry.BadLocator.selector, "e3"); }
        // Keccak Merkle membership over 4 records
        bytes32[4] memory l;
        for (uint256 i = 0; i < 4; ++i) l[i] = keccak256(abi.encodePacked(i, bytes2(uint16(i * 7))));
        bytes32 n01 = keccak256(abi.encodePacked(l[0], l[1]));
        bytes32 n23 = keccak256(abi.encodePacked(l[2], l[3]));
        a.register(5, keccak256(abi.encodePacked(n01, n23)), 4, 16, 0, hex"0011");
        bytes32[] memory proof = new bytes32[](2);
        proof[0] = l[3];
        proof[1] = n01;
        require(a.verifyLeaf(5, l[2], 2, proof), "membership");
        require(!a.verifyLeaf(5, l[2], 3, proof), "wrong index");
    }

    // ================================================================== gap tests (spec gaps 1-4)
    function _rejectCode(address who, bytes memory data) internal returns (uint8 code) {
        cheats.prank(who);
        (bool ok, bytes memory ret) = address(esm).call(data);
        require(!ok && ret.length == 36 && bytes4(ret) == ESMStorage.Rejected.selector, "expected Rejected(code)");
        bytes memory tail = new bytes(32);
        for (uint256 i = 0; i < 32; ++i) tail[i] = ret[4 + i];
        code = abi.decode(tail, (uint8));
    }

    function _reg1() internal {
        cheats.prank(alice);
        esm.registerDataset(10_000 * TOK, 100 * TOK, keccak256("D1"), 1024, 16, 1, abi.encodePacked(keccak256("arweave-tx-D1")));
    }

    /// @dev commit with an explicit S_c, relay the seed, return the reveal (proof set)
    function _commitSc(address who, uint256 idx, uint256 sc, uint256 suw, address uw, uint256 phi) internal returns (ESM.Reveal memory r) {
        uint32[] memory none = new uint32[](0);
        uint256[] memory nobits = new uint256[](0);
        bytes32 h;
        (r, h) = _mkReveal(who, 0, idx, 85, phi, 85, 0, none, nobits);
        r.suw = suw;
        r.underwriter = uw;
        h = esm.proposalHash(who, r);
        cheats.prank(who);
        esm.commit(1, 1, h, sc);
    }

    function _finishBatch0(ESM.Reveal memory r, address who) internal {
        _roll(G + 120);
        _seed(0);
        _roll(G + 125);
        r.proof = _proof(VK1, esm.proposalPublicValues(who, r));
    }

    /// Gap 1: S_c is chosen by the proposer and caps the claimable escrow: E_tr <= (10000 + Lambda) S_c / sigma  (Lambda = 1: S_c >= ceil(E/2))
    function test_gap1_creator_collateral_caps_escrow_lambda1() public {
        _deploy();
        _reg1();
        _roll(G + 5);
        uint256 e = M.escrowAlloc(10_000 * TOK, 16384, 16384 - 1000);
        uint256 need = M.ceilDiv(e, 2);
        _expectRevert(bob, abi.encodeCall(esm.commit, (1, 1, keccak256("x"), (500 * 10_000 * TOK) / 10_000 - 1)), ESMStorage.Rejected.selector, "S_c below the spam-prevention minimum");
        _expectRevert(bob, abi.encodeCall(esm.commit, (2, 1, keccak256("y"), 5)), ESMStorage.BadAxiom.selector, "no such axiom");
        ESM.Reveal memory rb = _commitSc(bob, 1, need - 1, 0, address(0), 1000);
        ESM.Reveal memory rc = _commitSc(carol, 2, need, S_UW, address(0), 1000);
        _finishBatch0(rb, bob);
        rc.proof = _proof(VK1, esm.proposalPublicValues(carol, rc));
        require(_rejectCode(bob, abi.encodeCall(esm.revealProposal, (rb))) == 19, "S_c = ceil(E/2) - 1 does not cover E_tr");
        _reveal(carol, rc);
        _roll(G + 300);
        esm.finalizeBatch(1, 0);
        _inv("gap1 adopt");
        (address pr,,, uint256 scA,,,,,,,,,) = esm.axiomCore(1);
        require(pr == carol && scA == need, "S_c = ceil(E/2) is admitted and recorded");
        require(esm.wallet(bob) < 1e12, "Bob's unrevealed commit is forfeitable");
        esm.forfeitUnrevealed(esm.proposalHash(bob, rb));
        _inv("gap1 forfeit");
    }

    /// Gap 1 (Lambda = 0): S_c >= E_tr and no leverage (S_uw must be 0)
    function test_gap1_creator_collateral_caps_escrow_lambda0() public {
        lam = 0;
        _deploy();
        _reg1();
        _roll(G + 5);
        uint256 e = M.escrowAlloc(10_000 * TOK, 16384, 16384 - 1000);
        ESM.Reveal memory rb = _commitSc(bob, 1, e - 1, 0, address(0), 1000);
        ESM.Reveal memory rc = _commitSc(carol, 2, e, 1, address(0), 1000); // S_uw = 1 > Lambda S_c = 0
        ESM.Reveal memory rd = _commitSc(dave, 3, e, 0, address(0), 1000);
        _finishBatch0(rb, bob);
        rc.proof = _proof(VK1, esm.proposalPublicValues(carol, rc));
        rd.proof = _proof(VK1, esm.proposalPublicValues(dave, rd));
        require(_rejectCode(bob, abi.encodeCall(esm.revealProposal, (rb))) == 19, "Lambda = 0: S_c < E_tr");
        require(_rejectCode(carol, abi.encodeCall(esm.revealProposal, (rc))) == 20, "Lambda = 0: no co-stake allowed");
        _reveal(dave, rd);
        _roll(G + 300);
        esm.finalizeBatch(1, 0);
        _inv("gap1 lambda0");
        (address pr,,,,,,,,,,,,) = esm.axiomCore(1);
        require(pr == dave, "S_c = E_tr admitted at Lambda = 0");
    }

    /// Gap 3: external underwriter (consent, S_uw <= Lambda S_c), R_guar and the S_uw refund go to the underwriter wallet
    function test_gap3_external_underwriter_receives_guar_and_collateral() public {
        _deploy();
        _reg1();
        _roll(G + 5);
        ESM.Reveal memory r = _commitSc(bob, 1, S_C, S_UW, gina, 1000);
        _finishBatch0(r, bob);
        require(_rejectCode(bob, abi.encodeCall(esm.revealProposal, (r))) == 21, "the underwriter has not consented");
        cheats.prank(gina);
        esm.setUnderwriterConsent(bob, true);
        uint256 ginaBefore = esm.wallet(gina);
        uint256 bobBefore = esm.wallet(bob);
        _reveal(bob, r);
        require(ginaBefore - esm.wallet(gina) == S_UW, "S_uw is locked from the underwriter's wallet");
        require(bobBefore - esm.wallet(bob) == 20 * TOK + 85, "the proposer only pays S_audit + DA fee (+ C_amort)");
        _inv("gap3 reveal");
        _roll(G + 300);
        esm.finalizeBatch(1, 0);
        (address uw,, , , uint256 suw) = esm.axiomExt(1);
        require(uw == gina && suw == S_UW, "underwriter recorded at adoption");
        ginaBefore = esm.wallet(gina);
        bobBefore = esm.wallet(bob);
        _roll(G + 300 + 50_000);
        esm.settle(1);
        _inv("gap3 settle");
        uint256 gGain = esm.wallet(gina) - ginaBefore;
        uint256 bGain = esm.wallet(bob) - bobBefore;
        require(gGain > S_UW, "underwriter gets S_uw back plus R_guar");
        require(bGain >= S_C + 20 * TOK, "proposer gets S_c + S_audit back plus R_prop");
    }

    /// Gap 3: S_uw > Lambda S_c is rejected
    function test_gap3_cost_of_leverage_is_capped() public {
        _deploy();
        _reg1();
        _roll(G + 5);
        ESM.Reveal memory r = _commitSc(bob, 1, S_C, S_C + 1, gina, 1000);
        _finishBatch0(r, bob);
        cheats.prank(gina);
        esm.setUnderwriterConsent(bob, true);
        require(_rejectCode(bob, abi.encodeCall(esm.revealProposal, (r))) == 20, "S_uw <= Lambda S_c");
    }

    /// Gap 2: Mode III releases (delta xs + delta xu) from the derivative's S_paid and delta xs from the root, so nothing leaks
    function test_gap2_mode3_symmetric_release_on_both_counters() public {
        _deploy();
        uint32[] memory none = new uint32[](0);
        uint256[] memory nobits = new uint256[](0);
        _reg1();
        _adoptOne(0, bob, 1, 85, 1000, 85, 2e5, none, nobits); // root v_s
        _adoptOne(1, carol, 2, 103, 900, 103, 60 * TOK, none, nobits); // clone v_i (fully amortized)
        _roll(G + 900 + 10);
        _reduce(frank, 2, 1, 4, 1, 747); // origin(v_i) = v_s, L_red = 98
        uint32[] memory ids = new uint32[](1);
        uint256[] memory bits = new uint256[](1);
        ids[0] = 2;
        bits[0] = 60;
        (,, uint256 savedRoot0, uint256 capRoot0,) = esm.axiomExt(1);
        _adoptOne(4, erin, 3, 90, 700, 25, 0, ids, bits); // axiom 3, dNew = 200, cites the clone with x = 60
        (, uint256 sp2,,,) = esm.axiomExt(2);
        (,,, uint256 capRoot1,) = esm.axiomExt(1);
        (, uint256[] memory cb0, uint256[] memory cx0) = esm.axiomCites(3);
        require(sp2 == 60 && cb0[0] == 60, "Stage 1 charges the whole slot to the cited axiom");
        require(capRoot0 - capRoot1 == cx0[0] && cx0[0] > 0, "Stage 2 charges x_s to the root");
        _roll(G + 6000);
        _slash(frank, 3, 2, 80, false); // Mode III: retain 120 / 200
        (, uint256 sp2b,,,) = esm.axiomExt(2);
        (,,, uint256 capRoot2,) = esm.axiomExt(1);
        require(sp2b == M.slotScale(cx0[0], 120, 200) + M.slotScale(60 - cx0[0], 120, 200), "derivative counter = base + xs' + xu'");
        require(capRoot2 == capRoot1 + (cx0[0] - M.slotScale(cx0[0], 120, 200)), "root regains delta xs");
        require(esm.reservationInvariant(1) && esm.reservationInvariant(2) && esm.reservationInvariant(3), "reservation bookkeeping");
        _slash(frank, 3, 1, 0, false); // Mode II-A on the rest: everything is released
        (, uint256 sp2c,,,) = esm.axiomExt(2);
        (,,, uint256 capRoot3,) = esm.axiomExt(1);
        require(sp2c == 0, "no residual reservation on the derivative");
        require(capRoot3 == savedRoot0 && savedRoot0 == capRoot0, "no capacity leaks from the root (old_rule_leaks)");
        require(esm.reservationInvariant(1) && esm.reservationInvariant(2), "reservation bookkeeping after II-A");
    }

    /// Gap 4: a tranche cannot hide behind an absorbed reservation (d_abs > 0): T2 still punctures it and the dataset still settles
    function test_gap4_slash_with_absorbed_window_and_settle() public {
        _deploy();
        uint32[] memory none = new uint32[](0);
        uint256[] memory nobits = new uint256[](0);
        _reg1();
        _adoptOne(0, bob, 1, 85, 1000, 85, 2e5, none, nobits); // dNew = 15384
        _adoptOne(1, carol, 2, 90, 900, 90, 0, none, nobits); // dNew = 100
        _roll(G + 5000);
        _slash(frank, 2, 2, 40, false); // Mode III on Carol: 40 bits into the hold window
        cheats.prank(hal);
        esm.topUpAbsorb(1, 40);
        _roll(G + 5000 + 400);
        esm.expireHold(1);
        (A.DataState memory st,,,,,,) = esm.datasetData(1);
        require(st.dAbs == 40 && st.dHold == 0, "absorbed window exists");
        _slash(frank, 2, 1, 0, false); // II-A on Carol's remaining 60 bits while d_abs = 40 > 0 (used to revert with Rejected(5))
        (st,,,,,,) = esm.datasetData(1);
        require(st.dAbs == 40 && st.dHold == 60, "init window rolled back, absorbed window untouched");
        // a second absorption on top of the existing claim is refused (one claimant), the hold rewinds instead
        cheats.prank(ivy);
        (bool ok,) = address(esm).call(abi.encodeCall(esm.topUpAbsorb, (1, 10)));
        require(!ok, "single absorbed claim");
        _roll(clk + 400);
        esm.expireHold(1);
        _inv("gap4 expire");
        _roll(clk + 50_000);
        uint256 halBefore = esm.wallet(hal);
        esm.settle(1);
        _inv("gap4 settle");
        require(esm.wallet(hal) > halBefore, "absorber is paid at settlement");
        uint256 uns;
        (st,,,,,, uns) = esm.datasetData(1);
        require(st.dInit == 0 && st.dAbs == 0 && uns == 0, "dataset settled");
    }
}
