// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {Base} from "./Base.sol";
import {ESMMath as M} from "../src/ESMMath.sol";

/// @notice Recomputes the cells of the paper's Tables 3-7 with the Solidity port and compares with the printed values.
///  Table 3 (BLC benchmarks)            : all cells that are arithmetic of the accounting model (code, Phi, Delta, %, escrow, royalty, Stage 2)
///  Table 4 (cash-flow trajectories)    : all 25 cells (N = 1, 5, 6, 10, 15 x 5 strategies)
///  Table 5 (sensitivity)               : every row (gamma_max, kappa_min, f_grind, q_detect, R_net, N_cite, N_repay) + integer scans
///  Tables 6-7 (ablation equilibria)    : only the cells that follow from accounting identities (royalty = 12 x 9, burn 50, sponsor 38/76, nets).
///                                        Equilibrium quantities (welfare W, P net, clone Q payoffs) need the game solver
///                                        `esm_exp3_ablation.py`, which is not part of the delivered sources: NOT verified here.
contract Tables is Base {
    // ================================================================== Table 3
    struct Row {
        uint256 code;
        uint256 phi;
        uint256 delta;
        uint256 esc;
        uint256 pct;
    }

    function _bench(uint256 wLen, uint256 ref, uint256 steps, uint256 extra, uint256 lres) internal pure returns (Row memory r) {
        r.code = wLen + ref + M.eliasOmegaLen(steps) + extra;
        r.phi = r.code + lres;
        r.delta = 16384 - r.phi;
        r.esc = M.escrowAlloc(10000, 16384, r.delta);
        r.pct = (r.delta * 10000) / 16384;
    }

    function _enet(uint256 esc) internal pure returns (uint256) {
        return esc - (500 * esc) / 10000;
    }

    function test_table3_upper_panel() public pure {
        eq(M.eliasOmegaLen(7457), 20, 1);
        eq(M.eliasOmegaLen(904), 17, 2);
        eq(M.eliasOmegaLen(911), 17, 3);
        eq(M.eliasOmegaLen(920), 17, 4);
        Row memory b1 = _bench(360, 2, 7457, 0, 34); // |w1| = 360, l_ref = 2, max steps 7457, k_err = 0 -> L_res = 34
        ok(b1.code == 382 && b1.phi == 416 && b1.delta == 15968 && b1.pct == 9746 && b1.esc == 9746, 10);
        Row memory b2 = _bench(4, 3, 904, 85, 1290); // unamortized axiom: + |p_s| = 85
        ok(b2.code == 109 && b2.phi == 1399 && b2.delta == 14985 && b2.pct == 9146 && b2.esc == 9146, 20);
        Row memory b3 = _bench(48, 3, 911, 4, 750); // amortized axiom: + l_E(v_s) = 4
        ok(b3.code == 72 && b3.phi == 822 && b3.delta == 15562 && b3.pct == 9498 && b3.esc == 9498, 30);
        eq(_enet(b3.esc), 9024, 31);
        eq(M.calcRoyalty(2000, 9024, 81, b3.delta), 9, 32); // "(9 roy.)"
        // Delta_amort(v_s, D_3) = 85 (fully amortized) needs a burn of 50 tokens at B = 10000, Phi0 = 16384
        eq(M.deltaAmort(85, 50, 10000, 16384, 9500), 85, 33);
        ok(M.deltaAmort(85, 49, 10000, 16384, 9500) < 85, 34);
    }

    function test_table3_lower_panel_benchmark4() public pure {
        // ---- 4A: beta-eta-padded clone, |p_iA| = 103, |q_A| = 4, cited by w3 on D3
        Row memory a = _bench(48, 3, 920, 4, 750);
        ok(a.code == 72 && a.phi == 822 && a.delta == 15562 && a.esc == 9498, 1);
        eq(a.phi + (103 - 85), 840, 2); // Phi_local partial
        uint256 lredA = M.monus(103, 4 + 1);
        eq(lredA, 98, 3);
        (uint256 xisA, uint256 xiiA, uint256 leftA) = M.stage2Redirect(103 - 4, lredA, 81);
        ok(xisA == 81 && xiiA == 18 && leftA == 0, 4);
        eq(M.calcRoyalty(2000, _enet(a.esc), xisA, a.delta), 9, 5);
        eq(M.calcRoyalty(2000, _enet(a.esc), xiiA, a.delta), 2, 6);
        // ---- 4B: inlined derivative clone, |p_iB| = 126, |q_B| = 48, cited by w2 on D3
        Row memory b = _bench(4, 3, 911, 4, 750);
        ok(b.code == 28 && b.phi == 778 && b.delta == 15606 && b.esc == 9525, 10);
        eq(b.phi + (126 - 85), 819, 11);
        uint256 lredB = M.monus(126, 48 + 1);
        eq(lredB, 77, 12);
        (uint256 xisB, uint256 xiiB,) = M.stage2Redirect(126 - 4, lredB, 81);
        ok(xisB == 77 && xiiB == 45, 13);
        eq(M.calcRoyalty(2000, _enet(b.esc), xisB, b.delta), 8, 14);
        eq(M.calcRoyalty(2000, _enet(b.esc), xiiB, b.delta), 5, 15);
        // floor superadditivity (syntactic_reduction_waterfall_valid): the clone can never divert more than the honest royalty
        le(9 + 2, M.calcRoyalty(2000, _enet(a.esc), 99, a.delta), 16);
        le(8 + 5, M.calcRoyalty(2000, _enet(b.esc), 122, b.delta), 17);
    }

    // ================================================================== Table 4
    function _waterfall(uint256 n) internal pure returns (int256 alice, int256 sponsor, int256 attacker) {
        uint256 debt = 1900; // D0 = 2.0 x 950
        uint256 owner;
        uint256 paid;
        uint256 debt2 = 1900;
        uint256 attOwner;
        uint256 rx = M.calcRoyalty(2000, 950, 1000, 1000); // 190 gross per dataset (Phi0 = 1e6, E_net = 950)
        uint256 r1 = M.calcRoyalty(2000, 950, 89990, 99990); // Strategy 5: redirected slot  -> 170
        uint256 r2 = M.calcRoyalty(2000, 950, 10000, 99990); // retained slot                -> 19
        for (uint256 k = 0; k < n; ++k) {
            M.M1 memory m = M.m1RedirectRbfPriority(rx, 1000, debt, 0, 0);
            debt -= m.paidU;
            paid += m.paidU;
            owner += m.owner;
            M.M1 memory s1 = M.m1RedirectRbfPriority(r1, 1000, debt2, 0, 0);
            debt2 -= s1.paidU;
            attOwner += s1.owner;
            M.M1 memory s2 = M.m1RedirectRbfPriority(r2, 1000, debt2, 0, 0);
            debt2 -= s2.paidU;
            attOwner += s2.owner;
        }
        alice = int256(owner); // 0 upfront
        sponsor = int256(paid) - 950;
        attacker = int256(attOwner) - 865;
    }

    function test_table4_all_25_cells() public pure {
        // Strategy 1: single-dataset pre-embedding
        (uint256 dA, uint256 dS, uint256 dR) = M.preEmbedding(100_000, 950, 10_000, 1_000_000, 10, 9500);
        ok(dA == 100_000 && dS == 99_990, 1);
        uint256 eTr = M.escrowAlloc(10_000, 1_000_000, dS);
        eq(eTr, 999, 2);
        eq(dR, 949, 3);
        int256 s1 = int256(dR) - 950 - 10;
        ok(s1 == -11, 4);
        ok(int256(eTr - (500 * eTr) / 10000) - 950 - 10 == -10, 5); // ceiling settlement form: -10
        // Strategy 2: self-funded author
        uint256 rnet = M.netRoyaltyPerDataset(2000, 950, 1000);
        eq(rnet, 171, 6);
        uint256[5] memory ns = [uint256(1), 5, 6, 10, 15];
        int256[5] memory s2 = [int256(-789), -105, 66, 750, 1605];
        int256[5] memory s3 = [int256(0), 0, 0, 0, 665];
        int256[5] memory s4 = [int256(-779), -95, 76, 760, 950];
        int256[5] memory s5 = [int256(-865), -865, -865, -865, -200];
        for (uint256 i = 0; i < 5; ++i) {
            ok(int256(ns[i] * rnet) - 960 == s2[i], 20 + i);
            (int256 al, int256 sp, int256 at) = _waterfall(ns[i]);
            ok(s1 == -11, 30 + i);
            ok(al == s3[i], 40 + i);
            ok(sp == s4[i], 50 + i);
            ok(at == s5[i], 60 + i);
        }
        // RBF debt is retired on dataset 12: 19 tokens of the 1900 cap remain, Alice keeps 152
        (int256 a11,,) = _waterfall(11);
        (int256 a12,,) = _waterfall(12);
        ok(a11 == 0 && a12 == 152, 70);
        // Strategy 5 per-dataset interception: 153 + 18 = 171
        eq(M.calcRoyalty(2000, 950, 89990, 99990) - (uint256(1000) * 170) / 10000, 153, 71);
        eq(M.calcRoyalty(2000, 950, 10000, 99990) - (uint256(1000) * 19) / 10000, 18, 72);
        eq(M.calcRoyalty(2000, 950, 89990, 99990), 170, 73);
    }

    // ================================================================== Table 5
    function test_table5_1a_gamma_max_and_1b_kappa_min() public pure {
        uint256[4] memory kap = [uint256(3000), 5000, 7000, 9000];
        uint256[4] memory g0 = [uint256(3157), 5263, 7368, 9473];
        uint256[4] memory g1 = [uint256(1578), 2631, 3684, 4736];
        for (uint256 i = 0; i < 4; ++i) {
            eq(M.gammaMax(kap[i], 10000, 0, 500), g0[i], i);
            eq(M.gammaMax(kap[i], 10000, 10000, 500), g1[i], 10 + i);
        }
        uint256[4] memory gam = [uint256(1000), 2000, 3000, 4000];
        uint256[4] memory k0 = [uint256(951), 1901, 2851, 3801];
        uint256[4] memory k1 = [uint256(1901), 3801, 5701, 7601];
        for (uint256 i = 0; i < 4; ++i) {
            eq(M.kappaMin(gam[i], 10000, 0, 500), k0[i], 20 + i);
            eq(M.kappaMin(gam[i], 10000, 10000, 500), k1[i], 30 + i);
        }
        // baseline: gamma = 2000 < 3684 and kappa = 7000 > 3801; margin 3500 - 1900 = +1600 bps
        ok(2000 < M.gammaMax(7000, 10000, 10000, 500) && 7000 > M.kappaMin(2000, 10000, 10000, 500), 40);
        eq((7000 * 10000) / 20000, 3500, 41);
        eq((2000 * 9500) / 10000, 1900, 42);
        eq(3500 - 1900, 1600, 43);
    }

    function _scan(uint256 kappa, uint256 gamma, uint256 lam) internal pure returns (uint256 viol, uint256 firstE, uint256 burnAtFirst, uint256 evadeAtFirst) {
        for (uint256 e = 1; e <= 20000; ++e) {
            uint256 sc = M.ceilDiv(10000 * e, 10000 + lam); // S_creator = R_gross / (1 + Lambda), rounded up
            uint256 burn = M.slashSplit(10000, sc, kappa).burn; // r_bps = 10000
            uint256 ev = (gamma * (e - (500 * e) / 10000)) / 10000; // royalty evaded by e2, on E_net = E_tr - floor(eps E_tr / 10000)
            if (!(burn > ev)) {
                if (viol == 0) (firstE, burnAtFirst, evadeAtFirst) = (e, burn, ev);
                viol++;
            }
        }
    }

    function test_table5_exhaustive_integer_scan_E_1_to_20000() public pure {
        (uint256 v0,,,) = _scan(7000, 2000, 10000); // baseline (kappa 7000, gamma 2000, Lambda = 1)
        eq(v0, 0, 1); // "zero integer-rounding violations across all E_tr in [1, 20000]"
        (uint256 v1, uint256 e1, uint256 b1, uint256 r1) = _scan(3000, 3000, 0); // knife-edge: +150 bps continuous margin
        ok(v1 == 1 && e1 == 10 && b1 == 3 && r1 == 3, 2); // "a single integer tie S_burn = R_evade = 3 at E_tr = 10"
        eq((uint256(500) * 10) / 10000, 0, 3); // floor(eps E_tr / 10000) = 0
    }

    function test_table5_2a_grinding_threshold_and_2b_inspection_rate() public pure {
        uint256[3] memory ks = [uint256(16), 32, 64];
        // the paper certifies f_grind on a 1e-6 grid: the SMALLEST ppm with (1-f)^K <= ratio, i.e. ceil(f * 1e6)
        uint256[3] memory p0 = [uint256(52180), 26440, 13309]; // units of 1e-4 %
        uint256[3] memory p1 = [uint256(78739), 40177, 20295];
        uint256[3] memory t0 = [uint256(5218), 2644, 1331]; // 3-decimal values of the main table (units of 1e-3 %)
        uint256[3] memory t1 = [uint256(7874), 4018, 2030];
        for (uint256 i = 0; i < 3; ++i) {
            uint256 a0 = (M.fGrindPpb(ks[i], 7000, 0) + 999) / 1000; // ppb -> ppm, rounded up
            uint256 a1 = (M.fGrindPpb(ks[i], 7000, 10000) + 999) / 1000;
            eq(a0, p0[i], i);
            eq(a1, p1[i], 10 + i);
            eq((a0 + 5) / 10, t0[i], 20 + i);
            eq((a1 + 5) / 10, t1[i], 23 + i);
        }
        uint256[3] memory kq = [uint256(5000), 7000, 9000];
        uint256[3] memory q0 = [uint256(6552), 5758, 5135]; // alpha -> 1 : slash = kappa
        uint256[3] memory q1 = [uint256(7917), 7308, 6786];
        for (uint256 i = 0; i < 3; ++i) {
            eq((M.qDetectPpm(kq[i], 0) + 50) / 100, q0[i], 30 + i);
            eq((M.qDetectPpm(kq[i], 10000) + 50) / 100, q1[i], 40 + i);
        }
        eq((M.qDetectPpm(10000, 0) + 50) / 100, 4872, 50); // alpha = 0
        eq((M.qDetectPpm(10000, 10000) + 50) / 100, 6552, 51);
    }

    function test_table5_3_recovery_N_cite_N_repay() public pure {
        uint256[5] memory gam = [uint256(1000), 1500, 2000, 2500, 3000];
        uint256[5] memory rn = [uint256(86), 128, 171, 214, 257];
        uint256[5] memory nc = [uint256(12), 8, 6, 5, 4];
        uint256[5] memory nr = [uint256(23), 15, 12, 9, 8];
        for (uint256 i = 0; i < 5; ++i) {
            uint256 r = M.netRoyaltyPerDataset(gam[i], 950, 1000);
            eq(r, rn[i], i);
            eq(M.ceilDiv(950, r), nc[i], 10 + i);
            eq(M.ceilDiv(1900, r), nr[i], 20 + i);
            eq(M.ceilDiv(960, r), nc[i], 30 + i); // N_cite(+DA) identical in every cell at beta_D = 1000 ...
        }
        // ... except (gamma = 2500, beta_D = 2000): 5 -> 6
        uint256 r2 = M.netRoyaltyPerDataset(2500, 950, 2000);
        ok(M.ceilDiv(950, r2) == 5 && M.ceilDiv(960, r2) == 6, 40);
    }

    // ================================================================== Tables 6-7 (accounting cells only)
    function test_table6_7_accounting_identities() public pure {
        uint256 roy9 = M.calcRoyalty(2000, 9024, 81, 15562);
        eq(12 * roy9, 108, 1); // author royalty over N = 12 datasets
        eq(216, 24 * roy9, 2); // N = 24
        // burn needed to fully amortize the 85-bit root (B = 10000, Phi0 = 16384, net 9500)
        uint256 burn;
        while (M.deltaAmort(85, burn, 10000, 16384, 9500) < 85) burn++;
        eq(burn, 50, 3);
        uint256 da = M.ceilDiv(85, 10000); // DA fee ceil(1e-4 x 85 bits) = 1 token
        eq(da, 1, 4);
        // S1 author net for M3 / M4- / M4: royalty - burn - g_tx - DA - c_dev = 108 - 50 - 1 - 1 - 20 = +36
        ok(int256(108) - int256(burn) - 1 - int256(da) - 20 == 36, 5);
        // M2 (no burn): 99 - 1 - 1 - 20 = +77 ; M1 with nothing published: -(1 + 1 + 20) = -22
        ok(int256(99) - 1 - int256(da) - 20 == 77, 6);
        ok(-int256(1 + da + 20) == -22, 7);
        // phase boundary c_dev <= 56 = 108 - 50 - 1 - 1
        eq(108 - 50 - 1 - 1, 56, 8);
        // Table 7, capital-constrained author (budget 12): own burn 12 + sponsor 38 = 50; debt 2.0 x 38 = 76
        eq(12 + 38, burn, 9);
        eq(2 * 38, 76, 10);
        ok(int256(108) - 12 - 1 - int256(da) - 20 - 76 == -2, 11); // M4, N = 12: royalty 108, net -2
        ok(int256(216) - 12 - 1 - int256(da) - 20 - 76 == 106, 12); // M4, N = 24: +106
        ok(int256(76) - 38 == 38, 13); // sponsor earns +38
        ok(int256(0) - 12 - 1 - int256(da) - 20 == -34, 14); // M3: royalty 0, net -34
        ok(int256(12) - 12 - 1 - int256(da) - 20 == -22, 15); // M4-: royalty 12, net -22
        // monotone phase boundaries of the 3-axis sweep: gas-indexed audit stake  floor(0.30 S_audit) > 2 g_tx + 1 + 1
        uint256 c = 30;
        ok((c * 20) / 100 > 2 * 1 + 1 + 1 && (c * 24) / 100 > 2 * 2 + 1 + 1 && (c * 44) / 100 > 2 * 5 + 1 + 1, 16);
        ok(!((c * 20) / 100 > 2 * 2 + 1 + 1) && !((c * 23) / 100 > 2 * 2 + 1 + 1) && !((c * 43) / 100 > 2 * 5 + 1 + 1), 17);
    }
}
