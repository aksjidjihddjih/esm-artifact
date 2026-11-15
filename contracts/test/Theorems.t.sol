// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {Base} from "./Base.sol";
import {ESMMath as M} from "../src/ESMMath.sol";
import {ESMAccounting as A} from "../src/ESMAccounting.sol";

/// @notice One property test per theorem of ESM_verified.lean (numbering = the paper's catalogue; #54 = shannon_len_ceilDiv_iff).
///         Each test restates the Lean theorem on the Solidity port. Inputs are fuzzed (3000 runs) and bounded into the
///         theorem's hypotheses and the frozen ranges of params.toml; Lean `let`-bindings are reproduced line by line.
contract Theorems is Base {
    // 1
    function test_T01_div_le_div_right(uint256 a, uint256 b, uint256 c) public pure {
        (a, b) = a <= b ? (a, b) : (b, a);
        le(M.div0(a, c), M.div0(b, c), 1);
    }

    // 2
    function test_T02_add_div_le_div_add(uint256 x, uint256 y, uint256 c) public pure {
        x = bnd(x, 0, 2 ** 254);
        y = bnd(y, 0, 2 ** 254);
        le(M.div0(x, c) + M.div0(y, c), M.div0(x + y, c), 2);
    }

    // 3
    function test_T03_mul_bps_div_le(uint256 rate, uint256 X) public pure {
        rate = bnd(rate, 0, 10000);
        X = bnd(X, 0, 2 ** 200);
        le((rate * X) / 10000, X, 3);
    }

    // 4
    function test_T04_escrowAlloc_mono(uint256 B, uint256 Phi, uint256 d1, uint256 d2) public pure {
        B = bnd(B, 0, TOK);
        Phi = bnd(Phi, 0, BITS);
        d1 = bnd(d1, 0, BITS);
        d2 = bnd(d2, 0, BITS);
        (d1, d2) = d1 <= d2 ? (d1, d2) : (d2, d1);
        le(M.escrowAlloc(B, Phi, d1), M.escrowAlloc(B, Phi, d2), 4);
    }

    // 5
    function test_T05_escrowAlloc_superadd(uint256 B, uint256 Phi, uint256 d1, uint256 d2) public pure {
        B = bnd(B, 0, TOK);
        Phi = bnd(Phi, 0, BITS);
        d1 = bnd(d1, 0, BITS / 2);
        d2 = bnd(d2, 0, BITS / 2);
        le(M.escrowAlloc(B, Phi, d1) + M.escrowAlloc(B, Phi, d2), M.escrowAlloc(B, Phi, d1 + d2), 5);
    }

    // 6
    function test_T06_pool_lower_bound_ceil(uint256 B, uint256 Phi0, uint256 best, uint256 eu) public pure {
        B = bnd(B, 0, TOK);
        Phi0 = bnd(Phi0, 1, BITS);
        best = bnd(best, 0, Phi0);
        uint256 dUsed = Phi0 - best; // h_front
        eu = bnd(eu, 0, M.min(M.escrowAlloc(B, Phi0, dUsed), B)); // h_escrow, and B_rem + e_used = B needs e_used <= B
        uint256 bRem = B - eu; // h_cons
        le(M.ceilDiv(B * best, Phi0), bRem, 6);
    }

    // 7
    function test_T07_local_desc_ge_one(uint256 w, uint256 om, uint256 ell, uint256 lres, uint256 dp, uint256 anc) public pure {
        w = bnd(w, 0, 2 ** 40);
        om = bnd(om, 0, 2 ** 40);
        ell = bnd(ell, 1, 2 ** 40); // h_elias : ell_delta >= 1
        lres = bnd(lres, 0, 2 ** 40);
        dp = bnd(dp, 0, 2 ** 40);
        anc = bnd(anc, 0, 2 ** 40);
        ok(w + om + ell + lres + dp + anc >= 1, 7);
    }

    // 8
    function test_T08_syntactic_reduction_waterfall_valid(uint256 g, uint256 En, uint256 au, uint256 cap, uint256 dt) public pure {
        g = bnd(g, 0, 20000);
        En = bnd(En, 0, TOK);
        au = bnd(au, 0, BITS);
        cap = bnd(cap, 0, BITS);
        dt = bnd(dt, 0, BITS);
        uint256 xs = M.min(au, cap);
        uint256 xu = au - xs;
        eq(xs + xu, au, 80);
        le(M.calcRoyalty(g, En, xs, dt) + M.calcRoyalty(g, En, xu, dt), M.calcRoyalty(g, En, au, dt), 81);
    }

    // 9
    function test_T09_capStep_conserves(uint256 R, uint256 acc, uint256 p1, uint256 p2) public pure {
        R = bnd(R, 0, 2 ** 120);
        acc = bnd(acc, 0, 2 ** 120);
        (uint256 R2, uint256 a2) = M.capStep(R, acc, p1, p2);
        eq(R2 + a2, R + acc, 9);
    }

    // 10
    function test_T10_capFold_conserves(uint256 seed, uint256 R, uint256 acc) public pure {
        uint256 n = rr(seed, 0) % 17;
        R = bnd(R, 0, 2 ** 100);
        acc = bnd(acc, 0, 2 ** 100);
        (uint256 R2, uint256 a2) = M.capFold(R, acc, arr(seed, n, 2 ** 99), arr(rr(seed, 9), n, 2 ** 99));
        eq(R2 + a2, R + acc, 10);
    }

    // 11
    function test_T11_capFold_general_bound(uint256 seed, uint256 saved, uint256 s0, uint256 dAm) public pure {
        dAm = bnd(dAm, 0, BITS);
        saved = bnd(saved, 0, dAm);
        s0 = bnd(s0, 0, dAm);
        uint256 n = rr(seed, 0) % 17;
        (, uint256 acc) = M.capFold(M.monus(saved, s0), s0, arr(seed, n, BITS), arr(rr(seed, 9), n, BITS));
        le(acc, M.max(s0, saved), 110);
        le(acc, dAm, 111);
    }

    // 12
    function test_T12_sumDiv_le(uint256 seed, uint256 c) public pure {
        uint256 n = rr(seed, 0) % 17;
        uint256[] memory a = arr(seed, n, 2 ** 200);
        uint256 s;
        for (uint256 i = 0; i < n; ++i) s += M.div0(a[i], c);
        le(s, M.div0(M.sum(a), c), 12);
    }

    // 13
    function test_T13_sumRoyalty_le_total(uint256 seed, uint256 g, uint256 En, uint256 dt) public pure {
        g = bnd(g, 0, 20000);
        En = bnd(En, 0, TOK);
        dt = bnd(dt, 0, BITS);
        uint256 n = rr(seed, 0) % 17;
        uint256[] memory xs = arr(seed, n, BITS / 16);
        le(M.sumRoyalty(g, En, dt, xs), M.calcRoyalty(g, En, M.sum(xs), dt), 13);
    }

    // 14
    function test_T14_settle_general_list_conserves(uint256 seed, uint256 eT, uint256 dt, uint256 eps, uint256 g, uint256 ph) public pure {
        eT = bnd(eT, 0, TOK);
        dt = bnd(dt, 1, BITS);
        eps = bnd(eps, 0, 10000);
        g = bnd(g, 0, 10000);
        ph = bnd(ph, 0, 10000);
        M.Settle memory r = M.settleTranche(eT, dt, eps, g, ph, partition(seed, rr(seed, 0) % 17, dt));
        le(r.anc, r.net, 140);
        eq(r.burn + r.anc + r.guar + r.prop, eT, 141);
    }

    // 15
    function test_T15_slot_four_way_split_conserves(uint256 seed, uint256 rx, uint256 beta, uint256 dt, uint256 phi, uint256 sst, uint256 stot) public pure {
        rx = bnd(rx, 0, TOK);
        beta = bnd(beta, 0, 10000);
        dt = bnd(dt, 0, 2 ** 97);
        phi = bnd(phi, 0, 10000);
        stot = bnd(stot, 0, 2 ** 60);
        sst = bnd(sst, 0, stot);
        uint256 anchor = (beta * rx) / 10000;
        uint256 rnet = rx - anchor;
        uint256 rbf = bnd(rr(seed, 1), 0, M.min(rnet, dt)); // any admissible rbf_paid_sum
        uint256 rrem = rnet - rbf;
        uint256 bound = stot == 0 ? 0 : (phi * sst * rrem) / (10000 * stot);
        uint256 dict = bnd(rr(seed, 2), 0, bound); // any admissible dict_div_sum
        M.Split4 memory r = M.slotFourWaySplit(rx, beta, dt, phi, sst, stot, rbf, dict);
        eq(r.anchor + r.rbf + r.dict + r.owner, rx, 15);
        M.Split4 memory q = M.slotFourWayAuto(rx, beta, dt, phi, sst, stot); // the contract's own choice
        eq(q.anchor + q.rbf + q.dict + q.owner, rx, 150);
    }

    // 16
    function test_T16_tranche_unroll_conserves_and_bounds(uint256 seed, uint256 B, uint256 Phi) public pure {
        B = bnd(B, 0, TOK);
        Phi = bnd(Phi, 0, BITS);
        uint256 Ei = bnd(rr(seed, 1), 0, TOK / 2);
        uint256 Ea = bnd(rr(seed, 2), 0, TOK / 2);
        uint256 di = bnd(rr(seed, 3), 0, BITS / 2);
        uint256 da = bnd(rr(seed, 4), 0, BITS / 2);
        uint256 dri = bnd(rr(seed, 5), 0, di);
        uint256 dra = bnd(rr(seed, 6), 0, da);
        uint256 du = bnd(rr(seed, 7), 0, BITS);
        M.Unroll memory r = M.trancheUnroll(B, Phi, Ei, Ea, di, da, dri, dra, du);
        le(r.eRemI, M.escrowAlloc(B, Phi, dri), 160);
        le(r.eRemA, M.escrowAlloc(B, Phi, dra), 161);
        le(r.eUnroll, M.escrowAlloc(B, Phi, du), 162);
        le(r.eRemI + r.eRemA + r.eUnroll, Ei + Ea, 163);
        eq(r.eRemI + r.eRemA + r.eUnroll + r.eDust, Ei + Ea, 164);
    }

    // 17
    function test_T17_puncture_invariant_preserved(uint256 seed) public pure {
        uint256 F = bnd(rr(seed, 0), 0, BITS);
        uint256 phiL = bnd(rr(seed, 1), 0, F);
        uint256 dTot = bnd(rr(seed, 2), 0, F - phiL); // h_front_before
        uint256 dUns = bnd(rr(seed, 3), 0, dTot); // h_inv_before
        uint256 dPhi = bnd(rr(seed, 4), 0, BITS);
        uint256 dRemTot = bnd(rr(seed, 5), 0, M.monus(dTot, dPhi)); // h_rem_bound
        (uint256 dRem, uint256 dTotNew, uint256 phiNew) = M.punctureFrontier(F, phiL, dTot, dUns, dPhi, dRemTot);
        le(dRem, dTotNew, 170);
        le(dTotNew, M.monus(F, phiNew), 171);
    }

    // 18
    function test_T18_single_data_pre_embedding_unprofitable(uint256 L, uint256 C, uint256 B, uint256 Phi, uint256 lE, uint256 net) public pure {
        L = bnd(L, 0, BITS);
        C = bnd(C, 0, TOK);
        B = bnd(B, 0, TOK);
        Phi = bnd(Phi, 1, BITS); // h_Phi
        lE = bnd(lE, 0, BITS);
        net = bnd(net, 0, 10000);
        (,, uint256 dR) = M.preEmbedding(L, C, B, Phi, lE, net);
        le(dR, C, 18);
    }

    // 19
    function test_T19_rbf_lifetime_cap(uint256 paid, uint256 D, uint256 Rnet) public pure {
        paid = bnd(paid, 0, 2 ** 96);
        D = bnd(D, 0, 2 ** 97);
        Rnet = bnd(Rnet, 0, TOK);
        uint256 D0 = paid + D; // h
        uint256 rep = M.min(Rnet, D);
        eq((paid + rep) + (D - rep), D0, 19);
        le(paid + rep, D0, 190);
    }

    // 20
    function test_T20_rbf_prorata_le_list(uint256 seed, uint256 R) public pure {
        R = bnd(R, 0, TOK);
        uint256[] memory sh = M.rbfProrata(R, arr(seed, rr(seed, 0) % 17, 2 ** 93));
        le(M.sum(sh), R, 20);
    }

    // 21
    function test_T21_tEff_bounds(uint256 t, uint256 N) public pure {
        t = bnd(t, 0, 2 ** 64);
        N = bnd(N, 1, 2 ** 32);
        uint256 e = M.tEff(t, N);
        le(t + 2 * N, e, 210);
        ok(e < t + 3 * N, 211);
    }

    // 22
    function test_T22_global_supply_invariant_preserved(uint256 seed) public pure {
        A.SupplyState memory s = genSupply(seed);
        uint256 wo = bnd(rr(seed, 10), 0, s.wallets);
        uint256 lo = bnd(rr(seed, 11), 0, s.locked);
        uint256 ma = bnd(rr(seed, 12), 0, 2 ** 90);
        uint256 total = wo + lo + ma; // h_tx_eq: w_out + l_out + m_add = w_in + l_in + b_add
        uint256 wi = bnd(rr(seed, 13), 0, total);
        uint256 li = bnd(rr(seed, 14), 0, total - wi);
        uint256 ba = total - wi - li;
        ok(A.supplyInv(s), 220);
        ok(A.supplyInv(A.ledgerTx(s, wo, wi, lo, li, ba, ma)), 221);
    }

    // 23
    function test_T23_DataInv_pool_lower(uint256 seed) public pure {
        A.DataState memory s = genState(seed);
        ok(A.dataInv(s), 230);
        le(M.ceilDiv(s.B0 * s.PhiBest, s.Phi0), s.BRem, 231);
        eq(A.poolLowerBound(s) <= s.BRem ? 1 : 0, 1, 232);
    }

    // 24
    function test_T24_stepAdopt_preserves_inv(uint256 seed) public pure {
        A.DataState memory s = genState(seed);
        if (s.PhiBest < 2) return; // h_imp needs Phi_new < Phi_best with Phi_new >= 1
        uint256 pn = bnd(rr(seed, 60), 1, s.PhiBest - 1);
        uint256 bn = bnd(rr(seed, 61), 0, M.escrowAlloc(s.B0, s.Phi0, s.PhiBest - pn));
        ok(A.dataInv(A.adopt(s, pn, bn)), 240);
    }

    // 25
    function test_T25_stepPuncture_concrete_preserves_inv(uint256 seed) public pure {
        A.DataState memory s = genState(seed);
        uint256 du = bnd(rr(seed, 62), 0, s.dInit + s.dAbs);
        ok(A.dataInv(A.puncture(s, du)), 250);
    }

    // 26
    function test_T26_stepHoldExpire_concrete_preserves_inv(uint256 seed) public pure {
        A.DataState memory s = genState(seed);
        uint256 da = bnd(rr(seed, 63), 0, s.dHold);
        ok(A.dataInv(A.holdExpire(s, da)), 260);
    }

    // 27
    function test_T27_stepSettleInit_preserves_inv(uint256 seed) public pure {
        ok(A.dataInv(A.settleInit(genState(seed))), 270);
    }

    // 28
    function test_T28_stepSettleAbs_preserves_inv(uint256 seed) public pure {
        ok(A.dataInv(A.settleAbs(genState(seed))), 280);
    }

    // 29
    function test_T29_stage1_single_bounds(uint256 saved, uint256 s0, uint256 sig, uint256 dt, uint256 dAm) public pure {
        dAm = bnd(dAm, 0, BITS);
        saved = bnd(saved, 0, dAm);
        s0 = bnd(s0, 0, dAm);
        sig = bnd(sig, 0, BITS);
        dt = bnd(dt, 0, BITS);
        uint256 sm = M.monus(saved, s0);
        uint256 au = M.stage1Alloc(sm, sig, dt);
        le(au, sm, 290);
        le(s0 + au, M.max(s0, saved), 291);
        le(s0 + au, dAm, 292);
    }

    // 30
    function test_T30_stage1_list_sum_le_delta(uint256 seed, uint256 dt) public pure {
        dt = bnd(dt, 0, BITS);
        uint256[] memory sh = M.stage1List(arr(seed, rr(seed, 0) % 17, BITS / 32), dt);
        le(M.sum(sh), dt, 30);
    }

    // 31
    function test_T31_puncture_slot_scale_valid(uint256 seed, uint256 dt, uint256 drem, uint256 sPaid, uint256 x) public pure {
        dt = bnd(dt, 1, BITS); // h_d_pos
        drem = bnd(drem, 0, dt); // h_rem
        sPaid = bnd(sPaid, 0, 2 ** 60);
        x = bnd(x, 0, BITS);
        uint256[] memory xs = partition(seed, rr(seed, 0) % 17, dt); // h_sum
        uint256 s;
        for (uint256 i = 0; i < xs.length; ++i) s += M.div0(xs[i] * drem, dt);
        le(s, drem, 310);
        uint256 xNew = M.slotScale(x, drem, dt);
        le(xNew, x, 311);
        le(M.sAfter(sPaid, x, xNew), sPaid, 312);
    }

    // 32
    function test_T32_allTranches_sum_bounded(uint256 seed) public pure {
        A.ListDataState memory s = genList(seed);
        ok(A.allTranchesBounded(s.B0, s.Phi0, s.tranches), 320);
        le(A.sumTrancheE(s.tranches), M.escrowAlloc(s.B0, s.Phi0, A.sumTrancheD(s.tranches)), 321);
    }

    // 33
    function test_T33_stepAdoptList_preserves_inv(uint256 seed) public pure {
        A.ListDataState memory s = genList(seed);
        ok(A.listDataInv(s), 330);
        if (s.PhiBest < 2) return;
        uint256 pn = bnd(rr(seed, 70), 1, s.PhiBest - 1);
        uint256 bn = bnd(rr(seed, 71), 0, M.escrowAlloc(s.B0, s.Phi0, s.PhiBest - pn));
        A.ListDataState memory r = A.stepAdoptList(s, pn, bn);
        ok(A.listDataInv(r), 331);
        eq(r.tranches.length, s.tranches.length + 1, 332);
        eq(r.tranches[r.tranches.length - 1].e, bn, 333); // new tranche is the head
    }

    // 34
    function test_T34_stepSettleHead_preserves_inv(uint256 seed) public pure {
        A.ListDataState memory s = genList(seed);
        A.ListDataState memory r = A.stepSettleHead(s);
        ok(A.listDataInv(r), 340);
        eq(r.tranches.length, s.tranches.length == 0 ? 0 : s.tranches.length - 1, 341);
    }

    // 35 - 46: the twelve ledger-branch theorems
    function test_T35_branch01_T0(uint256 seed) public pure {
        A.SupplyState memory s = genSupply(seed);
        uint256 q = s.wallets / 4;
        ok(A.supplyInv(A.branch01T0(s, bnd(rr(seed, 1), 0, q), bnd(rr(seed, 2), 0, q), bnd(rr(seed, 3), 0, q), bnd(rr(seed, 4), 0, q))), 35);
    }

    function test_T36_branch02_commit(uint256 seed) public pure {
        A.SupplyState memory s = genSupply(seed);
        ok(A.supplyInv(A.branch02Commit(s, bnd(rr(seed, 1), 0, s.wallets / 2), bnd(rr(seed, 2), 0, s.wallets / 2))), 36);
    }

    function test_T37_branch03_adopt(uint256 seed) public pure {
        A.SupplyState memory s = genSupply(seed);
        uint256 q = s.wallets / 4;
        ok(A.supplyInv(A.branch03Adopt(s, bnd(rr(seed, 1), 0, q), bnd(rr(seed, 2), 0, q), bnd(rr(seed, 3), 0, q), bnd(rr(seed, 4), 0, q))), 37);
    }

    function test_T38_branch04_reject(uint256 seed) public pure {
        A.SupplyState memory s = genSupply(seed);
        uint256 q = s.wallets / 3;
        ok(A.supplyInv(A.branch04Reject(s, bnd(rr(seed, 1), 0, s.locked), bnd(rr(seed, 2), 0, q), bnd(rr(seed, 3), 0, q), bnd(rr(seed, 4), 0, q))), 38);
    }

    function test_T39_branch05_unrevealed(uint256 seed) public pure {
        A.SupplyState memory s = genSupply(seed);
        ok(A.supplyInv(A.branch05Unrevealed(s, bnd(rr(seed, 1), 0, s.locked))), 39);
    }

    function test_T40_branch06_07_puncture(uint256 seed) public pure {
        A.SupplyState memory s = genSupply(seed);
        uint256 cut = bnd(rr(seed, 1), 0, s.locked);
        uint256 pay = bnd(rr(seed, 2), 0, cut);
        ok(A.supplyInv(A.branch0607Puncture(s, cut, pay, cut - pay, bnd(rr(seed, 3), 0, s.wallets))), 40);
    }

    function test_T41_branch08a_uw_topup(uint256 seed) public pure {
        A.SupplyState memory s = genSupply(seed);
        ok(A.supplyInv(A.branch08aUwTopup(s, bnd(rr(seed, 1), 0, s.wallets / 2), bnd(rr(seed, 2), 0, s.wallets / 2))), 41);
    }

    function test_T42_branch08b_hold_expire(uint256 seed) public pure {
        A.SupplyState memory s = genSupply(seed);
        ok(A.supplyInv(A.branch08bHoldExpire(s, bnd(rr(seed, 1), 0, s.locked))), 42);
    }

    function test_T43_branch09_settle(uint256 seed) public pure {
        A.SupplyState memory s = genSupply(seed);
        uint256 eTr = bnd(rr(seed, 1), 0, s.locked / 2);
        uint256 unl = bnd(rr(seed, 2), 0, s.locked / 2);
        uint256 eb = bnd(rr(seed, 3), 0, eTr);
        ok(A.supplyInv(A.branch09Settle(s, eTr, unl, eb, eTr - eb)), 43);
    }

    function test_T44_branch10_close_ok(uint256 seed) public pure {
        A.SupplyState memory s = genSupply(seed);
        ok(A.supplyInv(A.branch10CloseOk(s, bnd(rr(seed, 1), 0, s.locked / 2), bnd(rr(seed, 2), 0, s.locked / 2))), 44);
    }

    function test_T45_branch11_close_pen(uint256 seed) public pure {
        A.SupplyState memory s = genSupply(seed);
        ok(A.supplyInv(A.branch11ClosePen(s, bnd(rr(seed, 1), 0, s.locked / 2), bnd(rr(seed, 2), 0, s.locked / 2))), 45);
    }

    function test_T46_branch12_to_15(uint256 seed) public pure {
        A.SupplyState memory s = genSupply(seed);
        uint256 q = s.wallets / 3;
        A.SupplyState memory r = A.branch12to15(s, bnd(rr(seed, 1), 0, q), bnd(rr(seed, 2), 0, s.locked), bnd(rr(seed, 3), 0, q), bnd(rr(seed, 4), 0, 2 ** 90), bnd(rr(seed, 5), 0, q));
        ok(A.supplyInv(r), 46);
    }

    // 47
    function test_T47_release_symmetric(uint256 base, uint256 xs, uint256 xu, uint256 r, uint256 d) public pure {
        base = bnd(base, 0, 2 ** 90);
        xs = bnd(xs, 0, 2 ** 60);
        xu = bnd(xu, 0, 2 ** 60);
        d = bnd(d, 1, BITS); // hd
        r = bnd(r, 0, d); // hr
        eq(M.symmetricRelease(base, xs, xu, r, d), base + (xs * r) / d + (xu * r) / d, 47);
    }

    // 48
    function test_T48_old_rule_leaks(uint256 base, uint256 xs, uint256 xu, uint256 r, uint256 d) public pure {
        // the mechanized counterexample (decide): base = 0, xs = xu = 10, r = 1, d = 2
        ok(M.oldRuleRelease(0, 10, 10, 1, 2) != 0 + (10 * 1) / 2 + (10 * 1) / 2, 480);
        eq(M.oldRuleRelease(0, 10, 10, 1, 2), 15, 481);
        // in general the old rule leaves exactly delta_xs = xs - floor(xs r / d) of phantom reservation
        base = bnd(base, 0, 2 ** 90);
        xs = bnd(xs, 0, 2 ** 60);
        xu = bnd(xu, 0, 2 ** 60);
        d = bnd(d, 1, BITS);
        r = bnd(r, 0, d);
        eq(M.oldRuleRelease(base, xs, xu, r, d), M.symmetricRelease(base, xs, xu, r, d) + (xs - (xs * r) / d), 482);
    }

    // 49
    function test_T49_m1_redirect_rbf_priority_conserves(uint256 seed, uint256 rx, uint256 beta, uint256 du, uint256 ds) public pure {
        rx = bnd(rx, 0, TOK);
        beta = bnd(beta, 0, 10000);
        du = bnd(du, 0, 2 ** 97);
        ds = bnd(ds, 0, 2 ** 97);
        uint256 rem = M.m1RedirectRbfPriority(rx, beta, du, ds, 0).owner; // with div_s = 0 the owner gets the whole remainder
        uint256 dv = bnd(rr(seed, 1), 0, rem); // h_div
        M.M1 memory r = M.m1RedirectRbfPriority(rx, beta, du, ds, dv);
        eq(r.paidU, M.min(rx - r.anchor, du), 490);
        eq(r.anchor + r.paidU + r.paidS + r.divS + r.owner, rx, 491);
    }

    // 50
    function test_T50_game_pre_embedding_strictly_dominated(uint256 L, uint256 C, uint256 B, uint256 Phi, uint256 lE, uint256 net, uint256 burnDa, uint256 g) public pure {
        L = bnd(L, 0, BITS);
        C = bnd(C, 0, TOK / 2);
        B = bnd(B, 0, TOK);
        Phi = bnd(Phi, 1, BITS);
        lE = bnd(lE, 0, BITS);
        net = bnd(net, 0, 10000);
        burnDa = bnd(burnDa, 0, 2 ** 90);
        g = bnd(g, 0, 2 ** 90);
        if (burnDa + g == 0) g = 1; // h_cost
        (,, uint256 dR) = M.preEmbedding(L, C, B, Phi, lE, net);
        ok(dR < C + burnDa + g, 50);
    }

    // 51
    function test_T51_game_griefing_strictly_dominated(uint256 kappa, uint256 sigma, uint256 lambda, uint256 gamma, uint256 eps, uint256 eTr) public pure {
        kappa = bnd(kappa, 1, 10000);
        sigma = bnd(sigma, 1, 10000);
        lambda = bnd(lambda, 0, 20000);
        eps = bnd(eps, 0, 9999);
        uint256 gmax = M.gammaMax(kappa, sigma, lambda, eps);
        gamma = bnd(gamma, 0, gmax); // h_param holds for every gamma <= gamma_max
        eTr = bnd(eTr, 1, 2 ** 90); // h_E_pos
        ok(kappa * sigma * 10000 > (10000 + lambda) * (gamma * (10000 - eps)), 510);
        (uint256 loss, uint256 evade) = M.griefingScaled(kappa, sigma, lambda, gamma, eps, eTr);
        ok(evade < loss, 511);
        // and gamma_max is tight: gamma_max + 1 violates h_param
        ok(!(kappa * sigma * 10000 > (10000 + lambda) * ((gmax + 1) * (10000 - eps))), 512);
    }

    // 52
    function test_T52_game_watchtower_deterrence_equilibrium(uint256 q, uint256 net, uint256 lam, uint256 sc, uint256 rg, uint256 kslack) public pure {
        q = bnd(q, 1, 10000);
        net = bnd(net, 0, 10000);
        lam = bnd(lam, 0, 10);
        sc = bnd(sc, 0, 2 ** 40);
        rg = bnd(rg, 0, (1 + lam) * sc); // h_col
        uint256 kappa = M.ceilDiv((10000 - q) * net * (1 + lam), q) + bnd(kslack, 0, 3); // smallest kappa meeting h_cond, plus slack
        ok((10000 - q) * net * (1 + lam) <= q * kappa, 520); // h_cond
        ok(((10000 - q) * net) * rg <= (q * kappa) * sc, 521);
    }

    // 53
    function test_T53_game_honest_citation_dominates(uint256 eBase, uint256 dE, uint256 gamma) public pure {
        eBase = bnd(eBase, 0, 2 ** 100);
        dE = bnd(dE, 1, TOK); // h_gain
        gamma = bnd(gamma, 0, 9999); // h_gamma
        (uint256 roy, uint256 prop) = M.honestCitation(gamma, dE);
        ok(roy < dE, 530);
        ok(eBase < eBase + prop, 531);
    }

    // 54
    function test_T54_shannon_len_ceilDiv_iff(uint256 k, uint256 w, uint256 T) public pure {
        k = bnd(k, 0, 100);
        w = bnd(w, 1, 2 ** 120); // hw : 0 < w
        T = bnd(T, 0, 2 ** 128);
        eq((T <= (uint256(1) << k) * w) ? 1 : 0, (M.ceilDiv(T, w) <= (uint256(1) << k)) ? 1 : 0, 54);
        // and shannonLen is the least k >= 1 with 2^k * w >= T
        uint256 l = M.shannonLen(T, w);
        ok(l >= 1 && (uint256(1) << l) * w >= T && (l == 1 || (uint256(1) << (l - 1)) * w < T), 541);
    }
}
