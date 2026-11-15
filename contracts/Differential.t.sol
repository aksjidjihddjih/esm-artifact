// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {Base} from "./Base.sol";
import {ESMMath as M} from "../src/ESMMath.sol";
import {ESMAccounting as A} from "../src/ESMAccounting.sol";

/// @notice Differential tests: every row is (inputs | expected outputs).
///  ORACLE LEAN  : produced by `lean --run` on ESM_verified.lean (`#eval` of the Lean definitions themselves)
///  ORACLE PYTHON: independent big-integer implementation written from the theorem statements / paper equations
contract Differential is Base {
    // ---------------------------------------------------------------- ORACLE LEAN (35,000 rows)
    function test_lean_escrowAlloc() public view {
        uint256[] memory w = load("ESC");
        for (uint256 i = 0; i < w.length; i += 4) eq(M.escrowAlloc(w[i], w[i + 1], w[i + 2]), w[i + 3], i);
    }

    function test_lean_ceilDiv() public view {
        uint256[] memory w = load("CEIL");
        for (uint256 i = 0; i < w.length; i += 3) eq(M.ceilDiv(w[i], w[i + 1]), w[i + 2], i);
    }

    function test_lean_calcRoyalty() public view {
        uint256[] memory w = load("ROY");
        for (uint256 i = 0; i < w.length; i += 5) eq(M.calcRoyalty(w[i], w[i + 1], w[i + 2], w[i + 3]), w[i + 4], i);
    }

    function test_lean_safeRemEscrow() public view {
        uint256[] memory w = load("SAFEREM");
        for (uint256 i = 0; i < w.length; i += 6) eq(M.safeRemEscrow(w[i], w[i + 1], w[i + 2], w[i + 3], w[i + 4]), w[i + 5], i);
    }

    function test_lean_calcAmortGen() public view {
        uint256[] memory w = load("AMORT");
        for (uint256 i = 0; i < w.length; i += 6) eq(M.deltaAmort(w[i], w[i + 1], w[i + 2], w[i + 3], w[i + 4]), w[i + 5], i);
    }

    function test_lean_calcNetRewardGen() public view {
        uint256[] memory w = load("NETRWD");
        for (uint256 i = 0; i < w.length; i += 5) eq(M.netReward(w[i], w[i + 1], w[i + 2], w[i + 3]), w[i + 4], i);
    }

    function test_lean_calcTEff() public view {
        uint256[] memory w = load("TEFF");
        for (uint256 i = 0; i < w.length; i += 3) eq(M.tEff(w[i], w[i + 1]), w[i + 2], i);
    }

    function test_lean_allocStage1Single() public view {
        uint256[] memory w = load("STAGE1");
        for (uint256 i = 0; i < w.length; i += 4) eq(M.stage1Alloc(w[i], w[i + 1], w[i + 2]), w[i + 3], i);
    }

    function test_lean_applyLedgerTx() public view {
        uint256[] memory w = load("SUPPLY");
        for (uint256 i = 0; i < w.length; i += 14) {
            A.SupplyState memory s = A.SupplyState(w[i], w[i + 1], w[i + 2], w[i + 3]);
            A.SupplyState memory r = A.applyLedgerTx(s, w[i + 4], w[i + 5], w[i + 6], w[i + 7], w[i + 8], w[i + 9]);
            ok(r.wallets == w[i + 10] && r.locked == w[i + 11] && r.burned == w[i + 12] && r.minted == w[i + 13], i);
        }
    }

    function test_lean_stepAdopt() public view {
        uint256[] memory w = load("ADOPT");
        for (uint256 i = 0; i < w.length; i += 26) ok(sameState(A.stepAdopt(st(w, i), w[i + 12], w[i + 13]), st(w, i + 14)), i);
    }

    function test_lean_stepPunctureConcrete() public view {
        uint256[] memory w = load("PUNC");
        for (uint256 i = 0; i < w.length; i += 25) ok(sameState(A.stepPunctureConcrete(st(w, i), w[i + 12]), st(w, i + 13)), i);
    }

    function test_lean_stepHoldExpire() public view {
        uint256[] memory w = load("HOLD");
        for (uint256 i = 0; i < w.length; i += 25) ok(sameState(A.stepHoldExpire(st(w, i), w[i + 12]), st(w, i + 13)), i);
    }

    function test_lean_stepSettleInit_and_Abs() public view {
        uint256[] memory a = load("SINIT");
        for (uint256 i = 0; i < a.length; i += 24) ok(sameState(A.stepSettleInit(st(a, i)), st(a, i + 12)), i);
        uint256[] memory b = load("SABS");
        for (uint256 i = 0; i < b.length; i += 24) ok(sameState(A.stepSettleAbs(st(b, i)), st(b, i + 12)), i);
    }

    // ---------------------------------------------------------------- ORACLE PYTHON
    function test_py_shannonLen_and_clog2() public view {
        uint256[] memory w = load("SHAN");
        for (uint256 i = 0; i < w.length; i += 3) eq(M.shannonLen(w[i], w[i + 1]), w[i + 2], i);
        uint256[] memory c = load("CLOG");
        for (uint256 i = 0; i < c.length; i += 2) eq(M.clog2(c[i]), c[i + 1], i);
    }

    function test_py_stage2Redirect() public view {
        uint256[] memory w = load("ST2");
        for (uint256 i = 0; i < w.length; i += 6) {
            (uint256 a, uint256 b, uint256 c) = M.stage2Redirect(w[i], w[i + 1], w[i + 2]);
            ok(a == w[i + 3] && b == w[i + 4] && c == w[i + 5], i);
        }
    }

    function test_py_settleTranche() public view {
        uint256[] memory w = load("SETTLE");
        uint256 i;
        while (i < w.length) {
            uint256 n = w[i + 5];
            uint256[] memory xs = new uint256[](n);
            for (uint256 k = 0; k < n; ++k) xs[k] = w[i + 6 + k];
            M.Settle memory r = M.settleTranche(w[i], w[i + 1], w[i + 2], w[i + 3], w[i + 4], xs);
            uint256 o = i + 6 + n;
            ok(r.burn == w[o] && r.net == w[o + 1] && r.anc == w[o + 2] && r.rem == w[o + 3] && r.guar == w[o + 4] && r.prop == w[o + 5], i);
            i = o + 6;
        }
    }

    function test_py_slotFourWay_and_m1() public view {
        uint256[] memory w = load("SLOT4");
        for (uint256 i = 0; i < w.length; i += 10) {
            M.Split4 memory r = M.slotFourWayAuto(w[i], w[i + 1], w[i + 2], w[i + 3], w[i + 4], w[i + 5]);
            ok(r.anchor == w[i + 6] && r.rbf == w[i + 7] && r.dict == w[i + 8] && r.owner == w[i + 9], i);
        }
        uint256[] memory m = load("M1");
        for (uint256 i = 0; i < m.length; i += 10) {
            M.M1 memory r = M.m1RedirectRbfPriority(m[i], m[i + 1], m[i + 2], m[i + 3], m[i + 4]);
            ok(r.anchor == m[i + 5] && r.paidU == m[i + 6] && r.paidS == m[i + 7] && r.divS == m[i + 8] && r.owner == m[i + 9], i);
        }
    }

    function test_py_trancheUnroll() public view {
        uint256[] memory w = load("UNROLL");
        for (uint256 i = 0; i < w.length; i += 13) {
            M.Unroll memory r = M.trancheUnroll(w[i], w[i + 1], w[i + 2], w[i + 3], w[i + 4], w[i + 5], w[i + 6], w[i + 7], w[i + 8]);
            ok(r.eRemI == w[i + 9] && r.eRemA == w[i + 10] && r.eUnroll == w[i + 11] && r.eDust == w[i + 12], i);
        }
    }

    function test_py_symmetricRelease() public view {
        uint256[] memory w = load("SYMREL");
        for (uint256 i = 0; i < w.length; i += 7) {
            eq(M.symmetricRelease(w[i], w[i + 1], w[i + 2], w[i + 3], w[i + 4]), w[i + 5], i);
            eq(M.oldRuleRelease(w[i], w[i + 1], w[i + 2], w[i + 3], w[i + 4]), w[i + 6], i);
        }
    }

    function test_py_slashSplit_refund() public view {
        uint256[] memory w = load("SLASH");
        for (uint256 i = 0; i < w.length; i += 6) {
            M.Slash memory r = M.slashSplit(w[i], w[i + 1], w[i + 2]);
            ok(r.slash == w[i + 3] && r.hunter == w[i + 4] && r.burn == w[i + 5], i);
        }
        uint256[] memory f = load("REFUND");
        for (uint256 i = 0; i < f.length; i += 2) eq(M.refund30(f[i]), f[i + 1], i);
    }

    function test_py_gammaMax_kappaMin() public view {
        uint256[] memory g = load("GMAX");
        for (uint256 i = 0; i < g.length; i += 5) eq(M.gammaMax(g[i], g[i + 1], g[i + 2], g[i + 3]), g[i + 4], i);
        uint256[] memory k = load("KMIN");
        for (uint256 i = 0; i < k.length; i += 5) eq(M.kappaMin(k[i], k[i + 1], k[i + 2], k[i + 3]), k[i + 4], i);
    }

    function test_py_fGrind_qDetect() public view {
        uint256[] memory f = load("FGR");
        uint256 worst;
        for (uint256 i = 0; i < f.length; i += 4) {
            uint256 got = M.fGrindPpb(f[i], f[i + 1], f[i + 2]);
            uint256 d = got > f[i + 3] ? got - f[i + 3] : f[i + 3] - got;
            if (d > worst) worst = d;
        }
        le(worst, 2, 1); // 1e18 fixed point vs 90-digit Decimal: at most 2 parts per billion
        uint256[] memory q = load("QDET");
        for (uint256 i = 0; i < q.length; i += 3) eq(M.qDetectPpm(q[i], q[i + 1]), q[i + 2], i);
    }
}
