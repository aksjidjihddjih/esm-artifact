// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

/// @title ESMMath
/// @notice One-to-one port of the arithmetic of `ESM_verified.lean` (54 theorems, `Nat`) to `uint256`.
/// @dev Rules that make the port exact:
///  * every Lean `a - b` on `Nat` is `monus` (saturating); there is no checked subtraction on a path where
///    Lean uses truncating subtraction, and where a Lean hypothesis guarantees `b <= a` the port `revert`s if that
///    hypothesis does not hold (fail closed) instead of silently saturating;
///  * every Lean `a / 0` (= 0) is `div0`; Solidity's division by zero panic can never be reached;
///  * each `floor(x*y/z)` is ONE division, evaluated in the same order as in the Lean text;
///  * ranges frozen in `spec/params.toml`: token amounts <= 2^96-1, bit quantities <= 2^40, rates <= 20000 bps,
///    lists <= 16 entries. Every public entry point checks its inputs, so every intermediate product stays below
///    2^256 (worst cases are tabulated in `overflow_bits`: 136, 150, 150, 193, 206 bits).
library ESMMath {
    // ------------------------------------------------------------------ frozen bounds
    uint256 internal constant MAX_TOKEN = (uint256(1) << 96) - 1; // MINT_CAP
    uint256 internal constant MAX_BITS = uint256(1) << 40; // Phi0 <= n_k * b_k <= 2^30 * 2^10
    uint256 internal constant MAX_DEBT = uint256(1) << 97; // M_cap_bps (2.0x) * MAX_TOKEN
    uint256 internal constant BPS = 10_000;
    uint256 internal constant MAX_BPS = 20_000; // M_cap_bps is the largest rate-like constant
    uint256 internal constant MAX_LIST = 16; // MAX_CITED_AXIOMS (also K_rbf^max = 10 sponsors)
    uint256 internal constant MAX_BLOCK = uint256(1) << 64;
    uint256 internal constant MAX_EPOCH = uint256(1) << 32;

    error TokenRange(uint256 v);
    error BitsRange(uint256 v);
    error DebtRange(uint256 v);
    error BpsRange(uint256 v);
    error ListTooLong(uint256 n);
    /// @dev a Lean theorem hypothesis does not hold; `code` identifies which one (see each function)
    error Precondition(uint8 code);

    // ------------------------------------------------------------------ range guards
    function tok(uint256 x) internal pure returns (uint256) {
        if (x > MAX_TOKEN) revert TokenRange(x);
        return x;
    }

    function bt(uint256 x) internal pure returns (uint256) {
        if (x > MAX_BITS) revert BitsRange(x);
        return x;
    }

    function debt(uint256 x) internal pure returns (uint256) {
        if (x > MAX_DEBT) revert DebtRange(x);
        return x;
    }

    function bpsOk(uint256 x) internal pure returns (uint256) {
        if (x > MAX_BPS) revert BpsRange(x);
        return x;
    }

    function rate(uint256 x) internal pure returns (uint256) {
        // hypothesis `rate_bps <= 10000`
        if (x > BPS) revert Precondition(1);
        return x;
    }

    function lst(uint256 n) internal pure returns (uint256) {
        if (n > MAX_LIST) revert ListTooLong(n);
        return n;
    }

    // ------------------------------------------------------------------ Nat primitives
    function monus(uint256 a, uint256 b) internal pure returns (uint256) {
        unchecked {
            return a > b ? a - b : 0;
        }
    }

    function div0(uint256 a, uint256 b) internal pure returns (uint256) {
        return b == 0 ? 0 : a / b;
    }

    function min(uint256 a, uint256 b) internal pure returns (uint256) {
        return a < b ? a : b;
    }

    function max(uint256 a, uint256 b) internal pure returns (uint256) {
        return a > b ? a : b;
    }

    /// @dev Lean `ceilDiv a b = (a + b - 1) / b`; equals `a / b + [a % b != 0]` for b >= 1 and 0 for b = 0.
    function ceilDiv(uint256 a, uint256 b) internal pure returns (uint256) {
        if (b == 0) return 0;
        return a / b + (a % b == 0 ? 0 : 1);
    }

    /// @dev min { k : 2^k >= max(x, 1) }
    function clog2(uint256 x) internal pure returns (uint256 k) {
        if (x <= 1) return 0;
        x -= 1;
        while (x > 0) {
            k++;
            x >>= 1;
        }
    }

    /// @dev Shannon dictionary length l_E = min { k >= 1 : 2^k * w >= T } computed WITHOUT `2^k * w`
    ///      (Lean: `shannon_len_ceilDiv_iff`, w > 0). T = sum_m (W_E(m) + eps0) + eps0, w = W_E(u) + eps0.
    function shannonLen(uint256 t, uint256 w) internal pure returns (uint256) {
        uint256 k = clog2(ceilDiv(t, w));
        return k < 1 ? 1 : k;
    }

    /// @dev floor(log2 x), x >= 1 (0 for x = 0)
    function log2(uint256 x) internal pure returns (uint256 r) {
        while (x > 1) {
            r++;
            x >>= 1;
        }
    }

    /// @dev Elias-omega length: l(1) = 1, l(n) = 1 + floor(log2 n) + l(floor(log2 n)); 0 outside the domain (n = 0)
    function eliasOmegaLen(uint256 n) internal pure returns (uint256 total) {
        if (n == 0) return 0;
        while (n > 1) {
            uint256 k = log2(n);
            total += 1 + k;
            n = k;
        }
        return total + 1;
    }

    function sum(uint256[] memory xs) internal pure returns (uint256 s) {
        lst(xs.length);
        for (uint256 i = 0; i < xs.length; ++i) {
            s += xs[i];
        }
    }

    // ------------------------------------------------------------------ escrow / royalty / amortization
    /// @dev EscrowAlloc(B, Phi, d) = floor(B * d / Phi)
    function escrowAlloc(uint256 B, uint256 Phi, uint256 d) internal pure returns (uint256) {
        return div0(tok(B) * bt(d), bt(Phi));
    }

    /// @dev calcRoyalty gamma E_net x d_tr = floor(gamma * E_net * x / (10000 * d_tr))
    function calcRoyalty(uint256 gammaBps, uint256 eNet, uint256 x, uint256 dTr) internal pure returns (uint256) {
        return div0(bpsOk(gammaBps) * tok(eNet) * bt(x), BPS * bt(dTr));
    }

    /// @dev slot royalty R(x) (paper Eq. slot_royalty) = calcRoyalty
    function slotRoyalty(uint256 gammaBps, uint256 eNet, uint256 x, uint256 dTr) internal pure returns (uint256) {
        return calcRoyalty(gammaBps, eNet, x, dTr);
    }

    /// @dev calcAmortGen L C B Phi net = min L (10000 * C * Phi / (net * B))   (Delta_amort, Eq. delta_amort)
    function deltaAmort(uint256 L, uint256 C, uint256 B, uint256 Phi, uint256 netBps) internal pure returns (uint256) {
        return min(bt(L), div0(BPS * tok(C) * bt(Phi), bpsOk(netBps) * tok(B)));
    }

    /// @dev Delta_saved = Delta_amort (-) l_E
    function savedNet(uint256 dAmort, uint256 lE) internal pure returns (uint256) {
        return monus(bt(dAmort), bt(lE));
    }

    /// @dev calcNetRewardGen B Phi d_saved net = floor(net * EscrowAlloc(B, Phi, d_saved) / 10000)
    function netReward(uint256 B, uint256 Phi, uint256 dSaved, uint256 netBps) internal pure returns (uint256) {
        return (bpsOk(netBps) * escrowAlloc(B, Phi, dSaved)) / BPS;
    }

    // ------------------------------------------------------------------ Stage 1 / Stage 2 / cap fold
    /// @dev allocStage1Single saved_marg sigma_marg d_tr
    function stage1Alloc(uint256 savedMarg, uint256 sigmaMarg, uint256 dTr) internal pure returns (uint256) {
        if (sigmaMarg == 0) return 0;
        return (bt(savedMarg) * min(bt(sigmaMarg), bt(dTr))) / sigmaMarg;
    }

    /// @dev Stage 1 over a list of marginal budgets: share_i = floor(m_i * min(sigma, d_tr) / sigma), sigma = sum m
    function stage1List(uint256[] memory margs, uint256 dTr) internal pure returns (uint256[] memory shares) {
        uint256 sig = sum(margs);
        bt(sig);
        uint256 c = min(sig, bt(dTr));
        shares = new uint256[](margs.length);
        for (uint256 i = 0; i < margs.length; ++i) {
            shares[i] = div0(margs[i] * c, sig);
        }
    }

    /// @dev Stage 2 redirect (paper Eq. stage2_redirect; esm-core `stage2_redirect`):
    ///      x_{i->s} = min(a, L_red, R_cap), x_{i->i} = a - x_{i->s}, R_cap' = R_cap - x_{i->s}
    function stage2Redirect(uint256 a, uint256 lRed, uint256 rCap)
        internal
        pure
        returns (uint256 xIS, uint256 xII, uint256 capLeft)
    {
        xIS = min(bt(a), min(bt(lRed), bt(rCap)));
        xII = a - xIS;
        capLeft = rCap - xIS;
    }

    /// @dev capStep (R, acc) (p1, p2): x = min p1 (min p2 R); (R - x, acc + x)
    function capStep(uint256 R, uint256 acc, uint256 p1, uint256 p2) internal pure returns (uint256, uint256) {
        uint256 x = min(p1, min(p2, R));
        return (R - x, acc + x);
    }

    function capFold(uint256 R, uint256 acc, uint256[] memory p1, uint256[] memory p2)
        internal
        pure
        returns (uint256, uint256)
    {
        lst(p1.length);
        if (p1.length != p2.length) revert Precondition(2);
        for (uint256 i = 0; i < p1.length; ++i) {
            (R, acc) = capStep(R, acc, p1[i], p2[i]);
        }
        return (R, acc);
    }

    // ------------------------------------------------------------------ settlement
    struct Settle {
        uint256 burn;
        uint256 net;
        uint256 anc;
        uint256 rem;
        uint256 guar;
        uint256 prop;
    }

    /// @dev sumRoyalty gamma E_net d_tr xs
    function sumRoyalty(uint256 gammaBps, uint256 eNet, uint256 dTr, uint256[] memory xs) internal pure returns (uint256 s) {
        lst(xs.length);
        for (uint256 i = 0; i < xs.length; ++i) {
            s += calcRoyalty(gammaBps, eNet, xs[i], dTr);
        }
    }

    /// @dev settle_general_list_conserves. Preconditions: d_tr > 0 (code 3), sum xs <= d_tr (4), all rates <= 10000.
    function settleTranche(uint256 eTr, uint256 dTr, uint256 epsBps, uint256 gammaBps, uint256 phiGuarBps, uint256[] memory xs)
        internal
        pure
        returns (Settle memory r)
    {
        if (bt(dTr) == 0) revert Precondition(3);
        if (sum(xs) > dTr) revert Precondition(4);
        rate(epsBps);
        rate(gammaBps);
        rate(phiGuarBps);
        r.burn = (epsBps * tok(eTr)) / BPS;
        r.net = eTr - r.burn;
        r.anc = sumRoyalty(gammaBps, r.net, dTr, xs);
        r.rem = monus(r.net, r.anc);
        r.guar = (phiGuarBps * r.rem) / BPS;
        r.prop = r.rem - r.guar;
    }

    struct Split4 {
        uint256 anchor;
        uint256 rbf;
        uint256 dict;
        uint256 owner;
    }

    /// @dev slot_four_way_split_conserves with caller-supplied sums.
    ///      Preconditions: beta, phi <= 10000 (1); S_st <= S_tot (5); rbf <= min(R_net, D_tot) (6); dict <= bound (7).
    function slotFourWaySplit(
        uint256 rX,
        uint256 betaDBps,
        uint256 dTot,
        uint256 phiDictBps,
        uint256 sStBar,
        uint256 sTotBar,
        uint256 rbfPaidSum,
        uint256 dictDivSum
    ) internal pure returns (Split4 memory r) {
        rate(betaDBps);
        rate(phiDictBps);
        if (sStBar > sTotBar) revert Precondition(5);
        tok(rX);
        debt(dTot);
        r.anchor = (betaDBps * rX) / BPS;
        uint256 rNet = rX - r.anchor;
        if (rbfPaidSum > min(rNet, dTot)) revert Precondition(6);
        uint256 rRem = rNet - rbfPaidSum;
        uint256 bound = sTotBar == 0 ? 0 : (phiDictBps * sStBar * rRem) / (BPS * sTotBar);
        if (dictDivSum > bound) revert Precondition(7);
        r.rbf = rbfPaidSum;
        r.dict = dictDivSum;
        r.owner = rRem - dictDivSum;
    }

    /// @dev the waterfall as the contract runs it: RBF repayment at its maximum min(R_net, D_tot), dictionary dividend at its bound
    function slotFourWayAuto(uint256 rX, uint256 betaDBps, uint256 dTot, uint256 phiDictBps, uint256 sStBar, uint256 sTotBar)
        internal
        pure
        returns (Split4 memory r)
    {
        rate(betaDBps);
        rate(phiDictBps);
        uint256 anchor = (betaDBps * tok(rX)) / BPS;
        uint256 rNet = rX - anchor;
        uint256 rbf = min(rNet, debt(dTot));
        uint256 rRem = rNet - rbf;
        uint256 dict = sTotBar == 0 ? 0 : (phiDictBps * sStBar * rRem) / (BPS * sTotBar);
        return slotFourWaySplit(rX, betaDBps, dTot, phiDictBps, sStBar, sTotBar, rbf, dict);
    }

    struct M1 {
        uint256 anchor;
        uint256 paidU;
        uint256 paidS;
        uint256 divS;
        uint256 owner;
    }

    /// @dev m1_redirect_rbf_priority_conserves (Theorem 49): derivative debt D_u is repaid first, then root debt D_s.
    ///      Precondition: beta <= 10000 (1); div_s <= R_net - paid_u - paid_s (8).
    function m1RedirectRbfPriority(uint256 rX, uint256 betaDBps, uint256 dU, uint256 dS, uint256 divS)
        internal
        pure
        returns (M1 memory r)
    {
        rate(betaDBps);
        tok(rX);
        debt(dU);
        debt(dS);
        r.anchor = (betaDBps * rX) / BPS;
        uint256 rNet = rX - r.anchor;
        r.paidU = min(rNet, dU);
        uint256 rAfterU = rNet - r.paidU;
        r.paidS = min(rAfterU, dS);
        uint256 rRem = rAfterU - r.paidS;
        if (divS > rRem) revert Precondition(8);
        r.divS = divS;
        r.owner = rRem - divS;
    }

    /// @dev rbf_prorata_le_list: share_i = floor(R_repay * d_i / sum d); sum of shares <= R_repay
    function rbfProrata(uint256 rRepay, uint256[] memory ds) internal pure returns (uint256[] memory shares) {
        uint256 total = sum(ds);
        shares = new uint256[](ds.length);
        for (uint256 i = 0; i < ds.length; ++i) {
            shares[i] = div0(tok(rRepay) * debt(ds[i]), total);
        }
    }

    // ------------------------------------------------------------------ tranche / puncture
    /// @dev safeRemEscrow B Phi E_tr d_tr d_rem
    function safeRemEscrow(uint256 B, uint256 Phi, uint256 eTr, uint256 dTr, uint256 dRemTr) internal pure returns (uint256) {
        if (bt(dTr) == 0) return 0;
        return min((tok(eTr) * bt(dRemTr)) / dTr, escrowAlloc(B, Phi, dRemTr));
    }

    struct Unroll {
        uint256 eRemI;
        uint256 eRemA;
        uint256 eUnroll;
        uint256 eDust;
    }

    /// @dev tranche_unroll_conserves_and_bounds. Preconditions: d_rem_init <= d_init (9), d_rem_abs <= d_abs (10).
    function trancheUnroll(
        uint256 B,
        uint256 Phi,
        uint256 eInit,
        uint256 eAbs,
        uint256 dInit,
        uint256 dAbs,
        uint256 dRemInit,
        uint256 dRemAbs,
        uint256 dUnroll
    ) internal pure returns (Unroll memory r) {
        if (dRemInit > dInit) revert Precondition(9);
        if (dRemAbs > dAbs) revert Precondition(10);
        r.eRemI = safeRemEscrow(B, Phi, eInit, dInit, dRemInit);
        r.eRemA = safeRemEscrow(B, Phi, eAbs, dAbs, dRemAbs);
        uint256 eTotal = eInit + eAbs;
        uint256 eRem = r.eRemI + r.eRemA;
        r.eUnroll = min(monus(eTotal, eRem), escrowAlloc(B, Phi, dUnroll));
        r.eDust = monus(monus(eTotal, eRem), r.eUnroll);
    }

    /// @dev puncture_invariant_preserved: returns (d_rem, d_tot_new, Phi_new).
    ///      Preconditions: d_unsettled <= d_tot (11), d_tot <= F - Phi_local (12), d_rem_tot <= d_tot - delta_Phi (13).
    function punctureFrontier(uint256 F, uint256 phiLocal, uint256 dTot, uint256 dUnsettled, uint256 deltaPhi, uint256 dRemTot)
        internal
        pure
        returns (uint256 dRem, uint256 dTotNew, uint256 phiNew)
    {
        if (dUnsettled > dTot) revert Precondition(11);
        if (dTot > monus(F, phiLocal)) revert Precondition(12);
        if (dRemTot > monus(dTot, deltaPhi)) revert Precondition(13);
        uint256 dReq = dTot - dRemTot;
        uint256 dUnroll = min(dUnsettled, dReq);
        dRem = dUnsettled - dUnroll;
        dTotNew = dRemTot;
        phiNew = phiLocal + deltaPhi;
    }

    /// @dev puncture slot scale (Eq. puncture_slot_scale): x_new = floor(x * d_rem / d_tr)
    function slotScale(uint256 x, uint256 dRem, uint256 dTr) internal pure returns (uint256) {
        return div0(bt(x) * bt(dRem), bt(dTr));
    }

    /// @dev S_after = S_paid (-) (x - x_new)
    function sAfter(uint256 sPaid, uint256 x, uint256 xNew) internal pure returns (uint256) {
        return monus(sPaid, monus(x, xNew));
    }

    /// @dev symmetric release (release_symmetric, d > 0 (14), r <= d (15)):
    ///      (base + xs + xu) - ((xs - xs*r/d) + (xu - xu*r/d))  ==  base + xs*r/d + xu*r/d
    function symmetricRelease(uint256 base, uint256 xs, uint256 xu, uint256 r, uint256 d) internal pure returns (uint256) {
        if (bt(d) == 0) revert Precondition(14);
        if (bt(r) > d) revert Precondition(15);
        return monus(base + xs + xu, (xs - (xs * r) / d) + (xu - (xu * r) / d));
    }

    /// @dev the v15 rule that leaks (old_rule_leaks): only delta_xu is released from the derivative
    function oldRuleRelease(uint256 base, uint256 xs, uint256 xu, uint256 r, uint256 d) internal pure returns (uint256) {
        return monus(base + xs + xu, xu - (xu * r) / d);
    }

    // ------------------------------------------------------------------ slashing / refunds / epochs
    struct Slash {
        uint256 slash;
        uint256 hunter;
        uint256 burn;
    }

    /// @dev Eq. slash_split: S_slash = ceil(r * S / 10000), S_hunter = floor((10000 - kappa) * S_slash / 10000), S_burn = S_slash - S_hunter
    function slashSplit(uint256 rBps, uint256 sCreator, uint256 kappaBps) internal pure returns (Slash memory r) {
        rate(rBps);
        rate(kappaBps);
        r.slash = ceilDiv(rBps * tok(sCreator), BPS);
        r.hunter = ((BPS - kappaBps) * r.slash) / BPS;
        r.burn = r.slash - r.hunter;
    }

    /// @dev unrevealed commit / penalized close: ref = floor(3000 * S / 10000) is refunded, S - ref burned (branches 05, 11)
    function refund30(uint256 s) internal pure returns (uint256) {
        return (3000 * tok(s)) / BPS;
    }

    /// @dev calcTEff t_req N_ep = N_ep * floor((t_req + 3 N_ep - 1) / N_ep); N_ep > 0 (16)
    function tEff(uint256 tReq, uint256 nEp) internal pure returns (uint256) {
        if (nEp == 0 || nEp > MAX_EPOCH) revert Precondition(16);
        if (tReq > MAX_BLOCK) revert BitsRange(tReq);
        return nEp * ((tReq + 3 * nEp - 1) / nEp);
    }

    // ------------------------------------------------------------------ game-theoretic quantities (Theorems 49-53)
    /// @dev (d_amort, d_saved, dR_net) of a single-dataset pre-embedding strategy (single_data_pre_embedding_unprofitable)
    function preEmbedding(uint256 L, uint256 C, uint256 B, uint256 Phi, uint256 lE, uint256 netBps)
        internal
        pure
        returns (uint256 dAmort, uint256 dSaved, uint256 dRNet)
    {
        dAmort = deltaAmort(L, C, B, Phi, netBps);
        dSaved = savedNet(dAmort, lE);
        dRNet = netReward(B, Phi, dSaved, netBps);
    }

    /// @dev scaled loss / evade numerators of game_griefing_strictly_dominated
    function griefingScaled(uint256 kappa, uint256 sigma, uint256 lambda, uint256 gamma, uint256 eps, uint256 eTr)
        internal
        pure
        returns (uint256 loss, uint256 evade)
    {
        loss = (kappa * sigma * BPS) * tok(eTr);
        evade = ((BPS + lambda) * (gamma * monus(BPS, eps))) * eTr;
    }

    /// @dev honest citation: (royalty_inc, proposer_inc)
    function honestCitation(uint256 gammaBps, uint256 dENet) internal pure returns (uint256 royaltyInc, uint256 proposerInc) {
        royaltyInc = (bpsOk(gammaBps) * tok(dENet)) / BPS;
        proposerInc = dENet - royaltyInc;
    }

    // ------------------------------------------------------------------ closed forms used by the paper's sensitivity tables
    /// @dev largest gamma_bps with kappa*sigma*10000 > (10000 + Lambda) * gamma * (10000 - eps)   (Eq. griefing_constraint)
    function gammaMax(uint256 kappa, uint256 sigma, uint256 lambda, uint256 eps) internal pure returns (uint256) {
        uint256 num = kappa * sigma * BPS;
        uint256 den = (BPS + lambda) * monus(BPS, eps);
        if (num == 0 || den == 0) return 0;
        return (num - 1) / den;
    }

    /// @dev smallest kappa_bps satisfying the same constraint
    function kappaMin(uint256 gamma, uint256 sigma, uint256 lambda, uint256 eps) internal pure returns (uint256) {
        return ((BPS + lambda) * gamma * monus(BPS, eps)) / (sigma * BPS) + 1;
    }

    /// @dev R_net per dataset: R = floor(gamma * E_net / 10000), minus the beta_D anchor rebate
    function netRoyaltyPerDataset(uint256 gammaBps, uint256 eNet, uint256 betaDBps) internal pure returns (uint256) {
        uint256 r = (gammaBps * eNet) / BPS;
        return r - (betaDBps * r) / BPS;
    }

    /// @dev fixed point (1e18) x^k by repeated squaring
    function powFixed(uint256 x, uint256 k) internal pure returns (uint256 r) {
        r = 1e18;
        while (k > 0) {
            if (k & 1 == 1) r = (r * x) / 1e18;
            x = (x * x) / 1e18;
            k >>= 1;
        }
    }

    /// @dev grinding threshold f_grind in parts per billion: smallest f with (1-f)^K <= kappa' / (kappa' + 0.95 (1 + Lambda)),
    ///      kappa' = kappa_bps / 10000.  Binary search on a 1e18 fixed-point power.
    function fGrindPpb(uint256 K, uint256 kappaBps, uint256 lambdaBps) internal pure returns (uint256) {
        uint256 ratio = (kappaBps * 1e18) / (kappaBps + (9500 * (BPS + lambdaBps)) / BPS);
        uint256 lo = 0;
        uint256 hi = 1e9;
        while (lo < hi) {
            uint256 mid = (lo + hi) / 2;
            if (powFixed(1e18 - mid * 1e9, K) <= ratio) hi = mid;
            else lo = mid + 1;
        }
        return lo;
    }

    /// @dev q_detect* in parts per million: 0.95 (1 + Lambda) / (slash' + 0.95 (1 + Lambda)), rounded to nearest
    function qDetectPpm(uint256 slashBps, uint256 lambdaBps) internal pure returns (uint256) {
        uint256 num = 9500 * (BPS + lambdaBps);
        uint256 den = slashBps * BPS + num;
        return (num * 1_000_000 + den / 2) / den;
    }
}
