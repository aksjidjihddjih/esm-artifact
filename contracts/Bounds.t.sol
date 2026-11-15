// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {Base} from "./Base.sol";
import {ESMMath as M} from "../src/ESMMath.sol";
import {ESMAccounting as A} from "../src/ESMAccounting.sol";

contract Harness {
    function escrow(uint256 B, uint256 Phi, uint256 d) external pure returns (uint256) { return M.escrowAlloc(B, Phi, d); }
    function roy(uint256 g, uint256 e, uint256 x, uint256 d) external pure returns (uint256) { return M.calcRoyalty(g, e, x, d); }
    function amort(uint256 L, uint256 C, uint256 B, uint256 P, uint256 n) external pure returns (uint256) { return M.deltaAmort(L, C, B, P, n); }
    function tEff(uint256 t, uint256 n) external pure returns (uint256) { return M.tEff(t, n); }
    function sym(uint256 a, uint256 b, uint256 c, uint256 r, uint256 d) external pure returns (uint256) { return M.symmetricRelease(a, b, c, r, d); }
    function settle(uint256 e, uint256 d, uint256 x1, uint256 x2) external pure returns (uint256) {
        uint256[] memory xs = new uint256[](2);
        xs[0] = x1;
        xs[1] = x2;
        return M.settleTranche(e, d, 500, 2000, 1000, xs).prop;
    }
    function list(uint256 n) external pure returns (uint256) { return M.sum(new uint256[](n)); }
    function four(uint256 rx, uint256 rbf) external pure returns (uint256) { return M.slotFourWaySplit(rx, 1000, 5, 10000, 0, 0, rbf, 0).owner; }
    function m1(uint256 dv) external pure returns (uint256) { return M.m1RedirectRbfPriority(1000, 1000, 5, 5, dv).owner; }
    function adopt(uint256 pn, uint256 bn) external pure returns (uint256) {
        A.DataState memory s = A.DataState(10000, 16384, 1000, 1, 2, 3, 4, 5, 6, 7, 8, 9);
        return A.adopt(s, pn, bn).PhiBest;
    }
    function ledger(uint256 wo, uint256 lo, uint256 wi) external pure returns (uint256) {
        return A.ledgerTx(A.SupplyState(100, 50, 10, 160), wo, wi, lo, 0, 0, 0).wallets;
    }
    function mint(uint256 m) external pure returns (uint256) {
        return A.applyLedgerTx(A.SupplyState(0, 0, 0, 0), 0, 0, 0, 0, 0, m).minted;
    }
}

/// @notice frozen-range checks (fail closed), hypothesis checks, worst-case products (zero overflow)
contract Bounds is Base {
    Harness internal h = new Harness();

    function _sel(bytes memory e) internal pure returns (bytes4 s) {
        if (e.length >= 4) assembly { s := mload(add(e, 32)) }
    }

    function test_ranges_revert_with_the_right_error() public {
        try h.escrow(TOK + 1, 1, 1) returns (uint256) { revert Failed(1); } catch (bytes memory e) { eq(uint32(_sel(e)), uint32(M.TokenRange.selector), 1); }
        try h.escrow(1, BITS + 1, 1) returns (uint256) { revert Failed(2); } catch (bytes memory e) { eq(uint32(_sel(e)), uint32(M.BitsRange.selector), 2); }
        try h.escrow(1, 1, BITS + 1) returns (uint256) { revert Failed(3); } catch (bytes memory e) { eq(uint32(_sel(e)), uint32(M.BitsRange.selector), 3); }
        try h.roy(20001, 1, 1, 1) returns (uint256) { revert Failed(4); } catch (bytes memory e) { eq(uint32(_sel(e)), uint32(M.BpsRange.selector), 4); }
        try h.list(17) returns (uint256) { revert Failed(5); } catch (bytes memory e) { eq(uint32(_sel(e)), uint32(M.ListTooLong.selector), 5); }
        try h.tEff(1, 0) returns (uint256) { revert Failed(6); } catch (bytes memory e) { eq(uint32(_sel(e)), uint32(M.Precondition.selector), 6); }
        try h.mint(TOK + 1) returns (uint256) { revert Failed(7); } catch (bytes memory e) { eq(uint32(_sel(e)), uint32(M.TokenRange.selector), 7); }
        // the frozen caps themselves are accepted
        eq(h.escrow(TOK, BITS, BITS), TOK, 8);
        eq(h.mint(TOK), TOK, 9);
    }

    function _code(bytes memory e) internal pure returns (uint256 c) {
        require(_sel(e) == M.Precondition.selector, "not a Precondition error");
        assembly { c := mload(add(e, 36)) }
    }

    function test_theorem_hypotheses_are_enforced_fail_closed() public {
        try h.sym(0, 1, 1, 3, 2) returns (uint256) { revert Failed(10); } catch (bytes memory e) { eq(_code(e), 15, 10); } // r > d
        try h.sym(0, 1, 1, 0, 0) returns (uint256) { revert Failed(11); } catch (bytes memory e) { eq(_code(e), 14, 11); } // d = 0
        try h.settle(1000, 0, 0, 0) returns (uint256) { revert Failed(12); } catch (bytes memory e) { eq(_code(e), 3, 12); } // d_tr = 0
        try h.settle(1000, 10, 6, 5) returns (uint256) { revert Failed(13); } catch (bytes memory e) { eq(_code(e), 4, 13); } // sum xs > d_tr
        try h.four(1000, 1000) returns (uint256) { revert Failed(14); } catch (bytes memory e) { eq(_code(e), 6, 14); } // rbf > min(R_net, D_tot)
        try h.m1(10_000) returns (uint256) { revert Failed(15); } catch (bytes memory e) { eq(_code(e), 8, 15); } // div_s > remainder
        try h.adopt(0, 0) returns (uint256) { revert Failed(16); } catch (bytes memory e) { eq(_code(e), 21, 16); } // Phi_new >= 1
        try h.adopt(1000, 0) returns (uint256) { revert Failed(17); } catch (bytes memory e) { eq(_code(e), 22, 17); } // Phi_new < Phi_best
        try h.adopt(10, 10_000) returns (uint256) { revert Failed(18); } catch (bytes memory e) { eq(_code(e), 23, 18); } // b_new <= EscrowAlloc
        try h.ledger(101, 0, 101) returns (uint256) { revert Failed(19); } catch (bytes memory e) { eq(_code(e), 31, 19); } // w_out <= wallets
        try h.ledger(0, 51, 51) returns (uint256) { revert Failed(20); } catch (bytes memory e) { eq(_code(e), 32, 20); } // l_out <= locked
        try h.ledger(10, 0, 9) returns (uint256) { revert Failed(21); } catch (bytes memory e) { eq(_code(e), 33, 21); } // value conservation
    }

    /// worst-case intermediate products at the frozen maxima: documented bit lengths (params.toml [overflow_bits]) and < 2^256
    function test_worst_case_products_zero_overflow() public pure {
        uint256 bits_ = BITS;
        uint256 e1 = TOK * bits_;
        ok(M.log2(e1) + 1 == 136 && 136 == 96 + 40, 1); // B * d
        ok(M.log2(10000 * TOK * bits_) + 1 <= 150, 2); // 10000 * C * Phi
        ok(M.log2(bits_ * bits_) + 1 <= 81, 3); // Saved * min(Sigma, d)
        ok(M.log2(10000 * TOK * bits_) + 1 <= 150, 4); // gamma * E_net * x  (gamma <= 10000)
        ok(M.log2(20000 * TOK * bits_) + 1 <= 151, 5); // ... with the generic guard gamma <= 20000
        ok(M.log2(TOK * (uint256(1) << 97)) + 1 <= 193, 6); // R_repay * D
        ok(M.log2(10000 * TOK * TOK) + 1 <= 206, 7); // phi * S * R_rem
        // every public entry evaluated at the maxima without reverting
        eq(M.escrowAlloc(TOK, 1, BITS), TOK * BITS, 8);
        eq(M.calcRoyalty(10000, TOK, BITS, BITS), (10000 * TOK) / 10000, 9);
        eq(M.deltaAmort(BITS, TOK, 1, BITS, 10000), BITS, 10);
        eq(M.netReward(TOK, 1, BITS, 10000), (10000 * M.escrowAlloc(TOK, 1, BITS)) / 10000, 11);
        eq(M.tEff(2 ** 64, 2 ** 32) % (2 ** 32), 0, 12);
        uint256[] memory ds = new uint256[](16);
        for (uint256 i = 0; i < 16; ++i) ds[i] = 2 ** 97;
        eq(M.rbfProrata(TOK, ds)[0], (TOK * 2 ** 97) / (16 * 2 ** 97), 13);
        uint256[] memory xs = new uint256[](16);
        for (uint256 i = 0; i < 16; ++i) xs[i] = BITS / 16;
        M.Settle memory r = M.settleTranche(TOK, BITS, 10000, 10000, 10000, xs);
        eq(r.burn + r.anc + r.guar + r.prop, TOK, 14);
    }

    /// the contract-level frozen caps agree with the Rust crate / params.toml
    function test_frozen_constants() public pure {
        eq(M.MAX_TOKEN, 79228162514264337593543950335, 1);
        eq(M.MAX_BITS, 1099511627776, 2);
        eq(M.MAX_LIST, 16, 3);
        eq(M.MAX_BPS, 20000, 4);
        eq(M.MAX_DEBT, 2 * (M.MAX_TOKEN + 1), 5);
    }
}
