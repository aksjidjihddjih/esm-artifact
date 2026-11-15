// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {ESMMath as M} from "../src/ESMMath.sol";
import {ESMAccounting as A} from "../src/ESMAccounting.sol";

interface Vm {
    function readFileBinary(string calldata path) external view returns (bytes memory);
}

/// @dev forge-std-free helpers: bounded fuzz inputs, valid-state generators, vector loading
abstract contract Base {
    Vm internal constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));
    uint256 internal constant TOK = (uint256(1) << 96) - 1;
    uint256 internal constant BITS = uint256(1) << 40;

    error NotEqual(uint256 got, uint256 want, uint256 where_);
    error NotLe(uint256 a, uint256 b, uint256 where_);
    error Failed(uint256 where_);

    function load(string memory tag) internal view returns (uint256[] memory) {
        return abi.decode(vm.readFileBinary(string.concat("vectors/", tag, ".bin")), (uint256[]));
    }

    function bnd(uint256 x, uint256 lo, uint256 hi) internal pure returns (uint256) {
        if (hi < lo) revert Failed(9999);
        unchecked {
            uint256 span = hi - lo + 1;
            if (span == 0) return x;
            return lo + (x % span);
        }
    }

    function rr(uint256 seed, uint256 i) internal pure returns (uint256) {
        return uint256(keccak256(abi.encode(seed, i)));
    }

    function eq(uint256 got, uint256 want, uint256 w) internal pure {
        if (got != want) revert NotEqual(got, want, w);
    }

    function le(uint256 a, uint256 b, uint256 w) internal pure {
        if (a > b) revert NotLe(a, b, w);
    }

    function ok(bool c, uint256 w) internal pure {
        if (!c) revert Failed(w);
    }

    /// @dev `n` values, each <= mx
    function arr(uint256 seed, uint256 n, uint256 mx) internal pure returns (uint256[] memory a) {
        a = new uint256[](n);
        for (uint256 i = 0; i < n; ++i) a[i] = bnd(rr(seed, 100 + i), 0, mx);
    }

    /// @dev `n` values with sum <= total (random partition, sometimes saturated)
    function partition(uint256 seed, uint256 n, uint256 total) internal pure returns (uint256[] memory a) {
        a = new uint256[](n);
        uint256 rest = total;
        for (uint256 i = 0; i < n; ++i) {
            uint256 m = rr(seed, 200 + i) % 5;
            uint256 v = m == 0 ? 0 : (m == 1 ? rest : bnd(rr(seed, 300 + i), 0, rest));
            a[i] = v;
            rest -= v;
        }
    }

    // ---------------------------------------------------------------- valid states (satisfying DataInv / SupplyInv)
    function pickE(uint256 seed, uint256 i, uint256 B0, uint256 Phi0, uint256 d) internal pure returns (uint256) {
        uint256 esc = M.escrowAlloc(B0, Phi0, d);
        uint256 m = rr(seed, 400 + i) % 4;
        return m == 0 ? 0 : (m == 1 ? esc : bnd(rr(seed, 500 + i), 0, esc));
    }

    function genState(uint256 seed) internal pure returns (A.DataState memory s) {
        uint256 mode = rr(seed, 0) % 8;
        s.B0 = mode == 0 ? 0 : bnd(rr(seed, 1), 0, mode == 1 ? 1000 : (uint256(1) << 90));
        s.Phi0 = bnd(rr(seed, 2), 1, mode == 2 ? 5 : (uint256(1) << 38));
        s.PhiBest = bnd(rr(seed, 3), 1, s.Phi0);
        uint256 rest = s.Phi0 - s.PhiBest;
        uint256[] memory p = partition(seed, 4, rest);
        uint256 rot = rr(seed, 7) % 4;
        uint256[4] memory d;
        for (uint256 i = 0; i < 4; ++i) d[(i + rot) % 4] = p[i];
        d[3] += rest - (d[0] + d[1] + d[2] + d[3]); // any remainder goes to settled
        s.dInit = d[0];
        s.dAbs = d[1];
        s.dHold = d[2];
        s.dSettled = d[3];
        s.eInit = pickE(seed, 0, s.B0, s.Phi0, s.dInit);
        s.eAbs = pickE(seed, 1, s.B0, s.Phi0, s.dAbs);
        s.eHold = pickE(seed, 2, s.B0, s.Phi0, s.dHold);
        s.eSettled = pickE(seed, 3, s.B0, s.Phi0, s.dSettled);
        s.BRem = s.B0 - (s.eInit + s.eAbs + s.eHold + s.eSettled); // never underflows: superadditivity + EscrowAlloc(B0, Phi0, Phi0 - 1) <= B0
    }

    function genList(uint256 seed) internal pure returns (A.ListDataState memory s) {
        uint256 mode = rr(seed, 0) % 8;
        s.B0 = mode == 0 ? 0 : bnd(rr(seed, 1), 0, uint256(1) << 90);
        s.Phi0 = bnd(rr(seed, 2), 1, uint256(1) << 38);
        s.PhiBest = bnd(rr(seed, 3), 1, s.Phi0);
        uint256 n = rr(seed, 4) % 9;
        uint256[] memory p = partition(seed, n + 2, s.Phi0 - s.PhiBest);
        s.tranches = new A.Tranche[](n);
        uint256 used;
        for (uint256 i = 0; i < n; ++i) {
            s.tranches[i].d = p[i];
            s.tranches[i].e = pickE(seed, 10 + i, s.B0, s.Phi0, p[i]);
            used += p[i];
        }
        s.dHold = p[n];
        s.dSettled = p[n + 1] + (s.Phi0 - s.PhiBest - used - p[n] - p[n + 1]);
        s.eHold = pickE(seed, 50, s.B0, s.Phi0, s.dHold);
        s.eSettled = pickE(seed, 51, s.B0, s.Phi0, s.dSettled);
        s.BRem = s.B0 - (s.eHold + s.eSettled + A.sumTrancheE(s.tranches));
    }

    function genSupply(uint256 seed) internal pure returns (A.SupplyState memory s) {
        uint256 mx = uint256(1) << 92;
        s.wallets = bnd(rr(seed, 0), 0, rr(seed, 3) % 4 == 0 ? 3 : mx);
        s.locked = bnd(rr(seed, 1), 0, rr(seed, 4) % 4 == 0 ? 3 : mx);
        s.burned = bnd(rr(seed, 2), 0, mx);
        s.minted = s.wallets + s.locked + s.burned;
    }

    // ---------------------------------------------------------------- vector rows
    function st(uint256[] memory w, uint256 o) internal pure returns (A.DataState memory s) {
        s.B0 = w[o];
        s.Phi0 = w[o + 1];
        s.PhiBest = w[o + 2];
        s.dInit = w[o + 3];
        s.dAbs = w[o + 4];
        s.dHold = w[o + 5];
        s.dSettled = w[o + 6];
        s.eInit = w[o + 7];
        s.eAbs = w[o + 8];
        s.eHold = w[o + 9];
        s.eSettled = w[o + 10];
        s.BRem = w[o + 11];
    }

    function sameState(A.DataState memory a, A.DataState memory b) internal pure returns (bool) {
        return a.B0 == b.B0 && a.Phi0 == b.Phi0 && a.PhiBest == b.PhiBest && a.dInit == b.dInit && a.dAbs == b.dAbs
            && a.dHold == b.dHold && a.dSettled == b.dSettled && a.eInit == b.eInit && a.eAbs == b.eAbs
            && a.eHold == b.eHold && a.eSettled == b.eSettled && a.BRem == b.BRem;
    }
}
