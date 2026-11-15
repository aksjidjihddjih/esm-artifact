// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {ESMMath as M} from "./ESMMath.sol";
import {ESMAccounting as A} from "./ESMAccounting.sol";
import {IERC20, IVerifierRegistry, ISeedBeacon, IArchiveRegistry, IBatchRoot} from "./Interfaces.sol";

/// @title ESMStorage - constants, state and shared helpers of ESM (core) and ESMOps (module reached by delegatecall: identical layout)
/// @notice Wraps the pure, Lean-checked functions of ESMMath / ESMAccounting. Every state change goes through them, so
///         SupplyInv (wallets + locked + burned + redeemed = minted, backed 1:1 by the token balance) and DataInv hold after every call.
///         The 18 ledger schemas are the functions tagged `[B1] .. [B15]` below (`branchHits` counts executions).
/// @dev    Time is `_now()` (default `block.number`); on Arbitrum override it with the L1 block number (params.toml [time]).
///         Proofs are verified through the VerifierRegistry (zkVM guest = esm-core). Known simplifications are listed in step4_report.md.
abstract contract ESMStorage is IBatchRoot {
    // ------------------------------------------------------------------ frozen parameters (spec/params.toml)
    uint256 internal constant N_COM = 100;
    uint256 internal constant N_DELAY = 20;
    uint256 internal constant N_BATCH = 300;
    uint256 internal constant N_EPOCH = 49_800;
    uint256 internal constant N_LOCK = 50_000;
    uint256 internal constant N_REV_T6 = 180;
    uint256 internal constant N_HOLD = 300;
    uint256 internal constant BPS = 10_000;
    uint256 internal constant EPS_BPS = 500;
    uint256 internal constant GAMMA_BPS = 2000;
    uint256 internal constant BETA_D_BPS = 1000;
    uint256 internal constant KAPPA_BPS = 7000;
    uint256 internal constant SIGMA_COL_BPS = 10_000;
    uint256 internal constant SIGMA_DICT_BPS = 10_000;
    uint256 internal constant M_CAP_BPS = 20_000;
    uint256 internal constant DELTA_CAP_V1 = 65_536;
    uint256 internal constant MAX_CITED = 16;
    uint256 internal constant MAX_RBF = 10;
    uint256 internal constant MAX_CAND = 8;
    uint256 internal constant MAX_COMMITS = 64;
    uint256 internal constant MAX_UNSETTLED = 8;
    address internal constant DEAD = 0x000000000000000000000000000000000000dEaD;

    // ledger schema ids (branchHits index)
    uint8 internal constant B1 = 1; // T0 register dataset
    uint8 internal constant B2 = 2; // T1 phase 1 blind commit
    uint8 internal constant B3 = 3; // T1 phase 2 adopt
    uint8 internal constant B4 = 4; // T1 phase 2 reject (valid non-winner)
    uint8 internal constant B5 = 5; // T1 unrevealed forfeit
    uint8 internal constant B6 = 6; // T2 mode II-A full slash
    uint8 internal constant B7 = 7; // T2 mode III partial puncture
    uint8 internal constant B8A = 8; // T3 absorb top-up
    uint8 internal constant B8B = 9; // T3 hold expiry
    uint8 internal constant B9 = 10; // T4 settle
    uint8 internal constant B10 = 11; // T4 normal close
    uint8 internal constant B11 = 12; // T4 penalized close
    uint8 internal constant B12A = 13; // RBF sponsorship burn
    uint8 internal constant B12B = 14; // dictionary stake lock
    uint8 internal constant B12C = 15; // dictionary stake unlock
    uint8 internal constant B13 = 16; // T5 epoch update
    uint8 internal constant B14 = 17; // T6 syntactic reduction
    uint8 internal constant B15 = 18; // vault deposit / withdraw

    struct Params {
        uint256 daFeePerBit; // wei burned per published bit (eps_DA)
        uint256 sAudit; // syntactic-audit deposit S_audit
        uint256 commitCollateralBps; // MINIMUM (spam-prevention) creator collateral as a share of B_k^(0); the proposer may lock any larger S_c
        uint256 phiGuarBps; // guarantor share of the settlement remainder
        uint256 eps0; // Shannon dictionary smoothing weight
        uint256 lambdaBps; // underwriter leverage Lambda in bps: 0 (Lambda = 0) or 10_000 (Lambda = 1)
    }

    // ------------------------------------------------------------------ errors / events
    error Reentrancy();
    error Insufficient(address who, uint256 have, uint256 need);
    error TransferFailed();
    error BalanceDiff();
    error BadDataset();
    error BadKind();
    error WrongPhase();
    error Duplicate();
    error TooMany();
    error BadReveal();
    error BadProof();
    error NotOwner();
    error BadAxiom();
    error Rejected(uint8 code);
    error InvariantBroken(uint8 code);
    error BadParams();

    event Branch(uint8 indexed id, uint32 indexed ref, address indexed who, uint256 amount);
    event Committed(bytes32 indexed hash, address indexed who, uint8 kind, uint32 ref);

    // ------------------------------------------------------------------ immutables / storage
    IERC20 public immutable asset;
    IVerifierRegistry public immutable verifiers;
    ISeedBeacon public immutable beacon;
    IArchiveRegistry public immutable archive;
    uint256 public immutable genesis;
    Params public params;

    A.SupplyState public supply;
    uint256 public redeemed;
    uint256 public flushedBurn;
    uint256 public userWallets;
    uint256 public poolsTotal;
    mapping(address => uint256) public wallet;
    mapping(uint8 => uint256) public branchHits;
    uint256 private _guard = 1;

    struct Dataset {
        address owner;
        uint8 status; // 0 none, 1 open, 2 closed
        bool penalized;
        uint256 sk;
        uint64 holdStart;
        uint64 absAt;
        address absClaimant;
        uint256 absSuw;
        A.DataState d;
        uint32[] unsettled;
    }

    struct HoldClaim {
        address who;
        uint256 dAbs;
        uint256 dSuw;
    }

    struct Axiom {
        address proposer;
        address underwriter; // receives R_guar and the S_uw refund (defaults to the proposer)
        uint32 dataset;
        uint64 adoptedAt;
        uint64 seq;
        uint32 origin;
        bool active;
        bool settled;
        bytes32 programHash;
        uint256 progBits;
        uint256 phiLocal;
        uint256 lAxiom;
        uint256 dNew0;
        uint256 dNew;
        uint256 bNew;
        uint256 sc0;
        uint256 sc;
        uint256 suw;
        uint256 saudit;
        uint256 amortBurn;
        uint256 savedBits;
        uint256 lE0;
        uint256 lRed;
        uint256 rootCapLeft;
        uint256 sPaid; // Stage-1 reservation counter of THIS axiom as a cited derivative/root: sum of the live slots x charged against its own cap
        uint32[] citeIds;
        uint256[] citeBits;
        uint256[] citeXis;
        uint32[] citeRoot;
    }

    struct Commit {
        address who;
        uint8 kind;
        uint32 ref;
        uint32 batch;
        uint64 blk;
        bool revealed;
        bool settled;
        uint256 sc;
    }

    struct Cand {
        address who;
        address uw; // underwriter that co-stakes S_uw (== who when none was named)
        bytes32 hash;
        bytes32 programHash;
        uint256 progBits;
        uint256 phiLocal;
        uint256 lAxiom;
        uint256 cAmort;
        uint256 lock;
        uint256 suw;
        uint256 sc;
        uint256 phiBestAtReveal;
        uint32[] citeIds;
        uint256[] citeBits;
    }

    struct Sponsor {
        address who;
        uint256 debt;
    }

    struct Weight {
        uint128 cur;
        uint128 prev;
        uint64 curEpoch;
    }

    struct PhiDict {
        uint16 active;
        uint16 pending;
        uint64 pendingEpoch;
    }

    struct UserStake {
        uint256 amount;
        uint256 rewardDebt;
        uint256 reqAmount;
        uint256 reqEpoch;
    }

    mapping(address => mapping(address => bool)) public uwConsent; // underwriter => proposer => consent to co-stake

    uint32 public datasetCount;
    uint32 public axiomCount;
    mapping(uint32 => Dataset) internal ds;
    mapping(uint32 => HoldClaim) public claims;
    mapping(uint32 => Axiom) internal ax;
    mapping(bytes32 => Commit) public commits;
    mapping(uint256 => bytes32) public override batchRoot;
    mapping(uint32 => mapping(uint32 => uint256)) internal commitCount;
    mapping(uint32 => mapping(uint32 => Cand[])) internal cands;
    mapping(uint32 => mapping(uint32 => bool)) public finalized;
    mapping(uint32 => Sponsor[]) internal sponsors;
    mapping(uint32 => uint256) public debtOf;
    mapping(uint32 => uint256) public stakeTotal;
    mapping(uint32 => uint256) public accPerStake; // 1e27 scaled
    mapping(uint32 => mapping(address => UserStake)) public userStake;
    mapping(uint32 => Weight) internal wt;
    mapping(uint32 => PhiDict) internal phiDict;
    uint256 public epoch;
    uint256 public totalWeight;
    uint256 public snapTotal;

    constructor(IERC20 asset_, IVerifierRegistry v_, ISeedBeacon b_, IArchiveRegistry a_, uint256 genesis_, Params memory p_) {
        if (p_.lambdaBps != 0 && p_.lambdaBps != BPS) revert BadParams();
        asset = asset_;
        verifiers = v_;
        beacon = b_;
        archive = a_;
        params = p_;
        genesis = genesis_;
    }

    modifier nonReentrant() {
        if (_guard != 1) revert Reentrancy();
        _guard = 2;
        _;
        _guard = 1;
    }

    function _now() internal view virtual returns (uint256) {
        return block.number;
    }

    // ================================================================== internal accounting helpers
    function _credit(address a, uint256 x) internal {
        wallet[a] += x;
        userWallets += x;
    }

    function _debit(address a, uint256 x) internal {
        uint256 h = wallet[a];
        if (h < x) revert Insufficient(a, h, x);
        wallet[a] = h - x;
        userWallets -= x;
    }

    function _hit(uint8 id, uint32 ref, address who, uint256 amt) internal {
        branchHits[id]++;
        emit Branch(id, ref, who, amt);
    }

    /// @dev defence in depth: the proven functions already preserve it, this makes a violation impossible to persist
    function _chk() internal view {
        A.SupplyState memory s = supply;
        if (s.wallets + s.locked + s.burned + redeemed != s.minted || userWallets + poolsTotal != s.wallets) revert InvariantBroken(1);
    }

    // ---- shared pure helpers / views
    function btarget(uint32 aid) public view returns (uint256) {
        Axiom storage a = ax[aid];
        A.DataState storage d = ds[a.dataset].d;
        uint256 full = M.ceilDiv(a.lAxiom * (BPS - EPS_BPS) * d.B0, BPS * d.Phi0); // least C_amort_burn with Delta_amort = L_axiom
        return M.monus(full, a.amortBurn);
    }

    struct RevealT2 {
        uint32 axiomId;
        uint8 mode; // 1 = II-A (training-data fraud), 2 = III (out-of-sample invariant counterexample Z_punct)
        uint256 dUnroll;
        bool blameDataset;
        bytes32 evidence;
        bytes32 salt;
        uint32 vkVersion;
        bytes proof;
    }

    function slashHash(address who, RevealT2 calldata r) public pure returns (bytes32) {
        return keccak256(abi.encode(who, uint8(2), r.axiomId, r.mode, r.dUnroll, r.blameDataset, r.evidence, r.salt));
    }

    /// @dev Theorem 5.3 (3)(4) admission rule of a proposal: the claimed gross escrow E_tr is capped by the committed creator collateral,
    ///      E_tr <= 10000 (10000 + Lambda_bps) S_c / (10000 sigma_col_bps)   (Lambda = 0: S_c >= E_tr;  Lambda = 1: S_c >= ceil(E_tr / 2)),
    ///      the underwriter co-stake is S_uw <= Lambda S_c, and every cited axiom keeps its Stage-1 reservation inside its own saving.
    ///      Returns 0 when admissible, otherwise the `Rejected` code. Shared by the reveal (reject early) and the batch winner selection.
    function _admission(uint256 e, uint256 sc, uint256 suw, uint32[] memory ids, uint256[] memory bits) internal view returns (uint8) {
        if (e > (BPS * (BPS + params.lambdaBps) * sc) / (BPS * SIGMA_COL_BPS)) return 19;
        if (suw > (params.lambdaBps * sc) / BPS) return 20;
        for (uint256 i = 0; i < ids.length; ++i) {
            uint256 tot;
            for (uint256 j = 0; j < ids.length; ++j) {
                if (ids[j] == ids[i]) tot += bits[j];
            }
            Axiom storage a = ax[ids[i]];
            if (a.sPaid + tot > a.savedBits) return 22;
        }
        return 0;
    }

    function _phiActive(uint32 aid) internal view returns (uint256) {
        PhiDict storage p = phiDict[aid];
        return (p.pendingEpoch != 0 && p.pendingEpoch <= epoch) ? p.pending : p.active;
    }

}
