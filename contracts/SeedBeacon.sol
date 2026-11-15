// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {IBatchRoot, IDrandVerifier} from "./Interfaces.sol";

/// @title SeedBeacon
/// @notice rho_batch = keccak256(entropy(batch), batchRoot(batch), batch).
///  * `batchRoot` is the running hash of every Phase-1 commit of the batch, fixed before the entropy exists (no grinding);
///  * entropy enters ONCE per batch, no earlier than `N_COM + N_DELAY` blocks after the batch start, from either
///      (1) the permissionless L1 relay (the L1 contract's L2 alias is `relayer`; it forwards the L1 RANDAO), or
///      (2) a drand round whose BLS signature is verified on-chain (`drand` verifier; production: precompile / zkVM adapter).
///    `block.prevrandao` is NOT used: it is the constant 1 on Arbitrum.
contract SeedBeacon {
    uint256 public immutable genesis;
    uint256 public immutable readyOffset; // N_COM + N_DELAY
    address public immutable relayer;
    IDrandVerifier public immutable drand;
    uint64 public immutable drandRoundBase;
    uint64 public immutable drandRoundsPerBatch;
    address public immutable deployer;
    IBatchRoot public esm;

    mapping(uint256 => bytes32) public entropy;
    mapping(uint256 => uint8) public source; // 1 = L1 relay, 2 = drand

    error AlreadyBound();
    error NotDeployer();
    error NotRelayer();
    error TooEarly();
    error AlreadySet();
    error WrongRound(uint64 got, uint64 want);

    event SeedSet(uint256 indexed batch, uint8 source, bytes32 entropy);

    constructor(uint256 genesis_, uint256 readyOffset_, address relayer_, IDrandVerifier drand_, uint64 roundBase, uint64 roundsPerBatch) {
        genesis = genesis_;
        readyOffset = readyOffset_;
        relayer = relayer_;
        drand = drand_;
        drandRoundBase = roundBase;
        drandRoundsPerBatch = roundsPerBatch;
        deployer = msg.sender;
    }

    function bind(IBatchRoot esm_) external {
        if (msg.sender != deployer) revert NotDeployer();
        if (address(esm) != address(0)) revert AlreadyBound();
        esm = esm_;
    }

    function readyBlock(uint256 batch) public view returns (uint256) {
        return genesis + batch * 300 + readyOffset; // N_BATCH = 300 (params.toml)
    }

    function relaySeed(uint256 batch, bytes32 l1Randao) external {
        if (msg.sender != relayer) revert NotRelayer();
        _set(batch, l1Randao, 1);
    }

    function expectedRound(uint256 batch) public view returns (uint64) {
        return drandRoundBase + uint64(batch) * drandRoundsPerBatch;
    }

    function submitDrand(uint256 batch, uint64 round, bytes calldata signature) external {
        if (round != expectedRound(batch)) revert WrongRound(round, expectedRound(batch));
        _set(batch, drand.verify(round, signature), 2);
    }

    function _set(uint256 batch, bytes32 e, uint8 src) internal {
        if (block.number < readyBlock(batch)) revert TooEarly();
        if (entropy[batch] != bytes32(0)) revert AlreadySet();
        entropy[batch] = e == bytes32(0) ? bytes32(uint256(1)) : e;
        source[batch] = src;
        emit SeedSet(batch, src, e);
    }

    function isReady(uint256 batch) external view returns (bool) {
        return entropy[batch] != bytes32(0);
    }

    function seed(uint256 batch) external view returns (bytes32) {
        bytes32 e = entropy[batch];
        require(e != bytes32(0), "seed not ready");
        return keccak256(abi.encode(e, esm.batchRoot(batch), batch));
    }
}

/// @notice TEST ONLY drand stand-in: signature must be abi.encode(round, tag); randomness = keccak256(signature)
contract MockDrand is IDrandVerifier {
    function verify(uint64 round, bytes calldata signature) external pure returns (bytes32) {
        require(signature.length == 64 && uint256(bytes32(signature[0:32])) == round, "bad drand signature");
        return keccak256(signature);
    }
}
