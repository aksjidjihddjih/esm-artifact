// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

interface IERC20 {
    function balanceOf(address) external view returns (uint256);
    function transfer(address to, uint256 amount) external returns (bool);
    function transferFrom(address from, address to, uint256 amount) external returns (bool);
}

/// @dev zkVM proof verifier adapter: returns true iff `proof` proves the guest program `vkey` produced `publicValues`
interface IVerifier {
    function verify(bytes32 vkey, bytes calldata publicValues, bytes calldata proof) external view returns (bool);
}

/// @dev SP1 on-chain verifier (Groth16 / Plonk gateway): reverts when the proof is invalid
interface ISP1Verifier {
    function verifyProof(bytes32 programVKey, bytes calldata publicValues, bytes calldata proofBytes) external view;
}

interface IVerifierRegistry {
    function verify(uint8 kind, uint32 version, bytes calldata publicValues, bytes calldata proof) external view returns (bool);
}

interface ISeedBeacon {
    function isReady(uint256 batch) external view returns (bool);
    function seed(uint256 batch) external view returns (bytes32);
}

interface IArchiveRegistry {
    function register(uint32 id, bytes32 root, uint32 nK, uint16 bK, uint8 storageKind, bytes calldata uri) external returns (uint256 phi0);
    function rootOf(uint32 id) external view returns (bytes32);
}

interface IBatchRoot {
    function batchRoot(uint256 batch) external view returns (bytes32);
}

/// @dev drand (League of Entropy) BLS verification: returns the round's randomness, reverts if the signature is invalid
interface IDrandVerifier {
    function verify(uint64 round, bytes calldata signature) external view returns (bytes32 randomness);
}
