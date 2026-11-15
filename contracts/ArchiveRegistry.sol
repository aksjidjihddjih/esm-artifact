// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

/// @title ArchiveRegistry
/// @notice T0 record of a dataset D_k: keccak Merkle root of its records, n_k <= 2^30, b_k <= 2^10 (Phi_k^(0) = n_k b_k <= 2^40) and WHERE the data
///         lives permanently. Blobs are NOT used (pruned after ~18 days; L2 users cannot send blob transactions).
///   storageKind 0: small data posted as calldata of the register call (the bytes are hashed and emitted, nothing stored on chain but the hash)
///   storageKind 1: Arweave transaction id (32 bytes)      storageKind 2: IPFS CID (<= 64 bytes)
contract ArchiveRegistry {
    address public immutable esm;

    struct Record {
        bytes32 root;
        uint32 nK;
        uint16 bK;
        uint8 storageKind;
        bytes32 uriHash;
    }

    mapping(uint32 => Record) private records;
    mapping(uint32 => bytes) private uris; // Arweave / IPFS locators only

    error NotESM();
    error AlreadyRegistered();
    error BadShape();
    error BadLocator();

    event DatasetArchived(uint32 indexed id, bytes32 root, uint32 nK, uint16 bK, uint8 storageKind, bytes data);

    constructor(address esm_) {
        esm = esm_;
    }

    function register(uint32 id, bytes32 root, uint32 nK, uint16 bK, uint8 storageKind, bytes calldata uri) external returns (uint256 phi0) {
        if (msg.sender != esm) revert NotESM();
        if (records[id].nK != 0) revert AlreadyRegistered();
        if (nK == 0 || nK > (uint32(1) << 30) || bK == 0 || bK > 1024) revert BadShape();
        phi0 = uint256(nK) * uint256(bK); // <= 2^40
        if (storageKind == 0) {
            if (uri.length > 24_000) revert BadLocator(); // small data only
        } else if (storageKind == 1) {
            if (uri.length != 32) revert BadLocator();
            uris[id] = uri;
        } else if (storageKind == 2) {
            if (uri.length < 32 || uri.length > 64) revert BadLocator();
            uris[id] = uri;
        } else {
            revert BadLocator();
        }
        records[id] = Record(root, nK, bK, storageKind, keccak256(uri));
        emit DatasetArchived(id, root, nK, bK, storageKind, uri);
    }

    function rootOf(uint32 id) external view returns (bytes32) {
        return records[id].root;
    }

    function recordOf(uint32 id) external view returns (Record memory r, bytes memory locator) {
        return (records[id], uris[id]);
    }

    /// @notice Keccak Merkle membership of `leaf` at `index` (bit i of `index` selects left/right at level i); depth must be clog2(n_k)
    function verifyLeaf(uint32 id, bytes32 leaf, uint256 index, bytes32[] calldata proof) external view returns (bool) {
        Record storage r = records[id];
        if (r.nK == 0 || index >= r.nK) return false;
        uint256 depth;
        while ((uint256(1) << depth) < r.nK) depth++;
        if (proof.length != depth) return false;
        bytes32 h = leaf;
        for (uint256 i = 0; i < proof.length; ++i) {
            h = ((index >> i) & 1) == 0 ? keccak256(abi.encodePacked(h, proof[i])) : keccak256(abi.encodePacked(proof[i], h));
        }
        return h == r.root;
    }
}
