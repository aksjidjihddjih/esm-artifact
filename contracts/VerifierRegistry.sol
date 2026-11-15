// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {IVerifier, ISP1Verifier} from "./Interfaces.sol";

/// @title VerifierRegistry
/// @notice Versioned zkVM program keys (vkeys). The consensus-critical `esm-core` guest has ONE binary per version; fixing a bug
///         means registering a new (vkey, verifier) pair, never mutating an old one. The guardian can add / revoke versions only until
///         `guardianExpiry` (a block number); afterwards the registry is immutable except for nothing at all.
contract VerifierRegistry {
    uint8 public constant PROG_T1 = 1; // K_spot batch run + Counted MST
    uint8 public constant PROG_T2 = 2; // training-data fraud / out-of-sample counterexample
    uint8 public constant PROG_T6 = 3; // bounded Bohm-tree equivalence

    struct Version {
        bytes32 vkey;
        IVerifier verifier;
        bool revoked;
    }

    mapping(uint8 => Version[]) private versions;
    address public guardian;
    uint256 public immutable guardianExpiry;

    error NotGuardian();
    error GuardianExpired();
    error UnknownVersion();
    error BadKind();

    event VersionAdded(uint8 indexed kind, uint32 indexed version, bytes32 vkey, address verifier);
    event VersionRevoked(uint8 indexed kind, uint32 indexed version);
    event GuardianRenounced();

    constructor(address guardian_, uint256 guardianExpiryBlock) {
        guardian = guardian_;
        guardianExpiry = guardianExpiryBlock;
    }

    modifier onlyGuardian() {
        if (msg.sender != guardian) revert NotGuardian();
        if (block.number >= guardianExpiry) revert GuardianExpired();
        _;
    }

    function addVersion(uint8 kind, bytes32 vkey, IVerifier verifier) external onlyGuardian returns (uint32 version) {
        if (kind < 1 || kind > 3) revert BadKind();
        version = uint32(versions[kind].length);
        versions[kind].push(Version(vkey, verifier, false));
        emit VersionAdded(kind, version, vkey, address(verifier));
    }

    function revokeVersion(uint8 kind, uint32 version) external onlyGuardian {
        if (version >= versions[kind].length) revert UnknownVersion();
        versions[kind][version].revoked = true;
        emit VersionRevoked(kind, version);
    }

    function renounceGuardian() external {
        if (msg.sender != guardian) revert NotGuardian();
        guardian = address(0);
        emit GuardianRenounced();
    }

    function versionCount(uint8 kind) external view returns (uint256) {
        return versions[kind].length;
    }

    function getVersion(uint8 kind, uint32 version) external view returns (bytes32 vkey, address verifier, bool revoked) {
        if (version >= versions[kind].length) revert UnknownVersion();
        Version storage v = versions[kind][version];
        return (v.vkey, address(v.verifier), v.revoked);
    }

    function verify(uint8 kind, uint32 version, bytes calldata publicValues, bytes calldata proof) external view returns (bool) {
        if (version >= versions[kind].length) return false;
        Version storage v = versions[kind][version];
        if (v.revoked) return false;
        return v.verifier.verify(v.vkey, publicValues, proof);
    }
}

/// @notice production adapter: SP1 gateway (reverts on invalid proofs) -> bool
contract SP1VerifierAdapter is IVerifier {
    ISP1Verifier public immutable sp1;

    constructor(ISP1Verifier sp1_) {
        sp1 = sp1_;
    }

    function verify(bytes32 vkey, bytes calldata publicValues, bytes calldata proof) external view returns (bool) {
        try sp1.verifyProof(vkey, publicValues, proof) {
            return true;
        } catch {
            return false;
        }
    }
}

/// @notice TEST ONLY: accepts `proof == abi.encode(keccak256(abi.encode(vkey, publicValues)))`
contract MockVerifier is IVerifier {
    bool public accept = true;

    function setAccept(bool a) external {
        accept = a;
    }

    function verify(bytes32 vkey, bytes calldata publicValues, bytes calldata proof) external view returns (bool) {
        return accept && proof.length == 32 && bytes32(proof) == keccak256(abi.encode(vkey, publicValues));
    }
}
