// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Script} from "@forge-std/Script.sol";
import {Vm, VmSafe} from "@forge-std/Vm.sol";
import {SafeConfig} from "./SafeConfig.sol";
import {SafeBytecodes} from "./SafeCode.sol";

interface ISafeFactory {
    function createProxyWithNonce(address singleton, bytes calldata initializer, uint256 saltNonce)
        external
        returns (address);
    function proxyCreationCode() external view returns (bytes memory);
}

interface ISafeExecute {
    enum Operation {
        Call,
        DelegateCall
    }

    function execTransaction(
        address to,
        uint256 value,
        bytes calldata data,
        Operation operation,
        uint256 safeTxGas,
        uint256 baseGas,
        uint256 gasPrice,
        address gasToken,
        address refundReceiver,
        bytes calldata signatures
    ) external payable returns (bool);
}

interface ISafeOwners {
    function addOwnerWithThreshold(address owner, uint256 _threshold) external;
    function removeOwner(address prevOwner, address owner, uint256 _threshold) external;
    function changeThreshold(uint256 _threshold) external;
    function getOwners() external view returns (address[] memory);
    function getThreshold() external view returns (uint256);
    function isModuleEnabled(address module) external view returns (bool);
}

abstract contract SafeMultisend is Script {
    bytes32 internal constant multicallHash = 0xa9865ac2d9c7a1591619b188c4d88167b50df6cc0c5327fcbd1c8c75f7c066ad;
    bytes32 internal constant multicallHashEraVm = 0x064ddbf252714bcd4cb79f679e8c12df96d998ce07bbb13b3118c1dbf4a31942;

    function _assertMulticallCodehash(address safeMulticall) internal view {
        require(
            safeMulticall.codehash == (SafeConfig.isEraVm() ? multicallHashEraVm : multicallHash),
            "Safe multicall codehash"
        );
    }

    function _wrapSingleMultisend(bytes memory call) internal view returns (bytes memory) {
        bytes[] memory calls = new bytes[](1);
        calls[0] = call;
        return _encodeMultisend(calls);
    }

    function _encodeMultisend(bytes[] memory calls) internal view returns (bytes memory result) {
        // The Gnosis multicall contract uses a very obnoxious packed encoding
        // that is very similar to, but not exactly the same as
        // `abi.encodePacked`
        assembly ("memory-safe") {
            result := mload(0x40)
            mstore(add(0x04, result), 0x8d80ff0a) // selector for `multiSend(bytes)`
            mstore(add(0x24, result), 0x20)
            let bytes_length_ptr := add(0x44, result)
            mstore(bytes_length_ptr, 0x00)
            for {
                let i := add(0x20, calls)
                let end := add(i, shl(0x05, mload(calls)))
                let dst := add(0x20, bytes_length_ptr)
            } lt(i, end) { i := add(0x20, i) } {
                let src := mload(i)
                let len := mload(src)
                src := add(0x20, src)

                // We're using the old identity precompile version instead of
                // the MCOPY opcode version because I don't want to have to deal
                // with maintaining two versions of this
                if or(xor(returndatasize(), len), iszero(staticcall(gas(), 0x04, src, len, dst, len))) {
                    invalid()
                }

                dst := add(dst, len)
                mstore(bytes_length_ptr, add(len, mload(bytes_length_ptr)))
            }
            mstore(result, add(0x44, mload(bytes_length_ptr)))
            mstore(0x40, add(0x20, add(mload(result), result)))
        }
    }

    function _encodeMultisend(address safe, bytes memory call) internal pure returns (bytes memory) {
        return abi.encodePacked(
            uint8(ISafeExecute.Operation.Call),
            safe,
            uint256(0), // value
            call.length,
            call
        );
    }

    function _encodeChangeOwners(address safe, uint256 threshold, address oldOwner, address[] memory newOwners)
        internal
        pure
        returns (bytes[] memory)
    {
        bytes[] memory subCalls = new bytes[](newOwners.length + 1);
        for (uint256 i; i < newOwners.length; i++) {
            bytes memory data =
                abi.encodeCall(ISafeOwners.addOwnerWithThreshold, (newOwners[newOwners.length - i - 1], 1));
            subCalls[i] = _encodeMultisend(safe, data);
        }
        {
            bytes memory data =
                abi.encodeCall(ISafeOwners.removeOwner, (newOwners[newOwners.length - 1], oldOwner, threshold));
            subCalls[newOwners.length] = _encodeMultisend(safe, data);
        }
        return subCalls;
    }

    function _encodeSolversMultisend(address intentSettler, address[] memory solvers)
        internal
        pure
        returns (bytes[] memory)
    {
        bytes[] memory subCalls = new bytes[](solvers.length);
        address prevSolver = 0x0000000000000000000000000000000000000001;
        for (uint256 i; i < solvers.length; i++) {
            address solver = solvers[i];
            subCalls[i] = _encodeMultisend(
                intentSettler, abi.encodeWithSignature("setSolver(address,address,bool)", prevSolver, solver, true)
            );
            prevSolver = solver;
        }
        return subCalls;
    }

    function _assertEip7825(uint256[] memory gasSplits) internal pure {
        for (uint256 i = 1; i < gasSplits.length; i++) {
            require(gasSplits[i] + 15728639 > gasSplits[i - 1], "transaction is likely to exceed EIP-7825 limit");
        }
    }

    modifier eraVmCompat(
        bool isEraVm,
        uint256 privateKey,
        ISafeExecute safe,
        ISafeFactory safeFactory,
        address safeSingleton,
        address safeFallback,
        address safeMulticall,
        SafeBytecodes memory safeBytecodes
    ) {
        if (isEraVm) {
            (VmSafe.CallerMode callerMode, address msgSender, address txOrigin) = vm.readCallers();
            require(callerMode != VmSafe.CallerMode.Broadcast);
            if (callerMode == VmSafe.CallerMode.RecurrentBroadcast) {
                require(msgSender == txOrigin);
                require(msgSender == vm.addr(privateKey));
                vm.stopBroadcast();
            }

            bytes memory oldFactoryCode = address(safeFactory).code;
            vm.etch(address(safeFactory), safeBytecodes.factoryCode);
            bytes memory oldSingletonCode = safeSingleton.code;
            vm.etch(safeSingleton, safeBytecodes.singletonCode);
            bytes memory oldFallbackCode = safeFallback.code;
            vm.etch(safeFallback, safeBytecodes.fallbackCode);
            bytes memory oldMulticallCode = safeMulticall.code;
            vm.etch(safeMulticall, safeBytecodes.multicallCode);

            bytes memory oldSafeCode;
            if (address(safe) != address(0)) {
                oldSafeCode = address(safe).code;
                vm.etch(address(safe), safeBytecodes.proxyCode);
            }

            vm.startPrank(msgSender, txOrigin);
            vm.startStateDiffRecording();
            _;
            uint256 gasUsed = vm.lastCallGas().gasTotalUsed;
            Vm.AccountAccess[] memory accesses = vm.stopAndReturnStateDiff();
            vm.stopPrank();
            gasUsed = gasUsed * 6 / 5;

            Vm.AccountAccess memory theOneImportantCall;
            for (uint256 i; i < accesses.length; i++) {
                theOneImportantCall = accesses[i];
                if (theOneImportantCall.kind == VmSafe.AccountAccessKind.Call) {
                    require(theOneImportantCall.accessor == msgSender, "unexpected top-level call");
                    for (uint256 j = i + 1; j < accesses.length; j++) {
                        Vm.AccountAccess memory jAA = accesses[j];
                        if (jAA.kind == VmSafe.AccountAccessKind.Call) {
                            require(jAA.accessor != msgSender || jAA.account == address(vm), "duplicate top-level call");
                        }
                    }
                    break;
                }
            }

            vm.etch(address(safeFactory), oldFactoryCode);
            vm.etch(safeSingleton, oldSingletonCode);
            vm.etch(safeFallback, oldFallbackCode);
            vm.etch(safeMulticall, oldMulticallCode);

            if (address(safe) != address(0)) {
                vm.etch(address(safe), oldSafeCode);
            }

            if (callerMode == VmSafe.CallerMode.RecurrentBroadcast) {
                vm.startBroadcast(privateKey);

                // repeat the call from the modified function, blindly, while broadcasting
                {
                    address target = theOneImportantCall.account;
                    uint256 value = theOneImportantCall.value;
                    bytes memory data = theOneImportantCall.data;
                    assembly ("memory-safe") {
                        pop(call(gasUsed, target, value, add(0x20, data), mload(data), 0x00, 0x00))
                    }
                }
            }
        } else {
            _;
        }
    }
}
