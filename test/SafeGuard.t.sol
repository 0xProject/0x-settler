// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "@forge-std/Test.sol";
import {console} from "@forge-std/console.sol";
import {Vm} from "@forge-std/Vm.sol";

import {ItoA} from "src/utils/ItoA.sol";
import {AddressDerivation} from "src/utils/AddressDerivation.sol";

interface ISafeSetup {
    function addOwnerWithThreshold(address owner, uint256 _threshold) external;

    function removeOwner(address prevOwner, address owner, uint256 _threshold) external;

    function getOwners() external view returns (address[] memory);

    function setGuard(address guard) external;
}

enum Operation {
    Call,
    DelegateCall
}

interface ISafe {
    function execTransaction(
        address to,
        uint256 value,
        bytes calldata data,
        Operation operation,
        uint256 safeTxGas,
        uint256 baseGas,
        uint256 gasPrice,
        address gasToken,
        address payable refundReceiver,
        bytes memory signatures
    ) external payable returns (bool);

    function nonce() external view returns (uint256);

    function approveHash(bytes32 hashToApprove) external;

    event ApproveHash(bytes32 indexed approvedHash, address indexed owner);
}

interface IGuard {
    function checkTransaction(
        address to,
        uint256 value,
        bytes memory data,
        Operation operation,
        uint256 safeTxGas,
        uint256 baseGas,
        uint256 gasPrice,
        address gasToken,
        address payable refundReceiver,
        bytes memory signatures,
        address msgSender
    ) external;

    function checkAfterExecution(bytes32 txHash, bool success) external;
}

interface IZeroExSettlerDeployerSafeGuard is IGuard {
    event TimelockUpdated(uint256 oldDelay, uint256 newDelay);
    event SafeTransactionEnqueued(
        bytes32 indexed txHash,
        uint256 timelockEnd,
        address indexed to,
        uint256 value,
        bytes data,
        Operation operation,
        uint256 safeTxGas,
        uint256 baseGas,
        uint256 gasPrice,
        address gasToken,
        address payable refundReceiver,
        uint256 indexed nonce,
        bytes signatures
    );
    event SafeTransactionCanceled(bytes32 indexed txHash, address indexed canceledBy);
    event LockDown(address indexed lockedDownBy, bytes32 indexed unlockTxHash);
    event Unlocked();

    error PermissionDenied();
    error NoDelegateCall();
    error GuardNotInstalled();
    error GuardIsOwner();
    error TimelockNotElapsed(bytes32 txHash, uint256 timelockEnd);
    error TimelockElapsed(bytes32 txHash, uint256 timelockEnd);
    error AlreadyQueued(bytes32 txHash);
    error NotQueued(bytes32 txHash);
    error LockedDown(address lockedDownBy);
    error NotLockedDown();
    error UnlockHashNotApproved(bytes32 txHash);
    error UnexpectedUpgrade(address newSingleton);
    error Reentrancy();
    error ModuleInstalled(address module);

    function timelockEnd(bytes32) external view returns (uint256);
    function lockedDownBy() external view returns (address);
    function delay() external view returns (uint24);
    function safe() external view returns (address);

    function enqueue(
        address to,
        uint256 value,
        bytes calldata data,
        Operation operation,
        uint256 safeTxGas,
        uint256 baseGas,
        uint256 gasPrice,
        address gasToken,
        address payable refundReceiver,
        uint256 nonce,
        bytes calldata signatures
    ) external;

    function setDelay(uint24) external;

    function cancel(bytes32 txHash) external;

    function unlockTxHash() external view returns (bytes32);

    function lockDown() external;

    function unlock() external;
}

interface IMulticall {
    function multiSend(bytes memory transactions) external payable;
}

contract TestSafeGuard is Test {
    using ItoA for uint256;

    address internal constant factory = 0x914d7Fec6aaC8cd542e72Bca78B30650d45643d7;
    ISafe internal constant safe = ISafe(0xf36b9f50E59870A24F42F9Ba43b2aD0A4b8f2F51);
    IZeroExSettlerDeployerSafeGuard internal guard;
    uint256 internal pokeCounter;

    Vm.Wallet[] internal owners;

    function setUp() public {
        ISafeSetup _safe = ISafeSetup(address(safe));

        vm.createSelectFork(vm.envString("MAINNET_RPC_URL"), 21015655);
        vm.label(address(this), "FoundryTest");

        string memory mnemonic = "test test test test test test test test test test test junk";
        address[] memory oldOwners = _safe.getOwners();

        for (uint256 i; i < oldOwners.length; i++) {
            owners.push(vm.createWallet(vm.deriveKey(mnemonic, uint32(i)), string.concat("Owner #", i.itoa())));
        }

        vm.startPrank(address(_safe));
        for (uint256 i; i < oldOwners.length; i++) {
            _safe.addOwnerWithThreshold(owners[i].addr, 2);
        }
        for (uint256 i = 0; i < oldOwners.length; i++) {
            _safe.removeOwner(owners[0].addr, oldOwners[i], 2);
        }
        vm.stopPrank();

        oldOwners = _safe.getOwners();
        console.log(oldOwners.length, "owners");
        for (uint256 i = oldOwners.length; i > 0;) {
            i--;
            console.log("Owner", oldOwners[i]);
        }

        bytes memory creationCode = vm.getCode("SafeGuard.sol:ZeroExSettlerDeployerSafeGuard");
        guard = IZeroExSettlerDeployerSafeGuard(
            AddressDerivation.deriveDeterministicContract(factory, bytes32(0), keccak256(creationCode))
        );

        vm.prank(address(_safe));
        _safe.setGuard(address(guard));

        (bool success, bytes memory returndata) = factory.call(bytes.concat(bytes32(0), creationCode));
        assertTrue(success);
        assertEq(address(uint160(bytes20(returndata))), address(guard));

        vm.prank(address(_safe));
        guard.setDelay(uint24(1 weeks));

        // Heck yeah, bubble sort
        {
            Vm.Wallet memory tmp;
            for (uint256 i = 1; i < owners.length; i++) {
                for (uint256 j = i; j > 0; j--) {
                    if (owners[j - 1].addr > owners[j].addr) {
                        tmp = owners[j - 1];
                        owners[j - 1] = owners[j];
                        owners[j] = tmp;
                    }
                }
            }
            for (uint256 i; i < owners.length - 1; i++) {
                assertLt(uint160(owners[i].addr), uint160(owners[i + 1].addr));
            }
        }
    }

    function poke() external returns (uint256) {
        require(msg.sender == address(safe));
        return ++pokeCounter;
    }

    function _signSafeEncoded(Vm.Wallet storage signer, bytes32 hash) internal returns (bytes memory) {
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(signer, hash);
        return abi.encodePacked(r, s, v);
    }

    function _enqueuePoke()
        internal
        returns (
            address to,
            uint256 value,
            bytes memory data,
            Operation operation,
            uint256 safeTxGas,
            uint256 baseGas,
            uint256 gasPrice,
            address gasToken,
            address payable refundReceiver,
            uint256 nonce,
            bytes32 txHash,
            bytes memory signatures
        )
    {
        to = address(this);
        value = 0 ether;
        data = abi.encodeCall(this.poke, ());
        operation = Operation.Call;
        safeTxGas = 0;
        baseGas = 0;
        gasPrice = 0;
        gasToken = address(0);
        refundReceiver = payable(address(0));
        nonce = safe.nonce();

        txHash = keccak256(
            bytes.concat(
                hex"1901",
                keccak256(
                    abi.encode(
                        keccak256("EIP712Domain(uint256 chainId,address verifyingContract)"), block.chainid, safe
                    )
                ),
                keccak256(
                    abi.encode(
                        keccak256(
                            "SafeTx(address to,uint256 value,bytes data,uint8 operation,uint256 safeTxGas,uint256 baseGas,uint256 gasPrice,address gasToken,address refundReceiver,uint256 nonce)"
                        ),
                        to,
                        value,
                        keccak256(data),
                        operation,
                        safeTxGas,
                        baseGas,
                        gasPrice,
                        gasToken,
                        refundReceiver,
                        nonce
                    )
                )
            )
        );

        signatures = abi.encodePacked(_signSafeEncoded(owners[0], txHash), _signSafeEncoded(owners[1], txHash));

        vm.expectEmit(true, true, true, true, address(guard));
        emit IZeroExSettlerDeployerSafeGuard.SafeTransactionEnqueued(
            txHash,
            guard.delay() + vm.getBlockTimestamp(),
            to,
            value,
            data,
            operation,
            safeTxGas,
            baseGas,
            gasPrice,
            gasToken,
            refundReceiver,
            nonce,
            signatures
        );

        guard.enqueue(
            to, value, data, operation, safeTxGas, baseGas, gasPrice, gasToken, refundReceiver, nonce, signatures
        );
    }

    function testHappyPath() public {
        (
            address to,
            uint256 value,
            bytes memory data,
            Operation operation,
            uint256 safeTxGas,
            uint256 baseGas,
            uint256 gasPrice,
            address gasToken,
            address payable refundReceiver,
            ,
            ,
            bytes memory signatures
        ) = _enqueuePoke();

        vm.warp(vm.getBlockTimestamp() + guard.delay() + 1 seconds);

        safe.execTransaction(
            to, value, data, operation, safeTxGas, baseGas, gasPrice, gasToken, refundReceiver, signatures
        );

        assertEq(pokeCounter, 1);
    }

    function testTimelockNonExpiry() external {
        (
            address to,
            uint256 value,
            bytes memory data,
            Operation operation,
            uint256 safeTxGas,
            uint256 baseGas,
            uint256 gasPrice,
            address gasToken,
            address payable refundReceiver,
            ,
            bytes32 txHash,
            bytes memory signatures
        ) = _enqueuePoke();

        vm.warp(vm.getBlockTimestamp() + guard.delay());

        vm.expectRevert(
            abi.encodeWithSelector(
                IZeroExSettlerDeployerSafeGuard.TimelockNotElapsed.selector, txHash, vm.getBlockTimestamp()
            )
        );
        safe.execTransaction(
            to, value, data, operation, safeTxGas, baseGas, gasPrice, gasToken, refundReceiver, signatures
        );
    }

    function testCancelHappyPath() external {
        (
            address to,
            uint256 value,
            bytes memory data,
            Operation operation,
            uint256 safeTxGas,
            uint256 baseGas,
            uint256 gasPrice,
            address gasToken,
            address payable refundReceiver,
            ,
            bytes32 txHash,
            bytes memory signatures
        ) = _enqueuePoke();

        bytes32 unlockTxHash = guard.unlockTxHash();

        vm.startPrank(owners[owners.length - 1].addr);

        vm.expectEmit(true, true, true, true, address(safe));
        emit ISafe.ApproveHash(unlockTxHash, owners[4].addr);
        safe.approveHash(unlockTxHash);

        vm.expectEmit(true, true, true, true, address(guard));
        emit IZeroExSettlerDeployerSafeGuard.SafeTransactionCanceled(txHash, owners[4].addr);
        guard.cancel(txHash);

        vm.stopPrank();

        vm.warp(vm.getBlockTimestamp() + guard.delay() + 1 seconds);

        vm.expectRevert(
            abi.encodeWithSelector(
                IZeroExSettlerDeployerSafeGuard.TimelockNotElapsed.selector, txHash, type(uint256).max
            )
        );
        safe.execTransaction(
            to, value, data, operation, safeTxGas, baseGas, gasPrice, gasToken, refundReceiver, signatures
        );
    }

    function testCancelNoApprove() external {
        (,,,,,,,,,, bytes32 txHash,) = _enqueuePoke();

        bytes32 unlockTxHash = guard.unlockTxHash();

        vm.prank(owners[4].addr);
        vm.expectRevert(
            abi.encodeWithSelector(IZeroExSettlerDeployerSafeGuard.UnlockHashNotApproved.selector, unlockTxHash)
        );
        guard.cancel(txHash);
    }

    function testCancelNotOwner() external {
        (,,,,,,,,,, bytes32 txHash,) = _enqueuePoke();

        vm.expectRevert(abi.encodeWithSelector(IZeroExSettlerDeployerSafeGuard.PermissionDenied.selector));
        guard.cancel(txHash);
    }

    function testLockDownHappyPath()
        public
        returns (
            address to,
            uint256 value,
            bytes memory data,
            Operation operation,
            uint256 safeTxGas,
            uint256 baseGas,
            uint256 gasPrice,
            address gasToken,
            address payable refundReceiver,
            bytes32 txHash,
            bytes memory signatures
        )
    {
        (to, value, data, operation, safeTxGas, baseGas, gasPrice, gasToken, refundReceiver,, txHash, signatures) =
            _enqueuePoke();

        bytes32 unlockTxHash = guard.unlockTxHash();

        vm.startPrank(owners[4].addr);

        vm.expectEmit(true, true, true, true, address(safe));
        emit ISafe.ApproveHash(unlockTxHash, owners[4].addr);
        safe.approveHash(unlockTxHash);

        vm.expectEmit(true, true, true, true, address(guard));
        emit IZeroExSettlerDeployerSafeGuard.LockDown(owners[4].addr, unlockTxHash);
        guard.lockDown();

        vm.stopPrank();

        vm.warp(vm.getBlockTimestamp() + guard.delay() + 1 seconds);

        vm.expectRevert(abi.encodeWithSelector(IZeroExSettlerDeployerSafeGuard.LockedDown.selector, owners[4].addr));
        safe.execTransaction(
            to, value, data, operation, safeTxGas, baseGas, gasPrice, gasToken, refundReceiver, signatures
        );
    }

    function testUnlockHappyPath() external {
        (
            address to,
            uint256 value,
            bytes memory data,
            Operation operation,
            uint256 safeTxGas,
            uint256 baseGas,
            uint256 gasPrice,
            address gasToken,
            address payable refundReceiver,
            ,
            bytes memory signatures
        ) = testLockDownHappyPath();

        {
            address unlockTo = address(guard);
            uint256 unlockValue = 0 ether;
            bytes memory unlockData = abi.encodeCall(guard.unlock, ());
            Operation unlockOperation = Operation.Call;
            uint256 unlockSafeTxGas = 0;
            uint256 unlockBaseGas = 0;
            uint256 unlockGasPrice = 0;
            address unlockGasToken = address(0);
            address payable unlockRefundReceiver = payable(address(0));

            bytes32 unlockTxHash = keccak256(
                bytes.concat(
                    hex"1901",
                    keccak256(
                        abi.encode(
                            keccak256("EIP712Domain(uint256 chainId,address verifyingContract)"), block.chainid, safe
                        )
                    ),
                    keccak256(
                        abi.encode(
                            keccak256(
                                "SafeTx(address to,uint256 value,bytes data,uint8 operation,uint256 safeTxGas,uint256 baseGas,uint256 gasPrice,address gasToken,address refundReceiver,uint256 nonce)"
                            ),
                            unlockTo,
                            unlockValue,
                            keccak256(unlockData),
                            unlockOperation,
                            unlockSafeTxGas,
                            unlockBaseGas,
                            unlockGasPrice,
                            unlockGasToken,
                            unlockRefundReceiver,
                            safe.nonce()
                        )
                    )
                )
            );

            bytes memory unlockSignatures = abi.encodePacked(
                _signSafeEncoded(owners[0], unlockTxHash),
                _signSafeEncoded(owners[1], unlockTxHash),
                _signSafeEncoded(owners[2], unlockTxHash),
                _signSafeEncoded(owners[3], unlockTxHash),
                uint256(uint160(owners[4].addr)),
                bytes32(0),
                uint8(1)
            );
            safe.execTransaction(
                unlockTo,
                unlockValue,
                unlockData,
                unlockOperation,
                unlockSafeTxGas,
                unlockBaseGas,
                unlockGasPrice,
                unlockGasToken,
                unlockRefundReceiver,
                unlockSignatures
            );
        }

        vm.expectRevert("GS026");
        safe.execTransaction(
            to, value, data, operation, safeTxGas, baseGas, gasPrice, gasToken, refundReceiver, signatures
        );

        testHappyPath();
    }

    IMulticall internal constant _MULTICALL = IMulticall(0xA1dabEF33b3B82c7814B6D82A79e50F4AC44102B);

    function _encodeMulticallPoke()
        internal
        returns (
            address to,
            uint256 value,
            bytes memory data,
            Operation operation,
            uint256 safeTxGas,
            uint256 baseGas,
            uint256 gasPrice,
            address gasToken,
            address payable refundReceiver,
            uint256 nonce,
            bytes32 txHash,
            bytes memory signatures
        )
    {
        to = address(_MULTICALL);
        value = 0 ether;
        data = abi.encodeCall(this.poke, ());
        data = abi.encodeCall(
            _MULTICALL.multiSend,
            (abi.encodePacked(uint8(Operation.Call), address(this), uint256(0 ether), uint256(data.length), data))
        );
        operation = Operation.DelegateCall;
        safeTxGas = 0;
        baseGas = 0;
        gasPrice = 0;
        gasToken = address(0);
        refundReceiver = payable(address(0));
        nonce = safe.nonce();

        txHash = keccak256(
            bytes.concat(
                hex"1901",
                keccak256(
                    abi.encode(
                        keccak256("EIP712Domain(uint256 chainId,address verifyingContract)"), block.chainid, safe
                    )
                ),
                keccak256(
                    abi.encode(
                        keccak256(
                            "SafeTx(address to,uint256 value,bytes data,uint8 operation,uint256 safeTxGas,uint256 baseGas,uint256 gasPrice,address gasToken,address refundReceiver,uint256 nonce)"
                        ),
                        to,
                        value,
                        keccak256(data),
                        operation,
                        safeTxGas,
                        baseGas,
                        gasPrice,
                        gasToken,
                        refundReceiver,
                        nonce
                    )
                )
            )
        );

        signatures = abi.encodePacked(_signSafeEncoded(owners[0], txHash), _signSafeEncoded(owners[1], txHash));
    }

    function testMulticall0() external {
        (
            address to,
            uint256 value,
            bytes memory data,
            Operation operation,
            uint256 safeTxGas,
            uint256 baseGas,
            uint256 gasPrice,
            address gasToken,
            address payable refundReceiver,
            uint256 nonce,
            ,
            bytes memory signatures
        ) = _encodeMulticallPoke();

        vm.expectRevert(abi.encodeWithSelector(IZeroExSettlerDeployerSafeGuard.NoDelegateCall.selector));
        guard.enqueue(
            to, value, data, operation, safeTxGas, baseGas, gasPrice, gasToken, refundReceiver, nonce, signatures
        );
    }

    function testMulticall1() external {
        (
            address to,
            uint256 value,
            bytes memory data,
            Operation operation,
            uint256 safeTxGas,
            uint256 baseGas,
            uint256 gasPrice,
            address gasToken,
            address payable refundReceiver,
            ,
            ,
            bytes memory signatures
        ) = _encodeMulticallPoke();

        vm.expectRevert(abi.encodeWithSelector(IZeroExSettlerDeployerSafeGuard.NoDelegateCall.selector));
        safe.execTransaction(
            to, value, data, operation, safeTxGas, baseGas, gasPrice, gasToken, refundReceiver, signatures
        );
    }
}
