// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {BasePairTest} from "./BasePairTest.t.sol";

import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {IZeroEx} from "./vendor/IZeroEx.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {LibBytes} from "../utils/LibBytes.sol";
import {SafeTransferLib} from "src/vendor/SafeTransferLib.sol";

import {IAllowanceHolder} from "src/allowanceholder/IAllowanceHolder.sol";
import {MainnetSettler as Settler} from "src/chains/Mainnet/TakerSubmitted.sol";

contract Shim {
    // forgefmt: disable-next-line
    function chainId() external returns (uint256) { // this is non-view (mutable) on purpose
        return block.chainid;
    }

    // forgefmt: disable-next-line
    function blockNumber() external returns (uint256) { // this is non-view (mutable) on purpose
        return block.number;
    }
}

abstract contract SettlerBasePairTest is BasePairTest {
    using SafeTransferLib for IERC20;
    using LibBytes for bytes;

    uint256 internal constant PERMIT2_MAKER_NONCE = 1;

    Settler internal settler;
    IAllowanceHolder internal allowanceHolder;
    IZeroEx internal ZERO_EX = IZeroEx(0xDef1C0ded9bec7F1a1670819833240f027b25EfF);

    function settlerInitCode() internal virtual returns (bytes memory) {
        return bytes.concat(type(Settler).creationCode, abi.encode(bytes20(0)));
    }

    function _deploySettler() private returns (Settler r) {
        bytes memory initCode = settlerInitCode();
        assembly ("memory-safe") {
            r := create(0x00, add(0x20, initCode), mload(initCode))
            if iszero(r) { revert(0x00, 0x00) }
        }
    }

    function setUp() public virtual override {
        super.setUp();
        allowanceHolder = IAllowanceHolder(0x0000000000001fF3684f28c67538d4D072C22734);

        uint256 forkChainId = (new Shim()).chainId();
        vm.chainId(31337);
        settler = _deploySettler();
        vm.label(address(settler), "Settler");
        vm.etch(address(allowanceHolder), vm.getDeployedCode("AllowanceHolder.sol:AllowanceHolder"));
        vm.label(address(allowanceHolder), "AllowanceHolder");
        vm.chainId(forkChainId);
    }

    bytes32 internal constant CONSIDERATION_TYPEHASH =
        keccak256("Consideration(address token,uint256 amount,address counterparty,bool partialFillAllowed)");
    bytes32 internal constant RFQ_PERMIT2_WITNESS_TYPEHASH = keccak256(
        "PermitWitnessTransferFrom(TokenPermissions permitted,address spender,uint256 nonce,uint256 deadline,Consideration consideration)Consideration(address token,uint256 amount,address counterparty,bool partialFillAllowed)TokenPermissions(address token,uint256 amount)"
    );

    function _getDefaultFromPermit2Action() internal returns (bytes memory) {
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) = _getDefaultFromPermit2();
        return abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(settler), permit, sig));
    }

    function _getDefaultFromPermit2() internal returns (ISignatureTransfer.PermitTransferFrom memory, bytes memory) {
        return _getDefaultFromPermit2(amount());
    }

    function _getDefaultFromPermit2(uint256 amount_)
        internal
        returns (ISignatureTransfer.PermitTransferFrom memory, bytes memory)
    {
        return _getDefaultFromPermit2(fromToken(), amount_);
    }

    function _getDefaultFromPermit2(IERC20 token, uint256 amount_)
        internal
        returns (ISignatureTransfer.PermitTransferFrom memory, bytes memory)
    {
        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(token), amount_, PERMIT2_FROM_NONCE);
        bytes memory sig = getPermitTransferSignature(permit, address(settler), FROM_PRIVATE_KEY, permit2Domain);
        return (permit, sig);
    }
}
