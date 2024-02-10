// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {IERC20} from "../../src/IERC20.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";

import {SettlerBasePairTest} from "./SettlerBasePairTest.t.sol";
import {ICurveV2Pool} from "./vendor/ICurveV2Pool.sol";
import {IZeroEx} from "./vendor/IZeroEx.sol";

import {LibBytes} from "../utils/LibBytes.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";

import {SafeTransferLib} from "../../src/vendor/SafeTransferLib.sol";

import {IAllowanceHolder} from "../../src/allowanceholder/IAllowanceHolder.sol";
import {Settler} from "../../src/Settler.sol";
import {ISettlerActions} from "../../src/ISettlerActions.sol";
import {OtcOrderSettlement} from "../../src/core/OtcOrderSettlement.sol";

abstract contract AllowanceHolderPairTest is SettlerBasePairTest {
    using SafeTransferLib for IERC20;
    using LibBytes for bytes;

    function setUp() public virtual override {
        super.setUp();
        // Trusted Forwarder / Allowance Holder
        safeApproveIfBelow(fromToken(), FROM, address(allowanceHolder), amount());
    }

    function uniswapV3Path() internal virtual returns (bytes memory);
    function uniswapV2Pool() internal virtual returns (address);

    function testAllowanceHolder_uniswapV3() public {
        bytes[] memory actions = ActionDataBuilder.build(
            // Perform a transfer into Settler via AllowanceHolder
            abi.encodeCall(
                ISettlerActions.PERMIT2_TRANSFER_FROM,
                (
                    address(settler),
                    defaultERC20PermitTransfer(address(fromToken()), amount(), 0 /* nonce */ ),
                    new bytes(0) /* sig (empty) */
                )
            ),
            // Execute UniswapV3 from the Settler balance
            abi.encodeCall(ISettlerActions.UNISWAPV3_SWAP_EXACT_IN, (FROM, 10_000, 0, uniswapV3Path()))
        );

        IAllowanceHolder _allowanceHolder = allowanceHolder;
        Settler _settler = settler;
        IERC20 _fromToken = fromToken();
        uint256 _amount = amount();
        //_warm_allowanceHolder_slots(address(fromToken()), amount());

        vm.startPrank(FROM, FROM); // prank both msg.sender and tx.origin
        snapStartName("allowanceHolder_uniswapV3");
        //_cold_account_access();

        _allowanceHolder.exec(
            address(_settler),
            address(_fromToken),
            _amount,
            payable(address(_settler)),
            abi.encodeCall(
                _settler.execute,
                (actions, Settler.AllowedSlippage({buyToken: address(0), recipient: address(0), minAmountOut: 0 ether}))
            )
        );
        snapEnd();
    }

    function testAllowanceHolder_uniswapV3VIP() public {
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(
                // Perform a transfer into directly to the UniswapV3 pool via AllowanceHolder on demand
                ISettlerActions.UNISWAPV3_PERMIT2_SWAP_EXACT_IN,
                (
                    FROM,
                    amount(),
                    0,
                    uniswapV3Path(),
                    defaultERC20PermitTransfer(address(fromToken()), amount(), 0 /* nonce */ ),
                    new bytes(0) // sig (empty)
                )
            )
        );

        IAllowanceHolder _allowanceHolder = allowanceHolder;
        Settler _settler = settler;
        IERC20 _fromToken = fromToken();
        uint256 _amount = amount();
        //_warm_allowanceHolder_slots(address(fromToken()), amount());

        vm.startPrank(FROM, FROM); // prank both msg.sender and tx.origin
        snapStartName("allowanceHolder_uniswapV3VIP");
        //_cold_account_access();

        _allowanceHolder.exec(
            address(_settler),
            address(_fromToken),
            _amount,
            payable(address(_settler)),
            abi.encodeCall(
                _settler.execute,
                (actions, Settler.AllowedSlippage({buyToken: address(0), recipient: address(0), minAmountOut: 0 ether}))
            )
        );
        snapEnd();
    }

    function testAllowanceHolder_uniswapV3VIP_contract() public {
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(
                // Perform a transfer into directly to the UniswapV3 pool via AllowanceHolder on demand
                ISettlerActions.UNISWAPV3_PERMIT2_SWAP_EXACT_IN,
                (
                    FROM,
                    amount(),
                    0,
                    uniswapV3Path(),
                    defaultERC20PermitTransfer(address(fromToken()), amount(), 0 /* nonce */ ),
                    new bytes(0) // sig (empty)
                )
            )
        );

        IAllowanceHolder _allowanceHolder = allowanceHolder;
        Settler _settler = settler;
        IERC20 _fromToken = fromToken();
        uint256 _amount = amount();
        //_warm_allowanceHolder_slots(address(fromToken()), amount());

        vm.startPrank(FROM); // Do not prank tx.origin, msg.sender != tx.origin
        snapStartName("allowanceHolder_uniswapV3VIP_contract");
        //_cold_account_access();

        _allowanceHolder.exec(
            address(_settler),
            address(_fromToken),
            _amount,
            payable(address(_settler)),
            abi.encodeCall(
                _settler.execute,
                (actions, Settler.AllowedSlippage({buyToken: address(0), recipient: address(0), minAmountOut: 0 ether}))
            )
        );
        snapEnd();
    }

    function testAllowanceHolder_otc_VIP() public {
        ISignatureTransfer.PermitTransferFrom memory makerPermit =
            defaultERC20PermitTransfer(address(toToken()), amount(), PERMIT2_MAKER_NONCE);
        ISignatureTransfer.PermitTransferFrom memory takerPermit =
            defaultERC20PermitTransfer(address(fromToken()), amount(), 0);

        OtcOrderSettlement.Consideration memory makerConsideration = OtcOrderSettlement.Consideration({
            token: address(fromToken()),
            amount: amount(),
            counterparty: FROM,
            partialFillAllowed: false
        });

        bytes32 makerWitness = keccak256(bytes.concat(CONSIDERATION_TYPEHASH, abi.encode(makerConsideration)));
        bytes memory makerSig = getPermitWitnessTransferSignature(
            makerPermit, address(settler), MAKER_PRIVATE_KEY, OTC_PERMIT2_WITNESS_TYPEHASH, makerWitness, permit2Domain
        );

        bytes memory takerSig = new bytes(0);

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(
                ISettlerActions.SETTLER_OTC_PERMIT2, (FROM, makerPermit, MAKER, makerSig, takerPermit, takerSig)
            )
        );

        IAllowanceHolder _allowanceHolder = allowanceHolder;
        Settler _settler = settler;
        IERC20 _fromToken = fromToken();
        uint256 _amount = amount();
        //_warm_allowanceHolder_slots(address(_fromToken), _amount);

        vm.startPrank(FROM, FROM);
        snapStartName("allowanceHolder_otc");
        //_cold_account_access();

        _allowanceHolder.exec(
            address(_settler),
            address(_fromToken),
            _amount,
            payable(address(_settler)),
            abi.encodeCall(
                _settler.execute,
                (actions, Settler.AllowedSlippage({buyToken: address(0), recipient: address(0), minAmountOut: 0 ether}))
            )
        );
        snapEnd();
    }

    function testAllowanceHolder_otc_proportionalFee() public {
        ISignatureTransfer.PermitTransferFrom memory makerPermit =
            defaultERC20PermitTransfer(address(toToken()), amount(), PERMIT2_MAKER_NONCE);
        ISignatureTransfer.PermitTransferFrom memory takerPermit =
            defaultERC20PermitTransfer(address(fromToken()), amount(), 0);

        OtcOrderSettlement.Consideration memory makerConsideration = OtcOrderSettlement.Consideration({
            token: address(fromToken()),
            amount: amount(),
            counterparty: FROM,
            partialFillAllowed: true
        });

        bytes32 makerWitness = keccak256(bytes.concat(CONSIDERATION_TYPEHASH, abi.encode(makerConsideration)));
        bytes memory makerSig = getPermitWitnessTransferSignature(
            makerPermit, address(settler), MAKER_PRIVATE_KEY, OTC_PERMIT2_WITNESS_TYPEHASH, makerWitness, permit2Domain
        );

        bytes memory takerSig = new bytes(0);

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.PERMIT2_TRANSFER_FROM, (address(settler), takerPermit, takerSig)),
            abi.encodeCall(
                ISettlerActions.BASIC_SELL,
                (
                    address(fromToken()),
                    address(fromToken()),
                    1_000,
                    0x24,
                    abi.encodeCall(fromToken().transfer, (BURN_ADDRESS, 0))
                )
            ),
            abi.encodeCall(
                ISettlerActions.SETTLER_OTC_SELF_FUNDED,
                (FROM, makerPermit, MAKER, makerSig, address(fromToken()), amount())
            )
        );

        IAllowanceHolder _allowanceHolder = allowanceHolder;
        Settler _settler = settler;
        IERC20 _fromToken = fromToken();
        uint256 _amount = amount();
        //_warm_allowanceHolder_slots(address(_fromToken), _amount);

        vm.startPrank(FROM, FROM);
        snapStartName("allowanceHolder_otc_proportionalFee_sellToken");
        //_cold_account_access();

        _allowanceHolder.exec(
            address(_settler),
            address(_fromToken),
            _amount,
            payable(address(_settler)),
            abi.encodeCall(
                _settler.execute,
                (actions, Settler.AllowedSlippage({buyToken: address(0), recipient: address(0), minAmountOut: 0 ether}))
            )
        );
        snapEnd();
    }

    function testAllowanceHolder_otc_fixedFee() public {
        ISignatureTransfer.PermitTransferFrom memory makerPermit =
            defaultERC20PermitTransfer(address(toToken()), amount(), PERMIT2_MAKER_NONCE);
        ISignatureTransfer.PermitTransferFrom memory takerPermit =
            defaultERC20PermitTransfer(address(fromToken()), amount(), 0);

        OtcOrderSettlement.Consideration memory makerConsideration = OtcOrderSettlement.Consideration({
            token: address(fromToken()),
            amount: amount(),
            counterparty: FROM,
            partialFillAllowed: true
        });

        bytes32 makerWitness = keccak256(bytes.concat(CONSIDERATION_TYPEHASH, abi.encode(makerConsideration)));
        bytes memory makerSig = getPermitWitnessTransferSignature(
            makerPermit, address(settler), MAKER_PRIVATE_KEY, OTC_PERMIT2_WITNESS_TYPEHASH, makerWitness, permit2Domain
        );

        bytes memory takerSig = new bytes(0);

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.PERMIT2_TRANSFER_FROM, (address(settler), takerPermit, takerSig)),
            abi.encodeCall(
                ISettlerActions.BASIC_SELL,
                (
                    address(fromToken()),
                    address(0),
                    0,
                    0x00,
                    abi.encodeCall(fromToken().transfer, (BURN_ADDRESS, amount() * 1_000 / 10_000))
                )
            ),
            abi.encodeCall(
                ISettlerActions.SETTLER_OTC_SELF_FUNDED,
                (FROM, makerPermit, MAKER, makerSig, address(fromToken()), amount())
            )
        );

        IAllowanceHolder _allowanceHolder = allowanceHolder;
        Settler _settler = settler;
        IERC20 _fromToken = fromToken();
        uint256 _amount = amount();
        //_warm_allowanceHolder_slots(address(_fromToken), _amount);

        vm.startPrank(FROM, FROM);
        snapStartName("allowanceHolder_otc_fixedFee_sellToken");
        //_cold_account_access();

        _allowanceHolder.exec(
            address(_settler),
            address(_fromToken),
            _amount,
            payable(address(_settler)),
            abi.encodeCall(
                _settler.execute,
                (actions, Settler.AllowedSlippage({buyToken: address(0), recipient: address(0), minAmountOut: 0 ether}))
            )
        );
        snapEnd();
    }

    function testAllowanceHolder_uniswapV2_single_chain() public {
        // |7|6|5|4|3|2|1|0| - bit positions in swapInfo (uint8)
        // |0|0|0|0|0|0|F|Z| - Z: zeroForOne flag, F: sellTokenHasFee flag
        bool sellTokenHasFee = false;
        uint8 swapInfo = (address(fromToken()) < address(toToken()) ? 1 : 0) | (sellTokenHasFee ? 1 : 0) << 1;

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(
                ISettlerActions.PERMIT2_TRANSFER_FROM,
                (
                    uniswapV2Pool(),
                    defaultERC20PermitTransfer(address(fromToken()), amount(), 0 /* nonce */ ),
                    new bytes(0) /* sig (empty) */
                )
            ),
            abi.encodeCall(
                ISettlerActions.UNISWAPV2_SWAP, (FROM, address(fromToken()), uniswapV2Pool(), swapInfo, 0, 0)
            )
        );

        IAllowanceHolder _allowanceHolder = allowanceHolder;
        Settler _settler = settler;
        IERC20 _fromToken = fromToken();
        uint256 _amount = amount();
        _warm_allowanceHolder_slots(address(fromToken()), amount());

        vm.startPrank(FROM); // Do not prank tx.origin, msg.sender != tx.origin
        snapStartName("allowanceHolder_uniswapV2_single_chain");
        _cold_account_access();

        _allowanceHolder.exec(
            address(_settler),
            address(_fromToken),
            _amount,
            payable(address(_settler)),
            abi.encodeCall(
                _settler.execute,
                (actions, Settler.AllowedSlippage({buyToken: address(0), recipient: address(0), minAmountOut: 0 ether}))
            )
        );
        snapEnd();
    }

    /// @dev With a future deployment with EIP1153 these storage slots will be transient
    /// and therefor cost the same as if they were already warm
    /// TODO should we keep this on of have it as a flag if we deploy prior to EIP1153
    function _warm_allowanceHolder_slots(address token, uint256 amount) internal {
        bytes32 allowedSlot = keccak256(abi.encodePacked(address(settler), FROM, token));
        bytes32 allowedValue = bytes32(amount);
        vm.store(address(allowanceHolder), allowedSlot, allowedValue);
    }

    function _cold_account_access() internal {
        // `_warm_allowanceHolder_slots` also warms the whole `AllowanceHolder`
        // account. in order to pretend that we didn't just do that, we do a
        // cold account access inside the metered path. this costs an
        // erroneously-extra 100 gas.
        assembly ("memory-safe") {
            let _pop := call(gas(), 0xdead, 0, 0x00, 0x00, 0x00, 0x00)
        }
    }
}
