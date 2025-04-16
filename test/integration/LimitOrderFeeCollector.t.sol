// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {Address, MakerTraits, Order, LIMIT_ORDER_PROTOCOL, LimitOrderFeeCollector} from "src/LimitOrderFeeCollector.sol";

import {Test} from "@forge-std/Test.sol";

IERC20 constant WETH = IERC20(0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2);
IERC20 constant USDC = IERC20(0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48);

type TakerTraits is uint256;

interface ILimitOrderProtocol {
    function fillOrderArgs(
        Order calldata order,
        bytes32 r,
        bytes32 vs,
        uint256 amount,
        TakerTraits takerTraits,
        bytes calldata args
    ) external payable returns (uint256 makingAmount, uint256 takingAmount, bytes32 orderHash);

    function fillContractOrderArgs(
        Order calldata order,
        bytes calldata signature,
        uint256 amount,
        TakerTraits takerTraits,
        bytes calldata args
    ) external returns(uint256 makingAmount, uint256 takingAmount, bytes32 orderHash);
}

contract LimitOrderFeeCollectorTest is Test {
    address private constant _TOEHOLD1 = 0x914d7Fec6aaC8cd542e72Bca78B30650d45643d7;

    uint256 internal MAKER_KEY;
    address payable internal MAKER;
    uint256 internal TAKER_KEY;
    address payable internal TAKER;

    LimitOrderFeeCollector internal feeCollector;

    bytes32 internal constant LIMIT_ORDER_PROTOCOL_DOMAIN = keccak256(abi.encode(keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"),
                                                                                                                        keccak256("1inch Aggregation Router"),
                                                                                                                        keccak256("6"),
                                                                                                                        uint256(1),
                                                     LIMIT_ORDER_PROTOCOL));
    bytes32 internal constant LIMIT_ORDER_TYPEHASH = keccak256("Order(uint256 salt,address maker,address receiver,address makerAsset,address takerAsset,uint256 makingAmount,uint256 takingAmount,uint256 makerTraits)");
    ILimitOrderProtocol internal constant LIMIT_ORDER_PROTOCOL_ = ILimitOrderProtocol(LIMIT_ORDER_PROTOCOL);

    function setUp() public {
        vm.createSelectFork(vm.envString("MAINNET_RPC_URL"), 22282373);

        MAKER_KEY = uint256(keccak256("MAKER"));
        MAKER = payable(vm.addr(MAKER_KEY));
        deal(address(USDC), MAKER, 2_000_000 * 1e6);
        vm.prank(MAKER);
        require(USDC.approve(LIMIT_ORDER_PROTOCOL, type(uint256).max));

        deal(address(WETH), address(this), 1_000 * 1e18);
        require(WETH.approve(LIMIT_ORDER_PROTOCOL, type(uint256).max));

        (bool success, bytes memory returndata) = _TOEHOLD1.call(bytes.concat(bytes32(0), type(LimitOrderFeeCollector).creationCode, abi.encode(bytes20(keccak256("git commit")), address(this), WETH)));
        require(success);
        require(returndata.length == 20);
        feeCollector = LimitOrderFeeCollector(payable(address(uint160(bytes20(returndata)))));
    }

    function testAcceptOwnership() public {
        vm.prank(0x8E5DE7118a596E99B0563D3022039c11927f4827);
        feeCollector.acceptOwnership();
    }

    function testEOAUnwrap() public {
        uint256 makingAmount = 20_000 * 1e6;
        uint256 takingAmount = 10 * 1e18;

        bytes memory extension = bytes.concat(bytes28(0), bytes4(uint32(22)), bytes20(uint160(address(feeCollector))), bytes2(uint16(2500)));
        uint160 extensionHash = uint160(uint256(keccak256(extension)));

        Order memory order = Order({
            salt: extensionHash,
            maker: Address.wrap(uint256(uint160(address(MAKER)))),
            receiver: Address.wrap(uint256(uint160(address(feeCollector)))),
            makerAsset: Address.wrap(uint256(uint160(address(USDC)))),
            takerAsset: Address.wrap(uint256(uint160(address(WETH)))),
            makingAmount: makingAmount,
            takingAmount: takingAmount,
            makerTraits: MakerTraits.wrap((1 << 251) | (1 << 249) | (1 << 247))
        });

        TakerTraits takerTraits = TakerTraits.wrap(extension.length << 224);
        
        bytes32 structHash = keccak256(bytes.concat(LIMIT_ORDER_TYPEHASH, abi.encode(order)));
        bytes32 signingHash = keccak256(bytes.concat(bytes2(0x1901), LIMIT_ORDER_PROTOCOL_DOMAIN, structHash));
        (bytes32 r, bytes32 vs) = vm.signCompact(MAKER_KEY, signingHash);

        LIMIT_ORDER_PROTOCOL_.fillOrderArgs(order, r, vs, takingAmount, takerTraits, extension);
    }

    function testContract() public {

    }
}
