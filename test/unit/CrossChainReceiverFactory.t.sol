// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {IMultiCall, EIP150_MULTICALL_ADDRESS as MULTICALL_ADDRESS} from "src/multicall/MultiCallContext.sol";

import {Test} from "@forge-std/Test.sol";
import {ICrossChainReceiverFactory} from "src/interfaces/ICrossChainReceiverFactory.sol";

contract CrossChainReceiverFactoryTest is Test {
    ICrossChainReceiverFactory internal constant factory =
        ICrossChainReceiverFactory(payable(0x00000000000000304861c3aDfb80dd5ebeC96325));

    IERC20 internal constant WETH = IERC20(0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2);
    bytes32 internal constant salt = 0x0000000000000000000000000000000000000009435af220071616d150499b5f;

    function setUp() public {
        vm.etch(
            address(WETH),
            hex"6060604052600436106100af576000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff16806306fdde03146100b9578063095ea7b31461014757806318160ddd146101a157806323b872dd146101ca5780632e1a7d4d14610243578063313ce5671461026657806370a082311461029557806395d89b41146102e2578063a9059cbb14610370578063d0e30db0146103ca578063dd62ed3e146103d4575b6100b7610440565b005b34156100c457600080fd5b6100cc6104dd565b6040518080602001828103825283818151815260200191508051906020019080838360005b8381101561010c5780820151818401526020810190506100f1565b50505050905090810190601f1680156101395780820380516001836020036101000a031916815260200191505b509250505060405180910390f35b341561015257600080fd5b610187600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803590602001909190505061057b565b604051808215151515815260200191505060405180910390f35b34156101ac57600080fd5b6101b461066d565b6040518082815260200191505060405180910390f35b34156101d557600080fd5b610229600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803590602001909190505061068c565b604051808215151515815260200191505060405180910390f35b341561024e57600080fd5b61026460048080359060200190919050506109d9565b005b341561027157600080fd5b610279610b05565b604051808260ff1660ff16815260200191505060405180910390f35b34156102a057600080fd5b6102cc600480803573ffffffffffffffffffffffffffffffffffffffff16906020019091905050610b18565b6040518082815260200191505060405180910390f35b34156102ed57600080fd5b6102f5610b30565b6040518080602001828103825283818151815260200191508051906020019080838360005b8381101561033557808201518184015260208101905061031a565b50505050905090810190601f1680156103625780820380516001836020036101000a031916815260200191505b509250505060405180910390f35b341561037b57600080fd5b6103b0600480803573ffffffffffffffffffffffffffffffffffffffff16906020019091908035906020019091905050610bce565b604051808215151515815260200191505060405180910390f35b6103d2610440565b005b34156103df57600080fd5b61042a600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803573ffffffffffffffffffffffffffffffffffffffff16906020019091905050610be3565b6040518082815260200191505060405180910390f35b34600360003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825401925050819055503373ffffffffffffffffffffffffffffffffffffffff167fe1fffcc4923d04b559f4d29a8bfc6cda04eb5b0d3c460751c2402c5c5cc9109c346040518082815260200191505060405180910390a2565b60008054600181600116156101000203166002900480601f0160208091040260200160405190810160405280929190818152602001828054600181600116156101000203166002900480156105735780601f1061054857610100808354040283529160200191610573565b820191906000526020600020905b81548152906001019060200180831161055657829003601f168201915b505050505081565b600081600460003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020819055508273ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff167f8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925846040518082815260200191505060405180910390a36001905092915050565b60003073ffffffffffffffffffffffffffffffffffffffff1631905090565b600081600360008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002054101515156106dc57600080fd5b3373ffffffffffffffffffffffffffffffffffffffff168473ffffffffffffffffffffffffffffffffffffffff16141580156107b457507fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600460008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205414155b156108cf5781600460008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020541015151561084457600080fd5b81600460008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825403925050819055505b81600360008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206000828254039250508190555081600360008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825401925050819055508273ffffffffffffffffffffffffffffffffffffffff168473ffffffffffffffffffffffffffffffffffffffff167fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef846040518082815260200191505060405180910390a3600190509392505050565b80600360003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205410151515610a2757600080fd5b80600360003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825403925050819055503373ffffffffffffffffffffffffffffffffffffffff166108fc829081150290604051600060405180830381858888f193505050501515610ab457600080fd5b3373ffffffffffffffffffffffffffffffffffffffff167f7fcf532c15f0a6db0bd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65826040518082815260200191505060405180910390a250565b600260009054906101000a900460ff1681565b60036020528060005260406000206000915090505481565b60018054600181600116156101000203166002900480601f016020809104026020016040519081016040528092919081815260200182805460018160011615610100020316600290048015610bc65780601f10610b9b57610100808354040283529160200191610bc6565b820191906000526020600020905b815481529060010190602001808311610ba957829003601f168201915b505050505081565b6000610bdb33848461068c565b905092915050565b60046020528160005260406000206020528060005260406000206000915091505054815600a165627a7a72305820deb4c2ccab3c2fdca32ab3f46728389c2fe2c165d5fafa07661e4e004f6c344a0029"
        );

        IMultiCall multicall = IMultiCall(payable(MULTICALL_ADDRESS));
        bytes memory multicallInitcode = vm.getCode("MultiCall.sol:MultiCall");
        bytes32 multicallSalt = 0x0000000000000000000000000000000000000031a5e6991d522b26211cf840ce;
        (bool success, bytes memory returndata) =
            0x4e59b44847b379578588920cA78FbF26c0B4956C.call(bytes.concat(multicallSalt, multicallInitcode));
        require(success);
        require(returndata.length == 20);
        require(address(uint160(bytes20(returndata))) == MULTICALL_ADDRESS);

        // In production, this call would be bundled with the `MultiCall`s below, but that requires
        // that it go through a shim that strips the forwarded sender. That's a pain, so it's not
        // done in this test setup.
        vm.prank(0x000000000000F01B1D1c8EEF6c6cF71a0b658Fbc, 0x000000000000F01B1D1c8EEF6c6cF71a0b658Fbc);
        (success, returndata) = 0x4e59b44847b379578588920cA78FbF26c0B4956C.call(
            hex"40d0824c8df4e3642c10f547614c683762a4702daa5ec86bd42ec64291679b44326df01b1d1c8eef6c6cf71a0b658fbc1815601657fe5b7f60143603803560601c6df01b1d1c8eef6c6cf71a0b658fbc14336ccf9e3c5a263d527f621af382fa17f24f1416602e57fe5b3d54604b57583d55803d3d373d34f03d8159526d6045573dfd5b5260203df35b30ff60901b5952604e3df3"
        );
        require(success);
        require(returndata.length == 20);
        address shim = address(uint160(bytes20(returndata)));
        vm.label(shim, "wrapped native address storage shim");
        address wnativeStorage =
            address(uint160(uint256(keccak256(bytes.concat(bytes2(0xd694), bytes20(uint160(shim)), bytes1(0x01))))));
        vm.label(wnativeStorage, "wrapped native address storage");
        vm.prank(0x000000000000F01B1D1c8EEF6c6cF71a0b658Fbc);
        IMultiCall.Call[] memory calls = new IMultiCall.Call[](3);
        calls[0].target = shim;
        calls[0].data = bytes.concat(hex"7f30ff00000000000000000000", bytes20(uint160(address(WETH))), hex"5f52595ff3");
        calls[1].target = shim;
        calls[1].revertPolicy = IMultiCall.RevertPolicy.CONTINUE;
        calls[1].data = hex"00000000";
        calls[2].target = wnativeStorage;
        calls[2].revertPolicy = IMultiCall.RevertPolicy.CONTINUE;
        multicall.multicall(calls, 0);
        require(wnativeStorage.code.length != 0);

        vm.deal(address(this), 2 wei);
        vm.chainId(1);
        (success, returndata) = 0x4e59b44847b379578588920cA78FbF26c0B4956C.call{value: 2 wei}(
            bytes.concat(salt, vm.getCode("CrossChainReceiverFactory.sol"))
        );
        require(success);
        require(returndata.length == 20);
        require(address(uint160(bytes20(returndata))) == address(factory));
        vm.label(address(factory), "CrossChainReceiverFactory");
    }

    function _deployProxyToRoot(bytes32 root, uint256 privateKey, bool setOwner)
        internal
        returns (ICrossChainReceiverFactory proxy, address owner)
    {
        owner = vm.addr(privateKey);
        proxy = factory.deploy(root, setOwner, owner);
        vm.label(address(proxy), "Proxy");
    }

    function _deployProxy(bytes32 action, uint256 privateKey, bool setOwner)
        internal
        returns (ICrossChainReceiverFactory, address)
    {
        bytes32 root = keccak256(abi.encode(action, block.chainid));
        return _deployProxyToRoot(root, privateKey, setOwner);
    }

    function _deployProxy(bytes32 action, uint256 privateKey) internal returns (ICrossChainReceiverFactory, address) {
        return _deployProxy(action, privateKey, true);
    }

    function _deployProxy(bytes32 action) internal returns (ICrossChainReceiverFactory, address) {
        return _deployProxy(action, uint256(keccak256(abi.encode("owner"))));
    }

    function testProxyBytecode() public {
        bytes32 action = keccak256(abi.encode("action"));
        (ICrossChainReceiverFactory proxy, address owner) = _deployProxy(action);

        assertEq(
            address(proxy).code,
            abi.encodePacked(
                hex"3d3d3d3d363d3d37363d6c", uint104(uint160(address(factory))), hex"5af43d3d93803e602357fd5bf3"
            )
        );
    }

    function testSingleAction() public {
        bytes32 action = keccak256(abi.encode("action"));
        (ICrossChainReceiverFactory proxy, address owner) = _deployProxy(action);

        bytes32[] memory proof = new bytes32[](0);
        assertEq(proxy.isValidSignature(action, abi.encode(owner, proof, bytes(""))), bytes4(0x1626ba7e));
    }

    function testMultipleActions() public {
        bytes32 action1 = keccak256(abi.encode("action1"));
        bytes32 action2 = keccak256(abi.encode("action2"));
        bytes32 leaf1 = keccak256(abi.encode(action1, block.chainid));
        bytes32 leaf2 = keccak256(abi.encode(action2, block.chainid));
        bytes32 root;
        if (leaf2 < leaf1) {
            root = keccak256(abi.encodePacked(leaf2, leaf1));
        } else {
            root = keccak256(abi.encodePacked(leaf1, leaf2));
        }

        bytes32[] memory proof = new bytes32[](1);
        proof[0] = leaf1;

        (ICrossChainReceiverFactory proxy, address owner) =
            _deployProxyToRoot(root, uint256(keccak256(abi.encode("owner"))), false);
        assertEq(
            proxy.isValidSignature(action2, abi.encode(owner, proof, bytes(""))), bytes4(0x1626ba7e), "Action2 failed"
        );

        assertEq(
            proxy.isValidSignature(action1, abi.encode(owner, proof, bytes(""))),
            bytes4(0xffffffff),
            "Invalid signature allowed"
        );

        proof[0] = leaf2;
        assertEq(
            proxy.isValidSignature(action1, abi.encode(owner, proof, bytes(""))), bytes4(0x1626ba7e), "Action1 failed"
        );
    }

    function testOwner() public {
        (ICrossChainReceiverFactory proxy, address owner) = _deployProxy(keccak256(abi.encode("action")));

        vm.prank(owner);
        assertEq(proxy.owner(), owner, "Owner not set");
    }

    function testWrap() public {
        uint256 signerKey = uint256(keccak256(abi.encode("signer")));
        bytes32 root = keccak256(abi.encode("root"));
        (ICrossChainReceiverFactory proxy,) = _deployProxy(root, signerKey, false);

        vm.deal(address(proxy), 1 ether);
        assertEq(address(proxy).balance, 1 ether);
        assertEq(WETH.balanceOf(address(proxy)), 0 ether);
        assertEq(WETH.allowance(address(proxy), 0x000000000022D473030F116dDEE9F6B43aC78BA3), 0 ether);

        proxy.approvePermit2(IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE), 0.3 ether);
        assertEq(address(proxy).balance, 0.7 ether);
        assertEq(WETH.balanceOf(address(proxy)), 0.3 ether);
        assertEq(WETH.allowance(address(proxy), 0x000000000022D473030F116dDEE9F6B43aC78BA3), 0.3 ether);

        vm.expectRevert(new bytes(0));
        proxy.approvePermit2(IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE), 0.7 ether + 1 wei);
    }

    function testNestedEIP712Signature() public {
        uint256 ownerKey = uint256(keccak256(abi.encode("owner")));
        (ICrossChainReceiverFactory proxy,) = _deployProxy(keccak256(abi.encode("action")), ownerKey);

        bytes32 testDomainSeparator = keccak256(
            abi.encode(
                keccak256("EIP712Domain(string name,uint256 chainId,address verifyingContract)"),
                keccak256("TestEIP712Name"),
                block.chainid,
                address(this)
            )
        );
        bytes32 structHash =
            keccak256(abi.encode(keccak256("TestData(uint256 a,uint256 b)"), uint256(0x1234), uint256(0x5678)));
        bytes32 eip721Hash = keccak256(bytes.concat(hex"1901", testDomainSeparator, structHash));

        bytes32 signingHash = keccak256(
            bytes.concat(
                hex"1901",
                abi.encode(
                    testDomainSeparator,
                    keccak256(
                        abi.encode(
                            keccak256(
                                "TypedDataSign(TestData contents,string name,uint256 chainId,address verifyingContract)TestData(uint256 a,uint256 b)"
                            ),
                            structHash,
                            keccak256("ZeroExCrossChainReceiver"),
                            block.chainid,
                            address(proxy)
                        )
                    )
                )
            )
        );
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(ownerKey, signingHash);

        assertEq(
            proxy.isValidSignature(
                eip721Hash,
                abi.encodePacked(
                    r,
                    bytes32(uint256(uint8(v) - 27) << 255 | uint256(s)),
                    testDomainSeparator,
                    structHash,
                    "TestData(uint256 a,uint256 b)",
                    uint16(29)
                )
            ),
            bytes4(0x1626ba7e)
        );
    }
}
