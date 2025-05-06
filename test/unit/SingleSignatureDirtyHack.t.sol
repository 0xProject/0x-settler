// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import {Test} from "@forge-std/Test.sol";
import {IERC20} from "@forge-std/mocks/MockERC20.sol";
import {LibRLP} from "@solady/utils/LibRLP.sol";

import {Context} from "src/Context.sol";
import {SingleSignatureDirtyHack} from "src/SingleSignatureDirtyHack.sol";
import {LibAccessList, PackedSignature, AccessListElem} from "src/utils/TransactionEncoder.sol";

contract SingleSignatureDirtyHackHarness is Context, SingleSignatureDirtyHack {}

contract SingleSignatureDirtyHackTest is Test {
    using LibRLP for LibRLP.List;
    using LibAccessList for AccessListElem[];

    SingleSignatureDirtyHackHarness harness;
    IERC20 token;

    string constant WITNESS_TYPESTRING = "Witness(bytes32 salt)";
    bytes32 constant WITNESS_TYPEHASH = keccak256(abi.encodePacked(WITNESS_TYPESTRING));
    string constant WITNESS_TYPESTRING_SUFFIX = string(abi.encodePacked("Witness witness)", WITNESS_TYPESTRING));
    string constant STRUCT_TYPESTRING =
        string(abi.encodePacked("TransferAnd(address operator,uint256 deadline,", WITNESS_TYPESTRING_SUFFIX));
    bytes32 constant STRUCT_TYPEHASH = keccak256(abi.encodePacked(STRUCT_TYPESTRING));

    function setUp() public {
        harness = new SingleSignatureDirtyHackHarness();
        token = deployMockERC20("Test Token", "TT", 18);
    }

    function _signPayload(
        bytes32 salt,
        address operator,
        uint256 deadline,
        uint256 nonce,
        uint256 gasPrice,
        uint256 gasLimit,
        uint256 amount,
        uint256 signerPk,
        bytes memory extraData,
        function(uint256, uint256, uint256, address, bytes memory, bytes memory) view returns (bytes32) getPayload
    ) internal view returns (bytes32 structHash, PackedSignature memory sig) {
        structHash = keccak256(abi.encode(WITNESS_TYPEHASH, salt));

        bytes32 signingHash = keccak256(
            abi.encodePacked(
                hex"1901",
                harness.DOMAIN_SEPARATOR(),
                keccak256(abi.encode(STRUCT_TYPEHASH, operator, deadline, structHash))
            )
        );

        bytes memory data = abi.encodePacked(abi.encodeCall(IERC20.approve, (address(harness), amount)), signingHash);

        bytes32 payload = getPayload(nonce, gasPrice, gasLimit, address(token), data, extraData);

        (uint8 v, bytes32 r, bytes32 s) = vm.sign(signerPk, payload);
        sig = PackedSignature({r: r, vs: bytes32(uint256(s) | ((uint256(v) - 27) << 255))});
    }

    function _eip155Payload(
        uint256 nonce,
        uint256 gasPrice,
        uint256 gasLimit,
        address to,
        bytes memory data,
        bytes memory
    ) internal view returns (bytes32) {
        return keccak256(
            LibRLP.p(nonce).p(gasPrice).p(gasLimit).p(to).p(0 wei).p(data).p(block.chainid).p(uint256(0)).p(uint256(0))
                .encode()
        );
    }

    function _transferEIP155(
        address operator,
        SingleSignatureDirtyHack.TransferParams memory transferParams,
        uint256 gasPrice,
        uint256 gasLimit,
        PackedSignature memory sig,
        bytes memory
    ) internal {
        vm.prank(operator);
        harness.transferFrom(WITNESS_TYPESTRING_SUFFIX, transferParams, gasPrice, gasLimit, sig);
    }

    function testEIP155Transfer(
        uint256 signerPk,
        uint256 gasPrice,
        uint256 gasLimit,
        address to,
        uint256 amount,
        uint256 deadline,
        uint256 nonce,
        uint256 requestedAmount,
        bytes32 salt,
        address operator
    ) public {
        _commonTest(
            signerPk,
            gasPrice,
            gasLimit,
            to,
            amount,
            deadline,
            nonce,
            requestedAmount,
            salt,
            operator,
            bytes(""),
            _eip155Payload,
            _transferEIP155
        );
    }

    function _eip2930Payload(
        uint256 nonce,
        uint256 gasPrice,
        uint256 gasLimit,
        address to,
        bytes memory data,
        bytes memory encodedAccessList
    ) internal view returns (bytes32) {
        AccessListElem[] memory accessList = abi.decode(encodedAccessList, (AccessListElem[]));
        return keccak256(
            bytes.concat(
                bytes1(0x01),
                LibRLP.p(block.chainid).p(nonce).p(gasPrice).p(gasLimit).p(to).p(0 wei).p(data).p(accessList.encode())
                    .encode()
            )
        );
    }

    function _transferEIP2930(
        address operator,
        SingleSignatureDirtyHack.TransferParams memory transferParams,
        uint256 gasPrice,
        uint256 gasLimit,
        PackedSignature memory sig,
        bytes memory encodedAccessList
    ) internal {
        AccessListElem[] memory accessList = abi.decode(encodedAccessList, (AccessListElem[]));
        vm.prank(operator);
        harness.transferFrom(WITNESS_TYPESTRING_SUFFIX, transferParams, gasPrice, gasLimit, accessList, sig);
    }

    function testEIP2930Transfer(
        uint256 signerPk,
        uint256 gasPrice,
        uint256 gasLimit,
        address to,
        uint256 amount,
        uint256 deadline,
        uint256 nonce,
        uint256 requestedAmount,
        bytes32 salt,
        address operator,
        address accessedAcount,
        bytes32[3] memory slots
    ) public {
        bytes memory extraData;
        {
            AccessListElem[] memory accessList = new AccessListElem[](1);
            accessList[0] = AccessListElem({account: accessedAcount, slots: new bytes32[](3)});
            accessList[0].slots[0] = slots[0];
            accessList[0].slots[1] = slots[1];
            accessList[0].slots[2] = slots[2];
            extraData = abi.encode(accessList);
        }

        _commonTest(
            signerPk,
            gasPrice,
            gasLimit,
            to,
            amount,
            deadline,
            nonce,
            requestedAmount,
            salt,
            operator,
            extraData,
            _eip2930Payload,
            _transferEIP2930
        );
    }

    function _eip1559Payload(
        uint256 nonce,
        uint256 gasPrice,
        uint256 gasLimit,
        address to,
        bytes memory data,
        bytes memory extraData
    ) internal view returns (bytes32) {
        (uint256 gasPriorityPrice, AccessListElem[] memory accessList) =
            abi.decode(extraData, (uint256, AccessListElem[]));
        return keccak256(
            bytes.concat(
                bytes1(0x02),
                LibRLP.p(block.chainid).p(nonce).p(gasPriorityPrice).p(gasPrice).p(gasLimit).p(to).p(0 wei).p(data).p(
                    accessList.encode()
                ).encode()
            )
        );
    }

    function _transferEIP1559(
        address operator,
        SingleSignatureDirtyHack.TransferParams memory transferParams,
        uint256 gasPrice,
        uint256 gasLimit,
        PackedSignature memory sig,
        bytes memory encodedAccessList
    ) internal {
        (uint256 gasPriorityPrice, AccessListElem[] memory accessList) =
            abi.decode(encodedAccessList, (uint256, AccessListElem[]));
        vm.prank(operator);
        harness.transferFrom(
            WITNESS_TYPESTRING_SUFFIX, transferParams, gasPriorityPrice, gasPrice, gasLimit, accessList, sig
        );
    }

    function testEIP1559Transfer(
        uint256 signerPk,
        uint256 gasPriorityPrice,
        uint256 gasPrice,
        uint256 gasLimit,
        address to,
        uint256 amount,
        uint256 deadline,
        uint256 nonce,
        uint256 requestedAmount,
        bytes32 salt,
        address operator,
        address accessedAcount,
        bytes32[3] memory slots
    ) public {
        bytes memory extraData;
        {
            AccessListElem[] memory accessList = new AccessListElem[](1);
            accessList[0] = AccessListElem({account: accessedAcount, slots: new bytes32[](3)});
            accessList[0].slots[0] = slots[0];
            accessList[0].slots[1] = slots[1];
            accessList[0].slots[2] = slots[2];
            extraData = abi.encode(gasPriorityPrice, accessList);
        }

        _commonTest(
            signerPk,
            gasPrice,
            gasLimit,
            to,
            amount,
            deadline,
            nonce,
            requestedAmount,
            salt,
            operator,
            extraData,
            _eip1559Payload,
            _transferEIP1559
        );
    }

    function _commonTest(
        uint256 signerPk,
        uint256 gasPrice,
        uint256 gasLimit,
        address to,
        uint256 amount,
        uint256 deadline,
        uint256 nonce,
        uint256 requestedAmount,
        bytes32 salt,
        address operator,
        bytes memory extraData,
        function(uint256, uint256, uint256, address, bytes memory, bytes memory) view returns (bytes32) getPayload,
        function(address, SingleSignatureDirtyHack.TransferParams memory, uint256, uint256, PackedSignature memory, bytes memory) internal
            transfer
    ) internal {
        signerPk = bound(signerPk, 2, 115792089237316195423570985008687907852837564279074904382605163141518161494336);
        gasLimit = bound(gasLimit, 0, 30_000_000);
        deadline = bound(deadline, block.timestamp, type(uint256).max - 1);
        nonce = bound(nonce, 1, type(uint64).max - 3);
        amount = bound(amount, 2, type(uint256).max);
        requestedAmount = bound(requestedAmount, 1, amount);

        (bytes32 structHash, PackedSignature memory sig) =
            _signPayload(salt, operator, deadline, nonce, gasPrice, gasLimit, amount, signerPk, extraData, getPayload);

        SingleSignatureDirtyHack.TransferParams memory transferParams = SingleSignatureDirtyHack.TransferParams({
            structHash: structHash,
            token: token,
            from: vm.addr(signerPk),
            to: to,
            amount: amount,
            nonce: nonce,
            deadline: deadline,
            requestedAmount: requestedAmount
        });

        vm.prank(transferParams.from);
        token.approve(address(harness), amount);
        deal(address(token), address(transferParams.from), amount);

        transfer(operator, transferParams, gasPrice, gasLimit, sig, extraData);

        // can use incremental nonce
        nonce++;
        (structHash, sig) =
            _signPayload(salt, operator, deadline, nonce, gasPrice, gasLimit, amount, signerPk, extraData, getPayload);
        transferParams.nonce = nonce;

        vm.prank(transferParams.from);
        token.approve(address(harness), amount);
        deal(address(token), address(transferParams.from), amount);
        deal(address(token), address(to), 0);

        transfer(operator, transferParams, gasPrice, gasLimit, sig, extraData);

        // cannot replay
        vm.prank(transferParams.from);
        token.approve(address(harness), amount);
        vm.expectRevert(abi.encodeWithSelector(SingleSignatureDirtyHack.NonceReplay.selector, nonce, nonce));
        transfer(operator, transferParams, gasPrice, gasLimit, sig, extraData);

        // set valid nonce
        nonce++;
        transferParams.nonce = nonce;

        // cannot use invalid gas limit
        {
            uint256 invalidGasLimit = bound(gasLimit, 30_000_001, type(uint256).max);
            (structHash, sig) = _signPayload(
                salt, operator, deadline, nonce, gasPrice, invalidGasLimit, amount, signerPk, extraData, getPayload
            );
            vm.expectRevert(abi.encodeWithSignature("InvalidTransaction()"));
            transfer(operator, transferParams, gasPrice, invalidGasLimit, sig, extraData);
        }

        // needs to have correct allowance
        (structHash, sig) =
            _signPayload(salt, operator, deadline, nonce, gasPrice, gasLimit, amount, signerPk, extraData, getPayload);
        vm.prank(transferParams.from);
        token.approve(address(harness), amount - 1);
        vm.expectRevert(abi.encodeWithSelector(SingleSignatureDirtyHack.InvalidAllowance.selector, amount, amount - 1));
        transfer(operator, transferParams, gasPrice, gasLimit, sig, extraData);
        // set correct allowance
        vm.prank(transferParams.from);
        token.approve(address(harness), amount);

        // needs to have assets to transfer
        deal(address(token), address(transferParams.from), requestedAmount - 1);
        vm.expectRevert("ERC20: subtraction underflow");
        transfer(operator, transferParams, gasPrice, gasLimit, sig, extraData);

        // signature cannot be expired
        vm.warp(deadline + 1);

        vm.expectRevert(abi.encodeWithSelector(SingleSignatureDirtyHack.SignatureExpired.selector, deadline));
        transfer(operator, transferParams, gasPrice, gasLimit, sig, extraData);
        // set valid timestamp
        vm.warp(deadline);

        // needs to be a correct signature
        {
            PackedSignature memory badSig = PackedSignature({r: bytes32(uint256(0)), vs: bytes32(0)});
            vm.expectRevert(abi.encodeWithSignature("InvalidTransaction()"));
            transfer(operator, transferParams, gasPrice, gasLimit, badSig, extraData);
        }

        // needs to be signed by the correct signer
        (structHash, sig) = _signPayload(
            salt, operator, deadline, nonce, gasPrice, gasLimit, amount, signerPk - 1, extraData, getPayload
        );
        vm.expectRevert(
            abi.encodeWithSelector(
                SingleSignatureDirtyHack.InvalidSigner.selector, transferParams.from, vm.addr(signerPk - 1)
            )
        );
        transfer(operator, transferParams, gasPrice, gasLimit, sig, extraData);
    }
}
