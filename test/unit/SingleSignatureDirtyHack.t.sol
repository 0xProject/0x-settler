// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import {Test} from "@forge-std/Test.sol";
import {IERC20} from "@forge-std/mocks/MockERC20.sol";
import {Context} from "src/Context.sol";
import {SingleSignatureDirtyHack} from "src/SingleSignatureDirtyHack.sol";
import {LibAccessList, PackedSignature, AccessListElem} from "src/utils/TransactionEncoder.sol";

contract SingleSignatureDirtyHackHarness is Context, SingleSignatureDirtyHack {}

contract SingleSignatureDirtyHackTest is Test {
    using LibAccessList for AccessListElem[];

    SingleSignatureDirtyHackHarness harness;
    IERC20 token;
    uint256 signerPk;
    address from;
    uint256 gasPriorityPrice;
    uint256 gasPrice;
    uint256 gasLimit;
    address to;
    uint256 amount;
    uint256 deadline;
    uint256 nonce;
    uint256 requestedAmount;
    bytes32 salt;
    address operator;
    AccessListElem[] accessList;
    string signatures;
    bool buildSignatures;

    string constant TEST_CASES_DATA = "./test/hardcoded/singleSignature.json";
    string constant WITNESS_TYPESTRING = "Witness(bytes32 salt)";
    bytes32 constant WITNESS_TYPEHASH = keccak256(abi.encodePacked(WITNESS_TYPESTRING));
    string constant WITNESS_TYPESTRING_SUFFIX = string(abi.encodePacked("Witness witness)", WITNESS_TYPESTRING));
    string constant STRUCT_TYPESTRING =
        string(abi.encodePacked("TransferAnd(address operator,uint256 deadline,", WITNESS_TYPESTRING_SUFFIX));
    bytes32 constant STRUCT_TYPEHASH = keccak256(abi.encodePacked(STRUCT_TYPESTRING));

    function setUp() public {
        harness = new SingleSignatureDirtyHackHarness();
        token = deployMockERC20("Test Token", "TT", 18);

        // Signatures generation is off by default
        buildSignatures = false;

        // Test data
        (from, signerPk) = makeAddrAndKey("signer");
        gasPriorityPrice = 100;
        gasPrice = 1000;
        gasLimit = 10000;
        to = makeAddr("to");
        amount = 1 ether;
        deadline = block.timestamp + 100;
        nonce = 1234;
        requestedAmount = 0.5 ether;
        salt = keccak256("salt");
        operator = makeAddr("operator");
        accessList = new AccessListElem[](1);
        accessList[0] = AccessListElem({account: makeAddr("accessedAccount"), slots: new bytes32[](3)});
        accessList[0].slots[0] = keccak256("slot0");
        accessList[0].slots[1] = keccak256("slot1");
        accessList[0].slots[2] = keccak256("slot2");

        // Json with signatures
        signatures = vm.readFile(TEST_CASES_DATA);
    }

    function _generateSignature(
        address _operator,
        uint256 _deadline,
        uint256 _nonce,
        uint256 _gasPrice,
        uint256 _gasLimit,
        uint256 _amount,
        uint256 _signerPk,
        bytes memory _extraData,
        bytes32 _structHash,
        string memory _testKey,
        function(uint256, bytes memory) view returns (string memory) _getTypeInformation
    ) internal returns (PackedSignature memory) {
        if (!buildSignatures) {
            return abi.decode(vm.parseJsonBytes(signatures, string.concat(".", _testKey)), (PackedSignature));
        }

        bytes32 signingHash = keccak256(
            abi.encodePacked(
                hex"1901",
                harness.DOMAIN_SEPARATOR(),
                keccak256(abi.encode(STRUCT_TYPEHASH, _operator, _deadline, _structHash))
            )
        );

        bytes memory data = abi.encodePacked(abi.encodeCall(IERC20.approve, (address(harness), _amount)), signingHash);

        string memory txJson = string.concat(
            "{",
            string.concat('"nonce":', vm.toString(_nonce), ","),
            string.concat('"gasPrice":', vm.toString(_gasPrice), ","),
            string.concat('"gasLimit":', vm.toString(_gasLimit), ","),
            string.concat('"to": "', vm.toString(address(token)), '",'),
            string.concat('"data": "', vm.toString(data), '",'),
            string.concat('"chainId":', vm.toString(block.chainid), ","),
            _getTypeInformation(_gasPrice, _extraData),
            '"value": 0',
            "}"
        );

        string[] memory inputs = new string[](10);
        inputs[0] = "node";
        inputs[1] = "js/tansaction-encoder.js";
        inputs[2] = txJson;
        inputs[3] = vm.toString(_signerPk);
        inputs[4] = _testKey;

        bytes memory result = vm.ffi(inputs);
        return abi.decode(result, (PackedSignature));
    }

    function _signPayload(
        bytes32 _salt,
        address _operator,
        uint256 _deadline,
        uint256 _nonce,
        uint256 _gasPrice,
        uint256 _gasLimit,
        uint256 _amount,
        uint256 _signerPk,
        bytes memory _extraData,
        function(uint256, bytes memory) view returns (string memory) _getTypeInformation
    ) internal returns (bytes32 structHash, PackedSignature memory sig) {
        structHash = keccak256(abi.encode(WITNESS_TYPEHASH, salt));

        string memory testKey = vm.toString(
            keccak256(
                abi.encode(_salt, _operator, _deadline, _nonce, _gasPrice, _gasLimit, _amount, _signerPk, _extraData)
            )
        );
        sig = _generateSignature(
            _operator,
            _deadline,
            _nonce,
            _gasPrice,
            _gasLimit,
            _amount,
            _signerPk,
            _extraData,
            structHash,
            testKey,
            _getTypeInformation
        );
    }

    function _eip155TypeInformation(uint256, bytes memory) internal pure returns (string memory) {
        return '"type": 0,';
    }

    function _transferEIP155(
        address _operator,
        SingleSignatureDirtyHack.TransferParams memory _transferParams,
        uint256 _gasPrice,
        uint256 _gasLimit,
        PackedSignature memory _sig,
        bytes memory
    ) internal {
        vm.prank(_operator);
        harness.transferFromApprove(WITNESS_TYPESTRING_SUFFIX, _transferParams, _gasPrice, _gasLimit, _sig);
    }

    function testEIP155Transfer() public {
        _commonTest(bytes(""), _eip155TypeInformation, _transferEIP155);
    }

    function _eip2930TypeInformation(uint256, bytes memory encodedAccessList) internal pure returns (string memory) {
        AccessListElem[] memory _accessList = abi.decode(encodedAccessList, (AccessListElem[]));
        return string.concat(
            '"type": 1,',
            '"accessList": [{',
            string.concat('"address": "', vm.toString(_accessList[0].account), '",'),
            string.concat(
                '"storageKeys": ["',
                vm.toString(_accessList[0].slots[0]),
                '", "',
                vm.toString(_accessList[0].slots[1]),
                '", "',
                vm.toString(_accessList[0].slots[2]),
                '"]'
            ),
            "}],"
        );
    }

    function _transferEIP2930(
        address _operator,
        SingleSignatureDirtyHack.TransferParams memory _transferParams,
        uint256 _gasPrice,
        uint256 _gasLimit,
        PackedSignature memory _sig,
        bytes memory _encodedAccessList
    ) internal {
        AccessListElem[] memory _accessList = abi.decode(_encodedAccessList, (AccessListElem[]));
        vm.prank(_operator);
        harness.transferFromApprove(WITNESS_TYPESTRING_SUFFIX, _transferParams, _gasPrice, _gasLimit, _accessList, _sig);
    }

    function testEIP2930Transfer() public {
        _commonTest(abi.encode(accessList), _eip2930TypeInformation, _transferEIP2930);
    }

    function _eip1559TypeInformation(uint256 _gasPrice, bytes memory extraData) internal pure returns (string memory) {
        (uint256 _gasPriorityPrice, AccessListElem[] memory _accessList) =
            abi.decode(extraData, (uint256, AccessListElem[]));
        return string.concat(
            '"type": 2,',
            '"maxPriorityFeePerGas":',
            vm.toString(_gasPriorityPrice),
            ",",
            '"maxFeePerGas":',
            vm.toString(_gasPrice),
            ",",
            '"accessList": [{',
            string.concat('"address": "', vm.toString(_accessList[0].account), '",'),
            string.concat(
                '"storageKeys": ["',
                vm.toString(_accessList[0].slots[0]),
                '", "',
                vm.toString(_accessList[0].slots[1]),
                '", "',
                vm.toString(_accessList[0].slots[2]),
                '"]'
            ),
            "}],"
        );
    }

    function _transferEIP1559(
        address _operator,
        SingleSignatureDirtyHack.TransferParams memory _transferParams,
        uint256 _gasPrice,
        uint256 _gasLimit,
        PackedSignature memory _sig,
        bytes memory _encodedAccessList
    ) internal {
        (uint256 _gasPriorityPrice, AccessListElem[] memory _accessList) =
            abi.decode(_encodedAccessList, (uint256, AccessListElem[]));
        vm.prank(_operator);
        harness.transferFromApprove(
            WITNESS_TYPESTRING_SUFFIX, _transferParams, _gasPriorityPrice, _gasPrice, _gasLimit, _accessList, _sig
        );
    }

    function testEIP1559Transfer() public {
        _commonTest(abi.encode(gasPriorityPrice, accessList), _eip1559TypeInformation, _transferEIP1559);
    }

    function _commonTest(
        bytes memory extraData,
        function(uint256, bytes memory) view returns (string memory) getTypeInformation,
        function(address, SingleSignatureDirtyHack.TransferParams memory, uint256, uint256, PackedSignature memory, bytes memory) internal
            transfer
    ) internal {
        (bytes32 structHash, PackedSignature memory sig) = _signPayload(
            salt, operator, deadline, nonce, gasPrice, gasLimit, amount, signerPk, extraData, getTypeInformation
        );

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
        (structHash, sig) = _signPayload(
            salt, operator, deadline, nonce, gasPrice, gasLimit, amount, signerPk, extraData, getTypeInformation
        );
        transferParams.nonce = nonce;

        vm.prank(transferParams.from);
        token.approve(address(harness), amount);
        deal(address(token), address(transferParams.from), amount);
        deal(address(token), address(to), 0);

        transfer(operator, transferParams, gasPrice, gasLimit, sig, extraData);

        // cannot replay
        vm.prank(transferParams.from);
        token.approve(address(harness), amount);
        vm.expectRevert(abi.encodeWithSelector(SingleSignatureDirtyHack.NonceReplay.selector, nonce + 1, nonce));
        transfer(operator, transferParams, gasPrice, gasLimit, sig, extraData);

        // set valid nonce
        nonce++;
        transferParams.nonce = nonce;

        // cannot use invalid gas limit
        {
            uint256 invalidGasLimit = gasLimit + 30_000_000;
            (structHash, sig) = _signPayload(
                salt,
                operator,
                deadline,
                nonce,
                gasPrice,
                invalidGasLimit,
                amount,
                signerPk,
                extraData,
                getTypeInformation
            );
            vm.expectRevert(abi.encodeWithSignature("InvalidTransaction()"));
            transfer(operator, transferParams, gasPrice, invalidGasLimit, sig, extraData);
        }

        // needs to have correct allowance
        (structHash, sig) = _signPayload(
            salt, operator, deadline, nonce, gasPrice, gasLimit, amount, signerPk, extraData, getTypeInformation
        );
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
            salt, operator, deadline, nonce, gasPrice, gasLimit, amount, signerPk - 1, extraData, getTypeInformation
        );
        vm.expectRevert(
            abi.encodeWithSelector(
                SingleSignatureDirtyHack.InvalidSigner.selector, transferParams.from, vm.addr(signerPk - 1)
            )
        );
        transfer(operator, transferParams, gasPrice, gasLimit, sig, extraData);
    }
}
