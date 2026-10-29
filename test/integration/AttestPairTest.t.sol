// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {ISettlerActions} from "src/ISettlerActions.sol";
import {IAttestation} from "src/interfaces/IAttestation.sol";

import {SettlerBasePairTest} from "./SettlerBasePairTest.t.sol";

abstract contract AttestPairTest is SettlerBasePairTest {
    bytes32 internal constant ATTEST_METADATA = 0x0123456789abcdef012345670000000008118af9f7385b10f7e214da772b9e3e;

    function _getAttestAction(address taker, uint256 deadline) internal view returns (bytes memory) {
        bytes32 domain = keccak256(
            abi.encode(
                keccak256("EIP712Domain(string name,uint256 chainId,address verifyingContract)"),
                keccak256("0xSettler"),
                block.chainid,
                address(settler)
            )
        );
        bytes32 contents = keccak256(
            abi.encode(
                keccak256("Attestation(address taker,uint256 deadline,bytes12 zid,string appid)"),
                taker,
                deadline,
                bytes12(ATTEST_METADATA),
                keccak256("ch72gsb320000udocl363eofy")
            )
        );
        (uint8 v, bytes32 r, bytes32 s) =
            vm.sign(MAKER_PRIVATE_KEY, keccak256(abi.encodePacked(hex"1901", domain, contents)));
        return abi.encodeCall(ISettlerActions.ATTEST, (deadline, r, bytes32(uint256(s) | uint256(v - 27) << 255)));
    }

    function checkAttestation(address expectedTaker) external view {
        assertEq(msg.sender, address(settler));
        (address taker, bytes12 zid, string memory appid, address authority, uint40 deadline) =
            IAttestation(address(settler)).attestation();
        assertEq(taker, expectedTaker);
        assertEq(zid, bytes12(ATTEST_METADATA));
        assertEq(appid, "ch72gsb320000udocl363eofy");
        assertEq(authority, MAKER);
        assertEq(deadline, block.timestamp);
    }
}
