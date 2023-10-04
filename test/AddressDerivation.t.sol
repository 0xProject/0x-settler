// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {AddressDerivation} from "src/utils/AddressDerivation.sol";

import "forge-std/Test.sol";

contract Dummy {}

contract AddressDerivationTest is Test {
    function testEOA(uint256 privKey, uint256 k) public {
        privKey = bound(privKey, 1, AddressDerivation._SECP256K1_N - 1);
        k = bound(k, 1, AddressDerivation._SECP256K1_N - 1);
        Vm.Wallet memory parent = vm.createWallet(privKey, "parent");
        Vm.Wallet memory child = vm.createWallet(mulmod(privKey, k, AddressDerivation._SECP256K1_N), "child");
        assertEq(
            parent.addr,
            address(uint160(uint256(keccak256(abi.encodePacked(parent.publicKeyX, parent.publicKeyY))))),
            "sanity check"
        );
        uint8 v = 27 + uint8(parent.publicKeyY & 1);
        bytes32 r = bytes32(parent.publicKeyX);
        bytes32 s = bytes32(mulmod(parent.publicKeyX, k, AddressDerivation._SECP256K1_N));
        assertEq(ecrecover(bytes32(0), v, r, s), child.addr, "hack");
    }

    function testContract(address deployer, uint64 nonce) public {
        vm.assume(
            deployer > address(255) && deployer != address(this) && deployer != tx.origin && deployer != address(vm)
        );
        nonce = uint64(bound(nonce, vm.getNonce(deployer), type(uint64).max - 1));
        if (nonce > vm.getNonce(deployer)) {
            vm.setNonce(deployer, nonce);
        }
        vm.prank(deployer);
        address expected = address(new Dummy());

        assertEq(AddressDerivation.deriveContract(deployer, nonce), expected);
    }

    function testDeterministicContract(address deployer, bytes32 salt) public {
        vm.assume(
            deployer > address(255) && deployer != address(this) && deployer != tx.origin && deployer != address(vm)
        );
        vm.prank(deployer);
        address expected = address(new Dummy{salt: salt}());
        bytes32 initHash = keccak256(type(Dummy).creationCode);
        assertEq(AddressDerivation.deriveDeterministicContract(deployer, salt, initHash), expected);
    }
}
