// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {AddressDerivation} from "src/utils/AddressDerivation.sol";

import "forge-std/Test.sol";

contract Dummy {}

contract AddressDerivationTest is Test {
    function testEOA(uint256 privKey, uint256 k) public {
        privKey = boundPrivateKey(privKey);
        k = boundPrivateKey(k);
        Vm.Wallet memory parent = vm.createWallet(privKey, "parent");
        Vm.Wallet memory child = vm.createWallet(mulmod(privKey, k, AddressDerivation._SECP256K1_N), "child");
        assertEq(
            parent.addr,
            address(uint160(uint256(keccak256(abi.encodePacked(parent.publicKeyX, parent.publicKeyY))))),
            "sanity check"
        );
        assertEq(AddressDerivation.deriveEOA(parent.publicKeyX, parent.publicKeyY, k), child.addr);
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
