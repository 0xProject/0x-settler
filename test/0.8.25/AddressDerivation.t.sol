// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {AddressDerivation} from "src/utils/AddressDerivation.sol";
import {Panic} from "src/utils/Panic.sol";
import {UnsafeMath} from "src/utils/UnsafeMath.sol";

import "@forge-std/Test.sol";

contract Dummy {}

contract AddressDerivationTest is Test {
    using UnsafeMath for uint256;

    function testEOA() public {
        testEOA(2999, 30049578511147215784808879450296031459793860218934669378072903188292682383360);
    }

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

    function _inverse(uint256 r_, uint256 m) internal pure returns (uint256 t) {
        // extended euclidean algorithm
        uint256 t_ = 1;
        uint256 r = m;
        r_ = r_.unsafeMod(m);
        while (r_ != 0) {
            uint256 q = r.unsafeDiv(r_);
            unchecked {
                (r, r_, t, t_) =
                    (r_, r.unsafeAddMod(m - q.unsafeMulMod(r_, m), m), t_, t.unsafeAddMod(m - q.unsafeMulMod(t_, m), m));
            }
        }
        if (r != 1) {
            Panic.panic(Panic.DIVISION_BY_ZERO);
        }
    }

    function testEOADegenerate(uint256 privKey) public {
        privKey = boundPrivateKey(privKey);
        Vm.Wallet memory parent = vm.createWallet(privKey, "parent");
        uint256 k = _inverse(parent.publicKeyX, AddressDerivation._SECP256K1_N);
        assertEq(mulmod(k, parent.publicKeyX, AddressDerivation._SECP256K1_N), 1);
        Vm.Wallet memory child = vm.createWallet(mulmod(privKey, k, AddressDerivation._SECP256K1_N), "child");
        assertEq(AddressDerivation.deriveEOA(parent.publicKeyX, parent.publicKeyY, k), child.addr);
    }

    function testContract(address deployer, uint64 nonce) public {
        vm.assume(
            deployer > address(0xffff) && deployer != address(this) && deployer != tx.origin && deployer != address(vm)
                && deployer != address(console) && deployer != 0x3fAB184622Dc19b6109349B94811493BF2a45362
                && deployer != 0x4e59b44847b379578588920cA78FbF26c0B4956C
                && deployer != 0x1F95D37F27EA0dEA9C252FC09D5A6eaA97647353
        );
        nonce = uint64(bound(nonce, 0, type(uint64).max - 1));
        vm.setNonceUnsafe(deployer, nonce);
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
