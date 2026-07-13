// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {VmSafe} from "@forge-std/Vm.sol";

struct SafeBytecodes {
    bytes factoryCode;
    bytes singletonCode;
    bytes fallbackCode;
    bytes singletonCodeV141;
    bytes fallbackCodeV141;
    bytes multicallCode;
    bytes proxyCode;
    bytes proxyCodeEraVm;
}

function load(SafeBytecodes memory self, VmSafe vm) view {
    self.factoryCode = vm.readFileBinary("script/factory.bin");
    assert(keccak256(self.factoryCode) == 0x337d7f54be11b6ed55fef7b667ea5488db53db8320a05d1146aa4bd169a39a9b);
    self.singletonCode = vm.readFileBinary("script/singleton.bin");
    assert(keccak256(self.singletonCode) == 0x21842597390c4c6e3c1239e434a682b054bd9548eee5e9b1d6a4482731023c0f);
    self.fallbackCode = vm.readFileBinary("script/fallback.bin");
    assert(keccak256(self.fallbackCode) == 0x03e69f7ce809e81687c69b19a7d7cca45b6d551ffdec73d9bb87178476de1abf);
    self.multicallCode = vm.readFileBinary("script/multicall.bin");
    assert(keccak256(self.multicallCode) == 0xa9865ac2d9c7a1591619b188c4d88167b50df6cc0c5327fcbd1c8c75f7c066ad);
    self.proxyCode = vm.readFileBinary("script/proxy.bin");
    assert(keccak256(self.proxyCode) == 0xb89c1b3bdf2cf8827818646bce9a8f6e372885f8c55e5c07acbd307cb133b000);
    self.proxyCodeEraVm = vm.readFileBinary("script/proxy_eravm.bin");
    assert(keccak256(self.proxyCodeEraVm) == 0x3d70c4a51cf0b92f04e5e281833aeece55198933569c08f5d11fcc45c495253e);
}

function loadV141(SafeBytecodes memory self, VmSafe vm) view {
    self.singletonCodeV141 = vm.readFileBinary("script/singleton_v141.bin");
    assert(keccak256(self.singletonCodeV141) == 0xb1f926978a0f44a2c0ec8fe822418ae969bd8c3f18d61e5103100339894f81ff);
    self.fallbackCodeV141 = vm.readFileBinary("script/fallback_v141.bin");
    assert(keccak256(self.fallbackCodeV141) == 0x7c6007a5d711cea8dfd5d91f5940ec29c7f200fe511eb1fc1397b367af3c42f9);
}

using {load, loadV141} for SafeBytecodes global;
