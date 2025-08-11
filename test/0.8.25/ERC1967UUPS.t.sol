// SPDX-License-Identifier: MIT
pragma solidity 0.8.25;

import "@forge-std/Test.sol";

import {ERC1967UUPSProxy} from "src/proxy/ERC1967UUPSProxy.sol";
import {ERC1967UUPSUpgradeable, IERC1967Proxy} from "src/proxy/ERC1967UUPSUpgradeable.sol";
import {IERC165} from "@forge-std/interfaces/IERC165.sol";
import {IOwnable} from "src/interfaces/IOwnable.sol";
import {AbstractOwnable, Ownable} from "src/utils/TwoStepOwnable.sol";
import {Context} from "src/Context.sol";

interface IMock is IOwnable, IERC1967Proxy {}

contract Mock is IMock, ERC1967UUPSUpgradeable, Context, Ownable {
    constructor(uint256 version) ERC1967UUPSUpgradeable(version) {}

    function initialize(address initialOwner) external {
        super._initialize();
        super._setOwner(initialOwner);
    }

    // ugh. Solidity inheritance

    function supportsInterface(bytes4 interfaceId)
        public
        view
        override(IERC165, AbstractOwnable, ERC1967UUPSUpgradeable)
        returns (bool)
    {
        return super.supportsInterface(interfaceId);
    }

    function owner() public view override(IOwnable, AbstractOwnable, ERC1967UUPSUpgradeable) returns (address) {
        return super.owner();
    }

    function implementation() public view override(IERC1967Proxy, ERC1967UUPSUpgradeable) returns (address) {
        return super.implementation();
    }
}

contract OtherMock is Mock {
    constructor(uint256 version) Mock(version) {}

    event Initialized();

    function initialize() external {
        emit Initialized();
        super._initialize();
    }
}

contract BrokenMock is Mock {
    constructor(uint256 version) Mock(version) {}

    function upgrade(address) public payable override(IERC1967Proxy, ERC1967UUPSUpgradeable) onlyOwner returns (bool) {
        return true;
    }
}

contract ERC1967UUPSTest is Test {
    IMock internal mock;

    event Upgraded(address indexed);

    function setUp() external virtual {
        IMock impl = new Mock(1);
        vm.label(address(impl), "Implementation");
        vm.breakpoint("a");
        vm.expectEmit(true, true, true, true, _predict(address(this), 2));
        emit Upgraded(address(impl));
        address proxy = ERC1967UUPSProxy.create(address(impl), abi.encodeCall(Mock.initialize, (address(this))));
        vm.label(proxy, "Proxy");
        mock = IMock(proxy);
        assertEq(mock.version(), "1");
    }

    function _predict(address deployer, uint8 nonce) internal pure returns (address) {
        require(nonce > 0 && nonce < 128);
        return address(uint160(uint256(keccak256(abi.encodePacked(bytes2(0xd694), deployer, bytes1(nonce))))));
    }

    function testAddress() external {
        assertEq(address(mock), _predict(address(this), 2));
    }

    function testImplementation() external {
        assertEq(mock.implementation(), _predict(address(this), 1));
    }

    function testOwner() external {
        assertEq(mock.owner(), address(this));
    }

    function testUpgrade() external {
        IMock newImpl = new Mock(2);
        assertEq(address(newImpl), _predict(address(this), 3));

        vm.prank(address(0xDEAD));
        vm.expectRevert(abi.encodeWithSignature("PermissionDenied()"));
        mock.upgrade(address(newImpl));

        vm.expectEmit(true, true, true, true, address(mock));
        emit Upgraded(address(newImpl));
        mock.upgrade(address(newImpl));

        assertEq(mock.implementation(), address(newImpl));
        assertEq(mock.version(), "2");
    }

    event Initialized();

    function testUpgradeAndCall() external {
        IMock newImpl = new OtherMock(2);
        assertEq(address(newImpl), _predict(address(this), 3));

        bytes memory initializer = abi.encodeCall(OtherMock.initialize, ());

        vm.prank(address(0xDEAD));
        vm.expectRevert(abi.encodeWithSignature("PermissionDenied()"));
        mock.upgradeAndCall(address(newImpl), initializer);

        vm.expectEmit(true, true, true, true, address(mock));
        emit Initialized();
        vm.expectEmit(true, true, true, true, address(mock));
        emit Upgraded(address(newImpl));
        mock.upgradeAndCall(address(newImpl), initializer);

        assertEq(mock.implementation(), address(newImpl));
        assertEq(mock.version(), "2");
    }

    function testUpgradeSkipVersion() external {
        IMock newImpl = new Mock(3);
        assertEq(address(newImpl), _predict(address(this), 3));

        vm.expectEmit(true, true, true, true, address(mock));
        emit Upgraded(address(newImpl));
        mock.upgrade(address(newImpl));

        assertEq(mock.implementation(), address(newImpl));
        assertEq(mock.version(), "3");
    }

    function testBrokenUpgrade() external {
        IMock newImpl = new BrokenMock(2);
        assertEq(address(newImpl), _predict(address(this), 3));

        vm.expectRevert(abi.encodeWithSignature("RollbackFailed(address,address)", mock.implementation(), newImpl));
        mock.upgrade(address(newImpl));
    }

    function testBrokenUpgradeSkipVersion() external {
        IMock newImpl = new OtherMock(3);
        assertEq(address(newImpl), _predict(address(this), 3));

        bytes memory initializer = abi.encodeCall(OtherMock.initialize, ());

        vm.expectRevert(abi.encodeWithSignature("VersionMismatch(uint256,uint256)", 1, 3));
        mock.upgradeAndCall(address(newImpl), initializer);
    }

    function testBrokenVersion() external {
        IMock newImpl = new Mock(1);

        // the revert string has the arguments backwards here because we get
        // infinite recursion. which order we get depends on the context depth
        // and gas limit on entry.
        vm.expectRevert(abi.encodeWithSignature("RollbackFailed(address,address)", mock.implementation(), newImpl));
        mock.upgrade(address(newImpl));
    }

    function testCode() external {
        bytes32 expected = keccak256(
            bytes.concat(
                hex"365f5f375f5f365f7f",
                bytes32(uint256(keccak256("eip1967.proxy.implementation")) - 1),
                hex"545af43d5f5f3e6036573d5ffd5b3d5ff3"
            )
        );
        assertEq(keccak256(address(mock).code), expected);
    }
}
