// SPDX-License-Identifier: MIT
pragma solidity 0.8.21;

import "forge-std/Test.sol";

import {ERC1967UUPSProxy} from "src/proxy/ERC1967UUPSProxy.sol";
import {ERC1967UUPSUpgradeable, IERC1967Proxy} from "src/proxy/ERC1967UUPSUpgradeable.sol";
import {IERC165, AbstractOwnable, IOwnable, Ownable} from "src/deployer/TwoStepOwnable.sol";

interface IMock is IOwnable, IERC1967Proxy {}

contract Mock is IMock, ERC1967UUPSUpgradeable, Ownable {
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
}

contract OtherMock is Mock {
    event Initialized();

    function initialize() external {
        emit Initialized();
    }
}

contract BrokenMock is Mock {
    function upgrade(address) public payable override(IERC1967Proxy, ERC1967UUPSUpgradeable) onlyOwner {}
}

contract ERC1967UUPSTest is Test {
    IMock internal mock;

    function setUp() external virtual {
        IMock impl = new Mock();
        vm.label(address(impl), "Implementation");
        address proxy = ERC1967UUPSProxy.create(address(impl), abi.encodeCall(Mock.initialize, (address(this))));
        vm.label(proxy, "Proxy");
        mock = IMock(proxy);
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

    event Upgraded(address indexed);

    function testUpgrade() external {
        IMock newImpl = new Mock();
        assertEq(address(newImpl), _predict(address(this), 3));

        vm.prank(address(0xDEAD));
        vm.expectRevert(abi.encodeWithSignature("PermissionDenied()"));
        mock.upgrade(address(newImpl));

        vm.expectEmit(true, true, true, true, address(mock));
        emit Upgraded(address(newImpl));
        mock.upgrade(address(newImpl));

        assertEq(mock.implementation(), address(newImpl));
    }

    event Initialized();

    function testUpgradeAndCall() external {
        IMock newImpl = new OtherMock();
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
    }

    function testBrokenUpgrade() external {
        IMock newImpl = new BrokenMock();
        assertEq(address(newImpl), _predict(address(this), 3));

        vm.expectRevert(abi.encodeWithSignature("RollbackFailed()"));
        mock.upgrade(address(newImpl));
    }
}
