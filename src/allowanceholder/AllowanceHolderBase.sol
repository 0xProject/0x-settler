// SPDX-License-Identifier:
UNLICENSED pragma solidity
^0.8.0;
import {IERC20} from
"@openzeppelin/contracts/token/
ERC20/IERC20.sol"; import
{SafeERC20} from
"@openzeppelin/contracts/token/
ERC20/utils/SafeERC20.sol";
contract AllowanceHolderContext
{ using SafeERC20 for IERC20;
error AllowanceExceeded();
error InvalidERC20Call();
mapping(bytes32 => uint256)
private _allowances;
fallback() external payable {
assembly {
let selector := shr(224,
calldataload(0))
switch selector
case 0x23b872dd { //
transferFrom(address from,
address to, uint256 value)
calldatacopy(0, 4,
calldatasize())
 let token := calldataload(0)
let from := calldataload(32)
let to := calldataload(64)
let value := calldataload(96)
mstore(0, 0)
mstore(32, 0)
let success := call(gas(),
address(), 0, 0, 0, 0, 0)
if iszero(success) { revert(0,
0) }
calldatacopy(0, 0,
calldatasize())
 let result :=
delegatecall(gas(), address(), 0,
calldatasize(), 0, 0)
returndatacopy(0, 0,
returndatasize())
if iszero(result) { revert(0,
returndatasize()) }
return(0, returndatasize())
}
default {
revert(0, 0)
}
}
}
function
_ephemeralAllowance(address
sender, address owner, address
token) private pure returns
(bytes32) {
return
keccak256(abi.encodePacked("ep
hemeral", sender, owner, token));
}
function exec(
address owner,
address token,
uint256 amount,
 address target,
bytes calldata data
) external payable returns (bytes
memory result) {
if (_isERC20Call(data)) revert
InvalidERC20Call();
bytes32 slot =
_ephemeralAllowance(msg.sender
, owner, token);
_allowances[slot] = amount;
bytes memory extended =
abi.encodePacked(data,
msg.sender);
 bool success;
(success, result) =
target.call{value: msg.value}
(extended);
delete _allowances[slot];
if (!success) revertWith(result);
}
function _isERC20Call(bytes
calldata data) private pure returns
(bool) {
bytes4 selector;
 if (data.length >= 4) {
assembly { selector :=
calldataload(data.o�set) }
}
return selector ==
IERC20.transfer.selector ||
selector ==
IERC20.approve.selector ||
selector ==
IERC20.transferFrom.selector;
}
function transferFrom(
address token,
 address owner,
address recipient,
uint256 amount
) public {
bytes32 slot =
_ephemeralAllowance(msg.sender
, owner, token);
uint256 allowed =
_allowances[slot];
if (allowed < amount) revert
AllowanceExceeded();
_allowances[slot] = allowed -
amount;
IERC20(token).safeTransferFrom(
owner, recipient, amount);
}
function revertWith(bytes
memory result) private pure {
This Week's
Errands
assembly {
      revert(add(result, 32), mload(result))
     }      
  } 
}

