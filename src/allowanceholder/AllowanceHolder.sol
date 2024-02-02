// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {AllowanceHolderBase} from "./AllowanceHolderBase.sol";

// EVM version is set to shanghai which does not support TLOAD/TSTORE
/*
import {TransientStorage} from "./TransientStorage.sol";

contract AllowanceHolder is TransientStorage, AllowanceHolderBase {}
*/
