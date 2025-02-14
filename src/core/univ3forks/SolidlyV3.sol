// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

address constant solidlyV3Factory = 0x70Fe4a44EA505cFa3A57b95cF2862D4fd5F0f687;
address constant solidlyV3SonicFactory = 0x777fAca731b17E8847eBF175c94DbE9d81A8f630;
bytes32 constant solidlyV3InitHash = 0xe9b68c5f77858eecac2e651646e208175e9b1359d68d0e14fc69f8c54e5010bf;
uint8 constant solidlyV3ForkId = 3;

interface ISolidlyV3Callback {
    function solidlyV3SwapCallback(int256 amount0Delta, int256 amount1Delta, bytes calldata data) external;
}
