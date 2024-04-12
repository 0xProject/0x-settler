// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

interface ICurveV2Pool {
    struct CurveV2PoolData {
        address pool;
        uint256 fromTokenIndex;
        uint256 toTokenIndex;
    }

    function coins(uint256 i) external view returns (address);
    function exchange(uint256 i, uint256 j, uint256 dx, uint256 min_dy) external payable;
    // function exchange(uint256 i, uint256 j, uint256 dx, uint256 min_dy, bool use_eth) external payable;
}

interface ICurveV2SwapRouter {
    function exchange_multiple(
        address[9] memory _route,
        uint256[3][4] memory _swap_params,
        uint256 _amount,
        uint256 _expected
    ) external payable returns (uint256);
    function exchange_multiple(
        address[9] memory _route,
        uint256[3][4] memory _swap_params,
        uint256 _amount,
        uint256 _expected,
        address[4] memory _pools
    ) external payable returns (uint256);
    function exchange_multiple(
        address[9] memory _route,
        uint256[3][4] memory _swap_params,
        uint256 _amount,
        uint256 _expected,
        address[4] memory _pools,
        address _receiver
    ) external payable returns (uint256);
}
