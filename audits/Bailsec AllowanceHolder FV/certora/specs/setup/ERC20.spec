
methods {
    function _.safeTransferFrom(
        address token, address from, address to, uint256 amount
    ) internal => safeTransferFromCVL(token, from, to, amount) expect void;
}

// token => owner => balance
ghost mapping(address => mapping(address => mathint)) ghostBalances;

function safeTransferFromCVL(address token, address from, address to, uint256 amount) {
    require ghostBalances[token][from] >= to_mathint(amount),
        "summary: safeTransferFrom reverts on insufficient balance (Solmate require(success))";
    ghostBalances[token][from] = ghostBalances[token][from] - amount;
    ghostBalances[token][to]   = ghostBalances[token][to]   + amount;
}

