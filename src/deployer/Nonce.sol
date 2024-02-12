// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

type Nonce is uint32;

function incr(Nonce a) pure returns (Nonce) {
    return Nonce.wrap(Nonce.unwrap(a) + 1);
}

function gt(Nonce a, Nonce b) pure returns (bool) {
    return Nonce.unwrap(a) > Nonce.unwrap(b);
}

function isNull(Nonce a) pure returns (bool) {
    return Nonce.unwrap(a) == 0;
}

using {gt as >, incr, isNull} for Nonce global;

Nonce constant zero = Nonce.wrap(0);
