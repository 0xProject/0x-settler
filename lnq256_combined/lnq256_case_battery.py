"""Shared adversarial/random batteries for relaxed lnQ256 bounds work."""

from __future__ import annotations

import random
from typing import Iterable, List


def build_battery(random_cases: int, boundary_cases: int, seed: int) -> List[int]:
    rng = random.Random(seed)
    cases: List[int] = []

    cases.extend(range(1, 10_001))

    for e in range(512):
        p2 = 1 << e
        for d in range(-4, 5):
            x = p2 + d
            if x > 0:
                cases.append(x)

    for e in [4, 8, 16, 32, 64, 128, 255, 256, 257, 383, 511]:
        base = 1 << e
        for j in range(16):
            b = ((16 + j) * base) // 16
            for d in range(-6, 7):
                x = b + d
                if base <= x < (1 << (e + 1)):
                    cases.append(x)

    for _ in range(random_cases):
        bits = rng.randrange(1, 513)
        cases.append(rng.getrandbits(bits - 1) | (1 << (bits - 1)))

    for _ in range(boundary_cases):
        e = rng.randrange(4, 512)
        base = 1 << e
        j = rng.randrange(16)
        b = ((16 + j) * base) // 16
        x = b + rng.randint(-1000, 1000)
        if 0 < x < (1 << (e + 1)) and x >= base:
            cases.append(x)

    seen = set()
    uniq: List[int] = []
    for x in cases:
        if x not in seen:
            uniq.append(x)
            seen.add(x)
    return uniq


def merge_batteries(batteries: Iterable[Iterable[int]]) -> List[int]:
    merged: List[int] = []
    seen = set()
    for battery in batteries:
        for x in battery:
            if x not in seen:
                merged.append(x)
                seen.add(x)
    return merged
