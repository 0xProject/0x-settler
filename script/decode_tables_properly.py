#!/usr/bin/env python3
"""
Properly decode the lookup tables for sqrt.
The key insight is the XOR operation to select tables.
"""

def decode_table_properly(table_hi, table_lo):
    """Decode the 48 10-bit entries from the lookup tables."""
    seeds = []

    for i in range(16, 64):
        # c = 1 if i > 39 else 0
        c = 1 if i > 39 else 0

        # The assembly code does:
        # let table := xor(table_hi, mul(xor(table_lo, table_hi), c))
        # When c=0: table = xor(table_hi, 0) = table_hi
        # When c=1: table = xor(table_hi, xor(table_lo, table_hi)) = table_lo

        # So counterintuitively:
        # When i <= 39 (c=0), we use table_hi
        # When i > 39 (c=1), we use table_lo

        if c == 0:
            table = table_hi
        else:
            table = table_lo

        # shift = 0x186 + 0x0a * (0x18 * c - i)
        # 0x186 = 390, 0x0a = 10, 0x18 = 24
        shift = 390 + 10 * (24 * c - i)

        # Extract 10-bit seed
        seed = (table >> shift) & 0x3ff
        seeds.append((i, seed))

    return seeds

# Original tables (from git)
original_hi = 0xb26b4a8690a027198e559263e8ce2887e15832047f1f47b5e677dd974dcd
original_lo = 0x71dc26f1b76c9ad6a5a46819c661946418c621856057e5ed775d1715b96b

# Modified tables (your changes)
modified_hi = 0xb26b4a868f9fa6f9825391e3b8c22586e12826017e5f17a9e3771d573dc9
modified_lo = 0x70dbe6e5b36b9aa695a1671986519063188615815f97a5dd745c56e5ad68

print("Properly decoded lookup table entries:")
print("(Note: c=0 uses table_hi, c=1 uses table_lo)")
print("\nBucket | Original | Modified | Difference")
print("-" * 45)

original_seeds = decode_table_properly(original_hi, original_lo)
modified_seeds = decode_table_properly(modified_hi, modified_lo)

for (i, orig), (_, mod) in zip(original_seeds, modified_seeds):
    diff = mod - orig
    marker = " <-- BUCKET 44 (FAILING)" if i == 44 else ""
    c_val = "c=1" if i > 39 else "c=0"
    if diff != 0:
        print(f"  {i:2d}   |   {orig:3d}    |   {mod:3d}    |    {diff:+3d}  {c_val}{marker}")
    else:
        print(f"  {i:2d}   |   {orig:3d}    |   {mod:3d}    |     0   {c_val}{marker}")

print("\nBucket 44 analysis:")
orig_44 = next(seed for i, seed in original_seeds if i == 44)
mod_44 = next(seed for i, seed in modified_seeds if i == 44)
print(f"Original seed for bucket 44: {orig_44}")
print(f"Modified seed for bucket 44: {mod_44}")
print(f"Change: {mod_44 - orig_44}")

# Check monotonicity
print("\nMonotonicity check (seeds should decrease as i increases):")
is_monotonic_orig = all(s1[1] >= s2[1] for s1, s2 in zip(original_seeds[:-1], original_seeds[1:]))
is_monotonic_mod = all(s1[1] >= s2[1] for s1, s2 in zip(modified_seeds[:-1], modified_seeds[1:]))
print(f"Original table monotonic: {is_monotonic_orig}")
print(f"Modified table monotonic: {is_monotonic_mod}")

# Show specific examples
print("\nSample seeds to verify monotonic decreasing:")
for i in [38, 39, 40, 41, 43, 44, 45]:
    seed = next(s for idx, s in modified_seeds if idx == i)
    c_val = "table_lo" if i > 39 else "table_hi"
    print(f"  Bucket {i:2d}: {seed:3d} (using {c_val})")

# Debug bucket 44 specifically
print("\nDebug bucket 44 extraction:")
i = 44
c = 1  # since 44 > 39
table = modified_lo  # since c=1 means we use table_lo
shift = 390 + 10 * (24 * 1 - 44)
shift = 390 + 10 * (-20)
shift = 390 - 200
shift = 190
seed = (table >> shift) & 0x3ff
print(f"For i=44: c={c}, using table_lo")
print(f"Shift calculation: 390 + 10*(24*1 - 44) = 390 + 10*(-20) = {shift}")
print(f"Extracted seed: {seed}")
print(f"This matches the debug output: {seed == 430}")