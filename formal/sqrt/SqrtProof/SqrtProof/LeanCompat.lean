import Init

namespace SqrtCompat

theorem log2_eq_iff {n k : Nat} (h : n ≠ 0) :
    Nat.log2 n = k ↔ 2 ^ k ≤ n ∧ n < 2 ^ (k + 1) := by
  constructor
  · intro hlog
    constructor
    · simpa [hlog] using Nat.log2_self_le h
    · simpa [hlog] using Nat.lt_log2_self (n := n)
  · intro hk
    apply Nat.le_antisymm
    · exact Nat.lt_succ_iff.mp ((Nat.log2_lt h).2 hk.2)
    · exact (Nat.le_log2 h).2 hk.1

end SqrtCompat
