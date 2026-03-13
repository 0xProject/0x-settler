/-
  Karatsuba decomposition algebra for 512-bit square root.

  All theorems use explicit parameters (no `let` bindings in statements)
  to avoid opaqueness issues with Lean 4's `intro` for `let`.
-/
import SqrtProof.SqrtCorrect

-- ============================================================================
-- Helpers
-- ============================================================================

private theorem sq_expand (a b : Nat) :
    (a + b) * (a + b) = a * a + 2 * a * b + b * b := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm b a]
  have : 2 * a * b = a * b + a * b := by rw [Nat.mul_assoc, Nat.two_mul]
  omega

private theorem mul_reassoc (a b : Nat) : a * b * (a * b) = a * a * (b * b) := by
  rw [Nat.mul_assoc, Nat.mul_left_comm b a b, ← Nat.mul_assoc]

private theorem succ_sq (m : Nat) : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by
  have := sq_expand m 1; simp [Nat.mul_one] at this; omega

-- ============================================================================
-- Part 1: Algebraic identity (explicit parameters, no let)
-- ============================================================================

theorem karatsuba_identity
    (x_hi x_lo_hi x_lo_lo r_hi H : Nat)
    (hres : r_hi * r_hi ≤ x_hi) :
    x_hi * (H * H) + x_lo_hi * H + x_lo_lo +
      ((x_hi - r_hi * r_hi) * H + x_lo_hi) / (2 * r_hi) *
      (((x_hi - r_hi * r_hi) * H + x_lo_hi) / (2 * r_hi)) =
    (r_hi * H + ((x_hi - r_hi * r_hi) * H + x_lo_hi) / (2 * r_hi)) *
      (r_hi * H + ((x_hi - r_hi * r_hi) * H + x_lo_hi) / (2 * r_hi)) +
    ((x_hi - r_hi * r_hi) * H + x_lo_hi) % (2 * r_hi) * H + x_lo_lo := by
  -- Both sides equal r_hi^2*(H*H) + n*H + x_lo_lo + q^2
  -- where n = (x_hi - r_hi^2)*H + x_lo_hi
  -- Euclidean division: (2*r_hi) * q + rem = n
  have heuc := Nat.div_add_mod ((x_hi - r_hi * r_hi) * H + x_lo_hi) (2 * r_hi)
  -- Expand square: (r_hi*H + q)^2 = r_hi*H*(r_hi*H) + 2*(r_hi*H)*q + q*q
  have hexp := sq_expand (r_hi * H) (((x_hi - r_hi * r_hi) * H + x_lo_hi) / (2 * r_hi))
  -- r_hi*H*(r_hi*H) = r_hi*r_hi*(H*H)
  have hreassoc := mul_reassoc r_hi H
  -- Step 1: Expand square and reassociate on RHS
  rw [hexp, hreassoc]
  -- Step 2: Factor LHS: x_hi*(H*H) + x_lo_hi*H = r_hi*r_hi*(H*H) + n*H
  have hfact1 : x_hi * (H * H) + x_lo_hi * H =
      r_hi * r_hi * (H * H) + ((x_hi - r_hi * r_hi) * H + x_lo_hi) * H := by
    -- Work from RHS to LHS
    symm
    rw [Nat.add_mul, Nat.mul_assoc (x_hi - r_hi * r_hi) H H,
        ← Nat.add_assoc, ← Nat.add_mul]
    congr 1; congr 1; omega
  rw [hfact1]
  -- Step 3: Show 2*(r_hi*H)*q + rem*H = n*H and substitute back
  -- Helper: 2*(a*b)*c = 2*a*c*b (rearranges to factor out b)
  have h_prod_comm : ∀ a b c : Nat, 2 * (a * b) * c = 2 * a * c * b := by
    intro a b c
    rw [(Nat.mul_assoc 2 a b).symm, Nat.mul_assoc (2 * a) b c,
        Nat.mul_comm b c, (Nat.mul_assoc (2 * a) c b).symm]
  have hfact2 :
      2 * (r_hi * H) * (((x_hi - r_hi * r_hi) * H + x_lo_hi) / (2 * r_hi)) +
      ((x_hi - r_hi * r_hi) * H + x_lo_hi) % (2 * r_hi) * H =
      ((x_hi - r_hi * r_hi) * H + x_lo_hi) * H := by
    rw [h_prod_comm, ← Nat.add_mul]; congr 1
  rw [← hfact2]
  -- Step 4: Both sides have the same atoms, just in different order
  simp only [Nat.add_comm, Nat.add_left_comm]

-- ============================================================================
-- Part 2: Lower bound
-- ============================================================================

theorem rhi_H_le_natSqrt (x_hi x_lo r_hi H : Nat)
    (hr_hi : r_hi * r_hi ≤ x_hi) :
    r_hi * H ≤ natSqrt (x_hi * (H * H) + x_lo) := by
  have hsq : (r_hi * H) * (r_hi * H) ≤ x_hi * (H * H) + x_lo := by
    calc (r_hi * H) * (r_hi * H)
        = r_hi * r_hi * (H * H) := mul_reassoc r_hi H
      _ ≤ x_hi * (H * H) := Nat.mul_le_mul_right _ hr_hi
      _ ≤ x_hi * (H * H) + x_lo := Nat.le_add_right _ _
  suffices h : ¬(natSqrt (x_hi * (H * H) + x_lo) < r_hi * H) by omega
  intro h
  have h1 : natSqrt (x_hi * (H * H) + x_lo) + 1 ≤ r_hi * H := h
  have h2 := Nat.mul_le_mul h1 h1
  have h3 := natSqrt_lt_succ_sq (x_hi * (H * H) + x_lo)
  omega

-- ============================================================================
-- Part 3: Combined bracket (specialized to 512-bit case)
-- ============================================================================

private theorem natSqrt_ge_pow127 (x_hi : Nat) (hlo : 2 ^ 254 ≤ x_hi) :
    2 ^ 127 ≤ natSqrt x_hi := by
  suffices h : ¬(natSqrt x_hi < 2 ^ 127) by omega
  intro h
  have h1 : natSqrt x_hi + 1 ≤ 2 ^ 127 := h
  have h2 := Nat.mul_le_mul h1 h1
  have h3 := natSqrt_lt_succ_sq x_hi
  have h4 : (2 : Nat) ^ 127 * 2 ^ 127 = 2 ^ 254 := by rw [← Nat.pow_add]
  omega

set_option maxRecDepth 4096 in
/-- The Karatsuba bracket for the 512-bit case: natSqrt(x) ≤ r ≤ natSqrt(x) + 1.
    Stated with fully expanded terms to avoid let-binding issues. -/
theorem karatsuba_bracket_512 (x_hi x_lo_hi x_lo_lo : Nat)
    (hxhi_lo : 2 ^ 254 ≤ x_hi)
    (hxlo_hi : x_lo_hi < 2 ^ 128) (hxlo_lo : x_lo_lo < 2 ^ 128) :
    let H : Nat := 2 ^ 128
    let r_hi := natSqrt x_hi
    let q := ((x_hi - r_hi * r_hi) * H + x_lo_hi) / (2 * r_hi)
    let r := r_hi * H + q
    let x := x_hi * (H * H) + x_lo_hi * H + x_lo_lo
    natSqrt x ≤ r ∧ r ≤ natSqrt x + 1 := by
  intro H r_hi q r x
  -- Key natSqrt bounds
  have hs_lo := natSqrt_sq_le x   -- s² ≤ x
  have hs_hi := natSqrt_lt_succ_sq x  -- x < (s+1)²
  have hr_sq_le := natSqrt_sq_le x_hi  -- r_hi² ≤ x_hi
  have hr_sq_hi := natSqrt_lt_succ_sq x_hi  -- x_hi < (r_hi+1)²
  have hr_ge : 2 ^ 127 ≤ r_hi := natSqrt_ge_pow127 x_hi hxhi_lo
  have hr_pos : 0 < r_hi := by omega
  have hd_pos : 0 < 2 * r_hi := by omega
  have hxlo_hi' : x_lo_hi < H := hxlo_hi
  have hxlo_lo' : x_lo_lo < H := hxlo_lo
  -- r_hi * H ≤ natSqrt(x)
  have hlo : r_hi * H ≤ natSqrt x := by
    show r_hi * H ≤ natSqrt (x_hi * (H * H) + x_lo_hi * H + x_lo_lo)
    rw [Nat.add_assoc]
    exact rhi_H_le_natSqrt x_hi (x_lo_hi * H + x_lo_lo) r_hi H hr_sq_le
  -- x_lo_hi*H + x_lo_lo < H*H
  have hxlo_lt : x_lo_hi * H + x_lo_lo < H * H := by
    have := Nat.mul_le_mul_right H (show x_lo_hi + 1 ≤ H from hxlo_hi')
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  -- natSqrt(x) < (r_hi + 1) * H
  have hhi : natSqrt x < (r_hi + 1) * H := by
    suffices hx_lt : x < (r_hi + 1) * H * ((r_hi + 1) * H) by
      suffices h : ¬((r_hi + 1) * H ≤ natSqrt x) by omega
      intro hc; have h2 := Nat.mul_le_mul hc hc; omega
    show x < (r_hi + 1) * H * ((r_hi + 1) * H)
    rw [mul_reassoc]
    have hr_sq_hi' : x_hi < (r_hi + 1) * (r_hi + 1) := hr_sq_hi
    calc x
        < x_hi * (H * H) + H * H := by omega
      _ = (x_hi + 1) * (H * H) := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ (r_hi + 1) * (r_hi + 1) * (H * H) :=
          Nat.mul_le_mul_right _ (by omega)
  -- Key helpers for the bracket proof
  have hrhH := mul_reassoc r_hi H
  have hs_eq : natSqrt x = r_hi * H + (natSqrt x - r_hi * H) :=
    (Nat.add_sub_cancel' hlo).symm
  have hsx := sq_expand (r_hi * H) (natSqrt x - r_hi * H)
  -- s² = r_hi²*H² + 2*(r_hi*H)*e + e² ≤ x
  have h_sq_le : r_hi * r_hi * (H * H) + 2 * (r_hi * H) * (natSqrt x - r_hi * H) +
      (natSqrt x - r_hi * H) * (natSqrt x - r_hi * H) ≤ x := by
    rw [← hrhH, ← hsx, ← hs_eq]; exact hs_lo
  -- (s+1)² = r_hi²*H² + 2*(r_hi*H)*(e+1) + (e+1)² > x
  have hsx1 := sq_expand (r_hi * H) (natSqrt x - r_hi * H + 1)
  have h_sq_hi : x < r_hi * r_hi * (H * H) +
      2 * (r_hi * H) * (natSqrt x - r_hi * H + 1) +
      (natSqrt x - r_hi * H + 1) * (natSqrt x - r_hi * H + 1) := by
    have h_s1 : natSqrt x + 1 = r_hi * H + (natSqrt x - r_hi * H + 1) := by
      rw [← Nat.add_assoc]; congr 1
    rw [← hrhH, ← hsx1, ← h_s1]; exact hs_hi
  -- Product rearrangement: 2*(r_hi*H)*e = 2*r_hi*e*H
  have h2rhe : ∀ e : Nat, 2 * (r_hi * H) * e = 2 * r_hi * e * H := by
    intro e; rw [(Nat.mul_assoc 2 r_hi H).symm, Nat.mul_assoc (2 * r_hi) H e,
        Nat.mul_comm H e, (Nat.mul_assoc (2 * r_hi) e H).symm]
  -- Algebraic identity: x_hi*H² + x_lo_hi*H = r_hi²*H² + n*H
  -- (proved as standalone lemma to avoid 2^128 evaluation during rw)
  have hfact_key : x_hi * (H * H) + x_lo_hi * H =
      r_hi * r_hi * (H * H) + ((x_hi - r_hi * r_hi) * H + x_lo_hi) * H := by
    have h := Nat.add_sub_cancel' hr_sq_le
    -- h : r_hi * r_hi + (x_hi - r_hi * r_hi) = x_hi
    -- RHS = (r_hi² + (x_hi-r_hi²)) * H² + x_lo_hi*H = x_hi*H² + x_lo_hi*H = LHS
    have : x_hi * (H * H) = (r_hi * r_hi + (x_hi - r_hi * r_hi)) * (H * H) := by
      rw [h]
    -- this : x_hi * (H * H) = (r_hi * r_hi + (x_hi - r_hi * r_hi)) * (H * H)
    rw [this, Nat.add_mul, Nat.add_assoc]
    have h3 : ((x_hi - r_hi * r_hi) * H + x_lo_hi) * H =
        (x_hi - r_hi * r_hi) * (H * H) + x_lo_hi * H := by
      rw [Nat.add_mul, Nat.mul_assoc]
    rw [h3]
  have h_decomp : x = r_hi * r_hi * (H * H) +
      ((x_hi - r_hi * r_hi) * H + x_lo_hi) * H + x_lo_lo := by
    show x_hi * (H * H) + x_lo_hi * H + x_lo_lo =
        r_hi * r_hi * (H * H) + ((x_hi - r_hi * r_hi) * H + x_lo_hi) * H + x_lo_lo
    rw [hfact_key]
  -- Lower bound: e ≤ q
  have h_e_le_q : natSqrt x - r_hi * H ≤ q := by
    rw [Nat.le_div_iff_mul_le hd_pos]
    -- Strategy: show e*d*H < (n+1)*H, then divide by H
    suffices h_mul : (natSqrt x - r_hi * H) * (2 * r_hi) * H <
        ((x_hi - r_hi * r_hi) * H + x_lo_hi + 1) * H by
      exact Nat.le_of_lt_succ (Nat.lt_of_mul_lt_mul_right h_mul)
    -- Rearrange LHS: e*d*H = 2*(r_hi*H)*e
    have h_rearr : (natSqrt x - r_hi * H) * (2 * r_hi) * H =
        2 * (r_hi * H) * (natSqrt x - r_hi * H) := by
      rw [Nat.mul_comm (natSqrt x - r_hi * H) (2 * r_hi)]
      exact (h2rhe (natSqrt x - r_hi * H)).symm
    -- 2*(r_hi*H)*e + r_hi²*H² ≤ x (from h_sq_le, dropping e²)
    have h_bound : 2 * (r_hi * H) * (natSqrt x - r_hi * H) +
        r_hi * r_hi * (H * H) ≤ x :=
      calc 2 * (r_hi * H) * (natSqrt x - r_hi * H) + r_hi * r_hi * (H * H)
          = r_hi * r_hi * (H * H) + 2 * (r_hi * H) * (natSqrt x - r_hi * H) :=
            Nat.add_comm _ _
        _ ≤ r_hi * r_hi * (H * H) + 2 * (r_hi * H) * (natSqrt x - r_hi * H) +
            (natSqrt x - r_hi * H) * (natSqrt x - r_hi * H) :=
            Nat.le_add_right _ _
        _ ≤ x := h_sq_le
    -- e*d*H = 2*(r_hi*H)*e < n*H + H = (n+1)*H
    rw [h_rearr, Nat.add_mul, Nat.one_mul]
    -- h_bound + h_decomp + hxlo_lo' close the goal
    omega
  -- Upper bound: q ≤ e + 1
  have h_q_le_e1 : q ≤ natSqrt x - r_hi * H + 1 := by
    show ((x_hi - r_hi * r_hi) * H + x_lo_hi) / (2 * r_hi) ≤
        natSqrt x - r_hi * H + 1
    -- Strategy: show n*H < (e+2)*(2*r_hi)*H, then divide by H
    suffices h_mul : ((x_hi - r_hi * r_hi) * H + x_lo_hi) * H <
        (natSqrt x - r_hi * H + 1 + 1) * (2 * r_hi) * H by
      have h2 := Nat.lt_of_mul_lt_mul_right h_mul
      -- h2 : n < (e+2) * d, so q = n/d < e+2, so q ≤ e+1
      have h3 := (Nat.div_lt_iff_lt_mul hd_pos).mpr h2
      omega
    -- (e+1)² ≤ 2*r_hi*H since e+1 ≤ H ≤ 2*r_hi
    have he_lt_H : natSqrt x - r_hi * H + 1 ≤ H := by omega
    have hH_le_2r : H ≤ 2 * r_hi := by omega
    have h_sq_bound : (natSqrt x - r_hi * H + 1) * (natSqrt x - r_hi * H + 1) ≤
        2 * r_hi * H :=
      calc (natSqrt x - r_hi * H + 1) * (natSqrt x - r_hi * H + 1)
          ≤ (natSqrt x - r_hi * H + 1) * H := Nat.mul_le_mul_left _ he_lt_H
        _ ≤ H * H := Nat.mul_le_mul_right _ he_lt_H
        _ ≤ 2 * r_hi * H := Nat.mul_le_mul_right _ hH_le_2r
    -- Rearrange RHS: (e+2)*(2*r_hi)*H = 2*(r_hi*H)*(e+1) + 2*r_hi*H
    have h_rhs : (natSqrt x - r_hi * H + 1 + 1) * (2 * r_hi) * H =
        2 * (r_hi * H) * (natSqrt x - r_hi * H + 1) + 2 * r_hi * H := by
      have : (natSqrt x - r_hi * H + 1 + 1) * (2 * r_hi) =
          2 * r_hi * (natSqrt x - r_hi * H + 1) + 2 * r_hi := by
        rw [show natSqrt x - r_hi * H + 1 + 1 = (natSqrt x - r_hi * H + 1) + 1 from rfl,
            Nat.add_mul, Nat.one_mul, Nat.mul_comm]
      rw [this, Nat.add_mul, (h2rhe (natSqrt x - r_hi * H + 1)).symm]
    rw [h_rhs]
    -- Goal: n*H < 2*(r_hi*H)*(e+1) + 2*r_hi*H
    -- From h_sq_hi and h_decomp: n*H + x_lo_lo < 2*(r_hi*H)*(e+1) + (e+1)²
    -- And (e+1)² ≤ 2*r_hi*H (h_sq_bound)
    -- So n*H < 2*(r_hi*H)*(e+1) + 2*r_hi*H
    omega
  constructor
  · -- natSqrt x ≤ r = r_hi * H + q
    show natSqrt x ≤ r_hi * H + q; omega
  · -- r = r_hi * H + q ≤ natSqrt x + 1
    show r_hi * H + q ≤ natSqrt x + 1; omega
