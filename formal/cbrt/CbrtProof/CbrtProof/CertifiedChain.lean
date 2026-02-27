/-
  Certified chain: 6 cbrt NR steps with per-octave error tracking.

  Given a certificate octave i with:
    - lo ≤ m ≤ hi (bounds on icbrt(x))
    - seed = cbrt seed for the octave
    - d1..d6 error bounds with d6 ≤ 1

  We prove: run6From x (seedOf i) ≤ m + 1.

  The proof chains:
    Step 1: d1 bound from analytic formula (cbrt_d1_bound)
    Steps 2-6: each step contracts via cbrtStep_upper_of_le + relaxation to lo
-/
import Init
import CbrtProof.FloorBound
import CbrtProof.CbrtCorrect
import CbrtProof.FiniteCert

namespace CbrtCertified

open CbrtCert

-- ============================================================================
-- Monomial normalization helpers
-- ============================================================================

/-- Factor a numeric constant out of a nested product: a * (b * n) = n * (a * b). -/
private theorem mul_factor_out (a b n : Nat) : a * (b * n) = n * (a * b) := by
  rw [show a * (b * n) = (a * b) * n from by rw [← Nat.mul_assoc]]
  rw [Nat.mul_comm]

-- ============================================================================
-- Pure polynomial identities (no subtraction)
-- ============================================================================

/-- d²(d+3s) + 3(d+s)s² = (d+s)³ + 2s³ -/
private theorem poly_id_ge (d s : Nat) :
    d * d * (d + s + 2 * s) + 3 * (d + s) * (s * s)
      = (d + s) * (d + s) * (d + s) + 2 * (s * s * s) := by
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc,
    Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc, Nat.add_left_comm]
  have h1 : d * (d * (s * 2)) = 2 * (d * (d * s)) := by
    rw [show d * (s * 2) = (d * s) * 2 from by rw [← Nat.mul_assoc]]
    rw [show d * ((d * s) * 2) = (d * (d * s)) * 2 from by rw [← Nat.mul_assoc]]
    rw [Nat.mul_comm]
  have h2 : d * (s * (s * 3)) = 3 * (d * (s * s)) := by
    rw [show s * (s * 3) = (s * s) * 3 from by rw [← Nat.mul_assoc]]
    rw [show d * ((s * s) * 3) = (d * (s * s)) * 3 from by rw [← Nat.mul_assoc]]
    rw [Nat.mul_comm]
  have h3 : s * (s * (s * 2)) = 2 * (s * (s * s)) := by
    rw [show s * (s * 2) = (s * s) * 2 from by rw [← Nat.mul_assoc]]
    rw [show s * ((s * s) * 2) = (s * (s * s)) * 2 from by rw [← Nat.mul_assoc]]
    rw [Nat.mul_comm]
  have h4 : s * (s * (s * 3)) = 3 * (s * (s * s)) := by
    rw [show s * (s * 3) = (s * s) * 3 from by rw [← Nat.mul_assoc]]
    rw [show s * ((s * s) * 3) = (s * (s * s)) * 3 from by rw [← Nat.mul_assoc]]
    rw [Nat.mul_comm]
  omega

/-- d²(m+2(d+m)) + 3m(d+m)² = m³ + 2(d+m)³ -/
private theorem poly_id_le (d m : Nat) :
    d * d * (m + 2 * (d + m)) + 3 * m * ((d + m) * (d + m))
      = m * m * m + 2 * ((d + m) * (d + m) * (d + m)) := by
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc,
    Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc, Nat.add_left_comm]
  have h1 : d * (d * (m * 2)) = 2 * (d * (d * m)) := by
    rw [show d * (m * 2) = (d * m) * 2 from by rw [← Nat.mul_assoc]]
    rw [show d * ((d * m) * 2) = (d * (d * m)) * 2 from by rw [← Nat.mul_assoc]]
    rw [Nat.mul_comm]
  have h2 : d * (m * (m * 2)) = 2 * (d * (m * m)) := by
    rw [show m * (m * 2) = (m * m) * 2 from by rw [← Nat.mul_assoc]]
    rw [show d * ((m * m) * 2) = (d * (m * m)) * 2 from by rw [← Nat.mul_assoc]]
    rw [Nat.mul_comm]
  have h3 : d * (d * (d * 2)) = 2 * (d * (d * d)) := by
    rw [show d * (d * 2) = (d * d) * 2 from by rw [← Nat.mul_assoc]]
    rw [show d * ((d * d) * 2) = (d * (d * d)) * 2 from by rw [← Nat.mul_assoc]]
    rw [Nat.mul_comm]
  have h4 : m * (m * (m * 2)) = 2 * (m * (m * m)) := by
    rw [show m * (m * 2) = (m * m) * 2 from by rw [← Nat.mul_assoc]]
    rw [show m * ((m * m) * 2) = (m * (m * m)) * 2 from by rw [← Nat.mul_assoc]]
    rw [Nat.mul_comm]
  have h5 : m * (m * (m * 3)) = 3 * (m * (m * m)) := by
    rw [show m * (m * 3) = (m * m) * 3 from by rw [← Nat.mul_assoc]]
    rw [show m * ((m * m) * 3) = (m * (m * m)) * 3 from by rw [← Nat.mul_assoc]]
    rw [Nat.mul_comm]
  have h6 : d * (m * (m * 3)) = 3 * (d * (m * m)) := by
    rw [show m * (m * 3) = (m * m) * 3 from by rw [← Nat.mul_assoc]]
    rw [show d * ((m * m) * 3) = (d * (m * m)) * 3 from by rw [← Nat.mul_assoc]]
    rw [Nat.mul_comm]
  have h7 : d * (d * (m * 3)) = 3 * (d * (d * m)) := by
    rw [show d * (m * 3) = (d * m) * 3 from by rw [← Nat.mul_assoc]]
    rw [show d * ((d * m) * 3) = (d * (d * m)) * 3 from by rw [← Nat.mul_assoc]]
    rw [Nat.mul_comm]
  omega

-- ============================================================================
-- Step-from-bound: one NR step error bound using lo as denominator
-- ============================================================================

/-- One NR step with certificate denominator.
    If z ∈ [m, m+D] and 2D ≤ m and lo ≤ m, then cbrtStep(x, z) - m ≤ D²/lo + 1.
    Relaxes cbrtStep_upper_of_le from D²/m to D²/lo. -/
theorem step_from_bound
    (x m lo z D : Nat)
    (hm2 : 2 ≤ m)
    (hloPos : 0 < lo)
    (hlo : lo ≤ m)
    (hxhi : x < (m + 1) * (m + 1) * (m + 1))
    (hmz : m ≤ z)
    (hzD : z - m ≤ D)
    (h2D : 2 * D ≤ m) :
    cbrtStep x z - m ≤ nextD lo D := by
  have hzD' : z ≤ m + D := by omega
  have hstep : cbrtStep x z ≤ m + (D * D / m) + 1 :=
    cbrtStep_upper_of_le x m z D hm2 hmz hzD' h2D hxhi
  have hDm : D * D / m ≤ D * D / lo :=
    Nat.div_le_div_left hlo hloPos
  have hle : cbrtStep x z ≤ m + (D * D / lo) + 1 :=
    Nat.le_trans hstep (Nat.add_le_add_right (Nat.add_le_add_left hDm m) 1)
  -- Goal: cbrtStep x z - m ≤ D * D / lo + 1
  -- From hle: cbrtStep x z ≤ m + (D * D / lo) + 1 = (D * D / lo + 1) + m
  -- By Nat.sub_le_of_le_add: cbrtStep x z - m ≤ D * D / lo + 1
  unfold nextD
  exact Nat.sub_le_of_le_add (by omega : cbrtStep x z ≤ (D * D / lo + 1) + m)

-- ============================================================================
-- First-step (d1) bound: analytic formula via cubic identity
-- ============================================================================

/-- Witness identity for m ≥ s:
    (m-s)²(m+2s) + 3ms² = m³+2s³.
    Used to prove AM-GM and the d1 bound. -/
private theorem cubic_witness_ge (m s : Nat) (h : s ≤ m) :
    (m - s) * (m - s) * (m + 2 * s) + 3 * m * (s * s)
      = m * m * m + 2 * (s * s * s) := by
  generalize hd : m - s = d
  have hm : m = d + s := by omega
  rw [hm]
  exact poly_id_ge d s

/-- Witness identity for s > m:
    (s-m)²(m+2s) + 3ms² = m³+2s³. -/
private theorem cubic_witness_le (m s : Nat) (h : m ≤ s) :
    (s - m) * (s - m) * (m + 2 * s) + 3 * m * (s * s)
      = m * m * m + 2 * (s * s * s) := by
  generalize hd : s - m = d
  have hs : s = d + m := by omega
  rw [hs]
  exact poly_id_le d m

/-- First-step error bound for cbrt NR step.
    Uses: 3s²(z₁ - m) ≤ (m-s)²(m+2s) + 3m(m+1) ≤ maxAbs²(hi+2s) + 3hi(hi+1). -/
theorem cbrt_d1_bound
    (x m s lo hi : Nat)
    (hs : 0 < s)
    (hmlo : m * m * m ≤ x)
    (hmhi : x < (m + 1) * (m + 1) * (m + 1))
    (hlo : lo ≤ m)
    (hhi : m ≤ hi) :
    let maxAbs := max (s - lo) (hi - s)
    cbrtStep x s - m ≤ (maxAbs * maxAbs * (hi + 2 * s) + 3 * hi * (hi + 1)) /
      (3 * (s * s)) := by
  simp only
  unfold cbrtStep
  -- Floor bound: m ≤ z₁
  have hmstep : m ≤ (x / (s * s) + 2 * s) / 3 :=
    cbrt_step_floor_bound x s m hs hmlo
  have hss : 0 < s * s := Nat.mul_pos hs hs
  have h3ss : 0 < 3 * (s * s) := by omega
  -- Key bound: 3s²·z₁ ≤ x + 2s³
  -- From: 3·z₁ ≤ ⌊x/s²⌋ + 2s  and  s²·⌊x/s²⌋ ≤ x.
  have h3z1 : 3 * ((x / (s * s) + 2 * s) / 3) ≤ x / (s * s) + 2 * s :=
    Nat.mul_div_le _ 3
  have hfloor : s * s * (x / (s * s)) ≤ x := Nat.mul_div_le x (s * s)
  have h3ssz1 : 3 * (s * s) * ((x / (s * s) + 2 * s) / 3) ≤ x + 2 * (s * s * s) := by
    have hmul : s * s * (3 * ((x / (s * s) + 2 * s) / 3)) ≤
        s * s * (x / (s * s) + 2 * s) :=
      Nat.mul_le_mul_left _ h3z1
    have hexp : s * s * (x / (s * s) + 2 * s) =
        s * s * (x / (s * s)) + s * s * (2 * s) := Nat.mul_add _ _ _
    have hexp2 : s * s * (2 * s) = 2 * (s * s * s) := by
      rw [Nat.mul_comm 2 s, ← Nat.mul_assoc (s * s) s 2, Nat.mul_comm (s * s * s) 2]
    have hcomm : s * s * (3 * ((x / (s * s) + 2 * s) / 3)) =
        3 * (s * s) * ((x / (s * s) + 2 * s) / 3) := by
      rw [← Nat.mul_assoc (s * s) 3, Nat.mul_comm (s * s) 3]
    rw [← hcomm]
    calc s * s * (3 * ((x / (s * s) + 2 * s) / 3))
        ≤ s * s * (x / (s * s) + 2 * s) := hmul
      _ = s * s * (x / (s * s)) + s * s * (2 * s) := hexp
      _ = s * s * (x / (s * s)) + 2 * (s * s * s) := by rw [hexp2]
      _ ≤ x + 2 * (s * s * s) := Nat.add_le_add_right hfloor _
  -- 3s²m ≤ 3s²z₁
  have h3ssm : 3 * (s * s) * m ≤ 3 * (s * s) * ((x / (s * s) + 2 * s) / 3) :=
    Nat.mul_le_mul_left _ hmstep
  -- AM-GM: 3ms² ≤ m³+2s³ ≤ x+2s³
  have ham : 3 * m * (s * s) ≤ x + 2 * (s * s * s) := by
    by_cases hsm : s ≤ m
    · have := cubic_witness_ge m s hsm; omega
    · have := cubic_witness_le m s (by omega); omega
  -- 3s²(z₁-m) ≤ (x+2s³) - 3ms²
  have hsub : 3 * (s * s) * ((x / (s * s) + 2 * s) / 3 - m) ≤
      x + 2 * (s * s * s) - 3 * m * (s * s) := by
    rw [Nat.mul_sub (3 * (s * s)) ((x / (s * s) + 2 * s) / 3) m]
    have hcomm2 : 3 * (s * s) * m = 3 * m * (s * s) := by
      rw [Nat.mul_assoc 3 (s * s) m, Nat.mul_comm (s * s) m, ← Nat.mul_assoc 3 m (s * s)]
    rw [hcomm2]
    exact Nat.sub_le_sub_right h3ssz1 _
  -- x+2s³-3ms² ≤ (m³+3m²+3m)+2s³-3ms²
  have hxup : x ≤ m * m * m + 3 * (m * m) + 3 * m := by
    have : (m + 1) * (m + 1) * (m + 1) = m * m * m + 3 * (m * m) + 3 * m + 1 := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul, Nat.mul_assoc,
        Nat.add_assoc]
      omega
    omega
  -- (m³+3m²+3m)+2s³-3ms² = diff²·(m+2s) + 3m(m+1)
  -- ≤ maxAbs²·(hi+2s) + 3hi(hi+1)
  -- Use Nat.le_div_iff_mul_le to convert goal
  rw [Nat.le_div_iff_mul_le h3ss]
  -- Goal: (z₁-m)·(3s²) ≤ maxAbs²·(hi+2s) + 3hi(hi+1)
  -- Chain through the bounds
  let RHS := max (s - lo) (hi - s) * max (s - lo) (hi - s) * (hi + 2 * s) + 3 * hi * (hi + 1)
  suffices h : 3 * (s * s) * ((x / (s * s) + 2 * s) / 3 - m) ≤ RHS by
    calc ((x / (s * s) + 2 * s) / 3 - m) * (3 * (s * s))
        = 3 * (s * s) * ((x / (s * s) + 2 * s) / 3 - m) := by
          rw [Nat.mul_comm]
      _ ≤ RHS := h
  -- Chain: 3s²(z₁-m) ≤ x+2s³-3ms² ≤ m³+3m²+3m+2s³-3ms² ≤ RHS
  have hstep1 : x + 2 * (s * s * s) - 3 * m * (s * s) ≤
      (m * m * m + 3 * (m * m) + 3 * m) + 2 * (s * s * s) - 3 * m * (s * s) :=
    Nat.sub_le_sub_right (Nat.add_le_add_right hxup _) _
  -- Now bound the cubic difference and the quadratic term
  have hcubic : m * m * m + 2 * (s * s * s) - 3 * m * (s * s) ≤
      max (s - lo) (hi - s) * max (s - lo) (hi - s) * (hi + 2 * s) := by
    by_cases hsm : s ≤ m
    · have hid := cubic_witness_ge m s hsm
      have hident : m * m * m + 2 * (s * s * s) - 3 * m * (s * s) =
          (m - s) * (m - s) * (m + 2 * s) := by omega
      rw [hident]
      have hdiff : m - s ≤ hi - s := Nat.sub_le_sub_right hhi s
      have hdm : m - s ≤ max (s - lo) (hi - s) :=
        Nat.le_trans hdiff (Nat.le_max_right _ _)
      have hm2s : m + 2 * s ≤ hi + 2 * s := Nat.add_le_add_right hhi _
      exact Nat.mul_le_mul (Nat.mul_le_mul hdm hdm) hm2s
    · -- s > m case (¬(s ≤ m) means m < s)
      have hsm' : m ≤ s := by omega
      have hid := cubic_witness_le m s hsm'
      have hident : m * m * m + 2 * (s * s * s) - 3 * m * (s * s) =
          (s - m) * (s - m) * (m + 2 * s) := by omega
      rw [hident]
      have hdiff : s - m ≤ s - lo := Nat.sub_le_sub_left hlo s
      have hdm : s - m ≤ max (s - lo) (hi - s) :=
        Nat.le_trans hdiff (Nat.le_max_left _ _)
      have hm2s : m + 2 * s ≤ hi + 2 * s := Nat.add_le_add_right hhi _
      exact Nat.mul_le_mul (Nat.mul_le_mul hdm hdm) hm2s
  have hquad : 3 * (m * m) + 3 * m ≤ 3 * hi * (hi + 1) := by
    have hmm1 : m * (m + 1) ≤ hi * (hi + 1) :=
      Nat.mul_le_mul hhi (by omega : m + 1 ≤ hi + 1)
    have h3mm : 3 * (m * m) + 3 * m = 3 * (m * (m + 1)) := by
      rw [Nat.mul_add m m 1, Nat.mul_one, Nat.mul_add 3 (m * m) m]
    have h3hh : 3 * hi * (hi + 1) = 3 * (hi * (hi + 1)) := by
      rw [Nat.mul_assoc]
    omega
  -- AM-GM: 3ms² ≤ m³+2s³ (needed for Nat subtraction safety)
  have ham_pure : 3 * m * (s * s) ≤ m * m * m + 2 * (s * s * s) := by
    by_cases hsm : s ≤ m
    · have := cubic_witness_ge m s hsm; omega
    · have := cubic_witness_le m s (by omega); omega
  -- Assemble: (m³+3m²+3m)+2s³-3ms² = (m³+2s³-3ms²)+(3m²+3m) [safe since AM-GM]
  have hassemble : (m * m * m + 3 * (m * m) + 3 * m) + 2 * (s * s * s) - 3 * m * (s * s) ≤
      RHS := by
    -- Rewrite LHS using AM-GM safety and Nat.sub_add_comm
    have hadd : (m * m * m + 3 * (m * m) + 3 * m) + 2 * (s * s * s) =
        (m * m * m + 2 * (s * s * s)) + (3 * (m * m) + 3 * m) := by omega
    rw [hadd, Nat.sub_add_comm ham_pure]
    exact Nat.add_le_add hcubic hquad
  calc 3 * (s * s) * ((x / (s * s) + 2 * s) / 3 - m)
      ≤ x + 2 * (s * s * s) - 3 * m * (s * s) := hsub
    _ ≤ (m * m * m + 3 * (m * m) + 3 * m) + 2 * (s * s * s) - 3 * m * (s * s) := hstep1
    _ ≤ RHS := hassemble

-- ============================================================================
-- Six-step certified chain
-- ============================================================================

/-- Chain 6 steps through the error recurrence, concluding z₆ ≤ m + 1. -/
theorem run6_le_m_plus_one
    (i : Fin 248)
    (x m : Nat)
    (hm2 : 2 ≤ m)
    (hmlo : m * m * m ≤ x)
    (hmhi : x < (m + 1) * (m + 1) * (m + 1))
    (hlo : loOf i ≤ m)
    (hhi : m ≤ hiOf i) :
    run6From x (seedOf i) ≤ m + 1 := by
  -- Name intermediate values using let
  let z1 := cbrtStep x (seedOf i)
  let z2 := cbrtStep x z1
  let z3 := cbrtStep x z2
  let z4 := cbrtStep x z3
  let z5 := cbrtStep x z4
  let z6 := cbrtStep x z5

  have hloPos : 0 < loOf i := lo_pos i
  have hsPos : 0 < seedOf i := seed_pos i

  -- Lower bounds via floor bound
  have hmz1 : m ≤ z1 := cbrt_step_floor_bound x (seedOf i) m hsPos hmlo
  have hz1Pos : 0 < z1 := by omega
  have hmz2 : m ≤ z2 := cbrt_step_floor_bound x z1 m hz1Pos hmlo
  have hz2Pos : 0 < z2 := by omega
  have hmz3 : m ≤ z3 := cbrt_step_floor_bound x z2 m hz2Pos hmlo
  have hz3Pos : 0 < z3 := by omega
  have hmz4 : m ≤ z4 := cbrt_step_floor_bound x z3 m hz3Pos hmlo
  have hz4Pos : 0 < z4 := by omega
  have hmz5 : m ≤ z5 := cbrt_step_floor_bound x z4 m hz4Pos hmlo

  -- Step 1: d1 bound from analytic formula
  have hd1 : z1 - m ≤ d1Of i := by
    have h := cbrt_d1_bound x m (seedOf i) (loOf i) (hiOf i) hsPos hmlo hmhi hlo hhi
    -- h has type with a let-binding for maxAbs; unfold it with simp only
    simp only at h
    -- Now h : cbrtStep x (seedOf i) - m ≤ (max ... * max ... * ... + ...) / (3 * ...)
    show cbrtStep x (seedOf i) - m ≤ d1Of i
    have hd1eq := d1_eq i
    have hmaxeq := maxabs_eq i
    -- Substitute maxabs into d1_eq to match h's RHS
    rw [hmaxeq] at hd1eq
    -- Now hd1eq : d1Of i = (max ... * max ... * ... + ...) / (3 * ...)
    -- Rewrite ← hd1eq to replace the big expression in h with d1Of i
    rw [← hd1eq] at h
    exact h
  have h2d1 : 2 * d1Of i ≤ m := Nat.le_trans (two_d1_le_lo i) hlo

  -- Steps 2-6 via step_from_bound
  have hd2 : z2 - m ≤ d2Of i := by
    have h := step_from_bound x m (loOf i) z1 (d1Of i) hm2 hloPos hlo hmhi hmz1 hd1 h2d1
    show cbrtStep x z1 - m ≤ d2Of i
    unfold d2Of; exact h
  have h2d2 : 2 * d2Of i ≤ m := Nat.le_trans (two_d2_le_lo i) hlo

  have hd3 : z3 - m ≤ d3Of i := by
    have h := step_from_bound x m (loOf i) z2 (d2Of i) hm2 hloPos hlo hmhi hmz2 hd2 h2d2
    show cbrtStep x z2 - m ≤ d3Of i
    unfold d3Of; exact h
  have h2d3 : 2 * d3Of i ≤ m := Nat.le_trans (two_d3_le_lo i) hlo

  have hd4 : z4 - m ≤ d4Of i := by
    have h := step_from_bound x m (loOf i) z3 (d3Of i) hm2 hloPos hlo hmhi hmz3 hd3 h2d3
    show cbrtStep x z3 - m ≤ d4Of i
    unfold d4Of; exact h
  have h2d4 : 2 * d4Of i ≤ m := Nat.le_trans (two_d4_le_lo i) hlo

  have hd5 : z5 - m ≤ d5Of i := by
    have h := step_from_bound x m (loOf i) z4 (d4Of i) hm2 hloPos hlo hmhi hmz4 hd4 h2d4
    show cbrtStep x z4 - m ≤ d5Of i
    unfold d5Of; exact h
  have h2d5 : 2 * d5Of i ≤ m := Nat.le_trans (two_d5_le_lo i) hlo

  have hd6 : z6 - m ≤ d6Of i := by
    have h := step_from_bound x m (loOf i) z5 (d5Of i) hm2 hloPos hlo hmhi hmz5 hd5 h2d5
    show cbrtStep x z5 - m ≤ d6Of i
    unfold d6Of; exact h

  -- Terminal: d6 ≤ 1
  have hd6le1 : z6 - m ≤ 1 := Nat.le_trans hd6 (d6_le_one i)
  have hresult : z6 ≤ m + 1 := by omega
  -- Connect to run6From: unfold and reduce
  show run6From x (seedOf i) ≤ m + 1
  unfold run6From
  exact hresult

end CbrtCertified
