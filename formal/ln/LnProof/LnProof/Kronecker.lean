import LnProof.ShiftCert

/-!
# Polynomial identity testing by Kronecker evaluation

Two integer polynomials with ℓ1-norm below half of `2^B` agree everywhere
as soon as they agree at the single point `2^B`: the evaluation is the
balanced radix-`2^B` digit string of the coefficient list, which is
unique. This turns the certificate-vs-literal equalities — whose direct
list-equality decides force the whole construction through the kernel's
per-coefficient evaluation overhead — into one closed integer-arithmetic
comparison plus a symbolic ℓ1 bound.
-/

namespace LnPoly

/-- ℓ1 norm of the coefficient list. -/
def polyL1 : List Int → Nat
  | [] => 0
  | c :: cs => c.natAbs + polyL1 cs

theorem pow2_cast (B : Nat) : ((2 : Int) ^ B) = ((2 ^ B : Nat) : Int) := by
  rw [Int.natCast_pow]
  rfl

/-- A multiple of `2^B` strictly inside `(-2^B, 2^B)` is zero. -/
theorem eq_zero_of_mul_pow {B : Nat} {d k : Int} (hd : d = 2 ^ B * k)
    (h1 : -(2 ^ B) < d) (h2 : d < 2 ^ B) : d = 0 ∧ k = 0 := by
  have hP : (0 : Int) < 2 ^ B := by
    have e : ((2 : Int) ^ B) = ((2 ^ B : Nat) : Int) := by
      rw [Int.natCast_pow]
      rfl
    have h2 : 0 < 2 ^ B := Nat.pow_pos (by omega)
    omega
  rcases Int.lt_or_le k 0 with hk | hk
  · exfalso
    have h1k : k ≤ -1 := by omega
    have := mul_le_mul_left_nonneg h1k (by omega : (0 : Int) ≤ 2 ^ B)
    have e : (2 : Int) ^ B * (-1) = -(2 ^ B) := by
      rw [Int.mul_neg, Int.mul_one]
    omega
  rcases Int.lt_or_le 0 k with hk2 | hk2
  · exfalso
    have h1k : 1 ≤ k := by omega
    have := mul_le_mul_left_nonneg h1k (by omega : (0 : Int) ≤ 2 ^ B)
    have e : (2 : Int) ^ B * 1 = 2 ^ B := Int.mul_one _
    omega
  · have hk0 : k = 0 := by omega
    subst hk0
    rw [Int.mul_zero] at hd
    exact ⟨hd, rfl⟩

/-- Polynomials with small ℓ1 norm that agree at `2^B` agree everywhere. -/
theorem evalPoly_ext {B : Nat} : ∀ (p q : List Int),
    polyL1 p * 2 < 2 ^ B → polyL1 q * 2 < 2 ^ B →
    evalPoly p ((2 : Int) ^ B) = evalPoly q ((2 : Int) ^ B) →
    ∀ x : Int, evalPoly p x = evalPoly q x := by
  intro p
  induction p with
  | nil =>
    intro q
    induction q with
    | nil => intro _ _ _ _; rfl
    | cons b q' ihq =>
      intro hp hq he x
      -- 0 = b + 2^B e' forces b = 0 and e' = 0
      show evalPoly ([] : List Int) x = b + x * evalPoly q' x
      have he' : (0 : Int) = b + 2 ^ B * evalPoly q' ((2 : Int) ^ B) := he
      simp only [polyL1] at hq
      have hb : b.natAbs * 2 < 2 ^ B ∧ polyL1 q' * 2 < 2 ^ B := by omega
      have hbI : -(2 ^ B : Int) < b ∧ (b : Int) < 2 ^ B := by
        rw [pow2_cast B]
        omega
      obtain ⟨hb0, hk0⟩ := eq_zero_of_mul_pow (B := B) (d := -b)
        (k := evalPoly q' ((2 : Int) ^ B)) (by omega) (by omega) (by omega)
      have htail := ihq hp hb.2 (by
        show (0 : Int) = evalPoly q' ((2 : Int) ^ B)
        omega) x
      show (0 : Int) = b + x * evalPoly q' x
      have : evalPoly ([] : List Int) x = (0 : Int) := rfl
      rw [this] at htail
      rw [← htail]
      omega
  | cons a p' ihp =>
    intro q
    match q with
    | [] =>
      intro hp hq he x
      have he' : a + 2 ^ B * evalPoly p' ((2 : Int) ^ B) = (0 : Int) := he
      simp only [polyL1] at hp
      have ha : a.natAbs * 2 < 2 ^ B ∧ polyL1 p' * 2 < 2 ^ B := by omega
      have haI : -(2 ^ B : Int) < a ∧ (a : Int) < 2 ^ B := by
        rw [pow2_cast B]
        omega
      obtain ⟨ha0, hk0⟩ := eq_zero_of_mul_pow (B := B) (d := -a)
        (k := evalPoly p' ((2 : Int) ^ B)) (by omega) (by omega) (by omega)
      have htail := ihp [] ha.2 hq (by
        show evalPoly p' ((2 : Int) ^ B) = (0 : Int)
        omega) x
      show a + x * evalPoly p' x = (0 : Int)
      have h0 : evalPoly ([] : List Int) x = (0 : Int) := rfl
      rw [h0] at htail
      rw [htail]
      omega
    | b :: q' =>
      intro hp hq he x
      have he' : a + 2 ^ B * evalPoly p' ((2 : Int) ^ B) =
          b + 2 ^ B * evalPoly q' ((2 : Int) ^ B) := he
      simp only [polyL1] at hp hq
      have hb : a.natAbs * 2 < 2 ^ B ∧ polyL1 p' * 2 < 2 ^ B ∧
          b.natAbs * 2 < 2 ^ B ∧ polyL1 q' * 2 < 2 ^ B := by omega
      have habI : -(2 ^ B : Int) < a - b ∧ (a - b : Int) < 2 ^ B := by
        rw [pow2_cast B]
        omega
      have hd : a - b = 2 ^ B * (evalPoly q' ((2 : Int) ^ B) -
          evalPoly p' ((2 : Int) ^ B)) := by
        have e := Int.mul_sub ((2 : Int) ^ B) (evalPoly q' ((2 : Int) ^ B))
          (evalPoly p' ((2 : Int) ^ B))
        generalize hE1 : (2 : Int) ^ B * evalPoly p' ((2 : Int) ^ B) = E1 at he' e
        generalize hE2 : (2 : Int) ^ B * evalPoly q' ((2 : Int) ^ B) = E2 at he' e
        omega
      obtain ⟨hab0, hk0⟩ := eq_zero_of_mul_pow (B := B) hd habI.1 habI.2
      have htail := ihp q' hb.2.1 hb.2.2.2 (by omega) x
      show a + x * evalPoly p' x = b + x * evalPoly q' x
      rw [htail]
      omega

/-! ## ℓ1 bounds through the polynomial operations -/

theorem polyL1_polyAdd : ∀ (p q : List Int), polyL1 (polyAdd p q) ≤ polyL1 p + polyL1 q := by
  intro p
  induction p with
  | nil =>
    intro q
    show polyL1 q ≤ polyL1 ([] : List Int) + polyL1 q
    simp only [polyL1]
    omega
  | cons a p ih =>
    intro q
    match q with
    | [] =>
      show polyL1 (a :: p) ≤ polyL1 (a :: p) + polyL1 ([] : List Int)
      simp only [polyL1]
      omega
    | b :: q =>
      show (a + b).natAbs + polyL1 (polyAdd p q) ≤
        (a.natAbs + polyL1 p) + (b.natAbs + polyL1 q)
      have h1 := ih q
      have h2 := Int.natAbs_add_le a b
      omega

theorem polyL1_polyScale (a : Int) : ∀ (p : List Int),
    polyL1 (polyScale a p) ≤ a.natAbs * polyL1 p := by
  intro p
  induction p with
  | nil => exact Nat.le_refl _
  | cons c cs ih =>
    show (a * c).natAbs + polyL1 (polyScale a cs) ≤ a.natAbs * (c.natAbs + polyL1 cs)
    rw [Int.natAbs_mul]
    have hd : a.natAbs * (c.natAbs + polyL1 cs) =
        a.natAbs * c.natAbs + a.natAbs * polyL1 cs := Nat.mul_add _ _ _
    generalize hg1 : a.natAbs * c.natAbs = X at *
    generalize hg2 : a.natAbs * polyL1 cs = Y at *
    omega

theorem polyL1_polyMulX (p : List Int) : polyL1 (polyMulX p) = polyL1 p := by
  show (0 : Int).natAbs + polyL1 p = polyL1 p
  omega

theorem polyL1_polyNeg : ∀ (p : List Int), polyL1 (polyNeg p) = polyL1 p := by
  intro p
  induction p with
  | nil => rfl
  | cons c cs ih =>
    show (-c).natAbs + polyL1 (polyNeg cs) = c.natAbs + polyL1 cs
    rw [Int.natAbs_neg, ih]

theorem polyL1_polyMul : ∀ (p q : List Int), polyL1 (polyMul p q) ≤ polyL1 p * polyL1 q := by
  intro p
  induction p with
  | nil =>
    intro q
    show polyL1 ([] : List Int) ≤ polyL1 ([] : List Int) * polyL1 q
    simp only [polyL1]
    omega
  | cons a p ih =>
    intro q
    show polyL1 (polyAdd (polyScale a q) (polyMulX (polyMul p q))) ≤
      (a.natAbs + polyL1 p) * polyL1 q
    have h1 := polyL1_polyAdd (polyScale a q) (polyMulX (polyMul p q))
    have h2 := polyL1_polyScale a q
    have h3 := polyL1_polyMulX (polyMul p q)
    have h4 := ih q
    have hd : (a.natAbs + polyL1 p) * polyL1 q =
        a.natAbs * polyL1 q + polyL1 p * polyL1 q := Nat.add_mul _ _ _
    generalize hg1 : a.natAbs * polyL1 q = X at *
    generalize hg2 : polyL1 p * polyL1 q = Y at *
    omega

theorem polyL1_polyPow (p : List Int) : ∀ (k : Nat),
    polyL1 (polyPow p k) ≤ polyL1 p ^ k := by
  intro k
  induction k with
  | zero =>
    show (1 : Int).natAbs + polyL1 ([] : List Int) ≤ 1
    decide
  | succ n ih =>
    show polyL1 (polyMul p (polyPow p n)) ≤ polyL1 p ^ (n + 1)
    have h1 := polyL1_polyMul p (polyPow p n)
    have h2 : polyL1 p ^ (n + 1) = polyL1 p ^ n * polyL1 p := Nat.pow_succ _ _
    have h3 : polyL1 p * polyL1 (polyPow p n) ≤ polyL1 p * polyL1 p ^ n :=
      Nat.mul_le_mul_left _ ih
    have h4 : polyL1 p * polyL1 p ^ n = polyL1 p ^ n * polyL1 p := Nat.mul_comm _ _
    generalize hg1 : polyL1 p * polyL1 (polyPow p n) = X at *
    generalize hg2 : polyL1 p * polyL1 p ^ n = Y at *
    generalize hg3 : polyL1 p ^ n * polyL1 p = Z at *
    omega

theorem polyL1_expPolyNum (tn td : List Int) : ∀ (k : Nat),
    polyL1 (expPolyNum tn td k) ≤ LnExp.expNum k (polyL1 tn) (polyL1 td) := by
  intro k
  induction k with
  | zero =>
    show (1 : Int).natAbs + polyL1 ([] : List Int) ≤ 1
    decide
  | succ n ih =>
    show polyL1 (polyAdd (polyScale ((n : Int) + 1) (polyMul td (expPolyNum tn td n)))
      (polyPow tn (n + 1))) ≤
      (n + 1) * polyL1 td * LnExp.expNum n (polyL1 tn) (polyL1 td) +
        polyL1 tn ^ (n + 1)
    have h1 := polyL1_polyAdd (polyScale ((n : Int) + 1)
      (polyMul td (expPolyNum tn td n))) (polyPow tn (n + 1))
    have h2 := polyL1_polyScale ((n : Int) + 1) (polyMul td (expPolyNum tn td n))
    have h3 := polyL1_polyMul td (expPolyNum tn td n)
    have h4 := polyL1_polyPow tn (n + 1)
    have hna : ((n : Int) + 1).natAbs = n + 1 := by omega
    rw [hna] at h2
    have h5 : (n + 1) * polyL1 (polyMul td (expPolyNum tn td n)) ≤
        (n + 1) * (polyL1 td * polyL1 (expPolyNum tn td n)) :=
      Nat.mul_le_mul_left _ h3
    have h6 : polyL1 td * polyL1 (expPolyNum tn td n) ≤
        polyL1 td * LnExp.expNum n (polyL1 tn) (polyL1 td) :=
      Nat.mul_le_mul_left _ ih
    have h7 : (n + 1) * (polyL1 td * polyL1 (expPolyNum tn td n)) ≤
        (n + 1) * (polyL1 td * LnExp.expNum n (polyL1 tn) (polyL1 td)) :=
      Nat.mul_le_mul_left _ h6
    have h8 : (n + 1) * (polyL1 td * LnExp.expNum n (polyL1 tn) (polyL1 td)) =
        (n + 1) * polyL1 td * LnExp.expNum n (polyL1 tn) (polyL1 td) :=
      (Nat.mul_assoc _ _ _).symm
    generalize hg1 : polyL1 (polyScale ((n : Int) + 1)
      (polyMul td (expPolyNum tn td n))) = A at *
    generalize hg2 : (n + 1) * polyL1 (polyMul td (expPolyNum tn td n)) = C at *
    generalize hg3 : (n + 1) * (polyL1 td * polyL1 (expPolyNum tn td n)) = D at *
    generalize hg4 : (n + 1) * (polyL1 td * LnExp.expNum n (polyL1 tn) (polyL1 td)) = E at *
    generalize hg5 : (n + 1) * polyL1 td * LnExp.expNum n (polyL1 tn) (polyL1 td) = F at *
    generalize hg6 : polyL1 (polyPow tn (n + 1)) = G at *
    generalize hg7 : polyL1 tn ^ (n + 1) = H at *
    generalize hg8 : polyL1 (polyAdd (polyScale ((n : Int) + 1)
      (polyMul td (expPolyNum tn td n))) (polyPow tn (n + 1))) = T at *
    omega

end LnPoly
