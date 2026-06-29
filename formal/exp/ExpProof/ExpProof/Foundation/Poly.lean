import Init

/-!
# Polynomial positivity certificates

Dense `Int` polynomials (coefficients low-order first), interval-Horner
evaluation over nonnegative domains, and a fuel-bounded adaptive bisection
checker whose `true` result soundly certifies `0 ≤ P(x)` for every integer
`x` in the queried range. The checker is executed by the kernel via `decide`,
so the analytic components of the monotonicity proof reduce to computation.
-/

namespace ExpPoly

/-- Multiplication monotonicity helpers (Init-only, so spelled out). -/
theorem mul_le_mul_left_nonneg {a b c : Int} (h : a ≤ b) (hc : 0 ≤ c) :
    c * a ≤ c * b := by
  have h1 : 0 ≤ c * (b - a) := Int.mul_nonneg hc (by omega)
  rw [Int.mul_sub] at h1
  omega

theorem mul_le_mul_right_nonneg {a b c : Int} (h : a ≤ b) (hc : 0 ≤ c) :
    a * c ≤ b * c := by
  have h1 : 0 ≤ (b - a) * c := Int.mul_nonneg (by omega) hc
  rw [Int.sub_mul] at h1
  omega

theorem mul_le_mul_left_nonpos {a b c : Int} (h : a ≤ b) (hc : c ≤ 0) :
    c * b ≤ c * a := by
  have h1 : 0 ≤ -c * (b - a) := Int.mul_nonneg (by omega) (by omega)
  rw [Int.mul_sub, Int.neg_mul, Int.neg_mul] at h1
  omega

def evalPoly : List Int → Int → Int
  | [], _ => 0
  | c :: cs, x => c + x * evalPoly cs x

/-- Interval Horner over a nonnegative domain `[lo, hi]`, `0 ≤ lo`. Returns
`(vlo, vhi)` with `vlo ≤ P(x) ≤ vhi` for all `x ∈ [lo, hi]`. -/
def hornerIv : List Int → Int → Int → Int × Int
  | [], _, _ => (0, 0)
  | c :: cs, lo, hi =>
    let (plo, phi) := hornerIv cs lo hi
    let mlo := if 0 ≤ plo then lo * plo else hi * plo
    let mhi := if 0 ≤ phi then hi * phi else lo * phi
    (c + mlo, c + mhi)

theorem hornerIv_sound (cs : List Int) {lo hi x : Int}
    (h0 : 0 ≤ lo) (h1 : lo ≤ x) (h2 : x ≤ hi) :
    (hornerIv cs lo hi).1 ≤ evalPoly cs x ∧ evalPoly cs x ≤ (hornerIv cs lo hi).2 := by
  induction cs with
  | nil => simp [hornerIv, evalPoly]
  | cons c cs ih =>
    obtain ⟨ihlo, ihhi⟩ := ih
    simp only [hornerIv, evalPoly]
    constructor
    · -- lower bound
      have hx : 0 ≤ x := by omega
      split
      · -- 0 ≤ plo : lo * plo ≤ x * plo ≤ x * P(x)
        rename_i hplo
        have s1 : lo * (hornerIv cs lo hi).1 ≤ x * (hornerIv cs lo hi).1 :=
          mul_le_mul_right_nonneg h1 hplo
        have s2 : x * (hornerIv cs lo hi).1 ≤ x * evalPoly cs x :=
          mul_le_mul_left_nonneg ihlo hx
        omega
      · -- plo < 0 : hi * plo ≤ x * plo ≤ x * P(x)
        rename_i hplo
        have hplo' : (hornerIv cs lo hi).1 ≤ 0 := by omega
        have s1 : hi * (hornerIv cs lo hi).1 ≤ x * (hornerIv cs lo hi).1 := by
          have hcomm := mul_le_mul_left_nonpos h2 hplo'
          rw [Int.mul_comm ((hornerIv cs lo hi).1) hi,
            Int.mul_comm ((hornerIv cs lo hi).1) x] at hcomm
          exact hcomm
        have s2 : x * (hornerIv cs lo hi).1 ≤ x * evalPoly cs x :=
          mul_le_mul_left_nonneg ihlo hx
        omega
    · -- upper bound
      have hx : 0 ≤ x := by omega
      split
      · -- 0 ≤ phi : x * P(x) ≤ x * phi ≤ hi * phi
        rename_i hphi
        have s2 : x * evalPoly cs x ≤ x * (hornerIv cs lo hi).2 :=
          mul_le_mul_left_nonneg ihhi hx
        have s1 : x * (hornerIv cs lo hi).2 ≤ hi * (hornerIv cs lo hi).2 :=
          mul_le_mul_right_nonneg h2 hphi
        omega
      · -- phi < 0 : x * P(x) ≤ x * phi ≤ lo * phi
        rename_i hphi
        have hphi' : (hornerIv cs lo hi).2 ≤ 0 := by omega
        have s2 : x * evalPoly cs x ≤ x * (hornerIv cs lo hi).2 :=
          mul_le_mul_left_nonneg ihhi hx
        have s1 : x * (hornerIv cs lo hi).2 ≤ lo * (hornerIv cs lo hi).2 := by
          have hcomm := mul_le_mul_left_nonpos h1 hphi'
          rw [Int.mul_comm ((hornerIv cs lo hi).2) lo,
            Int.mul_comm ((hornerIv cs lo hi).2) x] at hcomm
          exact hcomm
        omega

/-- Adaptive bisection: certifies `0 ≤ P(x)` for every integer `x ∈ [lo, hi]`. -/
def checkNonneg (cs : List Int) (lo hi : Int) : Nat → Bool
  | 0 => false
  | fuel + 1 =>
    if hi < lo then true
    else if 0 ≤ (hornerIv cs lo hi).1 then true
    else if lo = hi then false
    else
      let mid := (lo + hi) / 2
      checkNonneg cs lo mid fuel && checkNonneg cs (mid + 1) hi fuel

theorem checkNonneg_sound (cs : List Int) (fuel : Nat) :
    ∀ lo hi : Int, 0 ≤ lo → checkNonneg cs lo hi fuel = true →
      ∀ x : Int, lo ≤ x → x ≤ hi → 0 ≤ evalPoly cs x := by
  induction fuel with
  | zero => intro lo hi _ h; simp [checkNonneg] at h
  | succ fuel ih =>
    intro lo hi hlo h x hx1 hx2
    unfold checkNonneg at h
    split at h
    · omega
    · split at h
      · rename_i hiv
        have := (hornerIv_sound cs hlo hx1 hx2).1
        omega
      · split at h
        · exact absurd h (by simp)
        · rw [Bool.and_eq_true] at h
          by_cases hm : x ≤ (lo + hi) / 2
          · exact ih lo ((lo + hi) / 2) hlo h.1 x hx1 hm
          · exact ih ((lo + hi) / 2 + 1) hi (by omega) h.2 x (by omega) hx2

/-! ## Polynomial algebra (with evaluation lemmas) -/

def polyAdd : List Int → List Int → List Int
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: polyAdd p q

theorem evalPoly_polyAdd (p q : List Int) (x : Int) :
    evalPoly (polyAdd p q) x = evalPoly p x + evalPoly q x := by
  induction p generalizing q with
  | nil => simp [polyAdd, evalPoly]
  | cons a p ih =>
    cases q with
    | nil => simp [polyAdd, evalPoly]
    | cons b q =>
      simp only [polyAdd, evalPoly, ih]
      rw [Int.mul_add]
      omega

def polyNeg (p : List Int) : List Int := p.map (-·)

theorem evalPoly_polyNeg (p : List Int) (x : Int) :
    evalPoly (polyNeg p) x = -evalPoly p x := by
  induction p with
  | nil => simp [polyNeg, evalPoly]
  | cons a p ih =>
    simp only [polyNeg, List.map, evalPoly] at *
    rw [ih]
    rw [show x * -evalPoly p x = -(x * evalPoly p x) by rw [Int.mul_neg]]
    omega

def polySub (p q : List Int) : List Int := polyAdd p (polyNeg q)

theorem evalPoly_polySub (p q : List Int) (x : Int) :
    evalPoly (polySub p q) x = evalPoly p x - evalPoly q x := by
  unfold polySub
  rw [evalPoly_polyAdd, evalPoly_polyNeg]
  omega

def polyScale (a : Int) (p : List Int) : List Int := p.map (a * ·)

theorem evalPoly_polyScale (a : Int) (p : List Int) (x : Int) :
    evalPoly (polyScale a p) x = a * evalPoly p x := by
  induction p with
  | nil => simp [polyScale, evalPoly]
  | cons c p ih =>
    simp only [polyScale, List.map, evalPoly] at *
    rw [ih, Int.mul_add]
    rw [show x * (a * evalPoly p x) = a * (x * evalPoly p x) by
      rw [← Int.mul_assoc, Int.mul_comm x a, Int.mul_assoc]]

theorem evalPoly_singleton (c x : Int) : evalPoly [c] x = c := by
  simp [evalPoly]

def polyMulX (p : List Int) : List Int := 0 :: p

theorem evalPoly_polyMulX (p : List Int) (x : Int) :
    evalPoly (polyMulX p) x = x * evalPoly p x := by
  simp [polyMulX, evalPoly]

def polyMul : List Int → List Int → List Int
  | [], _ => []
  | a :: p, q => polyAdd (polyScale a q) (polyMulX (polyMul p q))

theorem evalPoly_polyMul (p q : List Int) (x : Int) :
    evalPoly (polyMul p q) x = evalPoly p x * evalPoly q x := by
  induction p with
  | nil => simp [polyMul, evalPoly]
  | cons a p ih =>
    simp only [polyMul, evalPoly]
    rw [evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyMulX, ih]
    rw [Int.add_mul]
    rw [show x * (evalPoly p x * evalPoly q x) = x * evalPoly p x * evalPoly q x by
      rw [Int.mul_assoc]]

/-- Composition with `x + 1`: `evalPoly (polyCompAdd1 p) x = evalPoly p (x + 1)`. -/
def polyCompAdd1 : List Int → List Int
  | [] => []
  | c :: cs =>
    let q := polyCompAdd1 cs
    polyAdd [c] (polyAdd q (polyMulX q))

theorem evalPoly_polyCompAdd1 (p : List Int) (x : Int) :
    evalPoly (polyCompAdd1 p) x = evalPoly p (x + 1) := by
  induction p with
  | nil => simp [polyCompAdd1, evalPoly]
  | cons c cs ih =>
    simp only [polyCompAdd1, evalPoly]
    rw [evalPoly_polyAdd, evalPoly_polyAdd, evalPoly_polyMulX, ih]
    simp only [evalPoly]
    rw [Int.add_mul, Int.one_mul]
    omega

end ExpPoly
