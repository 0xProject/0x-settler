import LnProof.Foundation.Poly
import LnProof.Foundation.ExpSum

/-!
# Recentered polynomial nonnegativity certificates

The floor-specification certificate polynomials have ~1e-28 relative slack:
plain interval Horner cannot see the cancellation between their huge
monomials, so bisection alone would need ~1e30 cells. Recentering a
polynomial at each cell's left endpoint (an exact integer Taylor shift)
exposes the cancellation symbolically; interval Horner over the shifted
cell `[0, w]` then converges with a few hundred cells.

`checkCover` walks a caller-supplied list of cell widths and certifies
`0 ≤ P(x)` for every integer `x` in `[lo, hi]`.

The file also provides the polynomial-level partial-sum numerator
(`expPolyNum`) and its evaluation lemma, connecting the certificate
polynomials to the `expNum` caps of `LnProof.Foundation.ExpSum`.
-/

namespace LnPoly

/-- Synthetic division by `(x - a)`: `P(x) = Q(x) (x - a) + r`. -/
def synthDiv : List Int → Int → List Int × Int
  | [], _ => ([], 0)
  | [c], _ => ([], c)
  | c :: cs, a =>
    ((synthDiv cs a).2 :: (synthDiv cs a).1, c + a * (synthDiv cs a).2)

theorem synthDiv_eval (C : List Int) (a x : Int) :
    evalPoly C x = evalPoly (synthDiv C a).1 x * (x - a) + (synthDiv C a).2 := by
  match C with
  | [] => simp [synthDiv, evalPoly]
  | [c] => simp [synthDiv, evalPoly]
  | c :: c2 :: cs =>
    have ih := synthDiv_eval (c2 :: cs) a x
    show c + x * evalPoly (c2 :: cs) x = _
    rw [ih]
    show _ = ((synthDiv (c2 :: cs) a).2 +
        x * evalPoly ((synthDiv (c2 :: cs) a).1) x) * (x - a) +
      (c + a * (synthDiv (c2 :: cs) a).2)
    rw [Int.add_mul]
    have e1 : x * (evalPoly (synthDiv (c2 :: cs) a).1 x * (x - a) +
        (synthDiv (c2 :: cs) a).2) =
        x * evalPoly (synthDiv (c2 :: cs) a).1 x * (x - a) +
          x * (synthDiv (c2 :: cs) a).2 := by
      rw [Int.mul_add, Int.mul_assoc]
    have e2 : x * (synthDiv (c2 :: cs) a).2 =
        (x - a) * (synthDiv (c2 :: cs) a).2 + a * (synthDiv (c2 :: cs) a).2 := by
      rw [Int.sub_mul]
      omega
    have e3 : (x - a) * (synthDiv (c2 :: cs) a).2 =
        (synthDiv (c2 :: cs) a).2 * (x - a) := Int.mul_comm _ _
    omega

theorem synthDiv_length : ∀ (C : List Int) (a : Int), C ≠ [] →
    (synthDiv C a).1.length + 1 = C.length := by
  intro C a h
  match C with
  | [c] => rfl
  | c :: c2 :: cs =>
    have ih := synthDiv_length (c2 :: cs) a (by simp)
    show ((synthDiv (c2 :: cs) a).2 :: (synthDiv (c2 :: cs) a).1).length + 1 = _
    simp only [List.length_cons] at *
    omega

/-- Fuel-based Taylor shift (structural recursion, so the kernel computes
it inside `decide`). -/
def polyShiftAux : Nat → List Int → Int → List Int
  | 0, _, _ => []
  | _ + 1, [], _ => []
  | fuel + 1, c :: cs, a =>
    (synthDiv (c :: cs) a).2 :: polyShiftAux fuel (synthDiv (c :: cs) a).1 a

/-- Exact Taylor shift: `evalPoly (polyShift C a) δ = evalPoly C (a + δ)`. -/
def polyShift (C : List Int) (a : Int) : List Int :=
  polyShiftAux C.length C a

theorem polyShiftAux_eval (fuel : Nat) :
    ∀ (C : List Int) (a δ : Int), C.length ≤ fuel →
      evalPoly (polyShiftAux fuel C a) δ = evalPoly C (a + δ) := by
  induction fuel with
  | zero =>
    intro C a δ h
    have : C = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rfl
  | succ f ih =>
    intro C a δ h
    match C with
    | [] => rfl
    | c :: cs =>
      show (synthDiv (c :: cs) a).2 +
          δ * evalPoly (polyShiftAux f (synthDiv (c :: cs) a).1 a) δ = _
      have hlen : (synthDiv (c :: cs) a).1.length ≤ f := by
        have := synthDiv_length (c :: cs) a (by simp)
        simp only [List.length_cons] at *
        omega
      rw [ih _ a δ hlen, synthDiv_eval (c :: cs) a (a + δ)]
      have e1 : evalPoly (synthDiv (c :: cs) a).1 (a + δ) * (a + δ - a) =
          δ * evalPoly (synthDiv (c :: cs) a).1 (a + δ) := by
        rw [show a + δ - a = δ by omega, Int.mul_comm]
      omega

theorem polyShift_eval (C : List Int) (a δ : Int) :
    evalPoly (polyShift C a) δ = evalPoly C (a + δ) :=
  polyShiftAux_eval C.length C a δ (Nat.le_refl _)

/-- Certify `0 ≤ P(x)` for every integer `x ∈ [lo, hi]` by walking cells of
the given widths, recentering at each cell's left endpoint. -/
def checkCover (C : List Int) (lo hi : Int) : List Int → Bool
  | [] => decide (hi < lo)
  | w :: ws =>
    decide (0 ≤ w) && decide (0 ≤ (hornerIv (polyShift C lo) 0 w).1) &&
      checkCover C (lo + w + 1) hi ws

theorem checkCover_sound (C : List Int) (ws : List Int) :
    ∀ lo hi : Int, checkCover C lo hi ws = true →
      ∀ x : Int, lo ≤ x → x ≤ hi → 0 ≤ evalPoly C x := by
  induction ws with
  | nil =>
    intro lo hi h x h1 h2
    simp only [checkCover, decide_eq_true_eq] at h
    omega
  | cons w ws ih =>
    intro lo hi h x h1 h2
    simp only [checkCover, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hw, hcell⟩, hrest⟩ := h
    rcases Int.lt_or_le (lo + w) x with hout | hin
    · exact ih (lo + w + 1) hi hrest x (by omega) h2
    · have hs := (hornerIv_sound (polyShift C lo) (lo := 0) (hi := w)
        (x := x - lo) (Int.le_refl 0) (by omega) (by omega)).1
      rw [polyShift_eval] at hs
      rw [show lo + (x - lo) = x by omega] at hs
      omega

/-! ## Partial-sum numerators at the polynomial level -/

/-- Int mirror of `LnExp.expNum`. -/
def expNumI : Nat → Int → Int → Int
  | 0, _, _ => 1
  | n + 1, p, q => (n + 1) * q * expNumI n p q + p ^ (n + 1)

theorem expNumI_eq_expNum (k : Nat) (p q : Nat) :
    expNumI k (p : Int) (q : Int) = (LnExp.expNum k p q : Int) := by
  induction k with
  | zero => rfl
  | succ n ih =>
    show ((n : Int) + 1) * q * expNumI n p q + (p : Int) ^ (n + 1) = _
    rw [ih]
    show _ = ((((n + 1) * q * LnExp.expNum n p q + p ^ (n + 1) : Nat)) : Int)
    push_cast
    omega

def polyPow (P : List Int) : Nat → List Int
  | 0 => [1]
  | n + 1 => polyMul P (polyPow P n)

theorem evalPoly_polyPow (P : List Int) (n : Nat) (x : Int) :
    evalPoly (polyPow P n) x = evalPoly P x ^ n := by
  induction n with
  | zero => simp [polyPow, evalPoly]
  | succ k ih =>
    show evalPoly (polyMul P (polyPow P k)) x = _
    rw [evalPoly_polyMul, ih]
    rw [show evalPoly P x ^ (k + 1) = evalPoly P x ^ k * evalPoly P x from
      Int.pow_succ _ _]
    rw [Int.mul_comm]

/-- Polynomial-level partial-sum numerator: evaluates to
`expNumI k (TN(x)) (TD(x))`. -/
def expPolyNum (TN TD : List Int) : Nat → List Int
  | 0 => [1]
  | n + 1 =>
    polyAdd (polyScale ((n : Int) + 1) (polyMul TD (expPolyNum TN TD n)))
      (polyPow TN (n + 1))

theorem evalPoly_expPolyNum (TN TD : List Int) (k : Nat) (x : Int) :
    evalPoly (expPolyNum TN TD k) x =
      expNumI k (evalPoly TN x) (evalPoly TD x) := by
  induction k with
  | zero => simp [expPolyNum, expNumI, evalPoly]
  | succ n ih =>
    show evalPoly (polyAdd (polyScale ((n : Int) + 1)
      (polyMul TD (expPolyNum TN TD n))) (polyPow TN (n + 1))) x = _
    rw [evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyMul, ih,
      evalPoly_polyPow]
    show _ = ((n : Int) + 1) * evalPoly TD x * expNumI n (evalPoly TN x)
      (evalPoly TD x) + evalPoly TN x ^ (n + 1)
    rw [← Int.mul_assoc]

/-! ## Crude range and difference bounds over a box

`polyHi cs B` bounds `evalPoly cs t` from above for `t ∈ [0, B]`;
`polyAbs cs B` bounds its magnitude; `polyDiffHi cs B` bounds the divided
difference `(P(y) - P(x))/(y - x)` from above for `0 ≤ x ≤ y ≤ B`. A
negative `polyDiffHi` certificate proves the polynomial decreasing on the
whole box, which is how the bracket lemmas compare pipeline stage values
at integer points against the certificate polynomials' rational interval
ends. -/

def iabs (c : Int) : Int := if c < 0 then -c else c

def polyHi : List Int → Int → Int
  | [], _ => 0
  | c :: cs, B => c + B * max (polyHi cs B) 0

def polyDiffHi : List Int → Int → Int
  | [], _ => 0
  | _ :: cs, B => polyHi cs B + max (B * polyDiffHi cs B) 0

theorem polyHi_bound (cs : List Int) (B : Int) :
    ∀ t : Int, 0 ≤ t → t ≤ B → evalPoly cs t ≤ polyHi cs B := by
  induction cs with
  | nil => intro t _ _; exact Int.le_refl _
  | cons c cs ih =>
    intro t h0 hB
    show c + t * evalPoly cs t ≤ c + B * max (polyHi cs B) 0
    have hT := ih t h0 hB
    rcases Int.le_total (evalPoly cs t) 0 with hneg | hpos
    · have h1 : t * evalPoly cs t ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos h0 hneg
      have h2 : 0 ≤ B * max (polyHi cs B) 0 :=
        Int.mul_nonneg (by omega) (by omega)
      omega
    · have h1 : t * evalPoly cs t ≤ B * evalPoly cs t :=
        mul_le_mul_right_nonneg hB hpos
      have h2 : B * evalPoly cs t ≤ B * max (polyHi cs B) 0 :=
        mul_le_mul_left_nonneg (by omega) (by omega)
      omega

theorem polyDiffHi_bound (cs : List Int) (B : Int) :
    ∀ x y : Int, 0 ≤ x → x ≤ y → y ≤ B →
      evalPoly cs y - evalPoly cs x ≤ polyDiffHi cs B * (y - x) := by
  induction cs with
  | nil =>
    intro x y _ _ _
    show (0 : Int) - 0 ≤ 0 * (y - x)
    omega
  | cons c cs ih =>
    intro x y hx hxy hyB
    show c + y * evalPoly cs y - (c + x * evalPoly cs x) ≤
      (polyHi cs B + max (B * polyDiffHi cs B) 0) * (y - x)
    -- y T(y) - x T(x) = (y - x) T(y) + x (T(y) - T(x))
    have hsplit : y * evalPoly cs y - x * evalPoly cs x =
        (y - x) * evalPoly cs y + x * (evalPoly cs y - evalPoly cs x) := by
      rw [Int.sub_mul, Int.mul_sub]
      omega
    have h1 : (y - x) * evalPoly cs y ≤ (y - x) * polyHi cs B :=
      mul_le_mul_left_nonneg (polyHi_bound cs B y (by omega) hyB) (by omega)
    have h2 : x * (evalPoly cs y - evalPoly cs x) ≤ max (B * polyDiffHi cs B) 0 * (y - x) := by
      have hd := ih x y hx hxy hyB
      rcases Int.le_total 0 (polyDiffHi cs B) with hD | hD
      · have s1 : x * (evalPoly cs y - evalPoly cs x) ≤ x * (polyDiffHi cs B * (y - x)) := by
          rcases Int.le_total (evalPoly cs y - evalPoly cs x) (polyDiffHi cs B * (y - x))
            with h | h
          · exact mul_le_mul_left_nonneg h hx
          · have : evalPoly cs y - evalPoly cs x = polyDiffHi cs B * (y - x) := by omega
            rw [this]
            exact Int.le_refl _
        have s2 : x * (polyDiffHi cs B * (y - x)) ≤ B * (polyDiffHi cs B * (y - x)) :=
          mul_le_mul_right_nonneg (by omega)
            (Int.mul_nonneg hD (by omega))
        have e1 : B * (polyDiffHi cs B * (y - x)) = B * polyDiffHi cs B * (y - x) := by
          rw [Int.mul_assoc]
        have hmax : B * polyDiffHi cs B * (y - x) ≤ max (B * polyDiffHi cs B) 0 * (y - x) :=
          mul_le_mul_right_nonneg (by omega) (by omega)
        omega
      · -- divided difference is nonpositive: x * diff ≤ 0
        have hd0 : evalPoly cs y - evalPoly cs x ≤ 0 := by
          have : polyDiffHi cs B * (y - x) ≤ 0 :=
            Int.mul_nonpos_of_nonpos_of_nonneg hD (by omega)
          omega
        have s1 : x * (evalPoly cs y - evalPoly cs x) ≤ 0 :=
          Int.mul_nonpos_of_nonneg_of_nonpos hx hd0
        have : 0 ≤ max (B * polyDiffHi cs B) 0 * (y - x) :=
          Int.mul_nonneg (by omega) (by omega)
        omega
    have e2 : (polyHi cs B + max (B * polyDiffHi cs B) 0) * (y - x) =
        (y - x) * polyHi cs B + max (B * polyDiffHi cs B) 0 * (y - x) := by
      rw [Int.add_mul, Int.mul_comm (polyHi cs B) (y - x)]
    omega

/-! ## Homogenized two-point evaluation -/

/-- `homPoly cs num den` is `Σ_j cs_j num^j den^(deg - j)` at the
polynomial level. -/
def homPoly : List Int → List Int → List Int → List Int
  | [], _, _ => [0]
  | c :: cs, num, den =>
    polyAdd (polyScale c (polyPow den cs.length)) (polyMul num (homPoly cs num den))

/-- `homEvalI cs n d = Σ_j cs_j n^j d^(deg-j)`, Horner-style. -/
def homEvalI : List Int → Int → Int → Int
  | [], _, _ => 0
  | c :: cs, nv, dv => c * dv ^ cs.length + nv * homEvalI cs nv dv

theorem evalPoly_homPoly (cs : List Int) (num den : List Int) (x : Int) :
    evalPoly (homPoly cs num den) x =
      homEvalI cs (evalPoly num x) (evalPoly den x) := by
  induction cs with
  | nil =>
    show (0 : Int) + x * 0 = 0
    omega
  | cons c cs ih =>
    show evalPoly (polyAdd (polyScale c (polyPow den cs.length))
      (polyMul num (homPoly cs num den))) x = _
    rw [evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyPow, evalPoly_polyMul, ih]
    rfl

/-- The trivial homogenization identity: at the pair `(u d, d)` the
homogenized value collapses to `d^deg · P(u)`. -/
theorem homEvalI_collapse (u D : Int) :
    ∀ (c : Int) (cs : List Int),
      homEvalI (c :: cs) (u * D) D = D ^ cs.length * evalPoly (c :: cs) u := by
  intro c cs
  induction cs generalizing c with
  | nil =>
    show c * D ^ 0 + u * D * 0 = D ^ 0 * (c + u * 0)
    rw [Int.mul_zero, Int.mul_zero, Int.add_zero, Int.add_zero, Int.mul_comm]
  | cons c2 cs ih =>
    show c * D ^ (c2 :: cs).length + u * D * homEvalI (c2 :: cs) (u * D) D = _
    rw [ih c2]
    show c * D ^ (cs.length + 1) + u * D * (D ^ cs.length * evalPoly (c2 :: cs) u) =
      D ^ (cs.length + 1) * (c + u * evalPoly (c2 :: cs) u)
    have e1 : (D : Int) ^ (cs.length + 1) = D * D ^ cs.length := by
      rw [Int.pow_succ, Int.mul_comm]
    rw [e1, Int.mul_add]
    have e2 : u * D * (D ^ cs.length * evalPoly (c2 :: cs) u) =
        D * D ^ cs.length * (u * evalPoly (c2 :: cs) u) := by
      simp only [Int.mul_assoc, Int.mul_left_comm]
    have e3 : c * (D * D ^ cs.length) = D * D ^ cs.length * c := by
      rw [Int.mul_comm]
    omega

/-! ## Sharing-friendly mirrors of the shift checker

`synthDiv` names its recursive result three times, and the kernel
re-evaluates each occurrence during `decide`. The `M`-variants bind the
recursive result through a `match`, so the kernel computes it once per
step; `checkCoverM_sound` transfers soundness from the reference checker.
-/

def synthDivM : List Int → Int → List Int × Int
  | [], _ => ([], 0)
  | [c], _ => ([], c)
  | c :: cs, a =>
    match synthDivM cs a with
    | (q, r) => (r :: q, c + a * r)

theorem synthDivM_eq : ∀ (C : List Int) (a : Int), synthDivM C a = synthDiv C a := by
  intro C a
  match C with
  | [] => rfl
  | [c] => rfl
  | c :: c2 :: cs =>
    have ih := synthDivM_eq (c2 :: cs) a
    show (match synthDivM (c2 :: cs) a with
      | (q, r) => (r :: q, c + a * r)) = _
    rw [ih]
    rcases h : synthDiv (c2 :: cs) a with ⟨q, r⟩
    show (r :: q, c + a * r) = ((synthDiv (c2 :: cs) a).2 :: (synthDiv (c2 :: cs) a).1,
      c + a * (synthDiv (c2 :: cs) a).2)
    rw [h]

def polyShiftAuxM : Nat → List Int → Int → List Int
  | 0, _, _ => []
  | _ + 1, [], _ => []
  | fuel + 1, c :: cs, a =>
    match synthDivM (c :: cs) a with
    | (q, r) => r :: polyShiftAuxM fuel q a

theorem polyShiftAuxM_eq : ∀ (fuel : Nat) (C : List Int) (a : Int),
    polyShiftAuxM fuel C a = polyShiftAux fuel C a := by
  intro fuel
  induction fuel with
  | zero => intro C a; rfl
  | succ f ih =>
    intro C a
    match C with
    | [] => rfl
    | c :: cs =>
      show (match synthDivM (c :: cs) a with
        | (q, r) => r :: polyShiftAuxM f q a) = _
      rw [synthDivM_eq]
      rcases h : synthDiv (c :: cs) a with ⟨q, r⟩
      show r :: polyShiftAuxM f q a =
        (synthDiv (c :: cs) a).2 :: polyShiftAux f (synthDiv (c :: cs) a).1 a
      rw [h, ih]

def polyShiftM (C : List Int) (a : Int) : List Int :=
  polyShiftAuxM C.length C a

theorem polyShiftM_eq (C : List Int) (a : Int) : polyShiftM C a = polyShift C a :=
  polyShiftAuxM_eq C.length C a

def checkCoverM (C : List Int) (lo hi : Int) : List Int → Bool
  | [] => decide (hi < lo)
  | w :: ws =>
    decide (0 ≤ w) && decide (0 ≤ (hornerIv (polyShiftM C lo) 0 w).1) &&
      checkCoverM C (lo + w + 1) hi ws

theorem checkCoverM_eq (C : List Int) : ∀ (ws : List Int) (lo hi : Int),
    checkCoverM C lo hi ws = checkCover C lo hi ws := by
  intro ws
  induction ws with
  | nil => intro lo hi; rfl
  | cons w ws ih =>
    intro lo hi
    show (decide (0 ≤ w) && decide (0 ≤ (hornerIv (polyShiftM C lo) 0 w).1) &&
      checkCoverM C (lo + w + 1) hi ws) = _
    rw [polyShiftM_eq, ih]
    rfl

theorem checkCoverM_sound (C : List Int) (ws : List Int) (lo hi : Int)
    (h : checkCoverM C lo hi ws = true) :
    ∀ x : Int, lo ≤ x → x ≤ hi → 0 ≤ evalPoly C x := by
  refine checkCover_sound C ws lo hi ?_
  rw [← checkCoverM_eq]
  exact h

end LnPoly
