import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Common.Foundation.KroneckerShift

/-!
# Bernstein polynomial nonnegativity certificates

The checker computes integer Bernstein weights for a polynomial on a closed
interval. Nonnegative weights give a nonnegative weighted-power expansion.
The expansion identity is checked at a Kronecker point under explicit
coefficient bounds, so the computed weights are not trusted.
-/

namespace Common.Poly

def bernsteinTermPoly (a b : Int) (n i : Nat) : List Int :=
  polyMul (polyPow [-a, 1] i) (polyPow [b, -1] (n - i))

def bernsteinCertPoly (a b : Int) (n i : Nat) : List Int → List Int
  | [] => []
  | d :: ds =>
    polyAdd (polyScale d (bernsteinTermPoly a b n i))
      (bernsteinCertPoly a b n (i + 1) ds)

theorem eval_bernsteinTermPoly (a b t : Int) (n i : Nat) :
    evalPoly (bernsteinTermPoly a b n i) t =
      (t - a) ^ i * (b - t) ^ (n - i) := by
  unfold bernsteinTermPoly
  rw [evalPoly_polyMul, evalPoly_polyPow, evalPoly_polyPow]
  simp only [evalPoly]
  ring

theorem eval_bernsteinCertPoly_nonneg (a b t : Int) (n i : Nat) :
    ∀ ds : List Int, (∀ d ∈ ds, 0 ≤ d) → a ≤ t → t ≤ b →
      0 ≤ evalPoly (bernsteinCertPoly a b n i ds) t := by
  intro ds
  induction ds generalizing i with
  | nil =>
      intro _ _ _
      simp [bernsteinCertPoly, evalPoly]
  | cons d ds ih =>
      intro hds hat htb
      have hd : 0 ≤ d := hds d (by simp)
      have htail : ∀ z ∈ ds, 0 ≤ z := by
        intro z hz
        exact hds z (by simp [hz])
      have hx : 0 ≤ t - a := by omega
      have hy : 0 ≤ b - t := by omega
      have hterm : 0 ≤ evalPoly (bernsteinTermPoly a b n i) t := by
        rw [eval_bernsteinTermPoly]
        positivity
      have hrest := ih (i := i + 1) htail hat htb
      simp only [bernsteinCertPoly, evalPoly_polyAdd, evalPoly_polyScale]
      positivity

theorem nonnegOn_of_bernsteinCertificate (C ds : List Int) (a b : Int) (n : Nat)
    (hab : a < b)
    (hidentity : polyScale ((b - a) ^ n) C = bernsteinCertPoly a b n 0 ds)
    (hweights : ∀ d ∈ ds, 0 ≤ d) : NonnegOn C a b := by
  intro t hat htb
  have hcert := eval_bernsteinCertPoly_nonneg a b t n 0 ds hweights hat htb
  have heval := congrArg (fun P => evalPoly P t) hidentity
  change evalPoly (polyScale ((b - a) ^ n) C) t =
    evalPoly (bernsteinCertPoly a b n 0 ds) t at heval
  rw [evalPoly_polyScale] at heval
  have hw : 0 < (b - a) ^ n := by
    have : 0 < b - a := by omega
    positivity
  nlinarith

def scaleVariableAux (w : Int) : Nat → List Int → List Int
  | _, [] => []
  | i, c :: cs => c * w ^ i :: scaleVariableAux w (i + 1) cs

def scaleVariable (w : Int) (C : List Int) : List Int :=
  scaleVariableAux w 0 C

def bernsteinWeight (q : List Int) (n i : Nat) : Int :=
  (List.range (i + 1)).foldl
    (fun z j => z + q.getD j 0 * (Nat.choose (n - j) (i - j) : Int)) 0

/-- Candidate integer weights computed from the packed Taylor shift. -/
def bernsteinWitness (C : List Int) (a b : Int) : List Int :=
  let n := C.length - 1
  let q := scaleVariable (b - a) (kShiftWitness kB C a)
  (List.range C.length).map (bernsteinWeight q n)

def bernsteinCertEval (a b x : Int) (n i : Nat) : List Int → Int
  | [] => 0
  | d :: ds =>
    d * (x - a) ^ i * (b - x) ^ (n - i) +
      bernsteinCertEval a b x n (i + 1) ds

theorem eval_bernsteinCertPoly (a b x : Int) (n i : Nat) : ∀ ds : List Int,
    evalPoly (bernsteinCertPoly a b n i ds) x =
      bernsteinCertEval a b x n i ds := by
  intro ds
  induction ds generalizing i with
  | nil => simp [bernsteinCertPoly, bernsteinCertEval, evalPoly]
  | cons d ds ih =>
      simp only [bernsteinCertPoly, bernsteinCertEval, evalPoly_polyAdd,
        evalPoly_polyScale, eval_bernsteinTermPoly, ih]
      ring

def bernsteinCertL1 (a b : Int) (n i : Nat) : List Int → Nat
  | [] => 0
  | d :: ds =>
    d.natAbs * (a.natAbs + 1) ^ i * (b.natAbs + 1) ^ (n - i) +
      bernsteinCertL1 a b n (i + 1) ds

theorem polyL1_bernsteinTermPoly_le (a b : Int) (n i : Nat) :
    polyL1 (bernsteinTermPoly a b n i) ≤
      (a.natAbs + 1) ^ i * (b.natAbs + 1) ^ (n - i) := by
  unfold bernsteinTermPoly
  have hm := polyL1_polyMul (polyPow [-a, 1] i) (polyPow [b, -1] (n - i))
  have hp := polyL1_polyPow [-a, 1] i
  have hq := polyL1_polyPow [b, -1] (n - i)
  have ha : polyL1 ([-a, 1] : List Int) = a.natAbs + 1 := by
    simp [polyL1]
  have hb : polyL1 ([b, -1] : List Int) = b.natAbs + 1 := by
    simp [polyL1]
  rw [ha] at hp
  rw [hb] at hq
  exact le_trans hm (Nat.mul_le_mul hp hq)

theorem polyL1_bernsteinCertPoly_le (a b : Int) (n i : Nat) : ∀ ds : List Int,
    polyL1 (bernsteinCertPoly a b n i ds) ≤ bernsteinCertL1 a b n i ds := by
  intro ds
  induction ds generalizing i with
  | nil => simp [bernsteinCertPoly, bernsteinCertL1, polyL1]
  | cons d ds ih =>
      simp only [bernsteinCertPoly, bernsteinCertL1]
      have hadd := polyL1_polyAdd (polyScale d (bernsteinTermPoly a b n i))
        (bernsteinCertPoly a b n (i + 1) ds)
      have hscale := polyL1_polyScale d (bernsteinTermPoly a b n i)
      have hterm := polyL1_bernsteinTermPoly_le a b n i
      have hrest := ih (i := i + 1)
      have hscaled : polyL1 (polyScale d (bernsteinTermPoly a b n i)) ≤
          d.natAbs * ((a.natAbs + 1) ^ i * (b.natAbs + 1) ^ (n - i)) :=
        le_trans hscale (Nat.mul_le_mul_left _ hterm)
      calc
        polyL1 (polyAdd (polyScale d (bernsteinTermPoly a b n i))
            (bernsteinCertPoly a b n (i + 1) ds))
          ≤ polyL1 (polyScale d (bernsteinTermPoly a b n i)) +
              polyL1 (bernsteinCertPoly a b n (i + 1) ds) := hadd
        _ ≤ d.natAbs * ((a.natAbs + 1) ^ i * (b.natAbs + 1) ^ (n - i)) +
              bernsteinCertL1 a b n (i + 1) ds := Nat.add_le_add hscaled hrest
        _ = d.natAbs * (a.natAbs + 1) ^ i * (b.natAbs + 1) ^ (n - i) +
              bernsteinCertL1 a b n (i + 1) ds := by rw [Nat.mul_assoc]

/-- Exact checker with an explicit witness, used to validate generated weights. -/
def checkBernsteinKWithWitness
    (B : Nat) (C : List Int) (a b : Int) (ds : List Int) : Bool :=
  let n := C.length - 1
  decide (a < b) &&
    decide (∀ d ∈ ds, 0 ≤ d) &&
    decide (polyL1 (polyScale ((b - a) ^ n) C) * 2 < 2 ^ B) &&
    decide (bernsteinCertL1 a b n 0 ds * 2 < 2 ^ B) &&
    decide (evalPoly (polyScale ((b - a) ^ n) C) (((2 ^ B : Nat) : Int)) =
      bernsteinCertEval a b (((2 ^ B : Nat) : Int)) n 0 ds)

def checkBernsteinK (B : Nat) (C : List Int) (a b : Int) : Bool :=
  checkBernsteinKWithWitness B C a b (bernsteinWitness C a b)

theorem checkBernsteinKWithWitness_nonnegOn
    (B : Nat) (C : List Int) (a b : Int) (ds : List Int)
    (hcheck : checkBernsteinKWithWitness B C a b ds = true) : NonnegOn C a b := by
  simp only [checkBernsteinKWithWitness, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨⟨⟨⟨hab, hweights⟩, hpL1⟩, hcertL1⟩, hevalPoint⟩
  intro t hat htb
  let n := C.length - 1
  have hcert := eval_bernsteinCertPoly_nonneg a b t n 0 ds hweights hat htb
  have hqL1 : polyL1 (bernsteinCertPoly a b n 0 ds) * 2 < 2 ^ B := by
    have hbound := polyL1_bernsteinCertPoly_le a b n 0 ds
    exact lt_of_le_of_lt (Nat.mul_le_mul_right 2 hbound) hcertL1
  have heval : evalPoly (polyScale ((b - a) ^ n) C) ((2 : Int) ^ B) =
      evalPoly (bernsteinCertPoly a b n 0 ds) ((2 : Int) ^ B) := by
    rw [pow2_cast, eval_bernsteinCertPoly]
    exact hevalPoint
  have hevery := evalPoly_ext (B := B) (polyScale ((b - a) ^ n) C)
    (bernsteinCertPoly a b n 0 ds) hpL1 hqL1 heval t
  rw [evalPoly_polyScale] at hevery
  have hw : 0 < (b - a) ^ n := by
    have : 0 < b - a := by omega
    positivity
  nlinarith

theorem checkBernsteinK_nonnegOn (B : Nat) (C : List Int) (a b : Int)
    (hcheck : checkBernsteinK B C a b = true) : NonnegOn C a b := by
  exact checkBernsteinKWithWitness_nonnegOn B C a b (bernsteinWitness C a b) hcheck

theorem checkBernsteinKWithWitness_sound
    (B : Nat) (C : List Int) (a b : Int) (ds : List Int)
    (hcheck : checkBernsteinKWithWitness B C a b ds = true) :
    ∀ t : Int, a ≤ t → t ≤ b → 0 ≤ evalPoly C t := by
  exact checkBernsteinKWithWitness_nonnegOn B C a b ds hcheck

theorem checkBernsteinK_sound (B : Nat) (C : List Int) (a b : Int)
    (_hab : a < b) (hcheck : checkBernsteinK B C a b = true) :
    ∀ t : Int, a ≤ t → t ≤ b → 0 ≤ evalPoly C t := by
  exact checkBernsteinK_nonnegOn B C a b hcheck

end Common.Poly
