import LnProof.FloorBracket
import LnProof.FloorCertAux

/-!
# From cell certificates to exponential caps

Converts the kernel-checked nonnegativity of the four main certificate
polynomials into `capUB`/`capLB` facts about the pipeline value `X1`:
integer-scaled statements of `e^(X1/2^99) ≤ (m/S)(1+ε)` and the three
mirrors, with `ε = 42/10^29`, over the common denominator `10^27 · 2^99`.
-/

namespace LnFloorCert
open LnGeneratedModel LnPoly LnExp

set_option maxRecDepth 100000

theorem eval01 (x : Int) : evalPoly ([0, 1] : List Int) x = x := by
  show (0 : Int) + x * (1 + x * 0) = x
  omega

theorem evalCertGeUp (m : Nat) :
    evalPoly certGeUp (m : Int) =
      (EUD + EUN) * KF1 * ((m : Int) * evalPoly geTD (m : Int) ^ 23) +
        -(Sc : Int) * EUD *
          (23 * (expNumI 22 (evalPoly geTN (m : Int)) (evalPoly geTD (m : Int)) *
            evalPoly geTD (m : Int)) + 2 * evalPoly geTN (m : Int) ^ 23) := by
  unfold certGeUp
  simp only [evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyMul, evalPoly_polyPow,
    evalPoly_expPolyNum, eval01]

theorem evalCertGeLo (m : Nat) :
    evalPoly certGeLo (m : Int) =
      EUD * (Sc : Int) *
          expNumI 22 (evalPoly geTN2b (m : Int)) (evalPoly geTD2b (m : Int)) +
        -(EUD - EUN) * KF * ((m : Int) * evalPoly geTD2b (m : Int) ^ 22) := by
  unfold certGeLo
  simp only [evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyMul, evalPoly_polyPow,
    evalPoly_expPolyNum, eval01]

theorem evalCertLtUp (m : Nat) :
    evalPoly certLtUp (m : Int) =
      (EUD + EUN) * ((m : Int) *
          expNumI 22 (evalPoly ltTN2b (m : Int)) (evalPoly ltTD2b (m : Int))) +
        -EUD * (Sc : Int) * KF * evalPoly ltTD2b (m : Int) ^ 22 := by
  unfold certLtUp
  simp only [evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyMul, evalPoly_polyPow,
    evalPoly_expPolyNum, eval01]

theorem evalCertLtLo (m : Nat) :
    evalPoly certLtLo (m : Int) =
      (Sc : Int) * EUD * KF1 * evalPoly ltTD (m : Int) ^ 23 +
        -(EUD - EUN) * ((m : Int) *
          (23 * (expNumI 22 (evalPoly ltTN (m : Int)) (evalPoly ltTD (m : Int)) *
            evalPoly ltTD (m : Int)) + 2 * evalPoly ltTN (m : Int) ^ 23)) := by
  unfold certLtLo
  simp only [evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyMul, evalPoly_polyPow,
    evalPoly_expPolyNum, eval01]

theorem evalCertGeH (m : Nat) :
    evalPoly certGeH (m : Int) =
      24 * evalPoly geTD (m : Int) + -2 * evalPoly geTN (m : Int) := by
  show evalPoly (polyAdd (polyScale 24 geTD) (polyScale (-2) geTN)) (m : Int) = _
  simp only [evalPoly_polyAdd, evalPoly_polyScale]

theorem evalCertLtH (m : Nat) :
    evalPoly certLtH (m : Int) =
      24 * evalPoly ltTD (m : Int) + -2 * evalPoly ltTN (m : Int) := by
  show evalPoly (polyAdd (polyScale 24 ltTD) (polyScale (-2) ltTN)) (m : Int) = _
  simp only [evalPoly_polyAdd, evalPoly_polyScale]

theorem evalCertGeTD (m : Nat) :
    evalPoly certGeTD (m : Int) = evalPoly geTD (m : Int) + -1 := by
  show evalPoly (polyAdd geTD [-1]) (m : Int) = _
  rw [evalPoly_polyAdd]
  show _ + ((-1 : Int) + (m : Int) * 0) = _
  omega

theorem evalCertGeTD2 (m : Nat) :
    evalPoly certGeTD2 (m : Int) = evalPoly geTD2b (m : Int) + -1 := by
  show evalPoly (polyAdd geTD2b [-1]) (m : Int) = _
  rw [evalPoly_polyAdd]
  show _ + ((-1 : Int) + (m : Int) * 0) = _
  omega

theorem evalCertLtTD (m : Nat) :
    evalPoly certLtTD (m : Int) = evalPoly ltTD (m : Int) + -1 := by
  show evalPoly (polyAdd ltTD [-1]) (m : Int) = _
  rw [evalPoly_polyAdd]
  show _ + ((-1 : Int) + (m : Int) * 0) = _
  omega

theorem evalCertLtTD2 (m : Nat) :
    evalPoly certLtTD2 (m : Int) = evalPoly ltTD2b (m : Int) + -1 := by
  show evalPoly (polyAdd ltTD2b [-1]) (m : Int) = _
  rw [evalPoly_polyAdd]
  show _ + ((-1 : Int) + (m : Int) * 0) = _
  omega

/-! ## Int-to-Nat bridges for the two cap shapes at K = 22 -/

theorem capUB22_of_int {tn td y w : Nat} (htd : 0 < td) (hH : 2 * tn ≤ 24 * td)
    (h : (expNumI 22 (tn : Int) (td : Int) * (23 * (td : Int)) + 2 * (tn : Int) ^ 23) *
        (w : Int) ≤ (y : Int) * (25852016738884976640000 * (td : Int) ^ 23)) :
    capUB tn td y w := by
  refine capUB_of_partial htd (by omega : 2 * tn ≤ (22 + 2) * td) ?_
  show (expNum 22 tn td * (23 * td) + 2 * tn ^ 23) * w ≤ y * (fact 23 * td ^ 23)
  rw [show fact 23 = 25852016738884976640000 from by decide]
  refine Int.ofNat_le.mp ?_
  rw [expNumI_eq_expNum] at h
  simp only [Int.natCast_mul, Int.natCast_add, Int.natCast_pow]
  exact h

theorem capLB22_of_int {tn td y w : Nat}
    (h : (y : Int) * (1124000727777607680000 * (td : Int) ^ 22) ≤
        expNumI 22 (tn : Int) (td : Int) * (w : Int)) :
    capLB tn td y w := by
  refine ⟨22, ?_⟩
  show y * (fact 22 * td ^ 22) ≤ expNum 22 tn td * w
  rw [show fact 22 = 1124000727777607680000 from by decide]
  refine Int.ofNat_le.mp ?_
  rw [expNumI_eq_expNum] at h
  simp only [Int.natCast_mul, Int.natCast_pow]
  exact h

/-! ## Certificate nonnegativity to caps at the certificate rationals -/

theorem capGeUp {m : Nat} (h1 : Sc + 46 ≤ m) (h2 : m < MHI)
    (hup : 0 ≤ evalPoly certGeUp (m : Int)) :
    capUB (evalPoly geTN (m : Int)).toNat (evalPoly geTD (m : Int)).toNat
      (m * 10000000000000000000000000003401)
      143418293695452518191953761862290000000000000000000000000000000 := by
  have hw1 : (14341829369545251819195376186275 : Int) ≤ (m : Int) := by
    simp only [Sc] at h1; omega
  have hw2 : (m : Int) ≤ 20282409603651670423947251286015 := by
    simp only [MHI] at h2; omega
  have hTN0 : 0 ≤ evalPoly geTN (m : Int) := geTN_nonneg hw1 hw2
  have hTD1 : 1 ≤ evalPoly geTD (m : Int) := by
    have h := geTD_nonneg hw1 hw2
    rw [evalCertGeTD] at h
    omega
  have hHc : 2 * evalPoly geTN (m : Int) ≤ 24 * evalPoly geTD (m : Int) := by
    have h := geH_nonneg hw1 hw2
    rw [evalCertGeH] at h
    omega
  have htn : ((evalPoly geTN (m : Int)).toNat : Int) = evalPoly geTN (m : Int) :=
    Int.toNat_of_nonneg hTN0
  have htd : ((evalPoly geTD (m : Int)).toNat : Int) = evalPoly geTD (m : Int) :=
    Int.toNat_of_nonneg (by omega)
  refine capUB22_of_int (by omega) (by omega) ?_
  rw [htn, htd]
  rw [evalCertGeUp] at hup
  simp only [EUD, EUN, KF1, Sc] at hup
  simp only [Int.natCast_mul]
  rw [show ((143418293695452518191953761862290000000000000000000000000000000 : Nat) : Int) = 143418293695452518191953761862290000000000000000000000000000000 from rfl,
      show ((10000000000000000000000000003401 : Nat) : Int) = 10000000000000000000000000003401 from rfl]
  have eS : expNumI 22 (evalPoly geTN (m : Int)) (evalPoly geTD (m : Int)) *
      (23 * evalPoly geTD (m : Int)) =
      23 * (expNumI 22 (evalPoly geTN (m : Int)) (evalPoly geTD (m : Int)) *
        evalPoly geTD (m : Int)) := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [eS]
  have eR : (m : Int) * 10000000000000000000000000003401 *
      (25852016738884976640000 * evalPoly geTD (m : Int) ^ 23) =
      10000000000000000000000000003401 * 25852016738884976640000 *
        ((m : Int) * evalPoly geTD (m : Int) ^ 23) := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [eR]
  generalize hgET : expNumI 22 (evalPoly geTN (m : Int)) (evalPoly geTD (m : Int)) *
    evalPoly geTD (m : Int) = ET at hup ⊢
  generalize hgN23 : evalPoly geTN (m : Int) ^ 23 = N23 at hup ⊢
  generalize hgMT : (m : Int) * evalPoly geTD (m : Int) ^ 23 = MT at hup ⊢
  omega

theorem capGeLo {m : Nat} (h1 : Sc + 46 ≤ m) (h2 : m < MHI)
    (hlo : 0 ≤ evalPoly certGeLo (m : Int)) :
    capLB (evalPoly geTN2b (m : Int)).toNat (evalPoly geTD2b (m : Int)).toNat
      (m * 9999999999999999999999999996599)
      143418293695452518191953761862290000000000000000000000000000000 := by
  have hw1 : (14341829369545251819195376186275 : Int) ≤ (m : Int) := by
    simp only [Sc] at h1; omega
  have hw2 : (m : Int) ≤ 20282409603651670423947251286015 := by
    simp only [MHI] at h2; omega
  have hTN0 : 0 ≤ evalPoly geTN2b (m : Int) := geTN2_nonneg hw1 hw2
  have hTD1 : 1 ≤ evalPoly geTD2b (m : Int) := by
    have h := geTD2_nonneg hw1 hw2
    rw [evalCertGeTD2] at h
    omega
  have htn : ((evalPoly geTN2b (m : Int)).toNat : Int) = evalPoly geTN2b (m : Int) :=
    Int.toNat_of_nonneg hTN0
  have htd : ((evalPoly geTD2b (m : Int)).toNat : Int) = evalPoly geTD2b (m : Int) :=
    Int.toNat_of_nonneg (by omega)
  refine capLB22_of_int ?_
  rw [htn, htd]
  rw [evalCertGeLo] at hlo
  simp only [EUD, EUN, KF, Sc] at hlo
  simp only [Int.natCast_mul]
  rw [show ((143418293695452518191953761862290000000000000000000000000000000 : Nat) : Int) = 143418293695452518191953761862290000000000000000000000000000000 from rfl,
      show ((9999999999999999999999999996599 : Nat) : Int) = 9999999999999999999999999996599 from rfl]
  have eR : (m : Int) * 9999999999999999999999999996599 *
      (1124000727777607680000 * evalPoly geTD2b (m : Int) ^ 22) =
      9999999999999999999999999996599 * 1124000727777607680000 *
        ((m : Int) * evalPoly geTD2b (m : Int) ^ 22) := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [eR]
  generalize hgE : expNumI 22 (evalPoly geTN2b (m : Int)) (evalPoly geTD2b (m : Int)) =
    E at hlo ⊢
  generalize hgMT : (m : Int) * evalPoly geTD2b (m : Int) ^ 22 = MT at hlo ⊢
  omega

theorem capLtUp {m : Nat} (h1 : MLO ≤ m) (h2 : m + 46 ≤ Sc)
    (hup : 0 ≤ evalPoly certLtUp (m : Int)) :
    capLB (evalPoly ltTN2b (m : Int)).toNat (evalPoly ltTD2b (m : Int)).toNat
      143418293695452518191953761862290000000000000000000000000000000
      (m * 10000000000000000000000000003401) := by
  have hw1 : (10141204801825835211973625643008 : Int) ≤ (m : Int) := by
    simp only [MLO] at h1; omega
  have hw2 : (m : Int) ≤ 14341829369545251819195376186183 := by
    simp only [Sc] at h2; omega
  have hTN0 : 0 ≤ evalPoly ltTN2b (m : Int) := ltTN2_nonneg hw1 hw2
  have hTD1 : 1 ≤ evalPoly ltTD2b (m : Int) := by
    have h := ltTD2_nonneg hw1 hw2
    rw [evalCertLtTD2] at h
    omega
  have htn : ((evalPoly ltTN2b (m : Int)).toNat : Int) = evalPoly ltTN2b (m : Int) :=
    Int.toNat_of_nonneg hTN0
  have htd : ((evalPoly ltTD2b (m : Int)).toNat : Int) = evalPoly ltTD2b (m : Int) :=
    Int.toNat_of_nonneg (by omega)
  refine capLB22_of_int ?_
  rw [htn, htd]
  rw [evalCertLtUp] at hup
  simp only [EUD, EUN, KF, Sc] at hup
  simp only [Int.natCast_mul]
  rw [show ((143418293695452518191953761862290000000000000000000000000000000 : Nat) : Int) = 143418293695452518191953761862290000000000000000000000000000000 from rfl,
      show ((10000000000000000000000000003401 : Nat) : Int) = 10000000000000000000000000003401 from rfl]
  have eR : expNumI 22 (evalPoly ltTN2b (m : Int)) (evalPoly ltTD2b (m : Int)) *
      ((m : Int) * 10000000000000000000000000003401) =
      10000000000000000000000000003401 *
        ((m : Int) * expNumI 22 (evalPoly ltTN2b (m : Int)) (evalPoly ltTD2b (m : Int))) := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [eR]
  generalize hgME : (m : Int) * expNumI 22 (evalPoly ltTN2b (m : Int))
    (evalPoly ltTD2b (m : Int)) = ME at hup ⊢
  generalize hgT22 : evalPoly ltTD2b (m : Int) ^ 22 = T22 at hup ⊢
  omega

theorem capLtLo {m : Nat} (h1 : MLO ≤ m) (h2 : m + 46 ≤ Sc)
    (hlo : 0 ≤ evalPoly certLtLo (m : Int)) :
    capUB (evalPoly ltTN (m : Int)).toNat (evalPoly ltTD (m : Int)).toNat
      143418293695452518191953761862290000000000000000000000000000000
      (m * 9999999999999999999999999996599) := by
  have hw1 : (10141204801825835211973625643008 : Int) ≤ (m : Int) := by
    simp only [MLO] at h1; omega
  have hw2 : (m : Int) ≤ 14341829369545251819195376186183 := by
    simp only [Sc] at h2; omega
  have hTN0 : 0 ≤ evalPoly ltTN (m : Int) := ltTN_nonneg hw1 hw2
  have hTD1 : 1 ≤ evalPoly ltTD (m : Int) := by
    have h := ltTD_nonneg hw1 hw2
    rw [evalCertLtTD] at h
    omega
  have hHc : 2 * evalPoly ltTN (m : Int) ≤ 24 * evalPoly ltTD (m : Int) := by
    have h := ltH_nonneg hw1 hw2
    rw [evalCertLtH] at h
    omega
  have htn : ((evalPoly ltTN (m : Int)).toNat : Int) = evalPoly ltTN (m : Int) :=
    Int.toNat_of_nonneg hTN0
  have htd : ((evalPoly ltTD (m : Int)).toNat : Int) = evalPoly ltTD (m : Int) :=
    Int.toNat_of_nonneg (by omega)
  refine capUB22_of_int (by omega) (by omega) ?_
  rw [htn, htd]
  rw [evalCertLtLo] at hlo
  simp only [EUD, EUN, KF1, Sc] at hlo
  simp only [Int.natCast_mul]
  rw [show ((143418293695452518191953761862290000000000000000000000000000000 : Nat) : Int) = 143418293695452518191953761862290000000000000000000000000000000 from rfl,
      show ((9999999999999999999999999996599 : Nat) : Int) = 9999999999999999999999999996599 from rfl]
  have eS : expNumI 22 (evalPoly ltTN (m : Int)) (evalPoly ltTD (m : Int)) *
      (23 * evalPoly ltTD (m : Int)) =
      23 * (expNumI 22 (evalPoly ltTN (m : Int)) (evalPoly ltTD (m : Int)) *
        evalPoly ltTD (m : Int)) := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [eS]
  have eL : (23 * (expNumI 22 (evalPoly ltTN (m : Int)) (evalPoly ltTD (m : Int)) *
      evalPoly ltTD (m : Int)) + 2 * evalPoly ltTN (m : Int) ^ 23) *
      ((m : Int) * 9999999999999999999999999996599) =
      9999999999999999999999999996599 *
        ((m : Int) * (23 * (expNumI 22 (evalPoly ltTN (m : Int)) (evalPoly ltTD (m : Int)) *
          evalPoly ltTD (m : Int)) + 2 * evalPoly ltTN (m : Int) ^ 23)) := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [eL]
  generalize hgMS : (m : Int) * (23 * (expNumI 22 (evalPoly ltTN (m : Int))
    (evalPoly ltTD (m : Int)) * evalPoly ltTD (m : Int)) +
      2 * evalPoly ltTN (m : Int) ^ 23) = MS at hlo ⊢
  generalize hgT23 : evalPoly ltTD (m : Int) ^ 23 = T23 at hlo ⊢
  omega

/-! ## Sign of the pipeline value on each branch -/

theorem x1_nonneg_ge {m : Nat} (h1 : Sc + 46 ≤ m) (h2 : m < MHI) :
    0 ≤ toInt (x1W (zWord m)) := by
  have hw1 : (14341829369545251819195376186275 : Int) ≤ (m : Int) := by
    simp only [Sc] at h1; omega
  have hw2 : (m : Int) ≤ 20282409603651670423947251286015 := by
    simp only [MHI] at h2; omega
  have hTN0 : 0 ≤ evalPoly geTN2b (m : Int) := geTN2_nonneg hw1 hw2
  have hTD1 : 1 ≤ evalPoly geTD2b (m : Int) := by
    have h := geTD2_nonneg hw1 hw2
    rw [evalCertGeTD2] at h
    omega
  have hbr := bracket_ge_lo h1 h2
  rcases Int.lt_or_le (toInt (x1W (zWord m))) 0 with hneg | h
  · exfalso
    have hnn : 0 ≤ evalPoly geTN2b (m : Int) * 2 ^ 99 :=
      Int.mul_nonneg hTN0 (by omega)
    have hm : evalPoly geTD2b (m : Int) * toInt (x1W (zWord m)) ≤
        1 * toInt (x1W (zWord m)) :=
      mul_le_mul_right_nonpos hTD1 (by omega)
    have e1 : evalPoly geTD2b (m : Int) * toInt (x1W (zWord m)) =
        toInt (x1W (zWord m)) * evalPoly geTD2b (m : Int) := Int.mul_comm _ _
    have e2 : (1 : Int) * toInt (x1W (zWord m)) = toInt (x1W (zWord m)) :=
      Int.one_mul _
    generalize hg1 : evalPoly geTN2b (m : Int) * 2 ^ 99 = A at hbr hnn
    generalize hg2 : toInt (x1W (zWord m)) * evalPoly geTD2b (m : Int) = B at hbr e1
    generalize hg3 : evalPoly geTD2b (m : Int) * toInt (x1W (zWord m)) = C at hm e1
    omega
  · exact h

theorem x1_nonpos_lt {m : Nat} (h1 : MLO ≤ m) (h2 : m + 46 ≤ Sc) :
    toInt (x1W (zWord m)) ≤ 0 := by
  have hw1 : (10141204801825835211973625643008 : Int) ≤ (m : Int) := by
    simp only [MLO] at h1; omega
  have hw2 : (m : Int) ≤ 14341829369545251819195376186183 := by
    simp only [Sc] at h2; omega
  have hTN0 : 0 ≤ evalPoly ltTN2b (m : Int) := ltTN2_nonneg hw1 hw2
  have hTD1 : 1 ≤ evalPoly ltTD2b (m : Int) := by
    have h := ltTD2_nonneg hw1 hw2
    rw [evalCertLtTD2] at h
    omega
  have hbr := bracket_lt_lo h1 h2
  rcases Int.lt_or_le 0 (toInt (x1W (zWord m))) with hpos | h
  · exfalso
    have hnn : 0 ≤ evalPoly ltTN2b (m : Int) * 2 ^ 99 :=
      Int.mul_nonneg hTN0 (by omega)
    have hm : evalPoly ltTD2b (m : Int) * -toInt (x1W (zWord m)) ≤
        1 * -toInt (x1W (zWord m)) :=
      mul_le_mul_right_nonpos hTD1 (by omega)
    have e1 : evalPoly ltTD2b (m : Int) * -toInt (x1W (zWord m)) =
        -toInt (x1W (zWord m)) * evalPoly ltTD2b (m : Int) := Int.mul_comm _ _
    generalize hg1 : evalPoly ltTN2b (m : Int) * 2 ^ 99 = A at hbr hnn
    generalize hg2 : -toInt (x1W (zWord m)) * evalPoly ltTD2b (m : Int) = B at hbr e1
    generalize hg3 : evalPoly ltTD2b (m : Int) * -toInt (x1W (zWord m)) = C at hm e1
    omega
  · exact h

/-! ## Caps at the pipeline value over the common denominator 10^27 · 2^99 -/

theorem x1capGeUp {m : Nat} (h1 : Sc + 46 ≤ m) (h2 : m < MHI)
    (hup : 0 ≤ evalPoly certGeUp (m : Int)) :
    capUB ((toInt (x1W (zWord m))).toNat * 1000000000000000000000000000)
      633825300114114700748351602688000000000000000000000000000
      (m * 10000000000000000000000000003401)
      143418293695452518191953761862290000000000000000000000000000000 := by
  have hw1 : (14341829369545251819195376186275 : Int) ≤ (m : Int) := by
    simp only [Sc] at h1; omega
  have hw2 : (m : Int) ≤ 20282409603651670423947251286015 := by
    simp only [MHI] at h2; omega
  have hTN0 : 0 ≤ evalPoly geTN (m : Int) := geTN_nonneg hw1 hw2
  have hTD1 : 1 ≤ evalPoly geTD (m : Int) := by
    have h := geTD_nonneg hw1 hw2
    rw [evalCertGeTD] at h
    omega
  refine capUB_arg (q' := (evalPoly geTD (m : Int)).toNat) (by omega) ?_
    (capGeUp h1 h2 hup)
  rcases Int.lt_or_le (toInt (x1W (zWord m))) 0 with hneg | hpos
  · have h0 : (toInt (x1W (zWord m))).toNat = 0 := by omega
    rw [h0]
    omega
  · have hX1n : ((toInt (x1W (zWord m))).toNat : Int) = toInt (x1W (zWord m)) :=
      Int.toNat_of_nonneg hpos
    have htd : ((evalPoly geTD (m : Int)).toNat : Int) = evalPoly geTD (m : Int) :=
      Int.toNat_of_nonneg (by omega)
    have htn : ((evalPoly geTN (m : Int)).toNat : Int) = evalPoly geTN (m : Int) :=
      Int.toNat_of_nonneg hTN0
    refine Int.ofNat_le.mp ?_
    simp only [Int.natCast_mul]
    rw [show ((1000000000000000000000000000 : Nat) : Int) =
        1000000000000000000000000000 from rfl,
      show ((633825300114114700748351602688000000000000000000000000000 : Nat) : Int) =
        633825300114114700748351602688000000000000000000000000000 from rfl,
      hX1n, htd, htn]
    have hbr := bracket_ge_up h1 h2
    have c1 := mul_le_mul_right_nonneg hbr
      (show (0 : Int) ≤ 1000000000000000000000000000 by omega)
    have e1 : toInt (x1W (zWord m)) * 1000000000000000000000000000 *
        evalPoly geTD (m : Int) =
        toInt (x1W (zWord m)) * evalPoly geTD (m : Int) * 1000000000000000000000000000 := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    have e2 : evalPoly geTN (m : Int) * 2 ^ 99 * 1000000000000000000000000000 =
        evalPoly geTN (m : Int) *
          633825300114114700748351602688000000000000000000000000000 := by
      rw [Int.mul_assoc, show (2 : Int) ^ 99 * 1000000000000000000000000000 =
        633825300114114700748351602688000000000000000000000000000 from by decide]
    generalize hp1 : toInt (x1W (zWord m)) * evalPoly geTD (m : Int) *
      1000000000000000000000000000 = A at c1 e1
    generalize hp2 : toInt (x1W (zWord m)) * 1000000000000000000000000000 *
      evalPoly geTD (m : Int) = B at e1 ⊢
    generalize hp3 : evalPoly geTN (m : Int) * 2 ^ 99 *
      1000000000000000000000000000 = C at c1 e2
    generalize hp4 : evalPoly geTN (m : Int) *
      633825300114114700748351602688000000000000000000000000000 = D at e2 ⊢
    clear hp1 hp2 hp3 hp4 hbr hpos hX1n htd htn hTN0 hTD1 hw1 hw2 hup h1 h2
    omega

theorem x1capGeLo {m : Nat} (h1 : Sc + 46 ≤ m) (h2 : m < MHI)
    (hlo : 0 ≤ evalPoly certGeLo (m : Int)) :
    capLB ((toInt (x1W (zWord m))).toNat * 1000000000000000000000000000)
      633825300114114700748351602688000000000000000000000000000
      (m * 9999999999999999999999999996599)
      143418293695452518191953761862290000000000000000000000000000000 := by
  have hw1 : (14341829369545251819195376186275 : Int) ≤ (m : Int) := by
    simp only [Sc] at h1; omega
  have hw2 : (m : Int) ≤ 20282409603651670423947251286015 := by
    simp only [MHI] at h2; omega
  have hTN0 : 0 ≤ evalPoly geTN2b (m : Int) := geTN2_nonneg hw1 hw2
  have hTD1 : 1 ≤ evalPoly geTD2b (m : Int) := by
    have h := geTD2_nonneg hw1 hw2
    rw [evalCertGeTD2] at h
    omega
  refine capLB_arg (q' := (evalPoly geTD2b (m : Int)).toNat) (by omega) ?_
    (capGeLo h1 h2 hlo)
  have hpos := x1_nonneg_ge h1 h2
  have hX1n : ((toInt (x1W (zWord m))).toNat : Int) = toInt (x1W (zWord m)) :=
    Int.toNat_of_nonneg hpos
  have htd : ((evalPoly geTD2b (m : Int)).toNat : Int) = evalPoly geTD2b (m : Int) :=
    Int.toNat_of_nonneg (by omega)
  have htn : ((evalPoly geTN2b (m : Int)).toNat : Int) = evalPoly geTN2b (m : Int) :=
    Int.toNat_of_nonneg hTN0
  refine Int.ofNat_le.mp ?_
  simp only [Int.natCast_mul]
  rw [show ((1000000000000000000000000000 : Nat) : Int) =
      1000000000000000000000000000 from rfl,
    show ((633825300114114700748351602688000000000000000000000000000 : Nat) : Int) =
      633825300114114700748351602688000000000000000000000000000 from rfl,
    hX1n, htd, htn]
  have hbr := bracket_ge_lo h1 h2
  have c1 := mul_le_mul_right_nonneg hbr
    (show (0 : Int) ≤ 1000000000000000000000000000 by omega)
  have e1 : toInt (x1W (zWord m)) * 1000000000000000000000000000 *
      evalPoly geTD2b (m : Int) =
      toInt (x1W (zWord m)) * evalPoly geTD2b (m : Int) * 1000000000000000000000000000 := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have e2 : evalPoly geTN2b (m : Int) * 2 ^ 99 * 1000000000000000000000000000 =
      evalPoly geTN2b (m : Int) *
        633825300114114700748351602688000000000000000000000000000 := by
    rw [Int.mul_assoc, show (2 : Int) ^ 99 * 1000000000000000000000000000 =
      633825300114114700748351602688000000000000000000000000000 from by decide]
  generalize hp1 : toInt (x1W (zWord m)) * evalPoly geTD2b (m : Int) *
    1000000000000000000000000000 = A at c1 e1
  generalize hp2 : toInt (x1W (zWord m)) * 1000000000000000000000000000 *
    evalPoly geTD2b (m : Int) = B at e1 ⊢
  generalize hp3 : evalPoly geTN2b (m : Int) * 2 ^ 99 *
    1000000000000000000000000000 = C at c1 e2
  generalize hp4 : evalPoly geTN2b (m : Int) *
    633825300114114700748351602688000000000000000000000000000 = D at e2 ⊢
  clear hp1 hp2 hp3 hp4 hbr hpos hX1n htd htn hTN0 hTD1 hw1 hw2 hlo h1 h2
  omega

theorem x1capLtUp {m : Nat} (h1 : MLO ≤ m) (h2 : m + 46 ≤ Sc)
    (hup : 0 ≤ evalPoly certLtUp (m : Int)) :
    capLB ((-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000)
      633825300114114700748351602688000000000000000000000000000
      143418293695452518191953761862290000000000000000000000000000000
      (m * 10000000000000000000000000003401) := by
  have hw1 : (10141204801825835211973625643008 : Int) ≤ (m : Int) := by
    simp only [MLO] at h1; omega
  have hw2 : (m : Int) ≤ 14341829369545251819195376186183 := by
    simp only [Sc] at h2; omega
  have hTN0 : 0 ≤ evalPoly ltTN2b (m : Int) := ltTN2_nonneg hw1 hw2
  have hTD1 : 1 ≤ evalPoly ltTD2b (m : Int) := by
    have h := ltTD2_nonneg hw1 hw2
    rw [evalCertLtTD2] at h
    omega
  refine capLB_arg (q' := (evalPoly ltTD2b (m : Int)).toNat) (by omega) ?_
    (capLtUp h1 h2 hup)
  have hneg := x1_nonpos_lt h1 h2
  have hX1n : (((-toInt (x1W (zWord m))).toNat : Nat) : Int) = -toInt (x1W (zWord m)) :=
    Int.toNat_of_nonneg (by omega)
  have htd : ((evalPoly ltTD2b (m : Int)).toNat : Int) = evalPoly ltTD2b (m : Int) :=
    Int.toNat_of_nonneg (by omega)
  have htn : ((evalPoly ltTN2b (m : Int)).toNat : Int) = evalPoly ltTN2b (m : Int) :=
    Int.toNat_of_nonneg hTN0
  refine Int.ofNat_le.mp ?_
  simp only [Int.natCast_mul]
  rw [show ((1000000000000000000000000000 : Nat) : Int) =
      1000000000000000000000000000 from rfl,
    show ((633825300114114700748351602688000000000000000000000000000 : Nat) : Int) =
      633825300114114700748351602688000000000000000000000000000 from rfl,
    hX1n, htd, htn]
  have hbr := bracket_lt_lo h1 h2
  have c1 := mul_le_mul_right_nonneg hbr
    (show (0 : Int) ≤ 1000000000000000000000000000 by omega)
  have e1 : -toInt (x1W (zWord m)) * 1000000000000000000000000000 *
      evalPoly ltTD2b (m : Int) =
      -toInt (x1W (zWord m)) * evalPoly ltTD2b (m : Int) * 1000000000000000000000000000 := by
    simp only [Int.mul_assoc, Int.mul_comm]
  have e2 : evalPoly ltTN2b (m : Int) * 2 ^ 99 * 1000000000000000000000000000 =
      evalPoly ltTN2b (m : Int) *
        633825300114114700748351602688000000000000000000000000000 := by
    rw [Int.mul_assoc, show (2 : Int) ^ 99 * 1000000000000000000000000000 =
      633825300114114700748351602688000000000000000000000000000 from by decide]
  generalize hp1 : -toInt (x1W (zWord m)) * evalPoly ltTD2b (m : Int) *
    1000000000000000000000000000 = A at c1 e1
  generalize hp2 : -toInt (x1W (zWord m)) * 1000000000000000000000000000 *
    evalPoly ltTD2b (m : Int) = B at e1 ⊢
  generalize hp3 : evalPoly ltTN2b (m : Int) * 2 ^ 99 *
    1000000000000000000000000000 = C at c1 e2
  generalize hp4 : evalPoly ltTN2b (m : Int) *
    633825300114114700748351602688000000000000000000000000000 = D at e2 ⊢
  clear hp1 hp2 hp3 hp4 hbr hneg hX1n htd htn hTN0 hTD1 hw1 hw2 hup h1 h2
  omega

theorem x1capLtLo {m : Nat} (h1 : MLO ≤ m) (h2 : m + 46 ≤ Sc)
    (hlo : 0 ≤ evalPoly certLtLo (m : Int)) :
    capUB ((-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000)
      633825300114114700748351602688000000000000000000000000000
      143418293695452518191953761862290000000000000000000000000000000
      (m * 9999999999999999999999999996599) := by
  have hw1 : (10141204801825835211973625643008 : Int) ≤ (m : Int) := by
    simp only [MLO] at h1; omega
  have hw2 : (m : Int) ≤ 14341829369545251819195376186183 := by
    simp only [Sc] at h2; omega
  have hTN0 : 0 ≤ evalPoly ltTN (m : Int) := ltTN_nonneg hw1 hw2
  have hTD1 : 1 ≤ evalPoly ltTD (m : Int) := by
    have h := ltTD_nonneg hw1 hw2
    rw [evalCertLtTD] at h
    omega
  refine capUB_arg (q' := (evalPoly ltTD (m : Int)).toNat) (by omega) ?_
    (capLtLo h1 h2 hlo)
  have hX1n : (((-toInt (x1W (zWord m))).toNat : Nat) : Int) = -toInt (x1W (zWord m)) :=
    Int.toNat_of_nonneg (by have := x1_nonpos_lt h1 h2; omega)
  have htd : ((evalPoly ltTD (m : Int)).toNat : Int) = evalPoly ltTD (m : Int) :=
    Int.toNat_of_nonneg (by omega)
  have htn : ((evalPoly ltTN (m : Int)).toNat : Int) = evalPoly ltTN (m : Int) :=
    Int.toNat_of_nonneg hTN0
  refine Int.ofNat_le.mp ?_
  simp only [Int.natCast_mul]
  rw [show ((1000000000000000000000000000 : Nat) : Int) =
      1000000000000000000000000000 from rfl,
    show ((633825300114114700748351602688000000000000000000000000000 : Nat) : Int) =
      633825300114114700748351602688000000000000000000000000000 from rfl,
    hX1n, htd, htn]
  have hbr := bracket_lt_up h1 h2
  have c1 := mul_le_mul_right_nonneg hbr
    (show (0 : Int) ≤ 1000000000000000000000000000 by omega)
  have e1 : -toInt (x1W (zWord m)) * 1000000000000000000000000000 *
      evalPoly ltTD (m : Int) =
      -toInt (x1W (zWord m)) * evalPoly ltTD (m : Int) * 1000000000000000000000000000 := by
    simp only [Int.mul_assoc, Int.mul_comm]
  have e2 : evalPoly ltTN (m : Int) * 2 ^ 99 * 1000000000000000000000000000 =
      evalPoly ltTN (m : Int) *
        633825300114114700748351602688000000000000000000000000000 := by
    rw [Int.mul_assoc, show (2 : Int) ^ 99 * 1000000000000000000000000000 =
      633825300114114700748351602688000000000000000000000000000 from by decide]
  generalize hp1 : -toInt (x1W (zWord m)) * evalPoly ltTD (m : Int) *
    1000000000000000000000000000 = A at c1 e1
  generalize hp2 : -toInt (x1W (zWord m)) * 1000000000000000000000000000 *
    evalPoly ltTD (m : Int) = B at e1 ⊢
  generalize hp3 : evalPoly ltTN (m : Int) * 2 ^ 99 *
    1000000000000000000000000000 = C at c1 e2
  generalize hp4 : evalPoly ltTN (m : Int) *
    633825300114114700748351602688000000000000000000000000000 = D at e2 ⊢
  clear hp1 hp2 hp3 hp4 hbr hX1n htd htn hTN0 hTD1 hw1 hw2 hlo h1 h2
  omega

end LnFloorCert
