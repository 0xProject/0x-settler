/-
  Ceiling cube root for 512-bit values.
-/
import Mathlib.Tactic.Ring
import FormalYul.Preservation
import CbrtProof.CbrtCorrect

open FormalYul

private theorem cube_expand_aux (m : Nat) :
    (m + 1) * (m + 1) * (m + 1) = m * m * m + 3 * m * m + 3 * m + 1 := by
  ring_nf

/-- 512-bit ceiling cube root. -/
noncomputable def cbrtUp512 (x : Nat) : Nat :=
  let r := icbrt x
  if r * r * r < x then r + 1 else r

/-- cbrtUp512 is the ceiling cbrt: x ≤ r³ and r is minimal. -/
theorem cbrtUp512_correct (x : Nat) (_hx : x < 2 ^ 512) :
    let r := cbrtUp512 x
    x ≤ r * r * r ∧ ∀ y, x ≤ y * y * y → r ≤ y := by
  simp only
  have hs_lo : icbrt x * icbrt x * icbrt x ≤ x := icbrt_cube_le x
  have hs_hi : x < (icbrt x + 1) * (icbrt x + 1) * (icbrt x + 1) := icbrt_lt_succ_cube x
  unfold cbrtUp512
  simp only
  by_cases hlt : icbrt x * icbrt x * icbrt x < x
  · -- s³ < x: ceiling is s + 1
    simp [hlt]
    exact ⟨by omega, fun y hy => by
      suffices h : ¬(y < icbrt x + 1) by omega
      intro hc
      have hc' : y ≤ icbrt x := by omega
      have := cube_monotone hc'; omega⟩
  · -- s³ = x: ceiling is s
    simp [hlt]
    have hseq : icbrt x * icbrt x * icbrt x = x := by omega
    exact ⟨by omega, fun y hy => by
      suffices h : ¬(y < icbrt x) by omega
      intro hc
      have hc' : y ≤ icbrt x - 1 := by omega
      have h1 := cube_monotone hc'
      have h2 : 0 < icbrt x := by omega
      have h3 := cube_expand_aux (icbrt x - 1)
      have h4 : (icbrt x - 1) + 1 = icbrt x := by omega
      rw [h4] at h3
      omega⟩

theorem gt512_correct (xHi xLo sqHi sqLo : Nat)
    (hxHi : xHi < WORD_MOD) (hxLo : xLo < WORD_MOD)
    (hsqHi : sqHi < WORD_MOD) (hsqLo : sqLo < WORD_MOD) :
    let cmp := evmOr (evmGt sqHi xHi)
      (evmAnd (evmEq sqHi xHi) (evmGt sqLo xLo))
    (cmp ≠ 0) ↔ (sqHi * WORD_MOD + sqLo > xHi * WORD_MOD + xLo) := by
  simp only
  rw [FormalYul.Preservation.evmGt_eq_of_lt sqHi xHi hsqHi hxHi,
    FormalYul.Preservation.evmEq_eq_of_lt sqHi xHi hsqHi hxHi,
    FormalYul.Preservation.evmGt_eq_of_lt sqLo xLo hsqLo hxLo]
  by_cases hgt : xHi < sqHi
  · have hneq : ¬sqHi = xHi := by omega
    simp only [hgt, ite_true, hneq, ite_false]
    have hor_nz : ∀ v, evmOr 1 (evmAnd 0 v) ≠ 0 := by
      intro v
      unfold evmOr evmAnd u256 WORD_MOD
      simp (config := { decide := true })
    constructor
    · intro _
      have h1 : xHi * WORD_MOD + WORD_MOD ≤ sqHi * WORD_MOD := by
        have := Nat.mul_le_mul_right WORD_MOD hgt
        rwa [Nat.succ_mul] at this
      omega
    · intro _
      exact hor_nz _
  · by_cases heq : sqHi = xHi
    · subst heq
      simp only [Nat.lt_irrefl, ite_false, ite_true]
      by_cases hgtLo : xLo < sqLo
      · simp only [hgtLo, ite_true]
        constructor
        · intro _
          omega
        · intro _
          unfold evmOr evmAnd u256 WORD_MOD
          simp (config := { decide := true })
      · simp only [hgtLo, ite_false]
        have hor_z : evmOr 0 (evmAnd 1 0) = 0 := by
          unfold evmOr evmAnd u256 WORD_MOD
          simp (config := { decide := true })
        constructor
        · intro h
          exact absurd hor_z h
        · intro h
          omega
    · have hlt : sqHi < xHi := by omega
      have hng : ¬xHi < sqHi := by omega
      simp only [hng, ite_false, heq, ite_false]
      have hor_z : ∀ v, evmOr 0 (evmAnd 0 v) = 0 := by
        intro v
        unfold evmOr evmAnd u256 WORD_MOD
        simp (config := { decide := true })
      constructor
      · intro h
        exact absurd (hor_z _) h
      · intro h
        have h1 : sqHi * WORD_MOD + WORD_MOD ≤ xHi * WORD_MOD := by
          have := Nat.mul_le_mul_right WORD_MOD hlt
          rwa [Nat.succ_mul] at this
        omega

theorem gt512_01 (xHi xLo sqHi sqLo : Nat)
    (hxHi : xHi < WORD_MOD) (hxLo : xLo < WORD_MOD)
    (hsqHi : sqHi < WORD_MOD) (hsqLo : sqLo < WORD_MOD) :
    let cmp := evmOr (evmGt sqHi xHi)
      (evmAnd (evmEq sqHi xHi) (evmGt sqLo xLo))
    cmp = 0 ∨ cmp = 1 :=
  FormalYul.Preservation.evmOr_01 _ _
    (FormalYul.Preservation.evmGt_01 _ _ hsqHi hxHi)
    (FormalYul.Preservation.evmAnd_01 _ _
      (FormalYul.Preservation.evmEq_01 _ _ hsqHi hxHi)
      (FormalYul.Preservation.evmGt_01 _ _ hsqLo hxLo))

theorem lt512_correct (xHi xLo sqHi sqLo : Nat)
    (hxHi : xHi < WORD_MOD) (hxLo : xLo < WORD_MOD)
    (hsqHi : sqHi < WORD_MOD) (hsqLo : sqLo < WORD_MOD) :
    let cmp := evmOr (evmLt sqHi xHi)
      (evmAnd (evmEq sqHi xHi) (evmLt sqLo xLo))
    (cmp ≠ 0) ↔ (sqHi * WORD_MOD + sqLo < xHi * WORD_MOD + xLo) := by
  simp only
  have hltHi : evmLt sqHi xHi = evmGt xHi sqHi := by
    rw [FormalYul.Preservation.evmLt_eq_of_lt sqHi xHi hsqHi hxHi,
      FormalYul.Preservation.evmGt_eq_of_lt xHi sqHi hxHi hsqHi]
  have heqComm : evmEq sqHi xHi = evmEq xHi sqHi := by
    rw [FormalYul.Preservation.evmEq_eq_of_lt sqHi xHi hsqHi hxHi,
      FormalYul.Preservation.evmEq_eq_of_lt xHi sqHi hxHi hsqHi]
    by_cases h : sqHi = xHi
    · simp [h]
    · simp [h, Ne.symm h]
  have hltLo : evmLt sqLo xLo = evmGt xLo sqLo := by
    rw [FormalYul.Preservation.evmLt_eq_of_lt sqLo xLo hsqLo hxLo,
      FormalYul.Preservation.evmGt_eq_of_lt xLo sqLo hxLo hsqLo]
  rw [hltHi, heqComm, hltLo]
  have hgt := gt512_correct sqHi sqLo xHi xLo hsqHi hsqLo hxHi hxLo
  simp only at hgt
  exact hgt

theorem lt512_01 (xHi xLo sqHi sqLo : Nat)
    (hxHi : xHi < WORD_MOD) (hxLo : xLo < WORD_MOD)
    (hsqHi : sqHi < WORD_MOD) (hsqLo : sqLo < WORD_MOD) :
    let cmp := evmOr (evmLt sqHi xHi)
      (evmAnd (evmEq sqHi xHi) (evmLt sqLo xLo))
    cmp = 0 ∨ cmp = 1 :=
  FormalYul.Preservation.evmOr_01 _ _
    (FormalYul.Preservation.evmLt_01 _ _ hsqHi hxHi)
    (FormalYul.Preservation.evmAnd_01 _ _
      (FormalYul.Preservation.evmEq_01 _ _ hsqHi hxHi)
      (FormalYul.Preservation.evmLt_01 _ _ hsqLo hxLo))

theorem mul512_high_word_general (a b : Nat) (ha : a < WORD_MOD) (hb : b < WORD_MOD) :
    let mm := evmMulmod a b (evmNot 0)
    let m := evmMul a b
    evmSub (evmSub mm m) (evmLt mm m) = a * b / WORD_MOD := by
  simp only
  have hNot0 : evmNot 0 = WORD_MOD - 1 := by
    simpa using
      FormalYul.Preservation.evmNot_eq_of_lt 0 FormalYul.Preservation.zero_lt_word
  have hWM1Pos : (0 : Nat) < WORD_MOD - 1 := by
    unfold WORD_MOD
    omega
  have hWM1Lt : WORD_MOD - 1 < WORD_MOD := by
    unfold WORD_MOD
    omega
  have hmm : evmMulmod a b (evmNot 0) = (a * b) % (WORD_MOD - 1) := by
    rw [hNot0]
    exact FormalYul.Preservation.evmMulmod_eq_of_lt a b (WORD_MOD - 1)
      ha hb hWM1Lt hWM1Pos
  have hm : evmMul a b = (a * b) % WORD_MOD :=
    FormalYul.Preservation.evmMul_eq_mod_of_lt a b ha hb
  rw [hmm, hm]
  have hqBound : a * b / WORD_MOD < WORD_MOD := by
    have : a * b < WORD_MOD * WORD_MOD :=
      Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt ha) hb (by unfold WORD_MOD; omega)
    exact Nat.div_lt_of_lt_mul this
  have hloBound : a * b % WORD_MOD < WORD_MOD := Nat.mod_lt _ (by unfold WORD_MOD; omega)
  have hhiEq :
      (a * b) % (WORD_MOD - 1) =
        (a * b / WORD_MOD + a * b % WORD_MOD) % (WORD_MOD - 1) := by
    have hqW :
        a * b / WORD_MOD * WORD_MOD =
          (WORD_MOD - 1) * (a * b / WORD_MOD) + a * b / WORD_MOD := by
      have hsc := Nat.sub_add_cancel
        (Nat.one_le_of_lt (show 1 < WORD_MOD from by unfold WORD_MOD; omega))
      have h := Nat.mul_add (a * b / WORD_MOD) (WORD_MOD - 1) 1
      rw [hsc, Nat.mul_one] at h
      rw [h, Nat.mul_comm (a * b / WORD_MOD) (WORD_MOD - 1)]
    have habEq :
        a * b =
          (WORD_MOD - 1) * (a * b / WORD_MOD) +
            (a * b / WORD_MOD + a * b % WORD_MOD) := by
      have hdiv := Nat.div_add_mod (a * b) WORD_MOD
      rw [Nat.mul_comm] at hdiv
      omega
    have step := Nat.mul_add_mod (WORD_MOD - 1) (a * b / WORD_MOD)
      (a * b / WORD_MOD + a * b % WORD_MOD)
    rw [← habEq] at step
    exact step
  by_cases hcase : a * b / WORD_MOD + a * b % WORD_MOD < WORD_MOD - 1
  · have hhiVal :
        (a * b) % (WORD_MOD - 1) = a * b / WORD_MOD + a * b % WORD_MOD := by
      rw [hhiEq, Nat.mod_eq_of_lt hcase]
    have hhiWm : (a * b) % (WORD_MOD - 1) < WORD_MOD := by omega
    have hge : a * b % WORD_MOD ≤ (a * b) % (WORD_MOD - 1) := by
      rw [hhiVal]
      exact Nat.le_add_left _ _
    have hltEq : evmLt ((a * b) % (WORD_MOD - 1)) (a * b % WORD_MOD) = 0 := by
      rw [FormalYul.Preservation.evmLt_eq_of_lt _ _ hhiWm hloBound]
      exact if_neg (Nat.not_lt.mpr hge)
    rw [hltEq]
    have hsub1 :
        evmSub ((a * b) % (WORD_MOD - 1)) (a * b % WORD_MOD) =
          (a * b) % (WORD_MOD - 1) - a * b % WORD_MOD :=
      FormalYul.Preservation.evmSub_eq_of_le _ _ hhiWm hge
    rw [hsub1]
    have hqEq :
        (a * b) % (WORD_MOD - 1) - a * b % WORD_MOD = a * b / WORD_MOD := by
      omega
    rw [hqEq]
    exact FormalYul.Preservation.evmSub_eq_of_le _ 0 hqBound (Nat.zero_le _)
  · have hcase' : WORD_MOD - 1 ≤ a * b / WORD_MOD + a * b % WORD_MOD :=
      Nat.not_lt.mp hcase
    have hqLe : a * b / WORD_MOD ≤ WORD_MOD - 2 := by
      have ha' : a ≤ WORD_MOD - 1 := by omega
      have hb' : b ≤ WORD_MOD - 1 := by omega
      have hab : a * b ≤ (WORD_MOD - 1) * (WORD_MOD - 1) := Nat.mul_le_mul ha' hb'
      have h1 : a * b / WORD_MOD ≤ (WORD_MOD - 1) * (WORD_MOD - 1) / WORD_MOD :=
        @Nat.div_le_div_right _ _ WORD_MOD hab
      suffices h : (WORD_MOD - 1) * (WORD_MOD - 1) / WORD_MOD = WORD_MOD - 2 by omega
      unfold WORD_MOD
      omega
    have hhiVal :
        (a * b) % (WORD_MOD - 1) =
          a * b / WORD_MOD + a * b % WORD_MOD - (WORD_MOD - 1) := by
      rw [hhiEq, Nat.mod_eq_sub_mod hcase', Nat.mod_eq_of_lt (by omega)]
    have hltLo : (a * b) % (WORD_MOD - 1) < a * b % WORD_MOD := by
      rw [hhiVal]
      omega
    have hhiWm : (a * b) % (WORD_MOD - 1) < WORD_MOD := by omega
    have hltEq : evmLt ((a * b) % (WORD_MOD - 1)) (a * b % WORD_MOD) = 1 := by
      rw [FormalYul.Preservation.evmLt_eq_of_lt _ _ hhiWm hloBound]
      exact if_pos hltLo
    rw [hltEq]
    have hsub1 :
        evmSub ((a * b) % (WORD_MOD - 1)) (a * b % WORD_MOD) =
          (a * b) % (WORD_MOD - 1) + WORD_MOD - a * b % WORD_MOD := by
      unfold evmSub u256
      simp [Nat.mod_eq_of_lt hhiWm, Nat.mod_eq_of_lt hloBound]
      exact Nat.mod_eq_of_lt (show
        (a * b) % (WORD_MOD - 1) + WORD_MOD - a * b % WORD_MOD < WORD_MOD by
          rw [hhiVal]
          omega)
    rw [hsub1]
    have hval :
        (a * b) % (WORD_MOD - 1) + WORD_MOD - a * b % WORD_MOD < WORD_MOD := by
      rw [hhiVal]
      omega
    have hsub2 :
        evmSub ((a * b) % (WORD_MOD - 1) + WORD_MOD - a * b % WORD_MOD) 1 =
          (a * b) % (WORD_MOD - 1) + WORD_MOD - a * b % WORD_MOD - 1 :=
      FormalYul.Preservation.evmSub_eq_of_le _ 1 hval (by
        rw [hhiVal]
        omega)
    rw [hsub2]
    rw [hhiVal]
    omega

theorem mul512_high_word (r : Nat) (hr : r < WORD_MOD) :
    let mm := evmMulmod r r (evmNot 0)
    let m := evmMul r r
    evmSub (evmSub mm m) (evmLt mm m) = r * r / WORD_MOD := by
  simpa using mul512_high_word_general r r hr hr

theorem mul512_low_word_general (a b : Nat) (ha : a < WORD_MOD) (hb : b < WORD_MOD) :
    evmMul a b = (a * b) % WORD_MOD :=
  FormalYul.Preservation.evmMul_eq_mod_of_lt a b ha hb

theorem mul512_low_word (r : Nat) (hr : r < WORD_MOD) :
    evmMul r r = r * r % WORD_MOD :=
  mul512_low_word_general r r hr hr

private theorem div_mul_le_mul_div (a b k : Nat) (hk : 0 < k) :
    a / k * b ≤ a * b / k := by
  have h1 : a / k * b * k ≤ a * b := by
    calc a / k * b * k
        = a / k * k * b := by rw [Nat.mul_assoc, Nat.mul_comm b k, ← Nat.mul_assoc]
      _ ≤ a * b := Nat.mul_le_mul_right b (Nat.div_mul_le_self a k)
  have h2 : a / k * b * k / k = a / k * b :=
    Nat.mul_div_cancel (a / k * b) hk
  calc a / k * b
      = a / k * b * k / k := h2.symm
    _ ≤ a * b / k := Nat.div_le_div_right h1

theorem cube512_correct (r : Nat) (hr : r < WORD_MOD)
    (hcube : r * r * r < WORD_MOD * WORD_MOD) :
    let mm1 := evmMulmod r r (evmNot 0)
    let r2Lo := evmMul r r
    let r2Hi := evmSub (evmSub mm1 r2Lo) (evmLt mm1 r2Lo)
    let mm2 := evmMulmod r2Lo r (evmNot 0)
    let r3Lo := evmMul r2Lo r
    let r3Hi := evmAdd (evmSub (evmSub mm2 r3Lo) (evmLt mm2 r3Lo)) (evmMul r2Hi r)
    r3Hi * WORD_MOD + r3Lo = r * r * r := by
  simp only
  have hWPos : (0 : Nat) < WORD_MOD := by
    unfold WORD_MOD
    omega
  have hR2Hi :
      evmSub (evmSub (evmMulmod r r (evmNot 0)) (evmMul r r))
        (evmLt (evmMulmod r r (evmNot 0)) (evmMul r r)) =
        r * r / WORD_MOD :=
    mul512_high_word r hr
  have hR2Lo : evmMul r r = (r * r) % WORD_MOD :=
    mul512_low_word r hr
  rw [hR2Hi, hR2Lo]
  have hPLt : (r * r) % WORD_MOD < WORD_MOD := Nat.mod_lt _ hWPos
  have hCubeHi :
      evmSub
        (evmSub (evmMulmod ((r * r) % WORD_MOD) r (evmNot 0))
          (evmMul ((r * r) % WORD_MOD) r))
        (evmLt (evmMulmod ((r * r) % WORD_MOD) r (evmNot 0))
          (evmMul ((r * r) % WORD_MOD) r)) =
        (r * r) % WORD_MOD * r / WORD_MOD :=
    mul512_high_word_general ((r * r) % WORD_MOD) r hPLt hr
  have hR3Lo : evmMul ((r * r) % WORD_MOD) r =
      ((r * r) % WORD_MOD * r) % WORD_MOD :=
    mul512_low_word_general ((r * r) % WORD_MOD) r hPLt hr
  rw [hCubeHi, hR3Lo]
  have hQLt : r * r / WORD_MOD < WORD_MOD :=
    Nat.div_lt_of_lt_mul (Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt hr) hr
      (by unfold WORD_MOD; omega))
  have hQrLt : r * r / WORD_MOD * r < WORD_MOD := by
    calc r * r / WORD_MOD * r
        ≤ r * r * r / WORD_MOD := div_mul_le_mul_div (r * r) r WORD_MOD hWPos
      _ < WORD_MOD := Nat.div_lt_of_lt_mul hcube
  have hevmMulHi : evmMul (r * r / WORD_MOD) r = r * r / WORD_MOD * r := by
    unfold evmMul u256
    simp [Nat.mod_eq_of_lt hQLt, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hQrLt]
  rw [hevmMulHi]
  have hR3Decomp :
      r * r * r = r * r / WORD_MOD * r * WORD_MOD + (r * r) % WORD_MOD * r := by
    have hEucl := Nat.div_add_mod (r * r) WORD_MOD
    calc r * r * r
        = (WORD_MOD * (r * r / WORD_MOD) + (r * r) % WORD_MOD) * r :=
          congrArg (· * r) hEucl.symm
      _ = WORD_MOD * (r * r / WORD_MOD) * r + (r * r) % WORD_MOD * r := Nat.add_mul _ _ r
      _ = r * r / WORD_MOD * WORD_MOD * r + (r * r) % WORD_MOD * r := by
          rw [Nat.mul_comm WORD_MOD (r * r / WORD_MOD)]
      _ = r * r / WORD_MOD * r * WORD_MOD + (r * r) % WORD_MOD * r := by
          rw [Nat.mul_assoc, Nat.mul_comm WORD_MOD r, ← Nat.mul_assoc]
  have hSumEq :
      (r * r) % WORD_MOD * r / WORD_MOD + r * r / WORD_MOD * r =
        r * r * r / WORD_MOD := by
    rw [hR3Decomp]
    rw [show
      r * r / WORD_MOD * r * WORD_MOD + (r * r) % WORD_MOD * r =
        (r * r) % WORD_MOD * r + r * r / WORD_MOD * r * WORD_MOD by omega]
    exact (Nat.add_mul_div_right ((r * r) % WORD_MOD * r)
      (r * r / WORD_MOD * r) hWPos).symm
  have hSumLt :
      (r * r) % WORD_MOD * r / WORD_MOD + r * r / WORD_MOD * r < WORD_MOD := by
    rw [hSumEq]
    exact Nat.div_lt_of_lt_mul hcube
  have hevmAdd : evmAdd ((r * r) % WORD_MOD * r / WORD_MOD) (r * r / WORD_MOD * r) =
      (r * r) % WORD_MOD * r / WORD_MOD + r * r / WORD_MOD * r :=
    FormalYul.Preservation.evmAdd_eq_of_lt _ _ (by omega) hQrLt hSumLt
  rw [hevmAdd]
  have hPrEucl := Nat.div_add_mod ((r * r) % WORD_MOD * r) WORD_MOD
  symm
  calc r * r * r
      = r * r / WORD_MOD * r * WORD_MOD + (r * r) % WORD_MOD * r := hR3Decomp
    _ = r * r / WORD_MOD * r * WORD_MOD
        + (WORD_MOD * ((r * r) % WORD_MOD * r / WORD_MOD)
          + (r * r) % WORD_MOD * r % WORD_MOD) := by
        rw [hPrEucl]
    _ = (r * r) % WORD_MOD * r / WORD_MOD * WORD_MOD
        + r * r / WORD_MOD * r * WORD_MOD
        + (r * r) % WORD_MOD * r % WORD_MOD := by
        rw [Nat.mul_comm WORD_MOD ((r * r) % WORD_MOD * r / WORD_MOD)]
        omega
    _ = ((r * r) % WORD_MOD * r / WORD_MOD + r * r / WORD_MOD * r) * WORD_MOD
        + (r * r) % WORD_MOD * r % WORD_MOD := by
        rw [← Nat.add_mul]

theorem cbrt512_floorCorrection_correct (xHi xLo r : Nat)
    (hxHi : xHi < WORD_MOD) (hxLo : xLo < WORD_MOD)
    (hr : r < WORD_MOD) (hcube : r * r * r < WORD_MOD * WORD_MOD)
    (hwithin :
      icbrt (xHi * WORD_MOD + xLo) ≤ r ∧
        r ≤ icbrt (xHi * WORD_MOD + xLo) + 1) :
    let r2Lo := evmMul r r
    let mm1 := evmMulmod r r (evmNot 0)
    let r2Hi := evmSub (evmSub mm1 r2Lo) (evmLt mm1 r2Lo)
    let mm2 := evmMulmod r2Lo r (evmNot 0)
    let r3Lo := evmMul r2Lo r
    let r3Hi := evmAdd (evmSub (evmSub mm2 r3Lo) (evmLt mm2 r3Lo)) (evmMul r2Hi r)
    let cmp := evmOr (evmGt r3Hi xHi) (evmAnd (evmEq r3Hi xHi) (evmGt r3Lo xLo))
    evmSub r cmp = icbrt (xHi * WORD_MOD + xLo) := by
  simp only
  let r2Lo := evmMul r r
  let mm1 := evmMulmod r r (evmNot 0)
  let r2Hi := evmSub (evmSub mm1 r2Lo) (evmLt mm1 r2Lo)
  let mm2 := evmMulmod r2Lo r (evmNot 0)
  let r3Lo := evmMul r2Lo r
  let r3Hi := evmAdd (evmSub (evmSub mm2 r3Lo) (evmLt mm2 r3Lo)) (evmMul r2Hi r)
  let cmp := evmOr (evmGt r3Hi xHi) (evmAnd (evmEq r3Hi xHi) (evmGt r3Lo xLo))
  have hcubeEq : r3Hi * WORD_MOD + r3Lo = r * r * r := by
    simpa [r2Lo, mm1, r2Hi, mm2, r3Lo, r3Hi] using cube512_correct r hr hcube
  have hr3Lo : r3Lo < WORD_MOD := by
    exact FormalYul.Preservation.evmMul_lt_WORD_MOD _ _
  have hr3Hi : r3Hi < WORD_MOD := by
    exact FormalYul.Preservation.evmAdd_lt_WORD_MOD _ _
  have hcmp01 : cmp = 0 ∨ cmp = 1 := by
    simpa [cmp] using gt512_01 xHi xLo r3Hi r3Lo hxHi hxLo hr3Hi hr3Lo
  have hcmpIff : (cmp ≠ 0) ↔ (r * r * r > xHi * WORD_MOD + xLo) := by
    have hgt := gt512_correct xHi xLo r3Hi r3Lo hxHi hxLo hr3Hi hr3Lo
    simp only at hgt
    rw [hcubeEq] at hgt
    simpa [cmp] using hgt
  change evmSub r cmp = icbrt (xHi * WORD_MOD + xLo)
  have hrCases :
      r = icbrt (xHi * WORD_MOD + xLo) ∨
        r = icbrt (xHi * WORD_MOD + xLo) + 1 := by
    omega
  rcases hrCases with hrEq | hrEq
  · have hNotGt : ¬(r * r * r > xHi * WORD_MOD + xLo) := by
      rw [hrEq]
      exact Nat.not_lt.mpr (icbrt_cube_le (xHi * WORD_MOD + xLo))
    have hcmpZero : cmp = 0 := by
      rcases hcmp01 with h | h
      · exact h
      · exfalso
        exact hNotGt (hcmpIff.mp (by omega))
    rw [hcmpZero, FormalYul.Preservation.evmSub_eq_of_le _ 0 hr (Nat.zero_le _)]
    exact hrEq
  · have hGt : r * r * r > xHi * WORD_MOD + xLo := by
      rw [hrEq]
      exact icbrt_lt_succ_cube (xHi * WORD_MOD + xLo)
    have hcmpOne : cmp = 1 := by
      rcases hcmp01 with h | h
      · exfalso
        have := hcmpIff.mpr hGt
        omega
      · exact h
    rw [hcmpOne, FormalYul.Preservation.evmSub_eq_of_le _ 1 hr (by rw [hrEq]; omega)]
    rw [hrEq]
    omega
