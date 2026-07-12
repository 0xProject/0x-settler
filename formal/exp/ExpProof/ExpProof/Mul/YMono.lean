import ExpProof.Mul.XMono

/-!
# `mulExpRay` monotonicity in the multiplier

At a fixed exponent the kernel magnitude is nondecreasing in the multiplier's magnitude, by a
unit-step induction in pure word arithmetic. A unit step in the magnitude either keeps the
headroom shift — the scale grows by one headroom unit and the same-shift floor is monotone — or
drops it by exactly one bit, where the doubled new scale exceeds the old one by exactly `2^S`
(`2·(a+1)·2^(S−1) = a·2^S + 2^S`), so the quotient at most doubles one unit short
(`2·num > den` absorbs the floor loss), and the decremented shift argument satisfies
`arg1 ≤ 2·arg2 + 1`; since the old closing modulus is even and `2·arg2 + 1` is the largest value
sharing `arg2`'s floor at the dropped shift, the shifted floors stay ordered
(`seam_close_odd`). The scale point orders trivially and the clamp is constant; sign composition
yields the signed public statement on the whole value domain.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation
open Common.Word
open ExpRealSpec

set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

/-! ## Magnitude words normalize through the absolute value -/

/-- A supported magnitude word is its own absolute value. -/
private theorem absTree_of_small {a : Nat} (ha : a ≤ scaleMax) : absTree a = a :=
  absTree_nonneg (lt_of_le_of_lt ha (by unfold scaleMax; norm_num))

/-- The kernel magnitude depends on the multiplier only through its magnitude word. -/
theorem mulMagnitude_abs_norm {y : Nat} (habs : absTree y ≤ scaleMax) (x : Nat) :
    mulMagnitudeTree y x = mulMagnitudeTree (absTree y) x := by
  have h : absTree (absTree y) = absTree y := absTree_of_small habs
  unfold mulMagnitudeTree mulShiftTree r0MulTree mulScaleTree
  rw [h]

/-- The closing shift depends on the multiplier only through its magnitude word. -/
theorem mulShift_abs_norm {y : Nat} (habs : absTree y ≤ scaleMax) (x : Nat) :
    mulShiftTree y x = mulShiftTree (absTree y) x := by
  have h : absTree (absTree y) = absTree y := absTree_of_small habs
  unfold mulShiftTree
  rw [h]

/-! ## Headroom arithmetic from scale maximality -/

/-- The headroom shift is antitone in the magnitude. -/
theorem scaleShift_antitone {a b : Nat} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ scaleMax) :
    scaleShiftTree b ≤ scaleShiftTree a := by
  have haQ : a ≤ scaleMax := le_trans hab hb
  have haw : a < 2 ^ 256 := lt_of_le_of_lt haQ (by unfold scaleMax; norm_num)
  have hbw : b < 2 ^ 256 := lt_of_le_of_lt hb (by unfold scaleMax; norm_num)
  have haa : absTree a = a := absTree_of_small haQ
  have hba : absTree b = b := absTree_of_small hb
  have hmax := mulScaleTree_max (y := a) haw (by rw [haa]; exact ha) (by rw [haa]; exact haQ)
  obtain ⟨_, hspec_a, _⟩ := mulScaleTree_spec (y := a) haw (by rw [haa]; exact haQ)
  obtain ⟨_, hspec_b, hcap_b⟩ := mulScaleTree_spec (y := b) hbw (by rw [hba]; exact hb)
  rw [hspec_a, haa] at hmax
  rw [hspec_b, hba] at hcap_b
  rw [haa] at hspec_a
  rw [hba] at hspec_b
  -- b·2^Sb ≤ Q < 2·a·2^Sa ≤ 2·b·2^Sa, so 2^Sb < 2^(Sa+1)
  by_contra hcon
  push_neg at hcon
  have h1 : b * 2 ^ scaleShiftTree b < 2 * (a * 2 ^ scaleShiftTree a) :=
    lt_of_le_of_lt hcap_b hmax
  have h2 : 2 * (a * 2 ^ scaleShiftTree a) ≤ 2 * (b * 2 ^ scaleShiftTree a) := by
    have := Nat.mul_le_mul_right (2 ^ scaleShiftTree a) hab
    omega
  have h3 : b * 2 ^ scaleShiftTree b < b * 2 ^ (scaleShiftTree a + 1) := by
    have h4 : 2 * (b * 2 ^ scaleShiftTree a) = b * 2 ^ (scaleShiftTree a + 1) := by
      rw [pow_succ]
      ring
    omega
  have h5 : 2 ^ scaleShiftTree b < 2 ^ (scaleShiftTree a + 1) :=
    lt_of_mul_lt_mul_left h3 (Nat.zero_le b)
  have h6 : scaleShiftTree b < scaleShiftTree a + 1 :=
    (Nat.pow_lt_pow_iff_right (by norm_num)).mp h5
  omega

/-- A unit magnitude step drops the headroom shift by at most one. -/
theorem scaleShift_step {a : Nat} (ha : 1 ≤ a) (ha1 : a + 1 ≤ scaleMax) :
    scaleShiftTree a ≤ scaleShiftTree (a + 1) + 1 := by
  have haQ : a ≤ scaleMax := le_trans (Nat.le_succ a) ha1
  have haw : a < 2 ^ 256 := lt_of_le_of_lt haQ (by unfold scaleMax; norm_num)
  have ha1w : a + 1 < 2 ^ 256 := lt_of_le_of_lt ha1 (by unfold scaleMax; norm_num)
  have haa : absTree a = a := absTree_of_small haQ
  have ha1a : absTree (a + 1) = a + 1 := absTree_of_small ha1
  obtain ⟨_, hspec_a, hcap_a⟩ := mulScaleTree_spec (y := a) haw (by rw [haa]; exact haQ)
  have hmax1 := mulScaleTree_max (y := a + 1) ha1w (by rw [ha1a]; omega)
    (by rw [ha1a]; exact ha1)
  obtain ⟨_, hspec_a1, _⟩ := mulScaleTree_spec (y := a + 1) ha1w (by rw [ha1a]; exact ha1)
  rw [hspec_a, haa] at hcap_a
  rw [hspec_a1, ha1a] at hmax1
  -- a·2^Sa ≤ Q < 2·(a+1)·2^S(a+1): if Sa ≥ S(a+1)+2, then 2a < a+1, impossible for a ≥ 1
  by_contra hcon
  push_neg at hcon
  have h1 : a * 2 ^ scaleShiftTree a < 2 * ((a + 1) * 2 ^ scaleShiftTree (a + 1)) :=
    lt_of_le_of_lt hcap_a hmax1
  have h2 : (2:Nat) ^ (scaleShiftTree (a + 1) + 2) ≤ 2 ^ scaleShiftTree a :=
    Nat.pow_le_pow_right (by norm_num) hcon
  have h3 : a * 2 ^ (scaleShiftTree (a + 1) + 2) ≤ a * 2 ^ scaleShiftTree a :=
    Nat.mul_le_mul_left a h2
  have h4 : a * 2 ^ (scaleShiftTree (a + 1) + 2) =
      (2 * a) * (2 * 2 ^ scaleShiftTree (a + 1)) := by
    rw [pow_succ, pow_succ]
    ring
  have h5 : 2 * ((a + 1) * 2 ^ scaleShiftTree (a + 1)) =
      (a + 1) * (2 * 2 ^ scaleShiftTree (a + 1)) := by ring
  have hppos : 0 < 2 * 2 ^ scaleShiftTree (a + 1) := by positivity
  have h6 : 2 * a < a + 1 := by
    have h7 : (2 * a) * (2 * 2 ^ scaleShiftTree (a + 1)) <
        (a + 1) * (2 * 2 ^ scaleShiftTree (a + 1)) := by omega
    exact lt_of_mul_lt_mul_right h7 (Nat.zero_le _)
  omega

/-! ## Quotient comparisons at a fixed exponent -/

/-- `2·num > den` at any live exponent: the even accumulator dominates three `tod` magnitudes. -/
theorem num_den_ratio {x : Nat} (hx : x < 2 ^ 256) (hW : WideRegion x) :
    (evTree x : Int) - int256 (todTree x) <
      2 * ((evTree x : Int) + int256 (todTree x)) := by
  obtain ⟨_, hvlt⟩ := vTree_eq_wide hx hW
  obtain ⟨hev_lo, _⟩ := evTree_facts hvlt
  obtain ⟨htod_lo, htod_hi, _, _⟩ := todTree_bound_wide hx hW
  have hev : (0x1385291795942d41ba5fd317688e18710 : Int) ≤ (evTree x : Int) := by
    exact_mod_cast hev_lo
  have h1 : (0x1385291795942d41ba5fd317688e18710 : Int) =
      415147853590918758559635130244235626256 := by norm_num
  rw [h1] at hev
  have hp126 : (2:Int)^126 = 85070591730234615865843651857942052864 := by norm_num
  rw [hp126] at htod_lo htod_hi
  linarith [hev, htod_lo, htod_hi]

/-- The scaled quotient is monotone in the scale at a fixed exponent. -/
theorem r0Scaled_mono_scale {sc1 sc2 x : Nat} (h12 : sc1 ≤ sc2) (hshi2 : sc2 ≤ scaleMax)
    (hx : x < 2 ^ 256) (hW : WideRegion x) :
    int256 (r0ScaledTree sc1 x) ≤ int256 (r0ScaledTree sc2 x) := by
  obtain ⟨hadd, hsub, hnum_pos, hden_pos⟩ := numden_pos_wide hx hW
  obtain ⟨_, hvlt⟩ := vTree_eq_wide hx hW
  obtain ⟨hevlo, hevhi⟩ := evTree_facts hvlt
  obtain ⟨_, htod_hi, _, _⟩ := todTree_bound_wide hx hW
  set num := evmAdd (evTree x) (todTree x) with hnumdef
  set den := evmSub (evTree x) (todTree x) with hdendef
  have hnumw : num < 2 ^ 256 := evmAdd_lt _ _
  have hdenw : den < 2 ^ 256 := evmSub_lt _ _
  obtain ⟨hnumeq, hnum255⟩ := int256_eq_of_nonneg hnumw (by rw [hadd]; exact le_of_lt hnum_pos)
  obtain ⟨hdeneq, hden255⟩ := int256_eq_of_nonneg hdenw (by rw [hsub]; exact le_of_lt hden_pos)
  have hevhiI : (evTree x : Int) < 3 * 2 ^ 127 := by exact_mod_cast hevhi
  have hnumlt : int256 num < 2 ^ 129 := by
    rw [hadd]
    have hp126 : (2:Int)^126 = 85070591730234615865843651857942052864 := by norm_num
    rw [hp126] at htod_hi
    have hp : (3:Int) * 2 ^ 127 + 85070591730234615865843651857942052864 < 2 ^ 129 := by norm_num
    linarith [hevhiI, htod_hi]
  have hnumnat : num < 2 ^ 129 := by
    have hh : ((num : Nat) : Int) < 2 ^ 129 := by rw [hnumeq] at hnumlt; exact hnumlt
    exact_mod_cast hh
  have hdennat : 0 < den := by
    have hh : (0:Int) < ((den : Nat) : Int) := by rw [← hdeneq, hsub]; exact hden_pos
    exact_mod_cast hh
  have hden126 : 2 ^ 126 ≤ den := by
    have hev : (0x1385291795942d41ba5fd317688e18710 : Int) ≤ (evTree x : Int) := by
      exact_mod_cast hevlo
    have h : (2 ^ 126 : Int) ≤ ((den : Nat) : Int) := by
      rw [← hdeneq, hsub]
      have h1 : (0x1385291795942d41ba5fd317688e18710 : Int) =
          415147853590918758559635130244235626256 := by norm_num
      rw [h1] at hev
      have hp126 : (2:Int)^126 = 85070591730234615865843651857942052864 := by norm_num
      rw [hp126] at htod_hi
      rw [hp126]
      linarith [hev, htod_hi]
    exact_mod_cast h
  have hsw1 : sc1 < 2 ^ 256 := lt_of_le_of_lt (le_trans h12 hshi2) (by unfold scaleMax; norm_num)
  have hsw2 : sc2 < 2 ^ 256 := lt_of_le_of_lt hshi2 (by unfold scaleMax; norm_num)
  have hfit1 : sc1 * num < 2 ^ 256 := by
    have h1 : sc1 * num ≤ scaleMax * 2 ^ 129 :=
      Nat.mul_le_mul (le_trans h12 hshi2) (le_of_lt hnumnat)
    have h2 : scaleMax * 2 ^ 129 < 2 ^ 256 := by unfold scaleMax; norm_num
    omega
  have hfit2 : sc2 * num < 2 ^ 256 := by
    have h1 : sc2 * num ≤ scaleMax * 2 ^ 129 := Nat.mul_le_mul hshi2 (le_of_lt hnumnat)
    have h2 : scaleMax * 2 ^ 129 < 2 ^ 256 := by unfold scaleMax; norm_num
    omega
  have hq1 : r0ScaledTree sc1 x = sc1 * num / den := by
    show evmDiv (evmMul sc1 num) den = _
    rw [evmMul_eq_nat hsw1 hnumw hfit1, evmDiv_eq hfit1 hdenw (Nat.pos_iff_ne_zero.mp hdennat)]
  have hq2 : r0ScaledTree sc2 x = sc2 * num / den := by
    show evmDiv (evmMul sc2 num) den = _
    rw [evmMul_eq_nat hsw2 hnumw hfit2, evmDiv_eq hfit2 hdenw (Nat.pos_iff_ne_zero.mp hdennat)]
  clear_value num den
  have hqle : sc1 * num / den ≤ sc2 * num / den :=
    Nat.div_le_div_right (Nat.mul_le_mul_right num h12)
  have hsmall : ∀ sc : Nat, sc * num < 2 ^ 256 → sc * num / den < 2 ^ 255 := by
    intro sc hfit
    have h1 : sc * num / den ≤ sc * num / 2 ^ 126 :=
      Nat.div_le_div_left hden126 (Nat.two_pow_pos _)
    have h2 : sc * num / 2 ^ 126 < 2 ^ 130 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
      calc sc * num < 2 ^ 256 := hfit
        _ = 2 ^ 130 * 2 ^ 126 := by norm_num
    have h3 : (2:Nat) ^ 130 < 2 ^ 255 := by norm_num
    omega
  rw [hq1, hq2, int256_of_lt (hsmall sc1 hfit1), int256_of_lt (hsmall sc2 hfit2)]
  exact_mod_cast hqle

/-- The scaled quotient at most doubles when the doubled scale gains exactly one headroom unit:
`2·sc2 = sc1 + 2^S` with `S ≥ 1` gives `r0(sc1) ≤ 2·r0(sc2)` (`2·num > den` pays the floor
loss). -/
theorem r0Scaled_double_scale {sc1 sc2 S x : Nat} (hS : 1 ≤ S)
    (hid : 2 * sc2 = sc1 + 2 ^ S) (hshi1 : sc1 ≤ scaleMax) (hshi2 : sc2 ≤ scaleMax)
    (hx : x < 2 ^ 256) (hW : WideRegion x) :
    int256 (r0ScaledTree sc1 x) ≤ 2 * int256 (r0ScaledTree sc2 x) := by
  obtain ⟨hadd, hsub, hnum_pos, hden_pos⟩ := numden_pos_wide hx hW
  obtain ⟨_, hvlt⟩ := vTree_eq_wide hx hW
  obtain ⟨hevlo, hevhi⟩ := evTree_facts hvlt
  obtain ⟨_, htod_hi, _, _⟩ := todTree_bound_wide hx hW
  have hratio := num_den_ratio hx hW
  set num := evmAdd (evTree x) (todTree x) with hnumdef
  set den := evmSub (evTree x) (todTree x) with hdendef
  have hnumw : num < 2 ^ 256 := evmAdd_lt _ _
  have hdenw : den < 2 ^ 256 := evmSub_lt _ _
  obtain ⟨hnumeq, hnum255⟩ := int256_eq_of_nonneg hnumw (by rw [hadd]; exact le_of_lt hnum_pos)
  obtain ⟨hdeneq, hden255⟩ := int256_eq_of_nonneg hdenw (by rw [hsub]; exact le_of_lt hden_pos)
  have hevhiI : (evTree x : Int) < 3 * 2 ^ 127 := by exact_mod_cast hevhi
  have hnumlt : int256 num < 2 ^ 129 := by
    rw [hadd]
    have hp126 : (2:Int)^126 = 85070591730234615865843651857942052864 := by norm_num
    rw [hp126] at htod_hi
    have hp : (3:Int) * 2 ^ 127 + 85070591730234615865843651857942052864 < 2 ^ 129 := by norm_num
    linarith [hevhiI, htod_hi]
  have hnumnat : num < 2 ^ 129 := by
    have hh : ((num : Nat) : Int) < 2 ^ 129 := by rw [hnumeq] at hnumlt; exact hnumlt
    exact_mod_cast hh
  have hdennat : 0 < den := by
    have hh : (0:Int) < ((den : Nat) : Int) := by rw [← hdeneq, hsub]; exact hden_pos
    exact_mod_cast hh
  have hden126 : 2 ^ 126 ≤ den := by
    have hev : (0x1385291795942d41ba5fd317688e18710 : Int) ≤ (evTree x : Int) := by
      exact_mod_cast hevlo
    have h : (2 ^ 126 : Int) ≤ ((den : Nat) : Int) := by
      rw [← hdeneq, hsub]
      have h1 : (0x1385291795942d41ba5fd317688e18710 : Int) =
          415147853590918758559635130244235626256 := by norm_num
      rw [h1] at hev
      have hp126 : (2:Int)^126 = 85070591730234615865843651857942052864 := by norm_num
      rw [hp126] at htod_hi
      rw [hp126]
      linarith [hev, htod_hi]
    exact_mod_cast h
  -- `2·num > den` as Nats
  have hratioN : den < 2 * num := by
    have h1 : ((den : Nat) : Int) < 2 * ((num : Nat) : Int) := by
      rw [← hdeneq, ← hnumeq, hadd, hsub]
      exact hratio
    exact_mod_cast h1
  have hsw1 : sc1 < 2 ^ 256 := lt_of_le_of_lt hshi1 (by unfold scaleMax; norm_num)
  have hsw2 : sc2 < 2 ^ 256 := lt_of_le_of_lt hshi2 (by unfold scaleMax; norm_num)
  have hfit1 : sc1 * num < 2 ^ 256 := by
    have h1 : sc1 * num ≤ scaleMax * 2 ^ 129 := Nat.mul_le_mul hshi1 (le_of_lt hnumnat)
    have h2 : scaleMax * 2 ^ 129 < 2 ^ 256 := by unfold scaleMax; norm_num
    omega
  have hfit2 : sc2 * num < 2 ^ 256 := by
    have h1 : sc2 * num ≤ scaleMax * 2 ^ 129 := Nat.mul_le_mul hshi2 (le_of_lt hnumnat)
    have h2 : scaleMax * 2 ^ 129 < 2 ^ 256 := by unfold scaleMax; norm_num
    omega
  have hq1 : r0ScaledTree sc1 x = sc1 * num / den := by
    show evmDiv (evmMul sc1 num) den = _
    rw [evmMul_eq_nat hsw1 hnumw hfit1, evmDiv_eq hfit1 hdenw (Nat.pos_iff_ne_zero.mp hdennat)]
  have hq2 : r0ScaledTree sc2 x = sc2 * num / den := by
    show evmDiv (evmMul sc2 num) den = _
    rw [evmMul_eq_nat hsw2 hnumw hfit2, evmDiv_eq hfit2 hdenw (Nat.pos_iff_ne_zero.mp hdennat)]
  clear_value num den
  -- Nat inequality: sc1·num/den ≤ 2·(sc2·num/den)
  have hkey : sc1 * num / den ≤ 2 * (sc2 * num / den) := by
    -- 2·(sc2·num/den) ≥ (2·sc2·num)/den − 1 = ((sc1 + 2^S)·num)/den − 1
    --   ≥ sc1·num/den + (2^S·num)/den − 1 ≥ sc1·num/den   (2^S·num ≥ 2·num > den)
    have hsplit : 2 * sc2 * num = sc1 * num + 2 ^ S * num := by
      rw [show sc1 * num + 2 ^ S * num = (sc1 + 2 ^ S) * num from by ring, ← hid]
    have hdbl : 2 * sc2 * num / den ≤ 2 * (sc2 * num / den) + 1 := by
      have hdm := Nat.div_add_mod (sc2 * num) den
      have hmod : (sc2 * num) % den < den := Nat.mod_lt _ hdennat
      have h2c : 2 * (sc2 * num) < (2 * (sc2 * num / den) + 2) * den := by
        calc 2 * (sc2 * num)
            = 2 * (den * (sc2 * num / den)) + 2 * ((sc2 * num) % den) := by omega
          _ < 2 * (den * (sc2 * num / den)) + 2 * den := by omega
          _ = (2 * (sc2 * num / den) + 2) * den := by ring
      have harg : 2 * sc2 * num < (2 * (sc2 * num / den) + 2) * den := by
        rw [show 2 * sc2 * num = 2 * (sc2 * num) from by ring]
        exact h2c
      have hlt := (Nat.div_lt_iff_lt_mul hdennat).mpr harg
      omega
    have hsuper : sc1 * num / den + 2 ^ S * num / den ≤ (sc1 * num + 2 ^ S * num) / den := by
      rw [Nat.le_div_iff_mul_le hdennat]
      have ha := Nat.div_mul_le_self (sc1 * num) den
      have hb := Nat.div_mul_le_self (2 ^ S * num) den
      calc (sc1 * num / den + 2 ^ S * num / den) * den
          = sc1 * num / den * den + 2 ^ S * num / den * den := by ring
        _ ≤ sc1 * num + 2 ^ S * num := Nat.add_le_add ha hb
    have hSnum : 1 ≤ 2 ^ S * num / den := by
      rw [Nat.le_div_iff_mul_le hdennat]
      have h1 : 2 * num ≤ 2 ^ S * num := by
        have h2 : (2:Nat) ≤ 2 ^ S := by
          calc (2:Nat) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ S := Nat.pow_le_pow_right (by norm_num) hS
        exact Nat.mul_le_mul_right num h2
      calc 1 * den = den := Nat.one_mul den
        _ ≤ 2 * num := le_of_lt hratioN
        _ ≤ 2 ^ S * num := h1
    have hchain : sc1 * num / den + 1 ≤ 2 * sc2 * num / den := by
      calc sc1 * num / den + 1 ≤ sc1 * num / den + 2 ^ S * num / den :=
            Nat.add_le_add_left hSnum _
        _ ≤ (sc1 * num + 2 ^ S * num) / den := hsuper
        _ = 2 * sc2 * num / den := by rw [← hsplit]
    omega
  have hsmall : ∀ sc : Nat, sc * num < 2 ^ 256 → sc * num / den < 2 ^ 255 := by
    intro sc hfit
    have h1 : sc * num / den ≤ sc * num / 2 ^ 126 :=
      Nat.div_le_div_left hden126 (Nat.two_pow_pos _)
    have h2 : sc * num / 2 ^ 126 < 2 ^ 130 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
      calc sc * num < 2 ^ 256 := hfit
        _ = 2 ^ 130 * 2 ^ 126 := by norm_num
    have h3 : (2:Nat) ^ 130 < 2 ^ 255 := by norm_num
    omega
  rw [hq1, hq2, int256_of_lt (hsmall sc1 hfit1), int256_of_lt (hsmall sc2 hfit2)]
  exact_mod_cast hkey

/-! ## The odd-extended seam floor -/

/-- The seam floor comparison with one extra unit of slack: an odd excess over the doubled
argument cannot cross the even closing modulus, so `arg1 ≤ 2·arg2 + 1` still orders the shifted
floors across a one-bit shift drop. -/
theorem seam_close_odd {arg1 arg2 s1 s2 : Nat}
    (ha1 : arg1 < 2 ^ 256) (ha2 : arg2 < 2 ^ 256)
    (hs1 : s1 < 256) (hs2 : s2 < 256) (hseq : s2 + 1 = s1)
    (hnn1 : 0 ≤ int256 arg1) (hnn2 : 0 ≤ int256 arg2)
    (hle : int256 arg1 ≤ 2 * int256 arg2 + 1) :
    int256 (evmShr s1 arg1) ≤ int256 (evmShr s2 arg2) := by
  obtain ⟨he1, hlt1⟩ := int256_eq_of_nonneg ha1 hnn1
  obtain ⟨he2, hlt2⟩ := int256_eq_of_nonneg ha2 hnn2
  have hleN : arg1 ≤ 2 * arg2 + 1 := by
    have : ((arg1 : Nat) : Int) ≤ ((2 * arg2 + 1 : Nat) : Int) := by
      rw [← he1]
      push_cast
      rw [← he2]
      exact hle
    exact_mod_cast this
  rw [evmShr_eq_div hs1 ha1, evmShr_eq_div hs2 ha2]
  -- ⌊(2·arg2 + 1)/2^s1⌋ = ⌊2·arg2/2^s1⌋: the odd numerator cannot complete the even modulus
  have hodd : (2 * arg2 + 1) / 2 ^ s1 = 2 * arg2 / 2 ^ s1 := by
    apply Nat.succ_div_of_not_dvd
    intro hdvd
    have h2 : (2:Nat) ∣ 2 ^ s1 := dvd_pow_self 2 (by omega : s1 ≠ 0)
    have h3 : (2:Nat) ∣ 2 * arg2 + 1 := dvd_trans h2 hdvd
    omega
  have hkey : 2 * arg2 / 2 ^ s1 = arg2 / 2 ^ s2 := by
    rw [← hseq, pow_succ, Nat.mul_comm (2 ^ s2) 2, Nat.mul_div_mul_left arg2 (2 ^ s2) (by norm_num)]
  have hqle : arg1 / 2 ^ s1 ≤ arg2 / 2 ^ s2 := by
    rw [← hkey, ← hodd]
    exact Nat.div_le_div_right hleN
  have hq1lt : arg1 / 2 ^ s1 < 2 ^ 255 := by
    have h := Nat.div_le_self arg1 (2 ^ s1)
    exact lt_of_le_of_lt h hlt1
  have hq2lt : arg2 / 2 ^ s2 < 2 ^ 255 := by
    have h := Nat.div_le_self arg2 (2 ^ s2)
    exact lt_of_le_of_lt h hlt2
  rw [int256_of_lt hq1lt, int256_of_lt hq2lt]
  exact_mod_cast hqle

/-! ## The adjacent magnitude step -/

/-- The signed closing shift is antitone in the magnitude word. -/
theorem mulShiftY_antitone {a b x : Nat} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ scaleMax)
    (hx : x < 2 ^ 256) (hW : WideRegion x) :
    int256 (mulShiftTree b x) ≤ int256 (mulShiftTree a x) := by
  have haQ : a ≤ scaleMax := le_trans hab hb
  have haw : a < 2 ^ 256 := lt_of_le_of_lt haQ (by unfold scaleMax; norm_num)
  have hbw : b < 2 ^ 256 := lt_of_le_of_lt hb (by unfold scaleMax; norm_num)
  have haa : absTree a = a := absTree_of_small haQ
  have hba : absTree b = b := absTree_of_small hb
  have hta := mulShiftTree_transport (y := a) haw hx (by rw [haa]; exact haQ) hW
  have htb := mulShiftTree_transport (y := b) hbw hx (by rw [hba]; exact hb) hW
  rw [haa] at hta
  rw [hba] at htb
  rw [hta, htb]
  have hanti := scaleShift_antitone ha hab hb
  have hantiI : (scaleShiftTree b : Int) ≤ (scaleShiftTree a : Int) := by exact_mod_cast hanti
  linarith [hantiI]

/-- **The adjacent magnitude step**: at a fixed live exponent, one unit of magnitude never
decreases the kernel magnitude. -/
theorem mulMagnitudeY_step {a x : Nat} (ha : 1 ≤ a) (ha1 : a + 1 ≤ scaleMax)
    (hx : x < 2 ^ 256) (hW : WideRegion x) (hx0 : int256 x ≠ 0)
    (hlive2 : 2 ≤ int256 (mulShiftTree (a + 1) x)) :
    int256 (mulMagnitudeTree a x) ≤ int256 (mulMagnitudeTree (a + 1) x) := by
  have haQ : a ≤ scaleMax := le_trans (Nat.le_succ a) ha1
  have haw : a < 2 ^ 256 := lt_of_le_of_lt haQ (by unfold scaleMax; norm_num)
  have ha1w : a + 1 < 2 ^ 256 := lt_of_le_of_lt ha1 (by unfold scaleMax; norm_num)
  have haa : absTree a = a := absTree_of_small haQ
  have ha1a : absTree (a + 1) = a + 1 := absTree_of_small ha1
  have hlive1 : 2 ≤ int256 (mulShiftTree a x) :=
    le_trans hlive2 (mulShiftY_antitone ha (Nat.le_succ a) ha1 hx hW)
  -- headroom facts
  obtain ⟨hs256a, hspec_a, hcap_a⟩ := mulScaleTree_spec (y := a) haw (by rw [haa]; exact haQ)
  obtain ⟨hs256a1, hspec_a1, hcap_a1⟩ := mulScaleTree_spec (y := a + 1) ha1w
    (by rw [ha1a]; exact ha1)
  have hanti := scaleShift_antitone ha (Nat.le_succ a) ha1
  have hstep := scaleShift_step ha ha1
  -- word-level plumbing
  have hm1 := mulMagnitudeTree_live (y := a) hx hx0 hW.1
  have hm2 := mulMagnitudeTree_live (y := a + 1) hx hx0 hW.1
  obtain ⟨harg1eq, harg1nn, harg1hi⟩ := mulShiftArg_facts (y := a) haw (by omega) hx
    (by rw [haa]; exact haQ) hW
  obtain ⟨harg2eq, harg2nn, harg2hi⟩ := mulShiftArg_facts (y := a + 1) ha1w (by omega) hx
    (by rw [ha1a]; exact ha1) hW
  obtain ⟨hsh1lo, hsh1lt, hsh1eq⟩ := mulShift_word_facts (y := a) haw hx
    (by rw [haa]; exact haQ) hW hlive1
  obtain ⟨hsh2lo, hsh2lt, hsh2eq⟩ := mulShift_word_facts (y := a + 1) ha1w hx
    (by rw [ha1a]; exact ha1) hW hlive2
  have hta := mulShiftTree_transport (y := a) haw hx (by rw [haa]; exact haQ) hW
  have htb := mulShiftTree_transport (y := a + 1) ha1w hx (by rw [ha1a]; exact ha1) hW
  rw [haa] at hta hspec_a
  rw [ha1a] at htb hspec_a1
  have hr0a : r0MulTree a x = r0ScaledTree (a * 2 ^ scaleShiftTree a) x := by
    rw [r0MulTree_eq_scaled, hspec_a]
  have hr0a1 : r0MulTree (a + 1) x = r0ScaledTree ((a + 1) * 2 ^ scaleShiftTree (a + 1)) x := by
    rw [r0MulTree_eq_scaled, hspec_a1]
  rw [hspec_a] at hcap_a
  rw [hspec_a1] at hcap_a1
  rw [hm1, hm2]
  rcases Nat.eq_or_lt_of_le hanti with hSeq | hSlt
  · -- same headroom shift: the scale grows, the closing shift is unchanged
    have hr0mono : int256 (r0MulTree a x) ≤ int256 (r0MulTree (a + 1) x) := by
      rw [hr0a, hr0a1, ← hSeq]
      exact r0Scaled_mono_scale
        (Nat.mul_le_mul_right _ (Nat.le_succ a)) (by rw [hSeq] at hcap_a1 ⊢; exact hcap_a1)
        hx hW
    have hsheq' : mulShiftTree a x = mulShiftTree (a + 1) x := by
      have h1 : (mulShiftTree a x : Int) = (mulShiftTree (a + 1) x : Int) := by
        rw [hsh1eq, hsh2eq, hta, htb, hSeq]
      exact_mod_cast h1
    rw [← hsheq']
    set arg1 := evmSub (r0MulTree a x) marginWord with harg1def
    set arg2 := evmSub (r0MulTree (a + 1) x) marginWord with harg2def
    have ha1lt : arg1 < 2 ^ 256 := by rw [harg1def]; exact evmSub_lt _ _
    have ha2lt : arg2 < 2 ^ 256 := by rw [harg2def]; exact evmSub_lt _ _
    clear_value arg1 arg2
    have hargle : int256 arg1 ≤ int256 arg2 := by
      rw [harg1eq, harg2eq]
      exact sub_le_sub_right hr0mono 1
    obtain ⟨he1, hlt1⟩ := int256_eq_of_nonneg ha1lt (by rw [harg1eq]; exact harg1nn)
    obtain ⟨he2, hlt2⟩ := int256_eq_of_nonneg ha2lt (by rw [harg2eq]; exact harg2nn)
    have hargleN : arg1 ≤ arg2 := by
      have : ((arg1 : Nat) : Int) ≤ ((arg2 : Nat) : Int) := by rw [← he1, ← he2]; exact hargle
      exact_mod_cast this
    rw [evmShr_eq_div hsh1lt ha1lt, evmShr_eq_div hsh1lt ha2lt]
    have hqle : arg1 / 2 ^ mulShiftTree a x ≤ arg2 / 2 ^ mulShiftTree a x :=
      Nat.div_le_div_right hargleN
    have hq1lt : arg1 / 2 ^ mulShiftTree a x < 2 ^ 255 := by
      have h1 : arg1 / 2 ^ mulShiftTree a x ≤ arg1 := Nat.div_le_self _ _
      exact lt_of_le_of_lt h1 hlt1
    have hq2lt : arg2 / 2 ^ mulShiftTree a x < 2 ^ 255 := by
      have h1 : arg2 / 2 ^ mulShiftTree a x ≤ arg2 := Nat.div_le_self _ _
      exact lt_of_le_of_lt h1 hlt2
    rw [int256_of_lt hq1lt, int256_of_lt hq2lt]
    exact_mod_cast hqle
  · -- the headroom shift drops one bit: the doubled scale gains one headroom unit
    have hSid : scaleShiftTree a = scaleShiftTree (a + 1) + 1 := Nat.le_antisymm hstep hSlt
    have hid : 2 * ((a + 1) * 2 ^ scaleShiftTree (a + 1)) =
        a * 2 ^ scaleShiftTree a + 2 ^ scaleShiftTree a := by
      rw [hSid, pow_succ]
      ring
    have hS1 : 1 ≤ scaleShiftTree a := by
      rw [hSid]
      exact Nat.succ_le_succ (Nat.zero_le _)
    have hdouble : int256 (r0MulTree a x) ≤ 2 * int256 (r0MulTree (a + 1) x) := by
      rw [hr0a, hr0a1]
      exact r0Scaled_double_scale hS1 hid hcap_a hcap_a1 hx hW
    have hseq : mulShiftTree (a + 1) x + 1 = mulShiftTree a x := by
      have h1 : (mulShiftTree (a + 1) x : Int) + 1 = (mulShiftTree a x : Int) := by
        rw [hsh1eq, hsh2eq, hta, htb]
        have : (scaleShiftTree a : Int) = (scaleShiftTree (a + 1) : Int) + 1 := by
          exact_mod_cast hSid
        rw [this]
        ring
      exact_mod_cast h1
    set arg1 := evmSub (r0MulTree a x) marginWord with harg1def
    set arg2 := evmSub (r0MulTree (a + 1) x) marginWord with harg2def
    have ha1lt : arg1 < 2 ^ 256 := by rw [harg1def]; exact evmSub_lt _ _
    have ha2lt : arg2 < 2 ^ 256 := by rw [harg2def]; exact evmSub_lt _ _
    clear_value arg1 arg2
    have hargle : int256 arg1 ≤ 2 * int256 arg2 + 1 := by
      rw [harg1eq, harg2eq]
      linarith [hdouble]
    exact seam_close_odd ha1lt ha2lt hsh1lt hsh2lt hseq
      (by rw [harg1eq]; exact harg1nn) (by rw [harg2eq]; exact harg2nn) hargle

/-! ## The magnitude induction -/

/-- Unit-step induction over the magnitude: the endpoint's live shift bounds every
intermediate through the headroom antitonicity. -/
theorem mulMagnitudeY_mono_steps {x : Nat} (hx : x < 2 ^ 256) (hW : WideRegion x)
    (hx0 : int256 x ≠ 0) (n : Nat) :
    ∀ a : Nat, 1 ≤ a → a + n ≤ scaleMax →
    2 ≤ int256 (mulShiftTree (a + n) x) →
    int256 (mulMagnitudeTree a x) ≤ int256 (mulMagnitudeTree (a + n) x) := by
  induction n with
  | zero =>
    intro a _ _ _
    exact le_refl _
  | succ m ih =>
    intro a ha hbnd hlive
    have hstep : int256 (mulMagnitudeTree a x) ≤ int256 (mulMagnitudeTree (a + 1) x) := by
      have hlive1 : 2 ≤ int256 (mulShiftTree (a + 1) x) := by
        have h := mulShiftY_antitone (a := a + 1) (b := a + m + 1) (by omega)
          (by omega) (by omega) hx hW
        have h2 : a + (m + 1) = a + m + 1 := by omega
        rw [h2] at hlive
        linarith [h, hlive]
      exact mulMagnitudeY_step ha (by omega) hx hW hx0 hlive1
    have hrec := ih (a + 1) (by omega) (by omega) (by
      have h2 : a + 1 + m = a + (m + 1) := by omega
      rw [h2]
      exact hlive)
    have h3 : a + 1 + m = a + (m + 1) := by omega
    rw [h3] at hrec
    exact le_trans hstep hrec

/-- **Magnitude monotonicity in the multiplier at a fixed live exponent.** -/
theorem mulMagnitudeY_region_mono {a1 a2 x : Nat} (ha1 : 1 ≤ a1) (h12 : a1 ≤ a2)
    (ha2 : a2 ≤ scaleMax) (hx : x < 2 ^ 256) (hW : WideRegion x) (hx0 : int256 x ≠ 0)
    (hlive2 : 2 ≤ int256 (mulShiftTree a2 x)) :
    int256 (mulMagnitudeTree a1 x) ≤ int256 (mulMagnitudeTree a2 x) := by
  have h := mulMagnitudeY_mono_steps hx hW hx0 (a2 - a1) a1 ha1
    (by omega) (by rw [show a1 + (a2 - a1) = a2 from by omega]; exact hlive2)
  rw [show a1 + (a2 - a1) = a2 from by omega] at h
  exact h

/-! ## The public runtime statement -/

/-- **Monotonicity in the multiplier on the value domain.** For a fixed exponent and accepted
multipliers `y1 ≤ y2`, the signed results are ordered. -/
theorem run_mul_exp_ray_evm_mono_y {y1 y2 x : Nat}
    (h1 : MulExpRayValueDomain y1 x) (h2 : MulExpRayValueDomain y2 x)
    (hle : int256 y1 ≤ int256 y2) :
    MulExpRayRunYMonotone y1 y2 x := by
  have hrun1 : run_mul_exp_ray_evm y1 x = .ok (mulExpTree y1 x) :=
    run_mul_exp_ray_evm_eq_tree h1
  have hrun2 : run_mul_exp_ray_evm y2 x = .ok (mulExpTree y2 x) :=
    run_mul_exp_ray_evm_eq_tree h2
  obtain ⟨⟨hy1, hxw⟩, hscale1, hxhi, hshift1⟩ := h1
  obtain ⟨⟨hy2, _⟩, hscale2, _, hshift2⟩ := h2
  have habs1 : absTree y1 ≤ scaleMax :=
    (scaleShiftTree_le_127_iff (absTree_lt y1)).mp hscale1
  have habs2 : absTree y2 ≤ scaleMax :=
    (scaleShiftTree_le_127_iff (absTree_lt y2)).mp hscale2
  refine ⟨mulExpTree y1 x, mulExpTree y2 x, hrun1, hrun2, hle, ?_⟩
  -- the exponent's class decides the result shape
  by_cases hcl : int256 x ≤ int256 mulExpRayZeroMax
  · rw [mulExpTree_clamped hxw hcl, mulExpTree_clamped hxw hcl]
  by_cases hx0 : int256 x = 0
  · have hxz : x = 0 := (int256_zero_iff_of_canonical hxw).1 hx0
    subst hxz
    rw [mulExpTree_scale_point hy1 habs1, mulExpTree_scale_point hy2 habs2]
    exact hle
  -- the live region
  have hW : WideRegion x := ⟨by omega, hxhi⟩
  have hlv1 := hshift1
  have hlv2 := hshift2
  -- the live magnitudes, at the magnitude words
  rcases Nat.eq_zero_or_pos y1 with hz1 | hp1
  · subst hz1
    rw [mulExpTree_zero, int256_zero_word']
    -- the other result is nonnegative: `int256 y2 ≥ int256 0 = 0` keeps `y2` on the
    -- nonnegative-word side
    rcases Nat.eq_zero_or_pos y2 with hz2 | hp2
    · subst hz2
      rw [mulExpTree_zero, int256_zero_word']
    · have h0 : int256 (0 : Nat) = 0 := int256_zero_word'
      rw [h0] at hle
      have hy2small : y2 < 2 ^ 255 := by
        by_contra hbig
        have := int256_y_neg (by omega) hy2
        omega
      obtain ⟨hm0, _, _, _⟩ := mulMagnitude_bracket_live hy2 hxw (by omega) habs2 hx0 hW hlv2
      rw [int256_tree_pos hp2 hy2small]
      exact hm0
  rcases Nat.eq_zero_or_pos y2 with hz2 | hp2
  · subst hz2
    rw [mulExpTree_zero, int256_zero_word']
    have h0 : int256 (0 : Nat) = 0 := int256_zero_word'
    rw [h0] at hle
    have hy1big : 2 ^ 255 ≤ y1 := by
      by_contra hsmall
      have h1 : int256 y1 = (y1 : Int) := int256_of_lt (by omega)
      rw [h1] at hle
      have : y1 = 0 := by exact_mod_cast le_antisymm (by exact_mod_cast hle) (Nat.zero_le y1)
      omega
    have hm255 := mag_word_small hy1 (by omega) hxw habs1 hx0 hW hlv1
    obtain ⟨hm0, _, _, _⟩ := mulMagnitude_bracket_live hy1 hxw (by omega) habs1 hx0 hW hlv1
    rw [int256_tree_neg hy1big hy1 hm255]
    linarith [hm0]
  -- both multipliers nonzero
  by_cases hneg1 : y1 < 2 ^ 255
  · -- y1 on the nonnegative-word side, hence so is y2
    have hy2small : y2 < 2 ^ 255 := by
      by_contra hbig
      have hn := int256_y_neg (by omega) hy2
      have hp := int256_of_lt hneg1
      rw [hp] at hle
      have : (0:Int) ≤ (y1 : Int) := Int.natCast_nonneg y1
      omega
    have h12 : y1 ≤ y2 := by
      have ha := int256_of_lt hneg1
      have hb := int256_of_lt hy2small
      rw [ha, hb] at hle
      exact_mod_cast hle
    have haa2 : absTree y2 = y2 := absTree_nonneg hy2small
    rw [int256_tree_pos hp1 hneg1, int256_tree_pos hp2 hy2small]
    refine mulMagnitudeY_region_mono (by omega) h12 ?_ hxw hW hx0 hlv2
    rw [← haa2]
    exact habs2
  · -- y1 on the negative-word side
    have hy1big : 2 ^ 255 ≤ y1 := by omega
    by_cases hneg2 : y2 < 2 ^ 255
    · -- signs differ: a nonpositive result against a nonnegative one
      have hm255a := mag_word_small hy1 (by omega) hxw habs1 hx0 hW hlv1
      obtain ⟨hm0a, _, _, _⟩ := mulMagnitude_bracket_live hy1 hxw (by omega) habs1 hx0 hW hlv1
      obtain ⟨hm0b, _, _, _⟩ := mulMagnitude_bracket_live hy2 hxw (by omega) habs2 hx0 hW hlv2
      rw [int256_tree_neg hy1big hy1 hm255a, int256_tree_pos hp2 hneg2]
      linarith [hm0a, hm0b]
    · -- both negative: magnitudes reverse
      have hy2big : 2 ^ 255 ≤ y2 := by omega
      have haa1 : absTree y1 = 2 ^ 256 - y1 := absTree_neg hy1big hy1
      have haa2 : absTree y2 = 2 ^ 256 - y2 := absTree_neg hy2big hy2
      have h21 : absTree y2 ≤ absTree y1 := by
        rw [haa1, haa2]
        have ha := int256_neg_eq_abs hy1big hy1
        have hb := int256_neg_eq_abs hy2big hy2
        rw [ha, hb, haa1, haa2] at hle
        have h1 : ((2 ^ 256 - y2 : Nat) : Int) ≤ ((2 ^ 256 - y1 : Nat) : Int) := by omega
        exact_mod_cast h1
      have hmag : int256 (mulMagnitudeTree (absTree y2) x) ≤
          int256 (mulMagnitudeTree (absTree y1) x) := by
        refine mulMagnitudeY_region_mono ?_ h21 habs1 hxw hW hx0 ?_
        · have : 1 ≤ absTree y2 := absTree_pos hy2 (by omega)
          omega
        · rw [← mulShift_abs_norm habs1]
          exact hlv1
      have hm255a := mag_word_small hy1 (by omega) hxw habs1 hx0 hW hlv1
      have hm255b := mag_word_small hy2 (by omega) hxw habs2 hx0 hW hlv2
      rw [int256_tree_neg hy1big hy1 hm255a, int256_tree_neg hy2big hy2 hm255b,
        mulMagnitude_abs_norm habs1, mulMagnitude_abs_norm habs2]
      linarith [hmag]

end ExpYul
