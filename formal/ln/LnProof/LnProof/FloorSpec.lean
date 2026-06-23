import LnProof.FloorAssembly

/-!
# The floor-cut specification of the `lnWad` model

Top-line cut statement: for every input `1 ≤ x < 2^255`, the model output
`r` satisfies the two exponential-cut predicates that correspond to
`r ≤ 10^27·ln(x/10^18) < r + 2` under the standard real interpretation.

The two sides are arithmetized without real numbers through the
partial sums `S_N(t) = Σ_{j≤N} t^j/j!` of the exponential, using
the Taylor-cut interface from `LnProof.ExpSum`:

* `FloorSpecA` says `e^(r/10^27) ≤ x/10^18` (for negative `r`, the
  reciprocal form `e^(|r|/10^27) ≥ 10^18/x`), corresponding to
  `r ≤ 10^27·ln(x/10^18)`.
* `FloorSpecB` says `x/10^18 < e^((r+2)/10^27)` with one part in
  `10^30` of strictness margin (reciprocal form for `r + 2 ≤ 0`),
  corresponding to `10^27·ln(x/10^18) < r + 2`.

Both are `capUB`/`capLB` statements over `QS = 10^27·2^99`: a `capUB`
is a `∀ N` bound on every integer-scaled partial sum, a `capLB` exhibits
one witness partial sum. `LnProof.ExpLogCutSpec` packages these predicates
as an explicit log-cut specification.
-/

namespace LnFloorCert
open LnGeneratedModel LnPoly LnExp LnFloor

-- The self-corrected model term repeats the accumulator (the `s == -1` test
-- reads the shifted result), so elaboration-time `whnf` of it is expensive.
-- Keep it opaque here; the `decide +kernel` facts below still reduce it in the
-- kernel, which ignores this hint.
attribute [local irreducible] model_ln_wad_evm model_ln_wad_to_wad_evm

set_option maxRecDepth 4096

/-- `r ≤ 10^27·ln(x/10^18)`, arithmetized. -/
def FloorSpecA (r : Int) (x : Nat) : Prop :=
  if 0 ≤ r then
    capUB (r.toNat * 2 ^ 99) QS x (10 ^ 18)
  else
    capLB ((-r).toNat * 2 ^ 99) QS (10 ^ 18) x

/-- `10^27·ln(x/10^18) < r + 2`, arithmetized with `1/10^30` slack. -/
def FloorSpecB (r : Int) (x : Nat) : Prop :=
  if -1 ≤ r then
    capLB ((r + 2).toNat * 2 ^ 99) QS (x * 10 ^ 31) (10 ^ 18 * (10 ^ 31 - 10))
  else
    capUB ((-(r + 2)).toNat * 2 ^ 99) QS (10 ^ 18 * (10 ^ 31 - 10)) (x * 10 ^ 31)

/-! ## Small pieces -/

theorem expNum_zero (q : Nat) : ∀ n, expNum n 0 q = fact n * q ^ n := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    show (k + 1) * q * expNum k 0 q + 0 ^ (k + 1) = fact (k + 1) * q ^ (k + 1)
    rw [ih]
    have h0 : (0 : Nat) ^ (k + 1) = 0 := Nat.zero_pow (by omega)
    rw [h0]
    show (k + 1) * q * (fact k * q ^ k) + 0 = (k + 1) * fact k * q ^ (k + 1)
    have e : q ^ (k + 1) = q ^ k * q := Nat.pow_succ _ _
    rw [e]
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    omega

theorem capUB_diag {q y : Nat} (_hq : 0 < q) : capUB 0 q y y := by
  intro n
  rw [expNum_zero]
  have e : fact n * q ^ n * y = y * (fact n * q ^ n) := Nat.mul_comm _ _
  omega

/-- The model maps the wad exactly to zero. -/
theorem model_at_wad : toInt (model_ln_wad_evm 1000000000000000000) = 0 := by
  decide +kernel

/-- Binade window for the mantissa, low-shift side. -/
theorem mant_window_le {x : Nat} (h1 : 1 ≤ x) (h2 : x < 2 ^ 255)
    (hc : evmClz x ≤ 160) :
    mant x * 2 ^ (160 - evmClz x) ≤ x ∧ x < (mant x + 1) * 2 ^ (160 - evmClz x) := by
  obtain ⟨me, _, _⟩ := mant_facts h1 h2
  have hclz : evmClz x = 255 - Nat.log2 x := evmClz_eq h1 (by omega)
  have hm : mant x = x * 2 ^ (255 - Nat.log2 x) / 2 ^ 160 := me
  rw [hclz] at hc ⊢
  have hdm := Nat.div_add_mod (x * 2 ^ (255 - Nat.log2 x)) (2 ^ 160)
  have hml := Nat.mod_lt (x * 2 ^ (255 - Nat.log2 x)) (y := 2 ^ 160) (by decide)
  have hsplit : 2 ^ (255 - Nat.log2 x) * 2 ^ (160 - (255 - Nat.log2 x)) = 2 ^ 160 := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [hm]
  generalize hgq : x * 2 ^ (255 - Nat.log2 x) / 2 ^ 160 = q at *
  generalize hgA : (2 : Nat) ^ (255 - Nat.log2 x) = A at *
  generalize hgB : (2 : Nat) ^ (160 - (255 - Nat.log2 x)) = B at *
  have hA0 : 0 < A := by rw [← hgA]; exact Nat.pow_pos (by omega)
  constructor
  · refine Nat.le_of_mul_le_mul_left ?_ hA0
    have e1 : A * (q * B) = 2 ^ 160 * q := by
      rw [show A * (q * B) = q * (A * B) from by
        simp only [Nat.mul_left_comm], hsplit]
      exact Nat.mul_comm _ _
    have e2 : A * x = x * A := Nat.mul_comm _ _
    generalize hg1 : A * (q * B) = T1 at e1 ⊢
    generalize hg3 : A * x = T3 at e2 ⊢
    generalize hg4 : x * A = T4 at e2 hdm
    generalize hg5 : 2 ^ 160 * q = T5 at e1 hdm
    omega
  · have hlt : x * A < (q + 1) * 2 ^ 160 := by
      have e : (q + 1) * 2 ^ 160 = 2 ^ 160 * q + 2 ^ 160 := by
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
      omega
    refine Nat.lt_of_mul_lt_mul_left (a := A) ?_
    have e1 : A * x = x * A := Nat.mul_comm _ _
    have e2 : A * ((q + 1) * B) = (q + 1) * 2 ^ 160 := by
      rw [show A * ((q + 1) * B) = (q + 1) * (A * B) from by
        simp only [Nat.mul_assoc, Nat.mul_comm], hsplit]
    generalize hg1 : A * x = T1 at e1 ⊢
    generalize hg2 : x * A = T2 at e1 hlt
    generalize hg3 : A * ((q + 1) * B) = T3 at e2 ⊢
    generalize hg5 : (q + 1) * 2 ^ 160 = T5 at e2 hlt
    omega

/-- Binade window, high-shift side: the mantissa is exact. -/
theorem mant_window_gt {x : Nat} (h1 : 1 ≤ x) (h2 : x < 2 ^ 255)
    (hc : 160 < evmClz x) :
    mant x = x * 2 ^ (evmClz x - 160) := by
  obtain ⟨me, _, _⟩ := mant_facts h1 h2
  have hclz : evmClz x = 255 - Nat.log2 x := evmClz_eq h1 (by omega)
  have hm : mant x = x * 2 ^ (255 - Nat.log2 x) / 2 ^ 160 := me
  rw [hclz] at hc ⊢
  have hsplit : (2 : Nat) ^ (255 - Nat.log2 x) =
      2 ^ 160 * 2 ^ ((255 - Nat.log2 x) - 160) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [hm, hsplit]
  have e : x * (2 ^ 160 * 2 ^ ((255 - Nat.log2 x) - 160)) =
      x * 2 ^ ((255 - Nat.log2 x) - 160) * 2 ^ 160 := by
    simp only [Nat.mul_comm, Nat.mul_left_comm]
  rw [e]
  exact Nat.mul_div_cancel _ (by decide)

theorem clz_bounds {x : Nat} (h1 : 1 ≤ x) (h2 : x < 2 ^ 255) :
    1 ≤ evmClz x ∧ evmClz x ≤ 255 := by
  have hclz : evmClz x = 255 - Nat.log2 x := evmClz_eq h1 (by omega)
  have hlog : Nat.log2 x < 255 := (Nat.log2_lt (by omega)).mpr (by omega)
  omega

/-- On the `m ≥ S` branch with a nonnegative shift, the accumulator is
positive, so the output cannot be negative. -/
theorem v_pos_ge_pos {m c : Nat} (h1 : Sc ≤ m) (h2 : m < MHI) (hc : c ≤ 160) :
    0 ≤ toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551514598262029661683100 := by
  have hX1 := x1_nonneg_geF h1 h2
  have hx0 : 0 ≤ toInt (x1W (zWord m)) * 7450580596923828125 :=
    Int.mul_nonneg hX1 (by omega)
  have hl : 0 ≤ ln2kInt c := by
    unfold ln2kInt
    rw [if_pos hc]
    exact Int.mul_nonneg (by omega) (Int.natCast_nonneg _)
  generalize toInt (x1W (zWord m)) * 7450580596923828125 = X at hx0 ⊢
  omega

/-! ## The theorem -/

/-- **Floor specification.** For every `1 ≤ x < 2^255` the model output
`r` satisfies `r ≤ 10^27·ln(x/10^18) < r + 2`: the model computes
`⌊10^27·ln(x/10^18)⌋` exactly or one less. -/
theorem model_ln_wad_floor {x : Nat} (h1 : 1 ≤ x) (h2 : x < 2 ^ 255) :
    FloorSpecA (toInt (model_ln_wad_evm x)) x ∧
      FloorSpecB (toInt (model_ln_wad_evm x)) x := by
  by_cases hne : x = 1000000000000000000
  · subst hne
    rw [model_at_wad]
    constructor
    · show FloorSpecA 0 1000000000000000000
      unfold FloorSpecA
      rw [if_pos (by omega)]
      show capUB ((0 : Int).toNat * 2 ^ 99) QS 1000000000000000000 (10 ^ 18)
      have e : (0 : Int).toNat * 2 ^ 99 = 0 := by decide
      rw [e]
      exact capUB_diag QS_pos
    · show FloorSpecB 0 1000000000000000000
      unfold FloorSpecB
      rw [if_pos (by omega)]
      exact ⟨1, by decide +kernel⟩
  · obtain ⟨hbr1, hbr2⟩ := model_floor_bracket h1 h2 hne
    rw [show (4722366482869645213696 : Int) = 2 ^ 72 from by decide] at hbr1 hbr2
    have hbr2' : toInt (x1W (zWord (mant x))) * 7450580596923828125 +
        ln2kInt (evmClz x) + 116873961749927929127912020551514598262029661683100 <
        (toInt (model_ln_wad_evm x) + 1) * 2 ^ 72 := by
      have e : (toInt (model_ln_wad_evm x) + 1) * 2 ^ 72 =
          toInt (model_ln_wad_evm x) * 2 ^ 72 + 2 ^ 72 := by
        rw [Int.add_mul, Int.one_mul]
      omega
    -- Generalize the model word: it is the self-corrected floor, whose term
    -- doubles the accumulator; keeping it opaque avoids reducing it below.
    revert hbr1 hbr2'
    generalize toInt (model_ln_wad_evm x) = R
    intro hbr1 hbr2'
    obtain ⟨me, hmlo, hmhi⟩ := mant_facts h1 h2
    have hmant_eq : mant x = x * 2 ^ (255 - Nat.log2 x) / 2 ^ 160 := me
    have hmant_lo : MLO ≤ mant x := by rw [hmant_eq]; exact hmlo
    have hmant_hi : mant x < MHI := by rw [hmant_eq]; exact hmhi
    obtain ⟨hc1, hc255⟩ := clz_bounds h1 h2
    rcases Nat.lt_or_ge (mant x) Sc with hbranch | hbranch
    · -- m < S
      rcases Nat.lt_or_ge 160 (evmClz x) with hcgt | hc
      · have hw := mant_window_gt h1 h2 hcgt
        constructor
        · unfold FloorSpecA
          rcases Int.lt_or_le R 0 with hr | hr
          · rw [if_neg (by omega)]
            exact an_lt_neg hmant_lo hbranch hcgt hc255 hbr1 hbr2' hr hw
          · rw [if_pos hr]
            exact up_lt_neg hmant_lo hbranch hcgt hc255 hbr1 hr hw
        · unfold FloorSpecB
          rcases Int.lt_or_le R (-1) with hr | hr
          · rw [if_neg (by omega)]
            exact bn_lt_neg hmant_lo hbranch hcgt hc255 hbr2' (by omega) hw
          · rw [if_pos (by omega)]
            exact lo_lt_neg hmant_lo hbranch hcgt hc255 hbr2' hbr1 (by omega) hw
      · obtain ⟨hw1, hw2⟩ := mant_window_le h1 h2 hc
        constructor
        · unfold FloorSpecA
          rcases Int.lt_or_le R 0 with hr | hr
          · rw [if_neg (by omega)]
            exact an_lt_pos hmant_lo hbranch hc1 hc hbr1 hbr2' hr hw1
          · rw [if_pos hr]
            exact up_lt_pos hmant_lo hbranch hc1 hc hbr1 hr hw1
        · unfold FloorSpecB
          rcases Int.lt_or_le R (-1) with hr | hr
          · rw [if_neg (by omega)]
            exact bn_lt_pos hmant_lo hbranch hc1 hc hbr2' (by omega) hw2
          · rw [if_pos (by omega)]
            exact lo_lt_pos hmant_lo hbranch hc1 hc hbr2' hbr1 (by omega) hw2
    · -- m ≥ S
      rcases Nat.lt_or_ge 160 (evmClz x) with hcgt | hc
      · have hw := mant_window_gt h1 h2 hcgt
        constructor
        · unfold FloorSpecA
          rcases Int.lt_or_le R 0 with hr | hr
          · rw [if_neg (by omega)]
            exact an_ge_neg hbranch hmant_hi hcgt hc255 hbr1 hbr2' hr hw
          · rw [if_pos hr]
            exact up_ge_neg hbranch hmant_hi hcgt hc255 hbr1 hr hw
        · unfold FloorSpecB
          rcases Int.lt_or_le R (-1) with hr | hr
          · rw [if_neg (by omega)]
            exact bn_ge_neg hbranch hmant_hi hcgt hc255 hbr2' (by omega) hw
          · rw [if_pos (by omega)]
            exact lo_ge_neg hbranch hmant_hi hcgt hc255 hbr2' hbr1 (by omega) hw
      · obtain ⟨hw1, hw2⟩ := mant_window_le h1 h2 hc
        have hVpos := v_pos_ge_pos hbranch hmant_hi hc
        have hrpos : 0 ≤ R := by
          rcases Int.lt_or_le R 0 with hr | hr
          · exfalso
            have hRle : (R + 1) * 2 ^ 72 ≤ 0 := by
              have hle : R + 1 ≤ 0 := by omega
              have := mul_le_mul_right_nonneg hle (show (0 : Int) ≤ 2 ^ 72 by omega)
              generalize hgT : (R + 1) * 2 ^ 72 = T at this ⊢
              omega
            omega
          · exact hr
        constructor
        · unfold FloorSpecA
          rw [if_pos hrpos]
          exact up_ge_pos hbranch hmant_hi hc1 hc hbr1 hrpos hw1
        · unfold FloorSpecB
          rw [if_pos (by omega)]
          exact lo_ge_pos hbranch hmant_hi hc1 hc hbr2' (by omega) hw2

/-- Floor specification for the wad-scale wrapper: the ray-scale output keeps
the certified logarithm bracket, and the wrapper output is exactly its signed
floor division by `10^9`. -/
def FloorSpecToWad (ray wad : Int) (x : Nat) : Prop :=
  FloorSpecA ray x ∧ FloorSpecB ray x ∧
    wad * 1000000000 ≤ ray ∧ ray < (wad + 1) * 1000000000

/-- **Wad floor specification.** The `lnWadToWad` model returns the signed
floor of the certified ray-scale `lnWad` model divided by `10^9`, so the
ray-scale floor bracket is packaged with the exact division window. -/
theorem model_ln_wad_to_wad_floor {x : Nat} (h1 : 1 ≤ x) (h2 : x < 2 ^ 255) :
    FloorSpecToWad (toInt (model_ln_wad_evm x))
      (toInt (model_ln_wad_to_wad_evm x)) x := by
  obtain ⟨ha, hb⟩ := model_ln_wad_floor h1 h2
  obtain ⟨hlo, hhi⟩ := to_wad_floor_window (by omega : x < 2 ^ 256)
  -- Keep both model words opaque: their terms self-correct (and the wad word
  -- nests the ray word twice), so unifying them directly is expensive.
  revert ha hb hlo hhi
  generalize toInt (model_ln_wad_evm x) = R
  generalize toInt (model_ln_wad_to_wad_evm x) = W
  intro ha hb hlo hhi
  exact ⟨ha, hb, hlo, hhi⟩

/-- The ray-scale model output is negative exactly below one wad. -/
theorem model_ln_wad_negative_iff {x : Nat} (h1 : 1 ≤ x) (h2 : x < 2 ^ 255) :
    toInt (model_ln_wad_evm x) < 0 ↔ x < 10 ^ 18 := by
  constructor
  · intro hneg
    rcases Nat.lt_or_ge x (10 ^ 18) with hlt | hxle
    · exact hlt
    · have hm := model_ln_wad_mono (x := 10 ^ 18) (y := x) (by decide) hxle h2
      have hi := toInt_of_sle
        (model_lt (by decide : (10 ^ 18 : Nat) < 2 ^ 256))
        (model_lt (by omega : x < 2 ^ 256)) hm
      have hzero : toInt (model_ln_wad_evm (10 ^ 18)) = 0 := by
        rw [model_ln_wad_one_wad]
        decide
      rw [hzero] at hi
      omega
  · intro hx
    rcases Int.lt_or_le (toInt (model_ln_wad_evm x)) 0 with hneg | hrnon
    · exact hneg
    · obtain ⟨ha, _⟩ := model_ln_wad_floor h1 h2
      unfold FloorSpecA at ha
      rw [if_pos hrnon] at ha
      have h0 := ha 0
      simp only [expNum, fact, Nat.pow_zero, Nat.mul_one, Nat.one_mul] at h0
      omega

/-- The wad-scale wrapper output is negative exactly below one wad. -/
theorem model_ln_wad_to_wad_negative_iff {x : Nat} (h1 : 1 ≤ x) (h2 : x < 2 ^ 255) :
    toInt (model_ln_wad_to_wad_evm x) < 0 ↔ x < 10 ^ 18 := by
  constructor
  · intro hneg
    rcases Nat.lt_or_ge x (10 ^ 18) with hlt | hxle
    · exact hlt
    · have hm := model_ln_wad_to_wad_mono (x := 10 ^ 18) (y := x) (by decide) hxle h2
      have hi := toInt_of_sle
        (to_wad_lt (by decide : (10 ^ 18 : Nat) < 2 ^ 256))
        (to_wad_lt (by omega : x < 2 ^ 256)) hm
      have hzero : toInt (model_ln_wad_to_wad_evm (10 ^ 18)) = 0 := by
        rw [model_ln_wad_to_wad_one_wad]
        decide
      rw [hzero] at hi
      omega
  · intro hx
    have hrneg := (model_ln_wad_negative_iff h1 h2).mpr hx
    obtain ⟨_, _, hlo, _⟩ := model_ln_wad_to_wad_floor h1 h2
    rcases Int.lt_or_le (toInt (model_ln_wad_to_wad_evm x)) 0 with hwneg | hwpos
    · exact hwneg
    · have hprod : 0 ≤ toInt (model_ln_wad_to_wad_evm x) * 1000000000 := by
        exact Int.mul_nonneg hwpos (by omega)
      omega

end LnFloorCert
