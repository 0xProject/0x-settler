import LnProof.Floor.Assembly
import LnProof.Floor.CarryIndependent.CertificateRuntime
import LnProof.Floor.CarryIndependent.Upper

open FormalYul
open FormalYul.Preservation

/-!
# The floor-cut specification of the `lnWad` model

Top-line cut statement: for every input `1 ≤ x < 2^255`, the body output
`r` satisfies the two exponential-cut predicates that correspond to
`r ≤ 10^27·ln(x/10^18) < r + 2` under the standard real interpretation.

The two sides are arithmetized without real numbers through the
partial sums `S_N(t) = Σ_{j≤N} t^j/j!` of the exponential, using
the Taylor-cut interface from `Common.Foundation.ExpSum`:

* `FloorSpecA` says `e^(r/10^27) ≤ x/10^18` (for negative `r`, the
  reciprocal form `e^(|r|/10^27) ≥ 10^18/x`), corresponding to
  `r ≤ 10^27·ln(x/10^18)`.
* `FloorSpecB` says `x/10^18 < e^((r+2)/10^27)` with one part in
  `10^30` of strictness margin (reciprocal form for `r + 2 ≤ 0`),
  corresponding to `10^27·ln(x/10^18) < r + 2`.

Both are `capUB`/`capLB` statements over `QS = 10^27·2^99`: a `capUB`
is a `∀ N` bound on every integer-scaled partial sum, a `capLB` exhibits
one witness partial sum. `LnProof.Floor.CutEquiv` packages these predicates
as an explicit log-cut specification.
-/

namespace LnFloorCert
open LnYul Common.Poly Common.Exp LnFloor

-- The self-corrected body term repeats the accumulator (the `s == -1` test
-- reads the shifted result), so elaboration-time `whnf` of it is expensive.
-- Keep it opaque here; the `decide +kernel` facts below still reduce it in the
-- kernel, which ignores this hint.
attribute [local irreducible] lnWadToRayBody lnWadBody

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

/-- The body maps the wad exactly to zero. -/
theorem lnWadToRayBody_at_wad : int256 (lnWadToRayBody 1000000000000000000) = 0 := by
  have h := lnWadToRayBody_one_wad
  rw [show (10 : Nat) ^ 18 = 1000000000000000000 by decide] at h
  rw [h]
  decide

/-- On the `m ≥ S` branch with a nonnegative shift, the accumulator is
positive, so the output cannot be negative. -/
theorem v_pos_ge_pos {m c : Nat} (h1 : Sc ≤ m) (h2 : m < MHI) (hc : c ≤ 160) :
    0 ≤ int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551560854268589826112230 := by
  have hX1 := x1_nonneg_geF h1 h2
  have hx0 : 0 ≤ int256 (x1W (zWord m)) * 7450580596923828125 :=
    Int.mul_nonneg hX1 (by omega)
  have hl : 0 ≤ ln2kInt c := by
    unfold ln2kInt
    rw [if_pos hc]
    exact Int.mul_nonneg (by omega) (Int.natCast_nonneg _)
  generalize int256 (x1W (zWord m)) * 7450580596923828125 = X at hx0 ⊢
  omega

/-! ## Floor theorem -/

/-- Floor specification. For every `1 ≤ x < 2^255` the body output
`r` satisfies `r ≤ 10^27·ln(x/10^18) < r + 2`: the body computes
`⌊10^27·ln(x/10^18)⌋` exactly or one less. -/
theorem lnWadToRayBody_floor {x : Nat} (h1 : 1 ≤ x) (h2 : x < 2 ^ 255) :
    FloorSpecA (int256 (lnWadToRayBody x)) x ∧
      FloorSpecB (int256 (lnWadToRayBody x)) x := by
  by_cases hne : x = 1000000000000000000
  · subst hne
    rw [lnWadToRayBody_at_wad]
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
  · obtain ⟨me, hmlo, hmhi⟩ := mant_facts h1 h2
    have hmant_eq : mant x = x * 2 ^ (255 - Nat.log2 x) / 2 ^ 160 := me
    have hmant_lo : MLO ≤ mant x := by rw [hmant_eq]; exact hmlo
    have hmant_hi : mant x < MHI := by rw [hmant_eq]; exact hmhi
    have hcoreRuntime := LnFloorCarry.certified_mantissa_runtime_core_bound
      hmant_lo hmant_hi
    have hray : (LnFloorCarry.rayScale : Real) = 10 ^ 27 := by
      norm_num [LnFloorCarry.rayScale]
    have hlimit :
        LnFloorCarry.coreErrorLimit =
          (LnFloorCarry.coreErrorNum : Real) / LnFloorCarry.coreErrorDen := by
      norm_num [LnFloorCarry.coreErrorLimit, LnFloorCarry.coreErrorNum,
        LnFloorCarry.coreErrorDen]
    have hcore :
        LnFloorCarry.coreErrorRay (mant x)
            (int256 (x1W (zWord (mant x)))) <
          (LnFloorCarry.coreErrorNum : Real) / LnFloorCarry.coreErrorDen := by
      rw [hray, hlimit] at hcoreRuntime
      simpa only [LnFloorCarry.coreErrorRay] using hcoreRuntime
    have haCut := LnFloorCarry.lnWadToRayBody_cut_of_core_bound
      h1 h2 hne hcore
    have ha : FloorSpecA (int256 (lnWadToRayBody x)) x := by
      simpa [FloorSpecA, CutLeLogWadRay, CutExpLe, CutRatioLeExp] using haCut
    obtain ⟨hbr1, hbr2⟩ := lnWadToRayBody_floor_bracket h1 h2 hne
    rw [show (4722366482869645213696 : Int) = 2 ^ 72 from by decide] at hbr1 hbr2
    have hbr2' : int256 (x1W (zWord (mant x))) * 7450580596923828125 +
        ln2kInt (evmClz x) + 116873961749927929127912020551560854268589826112230 <
        (int256 (lnWadToRayBody x) + 1) * 2 ^ 72 := by
      have e : (int256 (lnWadToRayBody x) + 1) * 2 ^ 72 =
          int256 (lnWadToRayBody x) * 2 ^ 72 + 2 ^ 72 := by
        rw [Int.add_mul, Int.one_mul]
      omega
    generalize int256 (lnWadToRayBody x) = R at hbr1 hbr2' ha ⊢
    obtain ⟨hc1, hc255⟩ := clz_bounds h1 h2
    rcases Nat.lt_or_ge (mant x) Sc with hbranch | hbranch
    · -- m < S
      rcases Nat.lt_or_ge 160 (evmClz x) with hcgt | hc
      · have hw := mant_window_gt h1 h2 hcgt
        constructor
        · exact ha
        · unfold FloorSpecB
          rcases Int.lt_or_le R (-1) with hr | hr
          · rw [if_neg (by omega)]
            exact bn_lt_neg hmant_lo hbranch hcgt hc255 hbr2' (by omega) hw
          · rw [if_pos (by omega)]
            exact lo_lt_neg hmant_lo hbranch hcgt hc255 hbr2' hbr1 (by omega) hw
      · obtain ⟨_, hw2⟩ := mant_window_le h1 h2 hc
        constructor
        · exact ha
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
        · exact ha
        · unfold FloorSpecB
          rcases Int.lt_or_le R (-1) with hr | hr
          · rw [if_neg (by omega)]
            exact bn_ge_neg hbranch hmant_hi hcgt hc255 hbr2' (by omega) hw
          · rw [if_pos (by omega)]
            exact lo_ge_neg hbranch hmant_hi hcgt hc255 hbr2' hbr1 (by omega) hw
      · obtain ⟨_, hw2⟩ := mant_window_le h1 h2 hc
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
        · exact ha
        · unfold FloorSpecB
          rw [if_pos (by omega)]
          exact lo_ge_pos hbranch hmant_hi hc1 hc hbr2' (by omega) hw2

/-- Floor specification for the wad-scale wrapper: the ray-scale output keeps
the certified logarithm bracket, and the wrapper output is exactly its signed
floor division by `10^9`. -/
def FloorSpecToWad (ray wad : Int) (x : Nat) : Prop :=
  FloorSpecA ray x ∧ FloorSpecB ray x ∧
    wad * 1000000000 ≤ ray ∧ ray < (wad + 1) * 1000000000

/-- Wad floor specification. The `lnWad` body returns the signed
floor of the certified ray-scale `lnWadToRay` body divided by `10^9`, so the
ray-scale floor bracket is packaged with the exact division window. -/
theorem lnWadBody_floor {x : Nat} (h1 : 1 ≤ x) (h2 : x < 2 ^ 255) :
    FloorSpecToWad (int256 (lnWadToRayBody x))
      (int256 (lnWadBody x)) x := by
  obtain ⟨ha, hb⟩ := lnWadToRayBody_floor h1 h2
  obtain ⟨hlo, hhi⟩ := to_wad_floor_window (by omega : x < 2 ^ 256)
  -- Keep both body words opaque: their terms self-correct (and the wad word
  -- nests the ray word twice), so unifying them directly is expensive.
  revert ha hb hlo hhi
  generalize int256 (lnWadToRayBody x) = R
  generalize int256 (lnWadBody x) = W
  intro ha hb hlo hhi
  exact ⟨ha, hb, hlo, hhi⟩

/-- The ray-scale body output is negative exactly below one wad. -/
theorem lnWadToRayBody_negative_iff {x : Nat} (h1 : 1 ≤ x) (h2 : x < 2 ^ 255) :
    int256 (lnWadToRayBody x) < 0 ↔ x < 10 ^ 18 := by
  constructor
  · intro hneg
    rcases Nat.lt_or_ge x (10 ^ 18) with hlt | hxle
    · exact hlt
    · have hm := lnWadToRayBody_mono (x := 10 ^ 18) (y := x) (by decide) hxle h2
      have hi := toInt_of_sle
        (lnWadToRayBody_lt (by decide : (10 ^ 18 : Nat) < 2 ^ 256))
        (lnWadToRayBody_lt (by omega : x < 2 ^ 256)) hm
      have hzero : int256 (lnWadToRayBody (10 ^ 18)) = 0 := by
        rw [lnWadToRayBody_one_wad]
        decide
      rw [hzero] at hi
      omega
  · intro hx
    rcases Int.lt_or_le (int256 (lnWadToRayBody x)) 0 with hneg | hrnon
    · exact hneg
    · obtain ⟨ha, _⟩ := lnWadToRayBody_floor h1 h2
      unfold FloorSpecA at ha
      rw [if_pos hrnon] at ha
      have h0 := ha 0
      simp only [expNum, fact, Nat.pow_zero, Nat.mul_one, Nat.one_mul] at h0
      omega

/-- The wad-scale wrapper output is negative exactly below one wad. -/
theorem lnWadBody_negative_iff {x : Nat} (h1 : 1 ≤ x) (h2 : x < 2 ^ 255) :
    int256 (lnWadBody x) < 0 ↔ x < 10 ^ 18 := by
  constructor
  · intro hneg
    rcases Nat.lt_or_ge x (10 ^ 18) with hlt | hxle
    · exact hlt
    · have hm := lnWadBody_mono (x := 10 ^ 18) (y := x) (by decide) hxle h2
      have hi := toInt_of_sle
        (to_wad_lt (by decide : (10 ^ 18 : Nat) < 2 ^ 256))
        (to_wad_lt (by omega : x < 2 ^ 256)) hm
      have hzero : int256 (lnWadBody (10 ^ 18)) = 0 := by
        rw [lnWadBody_one_wad]
        decide
      rw [hzero] at hi
      omega
  · intro hx
    have hrneg := (lnWadToRayBody_negative_iff h1 h2).mpr hx
    obtain ⟨_, _, hlo, _⟩ := lnWadBody_floor h1 h2
    rcases Int.lt_or_le (int256 (lnWadBody x)) 0 with hwneg | hwpos
    · exact hwneg
    · have hprod : 0 ≤ int256 (lnWadBody x) * 1000000000 := by
        exact Int.mul_nonneg hwpos (by omega)
      omega

end LnFloorCert
