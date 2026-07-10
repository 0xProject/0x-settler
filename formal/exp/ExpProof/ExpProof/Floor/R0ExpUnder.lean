import ExpProof.Floor.R0Exp

/-!
# The deficit (under) side of the per-point `r0`-vs-`exp` bridge, and the seam bound

This module contains the counterpart to the never-over `r0Scaled_real_over_within`: the per-point
deficit `scale·exp(rt) ≤ r0 + 2993/1000` (`r0Scaled_real_under_within`), both signs and any scale
`2¹²⁵ ≤ scale ≤ scaleQ67`, with the same four-link chain:

1. link-1 deficit against the grid rational including the `div` floor, `≤ 2378/1000`;
2. the argument granularity (`Floor.GranV`) — free on the `t ≥ 0` half, `≤ (5¹⁸/2⁴¹)·1644901622230542074/10¹⁹`
   (`Mp`-folded) on the `t ≤ 0` half;
3. the `Mp` factor, `≤ 2/25` (via `r0 ≤ 1.45·scaleQ67`);
4. the under-direction reduced-argument gap, `≤ 307/1000` (via `exp(rt) ≤ √2·(1+ε)`).

Per sign half the links sum inside the budget: `2378/1000 + 2/25 + 307/1000 ≤ 2993/1000` on the
`t ≥ 0` half (granularity free there) and `2378/1000 + 2/25 +
(5¹⁸/2⁴¹)·1644901622230542074/10¹⁹ + 218/1000 ≤ 2993/1000` on the `t ≤ 0` half. The budget feeds
the `k = 65` deficit envelope `(2993/1000 + MARGIN)/2² < 1`. The module closes with the
octave-seam `r0`-doubling
bound `r0₁ + 3 ≤ 2·r0₂` (`SeamR0Bound`), where the `1 − exp(−1/RAY)` seam slack (≈ `8.5·10¹⁰` grid
units against `r0₂ > 2¹²³`) dwarfs both per-point budgets and the three integer units.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation
open Common.Poly

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2000

noncomputable section

/-- `exp(reducedArg) ≤ 14143/10000` (both signs). The reduced argument is within a half-octave,
`reducedArg ≤ log2/2 + 33/(32·2¹²⁸)`, so `exp` is at most `√2·(1+ε)`, which the `14143/10000`
ceiling covers with room. Drives the under gap-1. -/
theorem exp_reducedArg_le_sqrt2bound {x : Nat} (hx : x < 2 ^ 256)
    (hW : WideRegion x) :
    Real.exp (reducedArg x) ≤ 14143 / 10000 := by
  have hclose := abs_lt.mp (reducedArg_close_wide hx hW)
  have hthalf : (int256 (tTree x) : Real) / (2 ^ 129 : Real) ≤ Real.log 2 / 2 := by
    rcases le_or_gt 0 (int256 (tTree x)) with htnn | htneg
    · exact t_over_2128_le_half_log2 hx hW
    · have htle : (int256 (tTree x) : Real) ≤ 0 := by exact_mod_cast le_of_lt htneg
      have hlog2 : (0:Real) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have : (int256 (tTree x) : Real) / (2 ^ 129 : Real) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg htle (by positivity)
      linarith [this, hlog2]
  set u : Real := 9 / (8 * (2 ^ 129 : Real)) with hu
  have hupos : (0:Real) < u := by rw [hu]; positivity
  have husmall : u ≤ 1 / 100000 := by rw [hu, div_le_div_iff₀ (by positivity) (by norm_num)]; norm_num
  clear_value u
  have hrt : reducedArg x ≤ Real.log 2 / 2 + u := by linarith [hclose.2, hthalf]
  have hmono : Real.exp (reducedArg x) ≤ Real.exp (Real.log 2 / 2 + u) := Real.exp_le_exp.mpr hrt
  have hsplit : Real.exp (Real.log 2 / 2 + u) = Real.sqrt 2 * Real.exp u := by
    rw [Real.exp_add]; congr 1
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num : (0:Real) < 2)]; ring_nf
  have hep : (0:Real) < Real.exp u := Real.exp_pos u
  have h1u : (0:Real) < 1 - u := by
    have : (1:Real) / 100000 < 1 := by norm_num
    linarith [husmall, this]
  have hexpu : Real.exp u ≤ 1 / (1 - u) := by
    have h1 : (1 : Real) - u ≤ Real.exp (-u) := by linarith [Real.add_one_le_exp (-u)]
    rw [Real.exp_neg] at h1
    have h2 : (1 - u) * Real.exp u ≤ 1 := by
      have := mul_le_mul_of_nonneg_right h1 (le_of_lt hep)
      rwa [inv_mul_cancel₀ (ne_of_gt hep)] at this
    rw [le_div_iff₀ h1u]; linarith [h2]
  have hsqrt2 : Real.sqrt 2 ≤ 141422 / 100000 := by rw [Real.sqrt_le_iff]; constructor <;> norm_num
  calc Real.exp (reducedArg x) ≤ Real.sqrt 2 * Real.exp u := by rw [← hsplit]; exact hmono
    _ ≤ (141422 / 100000) * (1 / (1 - u)) :=
        mul_le_mul hsqrt2 hexpu (le_of_lt hep) (by norm_num)
    _ ≤ 14143 / 10000 := by
        rw [mul_one_div, div_le_div_iff₀ h1u (by norm_num)]; nlinarith [husmall]

/-! ## The `r0` bracket on the nonneg half -/

/-- `r0` is bracketed on the nonneg half: `scaleQ67 ≤ r0` and `100·r0 ≤ 145·scaleQ67`. -/
theorem r0_bracket_nonneg {scale x : Nat} (hshi : scale ≤ scaleQ67) (hx : x < 2 ^ 256)
    (hW : WideRegion x)
    (htnn : 0 ≤ int256 (tTree x)) :
    (scale : Int) ≤ int256 (r0ScaledTree scale x) ∧
      100 * (int256 (r0ScaledTree scale x)) ≤ 145 * (scale : Int) := by
  obtain ⟨hfloor_lo, hfloor_hi⟩ := r0_floor_sandwich hshi hx hW
  have h145 := num_le_145_den hx hW htnn
  have hSnn : (0:Int) ≤ (scale : Int) := Int.natCast_nonneg _
  set r0 := int256 (r0ScaledTree scale x) with hr0def
  set ev := (evTree x : Int) with hevdef
  set tod := int256 (todTree x) with htoddef
  have hden072 : (330077261860684142693791478386293573392 : Int) ≤ ev - tod := by
    have := den_ge_194 hx hW; rw [← hevdef, ← htoddef] at this; exact this
  have hdenpos : (0:Int) < ev - tod := lt_of_lt_of_le (by norm_num) hden072
  -- tod ≥ 0 on nonneg half
  have htodnn : (0:Int) ≤ tod := by
    obtain ⟨_, _, htodlo, _⟩ := todTree_bound_wide hx hW
    have hodnn : (0:Int) ≤ (odTree x : Int) := Int.natCast_nonneg _
    have htod : (2 ^ 129 : Int) * tod ≤ int256 (tTree x) * (odTree x : Int) := htodlo
    have hpos : (0:Int) ≤ int256 (tTree x) * (odTree x : Int) := mul_nonneg htnn hodnn
    nlinarith [htod, hpos]
  refine ⟨?_, ?_⟩
  · -- scale ≤ r0:  scale·num < (r0+1)·den, num ≥ den ⟹ scale·den < (r0+1)·den ⟹ scale < r0+1
    have hnumden : (scale : Int) * (ev - tod) ≤ (scale : Int) * (ev + tod) := by
      nlinarith [htodnn, hSnn]
    have h : (scale : Int) * (ev - tod) < (r0 + 1) * (ev - tod) := lt_of_le_of_lt hnumden hfloor_hi
    have := lt_of_mul_lt_mul_right h (le_of_lt hdenpos)
    omega
  · -- 100·r0 ≤ 145·scale:  100·r0·den ≤ 100·scale·num ≤ scale·145·den
    have h1 : 100 * (r0 * (ev - tod)) ≤ 100 * ((scale : Int) * (ev + tod)) :=
      mul_le_mul_of_nonneg_left hfloor_lo (by norm_num)
    have h2 : (scale : Int) * (100 * (ev + tod)) ≤ (scale : Int) * (145 * (ev - tod)) :=
      mul_le_mul_of_nonneg_left h145 hSnn
    have hchain : 100 * r0 * (ev - tod) ≤ 145 * (scale : Int) * (ev - tod) := by nlinarith [h1, h2]
    exact le_of_mul_le_mul_right hchain hdenpos

/-! ## The piecewise link-1 carry table -/

/-- Horner evaluation of a nonnegative-coefficient polynomial is nonnegative and monotone on the
nonnegative axis. -/
theorem evalPoly_nonneg_mono {p : List Int} (hp : ∀ c ∈ p, 0 ≤ c) :
    ∀ {a b : Int}, 0 ≤ a → a ≤ b →
      0 ≤ Common.Poly.evalPoly p a ∧ Common.Poly.evalPoly p a ≤ Common.Poly.evalPoly p b := by
  induction p with
  | nil => intro a b _ _; simp [Common.Poly.evalPoly]
  | cons c cs ih =>
    intro a b ha hab
    have hc : 0 ≤ c := hp c List.mem_cons_self
    have hcs : ∀ d ∈ cs, (0:Int) ≤ d := fun d hd => hp d (List.mem_cons_of_mem _ hd)
    obtain ⟨hnn_a, hmono⟩ := ih hcs ha hab
    have hb : 0 ≤ b := le_trans ha hab
    refine ⟨?_, ?_⟩
    · simp only [Common.Poly.evalPoly]
      have := mul_nonneg ha hnn_a
      omega
    · simp only [Common.Poly.evalPoly]
      have h1 : a * Common.Poly.evalPoly cs a ≤ b * Common.Poly.evalPoly cs a :=
        mul_le_mul_of_nonneg_right hab hnn_a
      have h2 : b * Common.Poly.evalPoly cs a ≤ b * Common.Poly.evalPoly cs b :=
        mul_le_mul_of_nonneg_left hmono hb
      omega

/-- The odd-accumulator domain cap `odNumV v ≤ odCap` (`= odVPoly` at `vmaxV + 1`): all `odVPoly`
coefficients are nonnegative, so the edge evaluation caps every grid point of the domain. -/
def odCap : Int := 174678221397644049575777143361928794627879205226578653562590130996770143609877303657406822247010342954119346790867564782461851026886997547906404137068846862087419955814213206609572436845308432

theorem odNumV_le_odCap {v : Nat} (hv : (v : Int) ≤ (ExpCertV.vmaxV : Int) + 1) :
    (odNumV v : Int) ≤ odCap := by
  rw [odNumV_eq_poly]
  have hcoeffs : ∀ c ∈ ExpCertV.odVPoly, (0:Int) ≤ c := by
    unfold ExpCertV.odVPoly; intro c hc; fin_cases hc <;> positivity
  have h := (evalPoly_nonneg_mono hcoeffs (Int.natCast_nonneg v) hv).2
  calc Common.Poly.evalPoly ExpCertV.odVPoly (v : Int)
      ≤ Common.Poly.evalPoly ExpCertV.odVPoly ((ExpCertV.vmaxV : Int) + 1) := h
    _ = odCap := by unfold ExpCertV.odVPoly ExpCertV.vmaxV odCap; norm_num [Common.Poly.evalPoly]

/-- The per-piece link-1 carry rows over the shared `granPieces` table, at the common `×100`
integer scale. Positive half (quadratic in the `DO` floor, `r0` bounded through the runtime floor
and the odd cap): the carry fits `1378/1000` of one denominator. Negative half over `DU` with
`r0 ≤ scaleQ67`. -/
def Link1PieceOK : Int × Int × Int × Int × Int → Prop
  | (_, _, T, DO, DU) =>
      1000 * ((2 ^ 637 + 269746241 * 2 ^ 480 * T) *
          (200 * (0x6f05b59d3b2000000000000000000000 : Int) * (DO * 2 ^ 725) +
           200 * (0x6f05b59d3b2000000000000000000000 : Int) * T * odCap +
           800 * (0x6f05b59d3b2000000000000000000000 : Int) * 2 ^ 637)) +
        200000 * 2 ^ 637 * (DO * 2 ^ 725) ≤
          137800 * ((DO * 2 ^ 725) * (DO * 2 ^ 725)) ∧
      1000 * ((2 ^ 637 + 269746241 * 2 ^ 480 * T) *
          (200 * (0x6f05b59d3b2000000000000000000000 : Int) * (DU * 2 ^ 725) +
           800 * (0x6f05b59d3b2000000000000000000000 : Int) * 2 ^ 637)) +
        200000 * 2 ^ 637 * (DU * 2 ^ 725) ≤
          137800 * ((DU * 2 ^ 725) * (DU * 2 ^ 725))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8000 in
theorem link1Pieces_hold : ∀ p ∈ ExpCertV.granPieces, Link1PieceOK p := by
  unfold Link1PieceOK
  decide +kernel

/-! ## Link 1 (under side): the grid rational vs `r0` -/

/-- **Link-1 under (nonneg half)**: `1000·(scaleQ67·NUMv − r0·DENv) ≤ 2378·DENv`. The floor residual
costs one denominator; the odd-truncation carry `(2⁶³⁷ + Wod·2⁴⁸⁰·t)·(scaleQ67 + r0)` is aggregated
piecewise over `granPieces` (`t ≤ T` and `DO·2⁷²⁵ ≤ DENv` per piece, the certified
`Link1PieceOK` row closing the quadratic), fitting `1.378` denominators. -/
theorem link1_under_int {scale x : Nat} (hslo : 2 ^ 125 ≤ scale) (hshi : scale ≤ scaleQ67)
    (hx : x < 2 ^ 256)
    (hW : WideRegion x)
    (htnn : 0 ≤ int256 (tTree x)) :
    1000 * ((scale : Int) * NUMv (vTree x) (int256 (tTree x)) -
        int256 (r0ScaledTree scale x) * DENv (vTree x) (int256 (tTree x))) ≤
      2378 * DENv (vTree x) (int256 (tTree x)) := by
  obtain ⟨hfloor_lo, hfloor_hi⟩ := r0_floor_sandwich hshi hx hW
  obtain ⟨hEp_lo, _, _, _⟩ := bridge_facts hx hW
  obtain ⟨htOp_lo, htOp_hi⟩ := tOd_bracket_nonneg hx hW htnn
  obtain ⟨hr0lo, hr0hi145⟩ := r0_bracket_nonneg hshi hx hW htnn
  obtain ⟨hDEN_lo, hDEN_up⟩ := DENv_runtime_bracket hx hW htnn
  have hshiI : (scale : Int) ≤ (0x6f05b59d3b2000000000000000000000 : Int) := by
    have h : ((scale : Nat) : Int) ≤ ((scaleQ67 : Nat) : Int) := by exact_mod_cast hshi
    have hs : ((scaleQ67 : Nat) : Int) = 0x6f05b59d3b2000000000000000000000 := by
      unfold scaleQ67; norm_num
    rw [hs] at h
    exact h
  have hLHS : (scale : Int) * NUMv (vTree x) (int256 (tTree x)) -
      int256 (r0ScaledTree scale x) * DENv (vTree x) (int256 (tTree x)) ≤
      2 ^ 637 * ((evTree x : Int) - int256 (todTree x)) +
        (2 ^ 637 + 269746241 * 2 ^ 480 * int256 (tTree x)) * ((scale : Int) + int256 (r0ScaledTree scale x)) := by
    unfold NUMv DENv
    set r0 := int256 (r0ScaledTree scale x) with hr0def
    set ev := (evTree x : Int) with hevdef
    set tod := int256 (todTree x) with htoddef
    set t := int256 (tTree x) with htdef
    set Ep := (evNumV (vTree x) : Int) with hEpdef
    set Op := (odNumV (vTree x) : Int) with hOpdef
    have h2126r0_np : (scale : Int) - r0 ≤ 0 := by linarith [hr0lo]
    have hr0p_nn : (0:Int) ≤ (scale : Int) + r0 := by
      have := Int.natCast_nonneg scale
      linarith [hr0lo]
    -- Ep·2^110·(scale−r0) ≤ 2^637·ev·(scale−r0)
    have hterm1 : Ep * 2 ^ 111 * ((scale : Int) - r0) ≤ 2 ^ 637 * ev * ((scale : Int) - r0) := by
      apply mul_le_mul_of_nonpos_right _ h2126r0_np
      nlinarith [hEp_lo]
    -- t·Op·(scale+r0) ≤ (2^637·tod + 2^637 + Wod·2^480·t)·(scale+r0)
    have hterm2 : t * Op * ((scale : Int) + r0) ≤
        (2 ^ 637 * tod + 2 ^ 637 + 269746241 * 2 ^ 480 * t) * ((scale : Int) + r0) :=
      mul_le_mul_of_nonneg_right htOp_hi hr0p_nn
    -- floor: scale·num − r0·den < den, scaled by 2^637
    have hfloor : (scale : Int) * (ev + tod) - r0 * (ev - tod) ≤ (ev - tod) := by
      linarith [hfloor_hi]
    have hfloor638 : (2:Int) ^ 637 * ((scale : Int) * (ev + tod) - r0 * (ev - tod)) ≤
        2 ^ 637 * (ev - tod) := mul_le_mul_of_nonneg_left hfloor (by positivity)
    nlinarith [hterm1, hterm2, hfloor638]
  -- select the covering piece; its certified facts drive the aggregation
  obtain ⟨_, hvsplit⟩ := tsq_split_wide hx hW
  have hvmaxI : ((vTree x : Nat) : Int) ≤ (ExpCertV.vmaxV : Int) := by
    exact_mod_cast vTree_le_vmax_wide hx hW
  obtain ⟨p, hp, hplo, hphi⟩ :=
    piecesCover_sound hvmaxI 0 granPieces_cover (Int.natCast_nonneg (vTree x))
  obtain ⟨vlo, vhi, T, DO, DU⟩ := p
  obtain ⟨hDOpos, _, _, hTnn, hDOfl, _, _, _, _, _, _⟩ :=
    granPieces_ok _ hp (vTree x) hplo hphi
  have hrow := (link1Pieces_hold _ hp).1
  have hcaps := granPieces_caps _ hp
  set r0 := int256 (r0ScaledTree scale x) with hr0def
  set t := int256 (tTree x) with htdef
  set den := (evTree x : Int) - int256 (todTree x) with hdendef
  set D := DENv (vTree x) t with hDdef
  set S := (scale : Int) with hSdef
  set Op := (odNumV (vTree x) : Int) with hOpdef
  have hSpos : (0 : Int) < S := by
    rw [hSdef]
    exact_mod_cast lt_of_lt_of_le (by norm_num : (0:Nat) < 2 ^ 125) hslo
  have hS67 : S ≤ (0x6f05b59d3b2000000000000000000000 : Int) := by rw [hSdef]; exact hshiI
  have hr0nn : (0 : Int) ≤ r0 := le_trans (le_of_lt hSpos) hr0lo
  -- `t ≤ T` on the piece
  have htT : t ≤ T := by
    have hsq := tsq_lt_capsq hvsplit hphi hcaps
    nlinarith [hsq, htnn, hTnn]
  have hOpnn : (0 : Int) ≤ Op := by rw [hOpdef]; exact Int.natCast_nonneg _
  have hOple : Op ≤ odCap := by rw [hOpdef]; exact odNumV_le_odCap (by linarith [hvmaxI])
  -- the piece's denominator floor holds at the runtime `t`
  have hDO_D : DO * 2 ^ 725 ≤ D := by
    have h1 : t * Op ≤ T * Op := mul_le_mul_of_nonneg_right htT hOpnn
    have h2 : DO * 2 ^ 725 ≤ (evNumV (vTree x) : Int) * 2 ^ 111 - T * Op := by
      rw [hOpdef]; exact hDOfl
    rw [hDdef]; unfold DENv; rw [← hOpdef]; linarith [h1, h2]
  have hDOpos' : (0 : Int) < DO * 2 ^ 725 := by positivity
  -- ×100 floor lift: `100·r0·D ≤ 100·S·NUMv + 145·Wev·2^591·S`
  have hEp111 : 2 ^ 637 * (evTree x : Int) ≤ (evNumV (vTree x) : Int) * 2 ^ 111 := by
    nlinarith [hEp_lo]
  have hnumlift : 2 ^ 637 * ((evTree x : Int) + int256 (todTree x)) ≤ NUMv (vTree x) t := by
    unfold NUMv; rw [← hOpdef]; linarith [hEp111, htOp_lo]
  have hNUMD : NUMv (vTree x) t = D + 2 * (t * Op) := by
    rw [hDdef, hOpdef]; unfold NUMv DENv; ring
  have h100 : 100 * (r0 * D) ≤ 100 * (S * NUMv (vTree x) t) + 145 * (72572599271425 * 2 ^ 591) * S := by
    have h1 : r0 * D ≤ 2 ^ 637 * (r0 * den) + 72572599271425 * 2 ^ 591 * r0 := by
      nlinarith [hDEN_up, hr0nn]
    have h2 : 2 ^ 637 * (r0 * den) ≤ 2 ^ 637 * (S * ((evTree x : Int) + int256 (todTree x))) := by
      nlinarith [hfloor_lo]
    have h3 : 2 ^ 637 * (S * ((evTree x : Int) + int256 (todTree x))) ≤ S * NUMv (vTree x) t := by
      nlinarith [hnumlift, hSpos]
    have h4 : 100 * (72572599271425 * 2 ^ 591 * r0) ≤ 145 * (72572599271425 * 2 ^ 591) * S := by
      nlinarith [hr0hi145]
    nlinarith [h1, h2, h3, h4]
  -- transfer to the piece floor
  have hK : 200 * (S * (t * Op)) + 145 * (72572599271425 * 2 ^ 591) * S ≤
      200 * S * T * odCap + 800 * S * 2 ^ 637 := by
    have htOple : t * Op ≤ T * odCap := by nlinarith [htT, hOple, htnn, hOpnn]
    have hW : (145 : Int) * (72572599271425 * 2 ^ 591) ≤ 800 * 2 ^ 637 := by norm_num
    nlinarith [htOple, hW, hSpos]
  have htransfer : (100 * (S + r0) - 200 * S) * (DO * 2 ^ 725) ≤
      200 * S * T * odCap + 800 * S * 2 ^ 637 := by
    have hnn : (0 : Int) ≤ 100 * (S + r0) - 200 * S := by linarith [hr0lo]
    have h1 : (100 * (S + r0) - 200 * S) * (DO * 2 ^ 725) ≤ (100 * (S + r0) - 200 * S) * D :=
      mul_le_mul_of_nonneg_left hDO_D hnn
    nlinarith [h1, h100, hK, hNUMD]
  have h100DO : 100 * ((S + r0) * (DO * 2 ^ 725)) ≤
      200 * S * (DO * 2 ^ 725) + 200 * S * T * odCap + 800 * S * 2 ^ 637 := by
    nlinarith [htransfer]
  -- feed the certified piece row and cancel one factor of `DO·2^725`
  have hcoefT_nn : (0 : Int) ≤ 2 ^ 637 + 269746241 * 2 ^ 480 * T := by nlinarith [hTnn]
  -- the certified row holds at the literal maximal scale; every scale coefficient on its
  -- left-hand side is nonnegative, so it holds a fortiori at the symbolic scale
  have hrow_s : 1000 * ((2 ^ 637 + 269746241 * 2 ^ 480 * T) *
      (200 * S * (DO * 2 ^ 725) + 200 * S * T * odCap + 800 * S * 2 ^ 637)) +
        200000 * 2 ^ 637 * (DO * 2 ^ 725) ≤
      137800 * ((DO * 2 ^ 725) * (DO * 2 ^ 725)) := by
    have hS67S_nn : (0 : Int) ≤ (0x6f05b59d3b2000000000000000000000 : Int) - S := by
      linarith [hS67]
    have hOpcap_nn : (0 : Int) ≤ odCap := le_trans hOpnn hOple
    have h1 : 200 * S * (DO * 2 ^ 725) ≤
        200 * (0x6f05b59d3b2000000000000000000000 : Int) * (DO * 2 ^ 725) := by
      nlinarith [mul_nonneg hS67S_nn (le_of_lt hDOpos')]
    have h2 : 200 * S * T * odCap ≤
        200 * (0x6f05b59d3b2000000000000000000000 : Int) * T * odCap := by
      nlinarith [mul_nonneg hS67S_nn (mul_nonneg hTnn hOpcap_nn)]
    have h3 : 800 * S * 2 ^ 637 ≤
        800 * (0x6f05b59d3b2000000000000000000000 : Int) * 2 ^ 637 := by
      nlinarith [hS67S_nn]
    have hsum_le : 200 * S * (DO * 2 ^ 725) + 200 * S * T * odCap + 800 * S * 2 ^ 637 ≤
        200 * (0x6f05b59d3b2000000000000000000000 : Int) * (DO * 2 ^ 725) +
          200 * (0x6f05b59d3b2000000000000000000000 : Int) * T * odCap +
          800 * (0x6f05b59d3b2000000000000000000000 : Int) * 2 ^ 637 := by
      linarith [h1, h2, h3]
    have hmul_le := mul_le_mul_of_nonneg_left hsum_le hcoefT_nn
    linarith [hrow, hmul_le]
  have hXY : (100000 * ((2 ^ 637 + 269746241 * 2 ^ 480 * T) * (S + r0)) + 200000 * 2 ^ 637) *
      (DO * 2 ^ 725) ≤ (137800 * (DO * 2 ^ 725)) * (DO * 2 ^ 725) := by
    have h1 := mul_le_mul_of_nonneg_left h100DO hcoefT_nn
    nlinarith [h1, hrow_s]
  have hDIV : 100000 * ((2 ^ 637 + 269746241 * 2 ^ 480 * T) * (S + r0)) + 200000 * 2 ^ 637 ≤
      137800 * (DO * 2 ^ 725) :=
    le_of_mul_le_mul_right hXY hDOpos'
  -- `coef ≤ coefT`, then assemble
  have hcoef_le : 100000 * ((2 ^ 637 + 269746241 * 2 ^ 480 * t) * (S + r0)) ≤
      100000 * ((2 ^ 637 + 269746241 * 2 ^ 480 * T) * (S + r0)) := by
    have hSr0 : (0 : Int) ≤ S + r0 := by linarith [hr0nn, hSpos]
    nlinarith [htT, hSr0]
  have hfin3 : (1378 : Int) * (DO * 2 ^ 725) ≤ 1378 * D := by linarith [hDO_D]
  linarith [hLHS, hDEN_lo, hDIV, hcoef_le, hfin3]

/-- **Link-1 under (nonpositive half)**: the same `2378/1000` budget, with no piece machinery: on
this half `DENv = Ep·2¹¹¹ − t·Op ≥ 2⁶³⁸·ev`, so the even-truncation width and the `tod`-floor unit
are absorbed against `2⁶³⁸·ev ≥ 2⁶³⁸·A0`. -/
theorem link1_under_int_neg {scale x : Nat} (hslo : 2 ^ 125 ≤ scale) (hshi : scale ≤ scaleQ67)
    (hx : x < 2 ^ 256)
    (hW : WideRegion x)
    (htneg : int256 (tTree x) ≤ 0) :
    1000 * ((scale : Int) * NUMv (vTree x) (int256 (tTree x)) -
        int256 (r0ScaledTree scale x) * DENv (vTree x) (int256 (tTree x))) ≤
      2378 * DENv (vTree x) (int256 (tTree x)) := by
  obtain ⟨_, hfloor_hi⟩ := r0_floor_sandwich hshi hx hW
  obtain ⟨hEp_lo, hEp_hi, _, _⟩ := bridge_facts hx hW
  obtain ⟨htOp_hi, _⟩ := tOd_bracket_neg hx hW htneg
  have hr0le := r0_le_scale_neg hshi hx hW htneg
  obtain ⟨hr0lo, _⟩ := r0Scaled_bounds hslo hshi hx hW
  obtain ⟨hev_lo, _⟩ := evTree_facts (vTree_eq_wide hx hW).2
  obtain ⟨htod_lo126, _, _, _⟩ := todTree_bound_wide hx hW
  have hshiI : (scale : Int) ≤ (0x6f05b59d3b2000000000000000000000 : Int) := by
    have h : ((scale : Nat) : Int) ≤ ((scaleQ67 : Nat) : Int) := by exact_mod_cast hshi
    have hs : ((scaleQ67 : Nat) : Int) = 0x6f05b59d3b2000000000000000000000 := by
      unfold scaleQ67; norm_num
    rw [hs] at h
    exact h
  have hSnn : (0:Int) ≤ (scale : Int) := Int.natCast_nonneg _
  have hLHS : (scale : Int) * NUMv (vTree x) (int256 (tTree x)) -
      int256 (r0ScaledTree scale x) * DENv (vTree x) (int256 (tTree x)) ≤
      2 ^ 637 * ((evTree x : Int) - int256 (todTree x)) +
        72572599271425 * 2 ^ 591 * (scale : Int) + 2 * 2 ^ 637 * (scale : Int) := by
    unfold NUMv DENv
    set r0 := int256 (r0ScaledTree scale x) with hr0def
    set ev := (evTree x : Int) with hevdef
    set tod := int256 (todTree x) with htoddef
    set t := int256 (tTree x) with htdef
    set Ep := (evNumV (vTree x) : Int) with hEpdef
    set Op := (odNumV (vTree x) : Int) with hOpdef
    have hr0nn : (0:Int) ≤ r0 := by
      have : (0:Int) < 2 ^ 123 := by positivity
      linarith [hr0lo]
    have h2126r0_nn : (0:Int) ≤ (scale : Int) - r0 := by linarith [hr0le]
    have h2126r0_le : (scale : Int) - r0 ≤ (scale : Int) := by linarith [hr0nn]
    have hr0p_nn : (0:Int) ≤ (scale : Int) + r0 := by linarith [hr0nn, hSnn]
    have hr0p_le : (scale : Int) + r0 ≤ 2 * (scale : Int) := by linarith [hr0le]
    -- Ep·2^110·(scale−r0) ≤ 2^637·ev·(scale−r0) + Wev·2^590·scale
    have hterm1 : Ep * 2 ^ 111 * ((scale : Int) - r0) ≤
        2 ^ 637 * ev * ((scale : Int) - r0) + 72572599271425 * 2 ^ 591 * (scale : Int) := by
      have h1 : Ep * 2 ^ 111 * ((scale : Int) - r0) ≤
          (2 ^ 637 * ev + 72572599271425 * 2 ^ 591) * ((scale : Int) - r0) := by
        apply mul_le_mul_of_nonneg_right _ h2126r0_nn
        nlinarith [hEp_hi]
      have h2 : (72572599271425 : Int) * 2 ^ 590 * ((scale : Int) - r0) ≤
          72572599271425 * 2 ^ 591 * (scale : Int) := by
        nlinarith [h2126r0_le, hr0nn, hSnn]
      nlinarith [h1, h2]
    -- t·Op·(scale+r0) ≤ (2^637·tod + 2^637)·(scale+r0) ≤ 2^637·tod·(scale+r0) + 2·2^637·scale
    have hterm2 : t * Op * ((scale : Int) + r0) ≤
        2 ^ 637 * tod * ((scale : Int) + r0) + 2 * 2 ^ 637 * (scale : Int) := by
      have h1 : t * Op * ((scale : Int) + r0) ≤ (2 ^ 637 * tod + 2 ^ 637) * ((scale : Int) + r0) :=
        mul_le_mul_of_nonneg_right htOp_hi hr0p_nn
      have h2 : (2:Int) ^ 637 * ((scale : Int) + r0) ≤ 2 ^ 637 * (2 * (scale : Int)) :=
        mul_le_mul_of_nonneg_left hr0p_le (by positivity)
      nlinarith [h1, h2]
    -- floor: scale·num − r0·den ≤ den, scaled
    have hfloor : (scale : Int) * (ev + tod) - r0 * (ev - tod) ≤ (ev - tod) := by
      linarith [hfloor_hi]
    have hfloor638 : (2:Int) ^ 637 * ((scale : Int) * (ev + tod) - r0 * (ev - tod)) ≤
        2 ^ 637 * (ev - tod) := mul_le_mul_of_nonneg_left hfloor (by positivity)
    nlinarith [hterm1, hterm2, hfloor638]
  -- budget against DENv = Ep·2^111 − t·Op ≥ 2^638·ev ≥ 2^638·A0; den ≤ ev + 2^126
  set ev := (evTree x : Int) with hevdef
  set tod := int256 (todTree x) with htoddef
  set D := DENv (vTree x) (int256 (tTree x)) with hDdef
  have hev' : (415147853590918758559635130244235626256 : Int) ≤ ev := by
    have : (0x1385291795942d41ba5fd317688e18710 : Int) ≤ ev := by
      rw [hevdef]; exact_mod_cast hev_lo
    rw [show (0x1385291795942d41ba5fd317688e18710 : Int) =
      415147853590918758559635130244235626256 from by norm_num] at this
    exact this
  -- pair the runtime `den` against `D` through the `t·Od` bracket: one floor unit of slop
  have hOpnn : (0 : Int) ≤ (odNumV (vTree x) : Int) := Int.natCast_nonneg _
  have htOp_np : int256 (tTree x) * (odNumV (vTree x) : Int) ≤ 0 := by
    nlinarith [htneg, hOpnn]
  have hEp111 : 2 ^ 637 * ev ≤ (evNumV (vTree x) : Int) * 2 ^ 111 := by
    rw [hevdef]; nlinarith [hEp_lo]
  have hDden : 2 ^ 637 * (ev - tod) ≤ D + 2 ^ 637 := by
    rw [hDdef]; unfold DENv
    linarith [hEp111, htOp_hi]
  have hD_A : 2 ^ 637 * 415147853590918758559635130244235626256 ≤ D := by
    have h1 : 2 ^ 637 * 415147853590918758559635130244235626256 ≤ 2 ^ 637 * ev := by
      nlinarith [hev']
    rw [hDdef]; unfold DENv
    have h2 : 2 ^ 637 * ev ≤ (evNumV (vTree x) : Int) * 2 ^ 111 -
        int256 (tTree x) * (odNumV (vTree x) : Int) := by
      linarith [hEp111, htOp_np]
    linarith [h1, h2]
  -- 1000·(2^637 + Wev·2^591·S + 2·2^637·S) ≤ 1378·2^637·A0, relaxing the symbolic scale to the
  -- literal maximal one first
  have hSrelax : 1000 * (72572599271425 * 2 ^ 591 * (scale : Int) +
        2 * 2 ^ 637 * (scale : Int)) ≤
      1000 * (72572599271425 * 2 ^ 591 * (0x6f05b59d3b2000000000000000000000 : Int) +
        2 * 2 ^ 637 * (0x6f05b59d3b2000000000000000000000 : Int)) := by
    nlinarith [hshiI]
  have hlit : 1000 * (2 ^ 637 : Int) +
      1000 * (72572599271425 * 2 ^ 591 * (0x6f05b59d3b2000000000000000000000 : Int) +
        2 * 2 ^ 637 * (0x6f05b59d3b2000000000000000000000 : Int)) ≤
      (1378 : Int) * (2 ^ 637 * 415147853590918758559635130244235626256) := by
    norm_num
  linarith [hLHS, hDden, hD_A, hlit, hSrelax]

/-! ## The per-point deficit (nonneg half) -/

/-- **The per-point deficit (nonneg half).** `scaleQ67·exp(rt) ≤ r0 + 2993/1000`: link-1 `≤ 2378/1000`, the
`Mp` factor `≤ 2/25`, the under gap `≤ 307/1000`; the granularity is free on this half. -/
theorem r0_real_under_tight {scale x : Nat} (hslo : 2 ^ 125 ≤ scale) (hshi : scale ≤ scaleQ67)
    (hx : x < 2 ^ 256)
    (hW : WideRegion x)
    (htnn : 0 ≤ int256 (tTree x)) :
    (scale : Real) * Real.exp (reducedArg x) ≤ (int256 (r0ScaledTree scale x) : Real) + 2993 / 1000 := by
  obtain ⟨_, hthi⟩ := tTree_in_cert_domain_wide hx hW
  have hvle := vTree_le_vmax_wide hx hW
  have hsRnn : (0:Real) ≤ (scale : Real) := by positivity
  have hshiR : (scale : Real) ≤ (0x6f05b59d3b2000000000000000000000 : Real) := by
    have h : ((scale : Nat) : Real) ≤ ((scaleQ67 : Nat) : Real) := by exact_mod_cast hshi
    have hs : ((scaleQ67 : Nat) : Real) = 0x6f05b59d3b2000000000000000000000 := by
      unfold scaleQ67; norm_num
    rw [hs] at h
    exact h
  set t := int256 (tTree x) with htdef
  set v := vTree x with hvdef
  set r0 := int256 (r0ScaledTree scale x) with hr0def
  have htdom : t ≤ (ExpCertV.H129 : Int) := by
    rw [show ((ExpCertV.H129 : Nat) : Int) = 235865763225513294137944142764154484399 from by
      unfold ExpCertV.H129; norm_num]
    exact hthi
  have hD : 1108965543718 * 2 ^ 725 ≤ DENv v t := DENv_ge_over (by omega) hthi
  have hDpos : (0:Int) < DENv v t := lt_of_lt_of_le (by positivity) hD
  have hDR : (0:Real) < (DENv v t : Real) := by exact_mod_cast hDpos
  have hDE : (1:Int) ≤ evalPoly ExpCertV.denExpV t := certDE_pos htnn htdom
  have hDER : (0:Real) < (evalPoly ExpCertV.denExpV t : Real) := by
    have : (0:Int) < evalPoly ExpCertV.denExpV t := lt_of_lt_of_le one_pos hDE
    exact_mod_cast this
  -- link 1: scale·Qv ≤ r0 + 2378/1000
  have hlink1 := link1_under_int hslo hshi hx hW htnn
  have hQv_le : (scale : Real) * ((NUMv v t : Real) / (DENv v t : Real)) ≤
      (r0 : Real) + 2378 / 1000 := by
    rw [mul_div_assoc', div_le_iff₀ hDR]
    have hR := (@Int.cast_le Real _ _ _ _ _ _ _).mpr hlink1
    push_cast at hR
    nlinarith [hR, hDR]
  -- link 2 (free): NE/DE ≤ Qv
  obtain ⟨hgran1, _⟩ := gran_over_pair hx hW htnn
  -- link 3: Et ≤ (NE/DE)·Mpp ≤ Qv·Mpp; Mpp excess ≤ 2/25 via r0 ≤ 1.45·2^126
  have hcertup := certUp_real htnn htdom
  set Et := Real.exp ((t : Real) / (2 ^ 129 : Real)) with hEtdef
  set NE := evalPoly ExpCertV.numExpV t with hNEdef
  set DE := evalPoly ExpCertV.denExpV t with hDEdef
  set Mpp : Real := ((2 ^ 132 : Real) + 1) / (2 ^ 132 : Real) with hMppdef
  have hEt_le : Et ≤ ((NE : Real) / (DE : Real)) * Mpp := by
    have hc : Et ≤ ((2 ^ 132 + 1 : Int) : Real) * (NE : Real) /
        (((2 ^ 132 : Int) : Real) * (DE : Real)) := hcertup
    rw [hMppdef]
    have key : ((NE : Real) / (DE : Real)) * (((2 ^ 132 : Real) + 1) / (2 ^ 132 : Real)) =
        ((2 ^ 132 + 1 : Int) : Real) * (NE : Real) / (((2 ^ 132 : Int) : Real) * (DE : Real)) := by
      push_cast; field_simp; ring
    rw [key]; exact hc
  have hMpp_nn : (0:Real) ≤ Mpp := by rw [hMppdef]; positivity
  have hEt_le_Qv : Et ≤ ((NUMv v t : Real) / (DENv v t : Real)) * Mpp :=
    le_trans hEt_le (mul_le_mul_of_nonneg_right hgran1 hMpp_nn)
  have hMpp1 : Mpp - 1 = 1 / (2 ^ 132 : Real) := by rw [hMppdef]; field_simp
  obtain ⟨_, hr0hi145⟩ := r0_bracket_nonneg hshi hx hW htnn
  have hr0R : (r0 : Real) ≤ (145 / 100) * (0x6f05b59d3b2000000000000000000000 : Real) := by
    have h := (@Int.cast_le Real _ _ _ _ _ _ _).mpr hr0hi145
    push_cast at h
    nlinarith [h, hshiR]
  have hEt_bound : (scale : Real) * Et ≤ (r0 : Real) + 2378 / 1000 + 2 / 25 := by
    have h1 : (scale : Real) * Et ≤
        (scale : Real) * (((NUMv v t : Real) / (DENv v t : Real)) * Mpp) :=
      mul_le_mul_of_nonneg_left hEt_le_Qv hsRnn
    have h2 : (scale : Real) * (((NUMv v t : Real) / (DENv v t : Real)) * Mpp) =
        (scale : Real) * ((NUMv v t : Real) / (DENv v t : Real)) +
          ((scale : Real) * ((NUMv v t : Real) / (DENv v t : Real))) * (Mpp - 1) := by ring
    have h3 : ((scale : Real) * ((NUMv v t : Real) / (DENv v t : Real))) * (Mpp - 1) ≤ 2 / 25 := by
      rw [hMpp1]
      have hcap : (scale : Real) * ((NUMv v t : Real) / (DENv v t : Real)) ≤
          (145 / 100) * (0x6f05b59d3b2000000000000000000000 : Real) + 2378 / 1000 := by linarith [hQv_le, hr0R]
      have := mul_le_mul_of_nonneg_right hcap (by positivity : (0:Real) ≤ 1 / (2 ^ 132 : Real))
      have hfin : ((145 / 100) * (0x6f05b59d3b2000000000000000000000 : Real) + 2378 / 1000) * (1 / (2 ^ 132 : Real)) ≤
          2 / 25 := by norm_num
      linarith [this, hfin]
    linarith [h1, h2 ▸ h1, h3, hQv_le]
  -- link 4 (under gap): 2^126·(Ert − Et) ≤ 307/1000
  set Ert := Real.exp (reducedArg x) with hErtdef
  have hgapunder := reducedArg_close_under_wide hx hW
  have hExp_diff : Ert - Et ≤ (reducedArg x - (t : Real) / (2 ^ 129 : Real)) * Ert := exp_diff_le _ _
  have hErt_le := exp_reducedArg_le_sqrt2bound hx hW
  rw [← hErtdef] at hErt_le
  have hErt_nn : (0:Real) ≤ Ert := le_of_lt (Real.exp_pos _)
  have hgap126 : (scale : Real) * (Ert - Et) ≤ 307 / 1000 := by
    have hgap : Ert - Et ≤ (1025 / (1024 * (2 ^ 129 : Real))) * Ert :=
      le_trans hExp_diff (mul_le_mul_of_nonneg_right (le_of_lt hgapunder) hErt_nn)
    have h1 : (scale : Real) * (Ert - Et) ≤ (scale : Real) * ((1025 / (1024 * (2 ^ 129 : Real))) * Ert) :=
      mul_le_mul_of_nonneg_left hgap hsRnn
    have h2 : (scale : Real) * ((1025 / (1024 * (2 ^ 129 : Real))) * Ert) ≤
        (scale : Real) * ((1025 / (1024 * (2 ^ 129 : Real))) * (14143 / 10000)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hErt_le (by positivity)) hsRnn
    have h2' : (scale : Real) * ((1025 / (1024 * (2 ^ 129 : Real))) * (14143 / 10000)) ≤
        (0x6f05b59d3b2000000000000000000000 : Real) * ((1025 / (1024 * (2 ^ 129 : Real))) * (14143 / 10000)) :=
      mul_le_mul_of_nonneg_right hshiR (by positivity)
    have h3 : (0x6f05b59d3b2000000000000000000000 : Real) * ((1025 / (1024 * (2 ^ 129 : Real))) * (14143 / 10000)) ≤ 307 / 1000 := by
      norm_num
    linarith [h1, h2, h2', h3]
  have hdist : (scale : Real) * Ert = (scale : Real) * Et + (scale : Real) * (Ert - Et) := by
    ring
  show (scale : Real) * Ert ≤ (r0 : Real) + 2993 / 1000
  have hsum : (2378 : Real) / 1000 + 2 / 25 + 307 / 1000 ≤ 2993 / 1000 := by norm_num
  linarith [hEt_bound, hgap126, hdist, hsum]

/-! ## The per-point deficit (nonpositive half) -/

/-- **The per-point deficit (nonpositive half).** `scaleQ67·exp(rt) ≤ r0 + 2993/1000`: link-1 `≤ 2378/1000`,
the `Mp`-folded granularity `≤ (5¹⁸/2⁴¹)·1644901622230542074/10¹⁹`, the `Mp` factor `≤ 2/25`
(via `r0 ≤ scaleQ67`), the under gap `≤ 307/1000`. -/
theorem r0_real_under_tight_neg {scale x : Nat} (hslo : 2 ^ 125 ≤ scale)
    (hshi : scale ≤ scaleQ67) (hx : x < 2 ^ 256)
    (hW : WideRegion x)
    (htneg : int256 (tTree x) ≤ 0) :
    (scale : Real) * Real.exp (reducedArg x) ≤ (int256 (r0ScaledTree scale x) : Real) + 2993 / 1000 := by
  have htdom := tdom_neg hx hW htneg
  have hvle := vTree_le_vmax_wide hx hW
  have hsRnn : (0:Real) ≤ (scale : Real) := by positivity
  have hshiR : (scale : Real) ≤ (0x6f05b59d3b2000000000000000000000 : Real) := by
    have h : ((scale : Nat) : Real) ≤ ((scaleQ67 : Nat) : Real) := by exact_mod_cast hshi
    have hs : ((scaleQ67 : Nat) : Real) = 0x6f05b59d3b2000000000000000000000 := by
      unfold scaleQ67; norm_num
    rw [hs] at h
    exact h
  set t := int256 (tTree x) with htdef
  set v := vTree x with hvdef
  set r0 := int256 (r0ScaledTree scale x) with hr0def
  have hD : 1108965543718 * 2 ^ 725 ≤ DENv v t := DENv_ge_neg (by omega) htneg
  have hDpos : (0:Int) < DENv v t := lt_of_lt_of_le (by positivity) hD
  have hDR : (0:Real) < (DENv v t : Real) := by exact_mod_cast hDpos
  have hDEpos : (0:Int) < evalPoly ExpCertV.denExpV t := (certNE_pos_neg_aux htneg htdom).2
  have hDER : (0:Real) < (evalPoly ExpCertV.denExpV t : Real) := by exact_mod_cast hDEpos
  -- link 1: scale·Qv ≤ r0 + 2378/1000
  have hlink1 := link1_under_int_neg hslo hshi hx hW htneg
  have hQv_le : (scale : Real) * ((NUMv v t : Real) / (DENv v t : Real)) ≤
      (r0 : Real) + 2378 / 1000 := by
    rw [mul_div_assoc', div_le_iff₀ hDR]
    have hR := (@Int.cast_le Real _ _ _ _ _ _ _).mpr hlink1
    push_cast at hR
    nlinarith [hR, hDR]
  -- links 2+3: Et ≤ (NE/DE)·Mp = Qv·Mp + (NE/DE − Qv)·Mp
  have hcertup := certUp_real_neg htneg htdom
  set Et := Real.exp ((t : Real) / (2 ^ 129 : Real)) with hEtdef
  set NE := evalPoly ExpCertV.numExpV t with hNEdef
  set DE := evalPoly ExpCertV.denExpV t with hDEdef
  set Mp : Real := (2 ^ 132 : Real) / ((2 ^ 132 : Real) - 1) with hMpdef
  have hEt_le : Et ≤ ((NE : Real) / (DE : Real)) * Mp := by
    rw [hMpdef]
    have key : ((NE : Real) / (DE : Real)) * ((2 ^ 132 : Real) / ((2 ^ 132 : Real) - 1)) =
        ((2 ^ 132 : Int) : Real) * (NE : Real) /
          (((2 ^ 132 - 1 : Int) : Real) * (DE : Real)) := by
      push_cast; field_simp; ring
    rw [key]; exact hcertup
  obtain ⟨hgran1, hgran2⟩ := gran_under_pair hx hW htneg
  have hMp_nn : (0:Real) ≤ Mp := by
    rw [hMpdef]
    have : (0:Real) < (2 ^ 132 : Real) - 1 := by norm_num
    positivity
  have hMp1 : Mp - 1 = 1 / ((2 ^ 132 : Real) - 1) := by rw [hMpdef]; field_simp
  have hr0le := r0_le_scale_neg hshi hx hW htneg
  have hr0R : (r0 : Real) ≤ (0x6f05b59d3b2000000000000000000000 : Real) := by
    have h := (@Int.cast_le Real _ _ _ _ _ _ _).mpr hr0le
    push_cast at h
    linarith [h, hshiR]
  -- the certified granularity envelope at the 2^126 normalization, rescaled to the symbolic
  -- scale and relaxed to the literal maximal-scale budget
  have hgran2S : (scale : Real) * Mp *
      ((NE : Real) / (DE : Real) - (NUMv v t : Real) / (DENv v t : Real)) ≤
      3814697265625 * 1644901622230542074 / (10000000000000000000 * 2199023255552) := by
    have hdiff_nn : (0:Real) ≤ (NE : Real) / (DE : Real) - (NUMv v t : Real) / (DENv v t : Real) := by
      linarith [hgran1]
    have hMp' : Mp ≤ (2 ^ 131 : Real) / ((2 ^ 131 : Real) - 1) := by
      rw [hMpdef, div_le_div_iff₀ (by norm_num) (by norm_num)]
      norm_num
    have hMp_nn' : (0:Real) ≤ Mp := hMp_nn
    have h1 : (scale : Real) * Mp *
        ((NE : Real) / (DE : Real) - (NUMv v t : Real) / (DENv v t : Real)) ≤
        (scale : Real) * ((2 ^ 131 : Real) / ((2 ^ 131 : Real) - 1)) *
          ((NE : Real) / (DE : Real) - (NUMv v t : Real) / (DENv v t : Real)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMp' hsRnn) hdiff_nn
    have h2 := mul_le_mul_of_nonneg_left hgran2 hsRnn
    have h3 : (scale : Real) * (1644901622230542074 / 10000000000000000000) ≤
        (0x6f05b59d3b2000000000000000000000 : Real) * (1644901622230542074 / 10000000000000000000) :=
      mul_le_mul_of_nonneg_right hshiR (by positivity)
    nlinarith [h1, h2, h3]
  have hEt_bound : (scale : Real) * Et ≤ (r0 : Real) + 2378 / 1000 + 2 / 25 +
      3814697265625 * 1644901622230542074 / (10000000000000000000 * 2199023255552) := by
    have h1 : (scale : Real) * Et ≤ (scale : Real) * (((NE : Real) / (DE : Real)) * Mp) :=
      mul_le_mul_of_nonneg_left hEt_le hsRnn
    -- split: scale·(NE/DE)·Mp = scale·Qv + scale·Qv·(Mp−1) + scale·Mp·(NE/DE − Qv)
    have hsplit : (scale : Real) * (((NE : Real) / (DE : Real)) * Mp) =
        (scale : Real) * ((NUMv v t : Real) / (DENv v t : Real)) +
        ((scale : Real) * ((NUMv v t : Real) / (DENv v t : Real))) * (Mp - 1) +
        (scale : Real) * Mp *
          ((NE : Real) / (DE : Real) - (NUMv v t : Real) / (DENv v t : Real)) := by ring
    have hMpterm : ((scale : Real) * ((NUMv v t : Real) / (DENv v t : Real))) * (Mp - 1) ≤
        2 / 25 := by
      rw [hMp1]
      have hcap : (scale : Real) * ((NUMv v t : Real) / (DENv v t : Real)) ≤
          (0x6f05b59d3b2000000000000000000000 : Real) + 2378 / 1000 := by linarith [hQv_le, hr0R]
      have := mul_le_mul_of_nonneg_right hcap
        (by positivity : (0:Real) ≤ 1 / ((2 ^ 132 : Real) - 1))
      have hfin : ((0x6f05b59d3b2000000000000000000000 : Real) + 2378 / 1000) * (1 / ((2 ^ 132 : Real) - 1)) ≤ 2 / 25 := by
        rw [mul_one_div, div_le_div_iff₀ (by norm_num) (by norm_num)]
        norm_num
      linarith [this, hfin]
    linarith [h1, hsplit ▸ h1, hMpterm, hgran2S, hQv_le]
  -- link 4 (under gap): 2^126·(Ert − Et) ≤ 307/1000
  set Ert := Real.exp (reducedArg x) with hErtdef
  have hgapunder := reducedArg_close_under_wide hx hW
  have hExp_diff : Ert - Et ≤ (reducedArg x - (t : Real) / (2 ^ 129 : Real)) * Ert := exp_diff_le _ _
  have hErt_nn : (0:Real) ≤ Ert := le_of_lt (Real.exp_pos _)
  -- on this half `rt ≤ 1025/(1024·2¹²⁹)`, so `Ert ≤ 10001/10000`
  have hErt_le : Ert ≤ 10001 / 10000 := by
    have htle : (t : Real) ≤ 0 := by exact_mod_cast htneg
    have htdivle : (t : Real) / (2 ^ 129 : Real) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg htle (by positivity)
    have hrtle : reducedArg x ≤ 1025 / (1024 * (2 ^ 129 : Real)) := by
      linarith [hgapunder, htdivle]
    set u : Real := 1025 / (1024 * (2 ^ 129 : Real)) with hu
    have hupos : (0:Real) < u := by rw [hu]; positivity
    have husmall : u ≤ 1 / 100000 := by rw [hu]; norm_num
    have h1u : (0:Real) < 1 - u := by rw [hu]; norm_num
    have hmono : Ert ≤ Real.exp u := by
      rw [hErtdef]; exact Real.exp_le_exp.mpr (by rw [hu]; exact hrtle)
    clear_value u
    have hexpu : Real.exp u ≤ 1 / (1 - u) := by
      have h1 : (1 : Real) - u ≤ Real.exp (-u) := by linarith [Real.add_one_le_exp (-u)]
      rw [Real.exp_neg] at h1
      have hep : (0:Real) < Real.exp u := Real.exp_pos u
      have h2 : (1 - u) * Real.exp u ≤ 1 := by
        have := mul_le_mul_of_nonneg_right h1 (le_of_lt hep)
        rwa [inv_mul_cancel₀ (ne_of_gt hep)] at this
      rw [le_div_iff₀ h1u]; linarith [h2]
    have hfin : (1:Real) / (1 - u) ≤ 10001 / 10000 := by
      rw [div_le_div_iff₀ h1u (by norm_num)]; nlinarith [husmall]
    linarith [hmono, hexpu, hfin]
  have hgap126 : (scale : Real) * (Ert - Et) ≤ 218 / 1000 := by
    have hgap : Ert - Et ≤ (1025 / (1024 * (2 ^ 129 : Real))) * Ert :=
      le_trans hExp_diff (mul_le_mul_of_nonneg_right (le_of_lt hgapunder) hErt_nn)
    have h1 : (scale : Real) * (Ert - Et) ≤ (scale : Real) * ((1025 / (1024 * (2 ^ 129 : Real))) * Ert) :=
      mul_le_mul_of_nonneg_left hgap hsRnn
    have h2 : (scale : Real) * ((1025 / (1024 * (2 ^ 129 : Real))) * Ert) ≤
        (scale : Real) * ((1025 / (1024 * (2 ^ 129 : Real))) * (10001 / 10000)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hErt_le (by positivity)) hsRnn
    have h2' : (scale : Real) * ((1025 / (1024 * (2 ^ 129 : Real))) * (10001 / 10000)) ≤
        (0x6f05b59d3b2000000000000000000000 : Real) * ((1025 / (1024 * (2 ^ 129 : Real))) * (10001 / 10000)) :=
      mul_le_mul_of_nonneg_right hshiR (by positivity)
    have h3 : (0x6f05b59d3b2000000000000000000000 : Real) * ((1025 / (1024 * (2 ^ 129 : Real))) * (10001 / 10000)) ≤ 218 / 1000 := by
      norm_num
    linarith [h1, h2, h2', h3]
  have hdist : (scale : Real) * Ert = (scale : Real) * Et + (scale : Real) * (Ert - Et) := by
    ring
  show (scale : Real) * Ert ≤ (r0 : Real) + 2993 / 1000
  have hsum : (2378 : Real) / 1000 + 2 / 25 + 3814697265625 * 1644901622230542074 / (10000000000000000000 * 2199023255552) +
      218 / 1000 ≤ 2993 / 1000 := by norm_num
  linarith [hEt_bound, hgap126, hdist, hsum]

/-- **Per-point deficit (tight, any sign):** `scale·exp(rt) ≤ r0 + 2993/1000` (the deficit budget
is certified at the maximal scale, and smaller scales only shrink the true deficit). -/
theorem r0Scaled_real_under_within {scale x : Nat} (hslo : 2 ^ 125 ≤ scale)
    (hshi : scale ≤ scaleQ67) (hx : x < 2 ^ 256) (hW : WideRegion x) :
    (scale : Real) * Real.exp (reducedArg x) ≤ (int256 (r0ScaledTree scale x) : Real) + 2993 / 1000 := by
  rcases le_or_gt 0 (int256 (tTree x)) with htnn | htneg
  · exact r0_real_under_tight hslo hshi hx hW htnn
  · exact r0_real_under_tight_neg hslo hshi hx hW (le_of_lt htneg)

theorem r0_real_under_within_wide {x : Nat} (hx : x < 2 ^ 256)
    (hW : WideRegion x) :
    (0x6f05b59d3b2000000000000000000000 : Real) * Real.exp (reducedArg x) ≤ (int256 (r0Tree x) : Real) + 2993 / 1000 := by
  have h := r0Scaled_real_under_within (scale := scaleQ67) (by unfold scaleQ67; norm_num)
    (le_refl _) hx hW
  rw [r0Tree_eq_scaled]
  have hs : ((scaleQ67 : Nat) : Real) = 0x6f05b59d3b2000000000000000000000 := by
    unfold scaleQ67; norm_num
  rw [← hs]
  exact h

theorem r0_real_under_within {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    (0x6f05b59d3b2000000000000000000000 : Real) * Real.exp (reducedArg x) ≤ (int256 (r0Tree x) : Real) + 2993 / 1000 :=
  r0_real_under_within_wide hx (wideRegion_of_wad hC hC0)

/-! ## The octave-seam `r0`-doubling consequence -/

/-- `2¹²³ < r0Tree x` on the region, directly from the runtime quotient range. -/
theorem r0Tree_gt_2126 {x : Nat} (hx : x < 2 ^ 256)
    (hW : WideRegion x) :
    (2 : Real) ^ 123 < (int256 (r0Tree x) : Real) := by
  obtain ⟨hr0lo, _⟩ := r0Tree_bounds_wide hx hW
  have h : ((2 ^ 124 : Int) : Real) ≤ (int256 (r0Tree x) : Real) := by exact_mod_cast hr0lo
  have h2 : (2 : Real) ^ 123 < ((2 ^ 124 : Int) : Real) := by norm_num
  linarith [h, h2]

/-- `2¹²² < r0ScaledTree scale x` on the region, for `2^125 ≤ scale ≤ scaleQ67`. -/
theorem r0Scaled_gt_2122 {scale x : Nat} (hslo : 2 ^ 125 ≤ scale) (hshi : scale ≤ scaleQ67)
    (hx : x < 2 ^ 256) (hW : WideRegion x) :
    (2 : Real) ^ 122 < (int256 (r0ScaledTree scale x) : Real) := by
  obtain ⟨hr0lo, _⟩ := r0Scaled_bounds hslo hshi hx hW
  have h : ((2 ^ 123 : Int) : Real) ≤ (int256 (r0ScaledTree scale x) : Real) := by
    exact_mod_cast hr0lo
  have h2 : (2 : Real) ^ 122 < ((2 ^ 123 : Int) : Real) := by norm_num
  linarith [h, h2]

/-- **The seam exp relation.** Across a seam (`X2 = X1 + 1`, `k2 = k1 + 1`),
`exp(rt1) = 2·exp(rt2)·exp(−1/RAY)`. -/
theorem reducedArg_seam {x1 x2 : Nat}
    (hk : int256 (kTree x2) = int256 (kTree x1) + 1)
    (hadj : int256 x2 = int256 x1 + 1) :
    Real.exp (reducedArg x1) =
      2 * Real.exp (reducedArg x2) * Real.exp (-(1 / (10 ^ 27 : Real))) := by
  have hrel : reducedArg x1 = reducedArg x2 + Real.log 2 + (-(1 / (10 ^ 27 : Real))) := by
    unfold reducedArg
    rw [show (int256 x2 : Real) = (int256 x1 : Real) + 1 from by exact_mod_cast hadj,
      show (int256 (kTree x2) : Real) = (int256 (kTree x1) : Real) + 1 from by exact_mod_cast hk]
    ring
  rw [hrel, Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0:Real) < 2)]
  ring

/-- **`r0` at most doubles across a seam, three units short** (the real reduction of
`SeamR0Bound`). The strict slack from `exp(−1/RAY) < 1` (against `r0Tree x2 > 2¹²³`, worth
`≈ 8.5·10¹⁰` grid units) dwarfs the per-point envelopes and the three integer units the
seam-floor comparison consumes. -/
theorem r0_seam_double_wide {x1 x2 : Nat}
    (hx1 : x1 < 2 ^ 256) (hx2 : x2 < 2 ^ 256)
    (hW1 : WideRegion x1) (hW2 : WideRegion x2)
    (hk : int256 (kTree x2) = int256 (kTree x1) + 1)
    (hadj : int256 x2 = int256 x1 + 1) :
    int256 (r0Tree x1) + 3 ≤ 2 * int256 (r0Tree x2) := by
  have hover1 := r0_real_over_within_wide hx1 hW1
  have hunder2 := r0_real_under_within_wide hx2 hW2
  have hr0_2_big := r0Tree_gt_2126 hx2 hW2
  have hseam := reducedArg_seam hk hadj
  set E1 := Real.exp (reducedArg x1) with hE1
  set E2 := Real.exp (reducedArg x2) with hE2
  set y := Real.exp (-(1 / (10 ^ 27 : Real))) with hy
  have hy_pos : 0 < y := Real.exp_pos _
  -- y ≤ 1 - 1/(2·RAY)
  have hy_bound : y ≤ 1 - 1 / (2 * (10 ^ 27 : Real)) := by
    rw [hy]
    have hz : (0:Real) < 1 / (10 ^ 27 : Real) := by positivity
    have hez : (1 : Real) + 1 / (10 ^ 27 : Real) ≤ Real.exp (1 / (10 ^ 27 : Real)) := by
      have := Real.add_one_le_exp (1 / (10 ^ 27 : Real)); linarith [this]
    rw [Real.exp_neg]
    have hexppos : 0 < Real.exp (1 / (10 ^ 27 : Real)) := Real.exp_pos _
    rw [inv_le_iff_one_le_mul₀ hexppos]
    have h1z : (1 - 1 / (2 * (10 ^ 27 : Real))) * (1 + 1 / (10 ^ 27 : Real)) ≥ 1 := by
      rw [ge_iff_le]; nlinarith [sq_nonneg (1 / (10 ^ 27 : Real))]
    nlinarith [hez, h1z, hexppos, mul_pos (by positivity : (0:Real) < 1 - 1/(2*(10^27:Real))) hexppos]
  -- scaleQ67·E1 = 2·(scaleQ67·E2)·y ≤ 2·(r0_2 + U)·y
  have hE2bound : (0x6f05b59d3b2000000000000000000000 : Real) * E2 ≤ (int256 (r0Tree x2) : Real) + (2993 / 1000 : Real) :=
    hunder2
  have hr0_1 : (int256 (r0Tree x1) : Real) ≤
      2 * ((int256 (r0Tree x2) : Real) + (2993 / 1000 : Real)) * y +
        3814697265625 * 5737291786393199862 / (10000000000000000000 * 2199023255552) := by
    have h1 : (0x6f05b59d3b2000000000000000000000 : Real) * E1 = 2 * ((0x6f05b59d3b2000000000000000000000 : Real) * E2) * y := by
      rw [hseam]; ring
    have h2 : (int256 (r0Tree x1) : Real) ≤ (0x6f05b59d3b2000000000000000000000 : Real) * E1 +
        3814697265625 * 5737291786393199862 / (10000000000000000000 * 2199023255552) := hover1
    rw [h1] at h2
    have h3 : 2 * ((0x6f05b59d3b2000000000000000000000 : Real) * E2) * y ≤
        2 * ((int256 (r0Tree x2) : Real) + (2993 / 1000 : Real)) * y :=
      mul_le_mul_of_nonneg_right
        (by linarith [mul_le_mul_of_nonneg_left hE2bound (by norm_num : (0:Real) ≤ 2)])
        (le_of_lt hy_pos)
    linarith [h2, h3]
  have hr0_2nn : (0:Real) ≤ (int256 (r0Tree x2) : Real) := by
    linarith [hr0_2_big, (by positivity : (0:Real) ≤ (2:Real)^126)]
  have hkey : 2 * ((int256 (r0Tree x2) : Real) + (2993 / 1000 : Real)) * y +
      3814697265625 * 5737291786393199862 / (10000000000000000000 * 2199023255552) + 3 < 2 * (int256 (r0Tree x2) : Real) := by
    -- the seam gap is dominated by `(r0 + U) / RAY`; the quotient exceeds `8.5·10¹⁰` here
    have hyb : 2 * ((int256 (r0Tree x2) : Real) + (2993 / 1000 : Real)) * y ≤
        2 * ((int256 (r0Tree x2) : Real) + (2993 / 1000 : Real)) * (1 - 1 / (2 * (10 ^ 27 : Real))) := by
      apply mul_le_mul_of_nonneg_left hy_bound
      linarith [hr0_2nn]
    have hexpand : 2 * ((int256 (r0Tree x2) : Real) + (2993 / 1000 : Real)) *
          (1 - 1 / (2 * (10 ^ 27 : Real))) =
        2 * (int256 (r0Tree x2) : Real) + 2 * (2993 / 1000 : Real) -
          ((int256 (r0Tree x2) : Real) + (2993 / 1000 : Real)) / (10 ^ 27 : Real) := by
      field_simp
      ring
    have hbig : ((int256 (r0Tree x2) : Real) + (2993 / 1000 : Real)) / (10 ^ 27 : Real) > 30 := by
      rw [gt_iff_lt, lt_div_iff₀ (by positivity)]
      nlinarith [hr0_2_big, (by norm_num : (30:Real) * 10 ^ 27 + 1 < 2 ^ 126)]
    have hUB : 2 * (2993 / 1000 : Real) + 3814697265625 * 5737291786393199862 / (10000000000000000000 * 2199023255552) + 3 < 30 := by norm_num
    linarith [hyb, hexpand ▸ hyb, hbig, hUB]
  have hreal : (int256 (r0Tree x1) : Real) + 3 ≤ 2 * (int256 (r0Tree x2) : Real) := by
    linarith [hr0_1, hkey]
  have hcast : ((int256 (r0Tree x1) + 3 : Int) : Real) ≤ ((2 * int256 (r0Tree x2) : Int) : Real) := by
    push_cast
    linarith [hreal]
  exact_mod_cast hcast

theorem r0_seam_double {x1 x2 : Nat}
    (hx1 : x1 < 2 ^ 256) (hx2 : x2 < 2 ^ 256)
    (hC1 : int256 Cmask < int256 x1) (hC01 : int256 x1 < int256 C0thresh)
    (hC2 : int256 Cmask < int256 x2) (hC02 : int256 x2 < int256 C0thresh)
    (hk : int256 (kTree x2) = int256 (kTree x1) + 1)
    (hadj : int256 x2 = int256 x1 + 1) :
    int256 (r0Tree x1) + 3 ≤ 2 * int256 (r0Tree x2) :=
  r0_seam_double_wide hx1 hx2 (wideRegion_of_wad hC1 hC01) (wideRegion_of_wad hC2 hC02) hk hadj

end

end ExpYul
