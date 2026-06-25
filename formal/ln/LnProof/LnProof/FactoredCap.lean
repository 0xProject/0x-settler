import LnProof.ErrorBoundCore
import LnProof.BiasCapNum

/-!
# Factored-octave cap primitive (checkpoint)

The positive-shift phase-direct route proves `e^(phase) ≥ posTopX` with a
single `sumGE 320` because it keeps the *full* log argument (~110).  This file
factors that exponential into

  octave (`cap2L^(160-c)`) · bias (`capBL`) · x1/H part · first-order extra,

so the only piece that still needs a per-`m` exponential bound is the small
`x1 = H·10^27` residual (argument in `[0, ln2/2]` on the ge branch).  That
residual is captured tightly by a low-degree cap rather than the linear
`x1capGeLoF`, which is what lets the global certificate avoid the intractable
degree-320 Kronecker cells.

`lo_ge_pos_factored` is the soundness bridge: it is exactly the
`lo_ge_pos_budget_exact` assembly with the x1 and bias caps taken as parameters,
so any sharper `capLB` for the x1 part drops straight in.
-/

namespace LnFloorCert

open LnYul LnFloor LnExp LnPoly

set_option maxRecDepth 100000

/-- Sharpened bias cap.  `capBL` keeps only ~31 digits (slop `3404`, i.e.
`3.4e-28` relative), which is too loose for the tight cells the factored route
needs.  Since the bias argument is constant, a `130`-term lower sum pins it to
`~1e-39` relative with a `10^60` denominator. -/
theorem capBLtight :
    capLB (BIASc * 2 ^ 27) QS
      biasCapNum
      (10 ^ 18 * 10 ^ 42) :=
  ⟨130, by decide⟩

/-- Factored ge positive-shift cut.  Given a cap for the x1/H part and the bias
(both over denominator `QS`), and the closing arithmetic inequality, produce the
upper-cut `capLB (lnErrArg r) lnErrQ (wadRayNum x) wadRayStrictDen`. -/
theorem lo_ge_pos_factored {m c x : Nat} {r : Int}
    {x1num x1den biasnum biasden : Nat}
    (hphase : posPhaseNatGe m c ≤ lnErrArg r)
    (hx1den : 0 < x1den) (hbiasden : 0 < biasden)
    (hx1 : capLB ((toInt (x1W (zWord m))).toNat * 1000000000000000000000000000) QS
      x1num x1den)
    (hbias : capLB (BIASc * 2 ^ 27) QS biasnum biasden)
    (hclose :
      wadRayNum x * (((x1den * (10 ^ 40) ^ (160 - c)) * biasden) * lnErrQ) ≤
        (((x1num * (2 * (10 ^ 40 - 1)) ^ (160 - c)) * biasnum) *
          (lnErrQ + posAvailGe m c r)) * wadRayStrictDen) :
    capLB (lnErrArg r) lnErrQ (wadRayNum x) wadRayStrictDen := by
  have cap1 := capLB_lift_right (den := lnErrorBoundDen) QS_pos hx1
  have cap2LQ := capLB_lift_right (den := lnErrorBoundDen) QS_pos cap2L
  have cap2 := capLB_pow cap2LQ (160 - c)
  have capB := capLB_lift_right (den := lnErrorBoundDen) QS_pos hbias
  have cap12 := capLB_mul cap1 cap2
  have cap123 := capLB_mul cap12 capB
  change capLB (posPhaseNatGe m c) lnErrQ
    ((x1num * (2 * (10 ^ 40 - 1)) ^ (160 - c)) * biasnum)
    ((x1den * (10 ^ 40) ^ (160 - c)) * biasden) at cap123
  have capE := capLB_first_order_self (posAvailGe m c r) lnErrQ
  have capR0 := capLB_mul cap123 capE
  have hsum : posPhaseNatGe m c + posAvailGe m c r = lnErrArg r := by
    unfold posAvailGe
    exact Nat.add_sub_of_le hphase
  rw [hsum] at capR0
  refine capLB_weaken ?_ capR0 ?_
  · have hlnErrQ : 0 < lnErrQ := Nat.mul_pos QS_pos (by decide)
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hx1den
      (Nat.pow_pos (by decide : (0 : Nat) < 10 ^ 40))) hbiasden) hlnErrQ
  · exact hclose

/-- The `n`-term lower partial sum is a valid lower cap for its own argument.
Stated abstractly so the kernel never reduces `expNum n`. -/
theorem capLB_expNum_self (n p q : Nat) :
    capLB p q (expNum n p q) (fact n * q ^ n) :=
  ⟨n, Nat.le_refl _⟩

/-- Degree-22 lower cap for the x1/H part of the ge phase, transported along the
floor bracket `geTN2b·2⁹⁹ ≤ H·geTD2b`.  No Kronecker: a trivial degree-22 base
cap at argument `geTN2b/geTD2b` is moved up to the true argument `H·10²⁷/QS` by
`capLB_arg`.  c-independent and bias-independent. -/
theorem ge_x1_cap_d22 {m : Nat} (h1 : Sc + 46 ≤ m) (h2 : m < MHI) :
    capLB ((toInt (x1W (zWord m))).toNat * 1000000000000000000000000000) QS
      (expNum 22 (evalPoly geTN2b (m : Int)).toNat (evalPoly geTD2b (m : Int)).toNat)
      (fact 22 * (evalPoly geTD2b (m : Int)).toNat ^ 22) := by
  have hTD : 0 < evalPoly geTD2b (m : Int) := geTD2b_pos_of_outer h1 h2
  have hTN : 0 ≤ evalPoly geTN2b (m : Int) := geTN2b_nonneg_of_outer h1 h2
  have hH : 0 ≤ toInt (x1W (zWord m)) := x1_nonneg_ge h1 h2
  have hbr := bracket_ge_lo h1 h2
  -- generalize the degree-12 Horner evaluations to opaque integers so no tactic
  -- expands `evalPoly` (which overflows the kernel)
  generalize hTNe : evalPoly geTN2b (m : Int) = TN at hbr hTN ⊢
  generalize hTDe : evalPoly geTD2b (m : Int) = TD at hbr hTD ⊢
  generalize hHe : toInt (x1W (zWord m)) = H at hbr hH ⊢
  have hTDnat : 0 < TD.toNat := by rw [Int.lt_toNat]; simpa using hTD
  refine capLB_arg (q' := TD.toNat) hTDnat ?_ (capLB_expNum_self 22 _ _)
  -- Nat bracket TN.toNat·2⁹⁹ ≤ H.toNat·TD.toNat from the Int bracket hbr
  have hbrN : TN.toNat * 2 ^ 99 ≤ H.toNat * TD.toNat := by
    refine Int.ofNat_le.mp ?_
    simp only [Int.natCast_mul, Int.natCast_pow, Int.toNat_of_nonneg hTN,
      Int.toNat_of_nonneg hH, Int.toNat_of_nonneg (Int.le_of_lt hTD)]
    simpa using hbr
  -- goal (Nat): TN.toNat * QS ≤ (H.toNat * 10²⁷) * TD.toNat, with QS = 10²⁷·2⁹⁹
  have hQSe : QS = 1000000000000000000000000000 * 2 ^ 99 := by decide
  calc TN.toNat * QS
      = TN.toNat * 2 ^ 99 * 1000000000000000000000000000 := by
        rw [hQSe]; simp only [Nat.mul_assoc, Nat.mul_comm]
    _ ≤ H.toNat * TD.toNat * 1000000000000000000000000000 := Nat.mul_le_mul_right _ hbrN
    _ = H.toNat * 1000000000000000000000000000 * TD.toNat := by
        simp only [Nat.mul_assoc, Nat.mul_comm]

/-- Composition: the ge positive-shift upper cut from (i) the smooth-phase floor
bound, and (ii) the closing budget inequality `hclose` with the degree-22 x1 cap
and the sharp bias.  This pins exactly what a c-independent cell cover must
discharge (`hclose`); the octave power on each side cancels, so `hclose` is a
per-`m` obligation up to the per-`k` octave-looseness factor. -/
theorem ge_pos_cut_factored {m c x : Nat} {r : Int}
    (h1 : Sc + 46 ≤ m) (h2 : m < MHI)
    (hphase : posPhaseNatGe m c ≤ lnErrArg r)
    (hclose :
      wadRayNum x *
          ((((fact 22 * (evalPoly geTD2b (m : Int)).toNat ^ 22) *
              (10 ^ 40) ^ (160 - c)) * (10 ^ 18 * 10 ^ 42)) * lnErrQ) ≤
        (((expNum 22 (evalPoly geTN2b (m : Int)).toNat (evalPoly geTD2b (m : Int)).toNat *
            (2 * (10 ^ 40 - 1)) ^ (160 - c)) *
            biasCapNum) *
          (lnErrQ + posAvailGe m c r)) * wadRayStrictDen) :
    capLB (lnErrArg r) lnErrQ (wadRayNum x) wadRayStrictDen := by
  have hTDnat : 0 < (evalPoly geTD2b (m : Int)).toNat := by
    rw [Int.lt_toNat]; simpa using geTD2b_pos_of_outer h1 h2
  exact lo_ge_pos_factored hphase
    (Nat.mul_pos (fact_pos 22) (Nat.pow_pos hTDnat))
    (by decide : 0 < 10 ^ 18 * 10 ^ 42)
    (ge_x1_cap_d22 h1 h2) capBLtight hclose

/-- Octave-collapse bound, batched as one kernel `decide` over `k ∈ [0,159]`.
`(10^40/(10^40-1))^k` peaks at `k=159` below the tight rational `(10^40+160)/10^40`
(looseness `~10^-40`), so the cell polynomial keeps small coefficients instead of
carrying the `~2^21000` octave power. -/
theorem octaveGeBound_all :
    (List.range 160).all
      (fun k => decide (10 ^ 40 * (10 ^ 40) ^ k ≤ (10 ^ 40 + 160) * (10 ^ 40 - 1) ^ k))
      = true := by decide +kernel

theorem octaveGeBound {k : Nat} (hk : k ≤ 159) :
    10 ^ 40 * (10 ^ 40) ^ k ≤ (10 ^ 40 + 160) * (10 ^ 40 - 1) ^ k := by
  have h := List.all_eq_true.mp octaveGeBound_all k (List.mem_range.mpr (by omega))
  simp only [decide_eq_true_eq] at h
  exact h

/-- C-independent reduction of `ge_pos_cut_factored`'s `hclose`.

The closing inequality factors as `octave · (x1/H cell) · bias · first-order`.
Three monotone substitutions collapse all `c`/`r`/`x` dependence into a single
degree-221 polynomial obligation in `m`:

* **min-phase** `minPosAvail ≤ posAvailGe m c r` (from
  `posPhaseNatGe_minAvail_le_lnErrArg`) lets `(lnErrQ + posAvailGe)` be lowered to
  the constant `(lnErrQ + minPosAvail)`;
* **window top** `x ≤ posTopX c m ≤ (m+1)·2^(160-c)` pulls the only `x` factor into
  `(m+1)·2^(160-c)`;
* **octave collapse** `A·(10^40)^k ≤ B·(10^40-1)^k` follows from the small-coefficient
  cell obligation `A·(10^40+160) ≤ B·10^40` via `octaveGeBound` (the tight rational
  octave bound), keeping the cell polynomial at floor-proof coefficient scale.

The surviving hypothesis `hred` is exactly the c-independent inequality a degree-221
Kronecker cell cover discharges. -/
theorem ge_pos_cut_reduced {m c x : Nat} {r : Int}
    (h1 : Sc + 46 ≤ m) (h2 : m < MHI) (hc1 : 1 ≤ c) (hc : c < 160)
    (hmin : posPhaseNatGe m c + minPosAvail ≤ lnErrArg r)
    (hxtop : x ≤ posTopX c m)
    (hred :
      ((m + 1) * 10 ^ 31 * (fact 22 * (evalPoly geTD2b (m : Int)).toNat ^ 22) *
          (10 ^ 18 * 10 ^ 42) * lnErrQ) * (10 ^ 40 + 160) ≤
        (expNum 22 (evalPoly geTN2b (m : Int)).toNat (evalPoly geTD2b (m : Int)).toNat *
            biasCapNum *
            (lnErrQ + minPosAvail) * wadRayStrictDen) * 10 ^ 40) :
    capLB (lnErrArg r) lnErrQ (wadRayNum x) wadRayStrictDen := by
  have hphase : posPhaseNatGe m c ≤ lnErrArg r := Nat.le_trans (Nat.le_add_right _ _) hmin
  have hmineq : minPosAvail ≤ posAvailGe m c r := by
    unfold posAvailGe; omega
  have hoct := octaveGeBound (k := 160 - c) (by omega)
  -- chain the octave bound with `hred`, then cancel the common `10^40`
  have keyineq :
      ((m + 1) * 10 ^ 31 * (fact 22 * (evalPoly geTD2b (m : Int)).toNat ^ 22) *
          (10 ^ 18 * 10 ^ 42) * lnErrQ) * (10 ^ 40) ^ (160 - c) ≤
        (expNum 22 (evalPoly geTN2b (m : Int)).toNat (evalPoly geTD2b (m : Int)).toNat *
            biasCapNum *
            (lnErrQ + minPosAvail) * wadRayStrictDen) * ((10 ^ 40 - 1) ^ (160 - c)) := by
    refine Nat.le_of_mul_le_mul_right ?_ (show 0 < 10 ^ 40 by decide)
    calc ((m + 1) * 10 ^ 31 * (fact 22 * (evalPoly geTD2b (m : Int)).toNat ^ 22) *
            (10 ^ 18 * 10 ^ 42) * lnErrQ) * (10 ^ 40) ^ (160 - c) * 10 ^ 40
        = ((m + 1) * 10 ^ 31 * (fact 22 * (evalPoly geTD2b (m : Int)).toNat ^ 22) *
            (10 ^ 18 * 10 ^ 42) * lnErrQ) * (10 ^ 40 * (10 ^ 40) ^ (160 - c)) := by
          simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ ((m + 1) * 10 ^ 31 * (fact 22 * (evalPoly geTD2b (m : Int)).toNat ^ 22) *
            (10 ^ 18 * 10 ^ 42) * lnErrQ) *
              ((10 ^ 40 + 160) * (10 ^ 40 - 1) ^ (160 - c)) := Nat.mul_le_mul_left _ hoct
      _ = ((m + 1) * 10 ^ 31 * (fact 22 * (evalPoly geTD2b (m : Int)).toNat ^ 22) *
            (10 ^ 18 * 10 ^ 42) * lnErrQ) * (10 ^ 40 + 160) * (10 ^ 40 - 1) ^ (160 - c) := by
          simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ (expNum 22 (evalPoly geTN2b (m : Int)).toNat (evalPoly geTD2b (m : Int)).toNat *
            biasCapNum *
            (lnErrQ + minPosAvail) * wadRayStrictDen) * 10 ^ 40 *
              (10 ^ 40 - 1) ^ (160 - c) := Nat.mul_le_mul_right _ hred
      _ = (expNum 22 (evalPoly geTN2b (m : Int)).toNat (evalPoly geTD2b (m : Int)).toNat *
            biasCapNum *
            (lnErrQ + minPosAvail) * wadRayStrictDen) * ((10 ^ 40 - 1) ^ (160 - c)) *
              10 ^ 40 := by simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  -- now assemble `hclose`
  refine ge_pos_cut_factored h1 h2 hphase ?_
  -- lower the RHS phase-availability to the constant `minPosAvail`
  refine Nat.le_trans ?_
    (Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_refl _) (Nat.add_le_add_left hmineq lnErrQ))
      (Nat.le_refl wadRayStrictDen))
  -- bound `wadRayNum x` by the window top
  have hxw : wadRayNum x ≤ (m + 1) * 2 ^ (160 - c) * 10 ^ 31 := by
    unfold wadRayNum
    exact Nat.mul_le_mul_right _
      (Nat.le_trans (by unfold posTopX at hxtop; exact hxtop) (Nat.sub_le _ _))
  refine Nat.le_trans (Nat.mul_le_mul hxw (Nat.le_refl _)) ?_
  -- pure AC + `(2·y)^k = 2^k·y^k`, closed by `keyineq` scaled by `2^(160-c)`
  calc (m + 1) * 2 ^ (160 - c) * 10 ^ 31 *
          ((((fact 22 * (evalPoly geTD2b (m : Int)).toNat ^ 22) * (10 ^ 40) ^ (160 - c)) *
            (10 ^ 18 * 10 ^ 42)) * lnErrQ)
      = (((m + 1) * 10 ^ 31 * (fact 22 * (evalPoly geTD2b (m : Int)).toNat ^ 22) *
            (10 ^ 18 * 10 ^ 42) * lnErrQ) * (10 ^ 40) ^ (160 - c)) * 2 ^ (160 - c) := by
          simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ ((expNum 22 (evalPoly geTN2b (m : Int)).toNat (evalPoly geTD2b (m : Int)).toNat *
            biasCapNum *
            (lnErrQ + minPosAvail) * wadRayStrictDen) * ((10 ^ 40 - 1) ^ (160 - c))) *
              2 ^ (160 - c) := Nat.mul_le_mul_right _ keyineq
    _ = (((expNum 22 (evalPoly geTN2b (m : Int)).toNat (evalPoly geTD2b (m : Int)).toNat *
            (2 * (10 ^ 40 - 1)) ^ (160 - c)) *
            biasCapNum) *
            (lnErrQ + minPosAvail)) * wadRayStrictDen := by
          simp only [Nat.mul_pow, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

end LnFloorCert
