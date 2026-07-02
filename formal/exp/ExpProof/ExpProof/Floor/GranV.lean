import ExpProof.Floor.R0Bound
import ExpProof.Floor.CapsV
import ExpProof.Cert.ExpVDOver
import ExpProof.Cert.ExpVDOvP00
import ExpProof.Cert.ExpVDUnP00
import ExpProof.Cert.ExpVDOvP01
import ExpProof.Cert.ExpVDUnP01
import ExpProof.Cert.ExpVDOvP02
import ExpProof.Cert.ExpVDUnP02
import ExpProof.Cert.ExpVDOvP03
import ExpProof.Cert.ExpVDUnP03
import ExpProof.Cert.ExpVDOvP04
import ExpProof.Cert.ExpVDUnP04
import ExpProof.Cert.ExpVDOvP05
import ExpProof.Cert.ExpVDUnP05
import ExpProof.Cert.ExpVDOvP06
import ExpProof.Cert.ExpVDUnP06
import ExpProof.Cert.ExpVDOvP07
import ExpProof.Cert.ExpVDUnP07
import ExpProof.Cert.ExpVDOvP08
import ExpProof.Cert.ExpVDUnP08
import ExpProof.Cert.ExpVDOvP09
import ExpProof.Cert.ExpVDUnP09
import ExpProof.Cert.ExpVDOvP10
import ExpProof.Cert.ExpVDUnP10
import ExpProof.Cert.ExpVDOvP11
import ExpProof.Cert.ExpVDUnP11
import ExpProof.Cert.ExpVDOvP12
import ExpProof.Cert.ExpVDUnP12
import ExpProof.Cert.ExpVDOvP13
import ExpProof.Cert.ExpVDUnP13
import ExpProof.Cert.ExpVDOvP14
import ExpProof.Cert.ExpVDUnP14
import ExpProof.Cert.ExpVDOvP15
import ExpProof.Cert.ExpVDUnP15
import ExpProof.Cert.ExpVDOvP16
import ExpProof.Cert.ExpVDUnP16
import ExpProof.Cert.ExpVDOvP17
import ExpProof.Cert.ExpVDUnP17
import ExpProof.Cert.ExpVDOvP18
import ExpProof.Cert.ExpVDUnP18
import ExpProof.Cert.ExpVDOvP19
import ExpProof.Cert.ExpVDUnP19
import ExpProof.Cert.ExpVDOvP20
import ExpProof.Cert.ExpVDUnP20
import ExpProof.Cert.ExpVDOvP21
import ExpProof.Cert.ExpVDUnP21
import ExpProof.Cert.ExpVDOvP22
import ExpProof.Cert.ExpVDUnP22
import ExpProof.Cert.ExpVDOvP23
import ExpProof.Cert.ExpVDUnP23
import ExpProof.Cert.ExpVDOvP24
import ExpProof.Cert.ExpVDUnP24
import ExpProof.Cert.ExpVDOvP25
import ExpProof.Cert.ExpVDUnP25
import ExpProof.Cert.ExpVDOvP26
import ExpProof.Cert.ExpVDUnP26
import ExpProof.Cert.ExpVDOvP27
import ExpProof.Cert.ExpVDUnP27
import ExpProof.Cert.ExpVDOvP28
import ExpProof.Cert.ExpVDUnP28
import ExpProof.Cert.ExpVDOvP29
import ExpProof.Cert.ExpVDUnP29
import ExpProof.Cert.ExpVDOvP30
import ExpProof.Cert.ExpVDUnP30
import ExpProof.Cert.ExpVDOvP31
import ExpProof.Cert.ExpVDUnP31

/-!
# The argument-granularity link: `ê` at the floored `v` vs `ê` at the exact `t²`

The runtime evaluates the even/odd polynomials at `v = ⌊t²/2^133⌋`, while the Taylor cut
(`Floor/CapsV`) certifies the rational at the exact square `t²`. This module bounds the gap. With
the aligned integer rational on the `v`-grid

```
ê(v, t) = NUMv(v, t) / DENv(v, t),   NUMv = Ev(v)·2^110 + t·Od(v),  DENv = Ev(v)·2^110 − t·Od(v)
```

(scale `2^725 = 2^(528+87+110)`; `Ev`/`Od` are `evNumV`/`odNumV` from `Floor/R0Bound`), three facts
combine:

* **the tie** — as a function of the square argument `w`, the rational is monotone (decreasing for
  `t > 0`, increasing for `t < 0`): the cross-product `Pev(b)·Pod(a) − Pev(a)·Pod(b) ≥ 0` for
  `0 ≤ a ≤ b` holds pairwise on the coefficients, so the cert value `ê(t²)` lies between the two
  grid values `ê(v, t)` and `ê(v+1, t)`;
* **the `K` identity** — one grid step is exact algebra:
  `NUMv(v)·DENv(v+1) − NUMv(v+1)·DENv(v) = 2t·2^110·K(v)` with
  `K(v) = Od(v)·Ev(v+1) − Ev(v)·Od(v+1)`, a degree-8 polynomial in `v` with all nine coefficients
  positive, so `K` is nonnegative and nondecreasing on the grid;
* **the piecewise denominator floors** — the grid `[0, vmaxV]` is split into 32 pieces, each with a
  `t`-cap `T` (`v` in the piece forces `|t| ≤ T` through `v = ⌊t²/2^133⌋`) and cover-certified
  floors `Ev(v)·2^110 ∓ T·Od(v) ≥ D·2^725` over the piece (the step looks one cell ahead, so the
  certs run to `vhi + 1`); on the negative half the one-grain lift `2|t|·K/(D·D′)` is additionally
  monotone in `|t|` (the derivative sign reduces to the over-half floor `Ev·2^110 − |t|·Od ≥ 0`),
  so each piece's `t = −T` floor applies. `piece_select` packages the per-piece constants — floors,
  `K`-cap, and the certified budget inequalities — for the runtime point.

`Floor/GranPair` combines these into the two per-side real-level budget bounds the `r0`-vs-`exp`
chains consume, taking the piecewise maximum over the 32 certified per-piece envelopes.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation
open Common.Poly

set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
set_option exponentiation.threshold 2000

/-! ## Generic polynomial positivity/monotonicity -/

/-- A polynomial with nonnegative coefficients evaluates nonnegatively on the nonnegative domain. -/
theorem evalPoly_nonneg_of_nonneg {p : List Int} (hp : ∀ c ∈ p, 0 ≤ c) {a : Int} (ha : 0 ≤ a) :
    0 ≤ evalPoly p a := by
  induction p with
  | nil => simp [evalPoly]
  | cons c cs ih =>
    have hc : 0 ≤ c := hp c List.mem_cons_self
    have hcs : ∀ d ∈ cs, 0 ≤ d := fun d hd => hp d (List.mem_cons_of_mem c hd)
    simp only [evalPoly]
    exact Int.add_nonneg hc (Int.mul_nonneg ha (ih hcs))

/-- A polynomial with nonnegative coefficients is monotone on the nonnegative domain. -/
theorem evalPoly_mono_of_nonneg {p : List Int} (hp : ∀ c ∈ p, 0 ≤ c) {a b : Int}
    (ha : 0 ≤ a) (hab : a ≤ b) : evalPoly p a ≤ evalPoly p b := by
  induction p with
  | nil => simp [evalPoly]
  | cons c cs ih =>
    have hcs : ∀ d ∈ cs, 0 ≤ d := fun d hd => hp d (List.mem_cons_of_mem c hd)
    have hih := ih hcs
    have hb : 0 ≤ b := le_trans ha hab
    have hcsnn : 0 ≤ evalPoly cs a := evalPoly_nonneg_of_nonneg hcs ha
    simp only [evalPoly]
    have h1 : a * evalPoly cs a ≤ b * evalPoly cs b := by
      calc a * evalPoly cs a ≤ b * evalPoly cs a :=
            mul_le_mul_of_nonneg_right hab hcsnn
        _ ≤ b * evalPoly cs b := mul_le_mul_of_nonneg_left hih hb
    linarith [h1]

/-! ## The even/odd polynomials in the square argument `w = t²` -/

/-- The even Horner polynomial in `w` (degree 5, monic), at the cleared scale `2¹¹⁹³`. -/
def Pev : List Int :=
  [0x4e14a45e5650b506e97f4c5da23861e2 * 2 ^ 1193,
   0x93f11e650dd6c64b96ce79065cdf809e * 2 ^ 933,
   0x9064d9657e9a21fc16bb69331c5c3057 * 2 ^ 671,
   0x9a036222841f47c6ed6fc3f7602053 * 2 ^ 415,
   0xb9aacfacf3c10b378435f8e22adf48500e * 2 ^ 133,
   1]

/-- The odd Horner polynomial in `w` (degree 4), at the cleared scale `2¹⁰⁴²`. -/
def Pod : List Int :=
  [0x270a522f2b285a8374bfa62ed11c30f1 * 2 ^ 1042,
   0xaf566247c05753b42892f77b67a6b7c6 * 2 ^ 779,
   0xad4506af99be27419341e1816ff351 * 2 ^ 524,
   0xc926ddbecdeeb42e68cd16db7da8c1 * 2 ^ 259,
   0xdc07aff8276bde9a361278df6a10]

/-- `evNumVPoly(t) = Pev(t²)`: the cert even polynomial is `Pev` composed with squaring. -/
theorem evNumVPoly_eq_Pev_sq (t : Int) :
    evalPoly ExpCertV.evNumVPoly t = evalPoly Pev (t ^ 2) := by
  unfold ExpCertV.evNumVPoly ExpCertV.mulT2 Pev
  simp only [evalPoly_polyAdd, evalPoly_polyScale, evalPoly]
  ring

/-- `odNumVPoly(t) = Pod(t²)`. -/
theorem odNumVPoly_eq_Pod_sq (t : Int) :
    evalPoly ExpCertV.odNumVPoly t = evalPoly Pod (t ^ 2) := by
  unfold ExpCertV.odNumVPoly ExpCertV.mulT2 Pod
  simp only [evalPoly_polyAdd, evalPoly_polyScale, evalPoly]
  ring

/-- `Pev(2¹³³·v) = evNumV(v)·2⁶⁶⁵` — the `w`-polynomial at the grid point `w = 2¹³³·v` recovers the
integer even-Horner accumulator (scaled). -/
theorem Pev_grid (v : Nat) : evalPoly Pev (2 ^ 133 * (v : Int)) = (evNumV v : Int) * 2 ^ 665 := by
  unfold Pev evNumV
  simp only [evalPoly]
  push_cast
  ring

/-- `Pod(2¹³³·v) = odNumV(v)·2⁵³²`. -/
theorem Pod_grid (v : Nat) : evalPoly Pod (2 ^ 133 * (v : Int)) = (odNumV v : Int) * 2 ^ 532 := by
  unfold Pod odNumV
  simp only [evalPoly]
  push_cast
  ring

theorem Pod_coeffs_nonneg : ∀ c ∈ Pod, (0 : Int) ≤ c := by
  unfold Pod; intro c hc; fin_cases hc <;> positivity

/-- The odd cert polynomial `odNumVPoly` is nonnegative everywhere (`= Pod(t²)`, nonneg coeffs). -/
theorem odNumVPoly_nonneg (t : Int) : 0 ≤ evalPoly ExpCertV.odNumVPoly t := by
  rw [odNumVPoly_eq_Pod_sq]
  exact evalPoly_nonneg_of_nonneg Pod_coeffs_nonneg (by positivity)

/-! ## Evaluation shapes and the reciprocal symmetry of the cert rational -/

/-- `evalPoly todNumV t = 2²³ · t · evalPoly odNumVPoly t`. -/
theorem evalTodNumV (t : Int) :
    evalPoly ExpCertV.todNumV t = 2 ^ 23 * (t * evalPoly ExpCertV.odNumVPoly t) := by
  unfold ExpCertV.todNumV
  rw [evalPoly_polyScale]
  simp only [evalPoly]
  ring

/-- `evalPoly numExpV t = evalPoly evNumVPoly t + evalPoly todNumV t`. -/
theorem evalNumExpV (t : Int) :
    evalPoly ExpCertV.numExpV t = evalPoly ExpCertV.evNumVPoly t + evalPoly ExpCertV.todNumV t := by
  unfold ExpCertV.numExpV; rw [evalPoly_polyAdd]

/-- `evalPoly denExpV t = evalPoly evNumVPoly t − evalPoly todNumV t`. -/
theorem evalDenExpV (t : Int) :
    evalPoly ExpCertV.denExpV t = evalPoly ExpCertV.evNumVPoly t - evalPoly ExpCertV.todNumV t := by
  unfold ExpCertV.denExpV; rw [evalPoly_polySub]

/-- `evNumVPoly` is even (`= Pev(t²)`). -/
theorem evNumVPoly_even (t : Int) :
    evalPoly ExpCertV.evNumVPoly (-t) = evalPoly ExpCertV.evNumVPoly t := by
  rw [evNumVPoly_eq_Pev_sq, evNumVPoly_eq_Pev_sq]
  congr 1; ring

/-- `todNumV` is odd (`= 2²³·t·Pod(t²)`). -/
theorem todNumV_odd (t : Int) :
    evalPoly ExpCertV.todNumV (-t) = -evalPoly ExpCertV.todNumV t := by
  rw [evalTodNumV, evalTodNumV, odNumVPoly_eq_Pod_sq, odNumVPoly_eq_Pod_sq]
  rw [show ((-t)^2 : Int) = t^2 from by ring]
  ring

/-- **Reciprocal symmetry** `numExpV(−t) = denExpV(t)` and `denExpV(−t) = numExpV(t)`. -/
theorem numExpV_neg_eq_denExpV (t : Int) :
    evalPoly ExpCertV.numExpV (-t) = evalPoly ExpCertV.denExpV t := by
  rw [evalNumExpV, evalDenExpV, evNumVPoly_even, todNumV_odd]; ring

theorem denExpV_neg_eq_numExpV (t : Int) :
    evalPoly ExpCertV.denExpV (-t) = evalPoly ExpCertV.numExpV t := by
  rw [evalDenExpV, evalNumExpV, evNumVPoly_even, todNumV_odd]; ring

/-- The numerator/denominator cert-polynomial values are nonnegative / positive on `[0, H128]`. -/
theorem certNE_nonneg {t : Int} (h1 : 0 ≤ t) (h2 : t ≤ (ExpCertV.H128 : Int)) :
    0 ≤ evalPoly ExpCertV.numExpV t := ExpCertV.numExpV_nonneg' h1 h2

theorem certDE_pos {t : Int} (h1 : 0 ≤ t) (h2 : t ≤ (ExpCertV.H128 : Int)) :
    1 ≤ evalPoly ExpCertV.denExpV t := ExpCertV.denExpV_ge_one h1 h2

/-- For `t ≤ 0` with `−t ∈ [0, H128]` the cert numerator/denominator at `t` are positive. -/
theorem certNE_pos_neg_aux {t : Int} (h1 : t ≤ 0) (h2 : (-t) ≤ (ExpCertV.H128 : Int)) :
    0 < evalPoly ExpCertV.numExpV t ∧ 0 < evalPoly ExpCertV.denExpV t := by
  have hnt : 0 ≤ -t := by omega
  -- numExpV(t) = denExpV(-t) ≥ 1 > 0
  have h1' : evalPoly ExpCertV.numExpV t = evalPoly ExpCertV.denExpV (-t) := by
    have := numExpV_neg_eq_denExpV (-t); rwa [neg_neg] at this
  have hde : 1 ≤ evalPoly ExpCertV.denExpV (-t) := ExpCertV.denExpV_ge_one hnt h2
  -- denExpV(t) = evNumVPoly(t) − todNumV(t); for t ≤ 0, todNumV(t) ≤ 0, and evNumVPoly(t) ≥ 1
  have htod_np : evalPoly ExpCertV.todNumV t ≤ 0 := by
    rw [evalTodNumV]
    have hodnn := odNumVPoly_nonneg t
    have : t * evalPoly ExpCertV.odNumVPoly t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h1 hodnn
    nlinarith [this]
  have hev1 : 1 ≤ evalPoly ExpCertV.evNumVPoly t := by
    have heven : evalPoly ExpCertV.evNumVPoly t = evalPoly ExpCertV.evNumVPoly (-t) := by
      rw [← evNumVPoly_even (-t), neg_neg]
    have htodnt : 0 ≤ evalPoly ExpCertV.todNumV (-t) := by
      rw [evalTodNumV]
      exact Int.mul_nonneg (by positivity) (Int.mul_nonneg hnt (odNumVPoly_nonneg (-t)))
    have hde' := hde
    rw [evalDenExpV] at hde'
    rw [heven]; linarith [hde', htodnt]
  refine ⟨by rw [h1']; omega, ?_⟩
  rw [evalDenExpV]; linarith [hev1, htod_np]

/-! ## The aligned integer rational on the `v`-grid -/

/-- `NUMv(v, t) = Ev(v)·2^110 + t·Od(v)` at the common scale `2^725`. -/
def NUMv (v : Nat) (t : Int) : Int := (evNumV v : Int) * 2 ^ 110 + t * (odNumV v : Int)

/-- `DENv(v, t) = Ev(v)·2^110 − t·Od(v)` at the common scale `2^725`. -/
def DENv (v : Nat) (t : Int) : Int := (evNumV v : Int) * 2 ^ 110 - t * (odNumV v : Int)

/-- `evNumV` as an `evalPoly` over the cert coefficient list. -/
theorem evNumV_eq_poly (v : Nat) : (evNumV v : Int) = evalPoly ExpCertV.evVPoly (v : Int) := by
  unfold evNumV ExpCertV.evVPoly
  simp only [evalPoly]
  push_cast
  ring

theorem odNumV_eq_poly (v : Nat) : (odNumV v : Int) = evalPoly ExpCertV.odVPoly (v : Int) := by
  unfold odNumV ExpCertV.odVPoly
  simp only [evalPoly]
  push_cast
  ring

/-- The over-half floor shape evaluated at a grid point:
`certDOverP T D (v) = Ev(v)·2^110 − T·Od(v) − D·2^725`. -/
theorem evalDOverP (T D : Int) (v : Nat) :
    evalPoly (ExpCertV.certDOverP T D) (v : Int) =
      (evNumV v : Int) * 2 ^ 110 - T * (odNumV v : Int) - D * 2 ^ 725 := by
  unfold ExpCertV.certDOverP
  rw [evalPoly_polyAdd, evalPoly_polySub, evalPoly_polyScale, evalPoly_polyScale,
    ← evNumV_eq_poly, ← odNumV_eq_poly]
  simp only [evalPoly]
  ring

/-- The under-half floor shape evaluated at a grid point:
`certDUnderP T D (v) = Ev(v)·2^110 + T·Od(v) − D·2^725`. -/
theorem evalDUnderP (T D : Int) (v : Nat) :
    evalPoly (ExpCertV.certDUnderP T D) (v : Int) =
      (evNumV v : Int) * 2 ^ 110 + T * (odNumV v : Int) - D * 2 ^ 725 := by
  unfold ExpCertV.certDUnderP
  rw [evalPoly_polyAdd, evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyScale,
    ← evNumV_eq_poly, ← odNumV_eq_poly]
  simp only [evalPoly]
  ring

/-! ## The certified global denominator floor over the grid -/

/-- The over-half denominator floor: `DENv(v, t) ≥ 554482771859·2^725` for `0 ≤ t ≤ H128` on the
grid `[0, vmaxV + 1]`, from the cover certificate `certDOver`. -/
theorem DENv_ge_over {v : Nat} {t : Int} (hv : v ≤ ExpCertV.vmaxV + 1)
    (ht0 : 0 ≤ t) (htH : t ≤ 117932881612756647068972071382077242199) :
    554482771859 * 2 ^ 725 ≤ DENv v t := by
  have hvI : (0 : Int) ≤ (v : Int) := Int.natCast_nonneg _
  have hvI2 : (v : Int) ≤ 1277263193518626341050532535110179583 := by
    have h : v ≤ 1277263193518626341050532535110179583 := by
      unfold ExpCertV.vmaxV at hv; omega
    exact_mod_cast h
  have hcert := ExpCertV.dOverV_nonneg hvI hvI2
  have hH : ((ExpCertV.H128 : Nat) : Int) = 117932881612756647068972071382077242199 := by
    unfold ExpCertV.H128; norm_num
  have hexp : evalPoly ExpCertV.certDOver (v : Int) =
      (evNumV v : Int) * 2 ^ 110 - 117932881612756647068972071382077242199 * (odNumV v : Int)
        - 554482771859 * 2 ^ 725 := by
    unfold ExpCertV.certDOver
    rw [evalDOverP, hH]
  rw [hexp] at hcert
  have hOd_nn : (0 : Int) ≤ (odNumV v : Int) := Int.natCast_nonneg _
  have htOd : t * (odNumV v : Int) ≤ 117932881612756647068972071382077242199 * (odNumV v : Int) :=
    mul_le_mul_of_nonneg_right htH hOd_nn
  unfold DENv
  linarith [hcert, htOd]

/-- The scaled even value alone clears the over floor. -/
theorem Ev_scaled_ge {v : Nat} (hv : v ≤ ExpCertV.vmaxV + 1) :
    554482771859 * 2 ^ 725 ≤ (evNumV v : Int) * 2 ^ 110 := by
  have h := DENv_ge_over hv (t := 0) le_rfl (by norm_num)
  unfold DENv at h
  linarith [h]

/-- On the nonpositive half the denominator is bounded below by the scaled even value. -/
theorem DENv_ge_neg {v : Nat} {t : Int} (hv : v ≤ ExpCertV.vmaxV + 1) (htnp : t ≤ 0) :
    554482771859 * 2 ^ 725 ≤ DENv v t := by
  have hOd_nn : (0 : Int) ≤ (odNumV v : Int) := Int.natCast_nonneg _
  have h := Ev_scaled_ge hv
  have htOd : t * (odNumV v : Int) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg htnp hOd_nn
  unfold DENv
  linarith [h, htOd]

/-! ## The `K` step polynomial -/

/-- One-grid-step cross product `K(v) = Od(v)·Ev(v+1) − Ev(v)·Od(v+1)`. -/
def KpM (v : Nat) : Int :=
  (odNumV v : Int) * (evNumV (v + 1) : Int) - (evNumV v : Int) * (odNumV (v + 1) : Int)

/-- `K` expanded: degree 8 in `v`, all nine coefficients positive. -/
def Kpoly : List Int := [
  124314103365382948540818484389625511162300300154596353471434559263576710760858295817293092085008263137731720671247221648067596832296011712645000813284745609572799860614715339074429845004953604219102947508964005670501289338774093304568104691068782792841751722685380505527135804513603544359590666402647994177984765095548996198922954351638285344422494208,
  430693347524554794343417296651509686134557738098954307704214627733020390530278276854672725773269273195478624746887483823521915971792313550530664645765146330112240663991043334744169297019302744406385806086948888789809498977224640089404613426031164334553095878029211115721153838092053743221232923214856740321361920,
  686241798384522667273603851832009005832991722966895305486733489217475120780434741578221376750207665260280559483314421737861160359613911796076366378147384024630930905683143857451910151039919766317250012570559885388869355828462187828089296162106016837843019513341114421608448,
  516930441971039446793370708723350125364637202395800871195912177274842681404775759909985132791355705126258878499764647160096038572134699599657143783480012402118176141075234265877953175422112442922930396729118643533020785802714646839296,
  204444652500469654421705147174126797534284466591134372022748954577461360623715926111412069421315335549677153452480685493529231437120364790325762132070320513045724004787419978918913755181249161744,
  41949223685511975480580776931828146057677792415359815945353299890032432268755601779612364142307888289245407764490095148612742616445009325314635169114466368,
  4316880982720124500406644109788966154643851890842252965238156761257284790660493659638039728545632279862302184602720,
  177702252311948919910468951720184092402653220933754361350350337206870976576,
  4462739169817451478086891138411024]

theorem Kpoly_coeffs_nonneg : ∀ c ∈ Kpoly, (0 : Int) ≤ c := by
  unfold Kpoly; intro c hc; fin_cases hc <;> norm_num

theorem KpM_eq_poly (v : Nat) : KpM v = evalPoly Kpoly (v : Int) := by
  unfold KpM evNumV odNumV Kpoly
  simp only [evalPoly]
  push_cast
  ring

theorem KpM_nonneg (v : Nat) : 0 ≤ KpM v := by
  rw [KpM_eq_poly]
  exact evalPoly_nonneg_of_nonneg Kpoly_coeffs_nonneg (Int.natCast_nonneg _)

/-- `K` is nondecreasing on the grid (positive coefficients), so a piece's upper edge caps it. -/
theorem KpM_le_at {v vhi : Nat} (hv : v ≤ vhi) {Khi : Int}
    (heval : evalPoly Kpoly (vhi : Int) = Khi) : KpM v ≤ Khi := by
  rw [KpM_eq_poly, ← heval]
  exact evalPoly_mono_of_nonneg Kpoly_coeffs_nonneg (Int.natCast_nonneg _) (by exact_mod_cast hv)

/-- **The discrete quotient identity**: one grid step of the aligned rational is exact algebra. -/
theorem step_identity (v : Nat) (t : Int) :
    NUMv v t * DENv (v + 1) t - NUMv (v + 1) t * DENv v t = 2 * t * 2 ^ 110 * KpM v := by
  unfold NUMv DENv KpM
  ring

/-! ## Grid placement of the exact square -/

/-- The squared reduced argument splits as `t² = 2¹³³·vTree x + r` with `0 ≤ r < 2¹³³`. -/
theorem tsq_split {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    2 ^ 133 * (vTree x : Int) ≤ (int256 (tTree x)) ^ 2 ∧
      (int256 (tTree x)) ^ 2 < 2 ^ 133 * (vTree x : Int) + 2 ^ 133 := by
  obtain ⟨hveq, _⟩ := vTree_eq hx hC hC0
  have hsqnn : (0 : Int) ≤ (int256 (tTree x)) ^ 2 := sq_nonneg _
  have hdm := Int.ediv_add_emod ((int256 (tTree x)) ^ 2) (2 ^ 133)
  have hmod_lt := Int.emod_lt_of_pos ((int256 (tTree x)) ^ 2) (by norm_num : (0:Int) < 2 ^ 133)
  have hmod_nn := Int.emod_nonneg ((int256 (tTree x)) ^ 2) (by norm_num : (2:Int) ^ 133 ≠ 0)
  rw [hveq]
  constructor
  · nlinarith [hdm, hmod_nn]
  · nlinarith [hdm, hmod_lt]

/-- The grid index never leaves the certified domain: `vTree x ≤ vmaxV`. -/
theorem vTree_le_vmax {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    vTree x ≤ ExpCertV.vmaxV := by
  obtain ⟨hlo, _⟩ := tsq_split hx hC hC0
  obtain ⟨htlo, hthi⟩ := tTree_in_cert_domain hx hC hC0
  have ht2 : (int256 (tTree x)) ^ 2 ≤ 117932881612756647068972071382077242199 ^ 2 := by
    nlinarith [htlo, hthi]
  have hlt : 2 ^ 133 * (vTree x : Int) <
      2 ^ 133 * (1277263193518626341050532535110179583 : Int) := by
    calc 2 ^ 133 * (vTree x : Int) ≤ (int256 (tTree x)) ^ 2 := hlo
      _ ≤ 117932881612756647068972071382077242199 ^ 2 := ht2
      _ < 2 ^ 133 * 1277263193518626341050532535110179583 := by norm_num
  have hvI : (vTree x : Int) < 1277263193518626341050532535110179583 :=
    lt_of_mul_lt_mul_left hlt (by positivity)
  have hvN : vTree x < 1277263193518626341050532535110179583 := by exact_mod_cast hvI
  unfold ExpCertV.vmaxV
  omega

/-! ## Cross-monotonicity of the rational in the square argument -/

/-- Power cross-product monotonicity: `a^(j+d)·b^j ≤ a^j·b^(j+d)` for `0 ≤ a ≤ b`. -/
theorem pow_pair_mono {a b : Int} (ha : 0 ≤ a) (hab : a ≤ b) (j d : Nat) :
    a ^ (j + d) * b ^ j ≤ a ^ j * b ^ (j + d) := by
  have hb : 0 ≤ b := le_trans ha hab
  have h := pow_le_pow_left₀ ha hab d
  calc a ^ (j + d) * b ^ j = (a ^ j * b ^ j) * a ^ d := by rw [pow_add]; ring
    _ ≤ (a ^ j * b ^ j) * b ^ d := by
        exact mul_le_mul_of_nonneg_left h (mul_nonneg (pow_nonneg ha _) (pow_nonneg hb _))
    _ = a ^ j * b ^ (j + d) := by rw [pow_add]; ring

/-- **The cross product is one-signed**: `Pev(b)·Pod(a) − Pev(a)·Pod(b) ≥ 0` for `0 ≤ a ≤ b`. Every
pairwise coefficient cross `e_i·o_j − e_j·o_i` (`i > j`) is nonnegative, and each pair's power
cross `a^j·b^i − a^i·b^j` is nonnegative on `0 ≤ a ≤ b`. -/
theorem pev_pod_cross {a b : Int} (ha : 0 ≤ a) (hab : a ≤ b) :
    0 ≤ evalPoly Pev b * evalPoly Pod a - evalPoly Pev a * evalPoly Pod b := by
  have hexpand : evalPoly Pev b * evalPoly Pod a - evalPoly Pev a * evalPoly Pod b =
      (((0x93f11e650dd6c64b96ce79065cdf809e * 2 ^ 933) * (0x270a522f2b285a8374bfa62ed11c30f1 * 2 ^ 1042) - (0x4e14a45e5650b506e97f4c5da23861e2 * 2 ^ 1193) * (0xaf566247c05753b42892f77b67a6b7c6 * 2 ^ 779) : Int)) * (a ^ 0 * b ^ 1 - a ^ 1 * b ^ 0) +
      (((0x9064d9657e9a21fc16bb69331c5c3057 * 2 ^ 671) * (0x270a522f2b285a8374bfa62ed11c30f1 * 2 ^ 1042) - (0x4e14a45e5650b506e97f4c5da23861e2 * 2 ^ 1193) * (0xad4506af99be27419341e1816ff351 * 2 ^ 524) : Int)) * (a ^ 0 * b ^ 2 - a ^ 2 * b ^ 0) +
      (((0x9064d9657e9a21fc16bb69331c5c3057 * 2 ^ 671) * (0xaf566247c05753b42892f77b67a6b7c6 * 2 ^ 779) - (0x93f11e650dd6c64b96ce79065cdf809e * 2 ^ 933) * (0xad4506af99be27419341e1816ff351 * 2 ^ 524) : Int)) * (a ^ 1 * b ^ 2 - a ^ 2 * b ^ 1) +
      (((0x9a036222841f47c6ed6fc3f7602053 * 2 ^ 415) * (0x270a522f2b285a8374bfa62ed11c30f1 * 2 ^ 1042) - (0x4e14a45e5650b506e97f4c5da23861e2 * 2 ^ 1193) * (0xc926ddbecdeeb42e68cd16db7da8c1 * 2 ^ 259) : Int)) * (a ^ 0 * b ^ 3 - a ^ 3 * b ^ 0) +
      (((0x9a036222841f47c6ed6fc3f7602053 * 2 ^ 415) * (0xaf566247c05753b42892f77b67a6b7c6 * 2 ^ 779) - (0x93f11e650dd6c64b96ce79065cdf809e * 2 ^ 933) * (0xc926ddbecdeeb42e68cd16db7da8c1 * 2 ^ 259) : Int)) * (a ^ 1 * b ^ 3 - a ^ 3 * b ^ 1) +
      (((0x9a036222841f47c6ed6fc3f7602053 * 2 ^ 415) * (0xad4506af99be27419341e1816ff351 * 2 ^ 524) - (0x9064d9657e9a21fc16bb69331c5c3057 * 2 ^ 671) * (0xc926ddbecdeeb42e68cd16db7da8c1 * 2 ^ 259) : Int)) * (a ^ 2 * b ^ 3 - a ^ 3 * b ^ 2) +
      (((0xb9aacfacf3c10b378435f8e22adf48500e * 2 ^ 133) * (0x270a522f2b285a8374bfa62ed11c30f1 * 2 ^ 1042) - (0x4e14a45e5650b506e97f4c5da23861e2 * 2 ^ 1193) * (0xdc07aff8276bde9a361278df6a10) : Int)) * (a ^ 0 * b ^ 4 - a ^ 4 * b ^ 0) +
      (((0xb9aacfacf3c10b378435f8e22adf48500e * 2 ^ 133) * (0xaf566247c05753b42892f77b67a6b7c6 * 2 ^ 779) - (0x93f11e650dd6c64b96ce79065cdf809e * 2 ^ 933) * (0xdc07aff8276bde9a361278df6a10) : Int)) * (a ^ 1 * b ^ 4 - a ^ 4 * b ^ 1) +
      (((0xb9aacfacf3c10b378435f8e22adf48500e * 2 ^ 133) * (0xad4506af99be27419341e1816ff351 * 2 ^ 524) - (0x9064d9657e9a21fc16bb69331c5c3057 * 2 ^ 671) * (0xdc07aff8276bde9a361278df6a10) : Int)) * (a ^ 2 * b ^ 4 - a ^ 4 * b ^ 2) +
      (((0xb9aacfacf3c10b378435f8e22adf48500e * 2 ^ 133) * (0xc926ddbecdeeb42e68cd16db7da8c1 * 2 ^ 259) - (0x9a036222841f47c6ed6fc3f7602053 * 2 ^ 415) * (0xdc07aff8276bde9a361278df6a10) : Int)) * (a ^ 3 * b ^ 4 - a ^ 4 * b ^ 3) +
      (((1) * (0x270a522f2b285a8374bfa62ed11c30f1 * 2 ^ 1042) - (0x4e14a45e5650b506e97f4c5da23861e2 * 2 ^ 1193) * (0) : Int)) * (a ^ 0 * b ^ 5 - a ^ 5 * b ^ 0) +
      (((1) * (0xaf566247c05753b42892f77b67a6b7c6 * 2 ^ 779) - (0x93f11e650dd6c64b96ce79065cdf809e * 2 ^ 933) * (0) : Int)) * (a ^ 1 * b ^ 5 - a ^ 5 * b ^ 1) +
      (((1) * (0xad4506af99be27419341e1816ff351 * 2 ^ 524) - (0x9064d9657e9a21fc16bb69331c5c3057 * 2 ^ 671) * (0) : Int)) * (a ^ 2 * b ^ 5 - a ^ 5 * b ^ 2) +
      (((1) * (0xc926ddbecdeeb42e68cd16db7da8c1 * 2 ^ 259) - (0x9a036222841f47c6ed6fc3f7602053 * 2 ^ 415) * (0) : Int)) * (a ^ 3 * b ^ 5 - a ^ 5 * b ^ 3) +
      (((1) * (0xdc07aff8276bde9a361278df6a10) - (0xb9aacfacf3c10b378435f8e22adf48500e * 2 ^ 133) * (0) : Int)) * (a ^ 4 * b ^ 5 - a ^ 5 * b ^ 4) := by
    simp only [Pev, Pod, evalPoly]
    ring
  have h10 : (0:Int) ≤ (((0x93f11e650dd6c64b96ce79065cdf809e * 2 ^ 933) * (0x270a522f2b285a8374bfa62ed11c30f1 * 2 ^ 1042) - (0x4e14a45e5650b506e97f4c5da23861e2 * 2 ^ 1193) * (0xaf566247c05753b42892f77b67a6b7c6 * 2 ^ 779) : Int)) * (a ^ 0 * b ^ 1 - a ^ 1 * b ^ 0) :=
    mul_nonneg (by norm_num) (by have := pow_pair_mono ha hab 0 1; simpa using this)
  have h20 : (0:Int) ≤ (((0x9064d9657e9a21fc16bb69331c5c3057 * 2 ^ 671) * (0x270a522f2b285a8374bfa62ed11c30f1 * 2 ^ 1042) - (0x4e14a45e5650b506e97f4c5da23861e2 * 2 ^ 1193) * (0xad4506af99be27419341e1816ff351 * 2 ^ 524) : Int)) * (a ^ 0 * b ^ 2 - a ^ 2 * b ^ 0) :=
    mul_nonneg (by norm_num) (by have := pow_pair_mono ha hab 0 2; simpa using this)
  have h21 : (0:Int) ≤ (((0x9064d9657e9a21fc16bb69331c5c3057 * 2 ^ 671) * (0xaf566247c05753b42892f77b67a6b7c6 * 2 ^ 779) - (0x93f11e650dd6c64b96ce79065cdf809e * 2 ^ 933) * (0xad4506af99be27419341e1816ff351 * 2 ^ 524) : Int)) * (a ^ 1 * b ^ 2 - a ^ 2 * b ^ 1) :=
    mul_nonneg (by norm_num) (by have := pow_pair_mono ha hab 1 1; simpa using this)
  have h30 : (0:Int) ≤ (((0x9a036222841f47c6ed6fc3f7602053 * 2 ^ 415) * (0x270a522f2b285a8374bfa62ed11c30f1 * 2 ^ 1042) - (0x4e14a45e5650b506e97f4c5da23861e2 * 2 ^ 1193) * (0xc926ddbecdeeb42e68cd16db7da8c1 * 2 ^ 259) : Int)) * (a ^ 0 * b ^ 3 - a ^ 3 * b ^ 0) :=
    mul_nonneg (by norm_num) (by have := pow_pair_mono ha hab 0 3; simpa using this)
  have h31 : (0:Int) ≤ (((0x9a036222841f47c6ed6fc3f7602053 * 2 ^ 415) * (0xaf566247c05753b42892f77b67a6b7c6 * 2 ^ 779) - (0x93f11e650dd6c64b96ce79065cdf809e * 2 ^ 933) * (0xc926ddbecdeeb42e68cd16db7da8c1 * 2 ^ 259) : Int)) * (a ^ 1 * b ^ 3 - a ^ 3 * b ^ 1) :=
    mul_nonneg (by norm_num) (by have := pow_pair_mono ha hab 1 2; simpa using this)
  have h32 : (0:Int) ≤ (((0x9a036222841f47c6ed6fc3f7602053 * 2 ^ 415) * (0xad4506af99be27419341e1816ff351 * 2 ^ 524) - (0x9064d9657e9a21fc16bb69331c5c3057 * 2 ^ 671) * (0xc926ddbecdeeb42e68cd16db7da8c1 * 2 ^ 259) : Int)) * (a ^ 2 * b ^ 3 - a ^ 3 * b ^ 2) :=
    mul_nonneg (by norm_num) (by have := pow_pair_mono ha hab 2 1; simpa using this)
  have h40 : (0:Int) ≤ (((0xb9aacfacf3c10b378435f8e22adf48500e * 2 ^ 133) * (0x270a522f2b285a8374bfa62ed11c30f1 * 2 ^ 1042) - (0x4e14a45e5650b506e97f4c5da23861e2 * 2 ^ 1193) * (0xdc07aff8276bde9a361278df6a10) : Int)) * (a ^ 0 * b ^ 4 - a ^ 4 * b ^ 0) :=
    mul_nonneg (by norm_num) (by have := pow_pair_mono ha hab 0 4; simpa using this)
  have h41 : (0:Int) ≤ (((0xb9aacfacf3c10b378435f8e22adf48500e * 2 ^ 133) * (0xaf566247c05753b42892f77b67a6b7c6 * 2 ^ 779) - (0x93f11e650dd6c64b96ce79065cdf809e * 2 ^ 933) * (0xdc07aff8276bde9a361278df6a10) : Int)) * (a ^ 1 * b ^ 4 - a ^ 4 * b ^ 1) :=
    mul_nonneg (by norm_num) (by have := pow_pair_mono ha hab 1 3; simpa using this)
  have h42 : (0:Int) ≤ (((0xb9aacfacf3c10b378435f8e22adf48500e * 2 ^ 133) * (0xad4506af99be27419341e1816ff351 * 2 ^ 524) - (0x9064d9657e9a21fc16bb69331c5c3057 * 2 ^ 671) * (0xdc07aff8276bde9a361278df6a10) : Int)) * (a ^ 2 * b ^ 4 - a ^ 4 * b ^ 2) :=
    mul_nonneg (by norm_num) (by have := pow_pair_mono ha hab 2 2; simpa using this)
  have h43 : (0:Int) ≤ (((0xb9aacfacf3c10b378435f8e22adf48500e * 2 ^ 133) * (0xc926ddbecdeeb42e68cd16db7da8c1 * 2 ^ 259) - (0x9a036222841f47c6ed6fc3f7602053 * 2 ^ 415) * (0xdc07aff8276bde9a361278df6a10) : Int)) * (a ^ 3 * b ^ 4 - a ^ 4 * b ^ 3) :=
    mul_nonneg (by norm_num) (by have := pow_pair_mono ha hab 3 1; simpa using this)
  have h50 : (0:Int) ≤ (((1) * (0x270a522f2b285a8374bfa62ed11c30f1 * 2 ^ 1042) - (0x4e14a45e5650b506e97f4c5da23861e2 * 2 ^ 1193) * (0) : Int)) * (a ^ 0 * b ^ 5 - a ^ 5 * b ^ 0) :=
    mul_nonneg (by norm_num) (by have := pow_pair_mono ha hab 0 5; simpa using this)
  have h51 : (0:Int) ≤ (((1) * (0xaf566247c05753b42892f77b67a6b7c6 * 2 ^ 779) - (0x93f11e650dd6c64b96ce79065cdf809e * 2 ^ 933) * (0) : Int)) * (a ^ 1 * b ^ 5 - a ^ 5 * b ^ 1) :=
    mul_nonneg (by norm_num) (by have := pow_pair_mono ha hab 1 4; simpa using this)
  have h52 : (0:Int) ≤ (((1) * (0xad4506af99be27419341e1816ff351 * 2 ^ 524) - (0x9064d9657e9a21fc16bb69331c5c3057 * 2 ^ 671) * (0) : Int)) * (a ^ 2 * b ^ 5 - a ^ 5 * b ^ 2) :=
    mul_nonneg (by norm_num) (by have := pow_pair_mono ha hab 2 3; simpa using this)
  have h53 : (0:Int) ≤ (((1) * (0xc926ddbecdeeb42e68cd16db7da8c1 * 2 ^ 259) - (0x9a036222841f47c6ed6fc3f7602053 * 2 ^ 415) * (0) : Int)) * (a ^ 3 * b ^ 5 - a ^ 5 * b ^ 3) :=
    mul_nonneg (by norm_num) (by have := pow_pair_mono ha hab 3 2; simpa using this)
  have h54 : (0:Int) ≤ (((1) * (0xdc07aff8276bde9a361278df6a10) - (0xb9aacfacf3c10b378435f8e22adf48500e * 2 ^ 133) * (0) : Int)) * (a ^ 4 * b ^ 5 - a ^ 5 * b ^ 4) :=
    mul_nonneg (by norm_num) (by have := pow_pair_mono ha hab 4 1; simpa using this)
  rw [hexpand]
  linarith [h10, h20, h21, h30, h31, h32, h40, h41, h42, h43, h50, h51, h52, h53, h54]

/-- **The tie**: with `s ≥ 0` and `0 ≤ a ≤ b`, the `w`-argument rational is nonincreasing:
`(Pev(b) + s·Pod(b))·(Pev(a) − s·Pod(a)) ≤ (Pev(a) + s·Pod(a))·(Pev(b) − s·Pod(b))`. -/
theorem tie_cross {a b : Int} (s : Int) (ha : 0 ≤ a) (hab : a ≤ b) (hs : 0 ≤ s) :
    (evalPoly Pev b + s * evalPoly Pod b) * (evalPoly Pev a - s * evalPoly Pod a) ≤
      (evalPoly Pev a + s * evalPoly Pod a) * (evalPoly Pev b - s * evalPoly Pod b) := by
  have hG := pev_pod_cross ha hab
  have hid : (evalPoly Pev a + s * evalPoly Pod a) * (evalPoly Pev b - s * evalPoly Pod b) -
      (evalPoly Pev b + s * evalPoly Pod b) * (evalPoly Pev a - s * evalPoly Pod a) =
      2 * (s * (evalPoly Pev b * evalPoly Pod a - evalPoly Pev a * evalPoly Pod b)) := by
    ring
  have := mul_nonneg hs hG
  linarith [hid, this]

/-! ## The grid/cert bridge -/

/-- The `w`-polynomials at a grid point recover the aligned rational's numerator (scale `2^555`). -/
theorem grid_num_eq (v : Nat) (t : Int) :
    evalPoly Pev (2 ^ 133 * (v : Int)) + 2 ^ 23 * t * evalPoly Pod (2 ^ 133 * (v : Int)) =
      2 ^ 555 * NUMv v t := by
  rw [Pev_grid, Pod_grid]
  unfold NUMv
  ring

theorem grid_den_eq (v : Nat) (t : Int) :
    evalPoly Pev (2 ^ 133 * (v : Int)) - 2 ^ 23 * t * evalPoly Pod (2 ^ 133 * (v : Int)) =
      2 ^ 555 * DENv v t := by
  rw [Pev_grid, Pod_grid]
  unfold DENv
  ring

/-- The cert polynomials at `t` are the `w`-polynomials at the exact square. -/
theorem NE_eq_w (t : Int) :
    evalPoly ExpCertV.numExpV t = evalPoly Pev (t ^ 2) + 2 ^ 23 * t * evalPoly Pod (t ^ 2) := by
  rw [evalNumExpV, evalTodNumV, ← evNumVPoly_eq_Pev_sq, ← odNumVPoly_eq_Pod_sq]
  ring

theorem DE_eq_w (t : Int) :
    evalPoly ExpCertV.denExpV t = evalPoly Pev (t ^ 2) - 2 ^ 23 * t * evalPoly Pod (t ^ 2) := by
  rw [evalDenExpV, evalTodNumV, ← evNumVPoly_eq_Pev_sq, ← odNumVPoly_eq_Pod_sq]
  ring

/-- **The tie at the runtime point (nonnegative half)**: the cert rational at `t²` lies between the
two grid values, as cross products. -/
theorem tie_over {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htnn : 0 ≤ int256 (tTree x)) :
    evalPoly ExpCertV.numExpV (int256 (tTree x)) * DENv (vTree x) (int256 (tTree x)) ≤
        NUMv (vTree x) (int256 (tTree x)) * evalPoly ExpCertV.denExpV (int256 (tTree x)) ∧
      NUMv (vTree x + 1) (int256 (tTree x)) * evalPoly ExpCertV.denExpV (int256 (tTree x)) ≤
        evalPoly ExpCertV.numExpV (int256 (tTree x)) * DENv (vTree x + 1) (int256 (tTree x)) := by
  obtain ⟨haw, hwb⟩ := tsq_split hx hC hC0
  set t := int256 (tTree x) with htdef
  set v := vTree x with hvdef
  have hs : (0:Int) ≤ 2 ^ 23 * t := by positivity
  have ha : (0:Int) ≤ 2 ^ 133 * (v : Int) := by positivity
  have hw : (0:Int) ≤ t ^ 2 := sq_nonneg _
  have hb1 : t ^ 2 ≤ 2 ^ 133 * ((v + 1 : Nat) : Int) := by push_cast; linarith [hwb]
  have hp555 : (0:Int) < 2 ^ 555 := by positivity
  constructor
  · -- a := grid v, b := t²: NE·(2^555·DENv v) ≤ (2^555·NUMv v)·DE
    have h1 := tie_cross (a := 2 ^ 133 * (v : Int)) (b := t ^ 2) (2 ^ 23 * t) ha haw hs
    rw [grid_num_eq, grid_den_eq, ← NE_eq_w, ← DE_eq_w] at h1
    -- h1 : NE·(2^555·DENv v t) ≤ (2^555·NUMv v t)·DE
    have h2 : 2 ^ 555 * (evalPoly ExpCertV.numExpV t * DENv v t) ≤
        2 ^ 555 * (NUMv v t * evalPoly ExpCertV.denExpV t) := by
      calc 2 ^ 555 * (evalPoly ExpCertV.numExpV t * DENv v t)
          = evalPoly ExpCertV.numExpV t * (2 ^ 555 * DENv v t) := by ring
        _ ≤ 2 ^ 555 * NUMv v t * evalPoly ExpCertV.denExpV t := h1
        _ = 2 ^ 555 * (NUMv v t * evalPoly ExpCertV.denExpV t) := by ring
    exact le_of_mul_le_mul_left h2 hp555
  · -- a := t², b := grid (v+1): (2^555·NUMv (v+1))·DE ≤ NE·(2^555·DENv (v+1))
    have h1 := tie_cross (a := t ^ 2) (b := 2 ^ 133 * ((v + 1 : Nat) : Int)) (2 ^ 23 * t) hw hb1 hs
    rw [grid_num_eq, grid_den_eq, ← NE_eq_w, ← DE_eq_w] at h1
    -- h1 : (2^555·NUMv (v+1) t)·DE ≤ NE·(2^555·DENv (v+1) t)
    have h2 : 2 ^ 555 * (NUMv (v + 1) t * evalPoly ExpCertV.denExpV t) ≤
        2 ^ 555 * (evalPoly ExpCertV.numExpV t * DENv (v + 1) t) := by
      calc 2 ^ 555 * (NUMv (v + 1) t * evalPoly ExpCertV.denExpV t)
          = 2 ^ 555 * NUMv (v + 1) t * evalPoly ExpCertV.denExpV t := by ring
        _ ≤ evalPoly ExpCertV.numExpV t * (2 ^ 555 * DENv (v + 1) t) := h1
        _ = 2 ^ 555 * (evalPoly ExpCertV.numExpV t * DENv (v + 1) t) := by ring
    exact le_of_mul_le_mul_left h2 hp555

/-- **The tie at the runtime point (nonpositive half)**: the directions flip. -/
theorem tie_under {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htnp : int256 (tTree x) ≤ 0) :
    NUMv (vTree x) (int256 (tTree x)) * evalPoly ExpCertV.denExpV (int256 (tTree x)) ≤
        evalPoly ExpCertV.numExpV (int256 (tTree x)) * DENv (vTree x) (int256 (tTree x)) ∧
      evalPoly ExpCertV.numExpV (int256 (tTree x)) * DENv (vTree x + 1) (int256 (tTree x)) ≤
        NUMv (vTree x + 1) (int256 (tTree x)) * evalPoly ExpCertV.denExpV (int256 (tTree x)) := by
  obtain ⟨haw, hwb⟩ := tsq_split hx hC hC0
  set t := int256 (tTree x) with htdef
  set v := vTree x with hvdef
  have hs : (0:Int) ≤ 2 ^ 23 * (-t) := by
    have : (0:Int) ≤ -t := by linarith [htnp]
    positivity
  have ha : (0:Int) ≤ 2 ^ 133 * (v : Int) := by positivity
  have hw : (0:Int) ≤ t ^ 2 := sq_nonneg _
  have hb1 : t ^ 2 ≤ 2 ^ 133 * ((v + 1 : Nat) : Int) := by push_cast; linarith [hwb]
  have hp555 : (0:Int) < 2 ^ 555 := by positivity
  -- with σ = −s ≥ 0, the `N`/`D` roles swap: Pev + σ·Pod = DENv-form, Pev − σ·Pod = NUMv-form
  constructor
  · have h1 := tie_cross (a := 2 ^ 133 * (v : Int)) (b := t ^ 2) (2 ^ 23 * (-t)) ha haw hs
    -- rewrite σ-forms into t-forms: Pev x + 2^23·(−t)·Pod x = Pev x − 2^23·t·Pod x
    have e1 : evalPoly Pev (t ^ 2) + 2 ^ 23 * (-t) * evalPoly Pod (t ^ 2) =
        evalPoly ExpCertV.denExpV t := by rw [DE_eq_w]; ring
    have e2 : evalPoly Pev (2 ^ 133 * (v : Int)) - 2 ^ 23 * (-t) * evalPoly Pod (2 ^ 133 * (v : Int)) =
        2 ^ 555 * NUMv v t := by rw [← grid_num_eq]; ring
    have e3 : evalPoly Pev (2 ^ 133 * (v : Int)) + 2 ^ 23 * (-t) * evalPoly Pod (2 ^ 133 * (v : Int)) =
        2 ^ 555 * DENv v t := by rw [← grid_den_eq]; ring
    have e4 : evalPoly Pev (t ^ 2) - 2 ^ 23 * (-t) * evalPoly Pod (t ^ 2) =
        evalPoly ExpCertV.numExpV t := by rw [NE_eq_w]; ring
    rw [e1, e2, e3, e4] at h1
    -- h1 : DE·(2^555·NUMv v t) ≤ (2^555·DENv v t)·NE
    have h2 : 2 ^ 555 * (NUMv v t * evalPoly ExpCertV.denExpV t) ≤
        2 ^ 555 * (evalPoly ExpCertV.numExpV t * DENv v t) := by
      calc 2 ^ 555 * (NUMv v t * evalPoly ExpCertV.denExpV t)
          = evalPoly ExpCertV.denExpV t * (2 ^ 555 * NUMv v t) := by ring
        _ ≤ 2 ^ 555 * DENv v t * evalPoly ExpCertV.numExpV t := h1
        _ = 2 ^ 555 * (evalPoly ExpCertV.numExpV t * DENv v t) := by ring
    exact le_of_mul_le_mul_left h2 hp555
  · have h1 := tie_cross (a := t ^ 2) (b := 2 ^ 133 * ((v + 1 : Nat) : Int)) (2 ^ 23 * (-t)) hw hb1 hs
    have e1 : evalPoly Pev (2 ^ 133 * ((v + 1 : Nat) : Int)) +
        2 ^ 23 * (-t) * evalPoly Pod (2 ^ 133 * ((v + 1 : Nat) : Int)) =
        2 ^ 555 * DENv (v + 1) t := by rw [← grid_den_eq]; ring
    have e2 : evalPoly Pev (t ^ 2) - 2 ^ 23 * (-t) * evalPoly Pod (t ^ 2) =
        evalPoly ExpCertV.numExpV t := by rw [NE_eq_w]; ring
    have e3 : evalPoly Pev (t ^ 2) + 2 ^ 23 * (-t) * evalPoly Pod (t ^ 2) =
        evalPoly ExpCertV.denExpV t := by rw [DE_eq_w]; ring
    have e4 : evalPoly Pev (2 ^ 133 * ((v + 1 : Nat) : Int)) -
        2 ^ 23 * (-t) * evalPoly Pod (2 ^ 133 * ((v + 1 : Nat) : Int)) =
        2 ^ 555 * NUMv (v + 1) t := by rw [← grid_num_eq]; ring
    rw [e1, e2, e3, e4] at h1
    -- h1 : (2^555·DENv (v+1) t)·NE ≤ DE·(2^555·NUMv (v+1) t)
    have h2 : 2 ^ 555 * (evalPoly ExpCertV.numExpV t * DENv (v + 1) t) ≤
        2 ^ 555 * (NUMv (v + 1) t * evalPoly ExpCertV.denExpV t) := by
      calc 2 ^ 555 * (evalPoly ExpCertV.numExpV t * DENv (v + 1) t)
          = 2 ^ 555 * DENv (v + 1) t * evalPoly ExpCertV.numExpV t := by ring
        _ ≤ evalPoly ExpCertV.denExpV t * (2 ^ 555 * NUMv (v + 1) t) := h1
        _ = 2 ^ 555 * (NUMv (v + 1) t * evalPoly ExpCertV.denExpV t) := by ring
    exact le_of_mul_le_mul_left h2 hp555

/-! ## The 32-piece granularity certificate -/

/-- The per-piece granularity facts at a grid point `v`: positivity of the floors and the cap,
the certified over/under denominator floors at both cells `v` and `v + 1`, the `K` cap, and the
certified budget inequalities of the piece against the two exported envelopes
(`3290521163436398582/10¹⁹` over, `1644901622230542074/10¹⁹` under, `Mp`-folded). -/
def PieceOK (v : Nat) (T DO DU Khi : Int) : Prop :=
  0 < DO ∧ 0 < DU ∧ 0 ≤ Khi ∧ 0 ≤ T ∧
  DO * 2 ^ 725 ≤ (evNumV v : Int) * 2 ^ 110 - T * (odNumV v : Int) ∧
  DO * 2 ^ 725 ≤ (evNumV (v + 1) : Int) * 2 ^ 110 - T * (odNumV (v + 1) : Int) ∧
  DU * 2 ^ 725 ≤ (evNumV v : Int) * 2 ^ 110 + T * (odNumV v : Int) ∧
  DU * 2 ^ 725 ≤ (evNumV (v + 1) : Int) * 2 ^ 110 + T * (odNumV (v + 1) : Int) ∧
  KpM v ≤ Khi ∧
  2 * T * 2 ^ 110 * Khi * 2 ^ 126 * 10000000000000000000 ≤
    3290521163436398582 * ((DO * 2 ^ 725) * (DO * 2 ^ 725)) ∧
  2 ^ 126 * 2 ^ 131 * (2 * T * 2 ^ 110 * Khi) * 10000000000000000000 ≤
    1644901622230542074 * ((2 ^ 131 - 1) * ((DU * 2 ^ 725) * (DU * 2 ^ 725)))

/-- The piece cap dominates the square: from the split `t² < 2^133·v + 2^133`, membership
`v ≤ vhi`, and the cap fact `2^133·(vhi + 1) ≤ T²`. -/
theorem tsq_lt_capsq {t : Int} {v : Nat} (hsplit : t ^ 2 < 2 ^ 133 * (v : Int) + 2 ^ 133)
    {vhi : Nat} (hv : v ≤ vhi) {T : Int}
    (hT : 2 ^ 133 * ((vhi : Nat) : Int) + 2 ^ 133 ≤ T ^ 2) :
    t ^ 2 < T ^ 2 := by
  have hvI : ((v : Nat) : Int) ≤ ((vhi : Nat) : Int) := by exact_mod_cast hv
  nlinarith [hsplit, hT, hvI]

theorem granPiece00 {v : Nat} (hlo : 0 ≤ v)
    (hhi : v ≤ 39914474797457073157829141722193111) :
    PieceOK v 20847785078312632088902884100098393904 650161701553 691253358954
      124331295357477641581904138056792287020328920739682114857664357354828442875869025295095260106579486090794973807518308090512373664288724599481183645678243760168249900040574863180675819774653612798639898143210993293324267181199503250600403357996412545035325722827268263235801420237458721567675109488896589057678111549643018134304154993533622467567878144 := by
  have hvlo : (0 : Int) ≤ (v : Int) := by exact_mod_cast hlo
  have hvhi : (v : Int) ≤ (39914474797457073157829141722193111 : Int) := by exact_mod_cast hhi
  have hOv := ExpCertV.dOvP00_nonneg (t := (v : Int)) (by omega) (by omega)
  have hOv1 := ExpCertV.dOvP00_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hUn := ExpCertV.dUnP00_nonneg (t := (v : Int)) (by omega) (by omega)
  have hUn1 := ExpCertV.dUnP00_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
  rw [evalDOverP] at hOv
  rw [evalDUnderP] at hUn
  rw [hcast, evalDOverP] at hOv1
  rw [hcast, evalDUnderP] at hUn1
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by linarith [hOv],
    by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
    KpM_le_at hhi (by simp only [Kpoly, evalPoly]; norm_num), by norm_num, by norm_num⟩

theorem granPiece01 {v : Nat} (hlo : 39914474797457073157829141722193111 ≤ v)
    (hhi : v ≤ 79828949594914146315658283444386223) :
    PieceOK v 29483220403189161767243017845519310570 641945658278 700065691212
      124348489536362811569823373638009000631667158096130666095582598399588448399876764381232405323636520833790009233576804961032917177931334727395109926278389044009567787762950649201982921306130024347784555916617412077827586978026950159438110911930706312161198243458825239986622498328512019492013159710459919171534255316797621253672688089454967194376994816 := by
  have hvlo : (39914474797457073157829141722193111 : Int) ≤ (v : Int) := by exact_mod_cast hlo
  have hvhi : (v : Int) ≤ (79828949594914146315658283444386223 : Int) := by exact_mod_cast hhi
  have hOv := ExpCertV.dOvP01_nonneg (t := (v : Int)) (by omega) (by omega)
  have hOv1 := ExpCertV.dOvP01_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hUn := ExpCertV.dUnP01_nonneg (t := (v : Int)) (by omega) (by omega)
  have hUn1 := ExpCertV.dUnP01_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
  rw [evalDOverP] at hOv
  rw [evalDUnderP] at hUn
  rw [hcast, evalDOverP] at hOv1
  rw [hcast, evalDUnderP] at hUn1
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by linarith [hOv],
    by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
    KpM_le_at hhi (by simp only [Kpoly, evalPoly]; norm_num), by norm_num, by norm_num⟩

theorem granPiece02 {v : Nat} (hlo : 79828949594914146315658283444386223 ≤ v)
    (hhi : v ≤ 119743424392371219473487425166579335) :
    PieceOK v 36109422980913784159270707268699614620 635708060030 706899646710
      124365685902235707931662185236865182628053618073184713460247915523785590877700978509232142340905979095147288222533178910762560856667920293458238258376258151566628589949793659760772938934721283732147475148813094180263002559134506224431737786068252674285070073042702412156288743997299619998620649343861387292828263704160125292993790052190201592961630208 := by
  have hvlo : (79828949594914146315658283444386223 : Int) ≤ (v : Int) := by exact_mod_cast hlo
  have hvhi : (v : Int) ≤ (119743424392371219473487425166579335 : Int) := by exact_mod_cast hhi
  have hOv := ExpCertV.dOvP02_nonneg (t := (v : Int)) (by omega) (by omega)
  have hOv1 := ExpCertV.dOvP02_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hUn := ExpCertV.dUnP02_nonneg (t := (v : Int)) (by omega) (by omega)
  have hUn1 := ExpCertV.dUnP02_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
  rw [evalDOverP] at hOv
  rw [evalDUnderP] at hUn
  rw [hcast, evalDOverP] at hOv1
  rw [hcast, evalDUnderP] at hUn1
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by linarith [hOv],
    by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
    KpM_le_at hhi (by simp only [Kpoly, evalPoly]; norm_num), by norm_num, by norm_num⟩

theorem granPiece03 {v : Nat} (hlo : 119743424392371219473487425166579335 ≤ v)
    (hhi : v ≤ 159657899189828292631316566888772447) :
    PieceOK v 41695570156625264177805768200196787807 630494171758 712709960499
      124382884455293592549521181635541090166983243381366801077634704386449155123538147775095644383601673251595741250522853679574835669070847383007608443452883503401958520975393281340104778870044828386724379056340673155550940420245984273438033970455973764538100904452446937706327654059882649333342250388341747084762611362343708770595139697547437718802268160 := by
  have hvlo : (119743424392371219473487425166579335 : Int) ≤ (v : Int) := by exact_mod_cast hlo
  have hvhi : (v : Int) ≤ (159657899189828292631316566888772447 : Int) := by exact_mod_cast hhi
  have hOv := ExpCertV.dOvP03_nonneg (t := (v : Int)) (by omega) (by omega)
  have hOv1 := ExpCertV.dOvP03_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hUn := ExpCertV.dUnP03_nonneg (t := (v : Int)) (by omega) (by omega)
  have hUn1 := ExpCertV.dUnP03_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
  rw [evalDOverP] at hOv
  rw [evalDUnderP] at hUn
  rw [hcast, evalDOverP] at hOv1
  rw [hcast, evalDUnderP] at hUn1
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by linarith [hOv],
    by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
    KpM_le_at hhi (by simp only [Kpoly, evalPoly]; norm_num), by norm_num, by norm_num⟩

theorem granPiece04 {v : Nat} (hlo : 159657899189828292631316566888772447 ≤ v)
    (hhi : v ≤ 199572373987285365789145708610965559) :
    PieceOK v 46617064615412821983671927489259435287 625934238048 717866387998
      124400085195733739761025602560746264278616327664634676182714279775205998993015648254637590643537148550327888188208261194060492726583694561054370906623381684559581344625217362931467757553311495193356235609856263696492370325585701457614481355682705860334329988295937236347726204889864872718037319011296191356466375193232176092864574154432488170961567744 := by
  have hvlo : (159657899189828292631316566888772447 : Int) ≤ (v : Int) := by exact_mod_cast hlo
  have hvhi : (v : Int) ≤ (199572373987285365789145708610965559 : Int) := by exact_mod_cast hhi
  have hOv := ExpCertV.dOvP04_nonneg (t := (v : Int)) (by omega) (by omega)
  have hOv1 := ExpCertV.dOvP04_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hUn := ExpCertV.dUnP04_nonneg (t := (v : Int)) (by omega) (by omega)
  have hUn1 := ExpCertV.dUnP04_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
  rw [evalDOverP] at hOv
  rw [evalDUnderP] at hUn
  rw [hcast, evalDOverP] at hOv1
  rw [hcast, evalDUnderP] at hUn1
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by linarith [hOv],
    by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
    KpM_le_at hhi (by simp only [Kpoly, evalPoly]; norm_num), by norm_num, by norm_num⟩

theorem granPiece05 {v : Nat} (hlo : 199572373987285365789145708610965559 ≤ v)
    (hhi : v ≤ 239486848784742438946974850333158671) :
    PieceOK v 51066435709074987640046250875008841866 621838651900 722558536211
      124417288123753436359835347518639131950249764195910712565839043606640499191676068467176975973602845905061591734256371371103126949086855419317934911533825904835688101580924850386714202151580739880884301210530166827007365319166903338988033945677286795960322070677949568801220865415748091974787433067612090788738328422094161653434502497346696847251472384 := by
  have hvlo : (199572373987285365789145708610965559 : Int) ≤ (v : Int) := by exact_mod_cast hlo
  have hvhi : (v : Int) ≤ (239486848784742438946974850333158671 : Int) := by exact_mod_cast hhi
  have hOv := ExpCertV.dOvP05_nonneg (t := (v : Int)) (by omega) (by omega)
  have hOv1 := ExpCertV.dOvP05_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hUn := ExpCertV.dUnP05_nonneg (t := (v : Int)) (by omega) (by omega)
  have hUn1 := ExpCertV.dUnP05_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
  rw [evalDOverP] at hOv
  rw [evalDUnderP] at hUn
  rw [hcast, evalDOverP] at hOv1
  rw [hcast, evalDUnderP] at hUn1
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by linarith [hOv],
    by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
    KpM_le_at hhi (by simp only [Kpoly, evalPoly]; norm_num), by norm_num, by norm_num⟩

theorem granPiece06 {v : Nat} (hlo : 239486848784742438946974850333158671 ≤ v)
    (hhi : v ≤ 279401323582199512104803992055351783) :
    PieceOK v 55158054703738454765934460694358669515 618094793288 726899025166
      124434493239549981596155017198872213098454764998568650821632835242999466335788378628546409502791047296403032067730444905302684600204546104057200490811476284704813315263361171252130107427929606736210745667903934480980096706370969525764751373103018335410042751956297398979863880642988644489413669262837966594493347115533922961077511275265630319091449856 := by
  have hvlo : (239486848784742438946974850333158671 : Int) ≤ (v : Int) := by exact_mod_cast hlo
  have hvhi : (v : Int) ≤ (279401323582199512104803992055351783 : Int) := by exact_mod_cast hhi
  have hOv := ExpCertV.dOvP06_nonneg (t := (v : Int)) (by omega) (by omega)
  have hOv1 := ExpCertV.dOvP06_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hUn := ExpCertV.dUnP06_nonneg (t := (v : Int)) (by omega) (by omega)
  have hUn1 := ExpCertV.dUnP06_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
  rw [evalDOverP] at hOv
  rw [evalDUnderP] at hUn
  rw [hcast, evalDOverP] at hOv1
  rw [hcast, evalDUnderP] at hUn1
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by linarith [hOv],
    by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
    KpM_le_at hhi (by simp only [Kpoly, evalPoly]; norm_num), by norm_num, by norm_num⟩

theorem granPiece07 {v : Nat} (hlo : 279401323582199512104803992055351783 ≤ v)
    (hhi : v ≤ 319315798379656585262633133777544895) :
    PieceOK v 58966440806378323534486035691038621139 614629293866 730961223213
      124451700543320687177243967447907493738634686713280628775100983611975805202752040889353877413014375516832698931548482651718513021265559009370228602810259469061747536661164515780773577557318528060603071915307121370309066625679902290704035239727413694095262005826377985200395700851400403348591051117166980795442448657546058790199544851673655003010039808 := by
  have hvlo : (279401323582199512104803992055351783 : Int) ≤ (v : Int) := by exact_mod_cast hlo
  have hvhi : (v : Int) ≤ (319315798379656585262633133777544895 : Int) := by exact_mod_cast hhi
  have hOv := ExpCertV.dOvP07_nonneg (t := (v : Int)) (by omega) (by omega)
  have hOv1 := ExpCertV.dOvP07_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hUn := ExpCertV.dUnP07_nonneg (t := (v : Int)) (by omega) (by omega)
  have hUn1 := ExpCertV.dUnP07_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
  rw [evalDOverP] at hOv
  rw [evalDUnderP] at hUn
  rw [hcast, evalDOverP] at hOv1
  rw [hcast, evalDUnderP] at hUn1
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by linarith [hOv],
    by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
    KpM_le_at hhi (by simp only [Kpoly, evalPoly]; norm_num), by norm_num, by norm_num⟩

theorem granPiece08 {v : Nat} (hlo : 319315798379656585262633133777544895 ≤ v)
    (hhi : v ≤ 359230273177113658420462275499738007) :
    PieceOK v 62543355234937896266708652300295181711 611391198603 734796085384
      124468910035262877267926375811746527820975306698922635425840511894904787143595947811096724002989298686672217212850128746563838558316488647056623737058434359811261359426985503361599249033910735301816371731468685286395592499639857246867579557693036893681604611310616417652470415124037663243490099281703786843208686442477137477570980613863363719996702720 := by
  have hvlo : (319315798379656585262633133777544895 : Int) ≤ (v : Int) := by exact_mod_cast hlo
  have hvhi : (v : Int) ≤ (359230273177113658420462275499738007 : Int) := by exact_mod_cast hhi
  have hOv := ExpCertV.dOvP08_nonneg (t := (v : Int)) (by omega) (by omega)
  have hOv1 := ExpCertV.dOvP08_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hUn := ExpCertV.dUnP08_nonneg (t := (v : Int)) (by omega) (by omega)
  have hUn1 := ExpCertV.dUnP08_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
  rw [evalDOverP] at hOv
  rw [evalDUnderP] at hUn
  rw [hcast, evalDOverP] at hOv1
  rw [hcast, evalDUnderP] at hUn1
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by linarith [hOv],
    by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
    KpM_le_at hhi (by simp only [Kpoly, evalPoly]; norm_num), by norm_num, by norm_num⟩

theorem granPiece09 {v : Nat} (hlo : 359230273177113658420462275499738007 ≤ v)
    (hhi : v ≤ 399144747974570731578291417221931119) :
    PieceOK v 65926485017139723075679505829736200590 608343412382 738440706802
      124486121715573888491101320648219831360978600025531681717397876827306892665309875389393384048481768653425841939803068139643786342072540530559822902480426047209561307177697067146275358391575766288843286569489630219937769323348732794039548321162137129920186263470953090477298031369179281491517916152969142359753029790232869618689856252942753648165781504 := by
  have hvlo : (359230273177113658420462275499738007 : Int) ≤ (v : Int) := by exact_mod_cast hlo
  have hvhi : (v : Int) ≤ (399144747974570731578291417221931119 : Int) := by exact_mod_cast hhi
  have hOv := ExpCertV.dOvP09_nonneg (t := (v : Int)) (by omega) (by omega)
  have hOv1 := ExpCertV.dOvP09_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hUn := ExpCertV.dUnP09_nonneg (t := (v : Int)) (by omega) (by omega)
  have hUn1 := ExpCertV.dUnP09_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
  rw [evalDOverP] at hOv
  rw [evalDUnderP] at hUn
  rw [hcast, evalDOverP] at hOv1
  rw [hcast, evalDUnderP] at hUn1
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by linarith [hOv],
    by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
    KpM_le_at hhi (by simp only [Kpoly, evalPoly]; norm_num), by norm_num, by norm_num⟩

theorem granPiece10 {v : Nat} (hlo : 399144747974570731578291417221931119 ≤ v)
    (hhi : v ≤ 439059222772027804736120558944124231) :
    PieceOK v 69144280814733066627417644920644591155 605457935097 741923087576
      124503335584451069928252872808980133651989775186603141404988555934311273225981935990264178352237801072926478468069242743489283246177418736929404644129855308733243265589345733196988586035281255492337370426875119924531347417976092688100894991354677828964594141904176367929784428502523428286373737126082244818656262835605108546925443459326996088449204224 := by
  have hvlo : (399144747974570731578291417221931119 : Int) ≤ (v : Int) := by exact_mod_cast hlo
  have hvhi : (v : Int) ≤ (439059222772027804736120558944124231 : Int) := by exact_mod_cast hhi
  have hOv := ExpCertV.dOvP10_nonneg (t := (v : Int)) (by omega) (by omega)
  have hOv1 := ExpCertV.dOvP10_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hUn := ExpCertV.dUnP10_nonneg (t := (v : Int)) (by omega) (by omega)
  have hUn1 := ExpCertV.dUnP10_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
  rw [evalDOverP] at hOv
  rw [evalDUnderP] at hUn
  rw [hcast, evalDOverP] at hOv1
  rw [hcast, evalDUnderP] at hUn1
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by linarith [hOv],
    by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
    KpM_le_at hhi (by simp only [Kpoly, evalPoly]; norm_num), by norm_num, by norm_num⟩

theorem granPiece11 {v : Nat} (hlo : 439059222772027804736120558944124231 ≤ v)
    (hhi : v ≤ 478973697569484877893949700666317343) :
    PieceOK v 72218845961827568318541414537399229239 602713016329 745264978126
      124520551642091783119960199891344051506346033527311875260959727302093972320951315622058263260947483656752103483840493935299413014630172637166451445835836333123354402531969814020920275057050896729991379522855922790213174946038953724627140431546256563282790729321557975220766789962190285045276381221546310035474840890128611108344299521825576877289373696 := by
  have hvlo : (439059222772027804736120558944124231 : Int) ≤ (v : Int) := by exact_mod_cast hlo
  have hvhi : (v : Int) ≤ (478973697569484877893949700666317343 : Int) := by exact_mod_cast hhi
  have hOv := ExpCertV.dOvP11_nonneg (t := (v : Int)) (by omega) (by omega)
  have hOv1 := ExpCertV.dOvP11_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hUn := ExpCertV.dUnP11_nonneg (t := (v : Int)) (by omega) (by omega)
  have hUn1 := ExpCertV.dUnP11_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
  rw [evalDOverP] at hOv
  rw [evalDUnderP] at hUn
  rw [hcast, evalDOverP] at hOv1
  rw [hcast, evalDUnderP] at hUn1
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by linarith [hOv],
    by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
    KpM_le_at hhi (by simp only [Kpoly, evalPoly]; norm_num), by norm_num, by norm_num⟩

theorem granPiece12 {v : Nat} (hlo : 478973697569484877893949700666317343 ≤ v)
    (hhi : v ≤ 518888172366941951051778842388510455) :
    PieceOK v 75167758079709234538337434275175078691 600091361400 748483673135
      124537769888693402066407683060126753630994224554535911823544217765065136973421379022289603810616577756414482304042522678965020214723268111737918587829660616124019790143784379899466091486140170232387841381760682133717066154372228166965327582139308493893339685755904415758459311234618014480863534215048472382060547521413140374874865461769524694558507008 := by
  have hvlo : (478973697569484877893949700666317343 : Int) ≤ (v : Int) := by exact_mod_cast hlo
  have hvhi : (v : Int) ≤ (518888172366941951051778842388510455 : Int) := by exact_mod_cast hhi
  have hOv := ExpCertV.dOvP12_nonneg (t := (v : Int)) (by omega) (by omega)
  have hOv1 := ExpCertV.dOvP12_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hUn := ExpCertV.dUnP12_nonneg (t := (v : Int)) (by omega) (by omega)
  have hUn1 := ExpCertV.dUnP12_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
  rw [evalDOverP] at hOv
  rw [evalDUnderP] at hUn
  rw [hcast, evalDOverP] at hOv1
  rw [hcast, evalDUnderP] at hUn1
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by linarith [hOv],
    by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
    KpM_le_at hhi (by simp only [Kpoly, evalPoly]; norm_num), by norm_num, by norm_num⟩

theorem granPiece13 {v : Nat} (hlo : 518888172366941951051778842388510455 ≤ v)
    (hhi : v ≤ 558802647164399024209607984110703567) :
    PieceOK v 78005269036144011942405564982788931618 597578949702 751593193213
      124554990324453313227895046439614183402643276463856617860620826667139541778214025095310619045745557140858097807995342065606587337322533394468882240084030263306935213398607214962659659999055128481075083753732139252846167979947868188032272919467882501275172597180793487630740957574925310783905297794170644686405700341432141068220616476957382929185505280 := by
  have hvlo : (518888172366941951051778842388510455 : Int) ≤ (v : Int) := by exact_mod_cast hlo
  have hvhi : (v : Int) ≤ (558802647164399024209607984110703567 : Int) := by exact_mod_cast hhi
  have hOv := ExpCertV.dOvP13_nonneg (t := (v : Int)) (by omega) (by omega)
  have hOv1 := ExpCertV.dOvP13_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hUn := ExpCertV.dUnP13_nonneg (t := (v : Int)) (by omega) (by omega)
  have hUn1 := ExpCertV.dUnP13_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
  rw [evalDOverP] at hOv
  rw [evalDUnderP] at hUn
  rw [hcast, evalDOverP] at hOv1
  rw [hcast, evalDUnderP] at hUn1
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by linarith [hOv],
    by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
    KpM_le_at hhi (by simp only [Kpoly, evalPoly]; norm_num), by norm_num, by norm_num⟩

theorem granPiece14 {v : Nat} (hlo : 558802647164399024209607984110703567 ≤ v)
    (hhi : v ≤ 598717121961856097367437125832896679) :
    PieceOK v 80743124413616312505576435261721815008 595164227770 754605091830
      124572212949568915525347499075817409466735988388004451686363063634024838682581974293417926941741606509843226188507680602219637031806014514444459283762049224244872920374774308501649176691013237726857731636612069833000109322912017234062636495543175662919935430568420743292434031610801823061616938660393534826247558241784867596685707613532519179226251264 := by
  have hvlo : (558802647164399024209607984110703567 : Int) ≤ (v : Int) := by exact_mod_cast hlo
  have hvhi : (v : Int) ≤ (598717121961856097367437125832896679 : Int) := by exact_mod_cast hhi
  have hOv := ExpCertV.dOvP14_nonneg (t := (v : Int)) (by omega) (by omega)
  have hOv1 := ExpCertV.dOvP14_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hUn := ExpCertV.dUnP14_nonneg (t := (v : Int)) (by omega) (by omega)
  have hUn1 := ExpCertV.dUnP14_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
  rw [evalDOverP] at hOv
  rw [evalDUnderP] at hUn
  rw [hcast, evalDOverP] at hOv1
  rw [hcast, evalDUnderP] at hUn1
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by linarith [hOv],
    by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
    KpM_le_at hhi (by simp only [Kpoly, evalPoly]; norm_num), by norm_num, by norm_num⟩

theorem granPiece15 {v : Nat} (hlo : 598717121961856097367437125832896679 ≤ v)
    (hhi : v ≤ 638631596759313170525266267555089791) :
    PieceOK v 83391140313250528355611536400393575614 592837541332 757529023260
      124589437764237620340825889469153674743743478040514552434825270072062036723231468590650395244014780971823114564072078109181139128465160131976111064838226271169192340088167775554464468086418974592526508495351327534529428960424730857521734109493908231115773540654136507544239294024475729934998271889261575071337487560484493736830994727238304877368049664 := by
  have hvlo : (598717121961856097367437125832896679 : Int) ≤ (v : Int) := by exact_mod_cast hlo
  have hvhi : (v : Int) ≤ (638631596759313170525266267555089791 : Int) := by exact_mod_cast hhi
  have hOv := ExpCertV.dOvP15_nonneg (t := (v : Int)) (by omega) (by omega)
  have hOv1 := ExpCertV.dOvP15_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hUn := ExpCertV.dUnP15_nonneg (t := (v : Int)) (by omega) (by omega)
  have hUn1 := ExpCertV.dUnP15_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
  rw [evalDOverP] at hOv
  rw [evalDUnderP] at hUn
  rw [hcast, evalDOverP] at hOv1
  rw [hcast, evalDUnderP] at hUn1
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by linarith [hOv],
    by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
    KpM_le_at hhi (by simp only [Kpoly, evalPoly]; norm_num), by norm_num, by norm_num⟩

theorem granPiece16 {v : Nat} (hlo : 638631596759313170525266267555089791 ≤ v)
    (hhi : v ≤ 678546071556770243683095409277282902) :
    PieceOK v 85957619938058733268340145980060814334 590590725148 760373152745
      124606664768656851518036872677698715585072660242495883986009404890147362516004161739630680550417490341371797531129102305738763492805064552636381614815576193227674230986790052469783804926104175636072026017497532913712764135972392518808738959695402684214634690318526071631420652836377713510044584171075898860077101066298649153619546421349176320735146240 := by
  have hvlo : (638631596759313170525266267555089791 : Int) ≤ (v : Int) := by exact_mod_cast hlo
  have hvhi : (v : Int) ≤ (678546071556770243683095409277282902 : Int) := by exact_mod_cast hhi
  have hOv := ExpCertV.dOvP16_nonneg (t := (v : Int)) (by omega) (by omega)
  have hOv1 := ExpCertV.dOvP16_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hUn := ExpCertV.dUnP16_nonneg (t := (v : Int)) (by omega) (by omega)
  have hUn1 := ExpCertV.dUnP16_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
  rw [evalDOverP] at hOv
  rw [evalDUnderP] at hUn
  rw [hcast, evalDOverP] at hOv1
  rw [hcast, evalDUnderP] at hUn1
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by linarith [hOv],
    by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
    KpM_le_at hhi (by simp only [Kpoly, evalPoly]; norm_num), by norm_num, by norm_num⟩

theorem granPiece17 {v : Nat} (hlo : 678546071556770243683095409277282902 ≤ v)
    (hhi : v ≤ 718460546354227316840924550999476014) :
    PieceOK v 88449661209567485301729053536557931646 588416800156 763144459353
      124623893963024045362843089991154923983117161607319595250352276881176522492194884460613602543396335504591097167825116970547969978539214562134291228254489780808179367553929062370966123062130918023648372481946314641375078442083168666134142802373602001339140773737530082849770581207983047544000442080270054092120631736071247951487235378516868923389575424 := by
  have hvlo : (678546071556770243683095409277282902 : Int) ≤ (v : Int) := by exact_mod_cast hlo
  have hvhi : (v : Int) ≤ (718460546354227316840924550999476014 : Int) := by exact_mod_cast hhi
  have hOv := ExpCertV.dOvP17_nonneg (t := (v : Int)) (by omega) (by omega)
  have hOv1 := ExpCertV.dOvP17_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hUn := ExpCertV.dUnP17_nonneg (t := (v : Int)) (by omega) (by omega)
  have hUn1 := ExpCertV.dUnP17_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
  rw [evalDOverP] at hOv
  rw [evalDUnderP] at hUn
  rw [hcast, evalDOverP] at hOv1
  rw [hcast, evalDUnderP] at hUn1
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by linarith [hOv],
    by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
    KpM_le_at hhi (by simp only [Kpoly, evalPoly]; norm_num), by norm_num, by norm_num⟩

theorem granPiece18 {v : Nat} (hlo : 718460546354227316840924550999476014 ≤ v)
    (hhi : v ≤ 758375021151684389998753692721669126) :
    PieceOK v 90873388353019950250431101958484117810 586309745473 765848963968
      124641125347536650643773361175679926890136980575009349858406217274206787157703076060760159328132847795954730513979593904465877332579468208634643270080823067198699615091677996267451877154545985645750394641445535218127962690400435113781818788548560000033757028278051636102985402707506385563404221303398065990638629109910072511299669406189628394175746304 := by
  have hvlo : (718460546354227316840924550999476014 : Int) ≤ (v : Int) := by exact_mod_cast hlo
  have hvhi : (v : Int) ≤ (758375021151684389998753692721669126 : Int) := by exact_mod_cast hhi
  have hOv := ExpCertV.dOvP18_nonneg (t := (v : Int)) (by omega) (by omega)
  have hOv1 := ExpCertV.dOvP18_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hUn := ExpCertV.dUnP18_nonneg (t := (v : Int)) (by omega) (by omega)
  have hUn1 := ExpCertV.dUnP18_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
  rw [evalDOverP] at hOv
  rw [evalDUnderP] at hUn
  rw [hcast, evalDOverP] at hOv1
  rw [hcast, evalDUnderP] at hUn1
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by linarith [hOv],
    by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
    KpM_le_at hhi (by simp only [Kpoly, evalPoly]; norm_num), by norm_num, by norm_num⟩

theorem granPiece19 {v : Nat} (hlo : 758375021151684389998753692721669126 ≤ v)
    (hhi : v ≤ 798289495949141463156582834443862238) :
    PieceOK v 93234129230825643967343854978518870515 584264323835 768491903858
      124658358922392128592532889289720157874976973585349126591994191589414143318317674249585953939689445877907213043541773343109004895170973418880732978969822834172603369724256116429567360678907949821785338291542213555676264600392085383654932815516512038924179692395697310049431946123044099632008145784092080082008997282395902899780773760707018755557253376 := by
  have hvlo : (758375021151684389998753692721669126 : Int) ≤ (v : Int) := by exact_mod_cast hlo
  have hvhi : (v : Int) ≤ (798289495949141463156582834443862238 : Int) := by exact_mod_cast hhi
  have hOv := ExpCertV.dOvP19_nonneg (t := (v : Int)) (by omega) (by omega)
  have hOv1 := ExpCertV.dOvP19_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hUn := ExpCertV.dUnP19_nonneg (t := (v : Int)) (by omega) (by omega)
  have hUn1 := ExpCertV.dUnP19_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
  rw [evalDOverP] at hOv
  rw [evalDUnderP] at hUn
  rw [hcast, evalDOverP] at hOv1
  rw [hcast, evalDUnderP] at hUn1
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by linarith [hOv],
    by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
    KpM_le_at hhi (by simp only [Kpoly, evalPoly]; norm_num), by norm_num, by norm_num⟩

theorem granPiece20 {v : Nat} (hlo : 798289495949141463156582834443862238 ≤ v)
    (hhi : v ≤ 838203970746598536314411976166055350) :
    PieceOK v 95536553193538501370371342040089081115 582275945893 771077868376
      124675594687787952904513478070993997490747165237763127035427566697901602250251952214812407209685403872705846247477937047935221784504131219775890895308710226597840163524000974576243137476334383522428088205286797851946215689878018940255286367216193327977552796517938163227068652880076009442161336421787011377599536749774501652579713675135944281723646208 := by
  have hvlo : (798289495949141463156582834443862238 : Int) ≤ (v : Int) := by exact_mod_cast hlo
  have hvhi : (v : Int) ≤ (838203970746598536314411976166055350 : Int) := by exact_mod_cast hhi
  have hOv := ExpCertV.dOvP20_nonneg (t := (v : Int)) (by omega) (by omega)
  have hOv1 := ExpCertV.dOvP20_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hUn := ExpCertV.dUnP20_nonneg (t := (v : Int)) (by omega) (by omega)
  have hUn1 := ExpCertV.dUnP20_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
  rw [evalDOverP] at hOv
  rw [evalDUnderP] at hUn
  rw [hcast, evalDOverP] at hOv1
  rw [hcast, evalDUnderP] at hUn1
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by linarith [hOv],
    by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
    KpM_le_at hhi (by simp only [Kpoly, evalPoly]; norm_num), by norm_num, by norm_num⟩

theorem granPiece21 {v : Nat} (hlo : 838203970746598536314411976166055350 ≤ v)
    (hhi : v ≤ 878118445544055609472241117888248462) :
    PieceOK v 97784779688729301059274137358180034302 580340563312 773610905858
      124692832643921609739303761894769059894869896935808653881092735350101587531430032270103876036884746059379184271665190236600427580654736038041033275582180880754632701237253832037879523775618655172970200553493385481080830204492902307986942299213350413599465132724297678377243046317980489697735516365263070803702961102484141857844356429316185731112812800 := by
  have hvlo : (838203970746598536314411976166055350 : Int) ≤ (v : Int) := by exact_mod_cast hlo
  have hvhi : (v : Int) ≤ (878118445544055609472241117888248462 : Int) := by exact_mod_cast hhi
  have hOv := ExpCertV.dOvP21_nonneg (t := (v : Int)) (by omega) (by omega)
  have hOv1 := ExpCertV.dOvP21_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hUn := ExpCertV.dUnP21_nonneg (t := (v : Int)) (by omega) (by omega)
  have hUn1 := ExpCertV.dUnP21_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
  rw [evalDOverP] at hOv
  rw [evalDUnderP] at hUn
  rw [hcast, evalDOverP] at hOv1
  rw [hcast, evalDUnderP] at hUn1
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by linarith [hOv],
    by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
    KpM_le_at hhi (by simp only [Kpoly, evalPoly]; norm_num), by norm_num, by norm_num⟩

theorem granPiece22 {v : Nat} (hlo : 878118445544055609472241117888248462 ≤ v)
    (hhi : v ≤ 918032920341512682630070259610441574) :
    PieceOK v 99982464869820254414073625773477941119 578454583528 776094608873
      124710072790990597721199448303578204419096487383493075972991988236652404616688783744159514396070007044240287824345887307801597044260536584308823059040717802692047418498078277708138651227072800784330541158563593883567212800396557524991247542232380730500213376057729041528063562241291700217040789465713509633913187647063710417510471795210628415965565184 := by
  have hvlo : (878118445544055609472241117888248462 : Int) ≤ (v : Int) := by exact_mod_cast hlo
  have hvhi : (v : Int) ≤ (918032920341512682630070259610441574 : Int) := by exact_mod_cast hhi
  have hOv := ExpCertV.dOvP22_nonneg (t := (v : Int)) (by omega) (by omega)
  have hOv1 := ExpCertV.dOvP22_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hUn := ExpCertV.dUnP22_nonneg (t := (v : Int)) (by omega) (by omega)
  have hUn1 := ExpCertV.dUnP22_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
  rw [evalDOverP] at hOv
  rw [evalDUnderP] at hUn
  rw [hcast, evalDOverP] at hOv1
  rw [hcast, evalDUnderP] at hUn1
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by linarith [hOv],
    by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
    KpM_le_at hhi (by simp only [Kpoly, evalPoly]; norm_num), by norm_num, by norm_num⟩

theorem granPiece23 {v : Nat} (hlo : 918032920341512682630070259610441574 ≤ v)
    (hhi : v ≤ 957947395138969755787899401332634686) :
    PieceOK v 102132871418149975280092501750017683679 576614801025 778532182941
      124727315129192427939713573108518851946746355961540412921623053526083995615369518787406156400695076250720100747414363107465415917032881745828700866616473650876388076205731326151647966692684964360547083172536492161275217469372676434156363226735329424653290080027222154454409639118762860054603295412526333649666966810986577471067570715716735210740850944 := by
  have hvlo : (918032920341512682630070259610441574 : Int) ≤ (v : Int) := by exact_mod_cast hlo
  have hvhi : (v : Int) ≤ (957947395138969755787899401332634686 : Int) := by exact_mod_cast hhi
  have hOv := ExpCertV.dOvP23_nonneg (t := (v : Int)) (by omega) (by omega)
  have hOv1 := ExpCertV.dOvP23_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hUn := ExpCertV.dUnP23_nonneg (t := (v : Int)) (by omega) (by omega)
  have hUn1 := ExpCertV.dUnP23_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
  rw [evalDOverP] at hOv
  rw [evalDUnderP] at hUn
  rw [hcast, evalDOverP] at hOv1
  rw [hcast, evalDUnderP] at hUn1
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by linarith [hOv],
    by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
    KpM_le_at hhi (by simp only [Kpoly, evalPoly]; norm_num), by norm_num, by norm_num⟩

theorem granPiece24 {v : Nat} (hlo : 957947395138969755787899401332634686 ≤ v)
    (hhi : v ≤ 997861869936426828945728543054827798) :
    PieceOK v 104238925391563160444514420500491969466 574818341390 780926502475
      124744559658724623950086768062280187113640267181028232089748655102248273765009698829204279618836024260322304499496915014301962516688500738379965223716524366256202176396180621776988492113153599027805245602558636322821111864671816950930814484595369147288875282103336550254160949808787471699319045469454297801346819930501072096316219218429756015474831616 := by
  have hvlo : (957947395138969755787899401332634686 : Int) ≤ (v : Int) := by exact_mod_cast hlo
  have hvhi : (v : Int) ≤ (997861869936426828945728543054827798 : Int) := by exact_mod_cast hhi
  have hOv := ExpCertV.dOvP24_nonneg (t := (v : Int)) (by omega) (by omega)
  have hOv1 := ExpCertV.dOvP24_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hUn := ExpCertV.dUnP24_nonneg (t := (v : Int)) (by omega) (by omega)
  have hUn1 := ExpCertV.dUnP24_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
  rw [evalDOverP] at hOv
  rw [evalDUnderP] at hUn
  rw [hcast, evalDOverP] at hOv1
  rw [hcast, evalDUnderP] at hUn1
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by linarith [hOv],
    by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
    KpM_le_at hhi (by simp only [Kpoly, evalPoly]; norm_num), by norm_num, by norm_num⟩

theorem granPiece25 {v : Nat} (hlo : 997861869936426828945728543054827798 ≤ v)
    (hhi : v ≤ 1037776344733883902103557684777020910) :
    PieceOK v 106303262929504594869818257246985820007 573062615355 783280156749
      124761806379784721773797541104042828508418061581110710714774372003029423130080663475144885725984487222537025652475264653903117504372851594413000910188341381740535255592335718526729635348334323826293981939499884365304112855169895086556973937458785015484930468250012152902743640195218386165140743123333051189013159768094053531385601709182103604421886208 := by
  have hvlo : (997861869936426828945728543054827798 : Int) ≤ (v : Int) := by exact_mod_cast hlo
  have hvhi : (v : Int) ≤ (1037776344733883902103557684777020910 : Int) := by exact_mod_cast hhi
  have hOv := ExpCertV.dOvP25_nonneg (t := (v : Int)) (by omega) (by omega)
  have hOv1 := ExpCertV.dOvP25_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hUn := ExpCertV.dUnP25_nonneg (t := (v : Int)) (by omega) (by omega)
  have hUn1 := ExpCertV.dUnP25_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
  rw [evalDOverP] at hOv
  rw [evalDUnderP] at hUn
  rw [hcast, evalDOverP] at hOv1
  rw [hcast, evalDUnderP] at hUn1
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by linarith [hOv],
    by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
    KpM_le_at hhi (by simp only [Kpoly, evalPoly]; norm_num), by norm_num, by norm_num⟩

theorem granPiece26 {v : Nat} (hlo : 1037776344733883902103557684777020910 ≤ v)
    (hhi : v ≤ 1077690819531340975261386826499214022) :
    PieceOK v 108328268942741352477812121806098843808 571345280717 785595487968
      124779055292570269899072569176395550207149945606838875899620012840469640089953192690680914462253864237586791356793011581725611868132856890861674052417374931958913382272035748078660810463609033602416655977972300619097870804628644144326794634936383430538313658777665592770608423623112584549096894351992861228505372852729716292034044933517264204570415360 := by
  have hvlo : (1037776344733883902103557684777020910 : Int) ≤ (v : Int) := by exact_mod_cast hlo
  have hvhi : (v : Int) ≤ (1077690819531340975261386826499214022 : Int) := by exact_mod_cast hhi
  have hOv := ExpCertV.dOvP26_nonneg (t := (v : Int)) (by omega) (by omega)
  have hOv1 := ExpCertV.dOvP26_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hUn := ExpCertV.dUnP26_nonneg (t := (v : Int)) (by omega) (by omega)
  have hUn1 := ExpCertV.dUnP26_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
  rw [evalDOverP] at hOv
  rw [evalDUnderP] at hUn
  rw [hcast, evalDOverP] at hOv1
  rw [hcast, evalDUnderP] at hUn1
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by linarith [hOv],
    by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
    KpM_le_at hhi (by simp only [Kpoly, evalPoly]; norm_num), by norm_num, by norm_num⟩

theorem granPiece27 {v : Nat} (hlo : 1077690819531340975261386826499214022 ≤ v)
    (hhi : v ≤ 1117605294328798048419215968221407134) :
    PieceOK v 110316109407476909531868921388717338981 569664210570 787874623042
      124796306397278829281397003614413639136369120172384195170136650261045884215508512174002585745594261301914147584573874806458850831483230446492832284181686273043379455747210133094758593510660561935119569748541092023013191742059770145448509959312139940918154391044235561210772363529417536390085012612494904915323547482551416688009151037590549562881138944 := by
  have hvlo : (1077690819531340975261386826499214022 : Int) ≤ (v : Int) := by exact_mod_cast hlo
  have hvhi : (v : Int) ≤ (1117605294328798048419215968221407134 : Int) := by exact_mod_cast hhi
  have hOv := ExpCertV.dOvP27_nonneg (t := (v : Int)) (by omega) (by omega)
  have hOv1 := ExpCertV.dOvP27_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hUn := ExpCertV.dUnP27_nonneg (t := (v : Int)) (by omega) (by omega)
  have hUn1 := ExpCertV.dUnP27_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
  rw [evalDOverP] at hOv
  rw [evalDUnderP] at hUn
  rw [hcast, evalDOverP] at hOv1
  rw [hcast, evalDUnderP] at hUn1
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by linarith [hOv],
    by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
    KpM_le_at hhi (by simp only [Kpoly, evalPoly]; norm_num), by norm_num, by norm_num⟩

theorem granPiece28 {v : Nat} (hlo : 1117605294328798048419215968221407134 ≤ v)
    (hhi : v ≤ 1157519769126255121577045109943600246) :
    PieceOK v 112268758510433036404380164835338032221 568017466591 790119500297
      124813559694107973344024788107043473917872234784266850263288391783433297169048150877731843676637794092356374813269801556437879061596983545081768014553611911044754174402003345596816607427109899526336836315448152237782498258409790180099419767003797832223547387772496458446073160169102979920523224045308674145374435976269957371998125303322935675350397184 := by
  have hvlo : (1117605294328798048419215968221407134 : Int) ≤ (v : Int) := by exact_mod_cast hlo
  have hvhi : (v : Int) ≤ (1157519769126255121577045109943600246 : Int) := by exact_mod_cast hhi
  have hOv := ExpCertV.dOvP28_nonneg (t := (v : Int)) (by omega) (by omega)
  have hOv1 := ExpCertV.dOvP28_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hUn := ExpCertV.dUnP28_nonneg (t := (v : Int)) (by omega) (by omega)
  have hUn1 := ExpCertV.dUnP28_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
  rw [evalDOverP] at hOv
  rw [evalDUnderP] at hUn
  rw [hcast, evalDOverP] at hOv1
  rw [hcast, evalDUnderP] at hUn1
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by linarith [hOv],
    by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
    KpM_le_at hhi (by simp only [Kpoly, evalPoly]; norm_num), by norm_num, by norm_num⟩

theorem granPiece29 {v : Nat} (hlo : 1157519769126255121577045109943600246 ≤ v)
    (hhi : v ≤ 1197434243923712194734874251665793358) :
    PieceOK v 114188021614114346553315397742450038434 566403276447 792331892069
      124830815183255287978488989230937912007852861268485186776484894629691039297391858695676855054821540550988755666246306222922080217137084067125422552803488226467137811892029054090053797255446672981786118025700422746450741633997798018226283790557025622187443712993615360108301740842729954061587078784532601098337144505997415684452821275968171765255782656 := by
  have hvlo : (1157519769126255121577045109943600246 : Int) ≤ (v : Int) := by exact_mod_cast hlo
  have hvhi : (v : Int) ≤ (1197434243923712194734874251665793358 : Int) := by exact_mod_cast hhi
  have hOv := ExpCertV.dOvP29_nonneg (t := (v : Int)) (by omega) (by omega)
  have hOv1 := ExpCertV.dOvP29_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hUn := ExpCertV.dUnP29_nonneg (t := (v : Int)) (by omega) (by omega)
  have hUn1 := ExpCertV.dUnP29_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
  rw [evalDOverP] at hOv
  rw [evalDUnderP] at hUn
  rw [hcast, evalDOverP] at hOv1
  rw [hcast, evalDUnderP] at hUn1
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by linarith [hOv],
    by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
    KpM_le_at hhi (by simp only [Kpoly, evalPoly]; norm_num), by norm_num, by norm_num⟩

theorem granPiece30 {v : Nat} (hlo : 1197434243923712194734874251665793358 ≤ v)
    (hhi : v ≤ 1237348718721169267892703393387986470) :
    PieceOK v 116075554802968570681645777137735089747 564820014566 794513423933
      124848072864918371545112139556887073102151888314737992274617563444406384623288591387553293909461112918653868880401685945220431541232626739228028551925510171276514210561293346598405224457657291404585578627906913330891689370353658953641245078501638134388438230868583098903895936536936896771400874658745568736075948590821250687327963145587281512196247808 := by
  have hvlo : (1197434243923712194734874251665793358 : Int) ≤ (v : Int) := by exact_mod_cast hlo
  have hvhi : (v : Int) ≤ (1237348718721169267892703393387986470 : Int) := by exact_mod_cast hhi
  have hOv := ExpCertV.dOvP30_nonneg (t := (v : Int)) (by omega) (by omega)
  have hOv1 := ExpCertV.dOvP30_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hUn := ExpCertV.dUnP30_nonneg (t := (v : Int)) (by omega) (by omega)
  have hUn1 := ExpCertV.dUnP30_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
  rw [evalDOverP] at hOv
  rw [evalDUnderP] at hUn
  rw [hcast, evalDOverP] at hOv1
  rw [hcast, evalDUnderP] at hUn1
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by linarith [hOv],
    by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
    KpM_le_at hhi (by simp only [Kpoly, evalPoly]; norm_num), by norm_num, by norm_num⟩

theorem granPiece31 {v : Nat} (hlo : 1237348718721169267892703393387986470 ≤ v)
    (hhi : v ≤ 1277263193518626341050532535110179582) :
    PieceOK v 117932881612756647068972071382077242231 563266185678 796665591163
      124865332739294834873516593328989107938627445220226415417519301074933005975501368871244922433473497551230403824606042833804361870589257536716807944070843003611163671987701060317587976677928870720398225511779857554302723969319393493947608003945282319951972195880806029003395011394810609114195299961562530515199537076949072909524942387258516947793649920 := by
  have hvlo : (1237348718721169267892703393387986470 : Int) ≤ (v : Int) := by exact_mod_cast hlo
  have hvhi : (v : Int) ≤ (1277263193518626341050532535110179582 : Int) := by exact_mod_cast hhi
  have hOv := ExpCertV.dOvP31_nonneg (t := (v : Int)) (by omega) (by omega)
  have hOv1 := ExpCertV.dOvP31_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hUn := ExpCertV.dUnP31_nonneg (t := (v : Int)) (by omega) (by omega)
  have hUn1 := ExpCertV.dUnP31_nonneg (t := (v : Int) + 1) (by omega) (by omega)
  have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
  rw [evalDOverP] at hOv
  rw [evalDUnderP] at hUn
  rw [hcast, evalDOverP] at hOv1
  rw [hcast, evalDUnderP] at hUn1
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by linarith [hOv],
    by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
    KpM_le_at hhi (by simp only [Kpoly, evalPoly]; norm_num), by norm_num, by norm_num⟩

/-- **Piece selection.** The runtime grid point lies in one of the 32 pieces, whose certified
constants apply, and the piece's `t`-cap dominates the reduced argument: `t² < T²`. -/
theorem piece_select {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    ∃ T DO DU Khi : Int,
      PieceOK (vTree x) T DO DU Khi ∧ (int256 (tTree x)) ^ 2 < T ^ 2 := by
  obtain ⟨_, hsplit⟩ := tsq_split hx hC hC0
  have hvmax := vTree_le_vmax hx hC hC0
  have hvmax' : vTree x ≤ 1277263193518626341050532535110179582 := by
    unfold ExpCertV.vmaxV at hvmax; omega
  rcases le_or_gt (vTree x) 39914474797457073157829141722193111 with h00 | h00
  · exact ⟨_, _, _, _, granPiece00 (Nat.zero_le _) h00, tsq_lt_capsq hsplit h00 (by norm_num)⟩
  rcases le_or_gt (vTree x) 79828949594914146315658283444386223 with h01 | h01
  · exact ⟨_, _, _, _, granPiece01 (Nat.le_of_lt h00) h01, tsq_lt_capsq hsplit h01 (by norm_num)⟩
  rcases le_or_gt (vTree x) 119743424392371219473487425166579335 with h02 | h02
  · exact ⟨_, _, _, _, granPiece02 (Nat.le_of_lt h01) h02, tsq_lt_capsq hsplit h02 (by norm_num)⟩
  rcases le_or_gt (vTree x) 159657899189828292631316566888772447 with h03 | h03
  · exact ⟨_, _, _, _, granPiece03 (Nat.le_of_lt h02) h03, tsq_lt_capsq hsplit h03 (by norm_num)⟩
  rcases le_or_gt (vTree x) 199572373987285365789145708610965559 with h04 | h04
  · exact ⟨_, _, _, _, granPiece04 (Nat.le_of_lt h03) h04, tsq_lt_capsq hsplit h04 (by norm_num)⟩
  rcases le_or_gt (vTree x) 239486848784742438946974850333158671 with h05 | h05
  · exact ⟨_, _, _, _, granPiece05 (Nat.le_of_lt h04) h05, tsq_lt_capsq hsplit h05 (by norm_num)⟩
  rcases le_or_gt (vTree x) 279401323582199512104803992055351783 with h06 | h06
  · exact ⟨_, _, _, _, granPiece06 (Nat.le_of_lt h05) h06, tsq_lt_capsq hsplit h06 (by norm_num)⟩
  rcases le_or_gt (vTree x) 319315798379656585262633133777544895 with h07 | h07
  · exact ⟨_, _, _, _, granPiece07 (Nat.le_of_lt h06) h07, tsq_lt_capsq hsplit h07 (by norm_num)⟩
  rcases le_or_gt (vTree x) 359230273177113658420462275499738007 with h08 | h08
  · exact ⟨_, _, _, _, granPiece08 (Nat.le_of_lt h07) h08, tsq_lt_capsq hsplit h08 (by norm_num)⟩
  rcases le_or_gt (vTree x) 399144747974570731578291417221931119 with h09 | h09
  · exact ⟨_, _, _, _, granPiece09 (Nat.le_of_lt h08) h09, tsq_lt_capsq hsplit h09 (by norm_num)⟩
  rcases le_or_gt (vTree x) 439059222772027804736120558944124231 with h10 | h10
  · exact ⟨_, _, _, _, granPiece10 (Nat.le_of_lt h09) h10, tsq_lt_capsq hsplit h10 (by norm_num)⟩
  rcases le_or_gt (vTree x) 478973697569484877893949700666317343 with h11 | h11
  · exact ⟨_, _, _, _, granPiece11 (Nat.le_of_lt h10) h11, tsq_lt_capsq hsplit h11 (by norm_num)⟩
  rcases le_or_gt (vTree x) 518888172366941951051778842388510455 with h12 | h12
  · exact ⟨_, _, _, _, granPiece12 (Nat.le_of_lt h11) h12, tsq_lt_capsq hsplit h12 (by norm_num)⟩
  rcases le_or_gt (vTree x) 558802647164399024209607984110703567 with h13 | h13
  · exact ⟨_, _, _, _, granPiece13 (Nat.le_of_lt h12) h13, tsq_lt_capsq hsplit h13 (by norm_num)⟩
  rcases le_or_gt (vTree x) 598717121961856097367437125832896679 with h14 | h14
  · exact ⟨_, _, _, _, granPiece14 (Nat.le_of_lt h13) h14, tsq_lt_capsq hsplit h14 (by norm_num)⟩
  rcases le_or_gt (vTree x) 638631596759313170525266267555089791 with h15 | h15
  · exact ⟨_, _, _, _, granPiece15 (Nat.le_of_lt h14) h15, tsq_lt_capsq hsplit h15 (by norm_num)⟩
  rcases le_or_gt (vTree x) 678546071556770243683095409277282902 with h16 | h16
  · exact ⟨_, _, _, _, granPiece16 (Nat.le_of_lt h15) h16, tsq_lt_capsq hsplit h16 (by norm_num)⟩
  rcases le_or_gt (vTree x) 718460546354227316840924550999476014 with h17 | h17
  · exact ⟨_, _, _, _, granPiece17 (Nat.le_of_lt h16) h17, tsq_lt_capsq hsplit h17 (by norm_num)⟩
  rcases le_or_gt (vTree x) 758375021151684389998753692721669126 with h18 | h18
  · exact ⟨_, _, _, _, granPiece18 (Nat.le_of_lt h17) h18, tsq_lt_capsq hsplit h18 (by norm_num)⟩
  rcases le_or_gt (vTree x) 798289495949141463156582834443862238 with h19 | h19
  · exact ⟨_, _, _, _, granPiece19 (Nat.le_of_lt h18) h19, tsq_lt_capsq hsplit h19 (by norm_num)⟩
  rcases le_or_gt (vTree x) 838203970746598536314411976166055350 with h20 | h20
  · exact ⟨_, _, _, _, granPiece20 (Nat.le_of_lt h19) h20, tsq_lt_capsq hsplit h20 (by norm_num)⟩
  rcases le_or_gt (vTree x) 878118445544055609472241117888248462 with h21 | h21
  · exact ⟨_, _, _, _, granPiece21 (Nat.le_of_lt h20) h21, tsq_lt_capsq hsplit h21 (by norm_num)⟩
  rcases le_or_gt (vTree x) 918032920341512682630070259610441574 with h22 | h22
  · exact ⟨_, _, _, _, granPiece22 (Nat.le_of_lt h21) h22, tsq_lt_capsq hsplit h22 (by norm_num)⟩
  rcases le_or_gt (vTree x) 957947395138969755787899401332634686 with h23 | h23
  · exact ⟨_, _, _, _, granPiece23 (Nat.le_of_lt h22) h23, tsq_lt_capsq hsplit h23 (by norm_num)⟩
  rcases le_or_gt (vTree x) 997861869936426828945728543054827798 with h24 | h24
  · exact ⟨_, _, _, _, granPiece24 (Nat.le_of_lt h23) h24, tsq_lt_capsq hsplit h24 (by norm_num)⟩
  rcases le_or_gt (vTree x) 1037776344733883902103557684777020910 with h25 | h25
  · exact ⟨_, _, _, _, granPiece25 (Nat.le_of_lt h24) h25, tsq_lt_capsq hsplit h25 (by norm_num)⟩
  rcases le_or_gt (vTree x) 1077690819531340975261386826499214022 with h26 | h26
  · exact ⟨_, _, _, _, granPiece26 (Nat.le_of_lt h25) h26, tsq_lt_capsq hsplit h26 (by norm_num)⟩
  rcases le_or_gt (vTree x) 1117605294328798048419215968221407134 with h27 | h27
  · exact ⟨_, _, _, _, granPiece27 (Nat.le_of_lt h26) h27, tsq_lt_capsq hsplit h27 (by norm_num)⟩
  rcases le_or_gt (vTree x) 1157519769126255121577045109943600246 with h28 | h28
  · exact ⟨_, _, _, _, granPiece28 (Nat.le_of_lt h27) h28, tsq_lt_capsq hsplit h28 (by norm_num)⟩
  rcases le_or_gt (vTree x) 1197434243923712194734874251665793358 with h29 | h29
  · exact ⟨_, _, _, _, granPiece29 (Nat.le_of_lt h28) h29, tsq_lt_capsq hsplit h29 (by norm_num)⟩
  rcases le_or_gt (vTree x) 1237348718721169267892703393387986470 with h30 | h30
  · exact ⟨_, _, _, _, granPiece30 (Nat.le_of_lt h29) h30, tsq_lt_capsq hsplit h30 (by norm_num)⟩
  exact ⟨_, _, _, _, granPiece31 (Nat.le_of_lt h30) hvmax',
    tsq_lt_capsq hsplit hvmax' (by norm_num)⟩

end ExpYul
