import ExpProof.Floor.R0Bound
import ExpProof.Floor.CapsV
import ExpProof.Cert.ExpVDOver
import ExpProof.Cert.ExpVDUnder

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
  positive, so `0 ≤ K(v) ≤ K(vmaxV)` on the grid;
* **the denominator floors** — the cover certificates `certDOver`/`certDUnder` pin
  `Ev(v)·2^110 ∓ H128·Od(v)` above explicit constants over the whole grid `[0, vmaxV + 1]`; on the
  negative half the one-grain lift `2|t|·K/(D·D′)` is additionally monotone in `|t|` (the derivative
  sign reduces to the over-half floor `Ev·2^110 − |t|·Od ≥ 0`), so the `t = −H128` floor applies.

`Floor/GranPair` packages these into the two per-side real-level budget bounds the `r0`-vs-`exp`
chains consume.
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

/-! ## The certified denominator floors over the grid -/

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
    rw [evalPoly_polyAdd, evalPoly_polySub, evalPoly_polyScale, evalPoly_polyScale,
      ← evNumV_eq_poly, ← odNumV_eq_poly, hH]
    simp only [evalPoly]
    ring
  rw [hexp] at hcert
  have hOd_nn : (0 : Int) ≤ (odNumV v : Int) := Int.natCast_nonneg _
  have htOd : t * (odNumV v : Int) ≤ 117932881612756647068972071382077242199 * (odNumV v : Int) :=
    mul_le_mul_of_nonneg_right htH hOd_nn
  unfold DENv
  linarith [hcert, htOd]

/-- The under-half denominator floor at the domain edge:
`Ev(v)·2^110 + H128·Od(v) ≥ 786932288647·2^725` on the grid, from `certDUnder`. -/
theorem D_at_H_ge_under {v : Nat} (hv : v ≤ ExpCertV.vmaxV + 1) :
    786932288647 * 2 ^ 725 ≤
      (evNumV v : Int) * 2 ^ 110 + 117932881612756647068972071382077242199 * (odNumV v : Int) := by
  have hvI : (0 : Int) ≤ (v : Int) := Int.natCast_nonneg _
  have hvI2 : (v : Int) ≤ 1277263193518626341050532535110179583 := by
    have h : v ≤ 1277263193518626341050532535110179583 := by
      unfold ExpCertV.vmaxV at hv; omega
    exact_mod_cast h
  have hcert := ExpCertV.dUnderV_nonneg hvI hvI2
  have hH : ((ExpCertV.H128 : Nat) : Int) = 117932881612756647068972071382077242199 := by
    unfold ExpCertV.H128; norm_num
  have hexp : evalPoly ExpCertV.certDUnder (v : Int) =
      (evNumV v : Int) * 2 ^ 110 + 117932881612756647068972071382077242199 * (odNumV v : Int)
        - 786932288647 * 2 ^ 725 := by
    unfold ExpCertV.certDUnder
    rw [evalPoly_polyAdd, evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyScale,
      ← evNumV_eq_poly, ← odNumV_eq_poly, hH]
    simp only [evalPoly]
    ring
  rw [hexp] at hcert
  linarith [hcert]

/-- The scaled even value dominates the whole `H128`-scaled odd value (the over floor is positive):
`H128·Od(v) ≤ Ev(v)·2^110` on the grid. -/
theorem HOd_le_Ev {v : Nat} (hv : v ≤ ExpCertV.vmaxV + 1) :
    117932881612756647068972071382077242199 * (odNumV v : Int) ≤ (evNumV v : Int) * 2 ^ 110 := by
  have h := DENv_ge_over hv (t := 117932881612756647068972071382077242199) (by norm_num) le_rfl
  unfold DENv at h
  have : (0 : Int) < 554482771859 * 2 ^ 725 := by positivity
  linarith [h, this]

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

/-- `K(vmaxV)`, the grid maximum of the step polynomial. -/
def KVMAXc : Int :=
  124865332739294834873516593328989107938627445220226415417519301074933005975501368871244922433473497551230403824606042833804361870589257536716807944070843003611163671987701060317587976677928870720398225511779857554302723969319393493947608003945282319951972195880806029003395011394810609114195299961562530515199537076949072909524942387258516947793649920

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

theorem KpM_le_KVMAX {v : Nat} (hv : v ≤ ExpCertV.vmaxV) : KpM v ≤ KVMAXc := by
  rw [KpM_eq_poly]
  have hvI : (v : Int) ≤ (1277263193518626341050532535110179582 : Int) := by
    have h : v ≤ 1277263193518626341050532535110179582 := by
      unfold ExpCertV.vmaxV at hv; omega
    exact_mod_cast h
  have h1 : evalPoly Kpoly (v : Int) ≤
      evalPoly Kpoly (1277263193518626341050532535110179582 : Int) :=
    evalPoly_mono_of_nonneg Kpoly_coeffs_nonneg (Int.natCast_nonneg _) hvI
  have h2 : evalPoly Kpoly (1277263193518626341050532535110179582 : Int) = KVMAXc := by
    simp only [Kpoly, evalPoly, KVMAXc]
    norm_num
  linarith [h1, h2 ▸ h1]

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


end ExpYul
