import ExpProof.Floor.R0Bound
import ExpProof.Floor.CapsV
import ExpProof.Floor.GranPieces
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
ê(v, t) = NUMv(v, t) / DENv(v, t),   NUMv = Ev(v)·2^111 + t·Od(v),  DENv = Ev(v)·2^111 − t·Od(v)
```

(scale `2^725 = 2^(528+87+110)`; `Ev`/`Od` are `evNumV`/`odNumV` from `Floor/R0Bound`), three facts
combine:

* **the tie** — as a function of the square argument `w`, the rational is monotone (decreasing for
  `t > 0`, increasing for `t < 0`): the cross-product `Pev(b)·Pod(a) − Pev(a)·Pod(b) ≥ 0` for
  `0 ≤ a ≤ b` holds pairwise on the coefficients, so the cert value `ê(t²)` lies between the two
  grid values `ê(v, t)` and `ê(v+1, t)`;
* **the `K` identity** — one grid step is exact algebra:
  `NUMv(v)·DENv(v+1) − NUMv(v+1)·DENv(v) = 2t·2^111·K(v)` with
  `K(v) = Od(v)·Ev(v+1) − Ev(v)·Od(v+1)`, a degree-8 polynomial in `v` with all nine coefficients
  positive, so `K` is nonnegative and nondecreasing on the grid;
* **the piecewise denominator floors** — the grid `[0, vmaxV]` is split into 32 pieces, each with a
  `t`-cap `T` (`v` in the piece forces `|t| ≤ T` through `v = ⌊t²/2^133⌋`) and cover-certified
  floors `Ev(v)·2^111 ∓ T·Od(v) ≥ D·2^725` over the piece (the step looks one cell ahead, so the
  certs run to `vhi + 1`); on the negative half the one-grain lift `2|t|·K/(D·D′)` is additionally
  monotone in `|t|` (the derivative sign reduces to the over-half floor `Ev·2^111 − |t|·Od ≥ 0`),
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

/-- The even Horner polynomial in `w` (degree 5, monic), at the cleared scale `2¹²⁰¹`. -/
def Pev : List Int :=
  [0x1385291795942d41ba5fd317688e18710 * 2 ^ 1201,
   0x93f11e650dd6c64b96ce79065cdf80f4 * 2 ^ 941,
   0x9064d9657e9a21fc16bb69331b81ae1e * 2 ^ 677,
   0x9a036222841f47c6ed6fc3f7599445 * 2 ^ 419,
   0xb9aacfacf3c10b378435f8e22adf48500e * 2 ^ 135,
   1]

/-- The odd Horner polynomial in `w` (degree 4), at the cleared scale `2¹⁰⁴⁸`. -/
def Pod : List Int :=
  [0x9c2948bcaca16a0dd2fe98bb4470c388 * 2 ^ 1048,
   0xaf566247c05753b42892f77b67a6b7c7 * 2 ^ 785,
   0xad4506af99be27419341e181693281 * 2 ^ 528,
   0xc926ddbecdeeb42e68cd16db7ed378 * 2 ^ 261,
   0xdc07aff8276bde9a361278df6a10]

/-- `evNumVPoly(t) = Pev(t²)`: the cert even polynomial is `Pev` composed with squaring. -/
theorem evNumVPoly_eq_Pev_sq (t : Int) :
    evalPoly ExpCertV.evNumVPoly t = evalPoly Pev (t ^ 2) := by
  unfold ExpCertV.evNumVPoly ExpCertV.mulT2 Pev
  simp only [evalPoly_polyAdd, evalPoly]
  ring

/-- `odNumVPoly(t) = Pod(t²)`. -/
theorem odNumVPoly_eq_Pod_sq (t : Int) :
    evalPoly ExpCertV.odNumVPoly t = evalPoly Pod (t ^ 2) := by
  unfold ExpCertV.odNumVPoly ExpCertV.mulT2 Pod
  simp only [evalPoly_polyAdd, evalPoly]
  ring

/-- `Pev(2¹³⁵·v) = evNumV(v)·2⁶⁶⁵` — the `w`-polynomial at the grid point `w = 2¹³⁵·v` recovers the
integer even-Horner accumulator (scaled). -/
theorem Pev_grid (v : Nat) : evalPoly Pev (2 ^ 135 * (v : Int)) = (evNumV v : Int) * 2 ^ 675 := by
  unfold Pev evNumV
  simp only [evalPoly]
  push_cast
  ring

/-- `Pod(2¹³⁵·v) = odNumV(v)·2⁵³²`. -/
theorem Pod_grid (v : Nat) : evalPoly Pod (2 ^ 135 * (v : Int)) = (odNumV v : Int) * 2 ^ 540 := by
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

/-- `evalPoly todNumV t = 2²⁴ · t · evalPoly odNumVPoly t`. -/
theorem evalTodNumV (t : Int) :
    evalPoly ExpCertV.todNumV t = 2 ^ 24 * (t * evalPoly ExpCertV.odNumVPoly t) := by
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

/-- `todNumV` is odd (`= 2²⁴·t·Pod(t²)`). -/
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

/-- The numerator/denominator cert-polynomial values are nonnegative / positive on `[0, H129]`. -/
theorem certNE_nonneg {t : Int} (h1 : 0 ≤ t) (h2 : t ≤ (ExpCertV.H129 : Int)) :
    0 ≤ evalPoly ExpCertV.numExpV t := ExpCertV.numExpV_nonneg' h1 h2

theorem certDE_pos {t : Int} (h1 : 0 ≤ t) (h2 : t ≤ (ExpCertV.H129 : Int)) :
    1 ≤ evalPoly ExpCertV.denExpV t := ExpCertV.denExpV_ge_one h1 h2

/-- For `t ≤ 0` with `−t ∈ [0, H129]` the cert numerator/denominator at `t` are positive. -/
theorem certNE_pos_neg_aux {t : Int} (h1 : t ≤ 0) (h2 : (-t) ≤ (ExpCertV.H129 : Int)) :
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

/-- `NUMv(v, t) = Ev(v)·2^111 + t·Od(v)` at the common scale `2^725`. -/
def NUMv (v : Nat) (t : Int) : Int := (evNumV v : Int) * 2 ^ 111 + t * (odNumV v : Int)

/-- `DENv(v, t) = Ev(v)·2^111 − t·Od(v)` at the common scale `2^725`. -/
def DENv (v : Nat) (t : Int) : Int := (evNumV v : Int) * 2 ^ 111 - t * (odNumV v : Int)

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
`certDOverP T D (v) = Ev(v)·2^111 − T·Od(v) − D·2^725`. -/
theorem evalDOverP (T D : Int) (v : Nat) :
    evalPoly (ExpCertV.certDOverP T D) (v : Int) =
      (evNumV v : Int) * 2 ^ 111 - T * (odNumV v : Int) - D * 2 ^ 725 := by
  unfold ExpCertV.certDOverP
  rw [evalPoly_polyAdd, evalPoly_polySub, evalPoly_polyScale, evalPoly_polyScale,
    ← evNumV_eq_poly, ← odNumV_eq_poly]
  simp only [evalPoly]
  ring

/-- The under-half floor shape evaluated at a grid point:
`certDUnderP T D (v) = Ev(v)·2^111 + T·Od(v) − D·2^725`. -/
theorem evalDUnderP (T D : Int) (v : Nat) :
    evalPoly (ExpCertV.certDUnderP T D) (v : Int) =
      (evNumV v : Int) * 2 ^ 111 + T * (odNumV v : Int) - D * 2 ^ 725 := by
  unfold ExpCertV.certDUnderP
  rw [evalPoly_polyAdd, evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyScale,
    ← evNumV_eq_poly, ← odNumV_eq_poly]
  simp only [evalPoly]
  ring

/-! ## The certified global denominator floor over the grid -/

/-- The over-half denominator floor: `DENv(v, t) ≥ 1108965543718·2^725` for `0 ≤ t ≤ H129` on the
grid `[0, vmaxV + 1]`, from the cover certificate `certDOver`. -/
theorem DENv_ge_over {v : Nat} {t : Int} (hv : v ≤ ExpCertV.vmaxV + 1)
    (htH : t ≤ 235865763225513294137944142764154484399) :
    1108965543718 * 2 ^ 725 ≤ DENv v t := by
  have hvI : (0 : Int) ≤ (v : Int) := Int.natCast_nonneg _
  have hvI2 : (v : Int) ≤ 1277263193518626341050532535110179583 := by
    have h : v ≤ 1277263193518626341050532535110179583 := by
      unfold ExpCertV.vmaxV at hv; omega
    exact_mod_cast h
  have hcert := ExpCertV.dOverV_nonneg hvI hvI2
  have hH : ((ExpCertV.H129 : Nat) : Int) = 235865763225513294137944142764154484399 := by
    unfold ExpCertV.H129; norm_num
  have hexp : evalPoly ExpCertV.certDOver (v : Int) =
      (evNumV v : Int) * 2 ^ 111 - 235865763225513294137944142764154484399 * (odNumV v : Int)
        - 1108965543718 * 2 ^ 725 := by
    unfold ExpCertV.certDOver
    rw [evalDOverP, hH]
  rw [hexp] at hcert
  have hOd_nn : (0 : Int) ≤ (odNumV v : Int) := Int.natCast_nonneg _
  have htOd : t * (odNumV v : Int) ≤ 235865763225513294137944142764154484399 * (odNumV v : Int) :=
    mul_le_mul_of_nonneg_right htH hOd_nn
  unfold DENv
  linarith [hcert, htOd]

/-- The scaled even value alone clears the over floor. -/
theorem Ev_scaled_ge {v : Nat} (hv : v ≤ ExpCertV.vmaxV + 1) :
    1108965543718 * 2 ^ 725 ≤ (evNumV v : Int) * 2 ^ 111 := by
  have h := DENv_ge_over hv (t := 0) (by norm_num)
  unfold DENv at h
  linarith [h]

/-- On the nonpositive half the denominator is bounded below by the scaled even value. -/
theorem DENv_ge_neg {v : Nat} {t : Int} (hv : v ≤ ExpCertV.vmaxV + 1) (htnp : t ≤ 0) :
    1108965543718 * 2 ^ 725 ≤ DENv v t := by
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
  124314103365382948540818484389625511203399177432453098518846457498424611868718936788294664267508136808084138787208378562630796118598660218488733713108899806680606730056981253470814633029881113238182689516541100092823765499012530288921867233641123804341166654951569367737662827074930978395230903701562235931446223508713572252330288363487742122325442560,
  430693347524554794343417296651509269546471125888783932883213067852427976792830819506154685161681309308421934362957503263238172463597752166322997479007299450300268826360292259046832109312788166610911298114935367705253725341124202899493244774245413341803253389569796633472510432176301708723695054007939636706410496,
  686241798384522667273603851831993255743976479454734108933770660426843907940620907261663442100255837834877719028054685866583528534712652427934848500737241369416125752426578930665894337646314144065132479326417994932879796724838817164446315062770611047713370345511153441964032,
  516930441971039446793370708722985432068498632768666228915957515544832603080870750486884619259761770023519567422223894490006504385081487220640805923736478421507588209150278363775126877525492198473202648229917180375976504407544406474752,
  204444652500469654421705147173882406799000050958223443836506004238012414689803007858846783088053803154580895166740525311062105616502632116907067400682504133082049679601164456670000760158882327056,
  41949223685511975480580776931803214095183058807997891029056426006309309876979761480785120698138076232828037019511000124510823093705593692832111535106926656,
  4316880982720124500406644109790128668229286147770009636876004160726008360785062858879885810687133295792221148970080,
  177702252311948919910468951720197103269093626476374115210152794580320102464,
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
theorem KpM_le_at {v : Nat} {vhi : Int} (hv : (v : Int) ≤ vhi) : KpM v ≤ evalPoly Kpoly vhi := by
  rw [KpM_eq_poly]
  exact evalPoly_mono_of_nonneg Kpoly_coeffs_nonneg (Int.natCast_nonneg _) hv

/-- **The discrete quotient identity**: one grid step of the aligned rational is exact algebra. -/
theorem step_identity (v : Nat) (t : Int) :
    NUMv v t * DENv (v + 1) t - NUMv (v + 1) t * DENv v t = 2 * t * 2 ^ 111 * KpM v := by
  unfold NUMv DENv KpM
  ring

/-! ## Grid placement of the exact square -/

/-- The squared reduced argument splits as `t² = 2¹³⁵·vTree x + r` with `0 ≤ r < 2¹³⁵`. -/
theorem tsq_split_wide {x : Nat} (hx : x < 2 ^ 256) (hW : WideRegion x) :
    2 ^ 135 * (vTree x : Int) ≤ (int256 (tTree x)) ^ 2 ∧
      (int256 (tTree x)) ^ 2 < 2 ^ 135 * (vTree x : Int) + 2 ^ 135 := by
  obtain ⟨hveq, _⟩ := vTree_eq_wide hx hW
  have hsqnn : (0 : Int) ≤ (int256 (tTree x)) ^ 2 := sq_nonneg _
  have hdm := Int.ediv_add_emod ((int256 (tTree x)) ^ 2) (2 ^ 135)
  have hmod_lt := Int.emod_lt_of_pos ((int256 (tTree x)) ^ 2) (by norm_num : (0:Int) < 2 ^ 135)
  have hmod_nn := Int.emod_nonneg ((int256 (tTree x)) ^ 2) (by norm_num : (2:Int) ^ 135 ≠ 0)
  rw [hveq]
  constructor
  · nlinarith [hdm, hmod_nn]
  · nlinarith [hdm, hmod_lt]

theorem tsq_split {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    2 ^ 135 * (vTree x : Int) ≤ (int256 (tTree x)) ^ 2 ∧
      (int256 (tTree x)) ^ 2 < 2 ^ 135 * (vTree x : Int) + 2 ^ 135 :=
  tsq_split_wide hx (wideRegion_of_wad hC hC0)

/-- The grid index never leaves the certified domain: `vTree x ≤ vmaxV`. -/
theorem vTree_le_vmax_wide {x : Nat} (hx : x < 2 ^ 256) (hW : WideRegion x) :
    vTree x ≤ ExpCertV.vmaxV := by
  obtain ⟨hlo, _⟩ := tsq_split_wide hx hW
  obtain ⟨htlo, hthi⟩ := tTree_in_cert_domain_wide hx hW
  have ht2 : (int256 (tTree x)) ^ 2 ≤ 235865763225513294137944142764154484399 ^ 2 := by
    nlinarith [htlo, hthi]
  have hlt : 2 ^ 135 * (vTree x : Int) <
      2 ^ 135 * (1277263193518626341050532535110179583 : Int) := by
    calc 2 ^ 135 * (vTree x : Int) ≤ (int256 (tTree x)) ^ 2 := hlo
      _ ≤ 235865763225513294137944142764154484399 ^ 2 := ht2
      _ < 2 ^ 135 * 1277263193518626341050532535110179583 := by norm_num
  have hvI : (vTree x : Int) < 1277263193518626341050532535110179583 :=
    lt_of_mul_lt_mul_left hlt (by positivity)
  have hvN : vTree x < 1277263193518626341050532535110179583 := by exact_mod_cast hvI
  unfold ExpCertV.vmaxV
  omega

theorem vTree_le_vmax {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    vTree x ≤ ExpCertV.vmaxV :=
  vTree_le_vmax_wide hx (wideRegion_of_wad hC hC0)

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
      (((0x93f11e650dd6c64b96ce79065cdf80f4 * 2 ^ 941) * (0x9c2948bcaca16a0dd2fe98bb4470c388 * 2 ^ 1048) - (0x1385291795942d41ba5fd317688e18710 * 2 ^ 1201) * (0xaf566247c05753b42892f77b67a6b7c7 * 2 ^ 785) : Int)) * (a ^ 0 * b ^ 1 - a ^ 1 * b ^ 0) +
      (((0x9064d9657e9a21fc16bb69331b81ae1e * 2 ^ 677) * (0x9c2948bcaca16a0dd2fe98bb4470c388 * 2 ^ 1048) - (0x1385291795942d41ba5fd317688e18710 * 2 ^ 1201) * (0xad4506af99be27419341e181693281 * 2 ^ 528) : Int)) * (a ^ 0 * b ^ 2 - a ^ 2 * b ^ 0) +
      (((0x9064d9657e9a21fc16bb69331b81ae1e * 2 ^ 677) * (0xaf566247c05753b42892f77b67a6b7c7 * 2 ^ 785) - (0x93f11e650dd6c64b96ce79065cdf80f4 * 2 ^ 941) * (0xad4506af99be27419341e181693281 * 2 ^ 528) : Int)) * (a ^ 1 * b ^ 2 - a ^ 2 * b ^ 1) +
      (((0x9a036222841f47c6ed6fc3f7599445 * 2 ^ 419) * (0x9c2948bcaca16a0dd2fe98bb4470c388 * 2 ^ 1048) - (0x1385291795942d41ba5fd317688e18710 * 2 ^ 1201) * (0xc926ddbecdeeb42e68cd16db7ed378 * 2 ^ 261) : Int)) * (a ^ 0 * b ^ 3 - a ^ 3 * b ^ 0) +
      (((0x9a036222841f47c6ed6fc3f7599445 * 2 ^ 419) * (0xaf566247c05753b42892f77b67a6b7c7 * 2 ^ 785) - (0x93f11e650dd6c64b96ce79065cdf80f4 * 2 ^ 941) * (0xc926ddbecdeeb42e68cd16db7ed378 * 2 ^ 261) : Int)) * (a ^ 1 * b ^ 3 - a ^ 3 * b ^ 1) +
      (((0x9a036222841f47c6ed6fc3f7599445 * 2 ^ 419) * (0xad4506af99be27419341e181693281 * 2 ^ 528) - (0x9064d9657e9a21fc16bb69331b81ae1e * 2 ^ 677) * (0xc926ddbecdeeb42e68cd16db7ed378 * 2 ^ 261) : Int)) * (a ^ 2 * b ^ 3 - a ^ 3 * b ^ 2) +
      (((0xb9aacfacf3c10b378435f8e22adf48500e * 2 ^ 135) * (0x9c2948bcaca16a0dd2fe98bb4470c388 * 2 ^ 1048) - (0x1385291795942d41ba5fd317688e18710 * 2 ^ 1201) * (0xdc07aff8276bde9a361278df6a10) : Int)) * (a ^ 0 * b ^ 4 - a ^ 4 * b ^ 0) +
      (((0xb9aacfacf3c10b378435f8e22adf48500e * 2 ^ 135) * (0xaf566247c05753b42892f77b67a6b7c7 * 2 ^ 785) - (0x93f11e650dd6c64b96ce79065cdf80f4 * 2 ^ 941) * (0xdc07aff8276bde9a361278df6a10) : Int)) * (a ^ 1 * b ^ 4 - a ^ 4 * b ^ 1) +
      (((0xb9aacfacf3c10b378435f8e22adf48500e * 2 ^ 135) * (0xad4506af99be27419341e181693281 * 2 ^ 528) - (0x9064d9657e9a21fc16bb69331b81ae1e * 2 ^ 677) * (0xdc07aff8276bde9a361278df6a10) : Int)) * (a ^ 2 * b ^ 4 - a ^ 4 * b ^ 2) +
      (((0xb9aacfacf3c10b378435f8e22adf48500e * 2 ^ 135) * (0xc926ddbecdeeb42e68cd16db7ed378 * 2 ^ 261) - (0x9a036222841f47c6ed6fc3f7599445 * 2 ^ 419) * (0xdc07aff8276bde9a361278df6a10) : Int)) * (a ^ 3 * b ^ 4 - a ^ 4 * b ^ 3) +
      (((1) * (0x9c2948bcaca16a0dd2fe98bb4470c388 * 2 ^ 1048) - (0x1385291795942d41ba5fd317688e18710 * 2 ^ 1201) * (0) : Int)) * (a ^ 0 * b ^ 5 - a ^ 5 * b ^ 0) +
      (((1) * (0xaf566247c05753b42892f77b67a6b7c7 * 2 ^ 785) - (0x93f11e650dd6c64b96ce79065cdf80f4 * 2 ^ 941) * (0) : Int)) * (a ^ 1 * b ^ 5 - a ^ 5 * b ^ 1) +
      (((1) * (0xad4506af99be27419341e181693281 * 2 ^ 528) - (0x9064d9657e9a21fc16bb69331b81ae1e * 2 ^ 677) * (0) : Int)) * (a ^ 2 * b ^ 5 - a ^ 5 * b ^ 2) +
      (((1) * (0xc926ddbecdeeb42e68cd16db7ed378 * 2 ^ 261) - (0x9a036222841f47c6ed6fc3f7599445 * 2 ^ 419) * (0) : Int)) * (a ^ 3 * b ^ 5 - a ^ 5 * b ^ 3) +
      (((1) * (0xdc07aff8276bde9a361278df6a10) - (0xb9aacfacf3c10b378435f8e22adf48500e * 2 ^ 135) * (0) : Int)) * (a ^ 4 * b ^ 5 - a ^ 5 * b ^ 4) := by
    simp only [Pev, Pod, evalPoly]
    ring
  have h10 : (0:Int) ≤ (((0x93f11e650dd6c64b96ce79065cdf80f4 * 2 ^ 941) * (0x9c2948bcaca16a0dd2fe98bb4470c388 * 2 ^ 1048) - (0x1385291795942d41ba5fd317688e18710 * 2 ^ 1201) * (0xaf566247c05753b42892f77b67a6b7c7 * 2 ^ 785) : Int)) * (a ^ 0 * b ^ 1 - a ^ 1 * b ^ 0) :=
    mul_nonneg (by norm_num) (by have := pow_pair_mono ha hab 0 1; simpa using this)
  have h20 : (0:Int) ≤ (((0x9064d9657e9a21fc16bb69331b81ae1e * 2 ^ 677) * (0x9c2948bcaca16a0dd2fe98bb4470c388 * 2 ^ 1048) - (0x1385291795942d41ba5fd317688e18710 * 2 ^ 1201) * (0xad4506af99be27419341e181693281 * 2 ^ 528) : Int)) * (a ^ 0 * b ^ 2 - a ^ 2 * b ^ 0) :=
    mul_nonneg (by norm_num) (by have := pow_pair_mono ha hab 0 2; simpa using this)
  have h21 : (0:Int) ≤ (((0x9064d9657e9a21fc16bb69331b81ae1e * 2 ^ 677) * (0xaf566247c05753b42892f77b67a6b7c7 * 2 ^ 785) - (0x93f11e650dd6c64b96ce79065cdf80f4 * 2 ^ 941) * (0xad4506af99be27419341e181693281 * 2 ^ 528) : Int)) * (a ^ 1 * b ^ 2 - a ^ 2 * b ^ 1) :=
    mul_nonneg (by norm_num) (by have := pow_pair_mono ha hab 1 1; simpa using this)
  have h30 : (0:Int) ≤ (((0x9a036222841f47c6ed6fc3f7599445 * 2 ^ 419) * (0x9c2948bcaca16a0dd2fe98bb4470c388 * 2 ^ 1048) - (0x1385291795942d41ba5fd317688e18710 * 2 ^ 1201) * (0xc926ddbecdeeb42e68cd16db7ed378 * 2 ^ 261) : Int)) * (a ^ 0 * b ^ 3 - a ^ 3 * b ^ 0) :=
    mul_nonneg (by norm_num) (by have := pow_pair_mono ha hab 0 3; simpa using this)
  have h31 : (0:Int) ≤ (((0x9a036222841f47c6ed6fc3f7599445 * 2 ^ 419) * (0xaf566247c05753b42892f77b67a6b7c7 * 2 ^ 785) - (0x93f11e650dd6c64b96ce79065cdf80f4 * 2 ^ 941) * (0xc926ddbecdeeb42e68cd16db7ed378 * 2 ^ 261) : Int)) * (a ^ 1 * b ^ 3 - a ^ 3 * b ^ 1) :=
    mul_nonneg (by norm_num) (by have := pow_pair_mono ha hab 1 2; simpa using this)
  have h32 : (0:Int) ≤ (((0x9a036222841f47c6ed6fc3f7599445 * 2 ^ 419) * (0xad4506af99be27419341e181693281 * 2 ^ 528) - (0x9064d9657e9a21fc16bb69331b81ae1e * 2 ^ 677) * (0xc926ddbecdeeb42e68cd16db7ed378 * 2 ^ 261) : Int)) * (a ^ 2 * b ^ 3 - a ^ 3 * b ^ 2) :=
    mul_nonneg (by norm_num) (by have := pow_pair_mono ha hab 2 1; simpa using this)
  have h40 : (0:Int) ≤ (((0xb9aacfacf3c10b378435f8e22adf48500e * 2 ^ 135) * (0x9c2948bcaca16a0dd2fe98bb4470c388 * 2 ^ 1048) - (0x1385291795942d41ba5fd317688e18710 * 2 ^ 1201) * (0xdc07aff8276bde9a361278df6a10) : Int)) * (a ^ 0 * b ^ 4 - a ^ 4 * b ^ 0) :=
    mul_nonneg (by norm_num) (by have := pow_pair_mono ha hab 0 4; simpa using this)
  have h41 : (0:Int) ≤ (((0xb9aacfacf3c10b378435f8e22adf48500e * 2 ^ 135) * (0xaf566247c05753b42892f77b67a6b7c7 * 2 ^ 785) - (0x93f11e650dd6c64b96ce79065cdf80f4 * 2 ^ 941) * (0xdc07aff8276bde9a361278df6a10) : Int)) * (a ^ 1 * b ^ 4 - a ^ 4 * b ^ 1) :=
    mul_nonneg (by norm_num) (by have := pow_pair_mono ha hab 1 3; simpa using this)
  have h42 : (0:Int) ≤ (((0xb9aacfacf3c10b378435f8e22adf48500e * 2 ^ 135) * (0xad4506af99be27419341e181693281 * 2 ^ 528) - (0x9064d9657e9a21fc16bb69331b81ae1e * 2 ^ 677) * (0xdc07aff8276bde9a361278df6a10) : Int)) * (a ^ 2 * b ^ 4 - a ^ 4 * b ^ 2) :=
    mul_nonneg (by norm_num) (by have := pow_pair_mono ha hab 2 2; simpa using this)
  have h43 : (0:Int) ≤ (((0xb9aacfacf3c10b378435f8e22adf48500e * 2 ^ 135) * (0xc926ddbecdeeb42e68cd16db7ed378 * 2 ^ 261) - (0x9a036222841f47c6ed6fc3f7599445 * 2 ^ 419) * (0xdc07aff8276bde9a361278df6a10) : Int)) * (a ^ 3 * b ^ 4 - a ^ 4 * b ^ 3) :=
    mul_nonneg (by norm_num) (by have := pow_pair_mono ha hab 3 1; simpa using this)
  have h50 : (0:Int) ≤ (((1) * (0x9c2948bcaca16a0dd2fe98bb4470c388 * 2 ^ 1048) - (0x1385291795942d41ba5fd317688e18710 * 2 ^ 1201) * (0) : Int)) * (a ^ 0 * b ^ 5 - a ^ 5 * b ^ 0) :=
    mul_nonneg (by norm_num) (by have := pow_pair_mono ha hab 0 5; simpa using this)
  have h51 : (0:Int) ≤ (((1) * (0xaf566247c05753b42892f77b67a6b7c7 * 2 ^ 785) - (0x93f11e650dd6c64b96ce79065cdf80f4 * 2 ^ 941) * (0) : Int)) * (a ^ 1 * b ^ 5 - a ^ 5 * b ^ 1) :=
    mul_nonneg (by norm_num) (by have := pow_pair_mono ha hab 1 4; simpa using this)
  have h52 : (0:Int) ≤ (((1) * (0xad4506af99be27419341e181693281 * 2 ^ 528) - (0x9064d9657e9a21fc16bb69331b81ae1e * 2 ^ 677) * (0) : Int)) * (a ^ 2 * b ^ 5 - a ^ 5 * b ^ 2) :=
    mul_nonneg (by norm_num) (by have := pow_pair_mono ha hab 2 3; simpa using this)
  have h53 : (0:Int) ≤ (((1) * (0xc926ddbecdeeb42e68cd16db7ed378 * 2 ^ 261) - (0x9a036222841f47c6ed6fc3f7599445 * 2 ^ 419) * (0) : Int)) * (a ^ 3 * b ^ 5 - a ^ 5 * b ^ 3) :=
    mul_nonneg (by norm_num) (by have := pow_pair_mono ha hab 3 2; simpa using this)
  have h54 : (0:Int) ≤ (((1) * (0xdc07aff8276bde9a361278df6a10) - (0xb9aacfacf3c10b378435f8e22adf48500e * 2 ^ 135) * (0) : Int)) * (a ^ 4 * b ^ 5 - a ^ 5 * b ^ 4) :=
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
    evalPoly Pev (2 ^ 135 * (v : Int)) + 2 ^ 24 * t * evalPoly Pod (2 ^ 135 * (v : Int)) =
      2 ^ 564 * NUMv v t := by
  rw [Pev_grid, Pod_grid]
  unfold NUMv
  ring

theorem grid_den_eq (v : Nat) (t : Int) :
    evalPoly Pev (2 ^ 135 * (v : Int)) - 2 ^ 24 * t * evalPoly Pod (2 ^ 135 * (v : Int)) =
      2 ^ 564 * DENv v t := by
  rw [Pev_grid, Pod_grid]
  unfold DENv
  ring

/-- The cert polynomials at `t` are the `w`-polynomials at the exact square. -/
theorem NE_eq_w (t : Int) :
    evalPoly ExpCertV.numExpV t = evalPoly Pev (t ^ 2) + 2 ^ 24 * t * evalPoly Pod (t ^ 2) := by
  rw [evalNumExpV, evalTodNumV, ← evNumVPoly_eq_Pev_sq, ← odNumVPoly_eq_Pod_sq]
  ring

theorem DE_eq_w (t : Int) :
    evalPoly ExpCertV.denExpV t = evalPoly Pev (t ^ 2) - 2 ^ 24 * t * evalPoly Pod (t ^ 2) := by
  rw [evalDenExpV, evalTodNumV, ← evNumVPoly_eq_Pev_sq, ← odNumVPoly_eq_Pod_sq]
  ring

/-- **The tie at the runtime point (nonnegative half)**: the cert rational at `t²` lies between the
two grid values, as cross products. -/
theorem tie_over_wide {x : Nat} (hx : x < 2 ^ 256) (hW : WideRegion x)
    (htnn : 0 ≤ int256 (tTree x)) :
    evalPoly ExpCertV.numExpV (int256 (tTree x)) * DENv (vTree x) (int256 (tTree x)) ≤
        NUMv (vTree x) (int256 (tTree x)) * evalPoly ExpCertV.denExpV (int256 (tTree x)) ∧
      NUMv (vTree x + 1) (int256 (tTree x)) * evalPoly ExpCertV.denExpV (int256 (tTree x)) ≤
        evalPoly ExpCertV.numExpV (int256 (tTree x)) * DENv (vTree x + 1) (int256 (tTree x)) := by
  obtain ⟨haw, hwb⟩ := tsq_split_wide hx hW
  set t := int256 (tTree x) with htdef
  set v := vTree x with hvdef
  have hs : (0:Int) ≤ 2 ^ 24 * t := by positivity
  have ha : (0:Int) ≤ 2 ^ 135 * (v : Int) := by positivity
  have hw : (0:Int) ≤ t ^ 2 := sq_nonneg _
  have hb1 : t ^ 2 ≤ 2 ^ 135 * ((v + 1 : Nat) : Int) := by push_cast; linarith [hwb]
  have hp555 : (0:Int) < 2 ^ 564 := by positivity
  constructor
  · -- a := grid v, b := t²: NE·(2^555·DENv v) ≤ (2^555·NUMv v)·DE
    have h1 := tie_cross (a := 2 ^ 135 * (v : Int)) (b := t ^ 2) (2 ^ 24 * t) ha haw hs
    rw [grid_num_eq, grid_den_eq, ← NE_eq_w, ← DE_eq_w] at h1
    -- h1 : NE·(2^555·DENv v t) ≤ (2^555·NUMv v t)·DE
    have h2 : 2 ^ 564 * (evalPoly ExpCertV.numExpV t * DENv v t) ≤
        2 ^ 564 * (NUMv v t * evalPoly ExpCertV.denExpV t) := by
      calc 2 ^ 564 * (evalPoly ExpCertV.numExpV t * DENv v t)
          = evalPoly ExpCertV.numExpV t * (2 ^ 564 * DENv v t) := by ring
        _ ≤ 2 ^ 564 * NUMv v t * evalPoly ExpCertV.denExpV t := h1
        _ = 2 ^ 564 * (NUMv v t * evalPoly ExpCertV.denExpV t) := by ring
    exact le_of_mul_le_mul_left h2 hp555
  · -- a := t², b := grid (v+1): (2^555·NUMv (v+1))·DE ≤ NE·(2^555·DENv (v+1))
    have h1 := tie_cross (a := t ^ 2) (b := 2 ^ 135 * ((v + 1 : Nat) : Int)) (2 ^ 24 * t) hw hb1 hs
    rw [grid_num_eq, grid_den_eq, ← NE_eq_w, ← DE_eq_w] at h1
    -- h1 : (2^555·NUMv (v+1) t)·DE ≤ NE·(2^555·DENv (v+1) t)
    have h2 : 2 ^ 564 * (NUMv (v + 1) t * evalPoly ExpCertV.denExpV t) ≤
        2 ^ 564 * (evalPoly ExpCertV.numExpV t * DENv (v + 1) t) := by
      calc 2 ^ 564 * (NUMv (v + 1) t * evalPoly ExpCertV.denExpV t)
          = 2 ^ 564 * NUMv (v + 1) t * evalPoly ExpCertV.denExpV t := by ring
        _ ≤ evalPoly ExpCertV.numExpV t * (2 ^ 564 * DENv (v + 1) t) := h1
        _ = 2 ^ 564 * (evalPoly ExpCertV.numExpV t * DENv (v + 1) t) := by ring
    exact le_of_mul_le_mul_left h2 hp555

theorem tie_over {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htnn : 0 ≤ int256 (tTree x)) :
    evalPoly ExpCertV.numExpV (int256 (tTree x)) * DENv (vTree x) (int256 (tTree x)) ≤
        NUMv (vTree x) (int256 (tTree x)) * evalPoly ExpCertV.denExpV (int256 (tTree x)) ∧
      NUMv (vTree x + 1) (int256 (tTree x)) * evalPoly ExpCertV.denExpV (int256 (tTree x)) ≤
        evalPoly ExpCertV.numExpV (int256 (tTree x)) * DENv (vTree x + 1) (int256 (tTree x)) :=
  tie_over_wide hx (wideRegion_of_wad hC hC0) htnn

/-- **The tie at the runtime point (nonpositive half)**: the directions flip. -/
theorem tie_under_wide {x : Nat} (hx : x < 2 ^ 256) (hW : WideRegion x)
    (htnp : int256 (tTree x) ≤ 0) :
    NUMv (vTree x) (int256 (tTree x)) * evalPoly ExpCertV.denExpV (int256 (tTree x)) ≤
        evalPoly ExpCertV.numExpV (int256 (tTree x)) * DENv (vTree x) (int256 (tTree x)) ∧
      evalPoly ExpCertV.numExpV (int256 (tTree x)) * DENv (vTree x + 1) (int256 (tTree x)) ≤
        NUMv (vTree x + 1) (int256 (tTree x)) * evalPoly ExpCertV.denExpV (int256 (tTree x)) := by
  obtain ⟨haw, hwb⟩ := tsq_split_wide hx hW
  set t := int256 (tTree x) with htdef
  set v := vTree x with hvdef
  have hs : (0:Int) ≤ 2 ^ 24 * (-t) := by
    have : (0:Int) ≤ -t := by linarith [htnp]
    positivity
  have ha : (0:Int) ≤ 2 ^ 135 * (v : Int) := by positivity
  have hw : (0:Int) ≤ t ^ 2 := sq_nonneg _
  have hb1 : t ^ 2 ≤ 2 ^ 135 * ((v + 1 : Nat) : Int) := by push_cast; linarith [hwb]
  have hp555 : (0:Int) < 2 ^ 564 := by positivity
  -- with σ = −s ≥ 0, the `N`/`D` roles swap: Pev + σ·Pod = DENv-form, Pev − σ·Pod = NUMv-form
  constructor
  · have h1 := tie_cross (a := 2 ^ 135 * (v : Int)) (b := t ^ 2) (2 ^ 24 * (-t)) ha haw hs
    -- rewrite σ-forms into t-forms: Pev x + 2^23·(−t)·Pod x = Pev x − 2^23·t·Pod x
    have e1 : evalPoly Pev (t ^ 2) + 2 ^ 24 * (-t) * evalPoly Pod (t ^ 2) =
        evalPoly ExpCertV.denExpV t := by rw [DE_eq_w]; ring
    have e2 : evalPoly Pev (2 ^ 135 * (v : Int)) - 2 ^ 24 * (-t) * evalPoly Pod (2 ^ 135 * (v : Int)) =
        2 ^ 564 * NUMv v t := by rw [← grid_num_eq]; ring
    have e3 : evalPoly Pev (2 ^ 135 * (v : Int)) + 2 ^ 24 * (-t) * evalPoly Pod (2 ^ 135 * (v : Int)) =
        2 ^ 564 * DENv v t := by rw [← grid_den_eq]; ring
    have e4 : evalPoly Pev (t ^ 2) - 2 ^ 24 * (-t) * evalPoly Pod (t ^ 2) =
        evalPoly ExpCertV.numExpV t := by rw [NE_eq_w]; ring
    rw [e1, e2, e3, e4] at h1
    -- h1 : DE·(2^555·NUMv v t) ≤ (2^555·DENv v t)·NE
    have h2 : 2 ^ 564 * (NUMv v t * evalPoly ExpCertV.denExpV t) ≤
        2 ^ 564 * (evalPoly ExpCertV.numExpV t * DENv v t) := by
      calc 2 ^ 564 * (NUMv v t * evalPoly ExpCertV.denExpV t)
          = evalPoly ExpCertV.denExpV t * (2 ^ 564 * NUMv v t) := by ring
        _ ≤ 2 ^ 564 * DENv v t * evalPoly ExpCertV.numExpV t := h1
        _ = 2 ^ 564 * (evalPoly ExpCertV.numExpV t * DENv v t) := by ring
    exact le_of_mul_le_mul_left h2 hp555
  · have h1 := tie_cross (a := t ^ 2) (b := 2 ^ 135 * ((v + 1 : Nat) : Int)) (2 ^ 24 * (-t)) hw hb1 hs
    have e1 : evalPoly Pev (2 ^ 135 * ((v + 1 : Nat) : Int)) +
        2 ^ 24 * (-t) * evalPoly Pod (2 ^ 135 * ((v + 1 : Nat) : Int)) =
        2 ^ 564 * DENv (v + 1) t := by rw [← grid_den_eq]; ring
    have e2 : evalPoly Pev (t ^ 2) - 2 ^ 24 * (-t) * evalPoly Pod (t ^ 2) =
        evalPoly ExpCertV.numExpV t := by rw [NE_eq_w]; ring
    have e3 : evalPoly Pev (t ^ 2) + 2 ^ 24 * (-t) * evalPoly Pod (t ^ 2) =
        evalPoly ExpCertV.denExpV t := by rw [DE_eq_w]; ring
    have e4 : evalPoly Pev (2 ^ 135 * ((v + 1 : Nat) : Int)) -
        2 ^ 24 * (-t) * evalPoly Pod (2 ^ 135 * ((v + 1 : Nat) : Int)) =
        2 ^ 564 * NUMv (v + 1) t := by rw [← grid_num_eq]; ring
    rw [e1, e2, e3, e4] at h1
    -- h1 : (2^555·DENv (v+1) t)·NE ≤ DE·(2^555·NUMv (v+1) t)
    have h2 : 2 ^ 564 * (evalPoly ExpCertV.numExpV t * DENv (v + 1) t) ≤
        2 ^ 564 * (NUMv (v + 1) t * evalPoly ExpCertV.denExpV t) := by
      calc 2 ^ 564 * (evalPoly ExpCertV.numExpV t * DENv (v + 1) t)
          = 2 ^ 564 * DENv (v + 1) t * evalPoly ExpCertV.numExpV t := by ring
        _ ≤ evalPoly ExpCertV.denExpV t * (2 ^ 564 * NUMv (v + 1) t) := h1
        _ = 2 ^ 564 * (NUMv (v + 1) t * evalPoly ExpCertV.denExpV t) := by ring
    exact le_of_mul_le_mul_left h2 hp555

theorem tie_under {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htnp : int256 (tTree x) ≤ 0) :
    NUMv (vTree x) (int256 (tTree x)) * evalPoly ExpCertV.denExpV (int256 (tTree x)) ≤
        evalPoly ExpCertV.numExpV (int256 (tTree x)) * DENv (vTree x) (int256 (tTree x)) ∧
      evalPoly ExpCertV.numExpV (int256 (tTree x)) * DENv (vTree x + 1) (int256 (tTree x)) ≤
        NUMv (vTree x + 1) (int256 (tTree x)) * evalPoly ExpCertV.denExpV (int256 (tTree x)) :=
  tie_under_wide hx (wideRegion_of_wad hC hC0) htnp

/-! ## The 32-piece granularity certificate -/

/-- The per-piece granularity facts at a grid point `v`: positivity of the floors and the cap,
the certified over/under denominator floors at both cells `v` and `v + 1`, the `K` cap, and the
certified budget inequalities of the piece against the two exported envelopes
(`3290521163436398582/10¹⁹` over, `1644901622230542074/10¹⁹` under, `Mp`-folded). -/
def PieceOK (v : Nat) (T DO DU Khi : Int) : Prop :=
  0 < DO ∧ 0 < DU ∧ 0 ≤ Khi ∧ 0 ≤ T ∧
  DO * 2 ^ 725 ≤ (evNumV v : Int) * 2 ^ 111 - T * (odNumV v : Int) ∧
  DO * 2 ^ 725 ≤ (evNumV (v + 1) : Int) * 2 ^ 111 - T * (odNumV (v + 1) : Int) ∧
  DU * 2 ^ 725 ≤ (evNumV v : Int) * 2 ^ 111 + T * (odNumV v : Int) ∧
  DU * 2 ^ 725 ≤ (evNumV (v + 1) : Int) * 2 ^ 111 + T * (odNumV (v + 1) : Int) ∧
  KpM v ≤ Khi ∧
  2 * T * 2 ^ 111 * Khi * 2 ^ 126 * 10000000000000000000 ≤
    3290521163436398582 * ((DO * 2 ^ 725) * (DO * 2 ^ 725)) ∧
  2 ^ 126 * 2 ^ 131 * (2 * T * 2 ^ 111 * Khi) * 10000000000000000000 ≤
    1644901622230542074 * ((2 ^ 131 - 1) * ((DU * 2 ^ 725) * (DU * 2 ^ 725)))

/-- The piece cap dominates the square: from the split `t² < 2^133·v + 2^133`, membership
`v ≤ vhi`, and the cap fact `2^133·(vhi + 1) ≤ T²`. -/
theorem tsq_lt_capsq {t : Int} {v : Nat} (hsplit : t ^ 2 < 2 ^ 135 * (v : Int) + 2 ^ 135)
    {vhi : Int} (hv : (v : Int) ≤ vhi) {T : Int}
    (hT : 2 ^ 135 * vhi + 2 ^ 135 ≤ T ^ 2) :
    t ^ 2 < T ^ 2 := by
  nlinarith [hsplit, hT, hv]

/-- The per-piece granularity facts for one entry `(vlo, vhi, T, DO, DU)` of the shared table
`ExpCertV.granPieces`, with the `K` cap at the piece's upper edge. -/
def PieceHolds : Int × Int × Int × Int × Int → Prop
  | (vlo, vhi, T, DO, DU) =>
    ∀ v : Nat, vlo ≤ (v : Int) → (v : Int) ≤ vhi →
      PieceOK v T DO DU (evalPoly Kpoly vhi)

/-- Each piece's `t`-cap dominates its `v`-range: `(vhi + 1)·2^133 ≤ T²`. -/
theorem granPieces_caps :
    ∀ p ∈ ExpCertV.granPieces, 2 ^ 135 * p.2.1 + 2 ^ 135 ≤ p.2.2.1 ^ 2 := by
  decide +kernel

/-- `piecesCover lo hi ps`: the pieces' closed `v`-ranges, in table order, cover `[lo, hi]`. -/
def piecesCover (lo hi : Int) : List (Int × Int × Int × Int × Int) → Bool
  | [] => false
  | p :: rest => decide (p.1 ≤ lo) && (decide (hi ≤ p.2.1) || piecesCover (p.2.1 + 1) hi rest)

/-- A point of `[lo, hi]` lands inside one of the covering pieces' closed ranges. -/
theorem piecesCover_sound {ps : List (Int × Int × Int × Int × Int)} {hi v : Int}
    (hhi : v ≤ hi) : ∀ lo : Int, piecesCover lo hi ps = true → lo ≤ v →
    ∃ p ∈ ps, p.1 ≤ v ∧ v ≤ p.2.1 := by
  induction ps with
  | nil => intro lo h _; simp [piecesCover] at h
  | cons p rest ih =>
    intro lo h hlo
    simp only [piecesCover, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    rcases le_or_gt v p.2.1 with hv | hv
    · exact ⟨p, List.mem_cons_self, le_trans h1 hlo, hv⟩
    · rcases h2 with h2 | h2
      · omega
      · obtain ⟨q, hq, hql, hqh⟩ := ih _ h2 (by omega)
        exact ⟨q, List.mem_cons_of_mem _ hq, hql, hqh⟩

/-- The 32 pieces cover the whole certified grid `[0, vmaxV]`. -/
theorem granPieces_cover :
    piecesCover 0 (ExpCertV.vmaxV : Int) ExpCertV.granPieces = true := by
  decide +kernel

/-- Every entry of the shared table satisfies its per-piece facts: the cover-certified denominator
floors at `v` and `v + 1`, the `K` cap at the piece's upper edge, and the certified budget
inequalities. -/
theorem granPieces_ok : ∀ p ∈ ExpCertV.granPieces, PieceHolds p := by
  intro p hp
  simp only [ExpCertV.granPieces, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro v hlo hhi
    have hOv := ExpCertV.dOvP00_nonneg (t := (v : Int)) (by omega) (by omega)
    have hOv1 := ExpCertV.dOvP00_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hUn := ExpCertV.dUnP00_nonneg (t := (v : Int)) (by omega) (by omega)
    have hUn1 := ExpCertV.dUnP00_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
    rw [evalDOverP] at hOv
    rw [evalDUnderP] at hUn
    rw [hcast, evalDOverP] at hOv1
    rw [hcast, evalDUnderP] at hUn1
    refine ⟨by norm_num, by norm_num,
      evalPoly_nonneg_of_nonneg Kpoly_coeffs_nonneg (by norm_num), by norm_num,
      by linarith [hOv], by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
      KpM_le_at hhi, by simp only [Kpoly, evalPoly]; norm_num,
      by simp only [Kpoly, evalPoly]; norm_num⟩
  · intro v hlo hhi
    have hOv := ExpCertV.dOvP01_nonneg (t := (v : Int)) (by omega) (by omega)
    have hOv1 := ExpCertV.dOvP01_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hUn := ExpCertV.dUnP01_nonneg (t := (v : Int)) (by omega) (by omega)
    have hUn1 := ExpCertV.dUnP01_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
    rw [evalDOverP] at hOv
    rw [evalDUnderP] at hUn
    rw [hcast, evalDOverP] at hOv1
    rw [hcast, evalDUnderP] at hUn1
    refine ⟨by norm_num, by norm_num,
      evalPoly_nonneg_of_nonneg Kpoly_coeffs_nonneg (by norm_num), by norm_num,
      by linarith [hOv], by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
      KpM_le_at hhi, by simp only [Kpoly, evalPoly]; norm_num,
      by simp only [Kpoly, evalPoly]; norm_num⟩
  · intro v hlo hhi
    have hOv := ExpCertV.dOvP02_nonneg (t := (v : Int)) (by omega) (by omega)
    have hOv1 := ExpCertV.dOvP02_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hUn := ExpCertV.dUnP02_nonneg (t := (v : Int)) (by omega) (by omega)
    have hUn1 := ExpCertV.dUnP02_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
    rw [evalDOverP] at hOv
    rw [evalDUnderP] at hUn
    rw [hcast, evalDOverP] at hOv1
    rw [hcast, evalDUnderP] at hUn1
    refine ⟨by norm_num, by norm_num,
      evalPoly_nonneg_of_nonneg Kpoly_coeffs_nonneg (by norm_num), by norm_num,
      by linarith [hOv], by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
      KpM_le_at hhi, by simp only [Kpoly, evalPoly]; norm_num,
      by simp only [Kpoly, evalPoly]; norm_num⟩
  · intro v hlo hhi
    have hOv := ExpCertV.dOvP03_nonneg (t := (v : Int)) (by omega) (by omega)
    have hOv1 := ExpCertV.dOvP03_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hUn := ExpCertV.dUnP03_nonneg (t := (v : Int)) (by omega) (by omega)
    have hUn1 := ExpCertV.dUnP03_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
    rw [evalDOverP] at hOv
    rw [evalDUnderP] at hUn
    rw [hcast, evalDOverP] at hOv1
    rw [hcast, evalDUnderP] at hUn1
    refine ⟨by norm_num, by norm_num,
      evalPoly_nonneg_of_nonneg Kpoly_coeffs_nonneg (by norm_num), by norm_num,
      by linarith [hOv], by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
      KpM_le_at hhi, by simp only [Kpoly, evalPoly]; norm_num,
      by simp only [Kpoly, evalPoly]; norm_num⟩
  · intro v hlo hhi
    have hOv := ExpCertV.dOvP04_nonneg (t := (v : Int)) (by omega) (by omega)
    have hOv1 := ExpCertV.dOvP04_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hUn := ExpCertV.dUnP04_nonneg (t := (v : Int)) (by omega) (by omega)
    have hUn1 := ExpCertV.dUnP04_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
    rw [evalDOverP] at hOv
    rw [evalDUnderP] at hUn
    rw [hcast, evalDOverP] at hOv1
    rw [hcast, evalDUnderP] at hUn1
    refine ⟨by norm_num, by norm_num,
      evalPoly_nonneg_of_nonneg Kpoly_coeffs_nonneg (by norm_num), by norm_num,
      by linarith [hOv], by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
      KpM_le_at hhi, by simp only [Kpoly, evalPoly]; norm_num,
      by simp only [Kpoly, evalPoly]; norm_num⟩
  · intro v hlo hhi
    have hOv := ExpCertV.dOvP05_nonneg (t := (v : Int)) (by omega) (by omega)
    have hOv1 := ExpCertV.dOvP05_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hUn := ExpCertV.dUnP05_nonneg (t := (v : Int)) (by omega) (by omega)
    have hUn1 := ExpCertV.dUnP05_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
    rw [evalDOverP] at hOv
    rw [evalDUnderP] at hUn
    rw [hcast, evalDOverP] at hOv1
    rw [hcast, evalDUnderP] at hUn1
    refine ⟨by norm_num, by norm_num,
      evalPoly_nonneg_of_nonneg Kpoly_coeffs_nonneg (by norm_num), by norm_num,
      by linarith [hOv], by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
      KpM_le_at hhi, by simp only [Kpoly, evalPoly]; norm_num,
      by simp only [Kpoly, evalPoly]; norm_num⟩
  · intro v hlo hhi
    have hOv := ExpCertV.dOvP06_nonneg (t := (v : Int)) (by omega) (by omega)
    have hOv1 := ExpCertV.dOvP06_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hUn := ExpCertV.dUnP06_nonneg (t := (v : Int)) (by omega) (by omega)
    have hUn1 := ExpCertV.dUnP06_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
    rw [evalDOverP] at hOv
    rw [evalDUnderP] at hUn
    rw [hcast, evalDOverP] at hOv1
    rw [hcast, evalDUnderP] at hUn1
    refine ⟨by norm_num, by norm_num,
      evalPoly_nonneg_of_nonneg Kpoly_coeffs_nonneg (by norm_num), by norm_num,
      by linarith [hOv], by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
      KpM_le_at hhi, by simp only [Kpoly, evalPoly]; norm_num,
      by simp only [Kpoly, evalPoly]; norm_num⟩
  · intro v hlo hhi
    have hOv := ExpCertV.dOvP07_nonneg (t := (v : Int)) (by omega) (by omega)
    have hOv1 := ExpCertV.dOvP07_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hUn := ExpCertV.dUnP07_nonneg (t := (v : Int)) (by omega) (by omega)
    have hUn1 := ExpCertV.dUnP07_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
    rw [evalDOverP] at hOv
    rw [evalDUnderP] at hUn
    rw [hcast, evalDOverP] at hOv1
    rw [hcast, evalDUnderP] at hUn1
    refine ⟨by norm_num, by norm_num,
      evalPoly_nonneg_of_nonneg Kpoly_coeffs_nonneg (by norm_num), by norm_num,
      by linarith [hOv], by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
      KpM_le_at hhi, by simp only [Kpoly, evalPoly]; norm_num,
      by simp only [Kpoly, evalPoly]; norm_num⟩
  · intro v hlo hhi
    have hOv := ExpCertV.dOvP08_nonneg (t := (v : Int)) (by omega) (by omega)
    have hOv1 := ExpCertV.dOvP08_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hUn := ExpCertV.dUnP08_nonneg (t := (v : Int)) (by omega) (by omega)
    have hUn1 := ExpCertV.dUnP08_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
    rw [evalDOverP] at hOv
    rw [evalDUnderP] at hUn
    rw [hcast, evalDOverP] at hOv1
    rw [hcast, evalDUnderP] at hUn1
    refine ⟨by norm_num, by norm_num,
      evalPoly_nonneg_of_nonneg Kpoly_coeffs_nonneg (by norm_num), by norm_num,
      by linarith [hOv], by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
      KpM_le_at hhi, by simp only [Kpoly, evalPoly]; norm_num,
      by simp only [Kpoly, evalPoly]; norm_num⟩
  · intro v hlo hhi
    have hOv := ExpCertV.dOvP09_nonneg (t := (v : Int)) (by omega) (by omega)
    have hOv1 := ExpCertV.dOvP09_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hUn := ExpCertV.dUnP09_nonneg (t := (v : Int)) (by omega) (by omega)
    have hUn1 := ExpCertV.dUnP09_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
    rw [evalDOverP] at hOv
    rw [evalDUnderP] at hUn
    rw [hcast, evalDOverP] at hOv1
    rw [hcast, evalDUnderP] at hUn1
    refine ⟨by norm_num, by norm_num,
      evalPoly_nonneg_of_nonneg Kpoly_coeffs_nonneg (by norm_num), by norm_num,
      by linarith [hOv], by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
      KpM_le_at hhi, by simp only [Kpoly, evalPoly]; norm_num,
      by simp only [Kpoly, evalPoly]; norm_num⟩
  · intro v hlo hhi
    have hOv := ExpCertV.dOvP10_nonneg (t := (v : Int)) (by omega) (by omega)
    have hOv1 := ExpCertV.dOvP10_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hUn := ExpCertV.dUnP10_nonneg (t := (v : Int)) (by omega) (by omega)
    have hUn1 := ExpCertV.dUnP10_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
    rw [evalDOverP] at hOv
    rw [evalDUnderP] at hUn
    rw [hcast, evalDOverP] at hOv1
    rw [hcast, evalDUnderP] at hUn1
    refine ⟨by norm_num, by norm_num,
      evalPoly_nonneg_of_nonneg Kpoly_coeffs_nonneg (by norm_num), by norm_num,
      by linarith [hOv], by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
      KpM_le_at hhi, by simp only [Kpoly, evalPoly]; norm_num,
      by simp only [Kpoly, evalPoly]; norm_num⟩
  · intro v hlo hhi
    have hOv := ExpCertV.dOvP11_nonneg (t := (v : Int)) (by omega) (by omega)
    have hOv1 := ExpCertV.dOvP11_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hUn := ExpCertV.dUnP11_nonneg (t := (v : Int)) (by omega) (by omega)
    have hUn1 := ExpCertV.dUnP11_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
    rw [evalDOverP] at hOv
    rw [evalDUnderP] at hUn
    rw [hcast, evalDOverP] at hOv1
    rw [hcast, evalDUnderP] at hUn1
    refine ⟨by norm_num, by norm_num,
      evalPoly_nonneg_of_nonneg Kpoly_coeffs_nonneg (by norm_num), by norm_num,
      by linarith [hOv], by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
      KpM_le_at hhi, by simp only [Kpoly, evalPoly]; norm_num,
      by simp only [Kpoly, evalPoly]; norm_num⟩
  · intro v hlo hhi
    have hOv := ExpCertV.dOvP12_nonneg (t := (v : Int)) (by omega) (by omega)
    have hOv1 := ExpCertV.dOvP12_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hUn := ExpCertV.dUnP12_nonneg (t := (v : Int)) (by omega) (by omega)
    have hUn1 := ExpCertV.dUnP12_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
    rw [evalDOverP] at hOv
    rw [evalDUnderP] at hUn
    rw [hcast, evalDOverP] at hOv1
    rw [hcast, evalDUnderP] at hUn1
    refine ⟨by norm_num, by norm_num,
      evalPoly_nonneg_of_nonneg Kpoly_coeffs_nonneg (by norm_num), by norm_num,
      by linarith [hOv], by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
      KpM_le_at hhi, by simp only [Kpoly, evalPoly]; norm_num,
      by simp only [Kpoly, evalPoly]; norm_num⟩
  · intro v hlo hhi
    have hOv := ExpCertV.dOvP13_nonneg (t := (v : Int)) (by omega) (by omega)
    have hOv1 := ExpCertV.dOvP13_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hUn := ExpCertV.dUnP13_nonneg (t := (v : Int)) (by omega) (by omega)
    have hUn1 := ExpCertV.dUnP13_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
    rw [evalDOverP] at hOv
    rw [evalDUnderP] at hUn
    rw [hcast, evalDOverP] at hOv1
    rw [hcast, evalDUnderP] at hUn1
    refine ⟨by norm_num, by norm_num,
      evalPoly_nonneg_of_nonneg Kpoly_coeffs_nonneg (by norm_num), by norm_num,
      by linarith [hOv], by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
      KpM_le_at hhi, by simp only [Kpoly, evalPoly]; norm_num,
      by simp only [Kpoly, evalPoly]; norm_num⟩
  · intro v hlo hhi
    have hOv := ExpCertV.dOvP14_nonneg (t := (v : Int)) (by omega) (by omega)
    have hOv1 := ExpCertV.dOvP14_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hUn := ExpCertV.dUnP14_nonneg (t := (v : Int)) (by omega) (by omega)
    have hUn1 := ExpCertV.dUnP14_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
    rw [evalDOverP] at hOv
    rw [evalDUnderP] at hUn
    rw [hcast, evalDOverP] at hOv1
    rw [hcast, evalDUnderP] at hUn1
    refine ⟨by norm_num, by norm_num,
      evalPoly_nonneg_of_nonneg Kpoly_coeffs_nonneg (by norm_num), by norm_num,
      by linarith [hOv], by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
      KpM_le_at hhi, by simp only [Kpoly, evalPoly]; norm_num,
      by simp only [Kpoly, evalPoly]; norm_num⟩
  · intro v hlo hhi
    have hOv := ExpCertV.dOvP15_nonneg (t := (v : Int)) (by omega) (by omega)
    have hOv1 := ExpCertV.dOvP15_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hUn := ExpCertV.dUnP15_nonneg (t := (v : Int)) (by omega) (by omega)
    have hUn1 := ExpCertV.dUnP15_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
    rw [evalDOverP] at hOv
    rw [evalDUnderP] at hUn
    rw [hcast, evalDOverP] at hOv1
    rw [hcast, evalDUnderP] at hUn1
    refine ⟨by norm_num, by norm_num,
      evalPoly_nonneg_of_nonneg Kpoly_coeffs_nonneg (by norm_num), by norm_num,
      by linarith [hOv], by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
      KpM_le_at hhi, by simp only [Kpoly, evalPoly]; norm_num,
      by simp only [Kpoly, evalPoly]; norm_num⟩
  · intro v hlo hhi
    have hOv := ExpCertV.dOvP16_nonneg (t := (v : Int)) (by omega) (by omega)
    have hOv1 := ExpCertV.dOvP16_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hUn := ExpCertV.dUnP16_nonneg (t := (v : Int)) (by omega) (by omega)
    have hUn1 := ExpCertV.dUnP16_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
    rw [evalDOverP] at hOv
    rw [evalDUnderP] at hUn
    rw [hcast, evalDOverP] at hOv1
    rw [hcast, evalDUnderP] at hUn1
    refine ⟨by norm_num, by norm_num,
      evalPoly_nonneg_of_nonneg Kpoly_coeffs_nonneg (by norm_num), by norm_num,
      by linarith [hOv], by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
      KpM_le_at hhi, by simp only [Kpoly, evalPoly]; norm_num,
      by simp only [Kpoly, evalPoly]; norm_num⟩
  · intro v hlo hhi
    have hOv := ExpCertV.dOvP17_nonneg (t := (v : Int)) (by omega) (by omega)
    have hOv1 := ExpCertV.dOvP17_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hUn := ExpCertV.dUnP17_nonneg (t := (v : Int)) (by omega) (by omega)
    have hUn1 := ExpCertV.dUnP17_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
    rw [evalDOverP] at hOv
    rw [evalDUnderP] at hUn
    rw [hcast, evalDOverP] at hOv1
    rw [hcast, evalDUnderP] at hUn1
    refine ⟨by norm_num, by norm_num,
      evalPoly_nonneg_of_nonneg Kpoly_coeffs_nonneg (by norm_num), by norm_num,
      by linarith [hOv], by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
      KpM_le_at hhi, by simp only [Kpoly, evalPoly]; norm_num,
      by simp only [Kpoly, evalPoly]; norm_num⟩
  · intro v hlo hhi
    have hOv := ExpCertV.dOvP18_nonneg (t := (v : Int)) (by omega) (by omega)
    have hOv1 := ExpCertV.dOvP18_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hUn := ExpCertV.dUnP18_nonneg (t := (v : Int)) (by omega) (by omega)
    have hUn1 := ExpCertV.dUnP18_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
    rw [evalDOverP] at hOv
    rw [evalDUnderP] at hUn
    rw [hcast, evalDOverP] at hOv1
    rw [hcast, evalDUnderP] at hUn1
    refine ⟨by norm_num, by norm_num,
      evalPoly_nonneg_of_nonneg Kpoly_coeffs_nonneg (by norm_num), by norm_num,
      by linarith [hOv], by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
      KpM_le_at hhi, by simp only [Kpoly, evalPoly]; norm_num,
      by simp only [Kpoly, evalPoly]; norm_num⟩
  · intro v hlo hhi
    have hOv := ExpCertV.dOvP19_nonneg (t := (v : Int)) (by omega) (by omega)
    have hOv1 := ExpCertV.dOvP19_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hUn := ExpCertV.dUnP19_nonneg (t := (v : Int)) (by omega) (by omega)
    have hUn1 := ExpCertV.dUnP19_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
    rw [evalDOverP] at hOv
    rw [evalDUnderP] at hUn
    rw [hcast, evalDOverP] at hOv1
    rw [hcast, evalDUnderP] at hUn1
    refine ⟨by norm_num, by norm_num,
      evalPoly_nonneg_of_nonneg Kpoly_coeffs_nonneg (by norm_num), by norm_num,
      by linarith [hOv], by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
      KpM_le_at hhi, by simp only [Kpoly, evalPoly]; norm_num,
      by simp only [Kpoly, evalPoly]; norm_num⟩
  · intro v hlo hhi
    have hOv := ExpCertV.dOvP20_nonneg (t := (v : Int)) (by omega) (by omega)
    have hOv1 := ExpCertV.dOvP20_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hUn := ExpCertV.dUnP20_nonneg (t := (v : Int)) (by omega) (by omega)
    have hUn1 := ExpCertV.dUnP20_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
    rw [evalDOverP] at hOv
    rw [evalDUnderP] at hUn
    rw [hcast, evalDOverP] at hOv1
    rw [hcast, evalDUnderP] at hUn1
    refine ⟨by norm_num, by norm_num,
      evalPoly_nonneg_of_nonneg Kpoly_coeffs_nonneg (by norm_num), by norm_num,
      by linarith [hOv], by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
      KpM_le_at hhi, by simp only [Kpoly, evalPoly]; norm_num,
      by simp only [Kpoly, evalPoly]; norm_num⟩
  · intro v hlo hhi
    have hOv := ExpCertV.dOvP21_nonneg (t := (v : Int)) (by omega) (by omega)
    have hOv1 := ExpCertV.dOvP21_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hUn := ExpCertV.dUnP21_nonneg (t := (v : Int)) (by omega) (by omega)
    have hUn1 := ExpCertV.dUnP21_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
    rw [evalDOverP] at hOv
    rw [evalDUnderP] at hUn
    rw [hcast, evalDOverP] at hOv1
    rw [hcast, evalDUnderP] at hUn1
    refine ⟨by norm_num, by norm_num,
      evalPoly_nonneg_of_nonneg Kpoly_coeffs_nonneg (by norm_num), by norm_num,
      by linarith [hOv], by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
      KpM_le_at hhi, by simp only [Kpoly, evalPoly]; norm_num,
      by simp only [Kpoly, evalPoly]; norm_num⟩
  · intro v hlo hhi
    have hOv := ExpCertV.dOvP22_nonneg (t := (v : Int)) (by omega) (by omega)
    have hOv1 := ExpCertV.dOvP22_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hUn := ExpCertV.dUnP22_nonneg (t := (v : Int)) (by omega) (by omega)
    have hUn1 := ExpCertV.dUnP22_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
    rw [evalDOverP] at hOv
    rw [evalDUnderP] at hUn
    rw [hcast, evalDOverP] at hOv1
    rw [hcast, evalDUnderP] at hUn1
    refine ⟨by norm_num, by norm_num,
      evalPoly_nonneg_of_nonneg Kpoly_coeffs_nonneg (by norm_num), by norm_num,
      by linarith [hOv], by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
      KpM_le_at hhi, by simp only [Kpoly, evalPoly]; norm_num,
      by simp only [Kpoly, evalPoly]; norm_num⟩
  · intro v hlo hhi
    have hOv := ExpCertV.dOvP23_nonneg (t := (v : Int)) (by omega) (by omega)
    have hOv1 := ExpCertV.dOvP23_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hUn := ExpCertV.dUnP23_nonneg (t := (v : Int)) (by omega) (by omega)
    have hUn1 := ExpCertV.dUnP23_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
    rw [evalDOverP] at hOv
    rw [evalDUnderP] at hUn
    rw [hcast, evalDOverP] at hOv1
    rw [hcast, evalDUnderP] at hUn1
    refine ⟨by norm_num, by norm_num,
      evalPoly_nonneg_of_nonneg Kpoly_coeffs_nonneg (by norm_num), by norm_num,
      by linarith [hOv], by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
      KpM_le_at hhi, by simp only [Kpoly, evalPoly]; norm_num,
      by simp only [Kpoly, evalPoly]; norm_num⟩
  · intro v hlo hhi
    have hOv := ExpCertV.dOvP24_nonneg (t := (v : Int)) (by omega) (by omega)
    have hOv1 := ExpCertV.dOvP24_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hUn := ExpCertV.dUnP24_nonneg (t := (v : Int)) (by omega) (by omega)
    have hUn1 := ExpCertV.dUnP24_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
    rw [evalDOverP] at hOv
    rw [evalDUnderP] at hUn
    rw [hcast, evalDOverP] at hOv1
    rw [hcast, evalDUnderP] at hUn1
    refine ⟨by norm_num, by norm_num,
      evalPoly_nonneg_of_nonneg Kpoly_coeffs_nonneg (by norm_num), by norm_num,
      by linarith [hOv], by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
      KpM_le_at hhi, by simp only [Kpoly, evalPoly]; norm_num,
      by simp only [Kpoly, evalPoly]; norm_num⟩
  · intro v hlo hhi
    have hOv := ExpCertV.dOvP25_nonneg (t := (v : Int)) (by omega) (by omega)
    have hOv1 := ExpCertV.dOvP25_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hUn := ExpCertV.dUnP25_nonneg (t := (v : Int)) (by omega) (by omega)
    have hUn1 := ExpCertV.dUnP25_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
    rw [evalDOverP] at hOv
    rw [evalDUnderP] at hUn
    rw [hcast, evalDOverP] at hOv1
    rw [hcast, evalDUnderP] at hUn1
    refine ⟨by norm_num, by norm_num,
      evalPoly_nonneg_of_nonneg Kpoly_coeffs_nonneg (by norm_num), by norm_num,
      by linarith [hOv], by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
      KpM_le_at hhi, by simp only [Kpoly, evalPoly]; norm_num,
      by simp only [Kpoly, evalPoly]; norm_num⟩
  · intro v hlo hhi
    have hOv := ExpCertV.dOvP26_nonneg (t := (v : Int)) (by omega) (by omega)
    have hOv1 := ExpCertV.dOvP26_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hUn := ExpCertV.dUnP26_nonneg (t := (v : Int)) (by omega) (by omega)
    have hUn1 := ExpCertV.dUnP26_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
    rw [evalDOverP] at hOv
    rw [evalDUnderP] at hUn
    rw [hcast, evalDOverP] at hOv1
    rw [hcast, evalDUnderP] at hUn1
    refine ⟨by norm_num, by norm_num,
      evalPoly_nonneg_of_nonneg Kpoly_coeffs_nonneg (by norm_num), by norm_num,
      by linarith [hOv], by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
      KpM_le_at hhi, by simp only [Kpoly, evalPoly]; norm_num,
      by simp only [Kpoly, evalPoly]; norm_num⟩
  · intro v hlo hhi
    have hOv := ExpCertV.dOvP27_nonneg (t := (v : Int)) (by omega) (by omega)
    have hOv1 := ExpCertV.dOvP27_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hUn := ExpCertV.dUnP27_nonneg (t := (v : Int)) (by omega) (by omega)
    have hUn1 := ExpCertV.dUnP27_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
    rw [evalDOverP] at hOv
    rw [evalDUnderP] at hUn
    rw [hcast, evalDOverP] at hOv1
    rw [hcast, evalDUnderP] at hUn1
    refine ⟨by norm_num, by norm_num,
      evalPoly_nonneg_of_nonneg Kpoly_coeffs_nonneg (by norm_num), by norm_num,
      by linarith [hOv], by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
      KpM_le_at hhi, by simp only [Kpoly, evalPoly]; norm_num,
      by simp only [Kpoly, evalPoly]; norm_num⟩
  · intro v hlo hhi
    have hOv := ExpCertV.dOvP28_nonneg (t := (v : Int)) (by omega) (by omega)
    have hOv1 := ExpCertV.dOvP28_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hUn := ExpCertV.dUnP28_nonneg (t := (v : Int)) (by omega) (by omega)
    have hUn1 := ExpCertV.dUnP28_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
    rw [evalDOverP] at hOv
    rw [evalDUnderP] at hUn
    rw [hcast, evalDOverP] at hOv1
    rw [hcast, evalDUnderP] at hUn1
    refine ⟨by norm_num, by norm_num,
      evalPoly_nonneg_of_nonneg Kpoly_coeffs_nonneg (by norm_num), by norm_num,
      by linarith [hOv], by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
      KpM_le_at hhi, by simp only [Kpoly, evalPoly]; norm_num,
      by simp only [Kpoly, evalPoly]; norm_num⟩
  · intro v hlo hhi
    have hOv := ExpCertV.dOvP29_nonneg (t := (v : Int)) (by omega) (by omega)
    have hOv1 := ExpCertV.dOvP29_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hUn := ExpCertV.dUnP29_nonneg (t := (v : Int)) (by omega) (by omega)
    have hUn1 := ExpCertV.dUnP29_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
    rw [evalDOverP] at hOv
    rw [evalDUnderP] at hUn
    rw [hcast, evalDOverP] at hOv1
    rw [hcast, evalDUnderP] at hUn1
    refine ⟨by norm_num, by norm_num,
      evalPoly_nonneg_of_nonneg Kpoly_coeffs_nonneg (by norm_num), by norm_num,
      by linarith [hOv], by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
      KpM_le_at hhi, by simp only [Kpoly, evalPoly]; norm_num,
      by simp only [Kpoly, evalPoly]; norm_num⟩
  · intro v hlo hhi
    have hOv := ExpCertV.dOvP30_nonneg (t := (v : Int)) (by omega) (by omega)
    have hOv1 := ExpCertV.dOvP30_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hUn := ExpCertV.dUnP30_nonneg (t := (v : Int)) (by omega) (by omega)
    have hUn1 := ExpCertV.dUnP30_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
    rw [evalDOverP] at hOv
    rw [evalDUnderP] at hUn
    rw [hcast, evalDOverP] at hOv1
    rw [hcast, evalDUnderP] at hUn1
    refine ⟨by norm_num, by norm_num,
      evalPoly_nonneg_of_nonneg Kpoly_coeffs_nonneg (by norm_num), by norm_num,
      by linarith [hOv], by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
      KpM_le_at hhi, by simp only [Kpoly, evalPoly]; norm_num,
      by simp only [Kpoly, evalPoly]; norm_num⟩
  · intro v hlo hhi
    have hOv := ExpCertV.dOvP31_nonneg (t := (v : Int)) (by omega) (by omega)
    have hOv1 := ExpCertV.dOvP31_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hUn := ExpCertV.dUnP31_nonneg (t := (v : Int)) (by omega) (by omega)
    have hUn1 := ExpCertV.dUnP31_nonneg (t := (v : Int) + 1) (by omega) (by omega)
    have hcast : ((v : Int) + 1) = (((v + 1 : Nat)) : Int) := by push_cast; ring
    rw [evalDOverP] at hOv
    rw [evalDUnderP] at hUn
    rw [hcast, evalDOverP] at hOv1
    rw [hcast, evalDUnderP] at hUn1
    refine ⟨by norm_num, by norm_num,
      evalPoly_nonneg_of_nonneg Kpoly_coeffs_nonneg (by norm_num), by norm_num,
      by linarith [hOv], by linarith [hOv1], by linarith [hUn], by linarith [hUn1],
      KpM_le_at hhi, by simp only [Kpoly, evalPoly]; norm_num,
      by simp only [Kpoly, evalPoly]; norm_num⟩

/-- **Piece selection.** The runtime grid point lies in one of the 32 pieces, whose certified
constants apply, and the piece's `t`-cap dominates the reduced argument: `t² < T²`. -/
theorem piece_select_wide {x : Nat} (hx : x < 2 ^ 256) (hW : WideRegion x) :
    ∃ T DO DU Khi : Int,
      PieceOK (vTree x) T DO DU Khi ∧ (int256 (tTree x)) ^ 2 < T ^ 2 := by
  obtain ⟨_, hsplit⟩ := tsq_split_wide hx hW
  have hvI : ((vTree x : Nat) : Int) ≤ (ExpCertV.vmaxV : Int) := by
    exact_mod_cast vTree_le_vmax_wide hx hW
  obtain ⟨p, hp, hplo, hphi⟩ :=
    piecesCover_sound hvI 0 granPieces_cover (Int.natCast_nonneg _)
  obtain ⟨vlo, vhi, T, DO, DU⟩ := p
  exact ⟨T, DO, DU, evalPoly Kpoly vhi,
    granPieces_ok _ hp (vTree x) hplo hphi,
    tsq_lt_capsq hsplit hphi (granPieces_caps _ hp)⟩

theorem piece_select {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    ∃ T DO DU Khi : Int,
      PieceOK (vTree x) T DO DU Khi ∧ (int256 (tTree x)) ^ 2 < T ^ 2 :=
  piece_select_wide hx (wideRegion_of_wad hC hC0)

end ExpYul
