import ExpProof.Mono.EvOdLip
import ExpProof.Mono.Cross

/-!
# The same-octave cross inequality

For adjacent same-octave inputs the reciprocal-symmetric quotient `r0` is monotone. By the
cross-multiplication identity (`Cross.lean`) this reduces to `tod1·ev2 ≤ tod2·ev1`, which the floor
sandwich for `tod` (`Quot.todTree_bound`) reduces in turn to the **smooth** inequality

```
t1·od1·ev2 + 2^128·ev1 ≤ t2·od2·ev1.
```

The smooth inequality holds with large margin: writing `t2 = t1 + d`, `G ≤ d ≤ G + 1`, the gain
`d·od2·ev1 ≥ G·b0·a0` dominates the loss `2^128·ev1 + |t1|·|od1·ev2 − od2·ev1|`, the latter bounded
through the Lipschitz near-constancy of `Ev`/`Od` (`EvOdLip.lean`).
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

/-- The even accumulator's signed value is its (nonnegative) Nat value, in `[a0, 2^127)`. -/
theorem evTree_int {x : Nat} (hv : vTree x < 2 ^ 120) :
    (415147853590918758559635130244235626256 : Int) ≤ (evTree x : Int) ∧
      (evTree x : Int) < 3 * 2 ^ 127 := by
  obtain ⟨hlo, hhi⟩ := evTree_facts hv
  constructor
  · have : (0x1385291795942d41ba5fd317688e18710 : Int) ≤ (evTree x : Int) := by exact_mod_cast hlo
    rw [show (0x1385291795942d41ba5fd317688e18710 : Int) = 415147853590918758559635130244235626256 by
      norm_num] at this
    exact this
  · have : (evTree x : Int) < ((3 * 2 ^ 127 : Nat) : Int) := by exact_mod_cast hhi
    rw [show ((3 * 2 ^ 127 : Nat) : Int) = 3 * 2 ^ 127 by norm_num] at this; exact this

/-- The odd accumulator's signed value is its (nonnegative) Nat value, in `[b0, 5·2^125)`. -/
theorem odTree_int {x : Nat} (hv : vTree x < 2 ^ 120) :
    (207573926795459379279817565122117813128 : Int) ≤ (odTree x : Int) ∧
      (odTree x : Int) < 5 * 2 ^ 125 := by
  obtain ⟨hlo, hhi⟩ := odTree_facts hv
  constructor
  · have : (0x9c2948bcaca16a0dd2fe98bb4470c388 : Int) ≤ (odTree x : Int) := by exact_mod_cast hlo
    rw [show (0x9c2948bcaca16a0dd2fe98bb4470c388 : Int) = 207573926795459379279817565122117813128 by
      norm_num] at this
    exact this
  · have : (odTree x : Int) < ((5 * 2 ^ 125 : Nat) : Int) := by exact_mod_cast hhi
    rw [show ((5 * 2 ^ 125 : Nat) : Int) = 5 * 2 ^ 125 by norm_num] at this; exact this

/-- The even/odd accumulators' signed difference is bounded by `DEv`/`DOd` (the Lipschitz bound
transported to `Int`). -/
theorem evTree_lip_int {x1 x2 : Nat} (hv1 : vTree x1 < 2 ^ 120) (hv2 : vTree x2 < 2 ^ 120)
    (hg1 : vTree x1 ≤ vTree x2 + Wstep) (hg2 : vTree x2 ≤ vTree x1 + Wstep) :
    -(170473652738 : Int) ≤ (evTree x1 : Int) - (evTree x2 : Int) ∧
      (evTree x1 : Int) - (evTree x2 : Int) ≤ 170473652738 := by
  obtain ⟨h1, h2⟩ := evTree_lip hv1 hv2 hg1 hg2
  have c1 : ((evTree x1 : Nat) : Int) ≤ (evTree x2 : Int) + 170473652738 := by exact_mod_cast h1
  have c2 : ((evTree x2 : Nat) : Int) ≤ (evTree x1 : Int) + 170473652738 := by exact_mod_cast h2
  omega

theorem odTree_lip_int {x1 x2 : Nat} (hv1 : vTree x1 < 2 ^ 120) (hv2 : vTree x2 < 2 ^ 120)
    (hg1 : vTree x1 ≤ vTree x2 + Wstep) (hg2 : vTree x2 ≤ vTree x1 + Wstep) :
    -(21288422193 : Int) ≤ (odTree x1 : Int) - (odTree x2 : Int) ∧
      (odTree x1 : Int) - (odTree x2 : Int) ≤ 21288422193 := by
  obtain ⟨h1, h2⟩ := odTree_lip hv1 hv2 hg1 hg2
  have c1 : ((odTree x1 : Nat) : Int) ≤ (odTree x2 : Int) + 21288422193 := by exact_mod_cast h1
  have c2 : ((odTree x2 : Nat) : Int) ≤ (odTree x1 : Int) + 21288422193 := by exact_mod_cast h2
  omega

/-- The squared-argument step, as a `Nat` two-sided gap (`vTree x_i ≤ vTree x_j + W`). -/
theorem vTree_step_nat {x1 x2 : Nat} (hx1 : x1 < 2 ^ 256) (hx2 : x2 < 2 ^ 256)
    (hC1 : int256 Cmask < int256 x1) (hC01 : int256 x1 < int256 C0thresh)
    (hC2 : int256 Cmask < int256 x2) (hC02 : int256 x2 < int256 C0thresh)
    (hk : int256 (kTree x1) = int256 (kTree x2))
    (hadj : int256 x2 = int256 x1 + 1) :
    vTree x1 ≤ vTree x2 + Wstep ∧ vTree x2 ≤ vTree x1 + Wstep := by
  obtain ⟨hlo, hhi⟩ := vTree_step hx1 hx2 hC1 hC01 hC2 hC02 hk hadj
  have c1 : (vTree x1 : Int) ≤ (vTree x2 : Int) + Wstep := by omega
  have c2 : (vTree x2 : Int) ≤ (vTree x1 : Int) + Wstep := by omega
  exact ⟨by exact_mod_cast c1, by exact_mod_cast c2⟩

/-- Abstract smooth certificate over opaque accumulator/argument values. The gain `d·od2·ev1`
dominates the loss `2^128·ev2 + |t1|·|od1·ev2 − od2·ev1|`, where the cross difference is controlled
by the Lipschitz near-constancy. -/
theorem smooth_cross_of {t1 d ev1 ev2 od1 od2 : Int}
    (hd1 : (680564733841 : Int) ≤ d)
    (ht1lo : -(340282366920938463463374607431768211456 : Int) < t1)
    (ht1hi : t1 < 340282366920938463463374607431768211456)
    (hev1lo : (415147853590918758559635130244235626256 : Int) ≤ ev1)
    (hev1hi : ev1 < 510423550381407695195061911147652317184)
    (hev2lo : (415147853590918758559635130244235626256 : Int) ≤ ev2)
    (hev2hi : ev2 < 510423550381407695195061911147652317184)
    (hod2lo : (207573926795459379279817565122117813128 : Int) ≤ od2)
    (hod2hi : od2 < 212676479325586539664609129644855132160)
    (hevd1 : -(170473652738 : Int) ≤ ev1 - ev2) (hevd2 : ev1 - ev2 ≤ 170473652738)
    (hodd1 : -(21288422193 : Int) ≤ od1 - od2) (hodd2 : od1 - od2 ≤ 21288422193) :
    t1 * od1 * ev2 + 680564733841876926926749214863536422912 * ev1 ≤
      (t1 + d) * od2 * ev1 := by
  -- cross difference `cd = od1·ev2 − od2·ev1`, bounded by `CB = DOd·2^127 + 2^126·DEv`
  have hcd_eq : od1 * ev2 - od2 * ev1 = (od1 - od2) * ev2 + od2 * (ev2 - ev1) := by ring
  -- bound each piece
  have hev2nn : (0 : Int) ≤ ev2 := by linarith
  have hod2nn : (0 : Int) ≤ od2 := by linarith
  have hp1 : (od1 - od2) * ev2 ≤ 21288422193 * 510423550381407695195061911147652317184 := by
    nlinarith [hodd2, hodd1, hev2nn, hev2hi]
  have hp1' : -(21288422193 * 510423550381407695195061911147652317184 : Int) ≤ (od1 - od2) * ev2 := by
    nlinarith [hodd1, hev2nn, hev2hi]
  have hp2 : od2 * (ev2 - ev1) ≤ 212676479325586539664609129644855132160 * 170473652738 := by
    nlinarith [hod2nn, hod2hi, hevd1, hevd2]
  have hp2' : -(212676479325586539664609129644855132160 * 170473652738 : Int) ≤ od2 * (ev2 - ev1) := by
    nlinarith [hod2nn, hod2hi, hevd1, hevd2]
  -- so |cd| ≤ CB
  set CB : Int := 21288422193 * 510423550381407695195061911147652317184 +
    212676479325586539664609129644855132160 * 170473652738 with hCB
  have hcd_hi : od1 * ev2 - od2 * ev1 ≤ CB := by rw [hcd_eq, hCB]; linarith
  have hcd_lo : -CB ≤ od1 * ev2 - od2 * ev1 := by rw [hcd_eq, hCB]; linarith
  -- `t1·(od1·ev2 − od2·ev1) ≤ 2^127·CB`
  have hCBnn : (0 : Int) ≤ CB := by rw [hCB]; norm_num
  have htcd : t1 * (od1 * ev2 - od2 * ev1) ≤ 340282366920938463463374607431768211456 * CB := by
    rcases le_total 0 t1 with ht | ht
    · have h1 : t1 * (od1 * ev2 - od2 * ev1) ≤ t1 * CB :=
        mul_le_mul_left_nonneg hcd_hi ht
      have h2 : t1 * CB ≤ 340282366920938463463374607431768211456 * CB :=
        mul_le_mul_right_nonneg (le_of_lt ht1hi) hCBnn
      linarith
    · have h1 : t1 * (od1 * ev2 - od2 * ev1) ≤ t1 * (-CB) := by
        have := mul_le_mul_left_nonneg hcd_lo (show (0:Int) ≤ -t1 by linarith)
        nlinarith [this]
      have h2 : t1 * (-CB) ≤ 340282366920938463463374607431768211456 * CB := by nlinarith [ht1lo, hCBnn, ht]
      linarith
  -- gain: d·od2·ev1 ≥ 680564733841·b0·a0
  have hev1nn : (0 : Int) ≤ ev1 := by linarith
  have hgain : (680564733841 : Int) * 207573926795459379279817565122117813128 *
      415147853590918758559635130244235626256 ≤ d * od2 * ev1 := by
    have g1 : (680564733841 : Int) * 207573926795459379279817565122117813128 ≤ d * od2 := by
      have := mul_le_mul hd1 hod2lo (by norm_num : (0:Int) ≤ 207573926795459379279817565122117813128) (by linarith)
      linarith
    have g2 : (680564733841 : Int) * 207573926795459379279817565122117813128 *
        415147853590918758559635130244235626256 ≤ (d * od2) * ev1 :=
      mul_le_mul g1 hev1lo (by norm_num) (by positivity)
    linarith [g2]
  -- assemble: goal `t1·od1·ev2 + 2^128·ev2 ≤ (t1+d)·od2·ev1 = t1·od2·ev1 + d·od2·ev1`
  -- `t1·od1·ev2 − t1·od2·ev1 = t1·(od1·ev2 − od2·ev1) ≤ 2^127·CB`
  have hexpand : (t1 + d) * od2 * ev1 = t1 * od2 * ev1 + d * od2 * ev1 := by ring
  have hdecomp : t1 * od1 * ev2 - t1 * od2 * ev1 = t1 * (od1 * ev2 - od2 * ev1) := by ring
  rw [hexpand]
  -- numeric closure: 2^128·ev2 + 2^127·CB ≤ gain, and ev2 < 2^127
  have hkey : (680564733841876926926749214863536422912 : Int) * ev1 +
      340282366920938463463374607431768211456 * CB ≤
      (680564733841 : Int) * 207573926795459379279817565122117813128 *
        415147853590918758559635130244235626256 := by
    rw [hCB]
    nlinarith [hev1hi]
  nlinarith [htcd, hgain, hkey, hdecomp]

/-- **The smooth certificate.** For adjacent same-octave inputs,
`t1·od1·ev2 + 2^129·ev2 ≤ t2·od2·ev1`. -/
theorem smooth_cross {x1 x2 : Nat} (hx1 : x1 < 2 ^ 256) (hx2 : x2 < 2 ^ 256)
    (hC1 : int256 Cmask < int256 x1) (hC01 : int256 x1 < int256 C0thresh)
    (hC2 : int256 Cmask < int256 x2) (hC02 : int256 x2 < int256 C0thresh)
    (hk : int256 (kTree x1) = int256 (kTree x2))
    (hadj : int256 x2 = int256 x1 + 1) :
    int256 (tTree x1) * (odTree x1 : Int) * (evTree x2 : Int) +
        2 ^ 129 * (evTree x1 : Int) ≤
      int256 (tTree x2) * (odTree x2 : Int) * (evTree x1 : Int) := by
  have hv1 : vTree x1 < 2 ^ 120 := (vTree_eq hx1 hC1 hC01).2
  have hv2 : vTree x2 < 2 ^ 120 := (vTree_eq hx2 hC2 hC02).2
  obtain ⟨hg1, hg2⟩ := vTree_step_nat hx1 hx2 hC1 hC01 hC2 hC02 hk hadj
  obtain ⟨hev1lo, hev1hi⟩ := evTree_int hv1
  obtain ⟨hev2lo, hev2hi⟩ := evTree_int hv2
  obtain ⟨hod2lo, hod2hi⟩ := odTree_int hv2
  obtain ⟨hevd1, hevd2⟩ := evTree_lip_int hv1 hv2 hg1 hg2
  obtain ⟨hodd1, hodd2⟩ := odTree_lip_int hv1 hv2 hg1 hg2
  obtain ⟨htg1, -⟩ := tTree_step hx1 hx2 hC1 hC01 hC2 hC02 hk hadj
  obtain ⟨htlo1, hthi1⟩ := tTree_bound hx1 hC1 hC01
  -- numeric rewrites of the power bounds
  have hGv : (Gstep : Int) = 680564733841 := by unfold Gstep; norm_num
  rw [hGv] at htg1
  rw [show (2 : Int) ^ 128 = 340282366920938463463374607431768211456 by norm_num] at htlo1 hthi1
  rw [show (3 : Int) * 2 ^ 127 = 510423550381407695195061911147652317184 by norm_num] at hev1hi hev2hi
  rw [show (5 : Int) * 2 ^ 125 = 212676479325586539664609129644855132160 by norm_num] at hod2hi
  rw [show (2 : Int) ^ 129 = 680564733841876926926749214863536422912 by norm_num]
  -- t2 = t1 + d, d ∈ [G, G+1]
  have ht2eq : int256 (tTree x2) = int256 (tTree x1) + (int256 (tTree x2) - int256 (tTree x1)) := by
    ring
  rw [ht2eq]
  exact smooth_cross_of htg1 htlo1 hthi1 hev1lo hev1hi hev2lo hev2hi hod2lo hod2hi
    hevd1 hevd2 hodd1 hodd2

/-- Abstract bridge: from the two `tod` floor sandwiches, the smooth inequality, and `ev1 > 0`,
the cross inequality `tod1·ev2 ≤ tod2·ev1` follows. -/
theorem tod_cross_of {tod1 tod2 tprod1 tprod2 ev1 ev2 : Int}
    (hfl1 : (2 : Int) ^ 129 * tod1 ≤ tprod1) (hfu2 : tprod2 < 2 ^ 129 * tod2 + 2 ^ 129)
    (hev1pos : 0 < ev1) (hev2nn : 0 ≤ ev2)
    (hsmooth : tprod1 * ev2 + 2 ^ 129 * ev1 ≤ tprod2 * ev1) :
    tod1 * ev2 ≤ tod2 * ev1 := by
  -- 2^129·tod1·ev2 ≤ tprod1·ev2 ≤ tprod2·ev1 − 2^129·ev1 < 2^129·tod2·ev1
  have hp : (0 : Int) < 2 ^ 129 := by norm_num
  have s1 : 2 ^ 129 * tod1 * ev2 ≤ tprod1 * ev2 := mul_le_mul_right_nonneg hfl1 hev2nn
  have s2 : tprod2 * ev1 < (2 ^ 129 * tod2 + 2 ^ 129) * ev1 :=
    Int.mul_lt_mul_of_pos_right hfu2 hev1pos
  -- 2^129·tod1·ev2 ≤ tprod1·ev2 ≤ tprod2·ev1 − 2^129·ev1 < 2^129·tod2·ev1 + 2^129·ev1 − 2^129·ev1
  have hchain : 2 ^ 129 * (tod1 * ev2) < 2 ^ 129 * (tod2 * ev1) := by nlinarith [s1, s2, hsmooth]
  exact le_of_lt (lt_of_mul_lt_mul_left hchain (by norm_num : (0:Int) ≤ 2 ^ 129))

/-- **The same-octave cross inequality.** For adjacent same-octave inputs,
`tod1·ev2 ≤ tod2·ev1`. -/
theorem tod_cross {x1 x2 : Nat} (hx1 : x1 < 2 ^ 256) (hx2 : x2 < 2 ^ 256)
    (hC1 : int256 Cmask < int256 x1) (hC01 : int256 x1 < int256 C0thresh)
    (hC2 : int256 Cmask < int256 x2) (hC02 : int256 x2 < int256 C0thresh)
    (hk : int256 (kTree x1) = int256 (kTree x2))
    (hadj : int256 x2 = int256 x1 + 1) :
    int256 (todTree x1) * (evTree x2 : Int) ≤ int256 (todTree x2) * (evTree x1 : Int) := by
  obtain ⟨_, _, hfl1, _⟩ := todTree_bound hx1 hC1 hC01
  obtain ⟨_, _, _, hfu2⟩ := todTree_bound hx2 hC2 hC02
  have hv1 : vTree x1 < 2 ^ 120 := (vTree_eq hx1 hC1 hC01).2
  have hv2 : vTree x2 < 2 ^ 120 := (vTree_eq hx2 hC2 hC02).2
  have hev1pos : 0 < (evTree x1 : Int) := by
    have := (evTree_int hv1).1; linarith
  have hev2nn : 0 ≤ (evTree x2 : Int) := Int.natCast_nonneg _
  exact tod_cross_of hfl1 hfu2 hev1pos hev2nn
    (smooth_cross hx1 hx2 hC1 hC01 hC2 hC02 hk hadj)

/-- The squared-argument step gap on the wide region, as a `Nat` two-sided gap. -/
theorem vTree_step_nat_wide {x1 x2 : Nat} (hx1 : x1 < 2 ^ 256) (hx2 : x2 < 2 ^ 256)
    (hW1 : WideRegion x1) (hW2 : WideRegion x2)
    (hk : int256 (kTree x1) = int256 (kTree x2))
    (hadj : int256 x2 = int256 x1 + 1) :
    vTree x1 ≤ vTree x2 + Wstep ∧ vTree x2 ≤ vTree x1 + Wstep := by
  obtain ⟨hlo, hhi⟩ := vTree_step_wide hx1 hx2 hW1 hW2 hk hadj
  have c1 : (vTree x1 : Int) ≤ (vTree x2 : Int) + Wstep := by omega
  have c2 : (vTree x2 : Int) ≤ (vTree x1 : Int) + Wstep := by omega
  exact ⟨by exact_mod_cast c1, by exact_mod_cast c2⟩

/-- **The smooth certificate on the wide region.** -/
theorem smooth_cross_wide {x1 x2 : Nat} (hx1 : x1 < 2 ^ 256) (hx2 : x2 < 2 ^ 256)
    (hW1 : WideRegion x1) (hW2 : WideRegion x2)
    (hk : int256 (kTree x1) = int256 (kTree x2))
    (hadj : int256 x2 = int256 x1 + 1) :
    int256 (tTree x1) * (odTree x1 : Int) * (evTree x2 : Int) +
        2 ^ 129 * (evTree x1 : Int) ≤
      int256 (tTree x2) * (odTree x2 : Int) * (evTree x1 : Int) := by
  have hv1 : vTree x1 < 2 ^ 120 := (vTree_eq_wide hx1 hW1).2
  have hv2 : vTree x2 < 2 ^ 120 := (vTree_eq_wide hx2 hW2).2
  obtain ⟨hg1, hg2⟩ := vTree_step_nat_wide hx1 hx2 hW1 hW2 hk hadj
  obtain ⟨hev1lo, hev1hi⟩ := evTree_int hv1
  obtain ⟨hev2lo, hev2hi⟩ := evTree_int hv2
  obtain ⟨hod2lo, hod2hi⟩ := odTree_int hv2
  obtain ⟨hevd1, hevd2⟩ := evTree_lip_int hv1 hv2 hg1 hg2
  obtain ⟨hodd1, hodd2⟩ := odTree_lip_int hv1 hv2 hg1 hg2
  obtain ⟨htg1, -⟩ := tTree_step_wide hx1 hx2 hW1 hW2 hk hadj
  obtain ⟨htlo1, hthi1⟩ := tTree_bound_wide hx1 hW1
  have hGv : (Gstep : Int) = 680564733841 := by unfold Gstep; norm_num
  rw [hGv] at htg1
  rw [show (2 : Int) ^ 128 = 340282366920938463463374607431768211456 by norm_num] at htlo1 hthi1
  rw [show (3 : Int) * 2 ^ 127 = 510423550381407695195061911147652317184 by norm_num] at hev1hi hev2hi
  rw [show (5 : Int) * 2 ^ 125 = 212676479325586539664609129644855132160 by norm_num] at hod2hi
  rw [show (2 : Int) ^ 129 = 680564733841876926926749214863536422912 by norm_num]
  have ht2eq : int256 (tTree x2) = int256 (tTree x1) + (int256 (tTree x2) - int256 (tTree x1)) := by
    ring
  rw [ht2eq]
  exact smooth_cross_of htg1 htlo1 hthi1 hev1lo hev1hi hev2lo hev2hi hod2lo hod2hi
    hevd1 hevd2 hodd1 hodd2

/-- **The same-octave cross inequality on the wide region.** -/
theorem tod_cross_wide {x1 x2 : Nat} (hx1 : x1 < 2 ^ 256) (hx2 : x2 < 2 ^ 256)
    (hW1 : WideRegion x1) (hW2 : WideRegion x2)
    (hk : int256 (kTree x1) = int256 (kTree x2))
    (hadj : int256 x2 = int256 x1 + 1) :
    int256 (todTree x1) * (evTree x2 : Int) ≤ int256 (todTree x2) * (evTree x1 : Int) := by
  obtain ⟨_, _, hfl1, _⟩ := todTree_bound_wide hx1 hW1
  obtain ⟨_, _, _, hfu2⟩ := todTree_bound_wide hx2 hW2
  have hv1 : vTree x1 < 2 ^ 120 := (vTree_eq_wide hx1 hW1).2
  have hv2 : vTree x2 < 2 ^ 120 := (vTree_eq_wide hx2 hW2).2
  have hev1pos : 0 < (evTree x1 : Int) := by
    have := (evTree_int hv1).1; linarith
  have hev2nn : 0 ≤ (evTree x2 : Int) := Int.natCast_nonneg _
  exact tod_cross_of hfl1 hfu2 hev1pos hev2nn
    (smooth_cross_wide hx1 hx2 hW1 hW2 hk hadj)

end ExpYul
