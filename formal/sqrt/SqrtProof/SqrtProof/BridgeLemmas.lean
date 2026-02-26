import Init
import SqrtProof.FloorBound

namespace SqrtBridge

def bstep (x z : Nat) : Nat := (z + x / z) / 2

private theorem hmul2 (a b : Nat) : a * (2 * b) = 2 * (a * b) := by
  calc
    a * (2 * b) = (a * 2) * b := by rw [Nat.mul_assoc]
    _ = (2 * a) * b := by rw [Nat.mul_comm a 2]
    _ = 2 * (a * b) := by rw [Nat.mul_assoc]

private theorem div_split (m d : Nat) (hmd : d ≤ m) :
    (m * m + 2 * m) / (m + d) = (m - d) + (d * d + 2 * m) / (m + d) := by
  by_cases hzero : m + d = 0
  · have hm0 : m = 0 := by omega
    have hd0 : d = 0 := by omega
    subst hm0; subst hd0
    simp
  · have hsq0 := sq_identity_ge (m + d) m (by omega) (by omega)
    have hsq : (m + d) * (m - d) + d * d = m * m := by
      have hsub : 2 * m - (m + d) = m - d := by omega
      have hdm : (m + d) - m = d := by rw [Nat.add_sub_cancel_left]
      rw [hsub, hdm] at hsq0
      exact hsq0
    have hmul : (m + d) * (m - d) + (d * d + 2 * m) = m * m + 2 * m := by
      rw [← hsq]
      omega
    rw [← hmul]
    have hpos : 0 < m + d := by omega
    rw [Nat.mul_add_div hpos]

private theorem rhs_eq (s m : Nat) (hs : s ≤ m) :
    s * s + m * m + 2 * m - 2 * (s * m) = (m - s) * (m - s) + 2 * m := by
  have hsq := sq_identity_le s m hs
  rw [← hsq]
  rw [Nat.mul_sub, hmul2]
  let A := (m - s) * (m - s)
  change s * s + (2 * (s * m) - s * s + A) + 2 * m - 2 * (s * m) = A + 2 * m
  have hs2 : s * s ≤ 2 * (s * m) := by
    have hsm : s * s ≤ s * m := Nat.mul_le_mul_left s hs
    omega
  have hpre : s * s + (2 * (s * m) - s * s + A) + 2 * m
      = (2 * (s * m)) + A + 2 * m := by
    omega
  rw [hpre]
  omega

private theorem rhs_eq_rev (s m : Nat) (hs : m ≤ s) :
    s * s + m * m + 2 * m - 2 * (s * m) = (s - m) * (s - m) + 2 * m := by
  have hsq := sq_identity_le m s hs
  rw [← hsq]
  rw [Nat.mul_sub, hmul2]
  let A := (s - m) * (s - m)
  have hcomm : 2 * (s * m) = 2 * (m * s) := by rw [Nat.mul_comm s m]
  rw [hcomm]
  have hm2 : m * m ≤ 2 * (m * s) := by
    have hms : m * m ≤ m * s := Nat.mul_le_mul_left m hs
    omega
  have hpre : 2 * (m * s) - m * m + A + m * m + 2 * m
      = 2 * (m * s) + A + 2 * m := by
    have hsubadd : 2 * (m * s) - m * m + m * m = 2 * (m * s) := Nat.sub_add_cancel hm2
    omega
  rw [hpre]
  omega

/-- One-step error contraction for `z = m + d` with `d ≤ m`.
    This is the recurrence used by the finite-certificate bridge. -/
theorem step_error_bound
    (m d x : Nat)
    (hm : 0 < m)
    (hmd : d ≤ m)
    (hxhi : x < (m + 1) * (m + 1)) :
    bstep x (m + d) - m ≤ d * d / (2 * m) + 1 := by
  unfold bstep
  have hxhi' : x < m * m + (m + m) + 1 := by
    simpa [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hxhi
  have hx_le : x ≤ m * m + 2 * m := by omega
  have hdiv : x / (m + d) ≤ (m * m + 2 * m) / (m + d) := Nat.div_le_div_right hx_le
  rw [div_split m d hmd] at hdiv
  have hsum : m + d + x / (m + d) ≤ 2 * m + (d * d + 2 * m) / (m + d) := by
    omega
  have hhalf : (m + d + x / (m + d)) / 2 ≤ (2 * m + (d * d + 2 * m) / (m + d)) / 2 :=
    Nat.div_le_div_right hsum
  have hsub : (m + d + x / (m + d)) / 2 - m ≤ ((2 * m + (d * d + 2 * m) / (m + d)) / 2) - m :=
    Nat.sub_le_sub_right hhalf m
  have hright : ((2 * m + (d * d + 2 * m) / (m + d)) / 2) - m
      = ((d * d + 2 * m) / (m + d)) / 2 := by
    let q := (d * d + 2 * m) / (m + d)
    have htmp : (2 * m + q) / 2 = m + q / 2 := by
      have hswap : 2 * m + q = q + m * 2 := by omega
      rw [hswap, Nat.add_mul_div_right q m (by decide : 0 < 2)]
      omega
    rw [htmp, Nat.add_sub_cancel_left]
  rw [hright] at hsub
  have hden : m ≤ m + d := by omega
  have hdiv2 : (d * d + 2 * m) / (m + d) ≤ (d * d + 2 * m) / m :=
    Nat.div_le_div_left hden hm
  have hhalf2 : ((d * d + 2 * m) / (m + d)) / 2 ≤ ((d * d + 2 * m) / m) / 2 :=
    Nat.div_le_div_right hdiv2
  have hmain : ((d * d + 2 * m) / m) / 2 = d * d / (2 * m) + 1 := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm m 2]
    have hsum2 : d * d + 2 * m = d * d + 1 * (2 * m) := by omega
    rw [hsum2, Nat.add_mul_div_right (d * d) 1 (by omega : 0 < 2 * m)]
  have hbound : (m + d + x / (m + d)) / 2 - m ≤ ((d * d + 2 * m) / m) / 2 :=
    Nat.le_trans hsub hhalf2
  exact Nat.le_trans hbound (by simp [hmain])

/-- Upper bound for the first post-seed error `d₁ = bstep x s - m`, using only
    `m ∈ [lo, hi]` and the interval constraint `m² ≤ x < (m+1)²`. -/
theorem d1_bound
    (x m s lo hi : Nat)
    (hs : 0 < s)
    (hmlo : m * m ≤ x)
    (hmhi : x < (m + 1) * (m + 1))
    (hlo : lo ≤ m)
    (hhi : m ≤ hi) :
    let maxAbs := max (s - lo) (hi - s)
    bstep x s - m ≤ (maxAbs * maxAbs + 2 * hi) / (2 * s) := by
  unfold bstep
  simp only
  have hmstep : m ≤ (s + x / s) / 2 := babylon_step_floor_bound x s m hs hmlo
  have hmulsub : 2 * s * ((s + x / s) / 2 - m) = 2 * s * ((s + x / s) / 2) - 2 * s * m := by
    rw [Nat.mul_sub]
  have h2z : 2 * ((s + x / s) / 2) ≤ s + x / s := Nat.mul_div_le (s + x / s) 2
  have h2z_mul : 2 * s * ((s + x / s) / 2) ≤ s * (s + x / s) := by
    have := Nat.mul_le_mul_left s h2z
    simpa [Nat.mul_assoc, Nat.mul_comm 2 s] using this
  have hsub : 2 * s * ((s + x / s) / 2 - m) ≤ s * (s + x / s) - 2 * s * m := by
    have hsub' : 2 * s * ((s + x / s) / 2) - 2 * s * m ≤ s * (s + x / s) - 2 * s * m :=
      Nat.sub_le_sub_right h2z_mul (2 * s * m)
    simpa [hmulsub] using hsub'
  have hdivmul : s * (x / s) ≤ x := Nat.mul_div_le x s
  have hnum1 : s * (s + x / s) - 2 * s * m ≤ s * s + x - 2 * s * m := by
    have hpre : s * (s + x / s) = s * s + s * (x / s) := by rw [Nat.mul_add]
    rw [hpre]
    exact Nat.sub_le_sub_right (Nat.add_le_add_left hdivmul (s * s)) (2 * s * m)
  have hnum2 : s * s + x - 2 * s * m ≤ s * s + m * m + 2 * m - 2 * s * m := by
    have hmhi' : x < m * m + (m + m) + 1 := by
      simpa [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hmhi
    have hx_le : x ≤ m * m + 2 * m := by omega
    omega
  have hnum : 2 * s * ((s + x / s) / 2 - m) ≤ s * s + m * m + 2 * m - 2 * s * m :=
    Nat.le_trans hsub (Nat.le_trans hnum1 hnum2)
  let maxAbs := max (s - lo) (hi - s)
  have hs2 : 0 < 2 * s := by omega
  by_cases hsm : s ≤ m
  · have hr : s * s + m * m + 2 * m - 2 * s * m = (m - s) * (m - s) + 2 * m := by
      simpa [Nat.mul_assoc] using rhs_eq s m hsm
    rw [hr] at hnum
    have hds : m - s ≤ hi - s := Nat.sub_le_sub_right hhi s
    have hsq : (m - s) * (m - s) ≤ (hi - s) * (hi - s) := Nat.mul_le_mul hds hds
    have hsq' : (hi - s) * (hi - s) ≤ maxAbs * maxAbs := by
      have hmmax : hi - s ≤ maxAbs := Nat.le_max_right (s - lo) (hi - s)
      exact Nat.mul_le_mul hmmax hmmax
    have h2m : 2 * m ≤ 2 * hi := by omega
    have hfin : 2 * s * ((s + x / s) / 2 - m) ≤ maxAbs * maxAbs + 2 * hi := by
      exact Nat.le_trans hnum (Nat.add_le_add (Nat.le_trans hsq hsq') h2m)
    exact (Nat.le_div_iff_mul_le hs2).2 (by simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hfin)
  · have hms : m ≤ s := by omega
    have hr : s * s + m * m + 2 * m - 2 * s * m = (s - m) * (s - m) + 2 * m := by
      simpa [Nat.mul_assoc] using rhs_eq_rev s m hms
    rw [hr] at hnum
    have hds : s - m ≤ s - lo := Nat.sub_le_sub_left hlo s
    have hsq : (s - m) * (s - m) ≤ (s - lo) * (s - lo) := Nat.mul_le_mul hds hds
    have hsq' : (s - lo) * (s - lo) ≤ maxAbs * maxAbs := by
      have hmmax : s - lo ≤ maxAbs := Nat.le_max_left (s - lo) (hi - s)
      exact Nat.mul_le_mul hmmax hmmax
    have h2m : 2 * m ≤ 2 * hi := by omega
    have hfin : 2 * s * ((s + x / s) / 2 - m) ≤ maxAbs * maxAbs + 2 * hi := by
      exact Nat.le_trans hnum (Nat.add_le_add (Nat.le_trans hsq hsq') h2m)
    exact (Nat.le_div_iff_mul_le hs2).2 (by simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hfin)

end SqrtBridge
