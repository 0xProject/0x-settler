import Init
import SqrtProof.FloorBound
import SqrtProof.BridgeLemmas
import SqrtProof.FiniteCert

namespace SqrtCertified

open SqrtBridge
open SqrtCert

def run6From (x z : Nat) : Nat :=
  let z := bstep x z
  let z := bstep x z
  let z := bstep x z
  let z := bstep x z
  let z := bstep x z
  let z := bstep x z
  z

theorem step_from_bound
    (x m lo z D : Nat)
    (hm : 0 < m)
    (hloPos : 0 < lo)
    (hlo : lo ≤ m)
    (hxhi : x < (m + 1) * (m + 1))
    (hmz : m ≤ z)
    (hzD : z - m ≤ D)
    (hDle : D ≤ m) :
    bstep x z - m ≤ nextD lo D := by
  have hz' : m + (z - m) = z := by omega
  have hdle : z - m ≤ m := Nat.le_trans hzD hDle
  have hstep := SqrtBridge.step_error_bound m (z - m) x hm hdle hxhi
  have hstep' : bstep x z - m ≤ (z - m) * (z - m) / (2 * m) + 1 := by
    simpa only [hz'] using hstep
  have hsq : (z - m) * (z - m) ≤ D * D := Nat.mul_le_mul hzD hzD
  have hdiv1 : (z - m) * (z - m) / (2 * m) ≤ D * D / (2 * m) :=
    Nat.div_le_div_right hsq
  have hden : 2 * lo ≤ 2 * m := Nat.mul_le_mul_left 2 hlo
  have hdiv2 : D * D / (2 * m) ≤ D * D / (2 * lo) :=
    Nat.div_le_div_left hden (by omega : 0 < 2 * lo)
  have hfinal : (z - m) * (z - m) / (2 * m) + 1 ≤ D * D / (2 * lo) + 1 :=
    Nat.add_le_add_right (Nat.le_trans hdiv1 hdiv2) 1
  exact Nat.le_trans hstep' (by simpa [nextD] using hfinal)

theorem run6_error_le_cert
    (i : Fin 256)
    (x m : Nat)
    (hm : 0 < m)
    (hmlo : m * m ≤ x)
    (hmhi : x < (m + 1) * (m + 1))
    (hlo : loOf i ≤ m)
    (hhi : m ≤ hiOf i) :
    run6From x (seedOf i) - m ≤ d6 i := by
  let z1 := bstep x (seedOf i)
  let z2 := bstep x z1
  let z3 := bstep x z2
  let z4 := bstep x z3
  let z5 := bstep x z4
  let z6 := bstep x z5

  have hs : 0 < seedOf i := by
    have hpow : 0 < (2 : Nat) ^ ((i.val + 1) / 2) := Nat.pow_pos (by decide : 0 < (2 : Nat))
    simpa [seedOf, Nat.shiftLeft_eq, Nat.one_mul] using hpow

  have hmz1 : m ≤ z1 := by
    dsimp [z1]
    exact babylon_step_floor_bound x (seedOf i) m hs hmlo
  have hz1Pos : 0 < z1 := Nat.lt_of_lt_of_le hm hmz1
  have hd1 : z1 - m ≤ d1 i := by
    have h := SqrtBridge.d1_bound x m (seedOf i) (loOf i) (hiOf i) hs hmlo hmhi hlo hhi
    simpa [z1, d1, maxAbs] using h
  have hd1m : d1 i ≤ m := Nat.le_trans (d1_le_lo i) hlo

  have hmz2 : m ≤ z2 := by
    dsimp [z2]
    exact babylon_step_floor_bound x z1 m hz1Pos hmlo
  have hz2Pos : 0 < z2 := Nat.lt_of_lt_of_le hm hmz2
  have hd2 : z2 - m ≤ d2 i := by
    have h := step_from_bound x m (loOf i) z1 (d1 i) hm (lo_pos i) hlo hmhi hmz1 hd1 hd1m
    simpa [z2, d2, nextD] using h
  have hd2m : d2 i ≤ m := Nat.le_trans (d2_le_lo i) hlo

  have hmz3 : m ≤ z3 := by
    dsimp [z3]
    exact babylon_step_floor_bound x z2 m hz2Pos hmlo
  have hz3Pos : 0 < z3 := Nat.lt_of_lt_of_le hm hmz3
  have hd3 : z3 - m ≤ d3 i := by
    have h := step_from_bound x m (loOf i) z2 (d2 i) hm (lo_pos i) hlo hmhi hmz2 hd2 hd2m
    simpa [z3, d3, nextD] using h
  have hd3m : d3 i ≤ m := Nat.le_trans (d3_le_lo i) hlo

  have hmz4 : m ≤ z4 := by
    dsimp [z4]
    exact babylon_step_floor_bound x z3 m hz3Pos hmlo
  have hz4Pos : 0 < z4 := Nat.lt_of_lt_of_le hm hmz4
  have hd4 : z4 - m ≤ d4 i := by
    have h := step_from_bound x m (loOf i) z3 (d3 i) hm (lo_pos i) hlo hmhi hmz3 hd3 hd3m
    simpa [z4, d4, nextD] using h
  have hd4m : d4 i ≤ m := Nat.le_trans (d4_le_lo i) hlo

  have hmz5 : m ≤ z5 := by
    dsimp [z5]
    exact babylon_step_floor_bound x z4 m hz4Pos hmlo
  have hz5Pos : 0 < z5 := Nat.lt_of_lt_of_le hm hmz5
  have hd5 : z5 - m ≤ d5 i := by
    have h := step_from_bound x m (loOf i) z4 (d4 i) hm (lo_pos i) hlo hmhi hmz4 hd4 hd4m
    simpa [z5, d5, nextD] using h
  have hd5m : d5 i ≤ m := Nat.le_trans (d5_le_lo i) hlo

  have hmz6 : m ≤ z6 := by
    dsimp [z6]
    exact babylon_step_floor_bound x z5 m hz5Pos hmlo
  have hd6 : z6 - m ≤ d6 i := by
    have h := step_from_bound x m (loOf i) z5 (d5 i) hm (lo_pos i) hlo hmhi hmz5 hd5 hd5m
    simpa [z6, d6, nextD] using h

  simpa [run6From, z1, z2, z3, z4, z5, z6] using hd6

theorem run6_le_m_plus_one
    (i : Fin 256)
    (x m : Nat)
    (hm : 0 < m)
    (hmlo : m * m ≤ x)
    (hmhi : x < (m + 1) * (m + 1))
    (hlo : loOf i ≤ m)
    (hhi : m ≤ hiOf i) :
    run6From x (seedOf i) ≤ m + 1 := by
  have herr := run6_error_le_cert i x m hm hmlo hmhi hlo hhi
  have hsub : run6From x (seedOf i) - m ≤ 1 := Nat.le_trans herr (d6_le_one i)
  have hzle : run6From x (seedOf i) ≤ 1 + m := (Nat.sub_le_iff_le_add).1 hsub
  omega

end SqrtCertified
