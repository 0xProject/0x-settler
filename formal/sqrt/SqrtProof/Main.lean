import SqrtProof.FloorBound
import SqrtProof.StepMono
import SqrtProof.BridgeLemmas
import SqrtProof.FiniteCert
import SqrtProof.CertifiedChain
import SqrtProof.SqrtCorrect

open SqrtBridge
open SqrtCert
open SqrtCertified

private def linkFloorBound : Unit :=
  let _ := sq_identity_le
  let _ := sq_identity_ge
  let _ := mul_two_sub_le_sq
  let _ := two_mul_le_add_div_sq
  let _ := babylon_step_floor_bound
  let _ := babylon_from_ceil
  let _ := babylon_from_floor
  ()

private def linkStepMono : Unit :=
  let _ := babylonStep
  let _ := div_drop_le_one
  let _ := sum_nondec_step
  let _ := @babylonStep_mono_x
  let _ := babylonStep_mono_z
  let _ := babylonStep_lt_of_overestimate
  ()

private def linkBridgeLemmas : Unit :=
  let _ := SqrtBridge.bstep
  let _ := step_error_bound
  let _ := d1_bound
  ()

private def linkFiniteCert : Unit :=
  let _ := loTable
  let _ := hiTable
  let _ := seedOf
  let _ := loOf
  let _ := hiOf
  let _ := maxAbs
  let _ := d1
  let _ := nextD
  let _ := d2
  let _ := d3
  let _ := d4
  let _ := d5
  let _ := d6
  let _ := lo_pos
  let _ := d1_le_lo
  let _ := d2_le_lo
  let _ := d3_le_lo
  let _ := d4_le_lo
  let _ := d5_le_lo
  let _ := d6_le_one
  let _ := lo_sq_le_pow2
  let _ := pow2_succ_le_hi_succ_sq
  ()

private def linkCertifiedChain : Unit :=
  let _ := run6From
  let _ := step_from_bound
  let _ := run6_error_le_cert
  let _ := run6_le_m_plus_one
  ()

private def linkSqrtCorrect : Unit :=
  let _ := sqrtSeed
  let _ := innerSqrt
  let _ := floorSqrt
  let _ := maxProp
  let _ := checkOctave
  let _ := checkSeedPos
  let _ := checkUpperBound
  let _ := sqrtSeed_pos
  let _ := natSqrt
  let _ := natSqrt_spec
  let _ := natSqrt_sq_le
  let _ := natSqrt_lt_succ_sq
  let _ := innerSqrt_lower
  let _ := innerSqrt_eq_run6From
  let _ := innerSqrt_upper_cert
  let _ := innerSqrt_bracket_cert
  let _ := sqrtSeed_eq_seedOf_of_octave
  let _ := m_within_cert_interval
  let _ := innerSqrt_upper_of_octave
  let _ := innerSqrt_bracket_of_octave
  let _ := floor_correction
  let _ := innerSqrt_correct
  let _ := floorSqrt_correct
  let _ := floorSqrt_correct_cert
  let _ := floorSqrt_correct_of_octave
  let _ := innerSqrt_bracket_u256
  let _ := innerSqrt_bracket_u256_all
  let _ := floorSqrt_correct_u256
  let _ := sqrt_witness_correct_u256
  ()

/-- Aggregate linker anchor: if any referenced definition/theorem is missing or
    ill-typed, `lake exe sqrtproof` fails to build. -/
def proofLinked_all : Unit :=
  let _ := linkFloorBound
  let _ := linkStepMono
  let _ := linkBridgeLemmas
  let _ := linkFiniteCert
  let _ := linkCertifiedChain
  let _ := linkSqrtCorrect
  ()

theorem proofLinked_innerSqrt_bracket_u256_all :
    ∀ x : Nat, x < 2 ^ 256 →
      let m := natSqrt x
      m ≤ innerSqrt x ∧ innerSqrt x ≤ m + 1 :=
  innerSqrt_bracket_u256_all

theorem proofLinked_floorSqrt_correct_u256 :
    ∀ x : Nat, x < 2 ^ 256 →
      let r := floorSqrt x
      r * r ≤ x ∧ x < (r + 1) * (r + 1) :=
  floorSqrt_correct_u256

def main : IO Unit := do
  let _ := proofLinked_all
  IO.println "sqrtproof: linked to full proof surface."
  IO.println "sqrtproof: run `lake build` to kernel-check all imported modules."
