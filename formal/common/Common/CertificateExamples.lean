import Common.GenBernstein

namespace Common.CertificateExamples

open Common.Poly Common.GenCover Common.GenBernstein

set_option maxRecDepth 100000

def nonnegativeQuadratic : List Int := [1, 0, 1]
def nonnegativeQuadraticWeights : List Int := [1, 2, 101]

theorem quadraticCoverKCheck :
    checkCoverK kB nonnegativeQuadratic 0 10 [10] = true := by
  decide +kernel

theorem quadraticBernsteinCheck :
    checkBernsteinKWithWitness 9 nonnegativeQuadratic 0 10
      nonnegativeQuadraticWeights = true := by
  decide +kernel

theorem quadraticComputedBernsteinCheck :
    checkBernsteinK 9 nonnegativeQuadratic 0 10 = true := by
  decide +kernel

theorem quadraticCoverKNonneg : NonnegOn nonnegativeQuadratic 0 10 :=
  checkCoverK_nonnegOn kB nonnegativeQuadratic [10] 0 10 quadraticCoverKCheck

theorem quadraticBernsteinNonneg : NonnegOn nonnegativeQuadratic 0 10 :=
  checkBernsteinKWithWitness_nonnegOn 9 nonnegativeQuadratic 0 10
    nonnegativeQuadraticWeights quadraticBernsteinCheck

theorem quadraticMixedPartitionNonneg : NonnegOn nonnegativeQuadratic 0 10 := by
  exact NonnegOn.union
    (NonnegOn.restrict quadraticCoverKNonneg (by omega) (by omega : (4 : Int) ≤ 10))
    (NonnegOn.restrict quadraticBernsteinNonneg (by omega : (0 : Int) ≤ 5) (by omega))

theorem malformedBernsteinWitness :
    checkBernsteinKWithWitness 9 nonnegativeQuadratic 0 10 [] = false := by
  decide +kernel

theorem malformedBernsteinInterval :
    checkBernsteinKWithWitness 9 nonnegativeQuadratic 10 0
      nonnegativeQuadraticWeights = false := by
  decide +kernel

theorem insufficientBernsteinIdentityWidth :
    checkBernsteinKWithWitness 8 nonnegativeQuadratic 0 10
      nonnegativeQuadraticWeights = false := by
  decide +kernel

end Common.CertificateExamples
