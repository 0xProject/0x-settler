import LnProof.ErrorBoundCore

/-! Compute the tight bias cap numerator + the errLtW/errGeW constants for the
current BIASc + boundNum.  `errGeW` uses the GE-internal margin (692115493) at
which the GE cells were generated; `errLtW` uses the published `minPosAvail`. -/

open LnExp LnFloor LnGeneratedModel LnFloorCert LnPoly

#eval do
  let bcap := (LnExp.expNum 130 (BIASc * 2 ^ 27) QS * (10 ^ 18 * 10 ^ 42)) / (LnExp.fact 130 * QS ^ 130)
  let mpaGe := 692115493 * 2 ^ 99 + 2 ^ 27 * 10 ^ 9
  IO.println s!"BIASCAPNUM={bcap}"
  IO.println s!"minPosAvail={minPosAvail}"
  IO.println s!"errLtW={bcap * (lnErrQ + minPosAvail) * wadRayStrictDen * 10 ^ 40}"
  IO.println s!"errGeW={bcap * (lnErrQ + mpaGe) * wadRayStrictDen * 10 ^ 40}"
