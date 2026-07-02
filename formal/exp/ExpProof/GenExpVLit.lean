import ExpProof.Floor.CertDefsV
import Common.Foundation.KroneckerShift

/-!
# Cert literal + cover generator for the **v-form** reduced-argument Taylor caps

Computes the never-over (`certExpUp`) and not-two-below (`certExpLo`) v-form certificate polynomials
from the symbolic `ExpCertV` definitions, emits the building-block + cert literal coefficient lists
(`Cert/ExpVCertLit.lean`), then greedily walks `[0, H128]` for each — exactly the predicate the
in-kernel `checkCoverK` decides — and writes one `Cert/ExpV{Up,Lo,…}C<NN>.lean` cell file per sub-cell
plus the cover module with the symbolic-cert↔literal equality and the `_nonneg` ladder.

Run with `lake env lean GenExpVLit.lean` after `lake build ExpProof.Floor.CertDefsV`. Output is
deterministic (byte-identical on re-run). Only the generated `Cert/ExpV*` files are machine output;
this generator and the hand-written `Floor/CertDefsV.lean` symbolic definitions are tracked.
-/

open Common.Poly ExpCertV

namespace GenExpVLit

/-- Drop trailing zero coefficients. -/
def ptrim (a : List Int) : List Int :=
  let r := (a.reverse.dropWhile (· == 0)).reverse
  if r.isEmpty then [0] else r

/-- Largest `w ∈ [0, hiW]` with `0 ≤ (hornerIv S 0 w).1` (non-increasing in `w`). -/
partial def maxW (S : List Int) (hiW : Int) : Int :=
  let rec bs (lo hi : Int) : Int :=
    if lo ≥ hi then lo
    else let mid := (lo + hi + 1) / 2
         if 0 ≤ (hornerIv S 0 mid).1 then bs mid hi else bs lo (mid - 1)
  bs 0 hiW

/-- Greedy walk → `(reached?, (anchor, width) list)`. -/
partial def walk (C : List Int) (lo hi : Int) : Bool × List (Int × Int) :=
  let rec go (a : Int) (fuel : Nat) (acc : List (Int × Int)) : Bool × List (Int × Int) :=
    match fuel with
    | 0 => (false, acc.reverse)
    | fuel + 1 =>
      if a > hi then (true, acc.reverse)
      else
        let S := kShiftWitness kB C a
        if 0 ≤ (hornerIv S 0 0).1 then
          let w := maxW S (hi - a)
          go (a + w + 1) fuel ((a, w) :: acc)
        else (false, ((a, -1) :: acc).reverse)
  go lo 200000 []

def pad2 (i : Nat) : String := (if i < 10 then "0" else "") ++ toString i

/-- Walk `[lo, hi]`, write one cell file per sub-cell, then write the cover module. -/
def emit (litName coverMod modPrefix cellPrefix certEqName litNonneg symNonneg symName eqTac : String)
    (C : List Int) (lo hi : Int) : IO Unit := do
  let (ok, cells) := walk C lo hi
  IO.println s!"-- {coverMod}: reached={ok} ncells={cells.length}"
  if ! ok then IO.println s!"-- FAILED tail: {cells.drop (cells.length - 2)}"; return
  for (aw, i) in cells.zipIdx do
    let (a, w) := aw
    IO.FS.writeFile s!"ExpProof/Cert/{modPrefix}{pad2 i}.lean"
      s!"import ExpProof.Cert.ExpVCertLit\nimport Common.Foundation.KroneckerShift\n\nnamespace ExpCertV\nopen Common.Poly\n\nset_option maxRecDepth 100000\n\ntheorem {cellPrefix}{pad2 i} : checkCoverK kB {litName} {a} {a + w}\n    [{w}] = true := by\n  decide +kernel\n\nend ExpCertV\n"
  let lb := "{"; let rb := "}"
  let mut s := "import ExpProof.Floor.CertDefsV\nimport ExpProof.Cert.ExpVCertLit\nimport Common.Foundation.KroneckerShift\n"
  for (_, i) in cells.zipIdx do s := s ++ s!"import ExpProof.Cert.{modPrefix}{pad2 i}\n"
  s := s ++ s!"\nnamespace ExpCertV\nopen Common.Poly\n\nset_option maxRecDepth 100000\n\n"
  s := s ++ s!"theorem {certEqName} : {symName} = {litName} := by\n{eqTac}\n\n"
  s := s ++ s!"theorem {litNonneg} {lb}t : Int{rb} (h1 : {lo} ≤ t) (h2 : t ≤ {hi}) :\n"
  s := s ++ s!"    0 ≤ evalPoly {litName} t := by\n"
  let n := cells.length
  for (aw, i) in cells.zipIdx do
    let (a, w) := aw
    if i + 1 < n then
      s := s ++ s!"  rcases Int.lt_or_le t ({a + w} + 1) with h | h\n  · exact checkCoverK_sound _ _ _ _ _ {cellPrefix}{pad2 i} t (by omega) (by omega)\n"
    else
      s := s ++ s!"  exact checkCoverK_sound _ _ _ _ _ {cellPrefix}{pad2 i} t (by omega) h2\n"
  s := s ++ s!"\ntheorem {symNonneg} {lb}t : Int{rb} (h1 : {lo} ≤ t) (h2 : t ≤ {hi}) :\n"
  s := s ++ s!"    0 ≤ evalPoly {symName} t := by\n  rw [{certEqName}]; exact {litNonneg} h1 h2\n"
  s := s ++ "\nend ExpCertV\n"
  IO.FS.writeFile s!"ExpProof/Cert/{coverMod}.lean" s

def litText (name : String) (c : List Int) : String :=
  "def " ++ name ++ " : List Int := [\n  " ++
    String.intercalate ",\n  " (c.map toString) ++ "]\n\n"

end GenExpVLit

open GenExpVLit

/-- Tactic block proving `certExpUp = certExpUpLit`. -/
def upEqTac : String :=
  "  have hy : yUB = yUBLit := by unfold yUB numExpV evNumVPoly todNumV odNumVPoly mulT2; decide +kernel\n" ++
  "  have hw : wUB = wUBLit := by unfold wUB denExpV evNumVPoly todNumV odNumVPoly mulT2; decide +kernel\n" ++
  "  have ht : tailUp = tailUpLit := by unfold tailUp expN27; decide +kernel\n" ++
  "  unfold certExpUp\n  rw [hy, hw, ht]\n  decide +kernel"

/-- Tactic block proving `certExpLo = certExpLoLit`. -/
def loEqTac : String :=
  "  have he : expN27 = expN27Lit := by unfold expN27; decide +kernel\n" ++
  "  have hy : yLB = yLBLit := by unfold yLB numExpV evNumVPoly todNumV odNumVPoly mulT2; decide +kernel\n" ++
  "  have hw : wLB = wLBLit := by unfold wLB denExpV evNumVPoly todNumV odNumVPoly mulT2; decide +kernel\n" ++
  "  unfold certExpLo\n  rw [he, hy, hw]\n  decide +kernel"

/-- Tactic block proving `numExpV = numExpVLit`. -/
def numEqTac : String :=
  "  unfold numExpV evNumVPoly todNumV odNumVPoly mulT2\n  decide +kernel"

/-- Tactic block proving `certDenM1 = certDenM1Lit`. -/
def denM1EqTac : String :=
  "  unfold certDenM1 denExpV evNumVPoly todNumV odNumVPoly mulT2\n  decide +kernel"

/-- Tactic block proving `certDOver = certDOverLit`. -/
def dOverEqTac : String :=
  "  unfold certDOver certDOverP evVPoly odVPoly\n  decide +kernel"

/-- Tactic block proving `certDOverP T D = certDOvP<NN>Lit`. -/
def dOverPEqTac : String :=
  "  unfold certDOverP evVPoly odVPoly\n  decide +kernel"

/-- Tactic block proving `certDUnderP T D = certDUnP<NN>Lit`. -/
def dUnderPEqTac : String :=
  "  unfold certDUnderP evVPoly odVPoly\n  decide +kernel"

/-- The 32 granularity pieces: `(vlo, vhi, T, DOver, DUnder)` — the `v`-range, the piece `t`-cap
(`T² ≥ (vhi+1)·2^133`), and the floored denominators for the two halves. Each piece's floors are
certified over `[vlo, vhi + 1]` (the granularity step looks one cell ahead). -/
def granPieces : List (Int × Int × Int × Int × Int) := [
  (0, 39914474797457073157829141722193111, 20847785078312632088902884100098393904, 650161701553, 691253358954),
  (39914474797457073157829141722193111, 79828949594914146315658283444386223, 29483220403189161767243017845519310570, 641945658278, 700065691212),
  (79828949594914146315658283444386223, 119743424392371219473487425166579335, 36109422980913784159270707268699614620, 635708060030, 706899646710),
  (119743424392371219473487425166579335, 159657899189828292631316566888772447, 41695570156625264177805768200196787807, 630494171758, 712709960499),
  (159657899189828292631316566888772447, 199572373987285365789145708610965559, 46617064615412821983671927489259435287, 625934238048, 717866387998),
  (199572373987285365789145708610965559, 239486848784742438946974850333158671, 51066435709074987640046250875008841866, 621838651900, 722558536211),
  (239486848784742438946974850333158671, 279401323582199512104803992055351783, 55158054703738454765934460694358669515, 618094793288, 726899025166),
  (279401323582199512104803992055351783, 319315798379656585262633133777544895, 58966440806378323534486035691038621139, 614629293866, 730961223213),
  (319315798379656585262633133777544895, 359230273177113658420462275499738007, 62543355234937896266708652300295181711, 611391198603, 734796085384),
  (359230273177113658420462275499738007, 399144747974570731578291417221931119, 65926485017139723075679505829736200590, 608343412382, 738440706802),
  (399144747974570731578291417221931119, 439059222772027804736120558944124231, 69144280814733066627417644920644591155, 605457935097, 741923087576),
  (439059222772027804736120558944124231, 478973697569484877893949700666317343, 72218845961827568318541414537399229239, 602713016329, 745264978126),
  (478973697569484877893949700666317343, 518888172366941951051778842388510455, 75167758079709234538337434275175078691, 600091361400, 748483673135),
  (518888172366941951051778842388510455, 558802647164399024209607984110703567, 78005269036144011942405564982788931618, 597578949702, 751593193213),
  (558802647164399024209607984110703567, 598717121961856097367437125832896679, 80743124413616312505576435261721815008, 595164227770, 754605091830),
  (598717121961856097367437125832896679, 638631596759313170525266267555089791, 83391140313250528355611536400393575614, 592837541332, 757529023260),
  (638631596759313170525266267555089791, 678546071556770243683095409277282902, 85957619938058733268340145980060814334, 590590725148, 760373152745),
  (678546071556770243683095409277282902, 718460546354227316840924550999476014, 88449661209567485301729053536557931646, 588416800156, 763144459353),
  (718460546354227316840924550999476014, 758375021151684389998753692721669126, 90873388353019950250431101958484117810, 586309745473, 765848963968),
  (758375021151684389998753692721669126, 798289495949141463156582834443862238, 93234129230825643967343854978518870515, 584264323835, 768491903858),
  (798289495949141463156582834443862238, 838203970746598536314411976166055350, 95536553193538501370371342040089081115, 582275945893, 771077868376),
  (838203970746598536314411976166055350, 878118445544055609472241117888248462, 97784779688729301059274137358180034302, 580340563312, 773610905858),
  (878118445544055609472241117888248462, 918032920341512682630070259610441574, 99982464869820254414073625773477941119, 578454583528, 776094608873),
  (918032920341512682630070259610441574, 957947395138969755787899401332634686, 102132871418149975280092501750017683679, 576614801025, 778532182941),
  (957947395138969755787899401332634686, 997861869936426828945728543054827798, 104238925391563160444514420500491969466, 574818341390, 780926502475),
  (997861869936426828945728543054827798, 1037776344733883902103557684777020910, 106303262929504594869818257246985820007, 573062615355, 783280156749),
  (1037776344733883902103557684777020910, 1077690819531340975261386826499214022, 108328268942741352477812121806098843808, 571345280717, 785595487968),
  (1077690819531340975261386826499214022, 1117605294328798048419215968221407134, 110316109407476909531868921388717338981, 569664210570, 787874623042),
  (1117605294328798048419215968221407134, 1157519769126255121577045109943600246, 112268758510433036404380164835338032221, 568017466591, 790119500297),
  (1157519769126255121577045109943600246, 1197434243923712194734874251665793358, 114188021614114346553315397742450038434, 566403276447, 792331892069),
  (1197434243923712194734874251665793358, 1237348718721169267892703393387986470, 116075554802968570681645777137735089747, 564820014566, 794513423933),
  (1237348718721169267892703393387986470, 1277263193518626341050532535110179582, 117932881612756647068972071382077242231, 563266185678, 796665591163)]

#eval do
  let cUp := ptrim certExpUp
  let cLo := ptrim certExpLo
  let mut lits :=
    ("/-! Generated v-form cut-certificate literal coefficient lists. -/\n\nnamespace ExpCertV\n\n" ++
      litText "numExpVLit" (ptrim numExpV) ++
      litText "denExpVLit" (ptrim denExpV) ++
      litText "expN27Lit" (ptrim expN27) ++
      litText "tailUpLit" (ptrim tailUp) ++
      litText "yUBLit" (ptrim yUB) ++
      litText "wUBLit" (ptrim wUB) ++
      litText "yLBLit" (ptrim yLB) ++
      litText "wLBLit" (ptrim wLB) ++
      litText "certDenM1Lit" (ptrim certDenM1) ++
      litText "certExpUpLit" cUp ++
      litText "certExpLoLit" cLo ++
      litText "certDOverLit" (ptrim certDOver))
  for (p, i) in granPieces.zipIdx do
    let (_, _, t, dO, dU) := p
    lits := lits ++ litText s!"certDOvP{pad2 i}Lit" (ptrim (certDOverP t dO))
    lits := lits ++ litText s!"certDUnP{pad2 i}Lit" (ptrim (certDUnderP t dU))
  IO.FS.writeFile "ExpProof/Cert/ExpVCertLit.lean" (lits ++ "end ExpCertV\n")
  IO.println "v-form literals written"
  emit "certExpUpLit" "ExpVUp" "ExpVUpC" "expVUp_cell" "certExpUp_eq" "expVUpLit_nonneg"
    "expVUp_nonneg" "certExpUp" upEqTac cUp 0 (H128 : Int)
  emit "certExpLoLit" "ExpVLo" "ExpVLoC" "expVLo_cell" "certExpLo_eq" "expVLoLit_nonneg"
    "expVLo_nonneg" "certExpLo" loEqTac cLo 0 (H128 : Int)
  emit "numExpVLit" "ExpVNum" "ExpVNumC" "expVNum_cell" "numExpV_eq" "numExpVLit_nonneg"
    "numExpV_nonneg" "numExpV" numEqTac (ptrim numExpV) 0 (H128 : Int)
  emit "certDenM1Lit" "ExpVDenM1" "ExpVDenM1C" "expVDenM1_cell" "certDenM1_eq" "denM1VLit_nonneg"
    "denM1V_nonneg" "certDenM1" denM1EqTac (ptrim certDenM1) 0 (H128 : Int)
  emit "certDOverLit" "ExpVDOver" "ExpVDOverC" "expVDOver_cell" "certDOver_eq" "dOverVLit_nonneg"
    "dOverV_nonneg" "certDOver" dOverEqTac (ptrim certDOver) 0 ((vmaxV : Int) + 1)
  for (p, i) in granPieces.zipIdx do
    let (vlo, vhi, t, dO, dU) := p
    emit s!"certDOvP{pad2 i}Lit" s!"ExpVDOvP{pad2 i}" s!"ExpVDOvP{pad2 i}C" s!"dOvP{pad2 i}_cell"
      s!"certDOvP{pad2 i}_eq" s!"dOvP{pad2 i}Lit_nonneg" s!"dOvP{pad2 i}_nonneg"
      s!"(certDOverP {t} {dO})" dOverPEqTac (ptrim (certDOverP t dO)) vlo (vhi + 1)
    emit s!"certDUnP{pad2 i}Lit" s!"ExpVDUnP{pad2 i}" s!"ExpVDUnP{pad2 i}C" s!"dUnP{pad2 i}_cell"
      s!"certDUnP{pad2 i}_eq" s!"dUnP{pad2 i}Lit_nonneg" s!"dUnP{pad2 i}_nonneg"
      s!"(certDUnderP {t} {dU})" dUnderPEqTac (ptrim (certDUnderP t dU)) vlo (vhi + 1)
