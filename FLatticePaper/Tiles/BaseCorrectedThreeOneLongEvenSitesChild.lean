import FLatticePaper.Tiles.BaseCorrectedThreeOneLongEvenSitesFrame
import FLatticePaper.Tiles.BaseCorrectedThreeOneLongEvenSitesPolygons
import FLatticePaper.Tiles.BaseCorrectedThreeOneLongEvenSitesBoundary
import FLatticePaper.Tiles.CorrectedBaseTransport
import FLatticePaper.Tiles.CorrectedBaseSourceForms
import FLatticePaper.Tiles.CorrectedMixedBasePlacement

/-! The native source union and both of its inclusions at physical sites of this base exit. -/

namespace FLatticePaper.Tiles.BaseCorrectedThreeOneLongEvenSitesChild

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles Standard
open JointFamily LCorrecProps LCorrecRecursion CorrectedEvenPlacement CorrectedPlacementFrames
open CorrectedRegisterWords CorrectedRegisterDiagram CorrectedDomainLattice CorrectedWordCoverage
open CorrectedPlacedDiagram CorrectedChildColumns CorrectedColumnRuns CorrectedBaseHeadPlacement
open CorrectedBasePieces

theorem at_word (v : Word) (j : ℕ) (pre : stemPrefix v=List.replicate (j+1) Digit.three++[exit true]) (z : Site) (parity : CorrectedCellsBands.oddSite z=false) :
    CorrectedBaseTransport.Shows v true true z := by
  let w : Word := List.replicate (j+1) Digit.three
  let P := parentsAt w
  let p := P.current .odd
  let N := length v
  let g := periods v
  let r := register P true N (chart p (representative z))
  let D := fun i => (diagram g N true 1 true i).mem z
  let Q := fun i => CorrectedRegisterFaces.exact ((corrected r true 1 true i).probe r false 0)
  have hn : 0<N := Nat.succ_pos _
  have prev : -(parentsAt w).odd.det (parentsAt w).even=1 := by simp [w,BaseTileProps.parents_three,Fraction.det]
  have F : BaseCorrectedThreeOneLongEvenSites.Frame r := BaseCorrectedThreeOneLongEvenSitesFrame.at_word j N hn (representative z) (representative_even z)
  have positive : 0<r.M := by have h0 := F.f0; have h1 := F.f10; omega
  have orient (i : Fin 10) : let bb := diagram g N true 1 true i.val
      CorrectedPhysicalFaces.Aligned bb.a bb.b 0 := by
    have pre' : stemPrefix v=(Digit.three::List.replicate j .three)++[exit true] := by simpa only [List.replicate_succ] using pre
    exact CorrectedPlacedSectors.word .three _ v true true 1 pre' i
  have poly (i : Fin 10) : D i.val ↔ Q i.val := by
    have H := CorrectedBaseTransport.polygon v w true true 0 pre prev z i (orient i) positive
    dsimp only at H
    rw [parity] at H; exact H
  have read := CorrectedBaseProjection.word v w true pre z
  change CorrectedBaseProjection.Reading r g (orientation true (-(parentsAt w).odd.det (parentsAt w).even)) N z (CorrectedCellsBands.oddSite z) at read
  rw [prev,parity] at read
  have ends := BaseCorrectedThreeOneLongEvenSitesBoundary.ends r g N hn z read positive
  have nonbase : ¬IsBase (stemPrefix v) := by
    rw [pre]; exact CorrectedMixedBasePlacement.nonbase true true j (by decide)
  have S := CorrectedBaseSourceForms.regular v w true true pre nonbase prev z
  have col := CorrectedBaseHeadPlacement.three v j true true pre z
  dsimp only at S col
  have c0 : BaseCorrectedThreeOneLongEvenSites.contains r 0 ↔ D 0 :=
    (BaseCorrectedThreeOneLongEvenSitesPolygons.part0 r F).trans (poly 0).symm
  have c9 : BaseCorrectedThreeOneLongEvenSites.contains r 9 ↔ D 9 :=
    (BaseCorrectedThreeOneLongEvenSitesPolygons.part9 r F).trans (poly 9).symm
  have c1 : BaseCorrectedThreeOneLongEvenSites.contains r 1 ↔ D 1 :=
    (BaseCorrectedThreeOneLongEvenSitesPolygons.part1 r F).trans (poly 1).symm
  have c2 : BaseCorrectedThreeOneLongEvenSites.contains r 2 ↔ D 2 :=
    (BaseCorrectedThreeOneLongEvenSitesPolygons.part2 r F).trans (poly 2).symm
  have c3 : BaseCorrectedThreeOneLongEvenSites.contains r 3 ↔ D 3 :=
    (BaseCorrectedThreeOneLongEvenSitesPolygons.part3 r F).trans (poly 3).symm
  have c4 : BaseCorrectedThreeOneLongEvenSites.contains r 4 ↔ D 4 :=
    (BaseCorrectedThreeOneLongEvenSitesPolygons.part4 r F).trans (poly 4).symm
  have c5 : BaseCorrectedThreeOneLongEvenSites.contains r 5 ↔ D 5 :=
    (BaseCorrectedThreeOneLongEvenSitesPolygons.part5 r F).trans (poly 5).symm
  have c6 : BaseCorrectedThreeOneLongEvenSites.contains r 6 ↔ D 6 :=
    (BaseCorrectedThreeOneLongEvenSitesPolygons.part6 r F).trans (poly 6).symm
  have c7 : BaseCorrectedThreeOneLongEvenSites.contains r 7 ↔ D 7 ∧ holes g true (copies N true) z :=
    (BaseCorrectedThreeOneLongEvenSitesPolygons.part7 r F).trans (and_congr (poly 7).symm ends.symm)
  have c8 : BaseCorrectedThreeOneLongEvenSites.contains r 8 ↔ D 8 ∧ holes g true (copies N true) z :=
    (BaseCorrectedThreeOneLongEvenSitesPolygons.part8 r F).trans (and_congr (poly 8).symm ends.symm)
  have covered := BaseCorrectedThreeOneLongEvenSites.coverage r F
  rw [c0, c9, c1, c2, c3, c4, c5, c6, c7, c8] at covered
  change z∈shift _ _ ↔ D 0 ∨ D 9
  rw [S,col]
  change (CorrectedBasePieces.four D ∨ _ ∨ _ ∨ _) ↔ _
  unfold CorrectedBasePieces.four
  simpa only [or_and_right,or_assoc,or_left_comm,or_comm] using covered.symm

end FLatticePaper.Tiles.BaseCorrectedThreeOneLongEvenSitesChild
