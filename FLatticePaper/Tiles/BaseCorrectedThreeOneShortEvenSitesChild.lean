import FLatticePaper.Tiles.BaseCorrectedThreeOneShortEvenSitesFrame
import FLatticePaper.Tiles.BaseCorrectedThreeOneShortEvenSitesPolygons
import FLatticePaper.Tiles.BaseCorrectedThreeOneShortEvenSitesBoundary
import FLatticePaper.Tiles.CorrectedBaseTransport
import FLatticePaper.Tiles.CorrectedBaseSourceForms
import FLatticePaper.Tiles.CorrectedMixedBasePlacement

/-! The native source union and both of its inclusions at physical sites of this base exit. -/

namespace FLatticePaper.Tiles.BaseCorrectedThreeOneShortEvenSitesChild

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles Standard
open JointFamily LCorrecProps LCorrecRecursion CorrectedEvenPlacement CorrectedPlacementFrames
open CorrectedRegisterWords CorrectedRegisterDiagram CorrectedDomainLattice CorrectedWordCoverage
open CorrectedPlacedDiagram CorrectedChildColumns CorrectedColumnRuns CorrectedBaseHeadPlacement
open CorrectedBasePieces

theorem at_word (v : Word) (j : ℕ) (pre : stemPrefix v=List.replicate (j+1) Digit.three++[exit true]) (z : Site) (parity : CorrectedCellsBands.oddSite z=false) :
    CorrectedBaseTransport.Shows v true false z := by
  let w : Word := List.replicate (j+1) Digit.three
  let P := parentsAt w
  let p := P.current .odd
  let N := length v
  let g := periods v
  let r := register P true N (chart p (representative z))
  let D := fun i => (diagram g N true 1 false i).mem z
  let Q := fun i => CorrectedRegisterFaces.exact ((corrected r true 1 false i).probe r false 0)
  have hn : 0<N := Nat.succ_pos _
  have prev : -(parentsAt w).odd.det (parentsAt w).even=1 := by simp [w,BaseTileProps.parents_three,Fraction.det]
  have F : BaseCorrectedThreeOneShortEvenSites.Frame r := BaseCorrectedThreeOneShortEvenSitesFrame.at_word j N hn (representative z) (representative_even z)
  have positive : 0<r.M := by have h0 := F.f0; have h1 := F.f10; omega
  have orient (i : Fin 10) : let bb := diagram g N true 1 false i.val
      CorrectedPhysicalFaces.Aligned bb.a bb.b 0 := by
    have pre' : stemPrefix v=(Digit.three::List.replicate j .three)++[exit true] := by simpa only [List.replicate_succ] using pre
    exact CorrectedPlacedSectors.word .three _ v true false 1 pre' i
  have poly (i : Fin 10) : D i.val ↔ Q i.val := by
    have H := CorrectedBaseTransport.polygon v w true false 0 pre prev z i (orient i) positive
    dsimp only at H
    rw [parity] at H; exact H
  have read := CorrectedBaseProjection.word v w true pre z
  change CorrectedBaseProjection.Reading r g (orientation true (-(parentsAt w).odd.det (parentsAt w).even)) N z (CorrectedCellsBands.oddSite z) at read
  rw [prev,parity] at read
  have ends := BaseCorrectedThreeOneShortEvenSitesBoundary.ends r g N hn z read positive
  have nonbase : ¬IsBase (stemPrefix v) := by
    rw [pre]; exact CorrectedMixedBasePlacement.nonbase true true j (by decide)
  have S := CorrectedBaseSourceForms.regular v w true false pre nonbase prev z
  have col := CorrectedBaseHeadPlacement.three v j true false pre z
  dsimp only at S col
  have c0 : BaseCorrectedThreeOneShortEvenSites.contains r 0 ↔ D 0 :=
    (BaseCorrectedThreeOneShortEvenSitesPolygons.part0 r F).trans (poly 0).symm
  have c1 : BaseCorrectedThreeOneShortEvenSites.contains r 1 ↔ D 1 :=
    (BaseCorrectedThreeOneShortEvenSitesPolygons.part1 r F).trans (poly 1).symm
  have c2 : BaseCorrectedThreeOneShortEvenSites.contains r 2 ↔ D 2 :=
    (BaseCorrectedThreeOneShortEvenSitesPolygons.part2 r F).trans (poly 2).symm
  have c3 : BaseCorrectedThreeOneShortEvenSites.contains r 3 ↔ D 3 :=
    (BaseCorrectedThreeOneShortEvenSitesPolygons.part3 r F).trans (poly 3).symm
  have c4 : BaseCorrectedThreeOneShortEvenSites.contains r 4 ↔ D 4 :=
    (BaseCorrectedThreeOneShortEvenSitesPolygons.part4 r F).trans (poly 4).symm
  have c5 : BaseCorrectedThreeOneShortEvenSites.contains r 5 ↔ D 5 :=
    (BaseCorrectedThreeOneShortEvenSitesPolygons.part5 r F).trans (poly 5).symm
  have c6 : BaseCorrectedThreeOneShortEvenSites.contains r 6 ↔ D 6 :=
    (BaseCorrectedThreeOneShortEvenSitesPolygons.part6 r F).trans (poly 6).symm
  have c7 : BaseCorrectedThreeOneShortEvenSites.contains r 7 ↔ D 7 ∧ holes g true (copies N false) z :=
    (BaseCorrectedThreeOneShortEvenSitesPolygons.part7 r F).trans (and_congr (poly 7).symm ends.symm)
  have c8 : BaseCorrectedThreeOneShortEvenSites.contains r 8 ↔ D 8 ∧ holes g true (copies N false) z :=
    (BaseCorrectedThreeOneShortEvenSitesPolygons.part8 r F).trans (and_congr (poly 8).symm ends.symm)
  have covered := BaseCorrectedThreeOneShortEvenSites.coverage r F
  rw [c0, c1, c2, c3, c4, c5, c6, c7, c8] at covered
  change z∈shift _ _ ↔ D 0
  rw [S,col]
  change (CorrectedBasePieces.four D ∨ _ ∨ _ ∨ _) ↔ _
  unfold CorrectedBasePieces.four
  simpa only [or_and_right,or_assoc,or_left_comm,or_comm] using covered.symm

end FLatticePaper.Tiles.BaseCorrectedThreeOneShortEvenSitesChild
