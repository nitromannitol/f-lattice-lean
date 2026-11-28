import FLatticePaper.Tiles.CorrectedBaseHeadPlacement
import FLatticePaper.Tiles.CorrectedPureBridges

/-! The source union at a base predecessor in the placement used by the numerical diagram. -/

namespace FLatticePaper.Tiles.CorrectedBaseSourceForms

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles Standard
open JointFamily LCorrecProps LCorrecRecursion CorrectedColumnRuns CorrectedChildColumns
open CorrectedEvenPlacement CorrectedPlacedDiagram CorrectedPlacementFrames CorrectedBasePieces
open CorrectedBaseHeadPlacement

theorem regular (v w : Word) (one long : Bool) (pre : stemPrefix v=w++[exit one])
    (hn : ¬IsBase (stemPrefix v)) (sign : -(parentsAt w).odd.det (parentsAt w).even=1) (z : Site) :
    let g := periods v
    let P := fun i => (diagram g (length v) one 1 long i).mem z
    z∈shift (evenChild evenLCells v long) (g.origin (W1Odd v) long) ↔
      four P ∨ P 5 ∨ P 6 ∨ z-start g one∈column (headE (stemPrefix v)) g.b (copies (length v) long) := by
  intro g P
  have ph := CorrectedBaseHeadPlacement.phase v w one pre sign
  have det : decide (CorrectedRegisterDiagram.orientation one 1≠1)=W1Odd v := by rw [ph]; cases one <;> decide
  have S := sources v w one long pre _ _ rfl rfl z
  dsimp only at S
  rw [sign] at S
  have lo : z∈bridgePieces v true long ↔ P 5 := by
    have H := bridges v hn long true z
    simpa only [P,diagram,Block.mem,det,g] using H
  have hi : z∈bridgePieces v false long ↔ P 6 := by
    have H := bridges v hn long false z
    simpa only [P,diagram,Block.mem,det,g] using H
  rw [lo,hi,ph,head_start] at S
  rw [ph]
  exact S

theorem bridge_even {p : Fraction} {r : CorrectedRegisterDiagram.Register} {e : ℤ} {g : Periods} {N : ℕ} {long : Bool}
    (F : CorrectedPlacementFrames.Frame p r e g N) : CorrectedPhysicalFaces.EvenPoint (g.bridge false false long) := by
  cases long <;> simp only [Periods.bridge,Periods.center,Bool.false_eq_true,if_false,if_true,add_zero,sub_zero]
  all_goals repeat' first | exact F.a.even | exact F.b.even | exact F.u.even | exact F.v.even | exact F.fullV.even
                          | apply CorrectedPhysicalFaces.even_add | apply CorrectedPhysicalFaces.even_sub

theorem enlarged (v : Word) (j : ℕ) (long : Bool)
    (pre : stemPrefix v=List.replicate j .two++[exit false]) (z : Site) :
    let g := periods v
    let P := fun i => (diagram g (length v) false 1 long i).mem z
    z∈shift (evenChild evenLCells v long) (g.origin (W1Odd v) long) ↔
      four P ∨ z∈CorrectedPureBridges.grid ∨ z∈shift CorrectedPureBridges.grid (g.bridge false false long) ∨
      z-start g false∈column (headE (stemPrefix v)) g.b (copies (length v) long) := by
  intro g P
  have rep : stemPrefix v=List.replicate (j+1) .two := by rw [pre,List.replicate_succ']; rfl
  have sign : -(parentsAt (List.replicate j .two)).odd.det (parentsAt (List.replicate j .two)).even=1 := by
    simp [BaseTileProps.parents_two,Fraction.det]
  have ph := CorrectedBaseHeadPlacement.phase v _ false pre sign
  obtain ⟨lo,hi⟩ := CorrectedPureBridges.grids v j long rep
  have S := sources v _ false long pre _ _ lo (by simpa only [ph] using hi) z
  dsimp only at S
  rw [sign,ph,head_start] at S
  rw [ph]
  exact S

end FLatticePaper.Tiles.CorrectedBaseSourceForms
