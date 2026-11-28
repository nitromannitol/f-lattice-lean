import FLatticePaper.Tiles.CorrectedPlacedSources
import FLatticePaper.Tiles.CorrectedFirstPolygons

/-! The two alternate polygons in the preceding head and in the elongated target. -/

namespace FLatticePaper.Tiles.CorrectedAlternatePolygons

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open Standard JointFamily LCorrecProps LCorrecRecursion SurgicalWeak
open CorrectedCellsBands CorrectedHeadColumn CorrectedEvenPlacement CorrectedPlacementFrames
open CorrectedPlacedSources CorrectedPlacedDiagram CorrectedRegisterDiagram CorrectedChildColumns

/-- The two polygons with the common sum of the two primitive sides, at their actual corners. -/
def MixedAt (w : Word) (even : Bool) : Prop :=
  let P := parentsAt w
  let e := -P.odd.det P.even
  let a := vP1 w+vQ1 w
  let b := vP2 w+vQ2 w
  let gap := vP2 w+(if even then -e else e) • vQ1 w
  ∀ z, z ∈ (if even then altEvenT w else altOddT w) ↔ Band a b 0 0 z ∨ Band a b 0 0 (z-gap)

/-- The first non-base word has the required pair of actual alternate polygons in either family. -/
theorem first (even : Bool) : MixedAt [.one] even := by
  cases even
  · exact CorrectedFirstPolygons.odd
  · exact CorrectedFirstPolygons.even

/-- Passing to the next register identifies both axes and the displacement between the
two polygons of the preceding alternate head. -/
theorem head (v w : Word) (one : Bool) (pre : stemPrefix v=w++[exit one]) (h : MixedAt w false) :
    HeadPair v one (-(parentsAt w).odd.det (parentsAt w).even) := by
  let g := periods v
  let prev := -(parentsAt w).odd.det (parentsAt w).even
  have A : sibling g one=vP1 w+vQ1 w := by
    cases one <;> ext <;>
      simp [g,sibling,periods,pre,exit,vP1,vQ1,parentsAt_append_singleton,Parents.step,Parents.current,
        Parents.combine,texV1Odd,texV1Even] <;> ring
  have B : g.b=vP2 w+vQ2 w := by
    cases one <;> ext <;>
      simp [g,periods,pre,exit,vP2,vQ2,parentsAt_append_singleton,Parents.step,Parents.current,
        Parents.combine,texV2] <;> ring
  have u : (if one then g.a-g.u else g.u)=vQ1 w := by
    cases one <;> ext <;>
      simp [g,periods,pre,exit,vP1,vQ1,parentsAt_append_singleton,Parents.step,Parents.current,
        Parents.combine,texV1Odd,texV1Even] <;> ring
  have b : (if one then g.v-g.b else g.b-g.v)=vP2 w := by
    cases one <;> ext <;>
      simp [g,periods,pre,exit,vP2,vQ2,parentsAt_append_singleton,Parents.step,Parents.current,
        Parents.combine,texV2] <;> ring
  have parent : headE (stemPrefix v)=altOddT w := by
    rw [pre]; cases one <;> simp only [exit,headE,WeakStepPaper.regsAt_snoc,regStep,regOdo,domOdo,
      if_true,if_false,Bool.false_eq_true]
  intro z
  change z ∈ headE (stemPrefix v) ↔ Band (sibling g one) g.b 0 0 z ∨ Band (sibling g one) g.b 0 0 (z-gap g one prev)
  rw [parent,A,B,gap,u,b]
  exact h z

/-- The translated elongated target consists of precisely entries zero and nine whenever
the two-polygon description holds at this child. -/
theorem target (v w : Word) (one : Bool) (pre : stemPrefix v=w++[exit one]) (h : MixedAt (v++[.three]) true) (z : Site) :
    let g := periods v
    let prev := -(parentsAt w).odd.det (parentsAt w).even
    let piece := diagram g (length v) one prev true
    z ∈ shift (altEvenT (v++[.three])) (g.origin (W1Odd v) true) ↔ (piece 0).mem z ∨ (piece 9).mem z := by
  intro g prev piece
  let u := v++[Digit.three]
  let p := stemPrefix v
  have ev := JointRot.strip_append_replicate Digit.three v
  have ew : p++List.replicate (length v) .three=u := by
    rw [length,List.replicate_succ',←List.append_assoc,ev]
  obtain ⟨a,b,A,B⟩ := ew ▸ three_periods p (length v)
  change vP1 u=g.a at a
  change vP2 u=g.b at b
  change vQ1 u=g.fullU at A
  change vQ2 u=g.fullV at B
  have det : -(parentsAt u).odd.det (parentsAt u).even=orientation one prev := by
    have D := SiteScope.det_parentsAt u
    have ph : W1Odd u=W1Odd v := JointRot.phase_snoc_three v
    have bound : phase u<2 := Nat.mod_lt _ (by decide)
    rw [orientation_phase v w one pre,←ph]
    rcases (show phase u=0 ∨ phase u=1 by omega) with H|H <;> simp [D,W1Odd,H]
  have o : decide (orientation one prev≠1)=W1Odd v := by
    rw [orientation_phase v w one pre]; cases W1Odd v <;> decide
  let c := g.origin (W1Odd v) true
  rw [mem_shift]
  have cell := h (z-c)
  change (z-c ∈ altEvenT u) ↔ Band (vP1 u+vQ1 u) (vP2 u+vQ2 u) 0 0 (z-c) ∨
     Band (vP1 u+vQ1 u) (vP2 u+vQ2 u) 0 0 (z-c-(vP2 u+-(-(parentsAt u).odd.det (parentsAt u).even) • vQ1 u)) at cell
  rw [det,a,b,A,B] at cell
  change z-c ∈ altEvenT u ↔ _
  rw [cell]
  simp only [piece,diagram,Block.mem,o,if_true,neg_smul,c]
  abel

end FLatticePaper.Tiles.CorrectedAlternatePolygons
