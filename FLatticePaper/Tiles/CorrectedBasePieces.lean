import FLatticePaper.Tiles.CorrectedPlacedSources
import FLatticePaper.Tiles.CorrectedPureBridges

/-! The four full polygons, the two actual bridges and the base head column in one placement. -/

namespace FLatticePaper.Tiles.CorrectedBasePieces

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open Standard SurgicalWeak JointFamily JointRot LCorrecProps LCorrecRecursion
open CorrectedCellsBands CorrectedColumnRuns CorrectedHeadColumn CorrectedChildColumns
open CorrectedEvenPlacement CorrectedPlacementFrames CorrectedPlacedDiagram CorrectedPlacedSources

/-- The stem register is present at both possible exits, even on a pure run of twos. -/
theorem stem_band (v w : Word) (one : Bool) (pre : stemPrefix v=w++[exit one]) (z : Site) :
    let g := periods v
    z∈column (stemE (stemPrefix v)) g.a (length v) ↔ Band g.a g.b (length v) 0 z := by
  intro g
  let p := (parentsAt (stemPrefix v)).odd
  have reg : (regsAt (stemPrefix v)).1=some w := by
    rw [pre,WeakStepPaper.regsAt_snoc]; cases one <;> rfl
  have h := (parents_of_regs (stemPrefix v)).1 w reg
  have mem (y : Site) : y∈stemE (stemPrefix v) ↔ Band g.a g.b 0 0 y := by
    rw [stemE,reg]
    change y∈oddTile w ↔ Band (texV1Odd p) (texV2 p) 0 0 y
    rw [odd_band]
    simp only [p,SiteInduction.curO,h]
  obtain ⟨pd,pn,pm⟩ := (parentsAt_valid (stemPrefix v)).odd_bounds
  change 0<p.den at pd
  change 0≤p.num at pn
  change p.num≤p.den at pm
  have det : 0≤cross g.a g.b := by
    change 0≤cross (texV1Odd p) (texV2 p)
    dsimp [cross,texV1Odd,texV2]
    nlinarith only [mul_nonneg (show 0≤p.den by omega) (show 0≤p.den+p.num by omega),
      mul_nonneg pn (show 0≤p.den-p.num by omega)]
  have width : -g.b.1≤g.b.2 := by change -(p.num-p.den)≤p.num+p.den; omega
  have par : (g.a.1+g.a.2)%2=0 := by change (2*p.den+2*p.num)%2=0; omega
  exact horizontal_row _ _ _ _ par det width mem z

/-- The two unmodified bridges at any non-base exit, including a first exit after a pure run. -/
theorem bridges (v : Word) (hn : ¬IsBase (stemPrefix v)) (long plus : Bool) (z : Site) :
    let g := periods v
    z∈bridgePieces v plus long ↔ Band g.u g.v 0 0 (z-g.bridge (W1Odd v) plus long) := by
  intro g
  have small : enlarged v=false := by
    cases h : enlarged v
    · rfl
    · exfalso; apply hn; right; right
      simp only [enlarged,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at h
      exact h.2
  obtain ⟨_,⟨y,hy⟩⟩ := regs_some (stemPrefix v) hn
  have e := (parents_of_regs (stemPrefix v)).2 y hy
  simp only [bridgePieces,small,Bool.false_and,Bool.false_eq_true,if_false,Finset.union_empty,mem_shift,
    bridgeE,hy,regOdo,domOdo]
  rw [even_band]
  simp only [g,periods,vQ1,vQ2,SiteInduction.curE,e]

def four (P : ℕ → Prop) := P 1 ∨ P 2 ∨ P 3 ∨ P 4

/-- Four unchanged polygons together with a prescribed bridge replacement on each end and
the full alternate column. The upper replacement may share sites with the last stem row. -/
theorem sources (v w : Word) (one long : Bool) (pre : stemPrefix v=w++[exit one]) (lo hi : Tile)
    (lower : bridgePieces v true long=lo)
    (upper : let g := periods v
      let R := shift (column (stemE (stemPrefix v)) g.a (length v)) (g.row (W1Odd v) false long)
      R ∪ bridgePieces v false long=R ∪ hi) (z : Site) :
    let g := periods v
    let prev := -(parentsAt w).odd.det (parentsAt w).even
    let H := g.head (W1Odd v) (!one)
    let m := 2*length v-if long then 0 else 1
    z∈shift (evenChild evenLCells v long) (g.origin (W1Odd v) long) ↔
      four (fun i => (diagram g (length v) one prev long i).mem z) ∨ z∈lo ∨ z∈hi ∨
      z-H ∈ column (headE (stemPrefix v)) g.b m := by
  intro g prev H m
  have ph : decide (CorrectedRegisterDiagram.orientation one prev≠1)=W1Odd v := by
    rw [orientation_phase v w one pre]; cases W1Odd v <;> decide
  have ty : decide ((stemPrefix v).getLast?=some Digit.two)= !one := by
    rw [pre]; cases one <;> simp [exit]
  rw [CorrectedEvenPlacement.after_three]
  simp only [lower,upper]
  simp only [Finset.mem_union,mem_shift,full_band,stem_band v w one pre,ty,diagram,Block.mem,ph,four,H]
  tauto

end FLatticePaper.Tiles.CorrectedBasePieces
