import FLatticePaper.Tiles.CorrectedEvenPlacement
import FLatticePaper.Tiles.CorrectedCellsNear

/-! The two small squares in the pure-two corrected diagram, with the three upper bridge sites supplied by the stem. -/

namespace FLatticePaper.Tiles.CorrectedPureBridges

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open Standard JointFamily LCorrecProps LCorrecRecursion SurgicalWeak CorrectedColumnRuns CorrectedEvenPlacement

def grid : Tile := (Finset.Icc (0:ℤ) 2).product (Finset.Icc (0:ℤ) 2)
private def missing : Tile := {(0,0),(0,1),(1,0)}
private abbrev small := shift enlOdo.dom ((1,1):Site)

private theorem lower : oneTile ∪ small=grid := by decide
private theorem upper : small ∪ missing=grid := by decide

private theorem registers (j : ℕ) :
    regsAt (List.replicate (j+1) Digit.two)=(some (List.replicate j Digit.two),none) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [List.replicate_succ',WeakStepPaper.regsAt_snoc,ih]; rfl

/-- The lower bridge already gives all nine sites. At the upper bridge the final stem
tile supplies exactly the other three sites needed for the displayed square. -/
theorem grids (v : Word) (j : ℕ) (long : Bool) (hp : stemPrefix v=List.replicate (j+1) Digit.two) :
    let g := periods v
    let row := shift (column (stemE (stemPrefix v)) g.a (length v)) (g.row false false long)
    bridgePieces v true long=grid ∧ row ∪ bridgePieces v false long=row ∪ shift grid (g.bridge false false long) := by
  intro g row
  have o : W1Odd v=false := calc
    _ = W1Odd (stemPrefix v++List.replicate (trailingCount .three v) .three) :=
      congrArg W1Odd (JointRot.strip_append_replicate .three v).symm
    _ = W1Odd (stemPrefix v) := JointRot.W1Odd_append_replicate _ _ _ (by decide)
    _ = false := by rw [hp,W1Odd,AltRotStep.phase_replicate_two]; rfl
  have E : enlarged v=true := by simp [enlarged,hp,List.replicate_succ]
  have regs := registers j
  have st : stemE (stemPrefix v)=nstairN (2*(j:ℤ)+3) := by
    rw [hp]; simp only [stemE,regs,regOdo,domOdo]; exact SiteBase.oddTile_rep_two _
  have br : bridgeE (stemPrefix v)=oneTile := by rw [hp]; simp only [bridgeE,regs,regOdo,cellData,domOdo]
  have root : bridgePieces v true long=grid := by
    simp only [bridgePieces,o,E,Periods.bridge,Bool.false_eq_true,if_false,if_true,Bool.not_false,
      Bool.not_true,Bool.true_and,br,zero_add,AltRotStep.shift_zero]
    exact lower
  have top : bridgePieces v false long=shift small (g.bridge false false long) := by
    simp only [bridgePieces,o,E,Bool.true_and,Bool.not_false,if_true,Finset.empty_union,small,shift_shift]
    rw [add_comm]
  refine ⟨root,?_⟩
  let c := g.bridge false false long
  have exc (x : Site) (hx : x∈missing) : x+(g.a+g.b-g.v) ∈ stemE (stemPrefix v) := by
    rw [st]
    simp only [missing,Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl|rfl|rfl
    all_goals rw [nstairN,mem_shift,mem_nstairF (by omega)]
    all_goals left
    all_goals simp [g,periods,hp,vP1,vP2,vQ2,BaseTileProps.parents_two,texV1Odd,texV2]
    all_goals omega
  have included : shift missing c ⊆ row := by
    intro z hz
    apply mem_shift.mpr
    apply (mem_column _ _ _ _).mpr
    refine ⟨length v,le_rfl,?_⟩
    have val : z-g.row false false long-(length v:ℤ) • g.a=(z-c)+(g.a+g.b-g.v) := by
      have R : g.runA=(length v:ℤ) • g.a := rfl
      simp only [c,Periods.row,Periods.bridge,Bool.false_eq_true,if_false,sub_zero,R]
      abel
    rw [val]; exact exc _ (mem_shift.mp hz)
  rw [top,←upper,shift_union]
  ext z
  simp only [Finset.mem_union]
  exact ⟨fun h => h.elim Or.inl (fun y => Or.inr (Or.inl y)),
    fun h => h.elim Or.inl (fun y => y.elim Or.inr (fun q => Or.inl (included q)))⟩

end FLatticePaper.Tiles.CorrectedPureBridges
