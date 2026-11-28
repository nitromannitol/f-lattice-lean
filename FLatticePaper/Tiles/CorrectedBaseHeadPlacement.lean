import FLatticePaper.Tiles.CorrectedBaseEnds
import FLatticePaper.Tiles.CorrectedBasePieces

/-! The base head column in the same placement as the two extended polygons and their exceptional ends. -/

namespace FLatticePaper.Tiles.CorrectedBaseHeadPlacement

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open Standard JointFamily LCorrecProps LCorrecRecursion CorrectedColumnRuns
open CorrectedCellsBands CorrectedBaseEnds CorrectedEvenPlacement CorrectedPlacementFrames
open CorrectedPlacedSources CorrectedPlacedDiagram

def start (g : Periods) (one : Bool) : Site := if one then g.b+g.u else g.v
def copies (N : ℕ) (long : Bool) := 2*N-if long then 0 else 1

def lower (g : Periods) (one : Bool) : Site := start g one+g.u+(if one then ((0,-1):Site) else (2,-1))
def upper (g : Periods) (one : Bool) (m : ℕ) : Site :=
  start g one+g.b+g.u+(if one then ((-2,0):Site) else 0)+(m:ℤ) • g.b

def holes (g : Periods) (one : Bool) (m : ℕ) (z : Site) : Prop :=
  z≠lower g one ∧ z≠lower g one+((0,1):Site) ∧ z≠upper g one m ∧ z≠upper g one m+((0,1):Site)

def strips (g : Periods) (one : Bool) (d : ℤ) (m : ℕ) (z : Site) : Prop :=
  strip d m (z-(start g one+g.b)) ∨ strip d m (z-(start g one+g.a+((0,-2):Site)))

theorem phase (v w : Word) (one : Bool) (pre : stemPrefix v=w++[exit one])
    (sign : -(parentsAt w).odd.det (parentsAt w).even=1) : W1Odd v=one := by
  have h := orientation_phase v w one pre
  rw [sign] at h
  cases one <;> cases o : W1Odd v <;> simp_all [CorrectedRegisterDiagram.orientation]

theorem head_start (g : Periods) (one : Bool) : g.head one (!one)=start g one := by cases one <;> rfl

theorem three_axes (v : Word) (j : ℕ) (one : Bool) (pre : stemPrefix v=List.replicate (j+1) Digit.three++[exit one]) :
    let g := periods v
    let d := 2*((j:ℤ)+1)+2
    g.a=(2*d,2) ∧ g.b=(1-d,d+1) ∧ g.u=(d+(if one then 1 else -1),1) ∧ g.v=(1-(d+(if one then 1 else -1)),1+(d+(if one then 1 else -1))) := by
  cases one <;> dsimp only <;> refine ⟨?_,?_,?_,?_⟩
  all_goals ext <;> simp [periods,pre,exit,vP1,vP2,vQ1,vQ2,parentsAt_append_singleton,Parents.step,
    Parents.current,Parents.combine,BaseTileProps.parents_three,texV1Odd,texV1Even,texV2] <;> ring

/-- Both extended polygons of the pure-three head, with the exceptions at their actual placements. -/
theorem three (v : Word) (j : ℕ) (one long : Bool) (pre : stemPrefix v=List.replicate (j+1) Digit.three++[exit one]) (z : Site) :
    let g := periods v
    let m := copies (length v) long
    let P := fun i => (diagram g (length v) one 1 long i).mem z
    z-start g one ∈ column (headE (stemPrefix v)) g.b m ↔
      (P 7 ∨ P 8) ∧ holes g one m z := by
  intro g m P
  let d : ℤ := 2*((j:ℤ)+1)+2
  obtain ⟨A,B,U,V⟩ := three_axes v j one pre
  change g.a=(2*d,2) at A
  change g.b=(1-d,d+1) at B
  change g.u=(d+(if one then 1 else -1),1) at U
  change g.v=(1-(d+(if one then 1 else -1)),1+(d+(if one then 1 else -1))) at V
  have ex : exit one=.one ∨ exit one=.two := by cases one <;> simp [exit]
  have fromBase := CorrectedBaseEnds.three_column j m (exit one) ex (z-start g one)
  dsimp only at fromBase
  have nonzero : CorrectedDomainLattice.scale (⟨1,d⟩ : Fraction)≠0 := by
    unfold CorrectedDomainLattice.scale
    have h : 4≤d := by dsimp [d]; omega
    nlinarith [sq_nonneg d]
  have ne (x y : Site) : coords ⟨1,d⟩ x≠coords ⟨1,d⟩ y ↔ x≠y :=
    not_congr ((coords_injective _ nonzero).eq_iff)
  change (_ ∈ _ ↔ (_ ∨ _) ∧ coords ⟨1,d⟩ _≠coords ⟨1,d⟩ _ ∧
    coords ⟨1,d⟩ _≠coords ⟨1,d⟩ _ ∧ coords ⟨1,d⟩ _≠coords ⟨1,d⟩ _ ∧ coords ⟨1,d⟩ _≠coords ⟨1,d⟩ _) at fromBase
  simp only [ne] at fromBase
  rw [pre,B]
  refine fromBase.trans ?_
  obtain ⟨x,y⟩ := z
  cases one
  all_goals simp only [P,diagram,Block.mem,CorrectedRegisterDiagram.orientation,
    Bool.not_true,Bool.not_false,Bool.false_eq_true,if_true,if_false,Periods.head,start,
    holes,lower,upper,A,B,U,V,Prod.mk_add_mk,Prod.mk_sub_mk,Prod.smul_mk,smul_eq_mul]
  all_goals dsimp only [d,m,copies]
  all_goals norm_num [Prod.ext_iff,Prod.fst_add,Prod.snd_add,Prod.fst_sub,Prod.snd_sub,Prod.mk_add_mk,Prod.mk_sub_mk,Nat.cast_add]
  all_goals ring_nf
  all_goals grind
theorem two_axes (v : Word) (j : ℕ) (one : Bool) (pre : stemPrefix v=List.replicate j Digit.two++[exit one]) :
    let g := periods v
    let d := (j:ℤ)+2
    g.a=(2*d,2*d-2) ∧ g.b=(-1,2*d-1) ∧ g.u=(if one then (2*d-1,2*d-3) else (1,1)) ∧ g.v=(if one then (-2,4*d-4) else (0,2)) := by
  cases one <;> dsimp only <;> refine ⟨?_,?_,?_,?_⟩
  all_goals ext <;> simp [periods,pre,exit,vP1,vP2,vQ1,vQ2,parentsAt_append_singleton,Parents.step,
    Parents.current,Parents.combine,BaseTileProps.parents_two,texV1Odd,texV1Even,texV2] <;> ring

/-- Both extended polygons of the pure-two head, with the exceptions at their actual placements. -/
theorem two (v : Word) (j : ℕ) (one long : Bool) (pre : stemPrefix v=List.replicate j Digit.two++[exit one]) (z : Site) :
    let g := periods v
    let m := copies (length v) long
    let P := fun i => (diagram g (length v) one 1 long i).mem z
    z-start g one ∈ column (headE (stemPrefix v)) g.b m ↔
      (P 7 ∨ P 8) ∨ strips g one ((j:ℤ)+2) m z := by
  intro g m P
  let d : ℤ := (j:ℤ)+2
  obtain ⟨A,B,U,V⟩ := two_axes v j one pre
  change g.a=(2*d,2*d-2) at A
  change g.b=(-1,2*d-1) at B
  change g.u=(if one then (2*d-1,2*d-3) else (1,1)) at U
  change g.v=(if one then (-2,4*d-4) else (0,2)) at V
  have ex : exit one=.one ∨ exit one=.two := by cases one <;> simp [exit]
  have fromBase := CorrectedBaseEnds.two_column j m (exit one) ex (z-start g one)
  dsimp only at fromBase
  rw [pre,B]
  refine fromBase.trans ?_
  obtain ⟨x,y⟩ := z
  cases one
  all_goals simp only [P,diagram,Block.mem,CorrectedRegisterDiagram.orientation,
    Bool.not_true,Bool.not_false,Bool.false_eq_true,if_true,if_false,Periods.head,start,
    strips,A,B,U,V,Prod.mk_add_mk,Prod.mk_sub_mk,Prod.smul_mk,smul_eq_mul]
  all_goals dsimp only [d,m,copies]
  all_goals norm_num [Prod.ext_iff,Prod.fst_add,Prod.snd_add,Prod.fst_sub,Prod.snd_sub,Prod.mk_add_mk,Prod.mk_sub_mk,Nat.cast_add]
  all_goals ring_nf


end FLatticePaper.Tiles.CorrectedBaseHeadPlacement
