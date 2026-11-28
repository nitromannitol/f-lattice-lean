import FLatticePaper.Tiles.CorrectedPlacedDiagram

/-! Membership in the actual union of placed pieces after a three, in terms of its eight polygons. -/

namespace FLatticePaper.Tiles.CorrectedPlacedSources

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open Standard SurgicalWeak JointFamily JointRot LCorrecProps LCorrecRecursion
open CorrectedCellsBands CorrectedColumnRuns CorrectedHeadColumn CorrectedChildColumns
open CorrectedEvenPlacement CorrectedPlacementFrames CorrectedPlacedDiagram

def sibling (g : Periods) (one : Bool) := if one then g.u else g.a-g.u

def gap (g : Periods) (one : Bool) (prev : ℤ) : Site :=
  (if one then g.v-g.b else g.b-g.v)+prev • (if one then g.a-g.u else g.u)

/-- A two-polygon description of the actual odd alternate head in the old frame. -/
def HeadPair (v : Word) (one : Bool) (prev : ℤ) : Prop :=
  let g := periods v
  ∀ z, z ∈ headE (stemPrefix v) ↔ Band (sibling g one) g.b 0 0 z ∨
    Band (sibling g one) g.b 0 0 (z-gap g one prev)

private theorem last_periods (v : Word) :
    let w := v++[Digit.three]
    let g := periods v
    vP1 w=g.a ∧ vP2 w=g.b ∧ vQ1 w=g.fullU ∧ vQ2 w=g.fullV := by
  have ev := JointRot.strip_append_replicate Digit.three v
  have ew : stemPrefix v++List.replicate (length v) .three=v++[.three] := by
    rw [length,List.replicate_succ',←List.append_assoc,ev]
  exact ew ▸ three_periods (stemPrefix v) (length v)

/-- The axes of the full even tile after the run and of the odd standard target. -/
theorem full_band (v : Word) (z : Site) :
    z ∈ evenTile v ↔ Band (periods v).fullU (periods v).fullV 0 0 z := by
  have ⟨_,_,u,t⟩ := last_periods v
  rw [←u,←t,even_band]
  simp only [vQ1,vQ2,parentsAt_append_singleton,Parents.step,SiteInduction.curE]

theorem target_band (v : Word) (z : Site) :
    let g := periods v
    z ∈ oddTile (v++[.three]) ↔ Band (g.a+g.fullU+g.fullU) (g.b+g.fullV) 0 0 z := by
  obtain ⟨a,b,u,t⟩ := last_periods v
  dsimp only
  rw [←a,←b,←u,←t,odd_band]
  let P := parentsAt (v++[.three])
  have A : texV1Odd (P.current .odd)=texV1Odd P.odd+texV1Even P.even+texV1Even P.even := by
    ext <;> simp [Parents.current,Parents.combine,texV1Odd,texV1Even] <;> ring
  have B : texV2 (P.current .odd)=texV2 P.odd+texV2 P.even := by
    ext <;> simp [Parents.current,Parents.combine,texV2] <;> ring
  exact A ▸ B ▸ Iff.rfl

private theorem prefix_nonbase (v w : Word) (one : Bool) (pre : stemPrefix v=w++[exit one]) (h : ¬ IsBase w) :
    ¬ IsBase (stemPrefix v) := by
  rw [pre]
  rintro (e|all|all)
  · simp at e
  · exact h (Or.inr (Or.inl (fun d hd => all d (List.mem_append_left _ hd))))
  · exact h (Or.inr (Or.inr (fun d hd => all d (List.mem_append_left _ hd))))

private theorem no_enlargement (v : Word) (hn : ¬ IsBase (stemPrefix v)) : enlarged v=false := by
  cases h : enlarged v
  · rfl
  · exfalso; apply hn; right; right
    simp only [enlarged,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at h
    exact h.2

/-- Each standard register of a non-base prefix agrees with the physical band of its two periods. -/
private theorem registers (v : Word) (hn : ¬ IsBase (stemPrefix v)) (z : Site) :
    let g := periods v
    (z ∈ stemE (stemPrefix v) ↔ Band g.a g.b 0 0 z) ∧
    (z ∈ bridgeE (stemPrefix v) ↔ Band g.u g.v 0 0 z) := by
  obtain ⟨⟨x,hx⟩,⟨y,hy⟩⟩ := JointRot.regs_some _ hn
  have H := JointRot.parents_of_regs (stemPrefix v)
  have o := H.1 x hx
  have e := H.2 y hy
  simp only [stemE,bridgeE,hx,hy,regOdo,domOdo]
  change (z ∈ oddTile x ↔ Band (texV1Odd _) (texV2 _) 0 0 z) ∧
    (z ∈ evenTile y ↔ Band (texV1Even _) (texV2 _) 0 0 z)
  rw [odd_band,even_band]; simp only [SiteInduction.curO,SiteInduction.curE,o,e,and_self]

private theorem bounds (v w : Word) (one : Bool) (pre : stemPrefix v=w++[exit one]) :
    let g := periods v
    let s := sibling g one
    0 ≤ cross g.a g.b ∧ 0 ≤ cross s g.b ∧ s.2 ≤ s.1 ∧ -g.b.1 ≤ g.b.2 ∧
      (g.a.1+g.a.2)%2=0 ∧ (g.b.1+g.b.2)%2=0 := by
  let P := parentsAt w
  obtain ⟨pd,pn,ph⟩ := (parentsAt_valid w).odd_bounds
  obtain ⟨qd,qn,qh⟩ := (parentsAt_valid w).even_bounds
  change 0<P.odd.den at pd
  change 0<P.even.den at qd
  change 0≤P.odd.num at pn
  change 0≤P.even.num at qn
  change P.odd.num≤P.odd.den at ph
  change P.even.num≤P.even.den at qh
  dsimp only [P] at pd pn ph qd qn qh
  let g := periods v
  let s := sibling g one
  have H : 0 ≤ g.a.1 ∧ 0 ≤ g.a.2 ∧ 0 ≤ s.1 ∧ 0 ≤ s.2 ∧ g.b.1 ≤ 0 ∧ 0 ≤ g.b.2 ∧
      s.2 ≤ s.1 ∧ -g.b.1 ≤ g.b.2 ∧ (g.a.1+g.a.2)%2=0 ∧ (g.b.1+g.b.2)%2=0 := by
    cases one <;>
      simp [s,g,sibling,periods,vP1,vP2,vQ1,pre,parentsAt_append_singleton,exit,Parents.step,Parents.current,
        Parents.combine,texV1Odd,texV1Even,texV2] <;> omega
  obtain ⟨a₀,a₁,s₀,s₁,b₀,b₁,ws,wb,pa,pb⟩ := H
  have det {a : Site} (x : 0≤a.1) (y : 0≤a.2) : 0 ≤ cross a g.b :=
    sub_nonneg.mpr ((mul_nonpos_of_nonneg_of_nonpos y b₀).trans (mul_nonneg x b₁))
  exact ⟨det a₀ a₁,det s₀ s₁,ws,wb,pa,pb⟩

private theorem eight (P : ℕ → Prop) :
    (∃ i : Fin 8, P (i.val+1)) ↔ P 1 ∨ P 2 ∨ P 3 ∨ P 4 ∨ P 5 ∨ P 6 ∨ P 7 ∨ P 8 := by
  constructor
  · rintro ⟨i,h⟩; fin_cases i <;> tauto
  · rintro (h|h|h|h|h|h|h|h)
    exacts [⟨0,h⟩,⟨1,h⟩,⟨2,h⟩,⟨3,h⟩,⟨4,h⟩,⟨5,h⟩,⟨6,h⟩,⟨7,h⟩]

/-- The union of the actual pieces of either correction is the union of the
eight physical polygons once the preceding alternate head is expressed by its two polygons. -/
theorem sources (v w : Word) (one long : Bool) (pre : stemPrefix v=w++[exit one]) (hw : ¬ IsBase w) (z : Site) :
    let g := periods v
    let prev := -(parentsAt w).odd.det (parentsAt w).even
    HeadPair v one prev →
    (z ∈ shift (evenChild evenLCells v long) (g.origin (W1Odd v) long) ↔
      ∃ i : Fin 8, (diagram g (length v) one prev long (i.val+1)).mem z) := by
  intro g prev heads
  have hn := prefix_nonbase v w one pre hw
  have small := no_enlargement v hn
  have phase : decide (CorrectedRegisterDiagram.orientation one prev ≠ 1)=W1Odd v := by
    rw [orientation_phase v w one pre]
    cases W1Odd v <;> decide
  have two : decide ((stemPrefix v).getLast?=some Digit.two)= !one := by
    rw [pre]; cases one <;> simp [exit]
  obtain ⟨detA,detS,widthS,widthB,parA,parB⟩ := bounds v w one pre
  let m := 2*length v-if long then 0 else 1
  have stem (x : Site) : x ∈ column (stemE (stemPrefix v)) g.a (length v) ↔ Band g.a g.b (length v) 0 x :=
    horizontal_row _ g.a g.b _ parA detA widthB (fun y => (registers v hn y).1) x
  have col (x : Site) : x ∈ column (headE (stemPrefix v)) g.b m ↔
      Band (sibling g one) g.b 0 m x ∨ Band (sibling g one) g.b 0 m (x-gap g one prev) :=
    paired_column _ _ _ _ _ parB detS widthS heads x
  have bridge (s : Bool) : z ∈ bridgePieces v s long ↔ Band g.u g.v 0 0 (z-g.bridge (W1Odd v) s long) := by
    simp only [bridgePieces,small,Bool.false_and,Bool.false_eq_true,if_false,Finset.union_empty,mem_shift]
    exact (registers v hn _).2
  have headShift (a b c : Site) : z-(a+b+c)=(z-a)-(b+c) := by abel
  rw [CorrectedEvenPlacement.after_three,eight (fun i => (diagram g (length v) one prev long i).mem z)]
  change z ∈ ((shift (evenTile v) _ ∪ shift (evenTile v) _) ∪
      ((shift (column (stemE _) g.a _) _ ∪ bridgePieces v true long) ∪
       (shift (column (stemE _) g.a _) _ ∪ bridgePieces v false long))) ∪
      shift (column (headE _) g.b m) _ ↔ _
  simp only [Finset.mem_union,mem_shift,stem,col,bridge,full_band,two]
  simp only [diagram,Block.mem,phase,headShift,sibling,gap]
  tauto

end FLatticePaper.Tiles.CorrectedPlacedSources
