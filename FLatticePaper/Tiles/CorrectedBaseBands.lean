import FLatticePaper.Tiles.CorrectedCellsBands
import Mathlib.Tactic.IntervalCases

/-! Determinant descriptions of both base alternate parents, with their exterior column corrections. -/

namespace FLatticePaper.Tiles.CorrectedBaseBands

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open Standard PaperAltBase CorrectedCellsBands CorrectedColumnRuns

private def lower (d x t : ℤ) : Prop :=
  (if t%2=1 then -d else 4-2*d) ≤ d*t+2*x ∧ t%2 ≤ (d+1)*x+t

private def cut (d x t : ℤ) : Prop := (-2 ≤ t ∧ 0 ≤ x+t) ∨ (t = -3 ∧ x = d)

private theorem coarse (d x t : ℤ) (hd : 3 ≤ d) (h : lower d x t) :
    -2*d+3 ≤ d*t+2*x ∧ 0 ≤ (d+1)*x+t := by
  unfold lower at h
  split_ifs at h <;> omega

private theorem left_bound (d x t : ℤ) (hd : 3 ≤ d) (h₁ : lower d x t)
    (h₂ : lower d (d-x) (d-3-t)) : 0 ≤ x := by
  obtain ⟨_,lv⟩ := coarse _ _ _ hd h₁
  obtain ⟨uh,_⟩ := coarse _ _ _ hd h₂
  by_contra! hx
  have ht : 0 ≤ d*((d+1)*x+t) := mul_nonneg (by omega) lv
  have hp : 0 ≤ (d*(d+1)-2)*(-1-x) := mul_nonneg (by nlinarith) (by omega)
  linarith only [uh,ht,hp]

private theorem t_bound (d x t : ℤ) (hd : 3 ≤ d) (hx : x ≤ d) (h : lower d x t) : -3 ≤ t := by
  have H := (coarse _ _ _ hd h).1
  by_contra! ht
  have pos : 0 ≤ d*(-4-t) := mul_nonneg (by omega) (by omega)
  linarith

private theorem vertical (d x t : ℤ) (hd : 3 ≤ d) (hx : 0 ≤ x) (hy : 0 ≤ x+t) :
    t%2 ≤ (d+1)*x+t := by
  by_cases zero : x=0
  · subst x; simp only [mul_zero,zero_add] at *; omega
  have h : 0 ≤ d*(x-1) := mul_nonneg (by omega) (by omega)
  have := Int.emod_lt_of_pos t (by decide : (0 : ℤ) < 2)
  nlinarith

private theorem lower_iff (d x t : ℤ) (hd : 3 ≤ d) (hx : 0 ≤ x) (hu : x ≤ d) :
    lower d x t ↔ cut d x t := by
  constructor
  · intro hl
    have ht := t_bound d x t hd hu hl
    by_cases pos : 0 ≤ t
    · exact Or.inl ⟨by omega,by omega⟩
    unfold lower at hl
    interval_cases t <;> norm_num at hl ⊢ <;> unfold cut <;> norm_num <;> try omega
    by_cases h : x=0
    · subst x; norm_num at hl
    · omega
  · intro hc
    have hy : 0 ≤ x+t := by rcases hc with ⟨_,h⟩|⟨rfl,rfl⟩ <;> omega
    refine ⟨?_,vertical d x t hd hx hy⟩
    rcases hc with ⟨ht,_⟩|⟨rfl,rfl⟩
    · by_cases h : 0 ≤ t
      · have pos := mul_nonneg (show 0 ≤ d by omega) h
        split_ifs <;> omega
      · interval_cases t <;> norm_num <;> omega
    · norm_num; omega

/-- The cuts in the two reflected corners of the polygon, in coordinates (x, y-x). -/
private def cell (d x t : ℤ) : Prop :=
  0 ≤ x ∧ x ≤ d ∧ cut d x t ∧ cut d (d-x) (d-3-t)

private theorem pair_lower (d x t : ℤ) (hd : 3 ≤ d) :
    lower d x t ∧ lower d (d-x) (d-3-t) ↔ cell d x t := by
  constructor
  · rintro ⟨h,r⟩
    have hx := left_bound _ _ _ hd h r
    have e : d-(d-x)=x := by omega
    have ee : d-3-(d-3-t)=t := by omega
    have huu := left_bound _ _ _ hd r (by rwa [e,ee])
    exact ⟨hx,by omega,(lower_iff _ _ _ hd hx (by omega)).mp h,(lower_iff _ _ _ hd (by omega) (by omega)).mp r⟩
  · rintro ⟨hx,hu,h,r⟩
    exact ⟨(lower_iff _ _ _ hd hx hu).mpr h,(lower_iff _ _ _ hd (by omega) (by omega)).mpr r⟩

private theorem cell_band (d x y : ℤ) (hd : 3 ≤ d) (odd : d%2=1) :
    Band (d,d-2) (-1,d) 0 0 (x,y) ↔ cell d x (y-x) := by
  rw [←pair_lower _ _ _ hd]
  have par : (x+y)%2=(y-x)%2 := by omega
  have ref : (d-3-(y-x))%2=(y-x)%2 := by omega
  by_cases p : (y-x)%2=1
  · have v : (y-x)%2=1 := p
    simp [Band,allowances,probe,oddSite,cross,mulI,lower,par,v,ref,hd]
    ring_nf at *; omega
  · have v : (y-x)%2=0 := by omega
    by_cases he : 3*(d-2) ≤ d
    · have : d=3 := by omega
      subst d
      simp [Band,allowances,probe,oddSite,cross,mulI,lower,par,v]
      omega
    · simp [Band,allowances,probe,oddSite,cross,mulI,lower,par,v,ref,he]
      ring_nf at *; omega

/-- Exact polygon tests for the core between the two exterior segments. -/
theorem near_interior (d : ℤ) (hd : 3 ≤ d) (odd : d%2=1) (z : Site) :
    z ∈ nearInterior d ↔ Band (d,d-2) (-1,d) 0 0 z ∨ Band (d,d-2) (-1,d) 0 0 (z-(0,d-1)) := by
  obtain ⟨x,y⟩ := z
  simp only [Prod.mk_sub_mk,sub_zero,cell_band _ _ _ hd odd,cell,cut,nearInterior,Finset.mem_filter,
    mem_shift,nearStairAltF,boxF,Finset.mem_product,Finset.mem_Icc]
  omega


private theorem ladder_cell (d x y : ℤ) (hd : 4 ≤ d) (he : d%2=0) :
    Band (d+1,1) (1-d,d+1) 0 0 (x,y) ↔ cell (d+1) y (d+1-x-y) := by
  have hr := clockwise (d+1,1) (1-d,d+1) (x,y) 0 0 (by dsimp; omega)
  have ed : ((d+1,d+1-2):Site) = transverse (1-d,d+1) := by
    ext <;> dsimp [transverse]
    all_goals omega
  have eb : ((-1,d+1):Site) = mulI (d+1,1) := by rfl
  have ez : transverse (x,y) + (((0 : ℕ) : ℤ)+1) • mulI (d+1,1) + ((1,0):Site) = (y,d+1-x) := by
    ext <;> simp [mulI]
    all_goals ring
  rw [ez,←ed,←eb] at hr
  exact hr.trans (cell_band _ _ _ (by omega) (by omega))

private abbrev bottomPair (d : ℤ) : Tile := {(d+1,0),(d+1,1)}
private abbrev topPair (d : ℤ) : Tile := {(0,d+2),(0,d+3)}
private abbrev filled (d : ℤ) := shift (ladderAltF d) (1,1) ∪ bottomPair d ∪ topPair d

/-- Filling the two exterior vertex pairs of the normalized pure-three alternate parent gives the two polygons. -/
theorem ladder_filled (d : ℤ) (hd : 4 ≤ d) (he : d%2=0) (z : Site) :
    z ∈ filled d ↔ Band (d+1,1) (1-d,d+1) 0 0 z ∨ Band (d+1,1) (1-d,d+1) 0 0 (z-(d-2,2)) := by
  obtain ⟨x,y⟩ := z
  simp only [filled,bottomPair,topPair,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
    Prod.mk.injEq,Prod.mk_sub_mk,ladder_cell _ _ _ hd he,cell,cut,mem_shift,ladderAltF,boxF,
    Finset.mem_filter,Finset.mem_product,Finset.mem_Icc]
  omega

/-- The two lengthened polygons and the side segments give every site of the actual pure-two alternate register column. -/
theorem two_column (j k : ℕ) (s : Digit) (hs : s=.one ∨ s=.two) (z : Site) :
    let u := List.replicate j Digit.two
    let d := 2*(j : ℤ)+3
    z ∈ column (LCorrecRecursion.headE (u++[s])) (-1,d) k ↔
      (Band (d,d-2) (-1,d) 0 k z ∨ Band (d,d-2) (-1,d) 0 k (z-(0,d-1))) ∨
      (let x := z.1+1; let y := z.2-d; -(k : ℤ) ≤ x ∧ x ≤ 0 ∧ 0 ≤ y+d*x ∧ y+d*x < d) ∨
      (let x := z.1-(d+1); let y := z.2-(d-3); -(k : ℤ) ≤ x ∧ x ≤ 0 ∧ 0 ≤ y+d*x ∧ y+d*x < d) := by
  let d := 2*(j : ℤ)+3
  have hd : 3 ≤ d := by dsimp [d]; omega
  have hp : d%2=1 := by dsimp [d]; omega
  have hr := two_register j k s hs z
  dsimp only at hr ⊢
  rw [hr,
    paired_column (nearInterior d) (d,d-2) (-1,d) (0,d-1) k (by dsimp; omega)
      (by dsimp [cross]; nlinarith) (by dsimp; omega) (near_interior d hd hp)]

/-- The two lengthened polygons with precisely the first and last missing pairs give the actual pure-three register. -/
theorem three_column (j k : ℕ) (s : Digit) (hs : s=.one ∨ s=.two) (z : Site) :
    let u := List.replicate (j+1) Digit.three
    let d := 2*((j+1 : ℕ) : ℤ)+2
    let b : Site := (1-d,d+1)
    z ∈ column (LCorrecRecursion.headE (u++[s])) b k ↔
      (Band (d+1,1) b 0 k z ∨ Band (d+1,1) b 0 k (z-(d-2,2))) ∧
      z ∉ bottomPair d ∪ shift (topPair d) ((k : ℤ) • b) := by
  let d := 2*((j+1 : ℕ) : ℤ)+2
  have hd : 4 ≤ d := by dsimp [d]; omega
  have hp : d%2=0 := by dsimp [d]; omega
  dsimp only
  rw [three_register j k s hs,Finset.mem_sdiff]
  change (z ∈ column (filled d) (1-d,d+1) k ∧ _) ↔ _
  rw [paired_column (filled d) (d+1,1) (1-d,d+1) (d-2,2) k (by dsimp; omega)
    (by dsimp [cross]; nlinarith) (by dsimp; omega) (ladder_filled d hd hp)]

end FLatticePaper.Tiles.CorrectedBaseBands
