import FLatticePaper.Tiles.CorrectedPlacedDiagram

/-! The primitive and lengthened sides in a corrected physical diagram all use the same closed sector. -/

namespace FLatticePaper.Tiles.CorrectedPlacedSectors

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open CorrectedRegisterWords CorrectedRegisterDiagram CorrectedPhysicalFaces
open CorrectedEvenPlacement CorrectedPlacementFrames CorrectedPlacedDiagram JointFamily

private def H (sec : Fin 3) (z : Site) : Prop :=
  if sec=0 then 3*z.2 ≤ z.1 else z.1 ≤ 3*z.2

private def V (sec : Fin 3) (z : Site) : Prop :=
  if sec=2 then 3*(-z.1) ≤ z.2 else z.2 ≤ 3*(-z.1)

private theorem h_add {s : Fin 3} {a b : Site} (ha : H s a) (hb : H s b) : H s (a+b) := by
  unfold H at *; split_ifs at * <;> dsimp <;> omega

private theorem v_add {s : Fin 3} {a b : Site} (ha : V s a) (hb : V s b) : V s (a+b) := by
  unfold V at *; split_ifs at * <;> dsimp <;> omega

private theorem h_mul {s : Fin 3} {a : Site} (ha : H s a) (k : ℤ) (hk : 0 ≤ k) : H s (k • a) := by
  unfold H at *; split_ifs at *
  all_goals dsimp [Prod.smul_mk]; linarith only [mul_le_mul_of_nonneg_left ha hk]

private theorem v_mul {s : Fin 3} {a : Site} (ha : V s a) (k : ℤ) (hk : 0 ≤ k) : V s (k • a) := by
  unfold V at *; split_ifs at *
  all_goals dsimp [Prod.smul_mk]; linarith only [mul_le_mul_of_nonneg_left ha hk]

private theorem primitive (x : Digit) (xs v : Word) (one : Bool)
    (pre : stemPrefix v=(x::xs)++[exit one]) :
    let g := periods v
    let s := firstSector x
    H s g.a ∧ V s g.b ∧ H s g.u ∧ V s g.v ∧ H s (if one then g.u else g.a-g.u) := by
  let P := parentsAt (x::xs)
  let s := firstSector x
  obtain ⟨h₁,h₂⟩ := sectors x xs
  change inSector s (texV1Odd P.odd) at h₁
  change inSector s (texV1Even P.even) at h₂
  obtain ⟨_,p,_⟩ := (parentsAt_valid (x::xs)).odd_bounds
  obtain ⟨_,q,_⟩ := (parentsAt_valid (x::xs)).even_bounds
  change 0 ≤ P.odd.num at p
  change 0 ≤ P.even.num at q
  dsimp only
  change H s (vP1 (stemPrefix v)) ∧ V s (vP2 (stemPrefix v)) ∧
    H s (vQ1 (stemPrefix v)) ∧ V s (vQ2 (stemPrefix v)) ∧
    H s (if one then vQ1 (stemPrefix v) else vP1 (stemPrefix v)-vQ1 (stemPrefix v))
  rw [pre]
  simp only [vP1,vP2,vQ1,vQ2,parentsAt_append_singleton]
  change H s (texV1Odd (P.step (exit one)).odd) ∧ V s (texV2 (P.step (exit one)).odd) ∧
    H s (texV1Even (P.step (exit one)).even) ∧ V s (texV2 (P.step (exit one)).even) ∧
    H s (if one then texV1Even (P.step (exit one)).even else
      texV1Odd (P.step (exit one)).odd-texV1Even (P.step (exit one)).even)
  rcases (show s=0 ∨ s=1 ∨ s=2 by have := s.isLt; omega) with hs|hs|hs <;>
    cases one <;>
    norm_num [hs,H,V,inSector,exit,Parents.step,Parents.current,Parents.combine,texV1Odd,texV1Even,texV2,Fin.ext_iff] at h₁ h₂ ⊢ <;> omega

/-- All ten entries use the two projections determined by the first digit of the preceding word.
This includes both target polygons when the correction is elongated. -/
theorem word (x : Digit) (xs v : Word) (one long : Bool) (prev : ℤ)
    (pre : stemPrefix v=(x::xs)++[exit one]) (i : Fin 10) :
    let b := diagram (periods v) (length v) one prev long i.val
    Aligned b.a b.b (firstSector x) := by
  let s := firstSector x
  let g := periods v
  obtain ⟨A,B,U,T,sib⟩ := primitive x xs v one pre
  change H s g.a at A
  change V s g.b at B
  change H s g.u at U
  change V s g.v at T
  change H s (if one then g.u else g.a-g.u) at sib
  have fu : H s g.fullU := h_add U (h_mul A (length v) (by positivity))
  have fv : V s g.fullV := v_add T (v_mul B (2*(length v:ℤ)) (by positivity))
  have fullA := h_add A fu
  have fullA' := h_add fullA fu
  have fullB := v_add B fv
  have aligned {a b : Site} (h : H s a) (k : V s b) : Aligned a b s := ⟨h,k⟩
  change Aligned (diagram g (length v) one prev long i.val).a (diagram g (length v) one prev long i.val).b s
  fin_cases i
  all_goals simp only [diagram]
  all_goals first | (apply aligned <;> assumption) | (split <;> apply aligned <;> assumption)

end FLatticePaper.Tiles.CorrectedPlacedSectors
