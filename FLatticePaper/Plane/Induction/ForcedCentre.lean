import FLatticePaper.Plane.Induction.SlipReflect
import FLatticePaper.Plane.Induction.ReflectionI

/-! # Unseeded forced edges are carried by the reflection about a point `(c1, c2)` (Q34, sign `−1`, direct route)

`ForcedEdge F` depends on the field only through its Laplacian and the square structure. The centre reflection `x ↦ (c1,c2) − x`
maps the unit square with corners `squareCorners a b` onto `squareCorners (c1 − a − 1) (c2 − b − 1)`, exchanges the two inputs of a
site, and preserves the Laplacian (`ChildFrame.laplacian_reflect`). So the induction of `ReflectionI.forced_reflectI` carries a
forced edge to a forced edge. -/

namespace FLatticePaper.ForcedCentre

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank

/-- The corners of `squareCorners a b`, reflected about `(c1, c2)`, form `squareCorners (c1 − a − 1) (c2 − b − 1)`. -/
theorem mem_corners_centre (c1 c2 a b : ℤ) (x : Site) :
    x ∈ squareCorners a b ↔ ((c1, c2) - x) ∈ squareCorners (c1 - a - 1) (c2 - b - 1) := by
  obtain ⟨x1, x2⟩ := x
  simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.mk_sub_mk]
  constructor <;> intro h <;> omega

/-- The inverse form: a site of the reflected square maps back into `squareCorners a b`. -/
theorem mem_corners_centre' (c1 c2 a b : ℤ) (x : Site) :
    x ∈ squareCorners (c1 - a - 1) (c2 - b - 1) ↔ ((c1, c2) - x) ∈ squareCorners a b := by
  obtain ⟨x1, x2⟩ := x
  simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.mk_sub_mk]
  constructor <;> intro h <;> omega

/-- **Forced edges are carried by the reflection about `(c1, c2)`**, from the Laplacian and the input correspondences. -/
theorem forced_reflect_gen {F : Field} (c1 c2 : ℤ)
    (hL : ∀ x : Site, laplacian F ((c1, c2) - x) = laplacian F x)
    (hN : ∀ x : Site, FLatticePaper.incomingNeg ((c1, c2) - x) = (c1, c2) - FLatticePaper.incomingPos x)
    (hP : ∀ x : Site, FLatticePaper.incomingPos ((c1, c2) - x) = (c1, c2) - FLatticePaper.incomingNeg x)
    {c i : Site} (h : ForcedEdge F (fun _ _ => False) c i) :
    ForcedEdge F (fun _ _ => False) ((c1, c2) - c) ((c1, c2) - i) := by
  induction h with
  | seed hs => exact False.elim hs
  | @unit a b c' o inside hc hw ho hout hin hforced ih =>
    refine ForcedEdge.unit (a := c1 - a - 1) (b := c2 - b - 1)
      (fun z => (c1, c2) - inside ((c1, c2) - z)) ?_ ?_ ?_ ?_ ?_ ?_
    · exact (mem_corners_centre c1 c2 a b c').mp hc
    · rw [hL]
      exact hw
    · rcases ho with rfl | rfl
      · exact Or.inr (by rw [hP])
      · exact Or.inl (by rw [hN])
    · intro hmem
      apply hout
      have := (mem_corners_centre' c1 c2 a b ((c1, c2) - o)).mp hmem
      rwa [sub_sub_cancel] at this
    · intro c'' hc'' hne
      have hx : (c1, c2) - c'' ∈ squareCorners a b := (mem_corners_centre' c1 c2 a b c'').mp hc''
      have hne' : (c1, c2) - c'' ≠ c' := fun e => hne (by rw [← e, sub_sub_cancel])
      have hlap := hL c''
      rcases hin ((c1, c2) - c'') hx hne' with hb | ⟨hw', hy, hyin⟩
      · left
        rw [← hlap]
        exact hb
      · right
        refine ⟨by rw [← hlap]; exact hw', ?_, ?_⟩
        · exact (mem_corners_centre c1 c2 a b _).mp hy
        · rcases hyin with e | e
          · right
            show (c1, c2) - inside ((c1, c2) - c'') = FLatticePaper.incomingPos c''
            rw [e, hN, sub_sub_cancel]
          · left
            show (c1, c2) - inside ((c1, c2) - c'') = FLatticePaper.incomingNeg c''
            rw [e, hP, sub_sub_cancel]
    · intro c'' hc'' hne hw''
      have hx : (c1, c2) - c'' ∈ squareCorners a b := (mem_corners_centre' c1 c2 a b c'').mp hc''
      have hne' : (c1, c2) - c'' ≠ c' := fun e => hne (by rw [← e, sub_sub_cancel])
      have hw3 : laplacian F ((c1, c2) - c'') = 0 := by rw [hL]; exact hw''
      have key := ih ((c1, c2) - c'') hx hne' hw3
      rw [sub_sub_cancel] at key
      exact key

/-- **The centre reflection of the word's frame.** The forced edges of the standard field are carried by `x ↦ centre − x`. -/
theorem forced_reflect_centre (frame : ChildFrame) {F : Field} (hP : frame.Packet F)
    {c i : Site} (h : ForcedEdge F (fun _ _ => False) c i) :
    ForcedEdge F (fun _ _ => False) (frame.centre - c) (frame.centre - i) := by
  refine forced_reflect_gen frame.centre.1 frame.centre.2 ?_ ?_ ?_ h
  · intro x
    exact frame.laplacian_reflect hP x
  · intro x
    exact (frame.reflect_input_pos x).symm
  · intro x
    exact (frame.reflect_input_neg x).symm

end FLatticePaper.ForcedCentre
