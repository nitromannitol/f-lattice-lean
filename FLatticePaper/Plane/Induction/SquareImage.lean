import FLatticePaper.Plane.Induction.W1Phase

/-! # The quarter turn sends unit squares to unit squares (step (c) of the top-square argument)

`zTurnInv (x) = (x₂ + 1, -x₁)` is a lattice isometry (a quarter turn). Composed with a translation, `q ↦ zTurnInv (q - v) + k` maps
the four corners of a unit square `squareCorners a b` onto the four corners of the unit square `squareCorners (b - v₂ + 1 + k₁)
(-(a - v₁) - 1 + k₂)`, and every corner of the image is the image of a corner. -/

namespace FLatticePaper.SquareImage

open FLatticePaper FLatticePaper.AndOrRank FLatticePaper.W1Phase

theorem mem_squareCorners_iff (a b : ℤ) (z : Site) :
    z ∈ squareCorners a b ↔ z = (a, b) ∨ z = (a + 1, b) ∨ z = (a, b + 1) ∨ z = (a + 1, b + 1) := by
  simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton]

/-- The image of a corner of `squareCorners a b` is a corner of the image square. -/
theorem image_mem (a b : ℤ) (v k q : Site) (hq : q ∈ squareCorners a b) :
    zTurnInv (q - v) + k ∈ squareCorners (b - v.2 + 1 + k.1) (-(a - v.1) - 1 + k.2) := by
  rw [mem_squareCorners_iff] at hq ⊢
  rcases hq with rfl | rfl | rfl | rfl
  · right; right; left
    ext
    all_goals (simp [zTurnInv]; try ring)
  · left
    ext
    all_goals (simp [zTurnInv]; try ring)
  · right; right; right
    ext
    all_goals (simp [zTurnInv]; try ring)
  · right; left
    ext
    all_goals (simp [zTurnInv]; try ring)

/-- Every corner of the image square is the image of a corner of `squareCorners a b`. -/
theorem image_preimage (a b : ℤ) (v k p : Site)
    (hp : p ∈ squareCorners (b - v.2 + 1 + k.1) (-(a - v.1) - 1 + k.2)) :
    ∃ q ∈ squareCorners a b, zTurnInv (q - v) + k = p := by
  rw [mem_squareCorners_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · refine ⟨(a + 1, b), ?_, ?_⟩
    · rw [mem_squareCorners_iff]; right; left; rfl
    · ext
      all_goals (simp [zTurnInv]; try ring)
  · refine ⟨(a + 1, b + 1), ?_, ?_⟩
    · rw [mem_squareCorners_iff]; right; right; right; rfl
    · ext
      all_goals (simp [zTurnInv]; try ring)
  · refine ⟨(a, b), ?_, ?_⟩
    · rw [mem_squareCorners_iff]; left; rfl
    · ext
      all_goals (simp [zTurnInv]; try ring)
  · refine ⟨(a, b + 1), ?_, ?_⟩
    · rw [mem_squareCorners_iff]; right; right; left; rfl
    · ext
      all_goals (simp [zTurnInv]; try ring)

end FLatticePaper.SquareImage
