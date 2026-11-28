import FLatticePaper.Tiles.TileStepAssembly

/-! # Condition (C) from constants with which the pieces agree

If the pieces of a decomposition agree with constants `κ` on every overlap (outside the exceptional points), then on every edge of
the overlap graph the overlap constant is `κ j - κ i`, so the sum along a closed walk telescopes to `0`: `TileStepAssembly.WalkZero`.
This is the form in which condition (C) is proved for the corrected tile decompositions, by exhibiting the constants. -/

namespace FLatticePaper.Tiles.CorrectedWalkZero

open FLatticePaper.Tiles FLatticePaper.Tiles.JointFamily FLatticePaper.Tiles.JointGlue

/-- **Condition (C) from agreeing constants.** -/
theorem walkZero_of_agree (ps : List Piece) (κ : ℕ → ℤ) (hag : PiecesAgree ps κ) : TileStepAssembly.WalkZero ps := by
  intro off hoff i walk
  suffices h : ∀ (a b : Fin ps.length) (p : (overlapGraph (goodPart ps)).Walk a b), walkSum off p = κ b.1 - κ a.1 by
    simpa using h i i walk
  intro a b p
  induction p with
  | nil => simp [walkSum_nil]
  | @cons u v w hadj p ih =>
    rw [walkSum_cons, ih]
    obtain ⟨-, x, hx1, hx2⟩ := hadj
    have e1 := hoff u v x ⟨hx1, hx2⟩
    have e2 := hag u.1 v.1 (ps.get u) (ps.get v) (by simp) (by simp) x.1 hx1.1 hx2.1 hx1.2 hx2.2
    linarith

end FLatticePaper.Tiles.CorrectedWalkZero
