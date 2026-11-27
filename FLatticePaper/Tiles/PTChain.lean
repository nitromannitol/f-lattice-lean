import FLatticePaper.Tiles.PTAppend
import FLatticePaper.Tiles.PTAffineTransport
import FLatticePaper.Tiles.FirstSentenceSurgical

/-! The chain of blocks along a string: `chainR B [C₁, …, Cₘ] = B ++ (C₁ ++ (… ++ Cₘ))` as families (right nested appends),
and the seams between consecutive blocks. A string of a child odometer is a chain of placed piece strings, and its respect is
the respect of the blocks plus the seams (`chainR_respects`). The seams are the junction clauses of T1. -/

namespace FLatticePaper.Tiles

/-- The right-nested concatenation of a block with a list of blocks. -/
def PTFamily.chainR : PTFamily → List PTFamily → PTFamily
  | B, [] => B
  | B, C :: rest => B.append (PTFamily.chainR C rest)

/-- The seams between consecutive blocks of a chain. -/
def PTFamily.ChainSeams (o : Orientation) (rev : Bool) : PTFamily → List PTFamily → Prop
  | _, [] => True
  | B, C :: rest => PTFamily.SeamClause o rev B C ∧ PTFamily.ChainSeams o rev C rest

/-- The seam with a block does not change when the block is followed by further blocks (the first tile, odometer and domain of
`C.append R` are those of `C`). -/
theorem PTFamily.seam_head_congr (o : Orientation) (rev : Bool) (B C R : PTFamily) (hC0 : 0 < C.n)
    (h : PTFamily.SeamClause o rev B C) : PTFamily.SeamClause o rev B (C.append R) := by
  unfold PTFamily.SeamClause at h ⊢
  have e0 : (C.append R).odo 0 = C.odo 0 := funext (fun x => PTFamily.append_odo_lt C R 0 hC0 x)
  have d0 : (C.append R).dom 0 = C.dom 0 := PTFamily.append_dom_lt C R 0 hC0
  have t0 : (C.append R).tile 0 = C.tile 0 := PTFamily.append_tile_lt C R 0 hC0
  rw [e0, d0, t0]
  exact h

theorem PTFamily.chainR_n_pos (C : PTFamily) (rest : List PTFamily) (hC0 : 0 < C.n) :
    0 < (PTFamily.chainR C rest).n := by
  cases rest with
  | nil => exact hC0
  | cons D rest' =>
    show 0 < (C.append (PTFamily.chainR D rest')).n
    rw [PTFamily.append_n]
    omega

theorem PTFamily.seam_chain (o : Orientation) (rev : Bool) (B C : PTFamily) (rest : List PTFamily)
    (hC0 : 0 < C.n) (h : PTFamily.SeamClause o rev B C) :
    PTFamily.SeamClause o rev B (PTFamily.chainR C rest) := by
  cases rest with
  | nil => exact h
  | cons D rest' => exact PTFamily.seam_head_congr o rev B C (PTFamily.chainR D rest') hC0 h

/-- **The chain respects the string** when the first block and all later blocks respect it and every seam holds. -/
theorem PTFamily.chainR_respects (o : Orientation) (rev : Bool) (rest : List PTFamily) :
    ∀ (B : PTFamily), B.Respects o rev → 0 < B.n → (∀ C ∈ rest, C.Respects o rev ∧ 0 < C.n) →
      PTFamily.ChainSeams o rev B rest → (PTFamily.chainR B rest).Respects o rev := by
  induction rest with
  | nil =>
    intro B hB _ _ _
    exact hB
  | cons C rest ih =>
    intro B hB hB0 hall hseams
    obtain ⟨hseam, hseams'⟩ := hseams
    obtain ⟨hC, hC0⟩ := hall C (List.mem_cons_self)
    have hrest : (PTFamily.chainR C rest).Respects o rev :=
      ih C hC hC0 (fun D hD => hall D (List.mem_cons_of_mem C hD)) hseams'
    have hpos : 0 < (PTFamily.chainR C rest).n := PTFamily.chainR_n_pos C rest hC0
    exact PTFamily.append_respects B (PTFamily.chainR C rest) o rev hB hrest hB0 hpos
      (PTFamily.seam_chain o rev B C rest hC0 hseam)

/-- A placed piece: the family translated by its offset and then shifted by the affine term `a·x + c` (the placement of
`PlacedPiece`, with its affine correction). -/
def PTFamily.placed (F : PTFamily) (off a : GInt) (c : ℤ) : PTFamily :=
  (F.translate off).affineAdd a c

theorem PTFamily.placed_respects (F : PTFamily) (o : Orientation) (rev : Bool) (off a : GInt) (c : ℤ)
    (h : F.Respects o rev) : (F.placed off a c).Respects o rev :=
  PTFamily.affineAdd_respects _ o rev a c (PTFamily.translate_respects F o rev off h)

theorem PTFamily.placed_n (F : PTFamily) (off a : GInt) (c : ℤ) : (F.placed off a c).n = F.n := by
  unfold PTFamily.placed
  rw [PTFamily.affineAdd_n, PTFamily.translate_n]

end FLatticePaper.Tiles
