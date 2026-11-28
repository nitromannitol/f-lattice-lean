import FLatticePaper.Tiles.AltCorrectedGlueOdd

/-! # The glue of the six copies of a corrected alternate even child (route (B), even child)

At a corrected alternate even child (`w` ends in `three`) the tile is the union of six standard copies: the four copies of the even
register (offsets `altEvenD`, doubled with shift `S_q`) and the two plain copies of the odd register (offsets `altEvenR`), with no
parent piece. Their offsets are `AltPieces.evenQOffs`/`evenPOffs` (by unfolding), so the mixed claim is `AltItem5.item5_marks_even`.
Condition (C) is `ClosedPathAlt.AltClosedPathEven` (`ClosedPathGen` with the even copies first) and the glue is
`ChildGlue.glue_kept_pieces`. -/

namespace FLatticePaper.Tiles.AltCorrectedGlueEven

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
open FLatticePaper.Tiles.ChildGlue FLatticePaper.Tiles.ClosedPathAlt FLatticePaper.Tiles.SiteInduction
open FLatticePaper.Tiles.AltItem5 FLatticePaper.Tiles.AltRotStep
open FLatticePaper.Tiles.AltCorrectedGlueOdd (mem_shiftS_tOdd mem_shiftS_tEven)

/-- The offsets of the four even copies of the alternate even child are the `evenQOffs` of the parents. -/
theorem altEvenD_eq_evenQOffs (w : Word) :
    altEvenD w = AltPieces.evenQOffs (phase w == 1) (parentsAt w).odd (parentsAt w).even := rfl

/-- The offsets of the two odd copies of the alternate even child are the `evenPOffs` of the parents. -/
theorem altEvenR_eq_evenPOffs (w : Word) :
    altEvenR w = AltPieces.evenPOffs (phase w == 1) (parentsAt w).odd (parentsAt w).even := rfl

/-- **The mixed claim of the six copies, even child** (`H1` of the glue), from `AltItem5.item5_marks_even`. -/
theorem altEven_mixed (w u1 u2 : Word) (hw : ¬ IsBase w)
    (h1 : (stateAt w).tOdd = oddTile u1) (h2 : (stateAt w).tEven = evenTile u2) :
    ∀ a ∈ altEvenD w, ∀ b ∈ altEvenR w, ∀ z : ℤ × ℤ,
      z ∈ shiftS (tEvenSet u2) a → z ∈ shiftS (tOddSet u1) b →
        z ∈ shiftS (marksEven u2) a ∧ z ∈ shiftS (marksOdd u1) b := by
  intro a ha b hb z hza hzb
  rw [altEvenD_eq_evenQOffs] at ha
  rw [altEvenR_eq_evenPOffs] at hb
  have hA : z ∈ shift (stateAt w).tOdd b := by
    rw [h1]
    exact Finset.mem_coe.mp (by rw [coe_shift]; exact hzb)
  have hB : z ∈ shift (stateAt w).tEven a := by
    rw [h2]
    exact Finset.mem_coe.mp (by rw [coe_shift]; exact hza)
  obtain ⟨m1, m2⟩ := item5_marks_even hw u1 u2 h1 h2 b hb a ha z hA hB
  exact ⟨m2, m1⟩

/-- **The glue of the six copies of the corrected alternate even child.** Condition (C) gives the constants `κ`, and the glue on the
kept parts is a function `g` with `g = f0 i + κ i` there. -/
theorem altEven_glue (w u1 u2 : Word) (hw : ¬ IsBase w)
    (h1 : (stateAt w).tOdd = oddTile u1) (h2 : (stateAt w).tEven = evenTile u2) (f0 : ℕ → ℤ × ℤ → ℤ)
    (hC : AltClosedPathEven w u1 u2 f0) :
    ∃ κ : ℕ → ℤ, ∃ g : ℤ × ℤ → ℤ, ∀ i, i < 6 →
      ∀ z ∈ keptSet (pieceSet (altEvenD w) (altEvenR w) (tEvenSet u2) (tOddSet u1)) (pieceFlag (altEvenD w)) dblEven i,
        g z = f0 i z + κ i := by
  unfold AltClosedPathEven ClosedPathAltSum.ClosedPathGen at hC
  obtain ⟨κ, hM, hD⟩ := hC
  obtain ⟨g, hg⟩ := glue_kept_pieces (altEvenD w) (altEvenR w) (tEvenSet u2) (tOddSet u1) (marksEven u2) (marksOdd u1)
    dblEven (fun i z => f0 i z + κ i) (altEven_mixed w u1 u2 hw h1 h2) hM hD
  refine ⟨κ, g, fun i hi z hz => ?_⟩
  have hl : (altEvenD w).length + (altEvenR w).length = 6 := rfl
  exact hg i (by rw [hl]; exact hi) z hz

/-- **The domain of the corrected alternate even child is the union of its six copies**: a point lies in `altEvenTile` at a corrected word
exactly when it lies in one of the even copies `altEvenD` or the odd copies `altEvenR` (the parent piece is empty at `three`). -/
theorem altEven_cover (w u1 u2 : Word) (hc : w.getLast? = some Digit.three) (hw : ¬ IsBase w)
    (h1 : (stateAt w).tOdd = oddTile u1) (h2 : (stateAt w).tEven = evenTile u2) (z : ℤ × ℤ) :
    z ∈ SurgicalAltTiles.altEvenTile PaperAltBase.paperAltBaseTiles w ↔
      (∃ a ∈ altEvenD w, z ∈ shiftS (tEvenSet u2) a) ∨ (∃ b ∈ altEvenR w, z ∈ shiftS (tOddSet u1) b) := by
  obtain ⟨u, rfl⟩ := List.getLast?_eq_some_iff.mp hc
  have hp : ∀ (aO : Tile) (o : Bool) (p q : Fraction), altP1Part o Digit.three aO p q = ∅ := fun aO o p q => by cases o <;> rfl
  rw [altEvenTile_of_not_base _ hw, altEvenPieces_snoc, hp, Finset.union_empty]
  rw [h1, h2, altEvenD_eq_evenQOffs, altEvenR_eq_evenPOffs]
  simp only [evenStd, AltPieces.evenPOffs, AltPieces.evenQOffs, Finset.mem_union, AltPieces.mem_shift_doubled]
  simp only [Standard.mem_shift, mem_shiftS_tOdd, mem_shiftS_tEven, List.mem_cons,
    List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
  tauto

end FLatticePaper.Tiles.AltCorrectedGlueEven
