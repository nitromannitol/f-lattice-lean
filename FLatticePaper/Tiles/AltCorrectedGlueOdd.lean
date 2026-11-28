import FLatticePaper.Tiles.AltItem5
import FLatticePaper.Tiles.ClosedPathAlt
import FLatticePaper.Tiles.ChildGlue
import FLatticePaper.Tiles.AltRotStep

/-! # The glue of the six copies of a corrected alternate odd child (route (B), odd child)

At a corrected alternate odd child (`w` ends in `two`) the tile is the union of six standard copies: the two doubled copies of the odd
register (offsets `altOddD`, shift `S_p`) and the two plain copies of the even register (offsets `altOddR`), with no parent piece.
Their offsets are those of `AltPieces.oddPOffs`/`oddQOffs` (`altOddD_eq_oddPOffs`, `altOddR_eq_oddQOffs`, by unfolding), so the
mixed claim of the copies is `AltItem5.item5_marks_odd`. Condition (C) for the six copies is `ClosedPathAlt.AltClosedPathOdd`, which is
`ClosedPathAltSum.ClosedPathGen` with `κ`; the glue is `ChildGlue.glue_kept_pieces`, as for the standard odd child. -/

namespace FLatticePaper.Tiles.AltCorrectedGlueOdd

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
open FLatticePaper.Tiles.ChildGlue FLatticePaper.Tiles.ClosedPathAlt FLatticePaper.Tiles.SiteInduction
open FLatticePaper.Tiles.AltItem5 FLatticePaper.Tiles.AltRotStep

/-- The offsets of the four odd copies of the alternate odd child are the `oddPOffs` of the parents. -/
theorem altOddD_eq_oddPOffs (w : Word) :
    altOddD w = AltPieces.oddPOffs (phase w == 1) (parentsAt w).odd (parentsAt w).even := rfl

/-- The offsets of the two even copies of the alternate odd child are the `oddQOffs` of the parents. -/
theorem altOddR_eq_oddQOffs (w : Word) :
    altOddR w = AltPieces.oddQOffs (phase w == 1) (parentsAt w).odd (parentsAt w).even := rfl

/-- **The mixed claim of the six copies** (`H1` of the glue): an odd copy and an even copy of the alternate odd child meet only inside
their marks. From `AltItem5.item5_marks_odd`. -/
theorem altOdd_mixed (w u1 u2 : Word) (hw : ¬ IsBase w)
    (h1 : (stateAt w).tOdd = oddTile u1) (h2 : (stateAt w).tEven = evenTile u2) :
    ∀ a ∈ altOddD w, ∀ b ∈ altOddR w, ∀ z : ℤ × ℤ,
      z ∈ shiftS (tOddSet u1) a → z ∈ shiftS (tEvenSet u2) b →
        z ∈ shiftS (marksOdd u1) a ∧ z ∈ shiftS (marksEven u2) b := by
  intro a ha b hb z hza hzb
  rw [altOddD_eq_oddPOffs] at ha
  rw [altOddR_eq_oddQOffs] at hb
  have hA : z ∈ shift (stateAt w).tOdd a := by
    rw [h1]
    exact Finset.mem_coe.mp (by rw [coe_shift]; exact hza)
  have hB : z ∈ shift (stateAt w).tEven b := by
    rw [h2]
    exact Finset.mem_coe.mp (by rw [coe_shift]; exact hzb)
  exact item5_marks_odd hw u1 u2 h1 h2 a ha b hb z hA hB

/-- **The glue of the six copies of the corrected alternate odd child.** Condition (C) gives the constants `κ`, and the glue on the kept
parts is a function `g` with `g = f0 i + κ i` there (for the six copies `i < 6`). -/
theorem altOdd_glue (w u1 u2 : Word) (hw : ¬ IsBase w)
    (h1 : (stateAt w).tOdd = oddTile u1) (h2 : (stateAt w).tEven = evenTile u2) (f0 : ℕ → ℤ × ℤ → ℤ)
    (hC : AltClosedPathOdd w u1 u2 f0) :
    ∃ κ : ℕ → ℤ, ∃ g : ℤ × ℤ → ℤ, ∀ i, i < 6 →
      ∀ z ∈ keptSet (pieceSet (altOddD w) (altOddR w) (tOddSet u1) (tEvenSet u2)) (pieceFlag (altOddD w)) dblEven i,
        g z = f0 i z + κ i := by
  unfold AltClosedPathOdd ClosedPathAltSum.ClosedPathGen at hC
  obtain ⟨κ, hM, hD⟩ := hC
  obtain ⟨g, hg⟩ := glue_kept_pieces (altOddD w) (altOddR w) (tOddSet u1) (tEvenSet u2) (marksOdd u1) (marksEven u2)
    dblEven (fun i z => f0 i z + κ i) (altOdd_mixed w u1 u2 hw h1 h2) hM hD
  refine ⟨κ, g, fun i hi z hz => ?_⟩
  have hl : (altOddD w).length + (altOddR w).length = 6 := rfl
  exact hg i (by rw [hl]; exact hi) z hz


/-- Membership in a translated tile, as a set: `z ∈ shiftS (tOddSet u) a` is the Finset membership in `shift (oddTile u) a`. -/
theorem mem_shiftS_tOdd (u : Word) (a z : ℤ × ℤ) :
    z ∈ shiftS (tOddSet u) a ↔ z ∈ shift (oddTile u) a := by
  rw [← Finset.mem_coe, coe_shift]

/-- Membership in a translated even tile, as a set. -/
theorem mem_shiftS_tEven (u : Word) (a z : ℤ × ℤ) :
    z ∈ shiftS (tEvenSet u) a ↔ z ∈ shift (evenTile u) a := by
  rw [← Finset.mem_coe, coe_shift]

/-- **The domain of the corrected alternate odd child is the union of its six copies** (`pieceUnion`): a point lies in the alternate
tile `altOddTile` at a corrected word exactly when it lies in one of the copies `altOddD` of the odd register or `altOddR` of the even
register. The parent piece is absent at a corrected word (`altQ1Part` of `two` is empty). -/
theorem altOdd_cover (w u1 u2 : Word) (hc : w.getLast? = some Digit.two) (hw : ¬ IsBase w)
    (h1 : (stateAt w).tOdd = oddTile u1) (h2 : (stateAt w).tEven = evenTile u2) (z : ℤ × ℤ) :
    z ∈ SurgicalAltTiles.altOddTile PaperAltBase.paperAltBaseTiles w ↔
      (∃ a ∈ altOddD w, z ∈ shiftS (tOddSet u1) a) ∨ (∃ b ∈ altOddR w, z ∈ shiftS (tEvenSet u2) b) := by
  obtain ⟨u, rfl⟩ := List.getLast?_eq_some_iff.mp hc
  have hq : ∀ (aE : Tile) (o : Bool) (p q : Fraction), altQ1Part o Digit.two aE p q = ∅ := fun aE o p q => rfl
  rw [altOddTile_of_not_base _ hw, altOddPieces_snoc, hq, Finset.union_empty]
  rw [h1, h2, altOddD_eq_oddPOffs, altOddR_eq_oddQOffs]
  simp only [oddStd, AltPieces.oddPOffs, AltPieces.oddQOffs, Finset.mem_union, AltPieces.mem_shift_doubled]
  simp only [Standard.mem_shift, mem_shiftS_tOdd, mem_shiftS_tEven, List.mem_cons,
    List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
  tauto

end FLatticePaper.Tiles.AltCorrectedGlueOdd
