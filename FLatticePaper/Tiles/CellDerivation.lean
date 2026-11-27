import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Group.Prod

/-! (d) of `lemma:standard_tile_properties` through cells (operator's notes, Section 7.1).

A unit square (cell) is identified with its lower-left site `s`; its corners are `s`, `s + (1,0)`, `s + (0,1)`, `s + (1,1)`.
For a tile whose cells form the set `C`, a site `z` is an interior vertex when the four unit squares having `z` as a corner
are all cells (`Interior`), and a boundary vertex when it is a corner of a cell and not an interior vertex (`BoundaryVertex`).

The argument of the operator, with the three facts as named inputs of `common_point_in_strings`:
* `H1`: every point of a tile is a corner of one of its cells;
* `H2`: every boundary vertex of the cell region of a tile lies in the zero-one strings of the tile;
* `H3`: no unit square is a cell of both tiles (the missing lemma; it is not proved here).
A point common to two tiles is a corner of a cell of each. If it were an interior vertex of one cell region, the cell of the
other tile at that corner would be a cell of the first tile, against `H3`. So it is a boundary vertex of both, and `H2` puts
it in the strings of both. -/

namespace FLatticePaper.Tiles.CellDerivation

/-- The unit square with lower-left site `s` has the site `z` as a corner. -/
def HasCorner (s z : ℤ × ℤ) : Prop :=
  z = s ∨ z = s + ((1 : ℤ), (0 : ℤ)) ∨ z = s + ((0 : ℤ), (1 : ℤ)) ∨ z = s + ((1 : ℤ), (1 : ℤ))

/-- An interior vertex of the cell set `C`: the four unit squares having `z` as a corner are cells. -/
abbrev Interior (C : Set (ℤ × ℤ)) (z : ℤ × ℤ) : Prop :=
  z ∈ C ∧ z + ((-1 : ℤ), (0 : ℤ)) ∈ C ∧ z + ((0 : ℤ), (-1 : ℤ)) ∈ C ∧ z + ((-1 : ℤ), (-1 : ℤ)) ∈ C

/-- A boundary vertex of the cell set `C`: a corner of a cell of `C` that is not an interior vertex. -/
abbrev BoundaryVertex (C : Set (ℤ × ℤ)) (z : ℤ × ℤ) : Prop :=
  (∃ s ∈ C, HasCorner s z) ∧ ¬ Interior C z

/-- The unit squares having `z` as a corner are the four squares at `z`. -/
theorem squares_at {s z : ℤ × ℤ} (h : HasCorner s z) :
    s = z ∨ s = z + ((-1 : ℤ), (0 : ℤ)) ∨ s = z + ((0 : ℤ), (-1 : ℤ)) ∨ s = z + ((-1 : ℤ), (-1 : ℤ)) := by
  rcases h with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl (by ext <;> simp <;> omega))
  · exact Or.inr (Or.inr (Or.inl (by ext <;> simp <;> omega)))
  · exact Or.inr (Or.inr (Or.inr (by ext <;> simp <;> omega)))

/-- **The cell derivation of (d).** A point common to two tiles lies in the zero-one strings of both, given the cell facts
`H1`, `H2` for each tile and the cell-disjointness `H3`. -/
theorem common_point_in_strings (CX CY PX PY SX SY : Set (ℤ × ℤ))
    (H1X : ∀ z ∈ PX, ∃ s ∈ CX, HasCorner s z)
    (H1Y : ∀ z ∈ PY, ∃ s ∈ CY, HasCorner s z)
    (H2X : ∀ z, BoundaryVertex CX z → z ∈ SX)
    (H2Y : ∀ z, BoundaryVertex CY z → z ∈ SY)
    (H3 : ∀ s, s ∈ CX → s ∈ CY → False) :
    ∀ z ∈ PX, z ∈ PY → z ∈ SX ∧ z ∈ SY := by
  intro z hX hY
  obtain ⟨s, hsC, hsz⟩ := H1X z hX
  obtain ⟨t, htC, htz⟩ := H1Y z hY
  have hXb : BoundaryVertex CX z := by
    refine ⟨⟨s, hsC, hsz⟩, fun hint => ?_⟩
    have htX : t ∈ CX := by
      rcases squares_at htz with h | h | h | h
      · rw [h]; exact hint.1
      · rw [h]; exact hint.2.1
      · rw [h]; exact hint.2.2.1
      · rw [h]; exact hint.2.2.2
    exact H3 t htX htC
  have hYb : BoundaryVertex CY z := by
    refine ⟨⟨t, htC, htz⟩, fun hint => ?_⟩
    have hsY : s ∈ CY := by
      rcases squares_at hsz with h | h | h | h
      · rw [h]; exact hint.1
      · rw [h]; exact hint.2.1
      · rw [h]; exact hint.2.2.1
      · rw [h]; exact hint.2.2.2
    exact H3 s hsC hsY
  exact ⟨H2X z hXb, H2Y z hYb⟩

end FLatticePaper.Tiles.CellDerivation
