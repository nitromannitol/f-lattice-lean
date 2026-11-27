import FLatticePaper.Tiles.CellDerivation
import FLatticePaper.Tiles.MixedPiecesInMarks
import FLatticePaper.Tiles.StandardClauseA
import FLatticePaper.Tiles.StandardCornerCells

/-! The connection of the cell derivation of (d) to the register copies.

The cell set of a finite site set `T` is `cellTileOf T` (its unit squares with all corners in `T`). For a register tile the three
cell facts of the operator's argument are:
* `H1` (register tiles; w1 proves it for the standard tiles): every point of `T` is a corner of one of its cells;
* `H2` (register tiles, OPEN): every boundary vertex of the cell region of `T` lies in its marked sites. The repository has the
  unit-neighbour form only (`FourStrings`, clause 2: the inner boundary lies in the marks); the walk form is not yet proved;
* `H3` (copies, OPEN): no cell of the copy `T1 + a` is a cell of the copy `T2 + b`.

Translation carries `H1` and `H2` from a register tile to its copies `shiftS T a`, and `common_point_in_strings` then gives the
mixed-piece claim of `MixedPiecesInMarksOdd`. The inputs are named in `mixedOdd_of_cells`. -/

namespace FLatticePaper.Tiles.CellRegisters

open FLatticePaper.Tiles FLatticePaper.Tiles.CellDerivation FLatticePaper.Tiles.SiteInduction
open FLatticePaper.Tiles.Standard FLatticePaper.Tiles.StandardClause FLatticePaper.Farey FLatticePaper.Construction
open FLatticePaper.Tiles.MixedPieces FLatticePaper.Tiles.SiteStrings

/-- The cell set of a finite site set: the lower-left sites of its unit squares inside it (`cellTileOf`). -/
def cellSet (T : Finset (ℤ × ℤ)) : Set (ℤ × ℤ) := ↑(cellTileOf T)

theorem mem_shiftS_iff (C : Set (ℤ × ℤ)) (a x : ℤ × ℤ) : x ∈ shiftS C a ↔ x - a ∈ C := by
  simp only [shiftS, Set.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨x - a, h, by simp⟩

theorem eq_shift_iff (x y d a : ℤ × ℤ) : x + a = y + a + d ↔ x = y + d := by
  constructor
  · intro h
    calc x = (x + a) - a := by abel
      _ = (y + a + d) - a := by rw [h]
      _ = y + d := by abel
  · intro h
    rw [h]
    abel

theorem hasCorner_shift_iff (s z a : ℤ × ℤ) : HasCorner (s + a) (z + a) ↔ HasCorner s z := by
  unfold HasCorner
  simp only [add_left_inj, eq_shift_iff]

theorem interior_shift_iff (C : Set (ℤ × ℤ)) (a z : ℤ × ℤ) :
    Interior (shiftS C a) (z + a) ↔ Interior C z := by
  have e : ∀ d : ℤ × ℤ, z + a + d - a = z + d := fun d => by abel
  simp only [Interior, mem_shiftS_iff, e, add_sub_cancel_right]

theorem boundary_shift_iff (C : Set (ℤ × ℤ)) (a z : ℤ × ℤ) :
    BoundaryVertex (shiftS C a) (z + a) ↔ BoundaryVertex C z := by
  have key : (∃ s ∈ shiftS C a, HasCorner s (z + a)) ↔ (∃ t ∈ C, HasCorner t z) := by
    constructor
    · rintro ⟨s, hs, hsz⟩
      rw [mem_shiftS_iff] at hs
      refine ⟨s - a, hs, ?_⟩
      have e : s = (s - a) + a := by abel
      have hsz' : HasCorner ((s - a) + a) (z + a) := by rw [← e]; exact hsz
      exact (hasCorner_shift_iff (s - a) z a).1 hsz'
    · rintro ⟨t, ht, htz⟩
      exact ⟨t + a, (mem_shiftS_iff C a (t + a)).2 (by simpa using ht), (hasCorner_shift_iff t z a).2 htz⟩
  show (∃ s ∈ shiftS C a, HasCorner s (z + a)) ∧ ¬ Interior (shiftS C a) (z + a) ↔
    (∃ t ∈ C, HasCorner t z) ∧ ¬ Interior C z
  rw [key, interior_shift_iff]

/-- Translation of the cell fact `H1` from a finite tile to its copy `shiftS T a`. -/
theorem tileH1_shift (T : Finset (ℤ × ℤ)) (h : ∀ z ∈ T, ∃ s ∈ cellSet T, HasCorner s z) (a : ℤ × ℤ) :
    ∀ z ∈ shiftS (T : Set (ℤ × ℤ)) a, ∃ s ∈ shiftS (cellSet T) a, HasCorner s z := by
  intro z hz
  rw [mem_shiftS_iff] at hz
  obtain ⟨s, hs, hsz⟩ := h (z - a) (Finset.mem_coe.1 hz)
  refine ⟨s + a, (mem_shiftS_iff _ a (s + a)).2 (by simpa using hs), ?_⟩
  have e : z = (z - a) + a := by abel
  rw [e]
  exact (hasCorner_shift_iff s (z - a) a).2 hsz

/-- Translation of the cell fact `H2` from a tile to its copy: a boundary vertex of the copy's cell region lies in the translated
marks. -/
theorem tileH2_shift (T : Finset (ℤ × ℤ)) (M : Set (ℤ × ℤ)) (h : ∀ z, BoundaryVertex (cellSet T) z → z ∈ M) (a : ℤ × ℤ) :
    ∀ z, BoundaryVertex (shiftS (cellSet T) a) z → z ∈ shiftS M a := by
  intro z hz
  rw [mem_shiftS_iff]
  apply h
  have e : z = (z - a) + a := by abel
  rw [e] at hz
  exact (boundary_shift_iff (cellSet T) a (z - a)).1 hz

/-- The vertex form `HasCornerCell` of a finite tile gives the cell fact `H1` with the cells `cellTileOf` (the cells inside the tile). -/
theorem tileH1_of_hcc (T : Finset (ℤ × ℤ)) (h : HasCornerCell T) : ∀ z ∈ T, ∃ s ∈ cellSet T, HasCorner s z := by
  intro z hz
  obtain ⟨c, hzc, hall⟩ := h z hz
  have hcT : c ∈ cellTileOf T := Finset.mem_filter.2 ⟨hall c (by simp [cellCorners]), fun y hy => hall y hy⟩
  refine ⟨c, Finset.mem_coe.2 hcT, ?_⟩
  have hc : z = c ∨ z = c + gOne ∨ z = c + gI ∨ z = c + (gOne + gI) := by simpa [cellCorners] using hzc
  have e : gOne + gI = ((1 : ℤ), (1 : ℤ)) := by simp [gOne, gI]
  rcases hc with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · rw [e] at h
    exact Or.inr (Or.inr (Or.inr h))

/-- **The mixed claim of two register copies from the cell facts.** Copies of two tiles `T1 + a`, `T2 + b` meeting at a point have
the point in the translated marks of both, given `H1` and `H2` for each tile and `H3` for the copies. -/
theorem mixed_copies_of_cells (T1 T2 : Finset (ℤ × ℤ)) (M1 M2 : Set (ℤ × ℤ)) (a b : ℤ × ℤ)
    (H1a : ∀ z ∈ T1, ∃ s ∈ cellSet T1, HasCorner s z)
    (H1b : ∀ z ∈ T2, ∃ s ∈ cellSet T2, HasCorner s z)
    (H2a : ∀ z, BoundaryVertex (cellSet T1) z → z ∈ M1)
    (H2b : ∀ z, BoundaryVertex (cellSet T2) z → z ∈ M2)
    (H3 : ∀ s, s ∈ shiftS (cellSet T1) a → s ∈ shiftS (cellSet T2) b → False) :
    ∀ z ∈ shiftS (T1 : Set (ℤ × ℤ)) a, z ∈ shiftS (T2 : Set (ℤ × ℤ)) b → z ∈ shiftS M1 a ∧ z ∈ shiftS M2 b :=
  common_point_in_strings (shiftS (cellSet T1) a) (shiftS (cellSet T2) b) (shiftS (T1 : Set (ℤ × ℤ)) a)
    (shiftS (T2 : Set (ℤ × ℤ)) b) (shiftS M1 a) (shiftS M2 b) (tileH1_shift T1 H1a a) (tileH1_shift T2 H1b b)
    (tileH2_shift T1 M1 H2a a) (tileH2_shift T2 M2 H2b b) H3

/-- Input `H3` (copies, OPEN): for the odd child of `w`, no cell of a copy of the odd register is a cell of a copy of the even
register, at the offsets of the child (the paper's "no cell is contained in two subtiles with different parents"). -/
def CellsDisjointOdd (w : Word) : Prop :=
  ∀ u1 u2 : Word, (stateAt w).tOdd = oddTile u1 → (stateAt w).tEven = evenTile u2 →
    ∀ a ∈ pOffsetsOdd (phase w == 1) (parentsAt w).odd (parentsAt w).even,
    ∀ b ∈ qOffsetsOdd (phase w == 1) (parentsAt w).odd (parentsAt w).even,
      ∀ s, s ∈ shiftS (cellSet (oddTile u1)) a → s ∈ shiftS (cellSet (evenTile u2)) b → False

/-- **(d) for the odd child from the cell facts.** `H1` for all standard tiles is `oddTile_hcc`/`evenTile_hcc` (w1); given `H2`
for all register tiles and the copy-level `H3`, the mixed-piece claim `MixedPiecesInMarksOdd w` holds. -/
theorem mixedOdd_of_cells (w : Word)
    (H2o : ∀ u : Word, ∀ z, BoundaryVertex (cellSet (oddTile u)) z → z ∈ marksOdd u)
    (H2e : ∀ u : Word, ∀ z, BoundaryVertex (cellSet (evenTile u)) z → z ∈ marksEven u)
    (H3 : CellsDisjointOdd w) : MixedPiecesInMarksOdd w := by
  unfold MixedPiecesInMarksOdd
  intro u1 u2 hT1 hT2 a ha b hb z h1 h2
  exact mixed_copies_of_cells (oddTile u1) (evenTile u2) (marksOdd u1) (marksEven u2) a b
    (tileH1_of_hcc _ (oddTile_hcc u1)) (tileH1_of_hcc _ (evenTile_hcc u2))
    (H2o u1) (H2e u2) (H3 u1 u2 hT1 hT2 a ha b hb) z h1 h2

end FLatticePaper.Tiles.CellRegisters
