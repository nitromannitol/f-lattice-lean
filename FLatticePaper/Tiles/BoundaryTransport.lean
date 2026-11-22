import FLatticePaper.Tiles.BaseCellIdentities
import FLatticePaper.Tiles.BottomEdges

/-! Boundary edges under the quarter turn of cell tiles.

The quarter turn of a cell with lower-left corner `(a, b)` is the cell `(-b-1, a)`: its corners are the turns of its
corners, and the vertices turn by `rotI (x, y) = (-y, x)`. A boundary edge of `T` turns into a boundary edge of the turned
tile (`boundaryEdges_rotCells`), so a boundary walk turns into a boundary walk, with letters multiplied by `i`. -/

namespace FLatticePaper.Tiles.BoundaryTransport

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles

/-- The quarter turn of a cell (on lower-left corners): `(a, b) ↦ (-b-1, a)`. -/
def rotC (p : GInt) : GInt := (-p.2 - 1, p.1)

/-- The inverse quarter turn of a cell: `(a, b) ↦ (b, -a-1)`. -/
def rotCInv (p : GInt) : GInt := (p.2, -p.1 - 1)

/-- The quarter turn of a cell tile. -/
def rotCells (T : CellTile) : CellTile := T.image rotC

/-- The inverse quarter turn of a cell tile. -/
def rotCellsInv (T : CellTile) : CellTile := T.image rotCInv

/-- The inverse of `rotI` on vertices: `(x, y) ↦ (y, -x)`. -/
def rotIInv (z : GInt) : GInt := (z.2, -z.1)

/-- The turn of a directed edge: both endpoints turned by `rotI`. -/
def rotE (e : GInt × GInt) : GInt × GInt := (rotI e.1, rotI e.2)

/-- The inverse turn of a directed edge. -/
def rotEInv (e : GInt × GInt) : GInt × GInt := (rotIInv e.1, rotIInv e.2)

theorem rotCInv_rotC (p : GInt) : rotCInv (rotC p) = p := by
  ext <;> simp [rotCInv, rotC]

theorem rotC_rotCInv (p : GInt) : rotC (rotCInv p) = p := by
  ext <;> simp [rotC, rotCInv]

theorem rotE_rotEInv (x : GInt × GInt) : rotE (rotEInv x) = x := by
  ext <;> simp [rotE, rotEInv, rotI, rotIInv]

theorem rotCellsInv_rotCells (T : CellTile) : rotCellsInv (rotCells T) = T := by
  unfold rotCellsInv rotCells
  rw [Finset.image_image]
  have h : (rotCInv ∘ rotC) = id := funext rotCInv_rotC
  rw [h, Finset.image_id]

theorem mem_rotCells (T : CellTile) (p : GInt) : p ∈ rotCells T ↔ rotCInv p ∈ T := by
  unfold rotCells
  constructor
  · intro h
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 h
    rw [rotCInv_rotC]
    exact hq
  · intro h
    exact Finset.mem_image.2 ⟨rotCInv p, h, rotC_rotCInv p⟩

theorem mem_rotCellsInv (T : CellTile) (p : GInt) : p ∈ rotCellsInv T ↔ rotC p ∈ T := by
  unfold rotCellsInv
  constructor
  · intro h
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 h
    rw [rotC_rotCInv]
    exact hq
  · intro h
    exact Finset.mem_image.2 ⟨rotC p, h, rotCInv_rotC p⟩

/-- A boundary edge of `T` turns into a boundary edge of `rotCells T` (cells `(a, b) ↦ (-b-1, a)`). -/
theorem bShape_rotCells_of (T : CellTile) (e : GInt × GInt) (h : BShape T e) :
    BShape (rotCells T) (rotE e) := by
  obtain ⟨a, b, h⟩ := h
  rcases h with ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩
  · -- north edge of `(a, b)` turns into a top edge of the cell `(-b-1, a-1)`
    refine ⟨-b - 1, a - 1, Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩))⟩
    · ext <;> simp [rotE, rotI]
      all_goals omega
    · rw [mem_rotCells]
      have hc : rotCInv (-b - 1, a - 1) = (a - 1, b) := by
        ext <;> simp [rotCInv]
      rw [hc]
      exact h1
    · rw [mem_rotCells]
      have hc : rotCInv (-b - 1, a - 1 + 1) = (a, b) := by
        ext <;> simp [rotCInv]
      rw [hc]
      exact h2
  · -- top edge of `(a, b)` turns into a bottom edge of the cell `(-b-1, a)`
    refine ⟨-b - 1, a, Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩))⟩
    · ext <;> simp [rotE, rotI]
      all_goals omega
    · rw [mem_rotCells]
      have hc : rotCInv (-b - 1, a) = (a, b) := by
        ext <;> simp [rotCInv]
      rw [hc]
      exact h1
    · rw [mem_rotCells]
      have hc : rotCInv (-b - 1, a - 1) = (a - 1, b) := by
        ext <;> simp [rotCInv]
      rw [hc]
      exact h2
  · -- bottom edge of `(a, b)` turns into a north edge of the cell `(-b, a)`
    refine ⟨-b, a, Or.inl ⟨?_, ?_, ?_⟩⟩
    · ext <;> simp [rotE, rotI]
    · rw [mem_rotCells]
      have hc : rotCInv (-b - 1, a) = (a, b) := by
        ext <;> simp [rotCInv]
      rw [hc]
      exact h1
    · rw [mem_rotCells]
      have hc : rotCInv (-b, a) = (a, b - 1) := by
        ext <;> simp [rotCInv]
      rw [hc]
      exact h2
  · -- south-east edge of `(a, b)` turns into a top-west edge of the cell `(-b-1, a)`
    refine ⟨-b - 1, a, Or.inr (Or.inl ⟨?_, ?_, ?_⟩)⟩
    · ext <;> simp [rotE, rotI] <;> omega
    · rw [mem_rotCells]
      have hc : rotCInv (-b - 1, a) = (a, b) := by
        ext <;> simp [rotCInv]
      rw [hc]
      exact h1
    · rw [mem_rotCells]
      have hc : rotCInv (-b - 1 - 1, a) = (a, b + 1) := by
        ext <;> simp [rotCInv]
        all_goals omega
      rw [hc]
      exact h2

/-- A boundary edge of `T` turns (backwards) into a boundary edge of `rotCellsInv T`. -/
theorem bShape_rotCellsInv_of (T : CellTile) (e : GInt × GInt) (h : BShape T e) :
    BShape (rotCellsInv T) (rotEInv e) := by
  obtain ⟨a, b, h⟩ := h
  rcases h with ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩
  · -- north edge of `(a, b)` turns into a bottom edge of the cell `(b, -a)`
    refine ⟨b, -a, Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩))⟩
    · ext <;> simp [rotEInv, rotIInv]
    · rw [mem_rotCellsInv]
      have hc : rotC (b, -a) = (a - 1, b) := by
        ext <;> simp [rotC]
      rw [hc]
      exact h1
    · rw [mem_rotCellsInv]
      have hc : rotC (b, -a - 1) = (a, b) := by
        ext <;> simp [rotC]
      rw [hc]
      exact h2
  · -- top edge of `(a, b)` turns into a top edge of the cell `(b, -a-1)`
    refine ⟨b, -a - 1, Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩))⟩
    · ext <;> simp [rotEInv, rotIInv]
    · rw [mem_rotCellsInv]
      have hc : rotC (b, -a - 1) = (a, b) := by
        ext <;> simp [rotC]
      rw [hc]
      exact h1
    · rw [mem_rotCellsInv]
      have hc : rotC (b, -a - 1 + 1) = (a - 1, b) := by
        ext <;> simp [rotC]
      rw [hc]
      exact h2
  · -- bottom edge of `(a, b)` turns into a south edge of the cell `(b, -a-1)`
    refine ⟨b, -a - 1, Or.inr (Or.inl ⟨?_, ?_, ?_⟩)⟩
    · ext <;> simp [rotEInv, rotIInv]
      all_goals omega
    · rw [mem_rotCellsInv]
      have hc : rotC (b, -a - 1) = (a, b) := by
        ext <;> simp [rotC]
      rw [hc]
      exact h1
    · rw [mem_rotCellsInv]
      have hc : rotC (b - 1, -a - 1) = (a, b - 1) := by
        ext <;> simp [rotC]
      rw [hc]
      exact h2
  · -- south-east edge of `(a, b)` turns into a north edge of the cell `(b+1, -a-1)`
    refine ⟨b + 1, -a - 1, Or.inl ⟨?_, ?_, ?_⟩⟩
    · ext <;> simp [rotEInv, rotIInv]
      all_goals omega
    · rw [mem_rotCellsInv]
      have hc : rotC (b + 1 - 1, -a - 1) = (a, b) := by
        ext <;> simp [rotC]
      rw [hc]
      exact h1
    · rw [mem_rotCellsInv]
      have hc : rotC (b + 1, -a - 1) = (a, b + 1) := by
        ext <;> simp [rotC]
      rw [hc]
      exact h2

/-- The boundary edges of the quarter turn of a cell tile are the turned boundary edges. -/
theorem boundaryEdges_rotCells (T : CellTile) :
    (rotCells T).boundaryEdges = T.boundaryEdges.image rotE := by
  ext x
  rw [mem_boundaryEdges_iff_shape, Finset.mem_image]
  constructor
  · intro hx
    refine ⟨rotEInv x, ?_, ?_⟩
    · rw [mem_boundaryEdges_iff_shape]
      have h := bShape_rotCellsInv_of (rotCells T) x hx
      rw [rotCellsInv_rotCells] at h
      exact h
    · exact rotE_rotEInv x
  · rintro ⟨y, hy, rfl⟩
    rw [mem_boundaryEdges_iff_shape] at hy
    exact bShape_rotCells_of T y hy

end FLatticePaper.Tiles.BoundaryTransport
