import FLatticePaper.Tiles.RowChain
import FLatticePaper.Tiles.BaseCellIdentities

/-! Task 53, step 1: the base families. The cell tiles of the base tiles `stairF d`, `ladderF d`, `nstairN d`, `nladderN d`
are row chains (`CellRowChain`), hence edge-connected and free of checkerboard vertices, for all `d` in the ranges used
by the recursion. The stair and ladder cell tiles are the repo's `stairCells`, `ladderCells`
(`BaseCellIdentities`); the near families are computed here from the site membership and shifted. -/

namespace FLatticePaper.Tiles.BaseFamilies

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
  FLatticePaper.Tiles.StandardClause FLatticePaper.Tiles.BaseCellIdentities

/-- The cells of `nstairF d`: the lower-left corners whose four corners lie in `nstairF d`. -/
def nstairCellP (d a b : ℤ) : Prop :=
  (0 ≤ a ∧ a ≤ d ∧ 1 ≤ b ∧ b ≤ 2 * d - 2 ∧ 0 ≤ b - a ∧ b - a ≤ d - 1) ∨ (a = 0 ∧ b = d) ∨ (a = d ∧ b = d - 1)

/-- The cells of `nladderF d`: the lower-left corners whose four corners lie in `nladderF d`. -/
def nladderCellP (d a b : ℤ) : Prop :=
  ((-1 ≤ a ∧ a ≤ d ∧ 1 ≤ b ∧ b ≤ 3 * d - 2 ∧ 0 ≤ b - a ∧ b - a ≤ 2 * d) ∧
      ¬(a = -1 ∧ b < d + 2) ∧ ¬(a = d ∧ 2 * d - 3 < b)) ∨
    (a = -1 ∧ b = 2 * d) ∨ (a = d ∧ b = d - 1)

theorem mem_cellTileOf_nstairF (d : ℤ) (hd : 2 ≤ d) (a b : ℤ) :
    (a, b) ∈ cellTileOf (nstairF d) ↔ nstairCellP d a b := by
  rw [mem_cellTileOf, cellCorners_subset_iff]
  simp only [mem_nstairF hd, nstairCellP]
  constructor <;> intro h <;> omega

theorem mem_cellTileOf_nladderF (d : ℤ) (hd : 2 ≤ d) (a b : ℤ) :
    (a, b) ∈ cellTileOf (nladderF d) ↔ nladderCellP d a b := by
  rw [mem_cellTileOf, cellCorners_subset_iff]
  simp only [mem_nladderF hd, nladderCellP]
  constructor <;> intro h <;> omega

/-- The near-one staircase `nstairN d` is `nstairF d` shifted down by one: its cell `(a, b)` is the cell `(a, b + 1)`. -/
theorem mem_cellTileOf_nstairN (d : ℤ) (hd : 2 ≤ d) (a b : ℤ) :
    (a, b) ∈ cellTileOf (nstairN d) ↔ nstairCellP d a (b + 1) := by
  unfold nstairN
  rw [mem_cellTileOf, cellCorners_subset_iff]
  simp only [mem_shift, mem_nstairF hd, nstairCellP, Prod.fst_sub, Prod.snd_sub]
  constructor <;> intro h <;> omega

/-- The near-one ladder `nladderN d` is `nladderF d` shifted down by one. -/
theorem mem_cellTileOf_nladderN (d : ℤ) (hd : 2 ≤ d) (a b : ℤ) :
    (a, b) ∈ cellTileOf (nladderN d) ↔ nladderCellP d a (b + 1) := by
  unfold nladderN
  rw [mem_cellTileOf, cellCorners_subset_iff]
  simp only [mem_shift, mem_nladderF hd, nladderCellP, Prod.fst_sub, Prod.snd_sub]
  constructor <;> intro h <;> omega

/-! ### The staircase and the ladder (repo cell tiles) -/

theorem cellRowChain_stairCells (d : ℤ) (hd : 3 ≤ d) : CellRowChain (stairCells d) :=
  cellRowChain_of_witness (stairCells d) (fun a b => stairInT d a b) (fun a b => mem_stairCells d hd (a, b))
    0 d (fun b => if b ≤ d - 1 then 1 - b else 1)
    (by
      intro a b h
      unfold stairInT at h
      omega)
    (by
      intro b a₁ a₂ a₃ h₁ h₃ h12 h23
      unfold stairInT at h₁ h₃ ⊢
      omega)
    (by
      intro b hb0 hb1
      try dsimp only
      refine ⟨?_, fun hlt => ?_⟩ <;> unfold stairInT <;> split_ifs <;> omega)

theorem cellRowChain_ladderCells (d : ℤ) (hd : 4 ≤ d) : CellRowChain (ladderCells d) :=
  cellRowChain_of_witness (ladderCells d) (fun a b => ladderInT d a b) (fun a b => mem_ladderCells d hd (a, b))
    0 (d + 1) (fun b => if b = 0 then 0 else if b ≤ d - 1 then 1 - b else if b = d then 3 else d + 1)
    (by
      intro a b h
      unfold ladderInT at h
      omega)
    (by
      intro b a₁ a₂ a₃ h₁ h₃ h12 h23
      unfold ladderInT at h₁ h₃ ⊢
      omega)
    (by
      intro b hb0 hb1
      try dsimp only
      refine ⟨?_, fun hlt => ?_⟩ <;> unfold ladderInT <;> split_ifs <;> omega)

/-! ### The near families: row chains of the shifted cell sets -/

theorem cellRowChain_nstairN (d : ℤ) (hd : 2 ≤ d) : CellRowChain (cellTileOf (nstairN d)) :=
  cellRowChain_of_witness (cellTileOf (nstairN d)) (fun a b => nstairCellP d a (b + 1))
    (fun a b => mem_cellTileOf_nstairN d hd a b) 0 (2 * d - 3) (fun b => if b + 1 ≤ d then b + 1 else d)
    (by
      intro a b h
      unfold nstairCellP at h
      omega)
    (by
      intro b a₁ a₂ a₃ h₁ h₃ h12 h23
      unfold nstairCellP at h₁ h₃ ⊢
      omega)
    (by
      intro b hb0 hb1
      try dsimp only
      refine ⟨?_, fun hlt => ?_⟩ <;> unfold nstairCellP <;> split_ifs <;> omega)

theorem cellRowChain_nladderN (d : ℤ) (hd : 2 ≤ d) : CellRowChain (cellTileOf (nladderN d)) :=
  cellRowChain_of_witness (cellTileOf (nladderN d)) (fun a b => nladderCellP d a (b + 1))
    (fun a b => mem_cellTileOf_nladderN d hd a b) 0 (3 * d - 3) (fun b => if b + 1 ≤ d - 1 then b + 1 else d - 1)
    (by
      intro a b h
      unfold nladderCellP at h
      omega)
    (by
      intro b a₁ a₂ a₃ h₁ h₃ h12 h23
      unfold nladderCellP at h₁ h₃ ⊢
      omega)
    (by
      intro b hb0 hb1
      try dsimp only
      refine ⟨?_, fun hlt => ?_⟩ <;> unfold nladderCellP <;> split_ifs <;> omega)

/-! ### The base families as cell tiles of the base tiles -/

/-- The cell tile of `stairF d` (`d ≥ 3`) is a row chain. -/
theorem cellRowChain_stairF (d : ℤ) (hd : 3 ≤ d) : CellRowChain (cellTileOf (stairF d)) := by
  rw [cellTileOf_stairF d hd]
  exact cellRowChain_stairCells d hd

/-- The cell tile of `ladderF d` (`d ≥ 4`) is a row chain. -/
theorem cellRowChain_ladderF (d : ℤ) (hd : 4 ≤ d) : CellRowChain (cellTileOf (ladderF d)) := by
  rw [cellTileOf_ladderF d hd]
  exact cellRowChain_ladderCells d hd

/-- The cell tile of `nstairN d` (`d ≥ 3`, odd in the recursion) is a row chain. -/
theorem cellRowChain_nstairN' (d : ℤ) (hd : 3 ≤ d) : CellRowChain (cellTileOf (nstairN d)) :=
  cellRowChain_nstairN d (by omega)

/-- The cell tile of `nladderN d` (`d ≥ 4`, even in the recursion) is a row chain. -/
theorem cellRowChain_nladderN' (d : ℤ) (hd : 4 ≤ d) : CellRowChain (cellTileOf (nladderN d)) :=
  cellRowChain_nladderN d (by omega)

end FLatticePaper.Tiles.BaseFamilies
