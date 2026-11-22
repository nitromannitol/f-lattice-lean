import FLatticePaper.Tiles.BoundaryWalks
import FLatticePaper.Tiles.BaseCellIdentities
import FLatticePaper.Tiles.BaseCaseTiling

/-! The near-one stair tile `nstairN d` (`d = 2k+3`): its cell tile is the quarter turn of the reciprocal staircase
`stairCells d`, shifted to the lower-left vertex `(0, 0)`. Its boundary walk is the boundary walk of `stairCells d`
(`stairWord k`), cyclically shifted to the top-left vertex `(2-d, d+1)`, turned by the quarter turn, and translated. -/

namespace FLatticePaper.Tiles.NearStairBoundary

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard FLatticePaper.Tiles.BoundaryTransport FLatticePaper.Tiles.BoundaryWalks
open FLatticePaper.Tiles.BaseCellIdentities FLatticePaper.Tiles.StandardClause

/-- The cell tile of the near-one stair `nstairN (2k+3)` is the turned reciprocal staircase, shifted by `(d+1, d-2)`. -/
theorem cellTileOf_nstairN (k : ℕ) :
    cellTileOf (nstairN (2 * (k : ℤ) + 3)) =
      (rotCells (stairCells (2 * (k : ℤ) + 3))).image (· + ((2 * (k : ℤ) + 4), 2 * (k : ℤ) + 1)) := by
  have hd : (3 : ℤ) ≤ 2 * (k : ℤ) + 3 := by omega
  have hd2 : (2 : ℤ) ≤ 2 * (k : ℤ) + 3 := by omega
  ext ⟨x, y⟩
  rw [mem_cellTileOf, cellCorners_subset_iff, mem_image_add_iff, mem_rotCells, mem_stairCells _ hd]
  simp only [nstairN, mem_shift, mem_nstairF hd2, rotCInv, stairInT, Prod.fst_sub, Prod.snd_sub]
  constructor <;> intro h <;> omega

/-- The stair walk splits as `U ++ V`: the top segments `U` (through the top-left vertex) and the last segment `V`. -/
def nsU (k : ℕ) : F2Word :=
  List.replicate (2 * k + 3) Unit4.one ++
    ([Unit4.i, Unit4.i] ++ (List.replicate (2 * k + 1) [Unit4.negOne, Unit4.i]).flatten ++ [Unit4.i]) ++
    List.replicate (2 * k + 3) Unit4.negOne

/-- The last segment of the stair walk. -/
def nsV (k : ℕ) : F2Word :=
  [Unit4.negI, Unit4.negI] ++ (List.replicate (2 * k + 1) [Unit4.one, Unit4.negI]).flatten ++ [Unit4.negI]

theorem stairWord_split (k : ℕ) : stairWord k = nsU k ++ nsV k := by
  simp [stairWord, nsU, nsV, List.append_assoc]

/-- The sum of the top segments is the top-left vertex `(-(2k+1), 2k+4)` relative to `(0, 0)`. -/
theorem sum_nsU (k : ℕ) : F2Word.sum (nsU k) = (-(2 * (k : ℤ) + 1), 2 * (k : ℤ) + 4) := by
  simp only [nsU, F2Word.sum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Unit4.vec, List.map_append,
    List.sum_append]
  ext <;> simp [Unit4.vec] <;> ring

end FLatticePaper.Tiles.NearStairBoundary
