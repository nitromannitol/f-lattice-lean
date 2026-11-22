import FLatticePaper.Tiles.NearStairBoundary

/-! The near-one ladder tile `nladderN d` (`d = 2m+4`): its cell tile is the quarter turn of the ladder cell tile
`ladderCells d`, shifted by `(d+1, d-2)`. Its boundary walk is the repo walk `ladderWord m`, cut at the top-left vertex
`(2-d, d+1)`, turned by the quarter turn and translated; the word is `boundaryWordOf (v₀ of 2^(m+1)) (i · w₀ of 3^(m+1))`. -/

namespace FLatticePaper.Tiles.NearLadderBoundary

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard FLatticePaper.Tiles.BoundaryTransport FLatticePaper.Tiles.BoundaryWalks
open FLatticePaper.Tiles.BaseCellIdentities FLatticePaper.Tiles.StandardClause
open FLatticePaper.Tiles.NearStairBoundary

/-- The cell tile of `nladderN (2m+4)` is the turned ladder cell tile, shifted by `(d+1, d-2)`. -/
theorem cellTileOf_nladderN (m : ℕ) :
    cellTileOf (nladderN (2 * (m : ℤ) + 4)) =
      (rotCells (ladderCells (2 * (m : ℤ) + 4))).image (· + ((2 * (m : ℤ) + 5), 2 * (m : ℤ) + 2)) := by
  have hd : (4 : ℤ) ≤ 2 * (m : ℤ) + 4 := by omega
  have hd2 : (2 : ℤ) ≤ 2 * (m : ℤ) + 4 := by omega
  ext ⟨x, y⟩
  rw [mem_cellTileOf, cellCorners_subset_iff, mem_image_add_iff, mem_rotCells, mem_ladderCells _ hd]
  simp only [nladderN, mem_shift, mem_nladderF hd2, rotCInv, ladderInT, Prod.fst_sub, Prod.snd_sub]
  constructor <;> intro h <;> omega

/-- The lower-left vertex of the turned, shifted ladder cell tile is `(0, 0)`. -/
theorem nladder_lowerLeft (m : ℕ) :
    IsLowerLeft ((rotCells (ladderCells (2 * (m : ℤ) + 4))).image
      (· + ((2 * (m : ℤ) + 5), 2 * (m : ℤ) + 2))) (0, 0) := by
  have hd : (4 : ℤ) ≤ 2 * (m : ℤ) + 4 := by omega
  unfold IsLowerLeft
  refine ⟨?_, ?_⟩
  · unfold CellTile.vertices
    rw [Finset.mem_biUnion]
    refine ⟨(0, 0), ?_, by simp [cellCorners]⟩
    rw [Finset.mem_image]
    refine ⟨(-(2 * (m : ℤ) + 5), -(2 * (m : ℤ) + 2)), ?_, by ext <;> simp⟩
    rw [mem_rotCells, mem_ladderCells _ hd]
    simp only [rotCInv, ladderInT]
    omega
  · intro p hp
    unfold CellTile.vertices at hp
    rw [Finset.mem_biUnion] at hp
    obtain ⟨c, hc, hpc⟩ := hp
    rw [Finset.mem_image] at hc
    obtain ⟨q, hq, rfl⟩ := hc
    rw [mem_rotCells, mem_ladderCells _ hd] at hq
    simp only [rotCInv, ladderInT] at hq
    simp only [cellCorners, Finset.mem_insert, Finset.mem_singleton, gOne, gI, Prod.ext_iff, Prod.fst_add,
      Prod.snd_add] at hpc
    show 0 ≤ p.2 ∧ (p.2 = 0 → 0 ≤ p.1)
    omega

/-- The first `12m+25` letters of `ladderWord m`: the walk up to the top-left vertex. -/
def lU (m : ℕ) : F2Word :=
  List.replicate (2 * m + 3) Unit4.one ++ [Unit4.i] ++ List.replicate (2 * m + 5) Unit4.one ++
    ([Unit4.i, Unit4.i] ++ (List.replicate (2 * m + 1 + 1) [Unit4.negOne, Unit4.i]).flatten ++ [Unit4.i]) ++
    (List.replicate (2 * m + 3) Unit4.negOne ++ [Unit4.negI] ++ List.replicate (2 * m + 5) Unit4.negOne)

/-- The last letters of `ladderWord m`. -/
def lV (m : ℕ) : F2Word :=
  [Unit4.negI, Unit4.negI] ++ (List.replicate (2 * m + 1 + 1) [Unit4.one, Unit4.negI]).flatten ++ [Unit4.negI]

theorem ladderWord_split (m : ℕ) : ladderWord m = lU m ++ lV m := by
  simp [ladderWord, lU, lV, List.append_assoc]

theorem lU_length (m : ℕ) : (lU m).length = 12 * m + 25 := by
  simp [lU, List.length_flatten, List.map_replicate, List.sum_replicate]
  omega

/-- The top segment sums to the top-left vertex `(2-d, d+1)` relative to `(0, 0)`, `d = 2m+4`. -/
theorem sum_lU (m : ℕ) : F2Word.sum (lU m) = (-(2 * (m : ℤ) + 2), 2 * (m : ℤ) + 5) := by
  simp only [lU, F2Word.sum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Unit4.vec, List.map_append,
    List.sum_append]
  ext <;> simp [Unit4.vec] <;> ring

/-- The last segment, turned by `i`, is the base edge `v₀ (2^(m+1))`. -/
theorem lV_map (m : ℕ) : (lV m).map Unit4.mulI =
    [Unit4.one] ++ (List.replicate (2 * m + 1 + 1) [Unit4.one, Unit4.i]).flatten ++ [Unit4.one, Unit4.one] := by
  unfold lV
  simp only [List.map_append, List.map_cons, List.map_nil, map_flatten_rep, Unit4.mulI]
  exact aux_pos (2 * m + 1 + 1)

/-- The top segment, turned by `i`: `i w₁`, then `-v₀`, then `-(i w₁)`. -/
theorem lU_map (m : ℕ) : (lU m).map Unit4.mulI =
    (List.replicate (2 * m + 3) Unit4.i ++ [Unit4.negOne] ++ List.replicate (2 * m + 5) Unit4.i) ++
      (([Unit4.negOne] ++ (List.replicate (2 * m + 1 + 1) [Unit4.negOne, Unit4.negI]).flatten ++
          [Unit4.negOne, Unit4.negOne]) ++
        (List.replicate (2 * m + 3) Unit4.negI ++ [Unit4.one] ++ List.replicate (2 * m + 5) Unit4.negI)) := by
  unfold lU
  simp only [List.map_append, List.map_cons, List.map_nil, List.map_replicate, map_flatten_rep, Unit4.mulI]
  rw [aux_neg (2 * m + 1 + 1)]
  simp only [List.append_assoc]

theorem baseThree_one (k : ℕ) : (baseThreeEdges k).1 =
    List.replicate (2 * k + 1) Unit4.one ++ [Unit4.i] ++ List.replicate (2 * k + 3) Unit4.one := by
  have e1 : List.replicate (2 * k + 1) Unit4.one = List.replicate (2 * k) Unit4.one ++ [Unit4.one] :=
    List.replicate_succ'
  have e2 : List.replicate (2 * (k + 1) + 1) Unit4.one =
      List.replicate (2 * (k + 1)) Unit4.one ++ [Unit4.one] := List.replicate_succ'
  simp only [baseThreeEdges, oneOne_eq]
  rw [show 2 * k + 3 = 2 * (k + 1) + 1 by ring, e1, e2]
  simp

/-- The reciprocal base edge `w₀ (3^(m+1))` is `1^(2m+3) i 1^(2m+5)`. -/
theorem W1_eq (m : ℕ) : (baseThreeEdges (m + 1)).1 =
    List.replicate (2 * m + 3) Unit4.one ++ [Unit4.i] ++ List.replicate (2 * m + 5) Unit4.one := by
  rw [baseThree_one, show 2 * (m + 1) + 1 = 2 * m + 3 by ring, show 2 * (m + 1) + 3 = 2 * m + 5 by ring]

/-- The base edge `v₀ (2^(m+1))` is `1 (1i)^(2m+2) 1 1`. -/
theorem V0_eq (m : ℕ) : (baseTwoEdges (m + 1)).2 =
    [Unit4.one] ++ (List.replicate (2 * m + 1 + 1) [Unit4.one, Unit4.i]).flatten ++ [Unit4.one, Unit4.one] := by
  simp only [baseTwoEdges, oneI, show 2 * (m + 1) = 2 * m + 1 + 1 by ring]

/-- The ladder walk, turned by `i` and cut at the top-left vertex, is the boundary word of `(v₀, i·w₀)`. -/
theorem ladder_word_identity (m : ℕ) :
    boundaryWordOf (baseTwoEdges (m + 1)).2 ((baseThreeEdges (m + 1)).1.map Unit4.mulI) =
      (lV m ++ lU m).map Unit4.mulI := by
  have hsplit : (lV m ++ lU m).map Unit4.mulI = (lV m).map Unit4.mulI ++ (lU m).map Unit4.mulI := by
    simp only [List.map_append]
  rw [V0_eq, W1_eq, hsplit, lV_map, lU_map]
  unfold boundaryWordOf
  rw [hat_rev_map_neg, hat_rev_map_neg]
  simp only [List.map_append, List.map_cons, List.map_nil, List.map_replicate, map_flatten_rep, Unit4.mulI,
    Unit4.neg, List.append_assoc]

/-- The near-one ladder `nladderN (2m+4)` has boundary word `boundaryWordOf (v₀ (2^(m+1))) (i · w₀ (3^(m+1)))`. -/
theorem nladderN_boundary (m : ℕ) :
    IsBoundaryWordAt (cellTileOf (nladderN (2 * (m : ℤ) + 4))) (0, 0)
      (boundaryWordOf (baseTwoEdges (m + 1)).2 ((baseThreeEdges (m + 1)).1.map Unit4.mulI)) := by
  rw [cellTileOf_nladderN, ladder_word_identity, isBoundaryWordAt_iff]
  refine ⟨nladder_lowerLeft m, ?_⟩
  have hB : IsBoundaryFrom (ladderCells (2 * (m : ℤ) + 4)) (0, 0) (ladderWord m) :=
    ((isBoundaryWordAt_iff _ _ _).1 (ladder_boundary m)).2
  have hle : 12 * m + 25 ≤ (ladderWord m).length := by
    rw [ladderWord_split, List.length_append, lU_length]
    omega
  have hR := isBoundaryFrom_rotate _ _ _ hB (12 * m + 25) hle
  have hrot : (ladderWord m).rotate (12 * m + 25) =
      (ladderWord m).drop (12 * m + 25) ++ (ladderWord m).take (12 * m + 25) :=
    List.rotate_eq_drop_append_take hle
  rw [hrot, ladderWord_split, List.drop_left' (lU_length m), List.take_left' (lU_length m)] at hR
  have hC := isBoundaryFrom_rotCells _ _ _ hR
  have hT := isBoundaryFrom_translate _ _ ((2 * (m : ℤ) + 5), 2 * (m : ℤ) + 2) _ hC
  have hst : rotI ((0, 0) + F2Word.sum (lU m)) + ((2 * (m : ℤ) + 5), 2 * (m : ℤ) + 2) = (0, 0) := by
    rw [sum_lU]
    ext <;> simp [rotI]
  rw [hst] at hT
  exact hT

/-- The near-one ladder `nladderN 2` (the base word `2^0`): checked on its finitely many cells. -/
theorem nladderN_two_boundary :
    IsBoundaryWordAt (cellTileOf (nladderN 2)) (0, 0)
      (boundaryWordOf (baseTwoEdges 0).2 ((baseThreeEdges 0).1.map Unit4.mulI)) := by
  decide

end FLatticePaper.Tiles.NearLadderBoundary
