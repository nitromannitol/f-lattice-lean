import FLatticePaper.Tiles.BoundaryWalks
import FLatticePaper.Tiles.BaseCellIdentities
import FLatticePaper.Tiles.BaseCaseTiling

/-! The near-one stair tile `nstairN d` (`d = 2k+3`): its cell tile is the quarter turn of the reciprocal staircase
`stairCells d`, shifted to the lower-left vertex `(0, 0)`. Its boundary walk is the boundary walk of `stairCells d`
(`stairWord k`), cyclically shifted to the top-left vertex, turned by the quarter turn and translated; the word is
`boundaryWordOf (w₀ of 2^k) (i · v₀ of 3^k)`. -/

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

/-- The top segment `U` of the stair walk: the letters up to and including the top-left vertex. -/
def nsU (k : ℕ) : F2Word :=
  List.replicate (2 * k + 3) Unit4.one ++
    ([Unit4.i, Unit4.i] ++ (List.replicate (2 * k + 1) [Unit4.negOne, Unit4.i]).flatten ++ [Unit4.i]) ++
    List.replicate (2 * k + 3) Unit4.negOne

/-- The last segment `V` of the stair walk. -/
def nsV (k : ℕ) : F2Word :=
  [Unit4.negI, Unit4.negI] ++ (List.replicate (2 * k + 1) [Unit4.one, Unit4.negI]).flatten ++ [Unit4.negI]

theorem stairWord_split (k : ℕ) : stairWord k = nsU k ++ nsV k := by
  simp [stairWord, nsU, nsV, List.append_assoc]

/-- The top segment sums to the top-left vertex `(-(2k+1), 2k+4)` relative to `(0, 0)`. -/
theorem sum_nsU (k : ℕ) : F2Word.sum (nsU k) = (-(2 * (k : ℤ) + 1), 2 * (k : ℤ) + 4) := by
  simp only [nsU, F2Word.sum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Unit4.vec, List.map_append,
    List.sum_append]
  ext <;> simp [Unit4.vec] <;> ring

theorem nsU_length (k : ℕ) : (nsU k).length = 8 * k + 11 := by
  simp [nsU, List.length_flatten, List.map_replicate, List.sum_replicate]
  omega

/-! ### Flattened pairs and the base words -/

theorem flat_shift_neg (m : ℕ) :
    (List.replicate m [Unit4.negOne, Unit4.negI]).flatten ++ [Unit4.negOne] =
      Unit4.negOne :: (List.replicate m [Unit4.negI, Unit4.negOne]).flatten := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ, List.flatten_cons, List.append_assoc, ih]
    simp [List.replicate_succ, List.flatten_cons]

/-- Mapping a letter-function over a flattened pair. -/
theorem map_flatten_rep (f : Unit4 → Unit4) (m : ℕ) (a b : Unit4) :
    ((List.replicate m [a, b]).flatten).map f = (List.replicate m [f a, f b]).flatten := by
  induction m with
  | zero => simp
  | succ m ih => simp only [List.replicate_succ, List.flatten_cons, List.map_append, ih, List.map_cons, List.map_nil]

/-- The two-letter shift identity on the negative pairs. -/
theorem aux_neg (m : ℕ) :
    [Unit4.negOne, Unit4.negOne] ++ (List.replicate m [Unit4.negI, Unit4.negOne]).flatten ++ [Unit4.negOne] =
      [Unit4.negOne] ++ (List.replicate m [Unit4.negOne, Unit4.negI]).flatten ++ [Unit4.negOne, Unit4.negOne] := by
  have h := flat_shift_neg m
  have e : [Unit4.negOne] ++ (List.replicate m [Unit4.negOne, Unit4.negI]).flatten ++ [Unit4.negOne, Unit4.negOne] =
      [Unit4.negOne] ++ ((List.replicate m [Unit4.negOne, Unit4.negI]).flatten ++ [Unit4.negOne]) ++ [Unit4.negOne] := by
    simp
  rw [e, h]
  simp

/-- The two-letter shift identity on the positive pairs. -/
theorem aux_pos (m : ℕ) :
    [Unit4.one, Unit4.one] ++ (List.replicate m [Unit4.i, Unit4.one]).flatten ++ [Unit4.one] =
      [Unit4.one] ++ (List.replicate m [Unit4.one, Unit4.i]).flatten ++ [Unit4.one, Unit4.one] := by
  have h := flat_shift m
  have e : [Unit4.one] ++ (List.replicate m [Unit4.one, Unit4.i]).flatten ++ [Unit4.one, Unit4.one] =
      [Unit4.one] ++ ((List.replicate m [Unit4.one, Unit4.i]).flatten ++ [Unit4.one]) ++ [Unit4.one] := by
    simp
  rw [e, h]
  simp

theorem oneOne_eq (n : ℕ) : oneOne n = List.replicate (2 * n) Unit4.one := by
  induction n with
  | zero => simp [oneOne]
  | succ n ih =>
    unfold oneOne at *
    rw [List.replicate_succ, List.flatten_cons, ih]
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, List.replicate_succ, List.replicate_succ]
    simp

theorem baseThree_two (k : ℕ) : (baseThreeEdges k).2 = List.replicate (2 * k + 3) Unit4.one := by
  simp only [baseThreeEdges, oneOne_eq]
  rw [show 2 * k + 3 = 1 + 2 * (k + 1) by ring, List.replicate_add]
  simp

/-- The reciprocal base edge `v₀ (3^k)` turned by `i` is `i^{2k+3}`. -/
theorem W2_eq (k : ℕ) :
    ((baseThreeEdges k).2).map Unit4.mulI = List.replicate (2 * k + 3) Unit4.i := by
  rw [baseThree_two, List.map_replicate]
  simp [Unit4.mulI]

/-- The last segment `V`, turned by `i`, is the base edge `w₀ (2^k)`. -/
theorem V_eq (k : ℕ) : (nsV k).map Unit4.mulI = (baseTwoEdges k).1 := by
  unfold nsV baseTwoEdges oneI
  simp only [List.map_append, List.map_cons, List.map_nil, map_flatten_rep, Unit4.mulI]
  exact aux_pos (2 * k + 1)

/-- The top segment `U`, turned by `i`: the letters `i^{2k+3}`, then the negated `w₀ (2^k)`, then `(-i)^{2k+3}`. -/
theorem nsU_map (k : ℕ) :
    (nsU k).map Unit4.mulI = List.replicate (2 * k + 3) Unit4.i ++
      ((baseTwoEdges k).1.map Unit4.neg ++ List.replicate (2 * k + 3) Unit4.negI) := by
  unfold nsU baseTwoEdges oneI
  simp only [List.map_append, List.map_cons, List.map_nil, List.map_replicate, map_flatten_rep, Unit4.mulI,
    Unit4.neg]
  rw [aux_neg (2 * k + 1)]
  simp only [List.append_assoc]

theorem hat_rev_map_neg (w : F2Word) : F2Word.hat (F2Word.rev w) = w.map Unit4.neg := by
  simp [F2Word.hat, F2Word.rev]

/-- The boundary word of the near-one stair is the turned, rotated stair word. -/
theorem word_identity (k : ℕ) :
    boundaryWordOf (baseTwoEdges k).1 ((baseThreeEdges k).2.map Unit4.mulI) =
      (nsV k ++ nsU k).map Unit4.mulI := by
  rw [List.map_append, V_eq, W2_eq]
  unfold boundaryWordOf
  rw [hat_rev_map_neg, hat_rev_map_neg, nsU_map, List.map_replicate]
  simp [List.append_assoc, Unit4.neg]

/-! ### The lower-left vertex -/

theorem nstair_lowerLeft (k : ℕ) :
    IsLowerLeft ((rotCells (stairCells (2 * (k : ℤ) + 3))).image (· + ((2 * (k : ℤ) + 4), 2 * (k : ℤ) + 1)))
      (0, 0) := by
  have hd : (3 : ℤ) ≤ 2 * (k : ℤ) + 3 := by omega
  unfold IsLowerLeft
  refine ⟨?_, ?_⟩
  · unfold CellTile.vertices
    rw [Finset.mem_biUnion]
    refine ⟨(0, 0), ?_, by simp [cellCorners]⟩
    rw [Finset.mem_image]
    refine ⟨(-(2 * (k : ℤ) + 4), -(2 * (k : ℤ) + 1)), ?_, by ext <;> simp⟩
    rw [mem_rotCells, mem_stairCells _ hd]
    simp only [rotCInv, stairInT]
    omega
  · intro p hp
    unfold CellTile.vertices at hp
    rw [Finset.mem_biUnion] at hp
    obtain ⟨c, hc, hpc⟩ := hp
    rw [Finset.mem_image] at hc
    obtain ⟨q, hq, rfl⟩ := hc
    rw [mem_rotCells, mem_stairCells _ hd] at hq
    simp only [rotCInv, stairInT] at hq
    simp only [cellCorners, Finset.mem_insert, Finset.mem_singleton, gOne, gI, Prod.ext_iff, Prod.fst_add,
      Prod.snd_add] at hpc
    show 0 ≤ p.2 ∧ (p.2 = 0 → 0 ≤ p.1)
    omega

/-! ### The near-one stair boundary -/

/-- The near-one stair `nstairN (2k+3)` has boundary word `boundaryWordOf (w₀ (2^k)) (i · v₀ (3^k))` from `(0, 0)`. -/
theorem nstairN_boundary (k : ℕ) :
    IsBoundaryWordAt (cellTileOf (nstairN (2 * (k : ℤ) + 3))) (0, 0)
      (boundaryWordOf (baseTwoEdges k).1 ((baseThreeEdges k).2.map Unit4.mulI)) := by
  rw [cellTileOf_nstairN, word_identity, isBoundaryWordAt_iff]
  refine ⟨nstair_lowerLeft k, ?_⟩
  have hB : IsBoundaryFrom (stairCells (2 * (k : ℤ) + 3)) (0, 0) (stairWord k) :=
    ((isBoundaryWordAt_iff _ _ _).1 (stairWord_boundary k)).2
  have hle : 8 * k + 11 ≤ (stairWord k).length := by
    rw [stairWord_split, List.length_append, nsU_length]
    omega
  have hR := isBoundaryFrom_rotate _ _ _ hB (8 * k + 11) hle
  have hrot : (stairWord k).rotate (8 * k + 11) =
      (stairWord k).drop (8 * k + 11) ++ (stairWord k).take (8 * k + 11) :=
    List.rotate_eq_drop_append_take hle
  rw [hrot, stairWord_split, List.drop_left' (nsU_length k), List.take_left' (nsU_length k)] at hR
  have hC := isBoundaryFrom_rotCells _ _ _ hR
  have hT := isBoundaryFrom_translate _ _ ((2 * (k : ℤ) + 4), 2 * (k : ℤ) + 1) _ hC
  have hst : rotI ((0, 0) + F2Word.sum (nsU k)) + ((2 * (k : ℤ) + 4), 2 * (k : ℤ) + 1) = (0, 0) := by
    rw [sum_nsU]
    ext <;> simp [rotI]
  rw [hst] at hT
  exact hT

end FLatticePaper.Tiles.NearStairBoundary
