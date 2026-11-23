import FLatticePaper.Tiles.PackUnit
import FLatticePaper.Tiles.PseudoSquare

/-! Task 50, part 2 (Q10): the quarter turn of the tile, for the V-direction of the packing.

The quarter turn `rotCells` of a tile whose walk is `boundaryWordOf w₁ w₂` has the walk `boundaryWordOf (w₂·(−i)) (w₁·i)` after a
cyclic shift (`pseudoBoundaryWord_rotation`). Its first word `w₂·(−i)` is the admissible word of the packing, so the H-direction
of the rotated tile is the V-direction of the tile. The overlaps are transported back by `overlap_rotCells_iff`. -/

namespace FLatticePaper.Tiles

open FLatticePaper.Tiles.BoundaryTransport
open FLatticePaper.Tiles.BoundaryWalks (IsBoundaryFrom isBoundaryFrom_rotate isBoundaryFrom_rotCells)

/-- The boundary walk of the quarter turn: `boundaryWordOf (w₂·(−i)) (w₁·i)` from the rotated start, after the cyclic shift. -/
theorem isBoundaryFrom_rotCells_word (T : CellTile) (c : GInt) (w1 w2 : F2Word)
    (h : IsBoundaryFrom T c (boundaryWordOf w1 w2)) :
    ∃ c' : GInt, IsBoundaryFrom (rotCells T) c' (boundaryWordOf (w2.map Unit4.mulNegI) (w1.map Unit4.mulI)) := by
  have hR := isBoundaryFrom_rotCells T c _ h
  have hk : w1.length + w2.length + w1.length ≤ ((boundaryWordOf w1 w2).map Unit4.mulI).length := by
    simp only [List.length_map, boundaryWordOf, List.length_append, F2Word.hat, F2Word.rev, List.length_reverse]
    omega
  have hrot := isBoundaryFrom_rotate (rotCells T) (rotI c) ((boundaryWordOf w1 w2).map Unit4.mulI) hR
    (w1.length + w2.length + w1.length) hk
  refine ⟨rotI c + F2Word.sum (((boundaryWordOf w1 w2).map Unit4.mulI).take (w1.length + w2.length + w1.length)), ?_⟩
  have e : boundaryWordOf (w2.map Unit4.mulNegI) (w1.map Unit4.mulI) =
      ((boundaryWordOf w1 w2).map Unit4.mulI).rotate (w1.length + w2.length + w1.length) :=
    pseudoBoundaryWord_rotation w1 w2
  rw [e]
  exact hrot

/-! ### Coordinates of the quarter turn of the words -/

theorem mulNegI_eq_three (w : F2Word) :
    w.map Unit4.mulNegI = ((w.map Unit4.mulI).map Unit4.mulI).map Unit4.mulI := by
  simp only [List.map_map]
  rfl

theorem sum_fst_mulNegI (w : F2Word) : (F2Word.sum (w.map Unit4.mulNegI)).1 = (F2Word.sum w).2 := by
  rw [mulNegI_eq_three, F2Word_sum_map_mulI, F2Word_sum_map_mulI, F2Word_sum_map_mulI]
  simp [rotI]

theorem sum_snd_mulNegI (w : F2Word) : (F2Word.sum (w.map Unit4.mulNegI)).2 = -(F2Word.sum w).1 := by
  rw [mulNegI_eq_three, F2Word_sum_map_mulI, F2Word_sum_map_mulI, F2Word_sum_map_mulI]
  simp [rotI]

theorem sum_fst_mulI (w : F2Word) : (F2Word.sum (w.map Unit4.mulI)).1 = -(F2Word.sum w).2 := by
  rw [F2Word_sum_map_mulI]
  simp [rotI]

theorem sum_snd_mulI (w : F2Word) : (F2Word.sum (w.map Unit4.mulI)).2 = (F2Word.sum w).1 := by
  rw [F2Word_sum_map_mulI]
  simp [rotI]

/-- The letters of `w·(−i)` for `w` with letters `i, −1` are not `−i`. -/
theorem ne_negI_mulNegI {w : F2Word} (h : ∀ x ∈ w, x = .i ∨ x = .negOne) :
    ∀ x ∈ w.map Unit4.mulNegI, x ≠ .negI := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  rcases h y hy with rfl | rfl <;> decide

/-- The letters of `w·i` for `w` with letters `1, i` are not `−i`. -/
theorem ne_negI_mulI {w : F2Word} (h : ∀ x ∈ w, x = .one ∨ x = .i) :
    ∀ x ∈ w.map Unit4.mulI, x ≠ .negI := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  rcases h y hy with rfl | rfl <;> decide

theorem cntI_mulNegI {w : F2Word} (h : ∀ x ∈ w, x = .i ∨ x = .negOne) :
    cntI (w.map Unit4.mulNegI) = -(F2Word.sum w).1 := by
  rw [← sum_snd _ (ne_negI_mulNegI h), sum_snd_mulNegI]

theorem cntI_mulI {w : F2Word} (h : ∀ x ∈ w, x = .one ∨ x = .i) :
    cntI (w.map Unit4.mulI) = (F2Word.sum w).1 := by
  rw [← sum_snd _ (ne_negI_mulI h), sum_snd_mulI]

/-! ### Transport of the overlaps by the quarter turn -/

theorem rotCInv_sub_rotI (x w : GInt) : rotCInv (x - rotI w) = rotCInv x - w := by
  apply Prod.ext
  · simp [rotCInv, rotI]
  · simp [rotCInv, rotI]
    ring

/-- The quarter turn transports the overlaps: `T` and `T + rotI w` overlap exactly when `T` and `T + w` do. -/
theorem overlap_rotCells_iff (T : CellTile) (w : GInt) : Overlap (rotCells T) (rotI w) ↔ Overlap T w := by
  constructor
  · rintro ⟨x, hx, hxw⟩
    refine ⟨rotCInv x, (mem_rotCells T x).mp hx, ?_⟩
    have h := (mem_rotCells T (x - rotI w)).mp hxw
    rw [rotCInv_sub_rotI] at h
    exact h
  · rintro ⟨y, hy, hyw⟩
    refine ⟨rotC y, (mem_rotCells T (rotC y)).mpr ?_, ?_⟩
    · rw [rotCInv_rotC]
      exact hy
    · rw [mem_rotCells, rotCInv_sub_rotI, rotCInv_rotC]
      exact hyw

end FLatticePaper.Tiles
