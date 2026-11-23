import FLatticePaper.Tiles.NeighbourDisjoint
import FLatticePaper.Tiles.BoundaryWalks

/-! Task 50, part 2 (Q10): the row criterion for a boundary walk given only as a walk from a vertex (`IsBoundaryFrom`).

The row description of the tile (`mem_iff_nr`, `not_overlap_of`) uses the lower-left condition of `IsBoundaryWordAt` nowhere: the
proofs read the walk only through its sum, its nodup and its edge set. These copies take `IsBoundaryFrom`, so that the rotated
tile (whose lower-left vertex is not identified) satisfies the row criterion from the cyclic shift of its walk. -/

namespace FLatticePaper.Tiles

open FLatticePaper.Tiles.BoundaryWalks (IsBoundaryFrom)

theorem rowCount_eq_edges_from {T : CellTile} {c : GInt} {w : F2Word} (h : IsBoundaryFrom T c w) (b a : ℤ) :
    rowCount T.boundaryEdges b a = ((edgesFrom c w).map (vsgn b a)).sum := by
  obtain ⟨-, hnd, hset⟩ := h
  unfold rowCount
  rw [← hset, List.sum_toFinset _ hnd]

theorem mem_iff_interval_from {T : CellTile} {c : GInt} {w1 w2 : F2Word}
    (hT : IsBoundaryFrom T c (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne) (a b : ℤ) :
    ((a, b) : GInt) ∈ T ↔
      (c.2 ≤ b ∧ b < c.2 + cntI (w1 ++ w2)) ∧
        colS (w1.map Unit4.neg ++ w2.map Unit4.neg) (c + F2Word.sum (w1 ++ w2)) b ≤ a ∧
        a < colN (w1 ++ w2) c b := by
  have hrc := row_scan T b a
  rw [rowCount_eq_edges_from hT b a] at hrc
  have hword : boundaryWordOf w1 w2 = (w1 ++ w2) ++ (w1.map Unit4.neg ++ w2.map Unit4.neg) := by
    simp [boundaryWordOf, hat_rev, List.append_assoc]
  rw [hword, edgesFrom_append, List.map_append, List.sum_append] at hrc
  have hnoNeg : ∀ x ∈ w1 ++ w2, x ≠ .negI := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases h1 x hx with rfl | rfl <;> simp
    · rcases h2 x hx with rfl | rfl <;> simp
  have hnoI : ∀ x ∈ w1.map Unit4.neg ++ w2.map Unit4.neg, x ≠ .i := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      rcases h1 y hy with rfl | rfl <;> simp [Unit4.neg]
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      rcases h2 y hy with rfl | rfl <;> simp [Unit4.neg]
  rw [sum_north (w1 ++ w2) hnoNeg c b a, sum_south _ hnoI (c + F2Word.sum (w1 ++ w2)) b a] at hrc
  have hsnd : (c + F2Word.sum (w1 ++ w2)).2 = c.2 + cntI (w1 ++ w2) := by
    rw [Prod.snd_add, sum_snd _ hnoNeg]
  have hneg : cntNegI (w1.map Unit4.neg ++ w2.map Unit4.neg) = cntI (w1 ++ w2) := by
    rw [cntNegI_append, cntNegI_map_neg, cntNegI_map_neg, cntI_append]
  rw [hsnd, hneg] at hrc
  unfold cellInd at hrc
  have key := ite_sum_iff _ _ _ hrc
  rw [key]
  constructor
  · rintro ⟨hn, g1, g2, g3⟩
    refine ⟨⟨by omega, by omega⟩, g3, ?_⟩
    by_contra hc
    exact hn ⟨by omega, by omega, by omega⟩
  · rintro ⟨⟨h1', h2'⟩, h3, h4⟩
    refine ⟨fun hP1 => absurd hP1.2.2 (not_le.mpr h4), ?_⟩
    exact ⟨by omega, by omega, h3⟩

theorem mem_iff_nr_from {T : CellTile} {c : GInt} {w1 w2 : F2Word}
    (hT : IsBoundaryFrom T c (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne) (a b : ℤ) :
    ((a, b) : GInt) ∈ T ↔
      (0 ≤ b - c.2 ∧ b - c.2 < cntI w1 + cntI w2) ∧ Srow c w1 w2 (b - c.2) ≤ a ∧ a < Nrow c w1 w2 (b - c.2) := by
  rw [mem_iff_interval_from hT h1 h2 a b, cntI_append]
  have hn1 : ∀ x ∈ w1, x ≠ .negI := fun x hx => by
    rcases h1 x hx with h | h <;> simp [h]
  have hn2 : ∀ x ∈ w2, x ≠ .negI := fun x hx => by
    rcases h2 x hx with h | h <;> simp [h]
  by_cases hr : c.2 ≤ b ∧ b < c.2 + (cntI w1 + cntI w2)
  · rw [N_eq c w1 w2 hn1 b hr.1, S_eq c w1 w2 hn1 hn2 b hr.2]
    exact ⟨fun h => ⟨⟨by omega, by omega⟩, h.2⟩, fun h => ⟨⟨by omega, by omega⟩, h.2⟩⟩
  · constructor
    · rintro ⟨hr', -, -⟩
      exact absurd ⟨hr'.1, hr'.2⟩ hr
    · rintro ⟨hr', -, -⟩
      exact absurd ⟨by omega, by omega⟩ hr

theorem not_overlap_of_from {T : CellTile} {c : GInt} {w1 w2 : F2Word}
    (hT : IsBoundaryFrom T c (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne) (n1 n2 : ℤ)
    (hdisj : ∀ t : ℤ, 0 ≤ t → t < cntI w1 + cntI w2 → 0 ≤ t - n2 → t - n2 < cntI w1 + cntI w2 →
      Nrow c w1 w2 t ≤ Srow c w1 w2 (t - n2) + n1 ∨ Nrow c w1 w2 (t - n2) + n1 ≤ Srow c w1 w2 t) :
    ¬ Overlap T (n1, n2) := by
  rintro ⟨⟨a, b⟩, hx, hxn⟩
  have hxn' : ((a - n1, b - n2) : GInt) ∈ T := by
    simpa using hxn
  rw [mem_iff_nr_from hT h1 h2] at hx hxn'
  obtain ⟨⟨hx0, hx1⟩, hxs, hxN⟩ := hx
  obtain ⟨⟨hy0, hy1⟩, hys, hyN⟩ := hxn'
  have hsh : b - n2 - c.2 = (b - c.2) - n2 := by ring
  rw [hsh] at hys hyN hy0 hy1
  rcases hdisj (b - c.2) hx0 hx1 hy0 hy1 with d | d <;> linarith

end FLatticePaper.Tiles
