import FLatticePaper.Tiles.AlmostTiling

/-! Adjacency of consecutive columns of an edge-connected cell tile: if the tile has a cell in column `t` and a cell in column `t + 1`,
some row is occupied in both columns. A path of edge-adjacent cells from column `t` to column `t + 1` must cross between the two
columns, and the only adjacency across two consecutive columns is a horizontal step in one row. -/

namespace FLatticePaper.Tiles.StackedAdjacency

open FLatticePaper.Tiles

/-- **A common row.** In an edge-connected cell tile, a cell of column `t` and a cell of column `t + 1` give a row occupied in both
columns. -/
theorem common_row_of_edge_connected (T : CellTile) (hT : EdgeConnected T) (t : Int) (a b : GInt)
    (ha : a ∈ T) (hb : b ∈ T) (ha1 : a.1 = t) (hb1 : b.1 = t + 1) :
    ∃ y : Int, ((t, y) : GInt) ∈ T ∧ ((t + 1, y) : GInt) ∈ T := by
  have key : ∀ d e : GInt, Relation.ReflTransGen (fun p q => p ∈ T ∧ q ∈ T ∧ CellAdj p q) d e → d.1 ≤ t →
      (e.1 ≤ t ∨ ∃ y : Int, ((t, y) : GInt) ∈ T ∧ ((t + 1, y) : GInt) ∈ T) := by
    intro d e h hd
    induction h with
    | refl => exact Or.inl hd
    | @tail y z _ hstep ih =>
      rcases ih with hy | hex
      · obtain ⟨hyT, hzT, hadj⟩ := hstep
        rcases hadj with h1 | h1 | h1 | h1
        · -- `z = y + gOne`: the step moves right
          by_cases hz : z.1 ≤ t
          · exact Or.inl hz
          · have hy1 : y.1 = t := by
              have : z.1 = y.1 + 1 := by rw [h1]; simp [gOne]
              omega
            refine Or.inr ⟨y.2, ?_, ?_⟩
            · have e : ((t, y.2) : GInt) = y := by ext <;> simp [hy1]
              rw [e]; exact hyT
            · have e : ((t + 1, y.2) : GInt) = z := by
                ext
                · simp only; rw [h1]; simp [gOne, hy1]
                · simp only; rw [h1]; simp [gOne]
              rw [e]; exact hzT
        · by_cases hz : z.1 ≤ t
          · exact Or.inl hz
          · exfalso
            have : z.1 = y.1 - 1 := by rw [h1]; simp [gOne]
            omega
        · exact Or.inl (by rw [h1]; simp [gI]; omega)
        · exact Or.inl (by rw [h1]; simp [gI]; omega)
      · exact Or.inr hex
  have hpath := hT a ha b hb
  rcases key a b hpath (le_of_eq ha1) with hb' | hex
  · omega
  · exact hex

end FLatticePaper.Tiles.StackedAdjacency
