import FLatticePaper.Tiles.CoveringRows

/-! Witnesses for the successor condition `SuccCover`. A right end `(N_t + 1, c.2 + t)` is covered by a lattice translate
of a vertex of the tile: the row of vertices of `T` at height `h` is the union of the closed row intervals `[S_h, N_h]`
(cells of row `h`, lower corners) and `[S_{h-1}, N_{h-1}]` (cells of row `h-1`, upper corners). -/

namespace FLatticePaper.Tiles

/-- The column `a` lies in the closed row interval of the tile at relative row `j`. -/
def InRow (c : GInt) (w1 w2 : F2Word) (j a : ℤ) : Prop :=
  0 ≤ j ∧ j < cntI w1 + cntI w2 ∧ Srow c w1 w2 j ≤ a ∧ a ≤ Nrow c w1 w2 j

/-- A column in the closed interval of row `j` gives vertices of the tile at heights `c.2 + j` and `c.2 + j + 1`. -/
theorem vert_row {T : CellTile} {c : GInt} {w1 w2 : F2Word}
    (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne)
    {j a : ℤ} (hA : InRow c w1 w2 j a) :
    ((a, c.2 + j) : GInt) ∈ T.vertices ∧ ((a, c.2 + j + 1) : GInt) ∈ T.vertices := by
  obtain ⟨hj0, hj1, ha1, ha2⟩ := hA
  have hne := rows_nonempty hT h1 h2 j hj0 hj1
  have hmem : ∀ b : ℤ, ((b, c.2 + j) : GInt) ∈ T ↔ Srow c w1 w2 j ≤ b ∧ b < Nrow c w1 w2 j := fun b => by
    rw [mem_iff_nr hT h1 h2, show c.2 + j - c.2 = j by ring]
    exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨⟨hj0, hj1⟩, h.1, h.2⟩⟩
  rcases lt_or_eq_of_le ha2 with hlt | heq
  · have hc : ((a, c.2 + j) : GInt) ∈ T := (hmem a).mpr ⟨ha1, hlt⟩
    exact ⟨vert_of_mem_cell hc (by simp [cellCorners]),
      vert_of_mem_cell hc (by simp [cellCorners, gI])⟩
  · have hc : ((a - 1, c.2 + j) : GInt) ∈ T := (hmem (a - 1)).mpr ⟨by omega, by omega⟩
    refine ⟨vert_of_mem_cell hc ?_, vert_of_mem_cell hc ?_⟩
    · simp only [cellCorners, Finset.mem_insert, Finset.mem_singleton]
      right; left
      ext <;> simp [gOne, heq]
    · simp only [cellCorners, Finset.mem_insert, Finset.mem_singleton]
      right; right; right
      ext <;> simp [gOne, gI, heq]

/-- A point `x` is covered by the translate `u` when `x - u` is the lower vertex of row `j`. -/
theorem cov_row0 {T : CellTile} {c : GInt} {w1 w2 : F2Word} {L : Set GInt}
    (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne)
    {x u : GInt} {j : ℤ} (hu : u ∈ L) (hA : InRow c w1 w2 j (x.1 - u.1)) (hy : x.2 - u.2 = c.2 + j) :
    Cov T L x := by
  refine ⟨u, hu, ?_⟩
  have e : x - u = (x.1 - u.1, c.2 + j) := Prod.ext (by simp) (by simp [hy])
  rw [e]
  exact (vert_row hT h1 h2 hA).1

/-- As `cov_row0`, for the upper vertex of row `j`, at height `c.2 + j + 1`. -/
theorem cov_row1 {T : CellTile} {c : GInt} {w1 w2 : F2Word} {L : Set GInt}
    (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne)
    {x u : GInt} {j : ℤ} (hu : u ∈ L) (hA : InRow c w1 w2 j (x.1 - u.1)) (hy : x.2 - u.2 = c.2 + j + 1) :
    Cov T L x := by
  refine ⟨u, hu, ?_⟩
  have e : x - u = (x.1 - u.1, c.2 + j + 1) := Prod.ext (by simp) (by simp [hy])
  rw [e]
  exact (vert_row hT h1 h2 hA).2

/-- The translate `-g2` covers the right end `(N_t + 1, c.2 + t)` when `N_t + X2` lies in the row `t + r - 1`. -/
theorem cov_bot_negG2 {T : CellTile} {c : GInt} {w1 w2 : F2Word}
    (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne)
    (hn1 : ∀ x ∈ w1, x ≠ .negI) (hn2 : ∀ x ∈ w2, x ≠ .negI) {t : ℤ}
    (hA : InRow c w1 w2 (t + cntI w2 - 1) (Nrow c w1 w2 t + (F2Word.sum w2).1)) :
    Cov T (latticeOf (almostV₁ w1) (almostV₂ w2)) (Nrow c w1 w2 t + 1, c.2 + t) :=
  cov_row1 (j := t + cntI w2 - 1) hT h1 h2 (lattice_g2_mul hn1 hn2 (-1)) (by convert hA using 2; simp; ring) (by simp; ring)

/-- The translate `-g2` covers the upper right end `(N_t + 1, c.2 + t + 1)` when `N_t + X2` lies in row `t + r`. -/
theorem cov_top_negG2 {T : CellTile} {c : GInt} {w1 w2 : F2Word}
    (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne)
    (hn1 : ∀ x ∈ w1, x ≠ .negI) (hn2 : ∀ x ∈ w2, x ≠ .negI) {t : ℤ}
    (hA : InRow c w1 w2 (t + cntI w2) (Nrow c w1 w2 t + (F2Word.sum w2).1)) :
    Cov T (latticeOf (almostV₁ w1) (almostV₂ w2)) (Nrow c w1 w2 t + 1, c.2 + t + 1) :=
  cov_row1 (j := t + cntI w2) hT h1 h2 (lattice_g2_mul hn1 hn2 (-1)) (by convert hA using 2; simp; ring) (by simp; ring)

/-- The tile itself covers the upper right end `(N_t + 1, c.2 + t + 1)` when `N_t + 1` lies in row `t + 1`. -/
theorem cov_top_zero {T : CellTile} {c : GInt} {w1 w2 : F2Word} {L : Set GInt} (hL : (0 : GInt) ∈ L)
    (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne) {t : ℤ}
    (hA : InRow c w1 w2 (t + 1) (Nrow c w1 w2 t + 1)) :
    Cov T L (Nrow c w1 w2 t + 1, c.2 + t + 1) :=
  cov_row0 (j := t + 1) hT h1 h2 hL (by simpa using hA) (by simp [add_assoc])

/-- The translate `g1 = almost V₁` covers the upper right end `(N_t + 1, c.2 + t + 1)` when `N_t + 1 - P` lies in row
`t - q` (for `t ≥ q`, where `q` is the number of north steps of `w1` and `P` the first coordinate sum). -/
theorem cov_top_g1 {T : CellTile} {c : GInt} {w1 w2 : F2Word} {t : ℤ}
    (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne)
    (hn1 : ∀ x ∈ w1, x ≠ .negI)
    (hA : InRow c w1 w2 (t - cntI w1) (Nrow c w1 w2 t + 1 - (F2Word.sum w1).1)) :
    Cov T (latticeOf (almostV₁ w1) (almostV₂ w2)) (Nrow c w1 w2 t + 1, c.2 + t + 1) := by
  refine cov_row0 (j := t - cntI w1) hT h1 h2 (u := almostV₁ w1) ?_ ?_ ?_
  · exact ⟨1, 0, by ext <;> simp⟩
  · simpa [almostV₁_eq w1 hn1] using hA
  · simp [almostV₁_eq w1 hn1]; ring

end FLatticePaper.Tiles
