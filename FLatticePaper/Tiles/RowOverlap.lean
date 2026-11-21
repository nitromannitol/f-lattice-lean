import FLatticePaper.Tiles.CoveringRows

/-! Consecutive rows of an edge-connected tile overlap: a chain of edge-adjacent cells from row `t` to row `t+1` has a
vertical step, which is a column shared by the two rows (the tile is a simply connected union of cells, Sec. 4). -/

namespace FLatticePaper.Tiles

/-- A chain of steps from a point with `R` to a point without `R` contains a step from `R` to `¬R`. -/
theorem cross_of_chain {α : Type*} {r : α → α → Prop} {R : α → Prop} {x : α} (hx : R x) :
    ∀ {y : α}, Relation.ReflTransGen r x y → ¬ R y → ∃ a b, R a ∧ ¬ R b ∧ r a b := by
  intro y h
  induction h with
  | refl => intro hy; exact absurd hx hy
  | @tail b z _ hbz ih =>
    intro hz
    by_cases hb : R b
    · exact ⟨b, z, hb, hz, hbz⟩
    · exact ih hb

/-- The membership in a row of the tile, in absolute coordinates. -/
theorem mem_row_iff {T : CellTile} {c : GInt} {w1 w2 : F2Word}
    (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne)
    {j : ℤ} (hj0 : 0 ≤ j) (hj1 : j < cntI w1 + cntI w2) (b : ℤ) :
    ((b, c.2 + j) : GInt) ∈ T ↔ Srow c w1 w2 j ≤ b ∧ b < Nrow c w1 w2 j := by
  rw [mem_iff_nr hT h1 h2, show c.2 + j - c.2 = j by ring]
  exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨⟨hj0, hj1⟩, h.1, h.2⟩⟩

/-- Consecutive rows of the tile overlap: `S_{t+1} < N_t` and `S_t < N_{t+1}`. -/
theorem row_overlap {T : CellTile} {c : GInt} {w1 w2 : F2Word}
    (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2)) (hE : EdgeConnected T)
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne)
    {t : ℤ} (ht0 : 0 ≤ t) (ht1 : t + 1 < cntI w1 + cntI w2) :
    Srow c w1 w2 (t + 1) < Nrow c w1 w2 t ∧ Srow c w1 w2 t < Nrow c w1 w2 (t + 1) := by
  have hne0 := rows_nonempty hT h1 h2 t ht0 (by omega)
  have hne1 := rows_nonempty hT h1 h2 (t + 1) (by omega) ht1
  have hx : ((Nrow c w1 w2 t - 1, c.2 + t) : GInt) ∈ T :=
    (mem_row_iff hT h1 h2 ht0 (by omega) _).mpr ⟨by omega, by omega⟩
  have hy : ((Srow c w1 w2 (t + 1), c.2 + (t + 1)) : GInt) ∈ T :=
    (mem_row_iff hT h1 h2 (by omega) ht1 _).mpr ⟨le_refl _, hne1⟩
  have hchain := hE _ hx _ hy
  obtain ⟨a, b, ha, hb, hab⟩ := cross_of_chain (R := fun z : GInt => z.2 ≤ c.2 + t)
    (show (Nrow c w1 w2 t - 1, c.2 + t).2 ≤ c.2 + t from le_refl _) hchain
    (show ¬ ((Srow c w1 w2 (t + 1), c.2 + (t + 1)).2 ≤ c.2 + t) by simp)
  obtain ⟨haT, hbT, hadj⟩ := hab
  change a.2 ≤ c.2 + t at ha
  change ¬ b.2 ≤ c.2 + t at hb
  -- the adjacent pair is a vertical step from row `t` to row `t+1`
  have hvert : b = a + gI := by
    rcases hadj with h | h | h | h
    · exfalso
      have e : b.2 = a.2 := by rw [h]; simp [gOne]
      exact hb (by omega)
    · exfalso
      have e : b.2 = a.2 := by rw [h]; simp [gOne]
      exact hb (by omega)
    · exact h
    · exfalso
      have e : b.2 = a.2 - 1 := by rw [h]; simp [gI]
      exact hb (by omega)
  have ha2 : a.2 = c.2 + t := by
    have e : b.2 = a.2 + 1 := by rw [hvert]; simp [gI]
    omega
  have hA : Srow c w1 w2 t ≤ a.1 ∧ a.1 < Nrow c w1 w2 t :=
    (mem_row_iff hT h1 h2 ht0 (by omega) a.1).mp
      (by rw [show ((a.1, c.2 + t) : GInt) = a from Prod.ext rfl ha2.symm]; exact haT)
  have hB : Srow c w1 w2 (t + 1) ≤ a.1 ∧ a.1 < Nrow c w1 w2 (t + 1) :=
    (mem_row_iff hT h1 h2 (by omega) ht1 a.1).mp
      (by
        rw [show ((a.1, c.2 + (t + 1)) : GInt) = b from by
          rw [hvert]; exact Prod.ext (by simp [gI]) (by simp [gI, ha2]; ring)]
        exact hbT)
  exact ⟨by omega, by omega⟩

end FLatticePaper.Tiles
