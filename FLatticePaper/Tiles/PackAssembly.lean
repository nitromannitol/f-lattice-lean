import FLatticePaper.Tiles.PackHStrip

/-! Task 50, part 2 (Q10): no lattice translate of the tile overlaps it, hence `NoFirstCrossing`.

For a nonzero lattice vector `u = k v₁ + k' v₂` (with `v₁ = (Σw₁ + i)`, `v₂ = (Σw₂ − 1)`), the row criterion `not_overlap_of`
holds for all rows: for `k' ≥ 1` the translate lies to the left of the tile by the H-strip inequalities (`Nrow_le_H`,
`Srow_ge_H`), for `k' ≤ −1` to the right by the same inequalities, and for `k' = 0` by the iterated first row inequality
(`row_v1_iter`). So `Overlap T u` is false for every nonzero lattice vector, which makes `NoFirstCrossing` vacuous. -/

namespace FLatticePaper.Tiles

/-- The first lattice vector `Σw₁ + i` in coordinates: `(A, B + 1)`. -/
theorem almostV1_coords {w1 : F2Word} (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) :
    almostV₁ w1 = ((F2Word.sum w1).1, cntI w1 + 1) := by
  have hs := sum_snd w1 (fun x hx => by rcases h1 x hx with rfl | rfl <;> decide)
  apply Prod.ext
  · simp [almostV₁, gI]
  · simp [almostV₁, gI, hs]

/-- The second lattice vector `Σw₂ − 1` in coordinates: `(A₂ − 1, D)`. -/
theorem almostV2_coords {w2 : F2Word} (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne) :
    almostV₂ w2 = ((F2Word.sum w2).1 - 1, cntI w2) := by
  have hs := sum_snd w2 (fun x hx => by rcases h2 x hx with rfl | rfl <;> decide)
  apply Prod.ext
  · simp [almostV₂, gOne]
  · simp [almostV₂, gOne, hs]

/-- **No lattice translate overlaps the tile**: for `(k, k') ≠ (0, 0)` the translate by `k v₁ + k' v₂` is disjoint from the
tile (the row criterion `not_overlap_of`, for every row). -/
theorem not_overlap_lattice {T : CellTile} {c : GInt} {w1 w2 : F2Word}
    (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne)
    (hA1 : Admissible w1) (hA2 : Admissible (w2.map Unit4.mulNegI)) (k k' : ℤ) (hne : (k, k') ≠ (0, 0)) :
    ¬ Overlap T (k * (F2Word.sum w1).1 + k' * ((F2Word.sum w2).1 - 1), k * (cntI w1 + 1) + k' * cntI w2) := by
  have hq := cntI_nonneg w1
  have hr := cntI_nonneg w2
  have hsum2 := sum_fst_nonpos_of_i_negOne w2 h2
  refine not_overlap_of hT h1 h2 _ _ ?_
  intro t ht0 ht1 hd0 hd1
  rcases lt_trichotomy k' 0 with hneg | hzero | hpos
  · -- `k' ≤ −1`: the translate lies to the right of the tile, the first disjunct
    left
    have hN := Nrow_le_H c h1 h2 t ht0
    have hS := Srow_ge_H c hA1 h1 h2 _ hd0 hd1
    have ea : t - (k * (cntI w1 + 1) + k' * cntI w2) + 1 - cntI w2 =
        (t + 1 - (k' + 1) * cntI w2) + (-k) * (cntI w1 + 1) := by ring
    rw [ea] at hS
    have hP := Hent_add_mul_period w1 h1 (-k) (t + 1 - (k' + 1) * cntI w2)
    rw [hP] at hS
    have hM := Hent_mono_le w1 h1 (show t + 1 ≤ t + 1 - (k' + 1) * cntI w2 by nlinarith)
    have ek : (-k) * (F2Word.sum w1).1 = -(k * (F2Word.sum w1).1) := by ring
    have hσ : 0 ≤ (k' + 1) * ((F2Word.sum w2).1 - 1) := by nlinarith
    have ek' : k' * ((F2Word.sum w2).1 - 1) = ((F2Word.sum w2).1 - 1) + (k' - 1) * ((F2Word.sum w2).1 - 1) := by ring
    have hσ' : (k' + 1) * ((F2Word.sum w2).1 - 1) = k' * ((F2Word.sum w2).1 - 1) + ((F2Word.sum w2).1 - 1) := by ring
    rw [ek] at hS
    linarith
  · -- `k' = 0`: the translates by `k v₁`
    subst hzero
    rcases lt_trichotomy k 0 with hk | hk | hk
    · -- `k ≤ −1`: the translate lies to the right, the second disjunct
      obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = -(n : ℤ) := ⟨(-k).toNat, by omega⟩
      have hn : 1 ≤ n := by omega
      right
      have e1 : t - (-(n : ℤ) * (cntI w1 + 1) + 0 * cntI w2) = t + (n : ℤ) * (cntI w1 + 1) := by ring
      rw [e1] at hd0 hd1 ⊢
      have key := row_v1_iter c h1 h2 hA2 n hn (t + (n : ℤ) * (cntI w1 + 1)) (by linarith) hd1
      have e2 : t + (n : ℤ) * (cntI w1 + 1) - (n : ℤ) * (cntI w1 + 1) = t := by ring
      rw [e2] at key
      have e3 : -(n : ℤ) * (F2Word.sum w1).1 + 0 * ((F2Word.sum w2).1 - 1) = -((n : ℤ) * (F2Word.sum w1).1) := by ring
      rw [e3]
      linarith
    · exact absurd (Prod.ext hk (by simp)) hne
    · -- `k ≥ 1`: the translate lies to the left, the first disjunct
      obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = (n : ℤ) := ⟨k.toNat, by omega⟩
      have hn : 1 ≤ n := by omega
      left
      have e1 : t - ((n : ℤ) * (cntI w1 + 1) + 0 * cntI w2) = t - (n : ℤ) * (cntI w1 + 1) := by ring
      have e2 : (n : ℤ) * (F2Word.sum w1).1 + 0 * ((F2Word.sum w2).1 - 1) = (n : ℤ) * (F2Word.sum w1).1 := by ring
      rw [e1, e2]
      exact row_v1_iter c h1 h2 hA2 n hn t (by linarith) ht1
  · -- `k' ≥ 1`: the translate lies to the left of the tile, the second disjunct
    right
    have hN := Nrow_le_H c h1 h2 _ hd0
    have hS := Srow_ge_H c hA1 h1 h2 t ht0 ht1
    have ea : t - (k * (cntI w1 + 1) + k' * cntI w2) + 1 = (t + 1 - k' * cntI w2) + (-k) * (cntI w1 + 1) := by ring
    rw [ea] at hN
    have hP := Hent_add_mul_period w1 h1 (-k) (t + 1 - k' * cntI w2)
    rw [hP] at hN
    have hM := Hent_mono_le w1 h1 (show t + 1 - k' * cntI w2 ≤ t + 1 - cntI w2 by nlinarith)
    have ek : (-k) * (F2Word.sum w1).1 = -(k * (F2Word.sum w1).1) := by ring
    have hk1 : k' * ((F2Word.sum w2).1 - 1) ≤ (F2Word.sum w2).1 - 1 := by nlinarith
    linarith

/-- **`NoFirstCrossing` for the tile of the almost square tiling**: a nonzero lattice translate overlapping the tile would
contradict `not_overlap_lattice`, so the propagation holds vacuously. -/
theorem noFirstCrossing_of_boundary {T : CellTile} {c : GInt} {w1 w2 : F2Word}
    (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne)
    (hA1 : Admissible w1) (hA2 : Admissible (w2.map Unit4.mulNegI)) :
    NoFirstCrossing T (almostV₁ w1) (almostV₂ w2) := by
  refine ⟨fun u hu hne hov => ?_⟩
  exfalso
  obtain ⟨k, k', rfl⟩ := hu
  rw [almostV1_coords h1, almostV2_coords h2] at hov
  have hkk : (k, k') ≠ (0, 0) := by
    rintro h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    apply hne
    simp
  exact not_overlap_lattice hT h1 h2 hA1 hA2 k k' hkk hov

end FLatticePaper.Tiles
