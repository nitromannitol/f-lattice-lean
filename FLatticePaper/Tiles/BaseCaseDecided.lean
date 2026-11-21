import FLatticePaper.Tiles.BaseCaseAlmostTiling

/-! The two global inputs `NoFirstCrossing` and `NoFarAdjacency` of `almost_square_tiling`, reduced to finite checks.

A lattice vector `u ∈ latticeOf v₁ v₂` has the two Cramer numerators of `u` divisible by the determinant of `(v₁, v₂)`
(`latticeOf_DIVL`). The overlaps of the tile with a translate by a nonzero lattice vector are differences of two cells
of the tile, and the surrounding vectors are the eight pairs `(k, k') ≠ (0,0)` with `|k|, |k'| ≤ 1`. So both inputs
follow from decidable statements over the finite cell set, and these are decided for `d ≤ 7`. -/

namespace FLatticePaper.Tiles

/-- The Cramer numerators of `u` in the basis `(v₁, v₂)`: divisible by the determinant when `u ∈ latticeOf v₁ v₂`. -/
def DIVL (v₁ v₂ u : GInt) : Prop :=
  (v₁.1 * v₂.2 - v₁.2 * v₂.1) ∣ (u.1 * v₂.2 - u.2 * v₂.1) ∧
    (v₁.1 * v₂.2 - v₁.2 * v₂.1) ∣ (v₁.1 * u.2 - v₁.2 * u.1)

instance (v₁ v₂ u : GInt) : Decidable (DIVL v₁ v₂ u) := by
  unfold DIVL
  infer_instance

theorem latticeOf_DIVL {v₁ v₂ u : GInt} (hu : u ∈ latticeOf v₁ v₂) : DIVL v₁ v₂ u := by
  obtain ⟨k, k', hk⟩ := hu
  subst hk
  exact ⟨⟨k, by ring⟩, ⟨k', by ring⟩⟩

/-- The eight surrounding coefficient pairs `(k, k') ≠ (0,0)` with `|k|, |k'| ≤ 1`. -/
def surr8 : List (ℤ × ℤ) := [(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (1, -1), (-1, 1), (-1, -1)]

/-- The surrounding vector of a coefficient pair. -/
def svec (v₁ v₂ : GInt) (kk : ℤ × ℤ) : GInt :=
  (kk.1 * v₁.1 + kk.2 * v₂.1, kk.1 * v₁.2 + kk.2 * v₂.2)

theorem surr8_bounds : ∀ kk ∈ surr8, -1 ≤ kk.1 ∧ kk.1 ≤ 1 ∧ -1 ≤ kk.2 ∧ kk.2 ≤ 1 ∧ kk ≠ (0, 0) := by
  decide

theorem svec_mem_surround (v₁ v₂ : GInt) {kk : ℤ × ℤ} (hkk : kk ∈ surr8) :
    svec v₁ v₂ kk ∈ surroundVectors v₁ v₂ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := surr8_bounds kk hkk
  exact ⟨kk.1, kk.2, h1, h2, h3, h4, h5, rfl⟩

/-- `NoFirstCrossing` from a finite check on pairs of cells. -/
theorem noFirstCrossing_of_decide (T : CellTile) (v₁ v₂ : GInt)
    (h : ∀ x ∈ T, ∀ y ∈ T, DIVL v₁ v₂ (x - y) → x - y ≠ 0 →
      ∃ kk ∈ surr8, ∃ z ∈ T, z - svec v₁ v₂ kk ∈ T) :
    NoFirstCrossing T v₁ v₂ := by
  refine ⟨fun u hu hne hov => ?_⟩
  obtain ⟨x, hx, hxu⟩ := hov
  have hdiv : DIVL v₁ v₂ (x - (x - u)) := by
    rw [sub_sub_cancel]
    exact latticeOf_DIVL hu
  have hne' : x - (x - u) ≠ 0 := by
    rw [sub_sub_cancel]
    exact hne
  obtain ⟨kk, hkk, z, hz, hzk⟩ := h x hx (x - u) hxu hdiv hne'
  exact ⟨svec v₁ v₂ kk, svec_mem_surround v₁ v₂ hkk, ⟨z, hz, hzk⟩⟩

/-- `NoFarAdjacency` from a finite check on the cells adjacent to the tile. -/
theorem noFarAdjacency_of_decide (T : CellTile) (v₁ v₂ : GInt)
    (h : ∀ c ∈ T, ∀ e ∈ [((1 : ℤ), (0 : ℤ)), (0, 1), (-1, 0), (0, -1)], c + e ∉ T →
      (∃ kk ∈ surr8, c + e - svec v₁ v₂ kk ∈ T) ∨ (∀ p ∈ T, ¬ DIVL v₁ v₂ (c + e - p))) :
    NoFarAdjacency T v₁ v₂ := by
  refine ⟨fun d hd hdT => ?_⟩
  obtain ⟨c, hc, e, he, rfl⟩ := hd
  rcases h c hc e he hdT with ⟨kk, hkk, hz⟩ | hp
  · exact Or.inl ⟨svec v₁ v₂ kk, svec_mem_surround v₁ v₂ hkk, hz⟩
  · refine Or.inr (fun u hu hdu => ?_)
    apply hp (c + e - u) hdu
    rw [sub_sub_cancel]
    exact latticeOf_DIVL hu

/-! ### The decided instances for `d ≤ 7` -/

/-- `prop:base_cases` (a) for the reciprocal staircase `d = 3`, with both global inputs decided. -/
theorem stair_global_d3 :
    IsRegularAlmostTiling (stairCells (2 * ((0 : ℕ) : ℤ) + 3)) (almostV₁ (gH (stairH 0)))
        (almostV₂ (gV (stairV 0))) ∧
      EdgeSharingClause (stairCells (2 * ((0 : ℕ) : ℤ) + 3)) (almostV₁ (gH (stairH 0)))
        (almostV₂ (gV (stairV 0))) :=
  stair_almost_tiling 0
    (by rw [almostV1_stair, almostV2_stair]; exact noFirstCrossing_of_decide _ _ _ (by decide +kernel))
    (by rw [almostV1_stair, almostV2_stair]; exact noFarAdjacency_of_decide _ _ _ (by decide +kernel))

/-- `prop:base_cases` (a) for the reciprocal staircase `d = 5`, with both global inputs decided. -/
theorem stair_global_d5 :
    IsRegularAlmostTiling (stairCells (2 * ((1 : ℕ) : ℤ) + 3)) (almostV₁ (gH (stairH 1)))
        (almostV₂ (gV (stairV 1))) ∧
      EdgeSharingClause (stairCells (2 * ((1 : ℕ) : ℤ) + 3)) (almostV₁ (gH (stairH 1)))
        (almostV₂ (gV (stairV 1))) :=
  stair_almost_tiling 1
    (by rw [almostV1_stair, almostV2_stair]; exact noFirstCrossing_of_decide _ _ _ (by decide +kernel))
    (by rw [almostV1_stair, almostV2_stair]; exact noFarAdjacency_of_decide _ _ _ (by decide +kernel))

/-- `prop:base_cases` (a) for the reciprocal staircase `d = 7`, with both global inputs decided. -/
theorem stair_global_d7 :
    IsRegularAlmostTiling (stairCells (2 * ((2 : ℕ) : ℤ) + 3)) (almostV₁ (gH (stairH 2)))
        (almostV₂ (gV (stairV 2))) ∧
      EdgeSharingClause (stairCells (2 * ((2 : ℕ) : ℤ) + 3)) (almostV₁ (gH (stairH 2)))
        (almostV₂ (gV (stairV 2))) :=
  stair_almost_tiling 2
    (by rw [almostV1_stair, almostV2_stair]; exact noFirstCrossing_of_decide _ _ _ (by decide +kernel))
    (by rw [almostV1_stair, almostV2_stair]; exact noFarAdjacency_of_decide _ _ _ (by decide +kernel))

/-- `prop:base_cases` (a) for the doubled staircase `d = 4`, with both global inputs decided. -/
theorem ladder_global_d4 :
    IsRegularAlmostTiling (ladderCells (2 * ((0 : ℕ) : ℤ) + 4)) (almostV₁ (gH (ladderH (0 + 1))))
        (almostV₂ (gV (ladderV (0 + 1)))) ∧
      EdgeSharingClause (ladderCells (2 * ((0 : ℕ) : ℤ) + 4)) (almostV₁ (gH (ladderH (0 + 1))))
        (almostV₂ (gV (ladderV (0 + 1)))) :=
  ladder_almost_tiling 0
    (by rw [almostV1_ladder, almostV2_ladder]; exact noFirstCrossing_of_decide _ _ _ (by decide +kernel))
    (by rw [almostV1_ladder, almostV2_ladder]; exact noFarAdjacency_of_decide _ _ _ (by decide +kernel))

/-- `prop:base_cases` (a) for the doubled staircase `d = 6`, with both global inputs decided. -/
theorem ladder_global_d6 :
    IsRegularAlmostTiling (ladderCells (2 * ((1 : ℕ) : ℤ) + 4)) (almostV₁ (gH (ladderH (1 + 1))))
        (almostV₂ (gV (ladderV (1 + 1)))) ∧
      EdgeSharingClause (ladderCells (2 * ((1 : ℕ) : ℤ) + 4)) (almostV₁ (gH (ladderH (1 + 1))))
        (almostV₂ (gV (ladderV (1 + 1)))) :=
  ladder_almost_tiling 1
    (by rw [almostV1_ladder, almostV2_ladder]; exact noFirstCrossing_of_decide _ _ _ (by decide +kernel))
    (by rw [almostV1_ladder, almostV2_ladder]; exact noFarAdjacency_of_decide _ _ _ (by decide +kernel))

end FLatticePaper.Tiles
