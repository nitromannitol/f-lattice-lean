import FLattice.Auxiliary.FundamentalDiamond

/-!
# A geometric reduction from edge exclusions to harmonic peak cones

This conditional geometric lemma applies to a predicate in the three
scalar matrix coordinates. Its translation, reflection and edge-exclusion
premises must be supplied by the actual integer superharmonic constructions.
The proof only rounds to a fundamental diamond and extends a radius to its
boundary; no nearest-center or Voronoi characterization is assumed.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.ConeClassificationGeometry

open MatrixCoordinates

/-- Integer peak translations, coordinate reflections and exclusion of
the first-quadrant edge imply that every admitted matrix lies below a peak. -/
theorem exists_peak_above_of_invariances
    (Γ : ℝ → ℝ → ℝ → Prop)
    (hShift : ∀ a b c : ℝ, Γ a b c → ∀ s t : ℤ,
      Γ (a - ((s : ℝ) - (t : ℝ))) (b - ((s : ℝ) + (t : ℝ))) c)
    (hFlipA : ∀ a b c : ℝ, Γ a b c → Γ (-a) b c)
    (hFlipB : ∀ a b c : ℝ, Γ a b c → Γ a (-b) c)
    (hEdgeExclusion : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → u + v = 1 →
      ∀ a b c : ℝ, Γ a b c →
        ¬(matrix a b c - matrix u v (-radius u v)).PosDef)
    (a b c : ℝ) (hΓ : Γ a b c) :
    ∃ s t : ℤ,
      (matrix ((s : ℝ) - (t : ℝ)) ((s : ℝ) + (t : ℝ)) 0 - matrix a b c).PosSemidef := by
  obtain ⟨s, t, hDiamond⟩ := FundamentalDiamond.exists_peak_translate a b
  let a' := a - ((s : ℝ) - (t : ℝ))
  let b' := b - ((s : ℝ) + (t : ℝ))
  have hTranslated : Γ a' b' c := hShift a b c hΓ s t
  have hFirst : Γ |a'| b' c := by
    by_cases ha : 0 ≤ a'
    · simpa only [abs_of_nonneg ha] using hTranslated
    · simpa only [abs_of_neg (lt_of_not_ge ha)] using hFlipA a' b' c hTranslated
  have hPositiveQuadrant : Γ |a'| |b'| c := by
    by_cases hb : 0 ≤ b'
    · simpa only [abs_of_nonneg hb] using hFirst
    · simpa only [abs_of_neg (lt_of_not_ge hb)] using hFlipB |a'| b' c hFirst
  have hTrace : c ≤ -radius |a'| |b'| := by
    by_contra hAbove
    obtain ⟨u, v, hu, hv, hSum, hDifference⟩ :=
      FundamentalDiamond.exists_positive_edge_difference |a'| |b'| c
        (abs_nonneg _) (abs_nonneg _) hDiamond (lt_of_not_ge hAbove)
    exact hEdgeExclusion u v hu hv hSum |a'| |b'| c hPositiveQuadrant hDifference
  have hRadius : radius (-a') (-b') = radius |a'| |b'| := by
    simp only [radius, neg_sq, sq_abs]
  have hBelow : (matrix (-a') (-b') (-c)).PosSemidef := by
    apply posSemidef_of_radius_le
    rw [hRadius]
    linarith only [hTrace]
  refine ⟨s, t, ?_⟩
  rw [matrix_sub]
  have hA : (s : ℝ) - (t : ℝ) - a = -a' := by dsimp [a']; ring
  have hB : (s : ℝ) + (t : ℝ) - b = -b' := by dsimp [b']; ring
  rw [hA, hB, zero_sub]
  exact hBelow

end FLattice.Auxiliary.ConeClassificationGeometry
