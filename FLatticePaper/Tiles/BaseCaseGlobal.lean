import FLatticePaper.Tiles.BaseCaseAlmostTiling
import FLatticePaper.Tiles.GradeWindow

/-! The two global inputs `NoFirstCrossing` and `NoFarAdjacency` of the base tiles, for every `k`.

The windows of the numerators `N₁ = det(z, v₂)` and `N₂ = det(v₁, z)` on the cell sets are explicit in the parameter
`d`, so the packing `P` and the gap `A` of `GradeWindow.lean` follow for all `d` with a computation on the inequalities
that define the cells. This removes the hypotheses of `stair_almost_tiling`, `ladder_almost_tiling` and their
`paper` forms. -/

namespace FLatticePaper.Tiles

/-! ### The reciprocal staircase, `d = 2k + 3`: `v₁ = (d, 1)`, `v₂ = (1 - d, 1 + d)`, determinant `d² + 2d - 1` -/

/-- On `stairCells d`: `N₁ = (d+1)a + (d-1)b` lies in `[3-d, d²+d-2]` and `N₂ = db - a` in `[1-d, d²+d-2]`. -/
theorem stair_window (d : ℤ) (hd : 3 ≤ d) (x : GInt) (hx : x ∈ stairCells d) :
    (3 - d ≤ gradeNumOne (1 - d, 1 + d) x ∧ gradeNumOne (1 - d, 1 + d) x ≤ d * d + d - 2) ∧
      (1 - d ≤ gradeNumTwo (d, 1) x ∧ gradeNumTwo (d, 1) x ≤ d * d + d - 2) := by
  obtain ⟨a, b⟩ := x
  have hx' : stairInT d a b := (mem_stairCells d hd (a, b)).1 hx
  unfold stairInT at hx'
  simp only [gradeNumOne, gradeNumTwo]
  rcases hx' with ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · nlinarith [mul_nonneg (show (0 : ℤ) ≤ d - 1 by omega) (show (0 : ℤ) ≤ a + b - 1 by omega)]
    · nlinarith [mul_nonneg (show (0 : ℤ) ≤ d - 1 by omega) (show (0 : ℤ) ≤ d - (a + b) by omega)]
    · nlinarith [mul_nonneg (show (0 : ℤ) ≤ d by omega) (show (0 : ℤ) ≤ b by omega)]
    · nlinarith [mul_nonneg (show (0 : ℤ) ≤ d by omega) (show (0 : ℤ) ≤ d - b by omega)]
  · constructor <;> constructor <;> nlinarith
  · constructor <;> constructor <;> nlinarith

/-- The four unit steps: the numerators of `e ∈ {±(1,0), ±(0,1)}` are below the determinant in absolute value. -/
theorem stair_units (d : ℤ) (hd : 3 ≤ d) :
    (∀ e ∈ [((1 : ℤ), (0 : ℤ)), (0, 1), (-1, 0), (0, -1)],
      -gradeDet (d, 1) (1 - d, 1 + d) < gradeNumOne (1 - d, 1 + d) e ∧
        gradeNumOne (1 - d, 1 + d) e < gradeDet (d, 1) (1 - d, 1 + d)) ∧
    (∀ e ∈ [((1 : ℤ), (0 : ℤ)), (0, 1), (-1, 0), (0, -1)],
      -gradeDet (d, 1) (1 - d, 1 + d) < gradeNumTwo (d, 1) e ∧
        gradeNumTwo (d, 1) e < gradeDet (d, 1) (1 - d, 1 + d)) := by
  have hD : gradeDet (d, 1) (1 - d, 1 + d) = d * d + 2 * d - 1 := by
    unfold gradeDet
    ring
  rw [hD]
  constructor
  · intro e he
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> simp only [gradeNumOne] <;> constructor <;> nlinarith
  · intro e he
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> simp only [gradeNumTwo] <;> constructor <;> nlinarith

/-- The global inputs of the reciprocal staircase tile with parameter `d`. -/
theorem stair_global_of (d : ℤ) (hd : 3 ≤ d) :
    NoFirstCrossing (stairCells d) (d, 1) (1 - d, 1 + d) ∧
      NoFarAdjacency (stairCells d) (d, 1) (1 - d, 1 + d) := by
  have hD : gradeDet (d, 1) (1 - d, 1 + d) = d * d + 2 * d - 1 := by
    unfold gradeDet
    ring
  have hDpos : 0 < gradeDet (d, 1) (1 - d, 1 + d) := by
    rw [hD]
    nlinarith
  have hw1 : (d * d + d - 2) - (3 - d) < gradeDet (d, 1) (1 - d, 1 + d) := by
    rw [hD]
    linarith
  have hw2 : (d * d + d - 2) - (1 - d) < gradeDet (d, 1) (1 - d, 1 + d) := by
    rw [hD]
    linarith
  have h₁ : ∀ x ∈ stairCells d,
      3 - d ≤ gradeNumOne (1 - d, 1 + d) x ∧ gradeNumOne (1 - d, 1 + d) x ≤ d * d + d - 2 :=
    fun x hx => (stair_window d hd x hx).1
  have h₂ : ∀ x ∈ stairCells d,
      1 - d ≤ gradeNumTwo (d, 1) x ∧ gradeNumTwo (d, 1) x ≤ d * d + d - 2 :=
    fun x hx => (stair_window d hd x hx).2
  exact ⟨noFirstCrossing_of_window (stairCells d) (d, 1) (1 - d, 1 + d) hDpos hw1 hw2 h₁ h₂,
    noFarAdjacency_of_window (stairCells d) (d, 1) (1 - d, 1 + d) hDpos hw1 hw2 h₁ h₂
      (stair_units d hd).1 (stair_units d hd).2⟩

/-! ### The doubled staircase, `d = 2m + 4`: `v₁ = (2d, 2)`, `v₂ = (1 - d, 1 + d)`, determinant `2d² + 4d - 2` -/

/-- On `ladderCells d`: `N₁ = (d+1)a + (d-1)b` lies in `[3-d, 2d²+3d-3]`, and `N₂ = 2(db - a)` in
`[2(1-d), 2(d²+d-2)]`. -/
theorem ladder_window (d : ℤ) (hd : 4 ≤ d) (x : GInt) (hx : x ∈ ladderCells d) :
    (3 - d ≤ gradeNumOne (1 - d, 1 + d) x ∧ gradeNumOne (1 - d, 1 + d) x ≤ 2 * d * d + 3 * d - 3) ∧
      (2 * (1 - d) ≤ gradeNumTwo (2 * d, 2 * 1) x ∧ gradeNumTwo (2 * d, 2 * 1) x ≤ 2 * (d * d + d - 2)) := by
  obtain ⟨a, b⟩ := x
  have hx' : ladderInT d a b := (mem_ladderCells d hd (a, b)).1 hx
  unfold ladderInT at hx'
  simp only [gradeNumOne, gradeNumTwo]
  rcases hx' with ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7, h8⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · nlinarith [mul_nonneg (show (0 : ℤ) ≤ d - 1 by omega) (show (0 : ℤ) ≤ a + b - 1 by omega)]
    · nlinarith [mul_nonneg (show (0 : ℤ) ≤ d - 1 by omega) (show (0 : ℤ) ≤ 2 * d + 1 - (a + b) by omega)]
    · by_cases hb0 : b = 0
      · have ha : a ≤ d - 2 := by
          rcases h7 with h | h
          · exact absurd hb0 h
          · exact h
        subst hb0
        nlinarith
      · nlinarith [mul_nonneg (show (0 : ℤ) ≤ d by omega) (show (0 : ℤ) ≤ b - 1 by omega)]
    · by_cases hb : b = d + 1
      · have ha : 3 ≤ a := by
          rcases h8 with h | h
          · exact absurd hb h
          · exact h
        subst hb
        nlinarith
      · nlinarith [mul_nonneg (show (0 : ℤ) ≤ d by omega) (show (0 : ℤ) ≤ d - b by omega)]
  · constructor <;> constructor <;> nlinarith
  · constructor <;> constructor <;> nlinarith

/-- The four unit steps of the doubled staircase. -/
theorem ladder_units (d : ℤ) (hd : 4 ≤ d) :
    (∀ e ∈ [((1 : ℤ), (0 : ℤ)), (0, 1), (-1, 0), (0, -1)],
      -gradeDet (2 * d, 2 * 1) (1 - d, 1 + d) < gradeNumOne (1 - d, 1 + d) e ∧
        gradeNumOne (1 - d, 1 + d) e < gradeDet (2 * d, 2 * 1) (1 - d, 1 + d)) ∧
    (∀ e ∈ [((1 : ℤ), (0 : ℤ)), (0, 1), (-1, 0), (0, -1)],
      -gradeDet (2 * d, 2 * 1) (1 - d, 1 + d) < gradeNumTwo (2 * d, 2 * 1) e ∧
        gradeNumTwo (2 * d, 2 * 1) e < gradeDet (2 * d, 2 * 1) (1 - d, 1 + d)) := by
  have hD : gradeDet (2 * d, 2 * 1) (1 - d, 1 + d) = 2 * d * d + 4 * d - 2 := by
    unfold gradeDet
    ring
  rw [hD]
  constructor
  · intro e he
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> simp only [gradeNumOne] <;> constructor <;> nlinarith
  · intro e he
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> simp only [gradeNumTwo] <;> constructor <;> nlinarith

/-- The global inputs of the doubled staircase tile with parameter `d`. -/
theorem ladder_global_of (d : ℤ) (hd : 4 ≤ d) :
    NoFirstCrossing (ladderCells d) (2 * d, 2 * 1) (1 - d, 1 + d) ∧
      NoFarAdjacency (ladderCells d) (2 * d, 2 * 1) (1 - d, 1 + d) := by
  have hD : gradeDet (2 * d, 2 * 1) (1 - d, 1 + d) = 2 * d * d + 4 * d - 2 := by
    unfold gradeDet
    ring
  have hDpos : 0 < gradeDet (2 * d, 2 * 1) (1 - d, 1 + d) := by
    rw [hD]
    nlinarith
  have hw1 : (2 * d * d + 3 * d - 3) - (3 - d) < gradeDet (2 * d, 2 * 1) (1 - d, 1 + d) := by
    rw [hD]
    linarith
  have hw2 : 2 * (d * d + d - 2) - 2 * (1 - d) < gradeDet (2 * d, 2 * 1) (1 - d, 1 + d) := by
    rw [hD]
    linarith
  have h₁ : ∀ x ∈ ladderCells d,
      3 - d ≤ gradeNumOne (1 - d, 1 + d) x ∧ gradeNumOne (1 - d, 1 + d) x ≤ 2 * d * d + 3 * d - 3 :=
    fun x hx => (ladder_window d hd x hx).1
  have h₂ : ∀ x ∈ ladderCells d,
      2 * (1 - d) ≤ gradeNumTwo (2 * d, 2 * 1) x ∧ gradeNumTwo (2 * d, 2 * 1) x ≤ 2 * (d * d + d - 2) :=
    fun x hx => (ladder_window d hd x hx).2
  exact ⟨noFirstCrossing_of_window (ladderCells d) (2 * d, 2 * 1) (1 - d, 1 + d) hDpos hw1 hw2 h₁ h₂,
    noFarAdjacency_of_window (ladderCells d) (2 * d, 2 * 1) (1 - d, 1 + d) hDpos hw1 hw2 h₁ h₂
      (ladder_units d hd).1 (ladder_units d hd).2⟩

/-! ### The global inputs for every `k` and `m`, and the base-case theorems without them -/

/-- The global inputs of the reciprocal staircase `d = 2k + 3`, for every `k`. -/
theorem stair_global (k : ℕ) :
    NoFirstCrossing (stairCells (2 * (k : ℤ) + 3)) (almostV₁ (gH (stairH k))) (almostV₂ (gV (stairV k))) ∧
      NoFarAdjacency (stairCells (2 * (k : ℤ) + 3)) (almostV₁ (gH (stairH k))) (almostV₂ (gV (stairV k))) := by
  rw [almostV1_stair, almostV2_stair]
  exact stair_global_of _ (by omega)

/-- The global inputs of the doubled staircase `d = 2m + 4`, for every `m`. -/
theorem ladder_global (m : ℕ) :
    NoFirstCrossing (ladderCells (2 * (m : ℤ) + 4))
      (almostV₁ (gH (ladderH (m + 1)))) (almostV₂ (gV (ladderV (m + 1)))) ∧
      NoFarAdjacency (ladderCells (2 * (m : ℤ) + 4))
        (almostV₁ (gH (ladderH (m + 1)))) (almostV₂ (gV (ladderV (m + 1)))) := by
  rw [almostV1_ladder, almostV2_ladder]
  exact ladder_global_of _ (by omega)

/-- `prop:base_cases` (a) for the reciprocal staircase `d = 2k + 3`, for every `k`, with no global hypothesis. -/
theorem stair_almost_tiling_all (k : ℕ) :
    IsRegularAlmostTiling (stairCells (2 * (k : ℤ) + 3)) (almostV₁ (gH (stairH k)))
        (almostV₂ (gV (stairV k))) ∧
      EdgeSharingClause (stairCells (2 * (k : ℤ) + 3)) (almostV₁ (gH (stairH k)))
        (almostV₂ (gV (stairV k))) :=
  stair_almost_tiling k (stair_global k).1 (stair_global k).2

/-- The same, with the lattice written as the paper's `L'(1/d)`, for every `k`. -/
theorem stair_almost_tiling_paper_all (k : ℕ) :
    IsAlmostTiling (stairCells (2 * (k : ℤ) + 3)) (paperLattice 1 (2 * (k : ℤ) + 3)) :=
  stair_almost_tiling_paper k (stair_global k).1 (stair_global k).2

/-- `prop:base_cases` (a) for the doubled staircase `d = 2m + 4`, for every `m`, with no global hypothesis. -/
theorem ladder_almost_tiling_all (m : ℕ) :
    IsRegularAlmostTiling (ladderCells (2 * (m : ℤ) + 4))
        (almostV₁ (gH (ladderH (m + 1)))) (almostV₂ (gV (ladderV (m + 1)))) ∧
      EdgeSharingClause (ladderCells (2 * (m : ℤ) + 4))
        (almostV₁ (gH (ladderH (m + 1)))) (almostV₂ (gV (ladderV (m + 1)))) :=
  ladder_almost_tiling m (ladder_global m).1 (ladder_global m).2

/-- The same, with the lattice written as the paper's `L'(1/d)`, for every `m`. -/
theorem ladder_almost_tiling_paper_all (m : ℕ) :
    IsAlmostTiling (ladderCells (2 * (m : ℤ) + 4)) (paperLattice 1 (2 * (m : ℤ) + 4)) :=
  ladder_almost_tiling_paper m (ladder_global m).1 (ladder_global m).2

end FLatticePaper.Tiles
