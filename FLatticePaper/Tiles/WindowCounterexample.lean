import FLatticePaper.Tiles.BaseCaseDecided
import FLatticePaper.Tiles.GradeWindow

/-! A strict counterexample to the window bound of `packing_of_window`, for an admissible simple tile of
`lemma:almost_square_tiling`.

The tile `T0` has boundary words `w1 = 1 i 1` and `w2 = i i (-1)^4 i i`, so `v1 = almostV₁ w1 = (2, 2)`,
`v2 = almostV₂ w2 = (-5, 4)` and the determinant is `18`. The first Cramer numerator `N₁(z) = det(z, v2)` takes the
values `14` at `(1,2)` and `-6` at `(-4,2)`, so its spread is `20 > 18`: the window argument of `GradeWindow.lean`
does not apply to this tile. Packing still holds (checked by divisibility), and so do the two global inputs, which
are checked by the decidable lemmas of `BaseCaseDecided.lean`. The tile was found by a scan of the simple admissible
pairs with `|w1|, |w2| <= 12`. -/

namespace FLatticePaper.Tiles

instance (x y : GInt) : Decidable (CellAdj x y) := by
  unfold CellAdj
  infer_instance

/-- The cells of the counterexample tile, as lower-left corners. -/
def T0 : CellTile :=
  {(-4, 2), (-4, 3), (-3, 2), (-3, 3), (-3, 4), (-2, 2), (-1, 2), (0, 0), (0, 1), (0, 2), (1, 1), (1, 2)}

/-- The first boundary word `1 i 1`. -/
def w1₀ : F2Word := [.one, .i, .one]

/-- The second boundary word `i i (-1) (-1) (-1) (-1) i i`. -/
def w2₀ : F2Word := [.i, .i, .negOne, .negOne, .negOne, .negOne, .i, .i]

theorem w1₀_admissible : Admissible w1₀ :=
  ⟨by unfold Monotone w1₀; decide, by decide, by decide, Or.inl (by decide)⟩

theorem w2₀_admissible : Admissible (w2₀.map Unit4.mulNegI) :=
  ⟨by unfold Monotone; decide, by decide, by decide, Or.inl (by decide)⟩

theorem T0_lowerLeft : IsLowerLeft T0 (0, 0) := by
  unfold IsLowerLeft CellTile.vertices
  decide +kernel

theorem T0_boundary : IsBoundaryWordAt T0 (0, 0) (boundaryWordOf w1₀ w2₀) :=
  ⟨T0_lowerLeft, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The adjacency relation of `EdgeConnected T0`. -/
abbrev R0 : GInt → GInt → Prop := fun a b => a ∈ T0 ∧ b ∈ T0 ∧ CellAdj a b

theorem rtg0 {x y z : GInt} (h : Relation.ReflTransGen R0 x y) (hy : y ∈ T0) (hz : z ∈ T0)
    (hyz : CellAdj y z) : Relation.ReflTransGen R0 x z :=
  h.tail ⟨hy, hz, hyz⟩

/-- Every cell of `T0` is reached from the lower-left cell `(0, 0)` along an explicit chain of adjacent cells. -/
theorem T0_reach : ∀ x ∈ T0, Relation.ReflTransGen R0 (0, 0) x := by
  intro x hx
  have r0 : Relation.ReflTransGen R0 (0, 0) (0, 0) := Relation.ReflTransGen.refl
  have r1 : Relation.ReflTransGen R0 (0, 0) (0, 1) :=
    rtg0 r0 (by decide) (by decide) (by decide)
  have r2 : Relation.ReflTransGen R0 (0, 0) (1, 1) :=
    rtg0 r1 (by decide) (by decide) (by decide)
  have r3 : Relation.ReflTransGen R0 (0, 0) (0, 2) :=
    rtg0 r1 (by decide) (by decide) (by decide)
  have r4 : Relation.ReflTransGen R0 (0, 0) (1, 2) :=
    rtg0 r2 (by decide) (by decide) (by decide)
  have r5 : Relation.ReflTransGen R0 (0, 0) (-1, 2) :=
    rtg0 r3 (by decide) (by decide) (by decide)
  have r6 : Relation.ReflTransGen R0 (0, 0) (-2, 2) :=
    rtg0 r5 (by decide) (by decide) (by decide)
  have r7 : Relation.ReflTransGen R0 (0, 0) (-3, 2) :=
    rtg0 r6 (by decide) (by decide) (by decide)
  have r8 : Relation.ReflTransGen R0 (0, 0) (-4, 2) :=
    rtg0 r7 (by decide) (by decide) (by decide)
  have r9 : Relation.ReflTransGen R0 (0, 0) (-3, 3) :=
    rtg0 r7 (by decide) (by decide) (by decide)
  have r10 : Relation.ReflTransGen R0 (0, 0) (-4, 3) :=
    rtg0 r8 (by decide) (by decide) (by decide)
  have r11 : Relation.ReflTransGen R0 (0, 0) (-3, 4) :=
    rtg0 r9 (by decide) (by decide) (by decide)
  simp only [T0, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact r8
  · exact r10
  · exact r7
  · exact r9
  · exact r11
  · exact r6
  · exact r5
  · exact r0
  · exact r1
  · exact r3
  · exact r2
  · exact r4

/-- The relation `R0` is symmetric, so its reflexive-transitive closure reverses. -/
theorem rtg0_symm {x y : GInt} (h : Relation.ReflTransGen R0 x y) : Relation.ReflTransGen R0 y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head ⟨hbc.2.1, hbc.1, cellAdj_symm hbc.2.2⟩ ih

theorem T0_edgeConnected : EdgeConnected T0 := by
  intro x hx y hy
  exact (rtg0_symm (T0_reach x hx)).trans (T0_reach y hy)

theorem T0_simple : IsSimpleTile T0 :=
  ⟨⟨(0, 0), boundaryWordOf w1₀ w2₀, T0_boundary, by decide +kernel⟩, T0_edgeConnected⟩

theorem T0_det : gradeDet (2, 2) (-5, 4) = 18 := by
  decide

theorem T0_v1 : almostV₁ w1₀ = (2, 2) := by
  decide

theorem T0_v2 : almostV₂ w2₀ = (-5, 4) := by
  decide

/-- The window bound fails on `T0`: the spread of `N₁` is `20 > 18`. -/
theorem T0_window_fails :
    ¬ (∀ x ∈ T0, ∀ y ∈ T0, |gradeNumOne (-5, 4) x - gradeNumOne (-5, 4) y| < gradeDet (2, 2) (-5, 4)) := by
  intro h
  have := h (1, 2) (by decide) (-4, 2) (by decide)
  simp only [gradeNumOne, gradeDet] at this
  norm_num at this

/-- Packing holds on `T0`: two cells differing by a lattice vector are equal. -/
theorem T0_packing : ∀ x ∈ T0, ∀ y ∈ T0, x - y ∈ latticeOf (2, 2) (-5, 4) → x = y := by
  have hdec : ∀ x ∈ T0, ∀ y ∈ T0,
      (18 ∣ gradeNumOne (-5, 4) (x - y)) → (18 ∣ gradeNumTwo (2, 2) (x - y)) → x = y := by
    decide +kernel
  intro x hx y hy hxy
  obtain ⟨k, k', hk⟩ := hxy
  have h1 : gradeNumOne (-5, 4) (x - y) = k * 18 := by
    rw [hk, gradeNumOne_lattice, T0_det]
  have h2 : gradeNumTwo (2, 2) (x - y) = k' * 18 := by
    rw [hk, gradeNumTwo_lattice, T0_det]
  exact hdec x hx y hy ⟨k, by rw [h1]; ring⟩ ⟨k', by rw [h2]; ring⟩

/-- The two global inputs of `almost_square_tiling` hold for `T0`. -/
theorem T0_global : NoFirstCrossing T0 (2, 2) (-5, 4) ∧ NoFarAdjacency T0 (2, 2) (-5, 4) :=
  ⟨noFirstCrossing_of_decide _ _ _ (by decide +kernel), noFarAdjacency_of_decide _ _ _ (by decide +kernel)⟩

/-- `almost_square_tiling` applies to `T0`: the tiling conclusion holds for this tile, whose window bound fails. -/
theorem T0_almost_tiling :
    IsRegularAlmostTiling T0 (2, 2) (-5, 4) ∧ EdgeSharingClause T0 (2, 2) (-5, 4) := by
  have hF : NoFirstCrossing T0 (almostV₁ w1₀) (almostV₂ w2₀) := by
    rw [T0_v1, T0_v2]
    exact T0_global.1
  have hG : NoFarAdjacency T0 (almostV₁ w1₀) (almostV₂ w2₀) := by
    rw [T0_v1, T0_v2]
    exact T0_global.2
  have h := almost_square_tiling T0_simple T0_boundary w1₀_admissible w2₀_admissible hF hG
  rw [T0_v1, T0_v2] at h
  exact h

end FLatticePaper.Tiles
