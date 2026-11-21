import FLatticePaper.Tiles.EdgeClause
import FLatticePaper.Tiles.RowConvexCrossing

/-! The two global inputs of `lemma:almost_square_tiling` from a window on two numerators.

Let `D = det(v₁, v₂)` and let `N₁(z) = det(z, v₂)`, `N₂(z) = det(v₁, z)`. A lattice vector `k v₁ + k' v₂` has
`N₁ = k D` and `N₂ = k' D`. If the values of `N₁` and `N₂` on the cells of `T` each lie in an interval of length less
than `D`, then:

* `P` (packing): two cells of `T` whose difference is a lattice vector are equal, so `NoFirstCrossing` holds;
* `A` (gap): a cell `c + e` adjacent to `T` across a boundary edge, with `c + e - u ∈ T` for a lattice vector `u`,
  has `u = k v₁ + k' v₂` with `|k|, |k'| ≤ 1`, and `u ≠ 0`; so it lies in a surround translate.

Both follow from the bounds below, which are the only inputs about the tile. -/

namespace FLatticePaper.Tiles

/-- The determinant of the period pair `(v₁, v₂)`. -/
def gradeDet (v₁ v₂ : GInt) : ℤ := v₁.1 * v₂.2 - v₁.2 * v₂.1

/-- The first numerator `N₁(z) = det(z, v₂)`. -/
def gradeNumOne (v₂ z : GInt) : ℤ := z.1 * v₂.2 - z.2 * v₂.1

/-- The second numerator `N₂(z) = det(v₁, z)`. -/
def gradeNumTwo (v₁ z : GInt) : ℤ := v₁.1 * z.2 - v₁.2 * z.1

theorem gradeNumOne_lattice (v₁ v₂ : GInt) (k k' : ℤ) :
    gradeNumOne v₂ (k * v₁.1 + k' * v₂.1, k * v₁.2 + k' * v₂.2) = k * gradeDet v₁ v₂ := by
  unfold gradeNumOne gradeDet
  ring

theorem gradeNumTwo_lattice (v₁ v₂ : GInt) (k k' : ℤ) :
    gradeNumTwo v₁ (k * v₁.1 + k' * v₂.1, k * v₁.2 + k' * v₂.2) = k' * gradeDet v₁ v₂ := by
  unfold gradeNumTwo gradeDet
  ring

theorem gradeNumOne_sub (v₂ x y : GInt) :
    gradeNumOne v₂ (x - y) = gradeNumOne v₂ x - gradeNumOne v₂ y := by
  unfold gradeNumOne
  simp only [Prod.fst_sub, Prod.snd_sub]
  ring

theorem gradeNumTwo_sub (v₁ x y : GInt) :
    gradeNumTwo v₁ (x - y) = gradeNumTwo v₁ x - gradeNumTwo v₁ y := by
  unfold gradeNumTwo
  simp only [Prod.fst_sub, Prod.snd_sub]
  ring

/-- A coefficient `k` with `|k D| < D` vanishes. -/
theorem coeff_zero_of_window {D k : ℤ} (hD : 0 < D) (h1 : -D < k * D) (h2 : k * D < D) : k = 0 := by
  rcases lt_trichotomy k 0 with h | h | h
  · have hk : k ≤ -1 := by omega
    nlinarith
  · exact h
  · have hk : 1 ≤ k := by omega
    nlinarith

/-- A coefficient `k` with `k D - n` in `(-D, D)`, where `n ∈ (-D, D)`, lies in `[-1, 1]`. -/
theorem coeff_bounded_of_window {D k n : ℤ} (hD : 0 < D) (hn1 : -D < n) (hn2 : n < D)
    (h1 : -D < k * D - n) (h2 : k * D - n < D) : -1 ≤ k ∧ k ≤ 1 := by
  constructor
  · by_contra h
    have hk : k ≤ -2 := by omega
    nlinarith
  · by_contra h
    have hk : 2 ≤ k := by omega
    nlinarith

/-- Packing from the windows: no two cells of `T` differ by a nonzero lattice vector. -/
theorem packing_of_window (T : CellTile) (v₁ v₂ : GInt) {lo₁ hi₁ lo₂ hi₂ : ℤ}
    (hD : 0 < gradeDet v₁ v₂) (hw₁ : hi₁ - lo₁ < gradeDet v₁ v₂) (hw₂ : hi₂ - lo₂ < gradeDet v₁ v₂)
    (h₁ : ∀ x ∈ T, lo₁ ≤ gradeNumOne v₂ x ∧ gradeNumOne v₂ x ≤ hi₁)
    (h₂ : ∀ x ∈ T, lo₂ ≤ gradeNumTwo v₁ x ∧ gradeNumTwo v₁ x ≤ hi₂) :
    ∀ x ∈ T, ∀ y ∈ T, x - y ∈ latticeOf v₁ v₂ → x = y := by
  intro x hx y hy hxy
  obtain ⟨k, k', hk⟩ := hxy
  have e1 := gradeNumOne_sub v₂ x y
  have e2 := gradeNumTwo_sub v₁ x y
  rw [hk, gradeNumOne_lattice] at e1
  rw [hk, gradeNumTwo_lattice] at e2
  obtain ⟨a1, a2⟩ := h₁ x hx
  obtain ⟨b1, b2⟩ := h₁ y hy
  obtain ⟨c1, c2⟩ := h₂ x hx
  obtain ⟨d1, d2⟩ := h₂ y hy
  have hk0 : k = 0 := coeff_zero_of_window hD (by linarith) (by linarith)
  have hk0' : k' = 0 := coeff_zero_of_window hD (by linarith) (by linarith)
  have hz : x - y = 0 := by
    rw [hk, hk0, hk0']
    simp
  exact sub_eq_zero.mp hz

/-- `NoFirstCrossing` from the windows, through the packing reduction. -/
theorem noFirstCrossing_of_window (T : CellTile) (v₁ v₂ : GInt) {lo₁ hi₁ lo₂ hi₂ : ℤ}
    (hD : 0 < gradeDet v₁ v₂) (hw₁ : hi₁ - lo₁ < gradeDet v₁ v₂) (hw₂ : hi₂ - lo₂ < gradeDet v₁ v₂)
    (h₁ : ∀ x ∈ T, lo₁ ≤ gradeNumOne v₂ x ∧ gradeNumOne v₂ x ≤ hi₁)
    (h₂ : ∀ x ∈ T, lo₂ ≤ gradeNumTwo v₁ x ∧ gradeNumTwo v₁ x ≤ hi₂) :
    NoFirstCrossing T v₁ v₂ :=
  noFirstCrossing_of_packing (packing_of_window T v₁ v₂ hD hw₁ hw₂ h₁ h₂)

/-- `NoFarAdjacency` from the windows on `T` and the bounds of the numerators on the four unit steps. -/
theorem noFarAdjacency_of_window (T : CellTile) (v₁ v₂ : GInt) {lo₁ hi₁ lo₂ hi₂ : ℤ}
    (hD : 0 < gradeDet v₁ v₂) (hw₁ : hi₁ - lo₁ < gradeDet v₁ v₂) (hw₂ : hi₂ - lo₂ < gradeDet v₁ v₂)
    (h₁ : ∀ x ∈ T, lo₁ ≤ gradeNumOne v₂ x ∧ gradeNumOne v₂ x ≤ hi₁)
    (h₂ : ∀ x ∈ T, lo₂ ≤ gradeNumTwo v₁ x ∧ gradeNumTwo v₁ x ≤ hi₂)
    (e₁ : ∀ e ∈ [((1 : ℤ), (0 : ℤ)), (0, 1), (-1, 0), (0, -1)],
      -gradeDet v₁ v₂ < gradeNumOne v₂ e ∧ gradeNumOne v₂ e < gradeDet v₁ v₂)
    (e₂ : ∀ e ∈ [((1 : ℤ), (0 : ℤ)), (0, 1), (-1, 0), (0, -1)],
      -gradeDet v₁ v₂ < gradeNumTwo v₁ e ∧ gradeNumTwo v₁ e < gradeDet v₁ v₂) :
    NoFarAdjacency T v₁ v₂ := by
  refine ⟨fun d hd hdT => ?_⟩
  obtain ⟨c, hc, e, he, rfl⟩ := hd
  by_cases hex : ∃ u ∈ latticeOf v₁ v₂, c + e - u ∈ T
  · left
    obtain ⟨u, hu, ht⟩ := hex
    obtain ⟨k, k', hk⟩ := hu
    have hcu : c - (c + e - u) = u - e := by abel
    have hN1 := gradeNumOne_sub v₂ c (c + e - u)
    have hN2 := gradeNumTwo_sub v₁ c (c + e - u)
    have hue1 : gradeNumOne v₂ (u - e) = k * gradeDet v₁ v₂ - gradeNumOne v₂ e := by
      rw [gradeNumOne_sub, hk, gradeNumOne_lattice]
    have hue2 : gradeNumTwo v₁ (u - e) = k' * gradeDet v₁ v₂ - gradeNumTwo v₁ e := by
      rw [gradeNumTwo_sub, hk, gradeNumTwo_lattice]
    rw [hcu, hue1] at hN1
    rw [hcu, hue2] at hN2
    obtain ⟨a1, a2⟩ := h₁ c hc
    obtain ⟨b1, b2⟩ := h₁ (c + e - u) ht
    obtain ⟨c1, c2⟩ := h₂ c hc
    obtain ⟨d1, d2⟩ := h₂ (c + e - u) ht
    obtain ⟨f1, f2⟩ := e₁ e he
    obtain ⟨g1, g2⟩ := e₂ e he
    obtain ⟨hk1, hk2⟩ := coeff_bounded_of_window (k := k) hD f1 f2 (by linarith) (by linarith)
    obtain ⟨hk1', hk2'⟩ := coeff_bounded_of_window (k := k') hD g1 g2 (by linarith) (by linarith)
    have hne : (k, k') ≠ (0, 0) := by
      intro h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hu0 : u = 0 := by
        rw [hk]
        simp
      rw [hu0, sub_zero] at ht
      exact absurd ht hdT
    exact ⟨u, ⟨k, k', hk1, hk2, hk1', hk2', hne, hk⟩, ht⟩
  · right
    intro u hu hT
    exact hex ⟨u, hu, hT⟩

end FLatticePaper.Tiles
