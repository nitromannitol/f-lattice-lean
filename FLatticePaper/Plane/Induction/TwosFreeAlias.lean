import FLatticePaper.Plane.Induction.TwosFlatClass

/-! Twos flatness, the free alias: a tile point has at most one free alias, and the only non-native free site is `(-1, a)`,
which is the `U`-translate of the tile point `(a, 2a-1)`. This fixes the selection of a free centre (`TwosSel`). -/

noncomputable section

namespace FLatticePaper.TwosEPolicy

/-- An alias translate has the same class key. -/
theorem alias_classKey {a : ℤ} {c u : ℤ × ℤ} (h : AliasOf a c u) : classKey a u = classKey a c := by
  obtain ⟨i, l, hi⟩ := h
  unfold classKey
  rw [hi]
  dsimp only
  have e : (a - 1) * (c.1 - i * (a + 1) + 2 * l) - (a + 1) * (c.2 - i * (a - 1) - 2 * a * l) =
      ((a - 1) * c.1 - (a + 1) * c.2) + (2 * a * a + 4 * a - 2) * l := by ring
  rw [e, Int.add_mul_emod_self_left]

/-- Every site is an alias of itself. -/
theorem alias_self {a : ℤ} (c : ℤ × ℤ) : AliasOf a c c := ⟨0, 0, by simp⟩

/-- The only non-native free site is `(-1, a)`. -/
theorem free_nonnative_eq {a x y : ℤ} (ha : 4 ≤ a) (hF : FreeSite a x y) (hN : ¬ NativeT a x y) :
    x = -1 ∧ y = a := by
  unfold FreeSite FreeHSite FreeVSite at hF
  unfold NativeT at hN
  omega

/-- `(a, 2a-1)` is a tile point: its `U`-duplicate `(-1, a)` is free but not native. -/
theorem tile_a_2a1 {a : ℤ} (ha : 4 ≤ a) : TwosTile a (a, 2 * a - 1) := by
  apply tile_of_nodup
  · unfold NativeT
    omega
  · intro h
    have h1 := h.2
    unfold NativeT at h1
    omega
  · intro h
    have h1 := h.1
    unfold FreeSite FreeHSite FreeVSite at h1
    omega

/-- **The free alias is unique.** A free alias of a tile point is the point itself. -/
theorem free_alias_unique {a : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) {p1 p2 u1 u2 : ℤ}
    (hp : TwosTile a (p1, p2)) (hpF : FreeSite a p1 p2) (hu : AliasOf a (p1, p2) (u1, u2))
    (huF : FreeSite a u1 u2) : u1 = p1 ∧ u2 = p2 := by
  by_cases hN : NativeT a u1 u2
  · have hut : TwosTile a (u1, u2) := free_tile huF hN
    have hk : classKey a (u1, u2) = classKey a (p1, p2) := alias_classKey hu
    exact tile_unique ha he2 hut hp hk
  · exfalso
    obtain ⟨hx, hy⟩ := free_nonnative_eq ha huF hN
    have hk : classKey a (u1, u2) = classKey a (p1, p2) := alias_classKey hu
    rw [hx, hy] at hk
    have hU := classKey_add_U a (-1) a
    rw [show (-1 : ℤ) + (a + 1) = a by ring, show a + (a - 1) = 2 * a - 1 by ring] at hU
    obtain ⟨h1, h2⟩ := tile_unique ha he2 hp (tile_a_2a1 ha) (by rw [← hk, hU])
    rw [h1, h2] at hpF
    unfold FreeSite FreeHSite FreeVSite at hpF
    omega

end FLatticePaper.TwosEPolicy
