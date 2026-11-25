import FLatticePaper.Plane.Induction.TwosBlackDrop

/-! Twos flatness, the reduction of a flat condition to levels at tile representatives (for every selection type).

A native site `i` is a tile point, or a duplicate `q + U` (resp. `q + V`) of a free native site `q` (`native_cases`). For a
flat neighbour `i` of a tile point `p` (`Φ i = Φ p`), the potential gives the level relation of the representative: the tile
case `lev i = lev p`, the `U`-duplicate `lev q = lev p + 1`, the `V`-duplicate `lev q = lev p - 2`. The rank of `i` is the
rank of its representative (`rhoTwos_add_U`, `rhoTwos_add_V`). -/

noncomputable section

namespace FLatticePaper.TwosEPolicy

open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey
open scoped Classical

/-- A free native site is a tile point. -/
theorem free_tile {a x y : ℤ} (hF : FreeSite a x y) (hN : NativeT a x y) : TwosTile a (x, y) := by
  rw [tile_iff_lin]
  exact ⟨hN, fun h => h.2 hF⟩

/-- A native site is a tile point, or a duplicate of one of the two free-copy shifts. -/
theorem native_cases {a x y : ℤ} (hN : NativeT a x y) :
    TwosTile a (x, y) ∨
      (FreeSite a (x - (a + 1)) (y - (a - 1)) ∧ NativeT a (x - (a + 1)) (y - (a - 1))) ∨
      (FreeSite a (x + 2) (y - 2 * a) ∧ NativeT a (x + 2) (y - 2 * a)) := by
  by_cases h1 : (FreeSite a (x - (a + 1)) (y - (a - 1)) ∧ NativeT a (x - (a + 1)) (y - (a - 1)))
  · exact Or.inr (Or.inl h1)
  by_cases h2 : (FreeSite a (x + 2) (y - 2 * a) ∧ NativeT a (x + 2) (y - 2 * a))
  · exact Or.inr (Or.inr h2)
  exact Or.inl (tile_of_nodup hN h1 h2)

/-- The potential at the `U`-translate: `Φ(i) = Φ(i - U) - 1`. -/
theorem phi_dupU' {a : ℤ} {k : ℕ} (hk : a = 2 * (k : ℤ) + 4) (i1 i2 : ℤ) :
    twosPhi k 1 (i1, i2) = twosPhi k 1 (i1 - (a + 1), i2 - (a - 1)) - 1 := by
  subst hk
  have h := twosPhi_kernel_plus k (i1 - (2 * (k : ℤ) + 4 + 1), i2 - (2 * (k : ℤ) + 4 - 1))
  have e : ((i1 - (2 * (k : ℤ) + 4 + 1), i2 - (2 * (k : ℤ) + 4 - 1)) + (2 * (k : ℤ) + 5, 2 * (k : ℤ) + 3) :
      ℤ × ℤ) = (i1, i2) := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
  rw [e] at h
  linarith

/-- The potential at the `V`-translate: `Φ(i) = Φ(i + (-2, -2a)) + 2`, since `i = (i + (-2,-2a)) + V`. -/
theorem phi_dupV' {a : ℤ} {k : ℕ} (hk : a = 2 * (k : ℤ) + 4) (i1 i2 : ℤ) :
    twosPhi k 1 (i1, i2) = twosPhi k 1 (i1 + 2, i2 - 2 * a) + 2 := by
  have h := phi_dupV hk (i1 + 2) (i2 - 2 * a)
  rw [show i1 + 2 + -2 = i1 by ring, show i2 - 2 * a + 2 * a = i2 by ring] at h
  exact h

/-- The rank of a `U`-translate is the rank of the point. -/
theorem rho_dupU' {a : ℤ} (i1 i2 : ℤ) :
    rhoTwos a 1 (i1, i2) = rhoTwos a 1 (i1 - (a + 1), i2 - (a - 1)) := by
  have h := rhoTwos_add_U a (i1 - (a + 1)) (i2 - (a - 1))
  rw [show i1 - (a + 1) + (a + 1) = i1 by ring, show i2 - (a - 1) + (a - 1) = i2 by ring] at h
  exact h

/-- The rank of a `V`-translate is the rank of the point. -/
theorem rho_dupV' {a : ℤ} (i1 i2 : ℤ) :
    rhoTwos a 1 (i1, i2) = rhoTwos a 1 (i1 + 2, i2 - 2 * a) := by
  have h := rhoTwos_add_V a (i1 + 2) (i2 - 2 * a)
  rw [show i1 + 2 + -2 = i1 by ring, show i2 - 2 * a + 2 * a = i2 by ring] at h
  exact h

/-- **The flat reduction to levels.** For a non-special tile point `p` and a native non-special neighbour `i` with equal
potential, `i` is a tile point of the same level, or a `U`-duplicate of a free site one level higher, or a `V`-duplicate of a
free site two levels lower, or the `V`-duplicate of the special free site `(a+1, a-2)`. -/
theorem flat_levels {a : ℤ} {k : ℕ} (hk : a = 2 * (k : ℤ) + 4) {p1 p2 i1 i2 : ℤ}
    (hp : TwosTile a (p1, p2)) (hp1 : ¬ (p1 = a ∧ p2 = 2 * a - 2)) (hp2 : ¬ (p1 = a ∧ p2 = 2 * a - 1))
    (hp3 : ¬ (p1 = a + 1 ∧ p2 = a - 2))
    (hN : NativeT a i1 i2) (hi1 : ¬ (i1 = a ∧ i2 = 2 * a - 2)) (hi2 : ¬ (i1 = a ∧ i2 = 2 * a - 1))
    (hi3 : ¬ (i1 = a + 1 ∧ i2 = a - 2))
    (hΦ : twosPhi k 1 (i1, i2) = twosPhi k 1 (p1, p2)) :
    (TwosTile a (i1, i2) ∧ twosLev a i1 i2 = twosLev a p1 p2) ∨
    (FreeSite a (i1 - (a + 1)) (i2 - (a - 1)) ∧ NativeT a (i1 - (a + 1)) (i2 - (a - 1)) ∧
      twosLev a (i1 - (a + 1)) (i2 - (a - 1)) = twosLev a p1 p2 + 1) ∨
    (FreeSite a (i1 + 2) (i2 - 2 * a) ∧ NativeT a (i1 + 2) (i2 - 2 * a) ∧
      twosLev a (i1 + 2) (i2 - 2 * a) = twosLev a p1 p2 - 2 ∧ ¬ (i1 + 2 = a + 1 ∧ i2 - 2 * a = a - 2)) ∨
    (i1 + 2 = a + 1 ∧ i2 - 2 * a = a - 2) := by
  have ep := phi_tile_lev hk hp hp1 hp2 hp3
  by_cases hT : TwosTile a (i1, i2)
  · left
    have ei := phi_tile_lev hk hT hi1 hi2 hi3
    exact ⟨hT, by linarith⟩
  rcases native_cases hN with hT' | hU | hV
  · exact absurd hT' hT
  · obtain ⟨hF, hNq⟩ := hU
    have hq3 : ¬ (i1 - (a + 1) = a + 1 ∧ i2 - (a - 1) = a - 2) := by
      intro h
      unfold NativeT at hN
      omega
    have hq1 : ¬ (i1 - (a + 1) = a ∧ i2 - (a - 1) = 2 * a - 2) := by
      intro h
      unfold FreeSite FreeHSite FreeVSite at hF
      omega
    have hq2 : ¬ (i1 - (a + 1) = a ∧ i2 - (a - 1) = 2 * a - 1) := by
      intro h
      unfold FreeSite FreeHSite FreeVSite at hF
      omega
    have eq := phi_tile_lev hk (free_tile hF hNq) hq1 hq2 hq3
    have eu := phi_dupU' hk i1 i2
    right
    left
    exact ⟨hF, hNq, by linarith⟩
  · obtain ⟨hF, hNq⟩ := hV
    by_cases hq : i1 + 2 = a + 1 ∧ i2 - 2 * a = a - 2
    · exact Or.inr (Or.inr (Or.inr hq))
    have hq1 : ¬ (i1 + 2 = a ∧ i2 - 2 * a = 2 * a - 2) := by
      intro h
      unfold FreeSite FreeHSite FreeVSite at hF
      omega
    have hq2 : ¬ (i1 + 2 = a ∧ i2 - 2 * a = 2 * a - 1) := by
      intro h
      unfold FreeSite FreeHSite FreeVSite at hF
      omega
    have eq := phi_tile_lev hk (free_tile hF hNq) hq1 hq2 (fun h => hq h)
    have ev := phi_dupV' hk i1 i2
    right
    right
    left
    exact ⟨hF, hNq, by linarith, hq⟩

end FLatticePaper.TwosEPolicy
