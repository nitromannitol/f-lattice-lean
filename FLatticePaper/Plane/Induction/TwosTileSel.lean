import FLatticePaper.Plane.Induction.TwosTileColour
import FLatticePaper.Plane.Induction.TwosTileUnique
import FLatticePaper.Plane.Induction.TwosDeckTile

/-! The selected inputs of the twos policy at a tile point (sign `+1`).

At a tile point `t` the selected step is one of: the Edge partners of `t` (black); the free table step at `t` (a free site);
the free step of `(−1, a)` at the special point `(a, 2a−1)`; the candidate step at a non-free white native point. The reason is
that the alias of `t` in a free class is the free site itself (or `(−1, a)`, which is `t − U`), and the native alias of a
non-free class is the tile point (`tile_unique`). -/

namespace FLatticePaper.TwosEPolicy

open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey
open scoped Classical

theorem emod_add_mul_self' (x m T : ℤ) : (x + m * T) % T = x % T := by
  rw [Int.add_emod, Int.mul_emod_left, add_zero, Int.emod_emod]

theorem aliasOf_trans {a : ℤ} {c u v : Site} (h1 : AliasOf a c u) (h2 : AliasOf a u v) : AliasOf a c v := by
  obtain ⟨i, l, hi⟩ := h1
  obtain ⟨j, m, hj⟩ := h2
  refine ⟨i + j, l + m, ?_⟩
  rw [hj, hi]
  exact Prod.ext (by dsimp only; ring) (by dsimp only; ring)

theorem classKey_alias {a : ℤ} {c u : Site} (h : AliasOf a c u) : classKey a c = classKey a u := by
  obtain ⟨i, l, hi⟩ := h
  rw [hi]
  unfold classKey
  have e : (a - 1) * c.1 - (a + 1) * c.2 =
      ((a - 1) * (c.1 - i * (a + 1) + 2 * l) - (a + 1) * (c.2 - i * (a - 1) - 2 * a * l)) +
        (-l) * (2 * a * a + 4 * a - 2) := by
    ring
  rw [e, emod_add_mul_self']

theorem tile_special {a : ℤ} (ha : 4 ≤ a) (he : a % 2 = 0) : TwosTile a (a, 2 * a - 1) := by
  refine tc_tile_of_noAlias ?_ (Or.inr ?_)
  · show NativeT a a (2 * a - 1)
    unfold NativeT
    exact Or.inl ⟨⟨by omega, by omega, by omega, by omega, by omega, by omega⟩, by omega⟩
  · intro v hv hvN
    obtain ⟨v1, v2⟩ := v
    simp only [FreeSite, FreeHSite, FreeVSite] at hv
    unfold NativeT at hvN
    constructor
    · intro h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      rcases hv with (⟨e1, e2⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2⟩) | (⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩)
      all_goals omega
    · intro h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      rcases hv with (⟨e1, e2⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2⟩) | (⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩)
      all_goals omega

/-- A free alias of a tile point is the point itself, or the special case `(−1, a)` of the point `(a, 2a−1)`. -/
theorem tile_alias_free {a x y u1 u2 : ℤ} (ha : 4 ≤ a) (he : a % 2 = 0) (ht : TwosTile a (x, y))
    (hA : AliasOf a (x, y) (u1, u2)) (hF : FreeSite a u1 u2) :
    (u1 = x ∧ u2 = y ∧ FreeSite a x y) ∨ (u1 = -1 ∧ u2 = a ∧ x = a ∧ y = 2 * a - 1) := by
  by_cases hnat : NativeT a u1 u2
  · have htu : TwosTile a (u1, u2) := ⟨hnat, fun h => h.2 hF⟩
    obtain ⟨h1, h2⟩ := tile_unique ha he ht htu (classKey_alias hA)
    subst h1
    subst h2
    exact Or.inl ⟨rfl, rfl, hF⟩
  · have hu : u1 = -1 ∧ u2 = a := by
      unfold NativeT at hnat
      unfold FreeSite FreeHSite FreeVSite at hF
      omega
    obtain ⟨hu1, hu2⟩ := hu
    rw [hu1, hu2] at hA
    have hsp : AliasOf a (a, 2 * a - 1) (-1, a) := ⟨1, 0, Prod.ext (by dsimp only; ring) (by dsimp only; ring)⟩
    obtain ⟨h1, h2⟩ := tile_unique ha he ht (tile_special ha he) ((classKey_alias hA).trans (classKey_alias hsp).symm)
    exact Or.inr ⟨hu1, hu2, h1, h2⟩

/-- A native alias of a non-free tile point is the point itself. -/
theorem tile_alias_native {a x y u1 u2 : ℤ} (ha : 4 ≤ a) (he : a % 2 = 0) (ht : TwosTile a (x, y))
    (hnFC : ¬ FreeClass a (x, y)) (hA : AliasOf a (x, y) (u1, u2)) (hN : NativeT a u1 u2) :
    u1 = x ∧ u2 = y := by
  have htu : TwosTile a (u1, u2) := by
    refine ⟨hN, ?_⟩
    rintro ⟨⟨v, hvF, hvN, hp⟩, -⟩
    apply hnFC
    refine ⟨v, ?_, hvF⟩
    rcases hp with hp | hp
    · have hvu : AliasOf a (u1, u2) v := ⟨1, 0, by
        rw [hp]; exact Prod.ext (by dsimp only; ring) (by dsimp only; ring)⟩
      exact aliasOf_trans hA hvu
    · have hvu : AliasOf a (u1, u2) v := ⟨0, 1, by
        rw [hp]; exact Prod.ext (by dsimp only; ring) (by dsimp only; ring)⟩
      exact aliasOf_trans hA hvu
  obtain ⟨h1, h2⟩ := tile_unique ha he ht htu (classKey_alias hA)
  exact ⟨h1.symm, h2.symm⟩

end FLatticePaper.TwosEPolicy
