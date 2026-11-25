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

/-- The free step of `(−1, a)` (η = 1): the free table gives `(0, −1)`, since `(−1, a)` is odd for even `a`. -/
theorem freeDisp_neg_one {a : ℤ} (he : a % 2 = 0) : freeDisp a 1 (-1) a = (0, -1) := by
  have hnH : ¬ FreeHSite a (-1) a := by
    unfold FreeHSite
    omega
  have h00 : ¬ ((-1 : ℤ) = 0 ∧ a = 0) := by omega
  have hodd : ¬ EvenSite (-1, a) := by
    unfold EvenSite
    omega
  unfold freeDisp
  rw [if_neg hnH, if_neg h00, if_neg hodd]

/-- **The selected inputs at a tile point (sign `+1`).** Black: an Edge partner. White free: the free table step at the point
itself, or at the special point `(a, 2a−1)` (where the free alias is `(−1, a)`). White non-free: the candidate step. -/
theorem tile_twosSel (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    {x y : ℤ} (ht : TwosTile (2 * (k : ℤ) + 4) (x, y)) {i : Site}
    (hT : TwosSel (2 * (k : ℤ) + 4) 1 (standardField (List.replicate (k + 1) Digit.two)) (x, y) i) :
    (TwosBlackP (2 * (k : ℤ) + 4) x y ∧ Edge i (x, y)) ∨
    (¬ TwosBlackP (2 * (k : ℤ) + 4) x y ∧
      ((FreeSite (2 * (k : ℤ) + 4) x y ∧
          i = (x + (freeDisp (2 * (k : ℤ) + 4) 1 x y).1, y + (freeDisp (2 * (k : ℤ) + 4) 1 x y).2)) ∨
       (x = 2 * (k : ℤ) + 4 ∧ y = 2 * (2 * (k : ℤ) + 4) - 1 ∧ i = (x, y - 1)) ∨
       (¬ FreeClass (2 * (k : ℤ) + 4) (x, y) ∧ CandGuard (2 * (k : ℤ) + 4) x y ∧
          i = (x + (candDisp (2 * (k : ℤ) + 4) x y).1, y + (candDisp (2 * (k : ℤ) + 4) x y).2)))) := by
  have ha : 4 ≤ 2 * (k : ℤ) + 4 := by omega
  have he : (2 * (k : ℤ) + 4) % 2 = 0 := by omega
  have hcol := tile_colour k hagree hperiod (show NativeT (2 * (k : ℤ) + 4) x y from ht.1)
  unfold TwosSel at hT
  rcases hT with ⟨hb, hE⟩ | ⟨hw, hrest⟩
  · left
    refine ⟨?_, hE⟩
    rw [hcol] at hb
    by_contra h
    rw [if_neg h] at hb
    norm_num at hb
  · right
    have hnb : ¬ TwosBlackP (2 * (k : ℤ) + 4) x y := by
      intro h
      rw [hcol, if_pos h] at hw
      norm_num at hw
    refine ⟨hnb, ?_⟩
    rcases hrest with ⟨u, hA, hF, hi⟩ | ⟨hnFC, u, hA, hN, hC, hi⟩
    · obtain ⟨u1, u2⟩ := u
      rcases tile_alias_free ha he ht hA hF with ⟨h1, h2, hFxy⟩ | ⟨h1, h2, hx, hy⟩
      · left
        refine ⟨hFxy, ?_⟩
        dsimp only at hi
        rw [h1, h2] at hi
        exact hi
      · right
        left
        dsimp only at hi
        rw [h1, h2, freeDisp_neg_one he] at hi
        refine ⟨hx, hy, ?_⟩
        rw [hi]
        exact Prod.ext (by simp) (by simp [sub_eq_add_neg])
    · obtain ⟨u1, u2⟩ := u
      obtain ⟨h1, h2⟩ := tile_alias_native ha he ht hnFC hA hN
      right
      right
      dsimp only at hi hC
      rw [h1, h2] at hi
      rw [h1, h2] at hC
      exact ⟨hnFC, hC, hi⟩

end FLatticePaper.TwosEPolicy
