import FLatticePaper.Plane.Induction.TwosFreeAlias
import FLatticePaper.Plane.Induction.TwosBlackOdd

/-! Twos flatness, the selection at white centres. A free tile centre keeps its own free displacement (its free alias is
itself, `free_alias_unique`). The special tile point `(a, 2a-1)` is white and lies in the free class of `(-1, a)`, so it keeps the
free displacement of `(-1, a)`, which is `(0, -1)`. -/

noncomputable section

namespace FLatticePaper.TwosEPolicy

open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey
open scoped Classical

/-- A free native tile centre with zero charge keeps exactly its own free displacement. -/
theorem twosSel_free_self {a η : ℤ} {F : Field} (ha : 4 ≤ a) (he2 : a % 2 = 0) {c1 c2 i1 i2 : ℤ}
    (hl : laplacian F (c1, c2) = 0) (hc : TwosTile a (c1, c2)) (hF : FreeSite a c1 c2) :
    TwosSel a η F (c1, c2) (i1, i2) ↔
      (i1, i2) = (c1 + (freeDisp a η c1 c2).1, c2 + (freeDisp a η c1 c2).2) := by
  constructor
  · intro h
    rcases h with ⟨hm, -⟩ | ⟨-, h2 | h2⟩
    · rw [hl] at hm
      norm_num at hm
    · obtain ⟨⟨u1, u2⟩, hu, huF, hi⟩ := h2
      obtain ⟨e1, e2⟩ := free_alias_unique ha he2 hc hF hu huF
      subst e1
      subst e2
      exact hi
    · exfalso
      exact h2.1 ⟨(c1, c2), alias_self (c1, c2), hF⟩
  · intro h
    right
    refine ⟨hl, Or.inl ⟨(c1, c2), alias_self (c1, c2), hF, h⟩⟩

/-- The charge at an odd native site is `-1` or `0`, and it is `0` off the explicit black lines. -/
theorem lap_odd_value (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y) (hp : (x + y) % 2 = 1)
    (hw : ¬ LadderOddEvenBlack (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - y, x + 1)) :
    laplacian (standardField (List.replicate (k + 1) Digit.two)) (x, y) = 0 := by
  rw [laplacian_twos_native k hagree hperiod hn]
  simp only [rot_twos_ccw]
  have he : EvenSite (2 * (2 * (k : ℤ) + 4) - y, x + 1) := by
    unfold EvenSite
    dsimp only
    omega
  rw [if_pos he, if_neg hw]

/-- The free displacement at the non-native free site `(-1, a)` is `(0, -1)`. -/
theorem freeDisp_at_neg_one_a {a : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) : freeDisp a 1 (-1) a = (0, -1) := by
  unfold freeDisp
  rw [if_neg (by unfold FreeHSite; omega), if_neg (by omega), if_neg (by unfold EvenSite; dsimp only; omega)]

/-- The special tile point `(a, 2a-1)`: its charge is `0`, and its selected input is `(a, 2a-2)`. -/
theorem twosSel_special_1 (k : ℕ) {i1 i2 : ℤ}
    (hl : laplacian (standardField (List.replicate (k + 1) Digit.two)) (2 * (k : ℤ) + 4, 2 * (2 * (k : ℤ) + 4) - 1) = 0)
    (ha : 4 ≤ 2 * (k : ℤ) + 4)
    (h : TwosSel (2 * (k : ℤ) + 4) 1 (standardField (List.replicate (k + 1) Digit.two))
      (2 * (k : ℤ) + 4, 2 * (2 * (k : ℤ) + 4) - 1) (i1, i2)) :
    (i1, i2) = (2 * (k : ℤ) + 4, 2 * (2 * (k : ℤ) + 4) - 2) := by
  have he2 : (2 * (k : ℤ) + 4) % 2 = 0 := by omega
  rcases h with ⟨hm, -⟩ | ⟨-, h2 | ⟨hnfc, -⟩⟩
  · rw [hl] at hm
    norm_num at hm
  · obtain ⟨⟨u1, u2⟩, hu, huF, hi⟩ := h2
    by_cases hN : NativeT (2 * (k : ℤ) + 4) u1 u2
    · exfalso
      have hut : TwosTile (2 * (k : ℤ) + 4) (u1, u2) := free_tile huF hN
      have hk : classKey (2 * (k : ℤ) + 4) (u1, u2) = classKey (2 * (k : ℤ) + 4)
          (2 * (k : ℤ) + 4, 2 * (2 * (k : ℤ) + 4) - 1) := alias_classKey hu
      have hp : TwosTile (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 4, 2 * (2 * (k : ℤ) + 4) - 1) := tile_a_2a1 ha
      obtain ⟨e1, e2⟩ := tile_unique ha he2 hut hp hk
      rw [e1, e2] at huF
      unfold FreeSite FreeHSite FreeVSite at huF
      omega
    · have hxy := free_nonnative_eq ha huF hN
      obtain ⟨hx, hy⟩ := hxy
      subst hx
      subst hy
      simp only at hi
      rw [freeDisp_at_neg_one_a ha he2] at hi
      simp only [Prod.mk.injEq] at hi
      obtain ⟨h1, h2⟩ := hi
      rw [h1, h2]
      exact Prod.ext (by ring) (by ring)
  · exfalso
    exact hnfc ⟨(-1, 2 * (k : ℤ) + 4), ⟨1, 0, Prod.ext (by dsimp only; ring) (by dsimp only; ring)⟩,
      Or.inr (Or.inr ⟨rfl, by omega, by omega⟩)⟩

end FLatticePaper.TwosEPolicy
