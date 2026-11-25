import FLatticePaper.Plane.Induction.TwosTileLevel

/-! Twos flatness, step (i), tile points: the tile as linear conditions, and the key condition at the tile points.

`TwosTile a (x, y)` is the native point which is not a duplicated free copy (`dup_iff`, `tile_iff_lin`). A tile point other than the
three special points `(a, 2a-2)`, `(a, 2a-1)`, `(a+1, a-2)` has `TwosKey (x+1, y+1)` (`tile_key_succ`), so `chain_level_native` applies. -/

noncomputable section

namespace FLatticePaper.TwosEPolicy

open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey
open scoped Classical

/-- The duplicated free copies of a tile point, as linear conditions: `p - U` or `p - V` is a native free site. -/
theorem dup_iff (a x y : ℤ) :
    (∃ v : Site, FreeSite a v.1 v.2 ∧ NativeT a v.1 v.2 ∧
      ((x, y) = (v.1 + (a + 1), v.2 + (a - 1)) ∨ (x, y) = (v.1 - 2, v.2 + 2 * a))) ↔
    ((FreeSite a (x - (a + 1)) (y - (a - 1)) ∧ NativeT a (x - (a + 1)) (y - (a - 1))) ∨
      (FreeSite a (x + 2) (y - 2 * a) ∧ NativeT a (x + 2) (y - 2 * a))) := by
  constructor
  · rintro ⟨⟨v1, v2⟩, hF, hN, h | h⟩
    · simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have e1 : v1 = x - (a + 1) := by omega
      have e2 : v2 = y - (a - 1) := by omega
      subst e1
      subst e2
      exact Or.inl ⟨hF, hN⟩
    · simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have e1 : v1 = x + 2 := by omega
      have e2 : v2 = y - 2 * a := by omega
      subst e1
      subst e2
      exact Or.inr ⟨hF, hN⟩
  · rintro (⟨hF, hN⟩ | ⟨hF, hN⟩)
    · exact ⟨(x - (a + 1), y - (a - 1)), hF, hN, Or.inl (by simp only [Prod.mk.injEq]; constructor <;> ring)⟩
    · exact ⟨(x + 2, y - 2 * a), hF, hN, Or.inr (by simp only [Prod.mk.injEq]; constructor <;> ring)⟩

/-- The tile point, as linear conditions. -/
theorem tile_iff_lin (a x y : ℤ) : TwosTile a (x, y) ↔ (NativeT a x y ∧
    ¬ ((((FreeSite a (x - (a + 1)) (y - (a - 1))) ∧ NativeT a (x - (a + 1)) (y - (a - 1))) ∨
      ((FreeSite a (x + 2) (y - 2 * a)) ∧ NativeT a (x + 2) (y - 2 * a))) ∧ ¬ FreeSite a x y)) := by
  unfold TwosTile
  simp only
  rw [dup_iff]

set_option maxHeartbeats 400000 in
/-- A tile point other than the three special points has `TwosKey (x+1, y+1)`. -/
theorem tile_key_succ (a x y : ℤ) (ha : 4 ≤ a) (ht : TwosTile a (x, y)) (h1 : ¬ (x = a ∧ y = 2 * a - 2))
    (h2 : ¬ (x = a ∧ y = 2 * a - 1)) (h3 : ¬ (x = a + 1 ∧ y = a - 2)) : TwosKey a (x + 1) (y + 1) := by
  rw [tile_iff_lin] at ht
  obtain ⟨hN, hnot⟩ := ht
  by_cases hf : FreeSite a x y
  · unfold NativeT at hN
    unfold TwosKey
    unfold FreeSite FreeHSite FreeVSite at hf
    omega
  · have hnd : ¬ ((FreeSite a (x - (a + 1)) (y - (a - 1)) ∧ NativeT a (x - (a + 1)) (y - (a - 1))) ∨
        (FreeSite a (x + 2) (y - 2 * a) ∧ NativeT a (x + 2) (y - 2 * a))) := fun h => hnot ⟨h, hf⟩
    rcases hN with ⟨⟨n1, n2, n3, n4, n5, n6⟩, nst⟩ | ⟨n1, n2⟩ | ⟨n1, n2⟩
    · have hxa1 : x ≠ a + 1 := by
        intro hx
        apply hnd
        left
        exact ⟨by unfold FreeSite FreeHSite FreeVSite; omega, by unfold NativeT; omega⟩
      have hy3 : y + 1 ≠ 3 * a - 1 := by
        intro hy
        apply hnd
        have hc : x = a - 2 ∨ x = a - 1 ∨ x = a := by omega
        rcases hc with hc | hc | hc
        · right
          exact ⟨by unfold FreeSite FreeHSite FreeVSite; omega, by unfold NativeT; omega⟩
        · right
          exact ⟨by unfold FreeSite FreeHSite FreeVSite; omega, by unfold NativeT; omega⟩
        · left
          exact ⟨by unfold FreeSite FreeHSite FreeVSite; omega, by unfold NativeT; omega⟩
      have hya : x = a → y ≤ 2 * a - 1 := by
        intro hx
        by_contra hy
        apply hnd
        left
        exact ⟨by unfold FreeSite FreeHSite FreeVSite; omega, by unfold NativeT; omega⟩
      unfold TwosKey
      by_cases hsp : x = a ∧ y = 2 * a - 3
      · right; right; right; right
        constructor <;> omega
      · left
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
    · obtain rfl : x = -1 := n1
      have hy : y = 2 * a := by omega
      subst hy
      exact (hnd (Or.inr ⟨by unfold FreeSite FreeHSite FreeVSite; omega, by unfold NativeT; omega⟩)).elim
    · exact (h3 ⟨by omega, by omega⟩).elim

end FLatticePaper.TwosEPolicy
