import FLatticePaper.Plane.Induction.TwosEPolicy

/-! Twos flatness, native decisions by cases on `x`. `NativeT a x y` is a disjunction of the box and the two corners; each
case of `x` below is a separate decision lemma with linear conditions only, so that `omega` never sees the whole disjunction. -/

noncomputable section

namespace FLatticePaper.TwosEPolicy

/-- At a middle column `0 ≤ x ≤ a`, native is the box alone. -/
theorem nat_mid_iff {a x y : ℤ} (h0 : 0 ≤ x) (h1 : x ≤ a) :
    NativeT a x y ↔ (1 ≤ y + 1 ∧ y + 1 ≤ 3 * a - 1 ∧ -1 ≤ y + 1 - x ∧ y + 1 - x ≤ 2 * a + 1) := by
  unfold NativeT
  constructor
  · rintro (⟨hb, -⟩ | hc | hc)
    · omega
    · omega
    · omega
  · intro h
    refine Or.inl ⟨?_, ?_⟩
    · omega
    · rintro (hs | hs) <;> omega

/-- The column `x = -1`: native is the box with the strip removed, or the corner `y + 1 = 2a + 1`. -/
theorem nat_neg1_iff {a y : ℤ} :
    NativeT a (-1) y ↔ ((a + 2 ≤ y + 1 ∧ y + 1 ≤ 3 * a - 1 ∧ y + 2 ≤ 2 * a + 1) ∨ y + 1 = 2 * a + 1) := by
  unfold NativeT
  constructor
  · rintro (⟨hb, hs⟩ | hc | hc)
    · omega
    · omega
    · omega
  · rintro (h | h)
    · refine Or.inl ⟨?_, ?_⟩
      · omega
      · intro hs
        omega
    · exact Or.inr (Or.inl ⟨rfl, h⟩)

/-- The column `x = a + 1`: native is the box with the strip removed, or the corner `y + 1 = a - 1`. -/
theorem nat_a1_iff {a y : ℤ} :
    NativeT a (a + 1) y ↔ ((1 ≤ y + 1 ∧ y + 1 ≤ 2 * a - 2 ∧ y + 1 ≤ 3 * a - 1 ∧ a ≤ y + 1 ∧
      y + 1 ≤ 3 * a + 2) ∨ y + 1 = a - 1) := by
  unfold NativeT
  constructor
  · rintro (⟨hb, hs⟩ | hc | hc)
    · omega
    · omega
    · exact Or.inr hc.2
  · rintro (h | h)
    · refine Or.inl ⟨?_, ?_⟩
      · omega
      · intro hs
        omega
    · exact Or.inr (Or.inr ⟨rfl, h⟩)

end FLatticePaper.TwosEPolicy
