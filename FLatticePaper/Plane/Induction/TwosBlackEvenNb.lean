import FLatticePaper.Plane.Induction.TwosNativeDec
import FLatticePaper.Plane.Induction.TwosBlackEven

/-! Twos flatness, black even centres: the horizontal neighbours of a black even native site are native.

Each case of the column of the centre uses the decision lemmas of `TwosNativeDec` and only the white pieces that the case
needs (`ewp_k`), so that no `omega` sees the whole ten-piece disjunction. -/

noncomputable section

namespace FLatticePaper.TwosEPolicy

/-- The left neighbour of a black even native site is native. -/
theorem even_black_nat_left {a x y : ℤ} (ha : 4 ≤ a) (hN : NativeT a x y) (hB : ¬ EvenWhitePiece a x y)
    (he : (x + y) % 2 = 0) : NativeT a (x - 1) y := by
  have eA1 : ¬ (y - x = 2 * a ∧ 1 ≤ x ∧ x ≤ a - 2) := fun h => hB (ewp_1 h)
  have eA2 : x = -1 → ¬ (a + 1 ≤ y ∧ y ≤ 2 * a - 1) := fun hx h => hB (ewp_2 ⟨hx, h.1, h.2⟩)
  have eA3 : x = 0 → ¬ (0 ≤ y ∧ y ≤ a) := fun hx h => hB (ewp_3 ⟨hx, h.1, h.2⟩)
  have eE : x = 0 → ¬ (y = 2 * a) := fun hx h => hB (ewp_9 ⟨hx, h⟩)
  clear hB
  have hxr : -1 ≤ x ∧ x ≤ a + 1 := by
    unfold NativeT at hN
    omega
  rcases (show x = -1 ∨ x = 0 ∨ (1 ≤ x ∧ x ≤ a) ∨ x = a + 1 by omega) with h | h | ⟨h1, h2⟩ | h
  · exfalso
    have hA := eA2 h
    subst h
    rw [nat_neg1_iff] at hN
    omega
  · have hA3 := eA3 h
    have hE := eE h
    subst h
    rw [show (0 : ℤ) - 1 = -1 by norm_num, nat_neg1_iff]
    rw [nat_mid_iff (le_refl (0 : ℤ)) (by omega)] at hN
    omega
  · rw [nat_mid_iff (by omega : (0 : ℤ) ≤ x) h2] at hN
    rw [nat_mid_iff (by omega : (0 : ℤ) ≤ x - 1) (by omega : x - 1 ≤ a)]
    omega
  · subst h
    rw [nat_a1_iff] at hN
    rw [nat_mid_iff (by omega : (0 : ℤ) ≤ a + 1 - 1) (by omega : a + 1 - 1 ≤ a)]
    omega

/-- The right neighbour of a black even native site is native. -/
theorem even_black_nat_right {a x y : ℤ} (ha : 4 ≤ a) (hN : NativeT a x y) (hB : ¬ EvenWhitePiece a x y)
    (he : (x + y) % 2 = 0) : NativeT a (x + 1) y := by
  have eB1 : ¬ (y - x = -2 ∧ 2 ≤ x ∧ x ≤ a - 1) := fun h => hB (ewp_4 h)
  have eB2 : x = a + 1 → ¬ (a - 1 ≤ y ∧ y ≤ 2 * a - 3) := fun hx h => hB (ewp_5 ⟨hx, h.1, h.2⟩)
  have eB3 : x = a → ¬ (2 * a - 2 ≤ y ∧ y ≤ 3 * a - 2) := fun hx h => hB (ewp_6 ⟨hx, h.1, h.2⟩)
  have eF : x = a → ¬ (y = a - 2) := fun hx h => hB (ewp_10 ⟨hx, h⟩)
  clear hB
  have hxr : -1 ≤ x ∧ x ≤ a + 1 := by
    unfold NativeT at hN
    omega
  rcases (show x = -1 ∨ x = 0 ∨ (1 ≤ x ∧ x ≤ a - 1) ∨ x = a ∨ x = a + 1 by omega) with h | h | ⟨h1, h2⟩ | h | h
  · subst h
    rw [nat_neg1_iff] at hN
    rw [show (-1 : ℤ) + 1 = 0 by norm_num, nat_mid_iff (le_refl (0 : ℤ)) (by omega)]
    omega
  · subst h
    rw [nat_mid_iff (le_refl (0 : ℤ)) (by omega)] at hN
    rw [show (0 : ℤ) + 1 = 1 by norm_num, nat_mid_iff (by omega : (0 : ℤ) ≤ 1) (by omega : (1 : ℤ) ≤ a)]
    omega
  · rw [nat_mid_iff (by omega : (0 : ℤ) ≤ x) (by omega : x ≤ a)] at hN
    rw [nat_mid_iff (by omega : (0 : ℤ) ≤ x + 1) (by omega : x + 1 ≤ a)]
    have := eB1
    omega
  · have hF := eF h
    have hB3 := eB3 h
    subst x
    rw [nat_mid_iff (by omega : (0 : ℤ) ≤ a) (le_refl a)] at hN
    rw [nat_a1_iff]
    omega
  · have hB2 := eB2 h
    subst h
    rw [nat_a1_iff] at hN
    exfalso
    omega

end FLatticePaper.TwosEPolicy
