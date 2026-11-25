import FLatticePaper.Plane.Induction.TwosMinusRank

/-! Twos flatness, sign `-1`: the rank at a non-free tile point as an explicit `if` tree on the regions of `(h, y)`, `h = y - x`.
These are the inputs of the even black drop lemmas (the sign `-1` analogue of `TwosRhoCases`, sign `+1`). The free tile points use
`rhoTwos_tile_freeH_eta` and `rhoTwos_tile_freeV_eta` directly. -/

noncomputable section

namespace FLatticePaper.TwosEPolicy

/-- The sign `-1` bulk rank as an explicit `if` tree on the regions of `(h, y)`, `h = y - x`, with the parity term `(x + y) % 2`. -/
def bulkTreeM (a x y : ℤ) : ℤ :=
  if y - x = -1 then (if x = 2 then 2 else 2 * a + 6 - 2 * y)
  else if y - x = a - 1 then (if x = 1 then 2 * a else 2 * x + 4)
  else if y - x ≤ a - 2 then
    (if y ≤ a - 1 then 2 * y + 1 - (x + y) % 2 else if y = a then 1 - (x + y) % 2
      else 4 * a + 1 - 2 * y - (x + y) % 2)
  else if y ≤ 2 * a - 1 then 2 * y - 2 * a + 3 - (x + y) % 2
    else if y = 2 * a then 1 - (x + y) % 2 else 6 * a + 3 - 2 * y - (x + y) % 2

/-- The value of `bulkTreeM` on each region of `(h, y)` (sign `-1`), each as a lemma with the region as hypotheses. -/
theorem bt_F1 (a x y : ℤ) (h : y - x = -1) (hx : x = 2) : bulkTreeM a x y = 2 := by
  unfold bulkTreeM
  rw [if_pos h, if_pos hx]

theorem bt_F2 (a x y : ℤ) (h : y - x = -1) (hx : x ≠ 2) : bulkTreeM a x y = 2 * a + 6 - 2 * y := by
  unfold bulkTreeM
  rw [if_pos h, if_neg hx]

theorem bt_M1 (a x y : ℤ) (ha : 4 ≤ a) (h : y - x = a - 1) (hx : x = 1) : bulkTreeM a x y = 2 * a := by
  unfold bulkTreeM
  rw [if_neg (show ¬ (y - x = -1) by omega), if_pos h, if_pos hx]

theorem bt_M2 (a x y : ℤ) (ha : 4 ≤ a) (h : y - x = a - 1) (hx : x ≠ 1) : bulkTreeM a x y = 2 * x + 4 := by
  unfold bulkTreeM
  rw [if_neg (show ¬ (y - x = -1) by omega), if_pos h, if_neg hx]

theorem bt_L (a x y : ℤ) (h1 : y - x ≠ -1) (h2 : y - x ≠ a - 1) (h3 : y - x ≤ a - 2) (h4 : y ≤ a - 1) :
    bulkTreeM a x y = 2 * y + 1 - (x + y) % 2 := by
  unfold bulkTreeM
  rw [if_neg h1, if_neg h2, if_pos h3, if_pos h4]

theorem bt_E (a x y : ℤ) (h1 : y - x ≠ -1) (h2 : y - x ≠ a - 1) (h3 : y - x ≤ a - 2) (h4 : y = a) :
    bulkTreeM a x y = 1 - (x + y) % 2 := by
  unfold bulkTreeM
  rw [if_neg h1, if_neg h2, if_pos h3, if_neg (show ¬ (y ≤ a - 1) by omega), if_pos h4]

theorem bt_H (a x y : ℤ) (h1 : y - x ≠ -1) (h2 : y - x ≠ a - 1) (h3 : y - x ≤ a - 2) (h4 : a + 1 ≤ y) :
    bulkTreeM a x y = 4 * a + 1 - 2 * y - (x + y) % 2 := by
  unfold bulkTreeM
  rw [if_neg h1, if_neg h2, if_pos h3, if_neg (show ¬ (y ≤ a - 1) by omega), if_neg (show ¬ (y = a) by omega)]

theorem bt_hL (a x y : ℤ) (h1 : y - x ≠ -1) (h2 : y - x ≠ a - 1) (h3 : a ≤ y - x) (h4 : y ≤ 2 * a - 1) :
    bulkTreeM a x y = 2 * y - 2 * a + 3 - (x + y) % 2 := by
  unfold bulkTreeM
  rw [if_neg h1, if_neg h2, if_neg (show ¬ (y - x ≤ a - 2) by omega), if_pos h4]

theorem bt_hE (a x y : ℤ) (h1 : y - x ≠ -1) (h2 : y - x ≠ a - 1) (h3 : a ≤ y - x) (h4 : y = 2 * a) :
    bulkTreeM a x y = 1 - (x + y) % 2 := by
  unfold bulkTreeM
  rw [if_neg h1, if_neg h2, if_neg (show ¬ (y - x ≤ a - 2) by omega), if_neg (show ¬ (y ≤ 2 * a - 1) by omega),
    if_pos h4]

theorem bt_hH (a x y : ℤ) (h1 : y - x ≠ -1) (h2 : y - x ≠ a - 1) (h3 : a ≤ y - x) (h4 : 2 * a + 1 ≤ y) :
    bulkTreeM a x y = 6 * a + 3 - 2 * y - (x + y) % 2 := by
  unfold bulkTreeM
  rw [if_neg h1, if_neg h2, if_neg (show ¬ (y - x ≤ a - 2) by omega), if_neg (show ¬ (y ≤ 2 * a - 1) by omega),
    if_neg (show ¬ (y = 2 * a) by omega)]

/-- The ten regions of `bulkTreeM`, each with its value and region conditions (sign `-1`). -/
theorem bt_cover (a x y : ℤ) (ha : 4 ≤ a) :
    (bulkTreeM a x y = 2 ∧ y - x = -1 ∧ x = 2) ∨
    (bulkTreeM a x y = 2 * a + 6 - 2 * y ∧ y - x = -1 ∧ x ≠ 2) ∨
    (bulkTreeM a x y = 2 * a ∧ y - x = a - 1 ∧ x = 1) ∨
    (bulkTreeM a x y = 2 * x + 4 ∧ y - x = a - 1 ∧ x ≠ 1) ∨
    (bulkTreeM a x y = 2 * y + 1 - (x + y) % 2 ∧ y - x ≠ -1 ∧ y - x ≠ a - 1 ∧ y - x ≤ a - 2 ∧ y ≤ a - 1) ∨
    (bulkTreeM a x y = 1 - (x + y) % 2 ∧ y - x ≠ -1 ∧ y - x ≠ a - 1 ∧ y - x ≤ a - 2 ∧ y = a) ∨
    (bulkTreeM a x y = 4 * a + 1 - 2 * y - (x + y) % 2 ∧ y - x ≠ -1 ∧ y - x ≠ a - 1 ∧ y - x ≤ a - 2 ∧ a + 1 ≤ y) ∨
    (bulkTreeM a x y = 2 * y - 2 * a + 3 - (x + y) % 2 ∧ y - x ≠ -1 ∧ y - x ≠ a - 1 ∧ a ≤ y - x ∧ y ≤ 2 * a - 1) ∨
    (bulkTreeM a x y = 1 - (x + y) % 2 ∧ y - x ≠ -1 ∧ y - x ≠ a - 1 ∧ a ≤ y - x ∧ y = 2 * a) ∨
    (bulkTreeM a x y = 6 * a + 3 - 2 * y - (x + y) % 2 ∧ y - x ≠ -1 ∧ y - x ≠ a - 1 ∧ a ≤ y - x ∧ 2 * a + 1 ≤ y) := by
  by_cases h1 : y - x = -1
  · by_cases h2 : x = 2
    · exact Or.inl <| ⟨bt_F1 a x y h1 h2, h1, h2⟩
    · exact Or.inr <| Or.inl <| ⟨bt_F2 a x y h1 h2, h1, h2⟩
  by_cases h2 : y - x = a - 1
  · by_cases h3 : x = 1
    · exact Or.inr <| Or.inr <| Or.inl <| ⟨bt_M1 a x y ha h2 h3, h2, h3⟩
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl <| ⟨bt_M2 a x y ha h2 h3, h2, h3⟩
  by_cases h3 : y - x ≤ a - 2
  · by_cases h4 : y ≤ a - 1
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| ⟨bt_L a x y h1 h2 h3 h4, h1, h2, h3, h4⟩
    · by_cases h5 : y = a
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| ⟨bt_E a x y h1 h2 h3 h5, h1, h2, h3, h5⟩
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| ⟨bt_H a x y h1 h2 h3 (by omega), h1, h2, h3, by omega⟩
  · by_cases h4 : y ≤ 2 * a - 1
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| ⟨bt_hL a x y h1 h2 (by omega) h4, h1, h2, by omega, h4⟩
    · by_cases h5 : y = 2 * a
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| ⟨bt_hE a x y h1 h2 (by omega) h5, h1, h2, by omega, h5⟩
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| ⟨bt_hH a x y h1 h2 (by omega) (by omega), h1, h2, by omega, by omega⟩

/-- The rank at a non-free tile point other than `(a, 2a-1)`, as the explicit tree `bulkTreeM` (sign `-1`). -/
theorem rho_bulk_eq_m {a x y : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hp : TwosTile a (x, y))
    (hF : ¬ FreeSite a x y) (hsp : ¬ (x = a ∧ y = 2 * a - 1)) :
    rhoTwos a (-1) (x, y) = bulkTreeM a x y := by
  rw [rhoTwos_tile_bulk_eta (-1) ha he2 hp hF hsp]
  unfold bulkR bulkTreeM
  simp only [show ((-1 : ℤ) = 1) = False from by norm_num, if_false]
  split_ifs <;> omega

/-- The sign `-1` free V value as an explicit `if` tree. -/
theorem freeV_minus_eq (a x y : ℤ) : freeV a (-1) x y =
    (if y = 0 then 5 else if y < a then 2 * a + 3 - 2 * y - y % 2 else if y = a then 2
      else if y = a + 1 then 1 else 2 * a + 4 - 2 * (y - a) + (y - a) % 2) := by
  unfold freeV
  simp only [show ((-1 : ℤ) = 1) = False from by norm_num, if_false]

end FLatticePaper.TwosEPolicy
