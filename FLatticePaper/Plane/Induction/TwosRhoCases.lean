import FLatticePaper.Plane.Induction.TwosRankVal
import FLatticePaper.Plane.Induction.TwosTileRho

/-! Twos flatness, the rank at a tile point as a case disjunction (sign `+1`): each case gives the value as a linear
expression with the parity term, on an explicit region of `(x, y)`. These are the inputs of the drop lemmas. -/

noncomputable section

namespace FLatticePaper.TwosEPolicy

/-- The rank at a non-free tile point (not the special `(a, 2a-1)`), by the region of `(h, y)`, `h = y - x`. -/
theorem rho_bulk_cases {a x y : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hp : TwosTile a (x, y))
    (hF : ¬ FreeSite a x y) (hsp : ¬ (x = a ∧ y = 2 * a - 1)) :
    (y - x ≤ a - 2 ∧ y - x ≠ -1 ∧ y ≤ a - 1 ∧ rhoTwos a 1 (x, y) = 2 * y - (x + y) % 2) ∨
    (y - x ≤ a - 2 ∧ y - x ≠ -1 ∧ a - 1 ≤ y ∧ rhoTwos a 1 (x, y) = 4 * a - 4 - 2 * y - (x + y) % 2) ∨
    (a ≤ y - x ∧ y ≤ 2 * a - 1 ∧ rhoTwos a 1 (x, y) = 2 * y - 2 * a + 2 - (x + y) % 2) ∨
    (a ≤ y - x ∧ 2 * a - 1 ≤ y ∧ rhoTwos a 1 (x, y) = 6 * a - 2 - 2 * y - (x + y) % 2) ∨
    (y - x = a - 1 ∧ rhoTwos a 1 (x, y) = 2 * x + 3) ∨
    (y - x = -1 ∧ x = a ∧ rhoTwos a 1 (x, y) = 2 * a - 3) ∨
    (y - x = -1 ∧ x ≠ a ∧ rhoTwos a 1 (x, y) = 2 * a + 1 - 2 * y) := by
  rw [rhoTwos_tile_bulk ha he2 hp hF hsp]
  by_cases h1 : y - x = -1
  · by_cases hxa : x = a
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, hxa, by rw [bulk_first h1, if_pos hxa]⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, hxa, by rw [bulk_first h1, if_neg hxa]⟩)))))
  by_cases h2 : y - x = a - 1
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, bulk_mid ha h2⟩))))
  by_cases h3 : y - x ≤ a - 2
  · by_cases h4 : y ≤ a - 1
    · exact Or.inl ⟨h3, h1, h4, bulk_low_lo h3 h1 h4⟩
    · exact Or.inr (Or.inl ⟨h3, h1, by omega, bulk_low_hi h3 h1 (by omega)⟩)
  · by_cases h4 : y ≤ 2 * a - 1
    · exact Or.inr (Or.inr (Or.inl ⟨by omega, h4, bulk_high_lo ha (by omega) h4⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, bulk_high_hi ha (by omega) (by omega)⟩)))

/-- The rank at a free tile point, by the free class. -/
theorem rho_free_cases {a x y : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hp : TwosTile a (x, y))
    (hF : FreeSite a x y) :
    (x = 1 ∧ y = 0 ∧ rhoTwos a 1 (x, y) = 2 * a + 1) ∨
    (2 ≤ x ∧ x ≤ a ∧ y = x - 2 ∧ rhoTwos a 1 (x, y) = 2 * (a + 1 - x)) ∨
    (x = a + 1 ∧ y = a - 2 ∧ rhoTwos a 1 (x, y) = 1) ∨
    (x = 0 ∧ 0 ≤ y ∧ y < a ∧ rhoTwos a 1 (x, y) = 2 * y - y % 2) ∨
    (x = -1 ∧ a ≤ y ∧ y < 2 * a ∧ rhoTwos a 1 (x, y) = 2 * (y - a) + 1 + (y - a) % 2) := by
  by_cases hH : FreeHSite a x y
  · rw [rhoTwos_tile_freeH ha he2 hp hH]
    unfold FreeHSite at hH
    rcases hH with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2, by rw [freeH_one h1]⟩
    · exact Or.inr (Or.inl ⟨h1, h2, h3, by rw [freeH_mid h1 h2]⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, by rw [freeH_last h1 ha]⟩))
  · have hV : FreeVSite a x y := by
      unfold FreeSite at hF
      rcases hF with h | h
      · exact absurd h hH
      · exact h
    rw [rhoTwos_tile_freeV ha he2 hp hH hV]
    unfold FreeVSite at hV
    rcases hV with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2, h3, by rw [freeV_lo h3]⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2, h3, by rw [freeV_hi h2]⟩)))

end FLatticePaper.TwosEPolicy
