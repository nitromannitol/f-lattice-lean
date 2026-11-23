import FLatticePaper.Plane.Induction.Q3Bound
import FLatticePaper.Plane.Induction.SheetFacts

/-! Task 59, paragraph 5: the hypotheses of `price_floor_bound` discharged from the strong estimates of the conjugate word.

For a word that is not all threes, with `u = conjWord word`:
* `hconj : (frameAt u).child = (frameAt word).parents.odd.rotate` (`frameAt_conj_child`);
* `hR`, `hD` are the price range and the price drift of `StrongEstimates u` (`priceRange`, `priceDrift`);
* `hN1 : 1 ≤ N`, `hND : N + 1 ≤ D` follow from `frameAt_odd_num_pos` and the odd parity `N + D` (as in `parentStepSign_of_strong`).
So `price_floor_bound_of_strong`, `p_shift_bound_of_strong` and `paragraph5_field_identity_of_strong` need only the
strong estimates of `conjWord word` and the non-cube hypothesis. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

theorem price_floor_bound_of_strong {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (x : Site) :
    -parentFloor (frameAt word) x - 1 ≤
        (frameAt (conjWord word)).price (standardField (conjWord word)) (-x.2, x.1 - 1) -
          (frameAt (conjWord word)).cutPrice ∧
      (frameAt (conjWord word)).price (standardField (conjWord word)) (-x.2, x.1 - 1) -
          (frameAt (conjWord word)).cutPrice ≤ -parentFloor (frameAt word) x := by
  have hN := frameAt_odd_num_pos h
  obtain ⟨-, -, hNle⟩ := (frameAt word).valid.odd_bounds
  have hodd : ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den) % 2 = 1 :=
    (frameAt word).valid.odd_parity
  exact price_floor_bound (frame := frameAt word) (conj := frameAt (conjWord word))
    (G := standardField (conjWord word)) (frameAt_conj_child h) hSE.priceRange hSE.priceDrift
    (by omega) (by omega) x

theorem p_shift_bound_of_strong {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (x : Site) :
    (frameAt (conjWord word)).cutPrice -
        (frameAt (conjWord word)).price (standardField (conjWord word)) (-x.2, x.1 - 1) - 1 ≤
      (frameAt (conjWord word)).cutPrice -
        (frameAt (conjWord word)).price (standardField (conjWord word))
          (-(x - (frameAt word).sheetStep).2, (x - (frameAt word).sheetStep).1 - 1) := by
  have hN := frameAt_odd_num_pos h
  obtain ⟨-, -, hNle⟩ := (frameAt word).valid.odd_bounds
  have hodd : ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den) % 2 = 1 :=
    (frameAt word).valid.odd_parity
  exact ChildFrame.p_shift_bound (frameAt word) (frameAt_conj_child h) hSE.priceRange hSE.priceDrift
    (by omega) (by omega) x

theorem paragraph5_field_identity_of_strong {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (x : Site) :
    quarterTurnField (standardField (conjWord word))
        (x + (-(frameAt word).eps * (frameAt word).parents.even.den,
          -(frameAt word).eps * (frameAt word).parents.even.num)) -
      quarterTurnField (standardField (conjWord word)) x =
        (frameAt (conjWord word)).cutPrice -
          (frameAt (conjWord word)).price (standardField (conjWord word)) (-x.2, x.1 - 1) :=
  paragraph5_field_identity_proved (frame := frameAt word) (conj := frameAt (conjWord word))
    (G := standardField (conjWord word)) (frameAt_conj_child h) hSE.packet.periods x

end FLatticePaper.Induction
