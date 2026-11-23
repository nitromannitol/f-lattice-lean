import FLatticePaper.Plane.Induction.W1OfferTwo
import FLatticePaper.Plane.Induction.W1OddZero
import FLatticePaper.Plane.Induction.W1OddSeedZero
import FLatticePaper.Plane.Induction.W1OddSeedY
import FLatticePaper.Plane.Induction.TieReduce

/-! # Task 75 (odd_zero): `SeedFields.odd_zero` at a proper word, from the conjugate's even seed

For a proper word `w` with conjugate `conjWord w`, the odd-zero claim of `SeedFields w` (the quarter turn of `standardField w` vanishes on the
even line `parentN x₁ − parentD x₂ = 1 − d`) follows from:
* the seed value `quarterTurnField (standardField w) (oddSeedPoint) = 0`, which is `seed_zero_of_offers` with the two offers at `Y`
  (`offer_one_sheetA_pos`/`offer_one_sheetC_neg` and `offer_two_sheetC_pos`/`offer_two_sheetA_neg`; the second needs the even seed
  `hseed` of `conjWord w`);
* the seed lies on the line and is even (the certificates `±2` of the parent relation);
* `odd_zero_of_seed`, the whole line is one orbit. -/

namespace FLatticePaper.W1OddZeroWord

open Farey FLatticePaper FLatticePaper.Induction

/-- The seed point and its `Z`-image plus the kernel is the odd-seed image `Y`. -/
theorem Zseed_add_kernel_eq (frame : ChildFrame) :
    (-(W1OddSeedY.oddSeedPoint frame).2, (W1OddSeedY.oddSeedPoint frame).1 - 1) +
        frame.child.modifiedDeck.kernel = W1OddSeedY.oddSeedY frame := by
  unfold W1OddSeedY.oddSeedY
  rw [ChildFrame.child_modifiedDeck_kernel]
  rfl

/-- The seed is even and on the odd line of `w`, for `ε = +1`. -/
theorem seed_even_line_pos {w : Word} (hε : (frameAt w).eps = 1) :
    EvenSite (W1OddSeedY.oddSeedPoint (frameAt w)) ∧
      parentN w * (W1OddSeedY.oddSeedPoint (frameAt w)).1 - parentD w * (W1OddSeedY.oddSeedPoint (frameAt w)).2 =
        1 - (parentD w + parentN w) := by
  have hcn := (frameAt w).child_num_eq
  have hcd := (frameAt w).child_den_eq
  have hev : ((frameAt w).child.num + (frameAt w).child.den) % 2 = 0 := (frameAt w).child_even
  have hpe := ZoneI1.eps_eq (frameAt w)
  rw [hε] at hpe
  have hrel : (frameAt w).parents.odd.num * (frameAt w).parents.even.den -
      (frameAt w).parents.odd.den * (frameAt w).parents.even.num = 1 := by
    linear_combination (-1 : ℤ) * hpe
  have hz1 : (W1OddSeedY.oddSeedPoint (frameAt w)).1 =
      (frameAt w).parents.odd.den + (frameAt w).parents.odd.num - 1 := by
    unfold W1OddSeedY.oddSeedPoint
    rw [FLatticePaper.W1Seeds.phaseW_pos (frameAt w) hε]
    ring
  have hz2 : (W1OddSeedY.oddSeedPoint (frameAt w)).2 =
      (frameAt w).parents.odd.den - (frameAt w).parents.odd.num + 1 := by
    unfold W1OddSeedY.oddSeedPoint
    rw [FLatticePaper.W1Seeds.phaseW_pos (frameAt w) hε]
    ring
  have h2N : 2 * parentN w = (2 * (frameAt w).parents.odd.den + (frameAt w).parents.even.den) -
      (2 * (frameAt w).parents.odd.num + (frameAt w).parents.even.num) := by
    unfold parentN
    omega
  have h2D : 2 * parentD w = (2 * (frameAt w).parents.odd.den + (frameAt w).parents.even.den) +
      (2 * (frameAt w).parents.odd.num + (frameAt w).parents.even.num) := by
    unfold parentD
    omega
  refine ⟨?_, ?_⟩
  · unfold EvenSite
    rw [hz1, hz2]
    omega
  · have key : 2 * (parentN w * (W1OddSeedY.oddSeedPoint (frameAt w)).1 -
        parentD w * (W1OddSeedY.oddSeedPoint (frameAt w)).2) =
        2 * (1 - (parentD w + parentN w)) := by
      rw [hz1, hz2]
      linear_combination ((frameAt w).parents.odd.den + (frameAt w).parents.odd.num - 1) * h2N -
        ((frameAt w).parents.odd.den - (frameAt w).parents.odd.num + 1) * h2D + h2N + h2D + 2 * hrel
    exact mul_left_cancel₀ two_ne_zero key

/-- The seed is even and on the odd line of `w`, for `ε = −1`. -/
theorem seed_even_line_neg {w : Word} (hε : (frameAt w).eps = -1) :
    EvenSite (W1OddSeedY.oddSeedPoint (frameAt w)) ∧
      parentN w * (W1OddSeedY.oddSeedPoint (frameAt w)).1 - parentD w * (W1OddSeedY.oddSeedPoint (frameAt w)).2 =
        1 - (parentD w + parentN w) := by
  have hcn := (frameAt w).child_num_eq
  have hcd := (frameAt w).child_den_eq
  have hev : ((frameAt w).child.num + (frameAt w).child.den) % 2 = 0 := (frameAt w).child_even
  have hpe := ZoneI1.eps_eq (frameAt w)
  rw [hε] at hpe
  have hrel : (frameAt w).parents.odd.num * (frameAt w).parents.even.den -
      (frameAt w).parents.odd.den * (frameAt w).parents.even.num = -1 := by
    linear_combination (-1 : ℤ) * hpe
  have hz1 : (W1OddSeedY.oddSeedPoint (frameAt w)).1 =
      (frameAt w).parents.odd.den + (frameAt w).parents.odd.num - 1 + ((frameAt w).parents.even.den +
        (frameAt w).parents.even.num) := by
    unfold W1OddSeedY.oddSeedPoint
    rw [FLatticePaper.W1Seeds.phaseW_neg (frameAt w) hε]
    ring
  have hz2 : (W1OddSeedY.oddSeedPoint (frameAt w)).2 =
      (frameAt w).parents.odd.den - (frameAt w).parents.odd.num + 1 + ((frameAt w).parents.even.den -
        (frameAt w).parents.even.num) := by
    unfold W1OddSeedY.oddSeedPoint
    rw [FLatticePaper.W1Seeds.phaseW_neg (frameAt w) hε]
    ring
  have h2N : 2 * parentN w = (2 * (frameAt w).parents.odd.den + (frameAt w).parents.even.den) -
      (2 * (frameAt w).parents.odd.num + (frameAt w).parents.even.num) := by
    unfold parentN
    omega
  have h2D : 2 * parentD w = (2 * (frameAt w).parents.odd.den + (frameAt w).parents.even.den) +
      (2 * (frameAt w).parents.odd.num + (frameAt w).parents.even.num) := by
    unfold parentD
    omega
  refine ⟨?_, ?_⟩
  · unfold EvenSite
    rw [hz1, hz2]
    omega
  · have key : 2 * (parentN w * (W1OddSeedY.oddSeedPoint (frameAt w)).1 -
        parentD w * (W1OddSeedY.oddSeedPoint (frameAt w)).2) =
        2 * (1 - (parentD w + parentN w)) := by
      rw [hz1, hz2]
      linear_combination ((frameAt w).parents.odd.den + (frameAt w).parents.odd.num - 1 +
          ((frameAt w).parents.even.den + (frameAt w).parents.even.num)) * h2N -
        ((frameAt w).parents.odd.den - (frameAt w).parents.odd.num + 1 +
          ((frameAt w).parents.even.den - (frameAt w).parents.even.num)) * h2D + h2N + h2D - 2 * hrel
    exact mul_left_cancel₀ two_ne_zero key

/-- **`SeedFields.odd_zero` at a proper word** (task 75): the quarter turn of `standardField w` vanishes on the even line
`parentN x₁ − parentD x₂ = 1 − d`, from the conjugate's even seed `hseed` (the induction hypothesis). -/
theorem odd_zero_at_word {w : Word} (h : ∃ x ∈ w, x ≠ Digit.three) (hS : StrongEstimates (conjWord w))
    (hseed : ∀ z : Site, EvenSite z →
      (frameAt (conjWord w)).tGrade z = 2 - ((frameAt (conjWord w)).child.den + (frameAt (conjWord w)).child.num) →
        standardField (conjWord w) z = 0)
    (x : Site) (hx : EvenSite x)
    (hxl : parentN w * x.1 - parentD w * x.2 = 1 - (parentD w + parentN w)) :
    quarterTurnField (standardField w) x = 0 := by
  have hpk : (frameAt w).Packet (standardField w) := packet_of_strong h hS
  have hYe := Zseed_add_kernel_eq (frameAt w)
  have hYmem : (-(W1OddSeedY.oddSeedPoint (frameAt w)).2, (W1OddSeedY.oddSeedPoint (frameAt w)).1 - 1) +
      (frameAt w).child.modifiedDeck.kernel ∈ (frameAt w).closedPolygon := by
    rw [hYe]
    exact W1OddSeedY.oddSeed_Y_mem (frameAt w)
  have hz0 : quarterTurnField (standardField w) (W1OddSeedY.oddSeedPoint (frameAt w)) = 0 := by
    rcases (frameAt w).eps_unit with hε | hε
    · exact W1OddSeedZero.seed_zero_of_offers h hS _ hYmem
        (by rw [hYe]; exact FLatticePaper.W1OfferOne.offer_one_sheetA_pos h hS hε)
        (by rw [hYe]; exact FLatticePaper.W1OfferTwo.offer_two_sheetC_pos h hS hε hseed)
    · exact W1OddSeedZero.seed_zero_of_offers h hS _ hYmem
        (by rw [hYe]; exact FLatticePaper.W1OfferTwo.offer_two_sheetA_neg h hS hε hseed)
        (by rw [hYe]; exact FLatticePaper.W1OfferOne.offer_one_sheetC_neg h hS hε)
  have hline : EvenSite (W1OddSeedY.oddSeedPoint (frameAt w)) ∧
      parentN w * (W1OddSeedY.oddSeedPoint (frameAt w)).1 - parentD w * (W1OddSeedY.oddSeedPoint (frameAt w)).2 =
        1 - (parentD w + parentN w) := by
    rcases (frameAt w).eps_unit with hε | hε
    · exact seed_even_line_pos hε
    · exact seed_even_line_neg hε
  exact W1OddZero.odd_zero_of_seed w hpk _ x hline.1 hline.2 hx hxl hz0

end FLatticePaper.W1OddZeroWord
