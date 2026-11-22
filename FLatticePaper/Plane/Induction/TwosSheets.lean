import FLatticePaper.Plane.Induction.TwosField
import FLatticePaper.Plane.Induction.SheetSwap

/-! Task 29, scaffolding for the identification of the twos standard field.

The frame of the word `2^m` is explicit for every `m`: the odd parent is `m/(m+1)`, the even parent is `1/1`, the child is
`(2m+1)/(2m+3)` and `eps = -1` (so `W = 0`). Hence the sheet data are fixed: shift `(1,1)`, offset `(-1,1)`, constant `0`,
and the two sheets are

  A(z) = Fp(z - (1,1)),     C(z) = Fp(z - (0,2)) + (z_1 - z_2),

with `Fp = quarterTurnField (standardField (3^(m-1)))` = quarterTurnField (reciprocalField (m-1)) for `m >= 1`. The values
of the reciprocal field are not used here; the piece-wise identification of the minimum with the near-one staircase is the
next step (see the report). -/

namespace FLatticePaper.Induction
open Farey Construction

theorem parentsAt_replicate_two_explicit (m : ℕ) :
    parentsAt (List.replicate m Digit.two) =
      ⟨⟨(m : ℤ), (m : ℤ) + 1⟩, ⟨1, 1⟩⟩ := by
  rw [parentsAt_replicate_two, parentsAt_replicate_three]
  have h1 : (⟨1, 2 * (m : ℤ) + 1⟩ : Fraction).rotate = ⟨(m : ℤ), (m : ℤ) + 1⟩ := by
    unfold Fraction.rotate
    dsimp only
    rw [if_neg (show ¬ ((1 : ℤ) + (2 * (m : ℤ) + 1)) % 2 = 1 by omega)]
    congr 1 <;> omega
  have h2 : (⟨0, 1⟩ : Fraction).rotate = ⟨1, 1⟩ := by
    unfold Fraction.rotate
    dsimp only
    rw [if_pos (show ((0 : ℤ) + 1) % 2 = 1 by norm_num)]
    rfl
  unfold Parents.rotate
  rw [h1, h2]

/-- The frame of `2^m` has `eps = -1` for every `m`: `m * 1 - 1 * (m + 1) = -1`. -/
theorem twos_frame_eps (m : ℕ) : (frameAt (List.replicate m Digit.two)).eps = -1 := by
  show ((parentsAt (List.replicate m Digit.two)).odd).det (parentsAt (List.replicate m Digit.two)).even = -1
  rw [parentsAt_replicate_two_explicit]
  unfold Fraction.det
  ring

theorem twos_frame_phaseW (m : ℕ) : (frameAt (List.replicate m Digit.two)).phaseW = 0 := by
  unfold ChildFrame.phaseW
  rw [twos_frame_eps]
  norm_num

theorem twos_frame_shift (m : ℕ) : (frameAt (List.replicate m Digit.two)).sheetShift = (1, 1) := by
  unfold ChildFrame.sheetShift
  rw [twos_frame_phaseW]
  show (1 - 0 : ℤ) • (parentsAt (List.replicate m Digit.two)).even.unmodifiedDeck.kernel = (1, 1)
  rw [parentsAt_replicate_two_explicit]
  simp [Fraction.unmodifiedDeck]

theorem twos_frame_offset (m : ℕ) : (frameAt (List.replicate m Digit.two)).sheetOffset = (-1, 1) := by
  unfold ChildFrame.sheetOffset
  rw [twos_frame_eps]
  show (parentsAt (List.replicate m Digit.two)).even.unmodifiedDeck.transverse +
      (-1 : ℤ) • (parentsAt (List.replicate m Digit.two)).even.unmodifiedDeck.kernel = (-1, 1)
  rw [parentsAt_replicate_two_explicit]
  simp [Fraction.unmodifiedDeck]

theorem twos_frame_constant (m : ℕ) : (frameAt (List.replicate m Digit.two)).sheetConstant = 0 := by
  unfold ChildFrame.sheetConstant
  rw [twos_frame_phaseW]
  show ((parentsAt (List.replicate m Digit.two)).even.periodDenominator -
      (parentsAt (List.replicate m Digit.two)).even.den - (parentsAt (List.replicate m Digit.two)).even.num) / 2 +
      2 * 0 = 0
  rw [parentsAt_replicate_two_explicit]
  simp [Fraction.periodDenominator]

/-- The sheet `A` of the frame of `2^m` is the quarter-turned field at `z - (1,1)`. -/
theorem twos_sheetA (m : ℕ) (Fp : Field) (z : Site) :
    (frameAt (List.replicate m Digit.two)).sheetA Fp z = Fp (z - (1, 1)) := by
  unfold ChildFrame.sheetA
  rw [twos_frame_shift]

/-- The sheet `C` of the frame of `2^m` is the quarter-turned field at `z - (0,2)` plus the slope `z_1 - z_2`. -/
theorem twos_sheetC (m : ℕ) (Fp : Field) (z : Site) :
    (frameAt (List.replicate m Digit.two)).sheetC Fp z = Fp (z - (0, 2)) + (z.1 - z.2) := by
  unfold ChildFrame.sheetC
  rw [twos_frame_shift, twos_frame_offset, twos_frame_constant]
  have hslope : (frameAt (List.replicate m Digit.two)).siblingSlope (z - (1, 1)) = z.1 - z.2 := by
    unfold ChildFrame.siblingSlope
    show (parentsAt (List.replicate m Digit.two)).even.num * (z - (1, 1)).1 -
        (parentsAt (List.replicate m Digit.two)).even.den * (z - (1, 1)).2 = z.1 - z.2
    rw [parentsAt_replicate_two_explicit]
    simp only [Prod.fst_sub, Prod.snd_sub]
    ring
  rw [hslope]
  have harg : z - (1, 1) - (-1, 1) = z - (0, 2) := by abel
  rw [harg]
  ring

end FLatticePaper.Induction
