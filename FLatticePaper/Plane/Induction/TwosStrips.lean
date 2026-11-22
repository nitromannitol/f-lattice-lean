import FLatticePaper.Plane.Induction.TwosSheets
import FLatticePaper.Plane.Induction.Packet
import FLatticePaper.Plane.Induction.WordInduction

/-! Task 30, the strip pieces of min(A, C) on E for the twos words.

The reciprocal field `G = reciprocalField k = standardField (3^k)` (child `1/(2k+3)`) vanishes on its transverse zone
`1 - d <= y_1 - d y_2 <= 2d` and equals `harmonicGrid` on its longitudinal zone `1 - 2d <= (d+1) y_1 + (d-1) y_2 <= 2d+1`
(the strips of the reciprocal packet, `d = 2k+3`). The sheets of `2^(k+1)` read `G` at `Z(z - (1,1))` and `Z(z - (0,2))`,
`Z(x) = (-x_2, x_1 - 1)`. Where those points lie in a strip, the sheets are explicit harmonic expressions, with no tile
values. The pieces where both points are in strips are closed here; the tile pieces need the tile values and the deck
reduction (see the report). -/

namespace FLatticePaper.Induction
open Farey Construction

theorem child_threes_explicit (k : ℕ) :
    (frameAt (List.replicate k Digit.three)).child = ⟨1, 2 * (k : ℤ) + 3⟩ :=
  (baseChildren_threes k).1

/-- The reciprocal field vanishes on its transverse zone `1 - d <= y_1 - d y_2 <= 2d`, `d = 2k+3`. -/
theorem reciprocal_zero_zone (k : ℕ) (y : Site)
    (h1 : 1 - (2 * (k : ℤ) + 3) ≤ y.1 - (2 * (k : ℤ) + 3) * y.2)
    (h2 : y.1 - (2 * (k : ℤ) + 3) * y.2 ≤ 2 * (2 * (k : ℤ) + 3)) :
    standardField (List.replicate k Digit.three) y = 0 := by
  have hS := (reciprocal_packet k).strips.1 y
  have ht : (frameAt (List.replicate k Digit.three)).tGrade y = y.1 - (2 * (k : ℤ) + 3) * y.2 := by
    unfold ChildFrame.tGrade
    rw [child_threes_explicit k]
    simp only
    ring
  have hd : (frameAt (List.replicate k Digit.three)).child.den = 2 * (k : ℤ) + 3 := by
    rw [child_threes_explicit k]
  have hn : (frameAt (List.replicate k Digit.three)).child.num = 1 := by
    rw [child_threes_explicit k]
  apply hS
  · rw [ht, hd]
    linarith
  · rw [ht, hd, hn]
    linarith

/-- The reciprocal field equals the harmonic grid on its longitudinal zone `1 - 2d <= (d+1) y_1 + (d-1) y_2 <= 2d+1`. -/
theorem reciprocal_harm_zone (k : ℕ) (y : Site)
    (h1 : 1 - 2 * (2 * (k : ℤ) + 3) ≤ (2 * (k : ℤ) + 4) * y.1 + (2 * (k : ℤ) + 2) * y.2)
    (h2 : (2 * (k : ℤ) + 4) * y.1 + (2 * (k : ℤ) + 2) * y.2 ≤ 2 * (2 * (k : ℤ) + 3) + 1) :
    standardField (List.replicate k Digit.three) y = harmonicGrid y := by
  have hS := (reciprocal_packet k).strips.2 y
  have hd : (frameAt (List.replicate k Digit.three)).child.den = 2 * (k : ℤ) + 3 := by
    rw [child_threes_explicit k]
  have hn : (frameAt (List.replicate k Digit.three)).child.num = 1 := by
    rw [child_threes_explicit k]
  have hs : (frameAt (List.replicate k Digit.three)).sGrade y =
      (2 * (k : ℤ) + 4) * y.1 + (2 * (k : ℤ) + 2) * y.2 := by
    unfold ChildFrame.sGrade
    rw [hd, hn]
    ring
  apply hS
  · rw [hs, hd]
    linarith
  · rw [hs, hd, hn]
    linarith

theorem quarterTurn_reciprocal_zero (k : ℕ) (x : Site)
    (h1 : 1 - (2 * (k : ℤ) + 3) ≤ (-x.2) - (2 * (k : ℤ) + 3) * (x.1 - 1))
    (h2 : (-x.2) - (2 * (k : ℤ) + 3) * (x.1 - 1) ≤ 2 * (2 * (k : ℤ) + 3)) :
    quarterTurnField (reciprocalField k) x = harmonicGrid x := by
  rw [quarterTurnField_eq, ← standardField_threes]
  show standardField (List.replicate k Digit.three) (-x.2, x.1 - 1) + harmonicGrid x = harmonicGrid x
  rw [reciprocal_zero_zone k (-x.2, x.1 - 1) h1 h2]
  ring

theorem quarterTurn_reciprocal_harm (k : ℕ) (x : Site)
    (h1 : 1 - 2 * (2 * (k : ℤ) + 3) ≤ (2 * (k : ℤ) + 4) * (-x.2) + (2 * (k : ℤ) + 2) * (x.1 - 1))
    (h2 : (2 * (k : ℤ) + 4) * (-x.2) + (2 * (k : ℤ) + 2) * (x.1 - 1) ≤ 2 * (2 * (k : ℤ) + 3) + 1) :
    quarterTurnField (reciprocalField k) x = harmonicGrid (-x.2, x.1 - 1) + harmonicGrid x := by
  rw [quarterTurnField_eq, ← standardField_threes]
  show standardField (List.replicate k Digit.three) (-x.2, x.1 - 1) + harmonicGrid x =
    harmonicGrid (-x.2, x.1 - 1) + harmonicGrid x
  rw [reciprocal_harm_zone k (-x.2, x.1 - 1) h1 h2]

/-- Sheet `A` of `2^(k+1)` at a site whose quarter-turned argument is in the transverse zone of the reciprocal field. -/
theorem twos_sheetA_zero (k : ℕ) (z : Site)
    (h1 : 1 - (2 * (k : ℤ) + 3) ≤ (-(z.2 - 1)) - (2 * (k : ℤ) + 3) * ((z.1 - 1) - 1))
    (h2 : (-(z.2 - 1)) - (2 * (k : ℤ) + 3) * ((z.1 - 1) - 1) ≤ 2 * (2 * (k : ℤ) + 3)) :
    (frameAt (List.replicate (k + 1) Digit.two)).sheetA
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two)))) z =
      harmonicGrid (z - (1, 1)) := by
  rw [twos_sheetA, show conjWord (List.replicate (k + 1) Digit.two) = List.replicate k Digit.three from
    conjWord_replicate_two k, standardField_threes]
  exact quarterTurn_reciprocal_zero k (z - (1, 1)) (by simpa using h1) (by simpa using h2)

/-- Sheet `C` of `2^(k+1)` at a site whose quarter-turned argument `Z(z - (0,2))` is in the transverse zone. -/
theorem twos_sheetC_zero (k : ℕ) (z : Site)
    (h1 : 1 - (2 * (k : ℤ) + 3) ≤ (-(z.2 - 2)) - (2 * (k : ℤ) + 3) * (z.1 - 1))
    (h2 : (-(z.2 - 2)) - (2 * (k : ℤ) + 3) * (z.1 - 1) ≤ 2 * (2 * (k : ℤ) + 3)) :
    (frameAt (List.replicate (k + 1) Digit.two)).sheetC
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two)))) z =
      harmonicGrid (z - (0, 2)) + (z.1 - z.2) := by
  rw [twos_sheetC, show conjWord (List.replicate (k + 1) Digit.two) = List.replicate k Digit.three from
    conjWord_replicate_two k, standardField_threes]
  have hq := quarterTurn_reciprocal_zero k (z - (0, 2)) (by simpa using h1) (by simpa using h2)
  rw [hq]

end FLatticePaper.Induction
