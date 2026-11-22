import FLatticePaper.Plane.Induction.TwosPacket
import FLatticePaper.Plane.Induction.Potentials
import FLatticePaper.Construction.LadderRotation
import FLatticePaper.Construction.LadderLaplacian
import FLatticePaper.Construction.LadderReflection
import FLatticePaper.Construction.QuarterTurnCorrection
import FLatticePaper.Plane.QuarterTurn

/-! # The near-one ladder of `2^(k+1)` from its odd-ladder source (task 39)

The physical near-one field of the child `R(1/d)`, `d = 2k+4`, is the rotation `rotateLadderField d S` of an odd
ladder field `S` with the periods of `1/d` (`LadderRotation`). For this field:

* binarity holds on the whole plane, by the quarter-turn Laplacian identity and `ladderOdd_binary_laplacian`;
* the reflection about the centre `(d, 3d-2)` of the frame of `2^(k+1)` holds on the whole plane, with the symmetry
  constant `1 - d^2 - d`, by the reflection of `S` (`ladderOddField_reflection`) and the quarter-turn identity for the
  correction (checked on `d = 4, .., 12` before the proof);
* the periods are `(0, ladderEvenConstantV d)` (`rotateLadderField_periods`).

The two zero and harmonic strip facts on the closed polygon are not proved here; they are the hypotheses `hzero`,
`hharm` of `twos_packet_of_source`. -/

namespace FLatticePaper.Induction
open Farey Construction

/-- The counterclockwise quarter turn of the offset `(2d, 1)`. -/
theorem quarterTurn_offset_apply (den : ℤ) (point : Site) :
    QuarterTurn.counterclockwise.mapSite (2 * den, 1) point = (2 * den - point.2, point.1 + 1) := by
  apply Prod.ext
  · change -point.2 + 2 * den = 2 * den - point.2
    omega
  · rfl

/-- The Laplacian of the rotated field is the Laplacian of the source at the rotated point. -/
theorem rotateLadderField_laplacian (den : ℤ) (field : Field) (point : Site) :
    laplacian (rotateLadderField den field) point =
      laplacian field (QuarterTurn.counterclockwise.mapSite (2 * den, 1) point) := by
  have hoff : ¬ EvenSite ((2 * den, 1) : Site) := by
    unfold EvenSite
    dsimp only
    omega
  exact laplacian_quarterTurn_add_harmonic QuarterTurn.counterclockwise (2 * den, 1) hoff field
    centeredQuarterTurnCorrection harmonic_centeredQuarterTurnCorrection point

/-- The rotated odd-ladder field is binary on the whole plane. -/
theorem rotateLadderField_binary {den : ℤ} (hden : BaseMask.ladderOdd.Valid den) {field : Field}
    (hagree : (BaseMask.ladderOdd.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den)) (point : Site) :
    laplacian (rotateLadderField den field) point = -1 ∨ laplacian (rotateLadderField den field) point = 0 := by
  rw [rotateLadderField_laplacian]
  exact ladderOdd_binary_laplacian hden hagree hperiod _

/-- The reflection of the rotated odd-ladder field about `(d, 3d-2)`, with symmetry constant `1 - d^2 - d`, on the whole
plane. -/
theorem rotateLadderField_reflection {den : ℤ} (hden : BaseMask.ladderOdd.Valid den) {field : Field}
    (hagree : (BaseMask.ladderOdd.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den)) (point : Site) :
    rotateLadderField den field ((den, 3 * den - 2) - point) =
      rotateLadderField den field point - ((den - 1) * point.1 - (den + 1) * point.2) + (1 - den ^ 2 - den) := by
  have hpull : QuarterTurn.counterclockwise.mapSite (2 * den, 1) ((den, 3 * den - 2) - point) =
      reflectLadderOdd den (QuarterTurn.counterclockwise.mapSite (2 * den, 1) point) := by
    rw [quarterTurn_offset_apply, quarterTurn_offset_apply]
    simp only [reflectLadderOdd, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub]
    omega
  have hS := ladderOddField_reflection hden hagree hperiod (QuarterTurn.counterclockwise.mapSite (2 * den, 1) point)
  have h1 := four_mul_centeredQuarterTurnCorrection ((den, 3 * den - 2) - point)
  have h2 := four_mul_centeredQuarterTurnCorrection point
  have hmod : (((den, 3 * den - 2) - point).1 + ((den, 3 * den - 2) - point).2) % 2 =
      (point.1 + point.2) % 2 := by
    simp only [Prod.fst_sub, Prod.snd_sub]
    omega
  have htwo := two_mul_chooseTwo (den + 1)
  unfold rotateLadderField
  rw [hpull, hS]
  have key : 4 * (centeredQuarterTurnCorrection ((den, 3 * den - 2) - point) - centeredQuarterTurnCorrection point) =
      4 * (-((den - 1) * point.1 - (den + 1) * point.2) + (1 - den ^ 2 - den) -
        (den * (QuarterTurn.counterclockwise.mapSite (2 * den, 1) point).2 -
          (QuarterTurn.counterclockwise.mapSite (2 * den, 1) point).1) - (1 - chooseTwo (den + 1))) := by
    rw [quarterTurn_offset_apply]
    simp only [Prod.fst_sub, Prod.snd_sub] at h1 h2 hmod ⊢
    linear_combination h1 - h2 - hmod - 2 * htwo
  have hcorr := mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) key
  simp only [Fraction.transverseGrade, quarterTurn_offset_apply] at hcorr ⊢
  linear_combination hcorr

/-- The centre of the frame of `2^(k+1)` is `(d, 3d-2)` with `d = 2k+4`. -/
theorem twos_centre (k : ℕ) :
    (frameAt (List.replicate (k + 1) Digit.two)).centre = (2 * (k : ℤ) + 4, 3 * (2 * (k : ℤ) + 4) - 2) := by
  unfold ChildFrame.centre
  rw [ChildFrame.child_modifiedDeck_kernel, ChildFrame.child_modifiedDeck_transverse, twos_child_eq k]
  apply Prod.ext
  · simp only [Prod.fst_add]
    ring
  · simp only [Prod.snd_add]
    ring

/-- The transverse grade of the frame of `2^(k+1)`. -/
theorem twos_tGrade (k : ℕ) (z : Site) :
    (frameAt (List.replicate (k + 1) Digit.two)).tGrade z = (2 * (k : ℤ) + 3) * z.1 - (2 * (k : ℤ) + 5) * z.2 := by
  unfold ChildFrame.tGrade
  rw [twos_child_eq k]

/-- The symmetry constant of the frame of `2^(k+1)` is `1 - d^2 - d` with `d = 2k+4`. -/
theorem twos_symmetryConstant (k : ℕ) :
    (frameAt (List.replicate (k + 1) Digit.two)).symmetryConstant = 1 - (2 * (k : ℤ) + 4) ^ 2 - (2 * (k : ℤ) + 4) := by
  have hT : (frameAt (List.replicate (k + 1) Digit.two)).child.periodDenominator =
      8 * (k : ℤ) ^ 2 + 40 * (k : ℤ) + 46 := by
    rw [twos_child_eq k]
    unfold Fraction.periodDenominator
    dsimp only
    ring
  unfold ChildFrame.symmetryConstant
  rw [hT, twos_child_eq k]
  dsimp only
  rw [show (2 * (k : ℤ) + 5) + (2 * (k : ℤ) + 3) - (8 * (k : ℤ) ^ 2 + 40 * (k : ℤ) + 46) =
      2 * (1 - (2 * (k : ℤ) + 4) ^ 2 - (2 * (k : ℤ) + 4)) by ring]
  exact Int.mul_ediv_cancel_left _ (by norm_num)

/-- The periods of the physical near-one field `rotateLadderField d S` on the child of `2^(k+1)`: the constants
`(0, ladderEvenConstantV d)`, `d = 2k+4`. -/
theorem twos_physical_periods (k : ℕ) {S : Field}
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4))) :
    HasGeneratorPeriods (frameAt (List.replicate (k + 1) Digit.two)).child (rotateLadderField (2 * (k : ℤ) + 4) S)
      0 (ladderEvenConstantV (2 * (k : ℤ) + 4)) := by
  rw [child_replicate_two_succ]
  exact rotateLadderField_periods (by omega) hperiod

/-- The packet of the standard field of `2^(k+1)`, when that field is the rotated odd-ladder field of a source `S` with
the periods of `1/d` (`d = 2k+4`), with the zero and harmonic strip facts on its closed polygon as hypotheses. The
binarity and the reflection of the rotated field are proved here on the whole plane. -/
theorem twos_packet_of_source (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    (hid : standardField (List.replicate (k + 1) Digit.two) = rotateLadderField (2 * (k : ℤ) + 4) S)
    (hzero : ∀ z ∈ (frameAt (List.replicate (k + 1) Digit.two)).closedPolygon,
      1 - (frameAt (List.replicate (k + 1) Digit.two)).child.den ≤
        (frameAt (List.replicate (k + 1) Digit.two)).tGrade z →
      rotateLadderField (2 * (k : ℤ) + 4) S z = 0)
    (hharm : ∀ z ∈ (frameAt (List.replicate (k + 1) Digit.two)).closedPolygon,
      (frameAt (List.replicate (k + 1) Digit.two)).sGrade z ≤
        2 * ((frameAt (List.replicate (k + 1) Digit.two)).child.den +
          (frameAt (List.replicate (k + 1) Digit.two)).child.num) - 1 →
      rotateLadderField (2 * (k : ℤ) + 4) S z = harmonicGrid z) :
    (frameAt (List.replicate (k + 1) Digit.two)).Packet (standardField (List.replicate (k + 1) Digit.two)) := by
  have hden : BaseMask.ladderOdd.Valid (2 * (k : ℤ) + 4) := ⟨by omega, by omega⟩
  have heven : (2 * (k : ℤ) + 4) % 2 = 0 := by omega
  rw [hid]
  refine (frameAt (List.replicate (k + 1) Digit.two)).packet_of_stripInputs ?_ ?_
    (fun z _ => rotateLadderField_binary hden hagree hperiod z)
  · rw [(twos_coherentConstants k).1, (twos_coherentConstants k).2]
    exact twos_physical_periods k hperiod
  · exact ⟨hzero, hharm, fun z _ => by
      have h := rotateLadderField_reflection hden hagree hperiod z
      rw [twos_centre k, twos_tGrade k, twos_symmetryConstant k]
      rw [show (2 * (k : ℤ) + 4 - 1) = 2 * (k : ℤ) + 3 by ring,
        show (2 * (k : ℤ) + 4 + 1) = 2 * (k : ℤ) + 5 by ring] at h
      exact h⟩

end FLatticePaper.Induction
