import FLatticePaper.Plane.Induction.StandardField
import FLatticePaper.Plane.Induction.Binary
import FLatticePaper.Plane.Induction.Reflection
import FLatticePaper.Plane.Induction.SheetSwap
import FLatticePaper.Plane.Induction.ReciprocalInputs
import FLatticePaper.Plane.AlternateSlip
import FLatticePaper.Plane.QuarterTurn

namespace FLatticePaper.Induction
open Farey Construction

/-- The packet of a standard field at a frame: the coherent periods, the two strips, the central reflection and a
binary Laplacian. -/
structure ChildFrame.Packet (frame : ChildFrame) (F : Field) : Prop where
  periods : HasGeneratorPeriods frame.child F frame.coherentConstantU frame.coherentConstantV
  strips : frame.HasStrips F
  reflection : ∀ z, F (frame.centre - z) = F z - frame.tGrade z + frame.symmetryConstant
  binary : ∀ z, laplacian F z = -1 ∨ laplacian F z = 0

/-- The reciprocal field `B1` at the denominator `2k+3` has its extension constants. -/
theorem reciprocalField_spec (k : ℕ) :
    (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).Agrees (reciprocalField k) 0 ∧
      HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 3)) (reciprocalField k) 0
        (stairEvenConstantV (2 * (k : ℤ) + 3)) := by
  unfold reciprocalField
  exact ⟨(Classical.choose_spec (stairEven_exists_extension (den := 2 * (k : ℤ) + 3)
      (stairEven_valid_reciprocal k))).1,
    (Classical.choose_spec (stairEven_exists_extension (den := 2 * (k : ℤ) + 3)
      (stairEven_valid_reciprocal k))).2.1⟩

/-- The packet at the pure words `3^k`: the reciprocal staircase field on its reciprocal frame. -/
theorem reciprocal_packet (k : ℕ) :
    (frameAt (List.replicate k Digit.three)).Packet (standardField (List.replicate k Digit.three)) := by
  rw [standardField_threes]
  show (reciprocalFrame k).Packet (reciprocalField k)
  obtain ⟨hagree, hper⟩ := reciprocalField_spec k
  have hden : BaseMask.stairEven.Valid (2 * (k : ℤ) + 3) := stairEven_valid_reciprocal k
  obtain ⟨hU, hV⟩ := reciprocal_coherentConstants k
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [reciprocalFrame_child, hU, hV]
    exact hper
  · unfold ChildFrame.HasStrips
    refine ⟨fun z h1 h2 => ?_, fun z h1 h2 => ?_⟩
    · rw [reciprocal_child_den, reciprocal_tGrade] at h1
      rw [reciprocal_child_num, reciprocal_child_den, reciprocal_tGrade] at h2
      exact stairEven_eq_zero_of_transverse hden hagree hper z (by linarith) (by linarith)
    · rw [reciprocal_child_den, reciprocal_sGrade] at h1
      rw [reciprocal_child_num, reciprocal_child_den, reciprocal_sGrade] at h2
      rw [stairEven_eq_harmonic_of_longitudinal hden hagree hper z (by linarith) (by linarith)]
      linarith [four_mul_centeredQuarterTurnCorrection z, harmonicGrid_exact z]
  · intro z
    have hR := stairEven_reflection hden hagree hper z
    rw [reciprocal_centre k, reciprocal_tGrade, reciprocal_symmetryConstant k, hR]
    simp only [Fraction.transverseGrade]
    ring
  · intro z
    exact stairEven_binary_laplacian hden hagree hper z

/-- The conjugate of the odd parent is the even child of the swapped birth word. -/
theorem frameAt_conj_child {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) :
    (frameAt ((oddBirthPrefix word).map Digit.swapTwoThree)).child = (frameAt word).parents.odd.rotate := by
  have hP := parentsAt_odd_eq h
  show (parentsAt ((oddBirthPrefix word).map Digit.swapTwoThree)).current .even =
    (parentsAt word).odd.rotate
  rw [← rotate_parentsAt (oddBirthPrefix word), hP, (parentsAt_valid (oddBirthPrefix word)).rotate_current_odd]

/-- The Laplacian of an affine integer function vanishes, since the two incoming sites sum to twice the site. -/
theorem laplacian_affine (a b c : ℤ) (x : Site) :
    laplacian (fun w : Site => a * w.1 + b * w.2 + c) x = 0 := by
  by_cases h : EvenSite x
  · simp only [laplacian, incomingNeg, incomingPos, if_pos h]
    ring
  · simp only [laplacian, incomingNeg, incomingPos, if_neg h]
    ring

theorem laplacian_add_fn (f g : Field) (x : Site) :
    laplacian (fun w => f w + g w) x = laplacian f x + laplacian g x := by
  unfold laplacian
  ring

theorem evenSite_of_sum (v : Site) (t : ℤ) (h : v.1 + v.2 = 2 * t) : EvenSite v := by
  unfold EvenSite
  omega

/-- The harmonic quarter-turn of a binary field is binary. -/
theorem quarterTurnField_binary {G : Field} (hG : ∀ z, laplacian G z = -1 ∨ laplacian G z = 0) (x : Site) :
    laplacian (quarterTurnField G) x = -1 ∨ laplacian (quarterTurnField G) x = 0 := by
  have hoff : ¬ EvenSite ((0 : ℤ), (-1 : ℤ)) := by
    unfold EvenSite
    norm_num
  have h := laplacian_quarterTurn_add_harmonic QuarterTurn.counterclockwise (0, -1) hoff G harmonicGrid
    (fun y => harmonicGrid_harmonic y) x
  have hq : quarterTurnField G = fun input =>
      G (QuarterTurn.counterclockwise.mapSite (0, -1) input) + harmonicGrid input := rfl
  rw [hq, h]
  exact hG _

/-- The two sheets of a binary conjugate standard are binary. -/
theorem ChildFrame.sheets_binary (frame : ChildFrame) {G : Field}
    (hG : ∀ z, laplacian G z = -1 ∨ laplacian G z = 0) (z : Site) :
    (laplacian (frame.sheetA (quarterTurnField G)) z = -1 ∨ laplacian (frame.sheetA (quarterTurnField G)) z = 0) ∧
    (laplacian (frame.sheetC (quarterTurnField G)) z = -1 ∨ laplacian (frame.sheetC (quarterTurnField G)) z = 0) := by
  obtain ⟨k, hk, -, -, -, -, -, -, hsh, hof⟩ := frame.sheet_facts
  have hbin := quarterTurnField_binary hG
  constructor
  · have hsE : EvenSite (-frame.sheetShift) := by
      refine evenSite_of_sum _ (-((1 - frame.phaseW) * k)) ?_
      rw [hsh]
      simp only [Prod.fst_neg, Prod.snd_neg]
      linear_combination (-(1 - frame.phaseW)) * hk
    have hfun : frame.sheetA (quarterTurnField G) = fun w => quarterTurnField G (w + -frame.sheetShift) := by
      funext w
      unfold ChildFrame.sheetA
      rw [sub_eq_add_neg]
    rw [hfun, laplacian_translate_of_even (quarterTurnField G) z (-frame.sheetShift) hsE]
    exact hbin _
  · have hsE : EvenSite (-(frame.sheetShift + frame.sheetOffset)) := by
      refine evenSite_of_sum _ (-(frame.phaseW * k + frame.parents.even.num)) ?_
      rw [hsh, hof]
      simp only [Prod.fst_neg, Prod.snd_neg, Prod.fst_add, Prod.snd_add]
      linear_combination (-frame.phaseW) * hk
    have hsplit : frame.sheetC (quarterTurnField G) = fun w =>
        quarterTurnField G (w - frame.sheetShift - frame.sheetOffset) +
          (frame.siblingSlope (w - frame.sheetShift) + frame.sheetConstant) := by
      funext w
      unfold ChildFrame.sheetC
      ring
    have hlin : (fun w : Site => frame.siblingSlope (w - frame.sheetShift) + frame.sheetConstant) =
        fun w => frame.parents.even.num * w.1 + (-frame.parents.even.den) * w.2 +
          (frame.sheetConstant - frame.parents.even.num * frame.sheetShift.1 +
            frame.parents.even.den * frame.sheetShift.2) := by
      funext w
      unfold ChildFrame.siblingSlope
      simp only [Prod.fst_sub, Prod.snd_sub]
      ring
    have hfun : (fun w : Site => quarterTurnField G (w - frame.sheetShift - frame.sheetOffset)) =
        fun w => quarterTurnField G (w + -(frame.sheetShift + frame.sheetOffset)) := by
      funext w
      congr 1
      abel
    have htr : laplacian (fun w : Site => quarterTurnField G (w - frame.sheetShift - frame.sheetOffset)) z =
        laplacian (quarterTurnField G) (z + -(frame.sheetShift + frame.sheetOffset)) := by
      rw [hfun]
      exact laplacian_translate_of_even (quarterTurnField G) z _ hsE
    have haff : laplacian (fun w : Site => frame.siblingSlope (w - frame.sheetShift) + frame.sheetConstant) z = 0 := by
      rw [hlin]
      exact laplacian_affine _ _ _ z
    have hadd : laplacian (frame.sheetC (quarterTurnField G)) z =
        laplacian (fun w : Site => quarterTurnField G (w - frame.sheetShift - frame.sheetOffset)) z +
          laplacian (fun w : Site => frame.siblingSlope (w - frame.sheetShift) + frame.sheetConstant) z := by
      rw [hsplit]
      exact laplacian_add_fn _ _ z
    rw [hadd, htr, haff, add_zero]
    exact hbin _

end FLatticePaper.Induction
