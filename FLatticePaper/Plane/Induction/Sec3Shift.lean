import FLatticePaper.Plane.Induction.SheetOffsets
import FLatticePaper.Plane.Induction.HarmWrap
import FLatticePaper.Plane.Induction.VArcLongitudinal
import FLatticePaper.Plane.Induction.Reflection
import FLatticePaper.Plane.Induction.StrongEstimates
import FLatticePaper.Plane.Induction.StrongCoreDef

/-! §3 of the canonical V raw-slip monotonicity note: the shifted offers, in the note's convention.

The shift is `X = U_p` at ε = +1 (W1) and `X = U_q` at ε = −1 (W0), with `U_p = Upar = (2D, 2N)` and `U_q` the even parent's kernel. Proved: `F(z + σ) = F(z + X)` for the word's standard field with `σ = shortShift = ε U_p`, from the kernel period (`U_p + U_q` is the child kernel and its constant is `0`); `t(X) = −2`; and `A(z + X) = F_p(z)`. -/

namespace FLatticePaper.Sec3Shift

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1MSheet

/-- The shift `X` of §3 (note convention): `U_p` at ε = +1, `U_q` at ε = −1. -/
noncomputable def sec3X (word : Word) : Site :=
  if (frameAt word).eps = 1 then Upar word else (frameAt word).parents.even.unmodifiedDeck.kernel

theorem child_kernel_eq (word : Word) :
    (frameAt word).child.modifiedDeck.kernel =
      Upar word + (frameAt word).parents.even.unmodifiedDeck.kernel := by
  have hd := ChildFrame.child_den_eq (frameAt word)
  have hn := ChildFrame.child_num_eq (frameAt word)
  rw [ChildFrame.kernel_coords (frameAt word)]
  unfold Upar Fraction.unmodifiedDeck
  ext
  · simp only [Prod.fst_add]
    linarith
  · simp only [Prod.snd_add]
    linarith

theorem kernel_period {word : Word} (hW : StrongCore word) (z : Site) :
    standardField word (z + (frameAt word).child.modifiedDeck.kernel) = standardField word z := by
  have h := hW.packet.periods.1 z
  rw [ChildFrame.coherentConstantU_eq_zero (frameAt word)] at h
  simpa using h

theorem shortShift_eq_eps_Upar (word : Word) :
    (frameAt word).shortShift = (frameAt word).eps • Upar word := by
  unfold ChildFrame.shortShift Upar
  ext <;> simp <;> ring

theorem standardField_shortShift_eq_sec3X {word : Word} (hW : StrongCore word) (z : Site) :
    standardField word (z + (frameAt word).shortShift) = standardField word (z + sec3X word) := by
  unfold sec3X
  rcases ChildFrame.eps_unit (frameAt word) with he | he
  · rw [if_pos he, shortShift_eq_eps_Upar, he, one_smul]
  · have hne : ¬ (frameAt word).eps = 1 := by rw [he]; norm_num
    rw [if_neg hne]
    have e : z + (frameAt word).shortShift + (frameAt word).child.modifiedDeck.kernel =
        z + (frameAt word).parents.even.unmodifiedDeck.kernel := by
      rw [shortShift_eq_eps_Upar, he, child_kernel_eq word]
      ext <;> simp
    rw [← e]
    exact (kernel_period hW (z + (frameAt word).shortShift)).symm

theorem tGrade_sec3X (word : Word) : (frameAt word).tGrade (sec3X word) = -2 := by
  have he := SheetOffsets.eps_eq_det (word := word)
  have hd := ChildFrame.child_den_eq (frameAt word)
  have hn := ChildFrame.child_num_eq (frameAt word)
  unfold sec3X ChildFrame.tGrade
  rcases ChildFrame.eps_unit (frameAt word) with h1 | h1
  · rw [if_pos h1]
    unfold Upar
    dsimp only
    rw [h1] at he
    rw [hn, hd]
    linear_combination 2 * he
  · rw [if_neg (by rw [h1]; norm_num)]
    unfold Fraction.unmodifiedDeck
    dsimp only
    rw [h1] at he
    rw [hn, hd]
    linear_combination (-2) * he

theorem sheetA_sec3X {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (z : Site) : (frameAt word).sheetA (FqW word) (z + sec3X word) = FqW word z := by
  unfold sec3X
  rcases ChildFrame.eps_unit (frameAt word) with he | he
  · rw [if_pos he, SheetOffsets.sheetA_pos he]
    exact quarterTurnField_Upar_period h hSE z
  · have hne : ¬ (frameAt word).eps = 1 := by rw [he]; norm_num
    rw [if_neg hne]
    unfold ChildFrame.sheetA ChildFrame.sheetShift
    rw [SheetOffsets.phaseW_neg he, sub_zero, one_smul, add_sub_cancel_right]

end FLatticePaper.Sec3Shift
