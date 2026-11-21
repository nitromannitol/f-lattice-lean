import FLatticePaper.Plane.Induction.SheetFacts

namespace FLatticePaper.Induction
open Farey

/-- The conjugate word of a proper word: the swapped birth prefix of its odd parent. -/
def conjWord (word : Word) : Word := (oddBirthPrefix word).map Digit.swapTwoThree

/-- Induction over words: a property of the pure words and a step from the conjugate word gives every word. -/
theorem word_induction {P : Word → Prop}
    (hpure : ∀ k : ℕ, P (List.replicate k .three))
    (hstep : ∀ word, (∃ x ∈ word, x ≠ .three) → P (conjWord word) → P word) :
    ∀ word, P word := by
  have key : ∀ n : ℕ, ∀ word : Word, word.length = n → P word := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro word hlen
      by_cases hall : ∀ x ∈ word, x = Digit.three
      · rw [all_three_eq_replicate hall]
        exact hpure _
      · have hex : ∃ x ∈ word, x ≠ Digit.three := by
          by_contra hc
          exact hall (fun x hx => Classical.byContradiction fun hne => hc ⟨x, hx, hne⟩)
        have hlt : (conjWord word).length < n := by
          rw [← hlen]
          exact length_map_oddBirthPrefix_lt hex
        exact hstep word hex (ih _ hlt _ rfl)
  intro word
  exact key _ word rfl

/-- The three open inputs I1, I2, I3 of the step at a proper word (STATUS.md, Open). -/
def OpenInputs (word : Word) : Prop :=
  let frame := frameAt word
  let Fp := quarterTurnField (standardField (conjWord word))
  (∀ z ∈ frame.closedPolygon, 1 - frame.child.den ≤ frame.tGrade z → 0 ≤ frame.sheetC Fp z) ∧
  (∀ z ∈ frame.closedPolygon, frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 1 →
    harmonicGrid z ≤ (if frame.eps = 1 then frame.sheetC Fp z else frame.sheetA Fp z)) ∧
  (∀ z ∈ frame.closedPolygon, laplacian (frame.sheetMin Fp) z = -1 ∨ laplacian (frame.sheetMin Fp) z = 0)

end FLatticePaper.Induction
