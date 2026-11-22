import FLatticePaper.Plane.Induction.OpenLocal
import FLatticePaper.Plane.Induction.TwosPacket

/-! # The packet induction with the powers of two as base cases (task 39)

The induction `packet_standardField_of_inputs` takes the step from the conjugate word at every proper word. The words
`2^(k+1)` are treated here as base cases: their packets are supplied (from the near-one constants, `TwosPacket`), so the
open inputs are needed only at the proper words that are not powers of two. The pure words `3^k` keep their packets from
`reciprocal_packet`. -/

namespace FLatticePaper.Induction
open Farey Construction

/-- A nonempty power of the digit two: `2^(k+1)`. -/
def IsTwoPow (word : Word) : Prop := ∃ k : ℕ, word = List.replicate (k + 1) Digit.two

/-- Induction over words, with the pure words and the powers of two as base cases, and a step from the conjugate word at
the other proper words. -/
theorem word_induction_twos {P : Word → Prop}
    (hpure : ∀ k : ℕ, P (List.replicate k .three))
    (htwo : ∀ k : ℕ, P (List.replicate (k + 1) .two))
    (hstep : ∀ word, (∃ x ∈ word, x ≠ .three) → ¬ IsTwoPow word → P (conjWord word) → P word) :
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
        by_cases htw : IsTwoPow word
        · obtain ⟨k, hk⟩ := htw
          rw [hk]
          exact htwo k
        · have hlt : (conjWord word).length < n := by
            rw [← hlen]
            exact length_map_oddBirthPrefix_lt hex
          exact hstep word hex htw (ih _ hlt _ rfl)
  intro word
  exact key _ word rfl

/-- The packet of every standard field, from the packets of the powers of two and the open inputs at the other proper
words. -/
theorem packet_standardField_of_twos
    (htwo : ∀ k : ℕ, (frameAt (List.replicate (k + 1) Digit.two)).Packet
      (standardField (List.replicate (k + 1) Digit.two)))
    (hstar : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ IsTwoPow word → StarZoneInputs word)
    (hsheet : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ IsTwoPow word → SheetLocalInputs word) :
    ∀ word, (frameAt word).Packet (standardField word) := by
  refine word_induction_twos (P := fun word => (frameAt word).Packet (standardField word)) ?_ ?_ ?_
  · intro k
    exact reciprocal_packet k
  · intro k
    exact htwo k
  · intro word hproper htw hIH
    have hop := openInputs_of_inputs hproper hIH (hstar word hproper htw) (hsheet word hproper htw)
    obtain ⟨hA0, hEq, hrefl, -⟩ := sheetFacts_of_conjPacket hproper hIH
    obtain ⟨hC0, hGe, hbin⟩ := hop
    have hP := (frameAt word).packet_of_sheets (Fp := quarterTurnField (standardField (conjWord word)))
      hA0 hC0 hEq hGe hrefl hbin
    rw [standardField_proper hproper]
    exact hP

end FLatticePaper.Induction
