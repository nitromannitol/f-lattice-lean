import FLatticePaper.Plane.Induction.W1NonfreeHsq
import FLatticePaper.Plane.Induction.W1TieInputs

/-! # The sheet difference along a three-edge return (Q32, reading (a), part 1)

At an `M`-white root `c` with `Ψ(c) ≥ 0`, the rejected input `p₀` of `c` satisfies `max(0, Ψ(c) − 1) ≤ Ψ(p₀)`, and the three retained
`A`-arrows `p₀ → p₁ → p₂ → c` give `Ψ(p₀) ≤ Ψ(p₁) ≤ Ψ(p₂) ≤ Ψ(c)` (`psi_mono`). No square and no whiteness at the chain points is used:
if `Ψ(c) ≥ 1` the sibling estimate `Ψ(c) − 1 ≤ Ψ(p₀)` (`psi_unit_input`) applies; if `Ψ(c) = 0`, the tie lemma `inputs_tie_of_mwhite`
gives `C = A` at both inputs, so `Ψ(p₀) = 0`. -/

namespace FLatticePaper.SheetLowerBound

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1NonfreeHsq FLatticePaper.W1MSheet FLatticePaper.W1Step

theorem sheetPsi_chain_lower {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop}
    (Pd : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    {c p0 p1 p2 : Site} (hM : laplacian (MW word) c = 0) (hc0 : 0 ≤ sheetPsi word c)
    (hin : Edge p0 c)
    (hR0 : sheetPolicyA Pd (frameAt word).sheetShift p0 p1)
    (hR1 : sheetPolicyA Pd (frameAt word).sheetShift p1 p2)
    (hR2 : sheetPolicyA Pd (frameAt word).sheetShift p2 c) :
    max 0 (sheetPsi word c - 1) ≤ sheetPsi word p0 ∧ sheetPsi word p0 ≤ sheetPsi word p1 ∧
      sheetPsi word p1 ≤ sheetPsi word p2 ∧ sheetPsi word p2 ≤ sheetPsi word c := by
  have hbinF : ∀ x, laplacian (FqW word) x = -1 ∨ laplacian (FqW word) x = 0 :=
    fun x => quarterTurnField_binary hSE.packet.binary x
  have h1 := psi_mono hw hSE Pd hR0
  have h2 := psi_mono hw hSE Pd hR1
  have h3 := psi_mono hw hSE Pd hR2
  have hlow : max 0 (sheetPsi word c - 1) ≤ sheetPsi word p0 := by
    by_cases h1c : 1 ≤ sheetPsi word c
    · have hu := psi_unit_input hw hSE hin
      exact max_le (by omega) (by omega)
    · have h0 : sheetPsi word c = 0 := by omega
      have hT : (frameAt word).sheetC (FqW word) c = (frameAt word).sheetA (FqW word) c := by
        unfold sheetPsi at h0
        omega
      have hi := FLatticePaper.W1TieInputs.inputs_tie_of_mwhite (frameAt word) (FqW word) hbinF c hM hT p0 hin
      have hz : sheetPsi word p0 = 0 := by
        unfold sheetPsi
        omega
      exact max_le (by omega) (by omega)
  exact ⟨hlow, h1, h2, h3⟩

end FLatticePaper.SheetLowerBound
