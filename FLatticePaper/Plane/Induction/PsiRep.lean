import FLatticePaper.Plane.Induction.RepClasses
import FLatticePaper.Plane.Induction.SheetCharts
import FLatticePaper.Plane.Induction.CanonicalSigned
import FLatticePaper.Plane.Induction.FreeChain
import FLatticePaper.Plane.Induction.FreeHWhite
import FLatticePaper.Plane.Induction.Q3White
import FLatticePaper.Plane.Induction.I3Application
import FLatticePaper.Plane.Induction.OldPolicy

/-! The Ψ-monotonicity along a free V step, without the native-edge retention.

For a free V white `w ≠ V_end`, the sheet inequality `Ψ(w + X) ≤ Ψ(u + X)` (with `u = w + prescribedV 1 w`) follows from the chain potential
inequality `Φ(zTurn(u+X−lv)) ≤ Φ(zTurn(w+X−lv))`. That inequality holds because the native point is `z + (span element)` for a free
representative `z` (`RepClasses.rep_exists`), the chain potential drifts by the same constant under the span translation
(`chain_drift_of_periods`), and the representative's own step is retained (`PrescribedAt`, `chainNonincreasing`). -/

namespace FLatticePaper.PsiRep

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.Sec3Shift FLatticePaper.W1MSheet FLatticePaper.W1Step

/-- The chain potential does not increase from `q` to `q'` when `q` is a span translate of a retained free representative `z` and
`q' = q + pr` with `z → z + pr` retained. -/
theorem chain_le_of_step {word : Word} (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop}
    (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    {q q' z pr : Site}
    (hsp : q - z ∈ (frameAt (conjWord word)).child.modifiedDeck.span)
    (hstep : q' - q = pr) (hret : P.retained z (z + pr)) :
    (frameAt (conjWord word)).chainPotential (standardField (conjWord word)) (frameAt word).eps q' ≤
      (frameAt (conjWord word)).chainPotential (standardField (conjWord word)) (frameAt word).eps q := by
  obtain ⟨i0, j0, ht⟩ := hsp
  obtain ⟨c0, hc0⟩ := FreeChain.chain_drift_of_periods (frameAt (conjWord word)) hSE.packet.periods hSE.packet
    (frameAt word).eps i0 j0
  have hq' : q' = pr + q := by
    rw [← hstep]; abel
  have e1 : q - (frameAt (conjWord word)).child.modifiedDeck.combine i0 j0 = z := by
    rw [← ht]; abel
  have e2 : q' - (frameAt (conjWord word)).child.modifiedDeck.combine i0 j0 = z + pr := by
    rw [← ht, hq']; abel
  have h1 := hc0 q
  have h2 := hc0 q'
  rw [e1] at h1
  rw [e2] at h2
  have h3 := P.chainNonincreasing z (z + pr) hret
  linarith

/-- **The sheet inequality along a free V step.** For a free V white `w ≠ V_end`, `Ψ(w + X) ≤ Ψ(u + X)` with `u = w + prescribedV 1 w`,
given the prescription of the canonical policy at the free points (`PrescribedAt`). -/
theorem psi_le_of_rep {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop}
    (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hPres : PrescribedAt (frameAt (conjWord word)) (standardField (conjWord word)) (frameAt word).eps P.retained)
    {w : Site} (hw : w ∈ (frameAt word).freeV) (hne : w ≠ (frameAt word).vLast) :
    sheetPsi word (w + sec3X word) ≤ sheetPsi word (w + (frameAt word).prescribedV 1 w + sec3X word) := by
  obtain ⟨K, hK⟩ := sheetDiff_eq_neg_chain h hSE
  have e1 : w + sec3X word - (frameAt word).sheetShift = w + (sec3X word - (frameAt word).sheetShift) := by abel
  have e2 : w + (frameAt word).prescribedV 1 w + sec3X word - (frameAt word).sheetShift =
      w + (frameAt word).prescribedV 1 w + (sec3X word - (frameAt word).sheetShift) := by abel
  have key : sheetChainPotential word (standardField (conjWord word))
      (w + (frameAt word).prescribedV 1 w + sec3X word - (frameAt word).sheetShift) ≤
      sheetChainPotential word (standardField (conjWord word)) (w + sec3X word - (frameAt word).sheetShift) := by
    rw [i3_sheet_eq_chainPotential, i3_sheet_eq_chainPotential, e1, e2]
    rcases RepClasses.rep_exists h hw hne with ⟨z, hzH, hsp, hst⟩ | ⟨z, hzV, hsp, hst⟩
    · have hlap := laplacian_eq_zero_of_freeH (frameAt (conjWord word)) hSE.packet.strips hzH
      have hret := (hPres.1 z hzH hlap (z + (frameAt (conjWord word)).prescribedH (frameAt word).eps z)).mpr rfl
      exact chain_le_of_step hSE P hsp hst hret
    · have hlap := (frameAt (conjWord word)).laplacian_eq_zero_of_freeV hSE.packet.strips hzV
      have hret := (hPres.2 z hzV hlap (z + (frameAt (conjWord word)).prescribedV (frameAt word).eps z)).mpr rfl
      exact chain_le_of_step hSE P hsp hst hret
  show sheetDiffW word (w + sec3X word) ≤ sheetDiffW word (w + (frameAt word).prescribedV 1 w + sec3X word)
  rw [hK (w + sec3X word), hK (w + (frameAt word).prescribedV 1 w + sec3X word)]
  linarith

end FLatticePaper.PsiRep
