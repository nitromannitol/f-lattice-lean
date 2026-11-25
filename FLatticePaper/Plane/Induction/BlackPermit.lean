import FLatticePaper.Plane.Induction.SlipPermits
import FLatticePaper.Plane.Induction.StrongEstimates
import FLatticePaper.Plane.Induction.StarRangeArgument

/-! hslip, the black-even piece (sign `+1`): at a black site whose raw slip `D = F − F(· + σ)` is even, both inputs are permitted.

This is the black-even branch of `FLatticePaper.permitLocal_of_star_data`, stated on its own. The increments of the two inputs sum to
`laplacian F c − laplacian F (c + σ) ∈ {−1, 0}` (`slip_sum_eq`), each increment is a unit (`HasUnitSlip`), and at an even `D` the pairs
`(−1, +1)` and `(+1, −1)` are excluded (`NoEvenSlipSaddle`). Hence both increments are `≤ 0`.

At a word these hypotheses are fields of `StrongEstimates`: `F1_unitSlip` and `F1_noSlipSaddle` for `σ = shortShift`, and the binarity of
the packet. The odd black case (`OddBlackNoRise`), the white and the forced and free selections, and the sign `−1` are not here. -/

namespace FLatticePaper

open Farey FLatticePaper.Induction

/-- **The black-even permit.** At a black site with even raw slip, each input is permitted: its slip increment is `≤ 0`. -/
theorem black_even_permit {F : Field} {σ : Site} (hσ : EvenSite σ)
    (hbin : ∀ z, laplacian F z = -1 ∨ laplacian F z = 0)
    (hU : HasUnitSlip F (fun z => F (z + σ)))
    (hS2 : NoEvenSlipSaddle F (fun z => F (z + σ)))
    {c : Site} (hc : laplacian F c = -1) (hpar : (F c - F (c + σ)) % 2 = 0)
    {i : Site} (hi : i = incomingNeg c ∨ i = incomingPos c) :
    slipPermits F (fun z => F (z + σ)) c i := by
  have hS : ¬ ((slipIncrement F (fun z => F (z + σ)) c (incomingNeg c) = -1 ∧
      slipIncrement F (fun z => F (z + σ)) c (incomingPos c) = 1) ∨
      (slipIncrement F (fun z => F (z + σ)) c (incomingNeg c) = 1 ∧
      slipIncrement F (fun z => F (z + σ)) c (incomingPos c) = -1)) := hS2 c hpar
  have hsum := slip_sum_eq F σ c hσ
  have hU1 := hU c (incomingNeg c) (Or.inl rfl)
  have hU2 := hU c (incomingPos c) (Or.inr rfl)
  have hb2 := hbin (c + σ)
  rw [hc] at hsum
  have both : slipIncrement F (fun z => F (z + σ)) c (incomingNeg c) ≤ 0 ∧
      slipIncrement F (fun z => F (z + σ)) c (incomingPos c) ≤ 0 := by
    omega
  unfold slipPermits
  rcases hi with rfl | rfl
  · exact both.1
  · exact both.2

end FLatticePaper

namespace FLatticePaper.BlackPermit

open FLatticePaper FLatticePaper.Induction

/-- **The black-even permit at a word.** For a word, the unit slip and the no-saddle condition are fields of the strong estimates. -/
theorem black_even_permit_word (word : Farey.Word) (hWord : StrongEstimates word) {c i : Site}
    (hc : laplacian (standardField word) c = -1)
    (hpar : (standardField word c - standardField word (c + (frameAt word).shortShift)) % 2 = 0)
    (hi : i = FLatticePaper.incomingNeg c ∨ i = FLatticePaper.incomingPos c) :
    slipPermits (standardField word) (fun z => standardField word (z + (frameAt word).shortShift)) c i :=
  FLatticePaper.black_even_permit (evenSite_shortShift (frameAt word)) hWord.packet.binary
    hWord.F1_unitSlip hWord.F1_noSlipSaddle hc hpar hi

end FLatticePaper.BlackPermit
