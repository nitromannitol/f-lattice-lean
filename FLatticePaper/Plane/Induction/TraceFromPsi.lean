import FLatticePaper.Plane.Induction.PriceInputs
import FLatticePaper.Plane.Induction.PsiCalibration
import FLatticePaper.Plane.Induction.BottomMatch
import FLatticePaper.Plane.Induction.PriceDeck
import FLatticePaper.Plane.Induction.TieReduce

/-! Task w3, step 4: the word's own freeH trace from the sheet potential, and `hbd` at the word.

`TraceAt word` is the freeH trace `P(z) = c₀ − [z ≠ (1,0)]` of the word. The phase identities `price_W0_trace` and `price_W1_trace`
express the price through `Ψ = sheetPsi`; with the two calibrations (`Ψ((1,0)) = 0` in phase zero, `Ψ(reflH (1,0)) = 0` in phase one)
the trace reduces to the pointwise bound `Ψ(w) ≥ 1` at every other free H point `w` (PSI, w3 step 3). `hbd` is
`PriceDeck.hbd_of_packet` applied to the trace. -/

namespace FLatticePaper.TraceFromPsi

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1MSheet W1Step

/-- **The word's own freeH trace.** `P(z) = c₀` at the zero point `(1,0)`, `c₀ − 1` at the other free H points. -/
def TraceAt (word : Word) : Prop :=
  ∀ z ∈ (frameAt word).freeH,
    (frameAt word).price (standardField word) z =
      (frameAt word).cutPrice - (if z = ((1 : ℤ), (0 : ℤ)) then 0 else 1)

/-- **Phase zero.** If `Ψ ≥ 1` at every free H point other than `(1,0)`, the trace holds. -/
theorem traceAt_W0 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hW0 : (frameAt word).eps = -1)
    (hPSI : ∀ z ∈ (frameAt word).freeH, z ≠ ((1 : ℤ), (0 : ℤ)) → 1 ≤ sheetPsi word z) :
    TraceAt word := by
  intro z hz
  rw [PriceInputs.price_W0_trace h hSE hW0 z hz]
  by_cases hz1 : z = ((1 : ℤ), (0 : ℤ))
  · subst hz1
    rw [if_pos rfl, PsiCalibration.sheetPsi_H0_W0 word h hSE hW0]
    norm_num
  · rw [if_neg hz1, min_eq_left (by linarith [hPSI z hz hz1])]
    ring

/-- **Phase one.** If `Ψ(reflH z) ≥ 1` at every free H point other than `(1,0)`, the trace holds. -/
theorem traceAt_W1 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hW1 : (frameAt word).eps = 1)
    (hPSI : ∀ z ∈ (frameAt word).freeH, z ≠ ((1 : ℤ), (0 : ℤ)) → 1 ≤ sheetPsi word (ArcPsi.reflH word z)) :
    TraceAt word := by
  intro z hz
  rw [PriceInputs.price_W1_trace h hSE hW1 z hz]
  by_cases hz1 : z = ((1 : ℤ), (0 : ℤ))
  · subst hz1
    rw [if_pos rfl, BottomMatch.reflH_one_zero word, PsiCalibration.sheetPsi_hLast_W1 word h hSE hW1]
    norm_num
  · rw [if_neg hz1, min_eq_left (by linarith [hPSI z hz hz1])]
    ring

/-- **`hbd` at the word.** The boundary price bound follows from the word's own freeH trace. -/
theorem hbd_at_word {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hTr : TraceAt word) :
    ∀ z, OnBoundary (frameAt word).closedPolygon z → (frameAt word).price (standardField word) z ≤ (frameAt word).cutPrice :=
  PriceDeck.hbd_of_packet (frameAt word) (standardField word) (packet_of_strong h hSE) (fun z hz => by
    rw [hTr z hz]
    have : (0 : ℤ) ≤ (if z = ((1 : ℤ), (0 : ℤ)) then 0 else 1) := by split_ifs <;> norm_num
    linarith)

end FLatticePaper.TraceFromPsi
