import FLatticePaper.Plane.Induction.PsiArc
import FLatticePaper.Plane.Induction.NominalValues
import FLatticePaper.Plane.Induction.HBottom
import FLatticePaper.Plane.Induction.PsiCalibration
import FLatticePaper.Plane.Induction.StepTwoC

/-! Task w3, step A: `TraceAt word` from the strictly earlier estimates and traces, with the nominal values and the arc
discharged. The only inputs that remain are the earlier estimates and traces (`hSE`, `hSE'`, `hTrace'`, `hTraceW`), the
properness of `conjWord word` (`hX`, the non-base case), and, in phase one, the endpoint bound `hEnd` (step C).

The index hypothesis `hIdx` comes from the sheet shift (`PsiCalibration.sheetShift_W0 / W1`) and the arc abscissae `(H j).1 = j+1`.
The arc `H` is any enumeration of `freeH` by abscissa; its bottom `H 0 = (1,0)`, `H 1 = (2,0)` follows (`HBottom`). -/

namespace FLatticePaper.TraceStep

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1Step

/-- Phase zero: `TraceAt word` from the nominal values, the arc, and the earlier estimates. -/
theorem traceAt_W0 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hW0 : (frameAt word).eps = -1)
    (hX : ∃ x ∈ conjWord word, x ≠ Digit.three)
    (hSE' : StrongEstimates (conjWord (conjWord word)))
    (hTrace' : TraceFromPsi.TraceAt (conjWord (conjWord word)))
    (hTraceW : TraceFromPsi.TraceAt (conjWord word))
    (base : ℤ → Site)
    (hbase : ∀ r : ℤ, 0 ≤ r → r < FreeEnum.period (frameAt (conjWord word)) →
      base r ∈ (frameAt (conjWord word)).freeV ∧ (base r).2 = r)
    (H : ℕ → Site) (N : ℕ) (hHmem : ∀ j : ℕ, j < N → H j ∈ (frameAt word).freeH)
    (hHabs : ∀ j : ℕ, j < N → (H j).1 = (j : ℤ) + 1)
    (hcover : ∀ z ∈ (frameAt word).freeH, ∃ j : ℕ, j < N ∧ z = H j) (hN2 : 2 ≤ N) :
    TraceFromPsi.TraceAt word := by
  have hH0 : H 0 = ((1 : ℤ), (0 : ℤ)) := HBottom.H_zero_eq (frameAt word) (hHmem 0 (by omega)) (by
    have := hHabs 0 (by omega)
    simpa using this)
  have hH1 : H 1 = ((2 : ℤ), (0 : ℤ)) := HBottom.H_one_eq (frameAt word) (hHmem 1 (by omega)) (by
    have := hHabs 1 (by omega)
    norm_num at this
    exact this)
  have hIdx : ∀ j : ℕ, 1 ≤ j → j < N →
      (PsiMonoReal.qry word (H j)).2 = (j : ℤ) - (frameAt word).parents.even.den := by
    intro j _ hjN
    have hs := PsiCalibration.sheetShift_W0 word hW0
    have hH := hHabs j hjN
    show ((H j - (frameAt word).sheetShift).1 - 1) = _
    rw [hs, Prod.fst_sub, hH]
    ring
  have hstep : ∀ k, NominalValues.nominal (word := word) base (k + 1) ≤ NominalValues.nominal (word := word) base k := by
    intro k
    rcases NominalValues.nominal_step_E4 hX hSE hSE' hTrace' base hbase k with h0 | h0
    · linarith
    · rw [hW0] at h0
      linarith
  exact PsiArc.traceAt_W0_of_named h hSE hW0 base hbase H N hHmem
    (NominalValues.nominal (word := word) base) hstep hIdx
    (fun k hk => NominalValues.nominal_V h hSE base hbase k hk)
    (fun m => NominalValues.nominal_H h hSE hTraceW base hbase m) hcover hH0 hH1

/-- Phase one: `TraceAt word` from the nominal values, the arc, the endpoint bound `hEnd` and the bound `N ≤ d`. -/
theorem traceAt_W1 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hW1 : (frameAt word).eps = 1)
    (hX : ∃ x ∈ conjWord word, x ≠ Digit.three)
    (hSE' : StrongEstimates (conjWord (conjWord word)))
    (hTrace' : TraceFromPsi.TraceAt (conjWord (conjWord word)))
    (hTraceW : TraceFromPsi.TraceAt (conjWord word))
    (base : ℤ → Site)
    (hbase : ∀ r : ℤ, 0 ≤ r → r < FreeEnum.period (frameAt (conjWord word)) →
      base r ∈ (frameAt (conjWord word)).freeV ∧ (base r).2 = r)
    (H : ℕ → Site) (N : ℕ) (hHmem : ∀ j : ℕ, j < N → H j ∈ (frameAt word).freeH)
    (hHabs : ∀ j : ℕ, j < N → (H j).1 = (j : ℤ) + 1)
    (hcover : ∀ z ∈ (frameAt word).freeH, ∃ j : ℕ, j < N ∧ z = H j) (hN2 : 2 ≤ N)
    (hN : (N : ℤ) ≤ (frameAt word).child.den)
    (hEnd : ∀ j : ℕ, 1 ≤ j → j < N → (PsiMonoReal.qry word (ArcPsi.reflH word (H j))).2 = 0 →
      PsiMonoReal.earlierP word (PsiMonoReal.qry word (ArcPsi.reflH word (H j))) ≤
        NominalValues.nominal (word := word) base 1) :
    TraceFromPsi.TraceAt word := by
  have hH0 : H 0 = ((1 : ℤ), (0 : ℤ)) := HBottom.H_zero_eq (frameAt word) (hHmem 0 (by omega)) (by
    have := hHabs 0 (by omega)
    simpa using this)
  have hH1 : H 1 = ((2 : ℤ), (0 : ℤ)) := HBottom.H_one_eq (frameAt word) (hHmem 1 (by omega)) (by
    have := hHabs 1 (by omega)
    norm_num at this
    exact this)
  have hIdx : ∀ j : ℕ, 1 ≤ j → j < N →
      (PsiMonoReal.qry word (ArcPsi.reflH word (H j))).2 = (frameAt word).child.den - 1 - (j : ℤ) := by
    intro j _ hjN
    have hs := PsiCalibration.sheetShift_W1 word hW1
    have hH := hHabs j hjN
    show ((ArcPsi.reflH word (H j) - (frameAt word).sheetShift).1 - 1) = _
    rw [hs, sub_zero]
    unfold ArcPsi.reflH
    rw [hH]
    ring
  have hstep : ∀ k, NominalValues.nominal (word := word) base k ≤ NominalValues.nominal (word := word) base (k + 1) := by
    intro k
    rcases NominalValues.nominal_step_E4 hX hSE hSE' hTrace' base hbase k with h0 | h0
    · linarith
    · rw [hW1] at h0
      linarith
  exact PsiArc.traceAt_W1_of_named h hSE hW1 base hbase H N hHmem hHabs
    (NominalValues.nominal (word := word) base) hstep hN hIdx
    (fun k hk => NominalValues.nominal_V h hSE base hbase k hk)
    (fun m => NominalValues.nominal_H h hSE hTraceW base hbase m) hEnd hcover hH0 hH1

/-- **The trace step.** `TraceAt word` from the strictly earlier estimates and traces, for a proper conjugate; in phase one
the endpoint bound `hEnd` is the only further input. -/
theorem traceAt_step {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hX : ∃ x ∈ conjWord word, x ≠ Digit.three)
    (hSE' : StrongEstimates (conjWord (conjWord word)))
    (hTrace' : TraceFromPsi.TraceAt (conjWord (conjWord word)))
    (hTraceW : TraceFromPsi.TraceAt (conjWord word))
    (base : ℤ → Site)
    (hbase : ∀ r : ℤ, 0 ≤ r → r < FreeEnum.period (frameAt (conjWord word)) →
      base r ∈ (frameAt (conjWord word)).freeV ∧ (base r).2 = r)
    (H : ℕ → Site) (N : ℕ) (hHmem : ∀ j : ℕ, j < N → H j ∈ (frameAt word).freeH)
    (hHabs : ∀ j : ℕ, j < N → (H j).1 = (j : ℤ) + 1)
    (hcover : ∀ z ∈ (frameAt word).freeH, ∃ j : ℕ, j < N ∧ z = H j) (hN2 : 2 ≤ N)
    (hN : (N : ℤ) ≤ (frameAt word).child.den)
    (hEnd : (frameAt word).eps = 1 → ∀ j : ℕ, 1 ≤ j → j < N →
      (PsiMonoReal.qry word (ArcPsi.reflH word (H j))).2 = 0 →
        PsiMonoReal.earlierP word (PsiMonoReal.qry word (ArcPsi.reflH word (H j))) ≤
          NominalValues.nominal (word := word) base 1) :
    TraceFromPsi.TraceAt word := by
  rcases (frameAt word).eps_unit with hε | hε
  · exact traceAt_W1 h hSE hε hX hSE' hTrace' hTraceW base hbase H N hHmem hHabs hcover hN2 hN (hEnd hε)
  · exact traceAt_W0 h hSE hε hX hSE' hTrace' hTraceW base hbase H N hHmem hHabs hcover hN2

/-- The packet of `word`'s own field, from the conjugate's estimates alone (`packet_of_openInputs_step`). -/
theorem packet_of_strong_conj {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hS : StrongEstimates (conjWord word)) : (frameAt word).Packet (standardField word) :=
  packet_of_openInputs_step h hS.packet (openInputs_of_strong h hS)

/-- **The boundary bound from the trace.** `hbd` at `word`, from `TraceAt word` and the packet of `word`'s field. -/
theorem hbd_of_traceAt {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hS : StrongEstimates (conjWord word))
    (hT : TraceFromPsi.TraceAt word) :
    ∀ z, OnBoundary (frameAt word).closedPolygon z → (frameAt word).price (standardField word) z ≤ (frameAt word).cutPrice :=
  PriceDeck.hbd_of_packet (frameAt word) (standardField word) (packet_of_strong_conj h hS)
    (fun z hz => by
      rw [hT z hz]
      split_ifs <;> linarith)

/-- **The trace step with its boundary bound.** -/
theorem traceAt_step_hbd {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hX : ∃ x ∈ conjWord word, x ≠ Digit.three)
    (hSE' : StrongEstimates (conjWord (conjWord word)))
    (hTrace' : TraceFromPsi.TraceAt (conjWord (conjWord word)))
    (hTraceW : TraceFromPsi.TraceAt (conjWord word))
    (base : ℤ → Site)
    (hbase : ∀ r : ℤ, 0 ≤ r → r < FreeEnum.period (frameAt (conjWord word)) →
      base r ∈ (frameAt (conjWord word)).freeV ∧ (base r).2 = r)
    (H : ℕ → Site) (N : ℕ) (hHmem : ∀ j : ℕ, j < N → H j ∈ (frameAt word).freeH)
    (hHabs : ∀ j : ℕ, j < N → (H j).1 = (j : ℤ) + 1)
    (hcover : ∀ z ∈ (frameAt word).freeH, ∃ j : ℕ, j < N ∧ z = H j) (hN2 : 2 ≤ N)
    (hN : (N : ℤ) ≤ (frameAt word).child.den)
    (hEnd : (frameAt word).eps = 1 → ∀ j : ℕ, 1 ≤ j → j < N →
      (PsiMonoReal.qry word (ArcPsi.reflH word (H j))).2 = 0 →
        PsiMonoReal.earlierP word (PsiMonoReal.qry word (ArcPsi.reflH word (H j))) ≤
          NominalValues.nominal (word := word) base 1) :
    TraceFromPsi.TraceAt word ∧
      (∀ z, OnBoundary (frameAt word).closedPolygon z → (frameAt word).price (standardField word) z ≤ (frameAt word).cutPrice) := by
  have hT := traceAt_step h hSE hX hSE' hTrace' hTraceW base hbase H N hHmem hHabs hcover hN2 hN hEnd
  exact ⟨hT, hbd_of_traceAt h hSE hT⟩

/-- The row-form of the phase-zero trace step: the minus row is an input (it may be named when `conjWord word` is pure). -/
theorem traceAt_W0_row {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hW0 : (frameAt word).eps = -1) (hTraceW : TraceFromPsi.TraceAt (conjWord word))
    (base : ℤ → Site)
    (hbase : ∀ r : ℤ, 0 ≤ r → r < FreeEnum.period (frameAt (conjWord word)) →
      base r ∈ (frameAt (conjWord word)).freeV ∧ (base r).2 = r)
    (hrowM : StepTwoC.RawRow
      (fun i => EndpointDeck.Dq (frameAt (conjWord word)) (standardField (conjWord word)) (-1)
        (FreeEnum.vAt (frameAt (conjWord word)) base i)) (-1)
      ((frameAt (conjWord word)).parents.odd.den + (frameAt (conjWord word)).parents.odd.num)
      (FreeEnum.period (frameAt (conjWord word))))
    (H : ℕ → Site) (N : ℕ) (hHmem : ∀ j : ℕ, j < N → H j ∈ (frameAt word).freeH)
    (hHabs : ∀ j : ℕ, j < N → (H j).1 = (j : ℤ) + 1)
    (hcover : ∀ z ∈ (frameAt word).freeH, ∃ j : ℕ, j < N ∧ z = H j) (hN2 : 2 ≤ N) :
    TraceFromPsi.TraceAt word := by
  have hH0 : H 0 = ((1 : ℤ), (0 : ℤ)) := HBottom.H_zero_eq (frameAt word) (hHmem 0 (by omega)) (by
    have := hHabs 0 (by omega)
    simpa using this)
  have hH1 : H 1 = ((2 : ℤ), (0 : ℤ)) := HBottom.H_one_eq (frameAt word) (hHmem 1 (by omega)) (by
    have := hHabs 1 (by omega)
    norm_num at this
    exact this)
  have hIdx : ∀ j : ℕ, 1 ≤ j → j < N →
      (PsiMonoReal.qry word (H j)).2 = (j : ℤ) - (frameAt word).parents.even.den := by
    intro j _ hjN
    have hs := PsiCalibration.sheetShift_W0 word hW0
    have hH := hHabs j hjN
    show ((H j - (frameAt word).sheetShift).1 - 1) = _
    rw [hs, Prod.fst_sub, hH]
    ring
  have hstep : ∀ k, NominalValues.nominal (word := word) base (k + 1) ≤ NominalValues.nominal (word := word) base k := by
    intro k
    rcases NominalValues.nominal_step hSE base hbase hrowM k with h0 | h0
    · linarith
    · rw [hW0] at h0
      linarith
  exact PsiArc.traceAt_W0_of_named h hSE hW0 base hbase H N hHmem
    (NominalValues.nominal (word := word) base) hstep hIdx
    (fun k hk => NominalValues.nominal_V h hSE base hbase k hk)
    (fun m => NominalValues.nominal_H h hSE hTraceW base hbase m) hcover hH0 hH1

/-- The row-form of the phase-one trace step. -/
theorem traceAt_W1_row {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hW1 : (frameAt word).eps = 1) (hTraceW : TraceFromPsi.TraceAt (conjWord word))
    (base : ℤ → Site)
    (hbase : ∀ r : ℤ, 0 ≤ r → r < FreeEnum.period (frameAt (conjWord word)) →
      base r ∈ (frameAt (conjWord word)).freeV ∧ (base r).2 = r)
    (hrowM : StepTwoC.RawRow
      (fun i => EndpointDeck.Dq (frameAt (conjWord word)) (standardField (conjWord word)) (-1)
        (FreeEnum.vAt (frameAt (conjWord word)) base i)) (-1)
      ((frameAt (conjWord word)).parents.odd.den + (frameAt (conjWord word)).parents.odd.num)
      (FreeEnum.period (frameAt (conjWord word))))
    (H : ℕ → Site) (N : ℕ) (hHmem : ∀ j : ℕ, j < N → H j ∈ (frameAt word).freeH)
    (hHabs : ∀ j : ℕ, j < N → (H j).1 = (j : ℤ) + 1)
    (hcover : ∀ z ∈ (frameAt word).freeH, ∃ j : ℕ, j < N ∧ z = H j) (hN2 : 2 ≤ N)
    (hN : (N : ℤ) ≤ (frameAt word).child.den)
    (hEnd : ∀ j : ℕ, 1 ≤ j → j < N → (PsiMonoReal.qry word (ArcPsi.reflH word (H j))).2 = 0 →
      PsiMonoReal.earlierP word (PsiMonoReal.qry word (ArcPsi.reflH word (H j))) ≤
        NominalValues.nominal (word := word) base 1) :
    TraceFromPsi.TraceAt word := by
  have hH0 : H 0 = ((1 : ℤ), (0 : ℤ)) := HBottom.H_zero_eq (frameAt word) (hHmem 0 (by omega)) (by
    have := hHabs 0 (by omega)
    simpa using this)
  have hH1 : H 1 = ((2 : ℤ), (0 : ℤ)) := HBottom.H_one_eq (frameAt word) (hHmem 1 (by omega)) (by
    have := hHabs 1 (by omega)
    norm_num at this
    exact this)
  have hIdx : ∀ j : ℕ, 1 ≤ j → j < N →
      (PsiMonoReal.qry word (ArcPsi.reflH word (H j))).2 = (frameAt word).child.den - 1 - (j : ℤ) := by
    intro j _ hjN
    have hs := PsiCalibration.sheetShift_W1 word hW1
    have hH := hHabs j hjN
    show ((ArcPsi.reflH word (H j) - (frameAt word).sheetShift).1 - 1) = _
    rw [hs, sub_zero]
    unfold ArcPsi.reflH
    rw [hH]
    ring
  have hstep : ∀ k, NominalValues.nominal (word := word) base k ≤ NominalValues.nominal (word := word) base (k + 1) := by
    intro k
    rcases NominalValues.nominal_step hSE base hbase hrowM k with h0 | h0
    · linarith
    · rw [hW1] at h0
      linarith
  exact PsiArc.traceAt_W1_of_named h hSE hW1 base hbase H N hHmem hHabs
    (NominalValues.nominal (word := word) base) hstep hN hIdx
    (fun k hk => NominalValues.nominal_V h hSE base hbase k hk)
    (fun m => NominalValues.nominal_H h hSE hTraceW base hbase m) hEnd hcover hH0 hH1

/-- **The trace step from the minus row.** The row is the input: named for the all-threes conjugate, and `rowMinus` otherwise. -/
theorem traceAt_step_row {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hTraceW : TraceFromPsi.TraceAt (conjWord word))
    (base : ℤ → Site)
    (hbase : ∀ r : ℤ, 0 ≤ r → r < FreeEnum.period (frameAt (conjWord word)) →
      base r ∈ (frameAt (conjWord word)).freeV ∧ (base r).2 = r)
    (hrowM : StepTwoC.RawRow
      (fun i => EndpointDeck.Dq (frameAt (conjWord word)) (standardField (conjWord word)) (-1)
        (FreeEnum.vAt (frameAt (conjWord word)) base i)) (-1)
      ((frameAt (conjWord word)).parents.odd.den + (frameAt (conjWord word)).parents.odd.num)
      (FreeEnum.period (frameAt (conjWord word))))
    (H : ℕ → Site) (N : ℕ) (hHmem : ∀ j : ℕ, j < N → H j ∈ (frameAt word).freeH)
    (hHabs : ∀ j : ℕ, j < N → (H j).1 = (j : ℤ) + 1)
    (hcover : ∀ z ∈ (frameAt word).freeH, ∃ j : ℕ, j < N ∧ z = H j) (hN2 : 2 ≤ N)
    (hN : (N : ℤ) ≤ (frameAt word).child.den)
    (hEnd : (frameAt word).eps = 1 → ∀ j : ℕ, 1 ≤ j → j < N →
      (PsiMonoReal.qry word (ArcPsi.reflH word (H j))).2 = 0 →
        PsiMonoReal.earlierP word (PsiMonoReal.qry word (ArcPsi.reflH word (H j))) ≤
          NominalValues.nominal (word := word) base 1) :
    TraceFromPsi.TraceAt word := by
  rcases (frameAt word).eps_unit with hε | hε
  · exact traceAt_W1_row h hSE hε hTraceW base hbase hrowM H N hHmem hHabs hcover hN2 hN (hEnd hε)
  · exact traceAt_W0_row h hSE hε hTraceW base hbase hrowM H N hHmem hHabs hcover hN2

end FLatticePaper.TraceStep
