import FLatticePaper.Plane.Induction.StepTwoC
import FLatticePaper.Plane.Induction.ClippedFreeV
import FLatticePaper.Plane.Induction.LiftPsi
import FLatticePaper.Plane.Induction.TraceFromPsi
import FLatticePaper.Plane.Induction.ZoneI1

/-! Task w3, E4: the minus row of the conjugate's raw slip on its labelled V cut.

For `C = frameAt (conjWord word)`, `G = standardField (conjWord word)`, `r = N' + D'` (the conjugate's own parent sum) and
`L = period C`, the row `D_−(V'_i) = rowVal (−1) r L i` holds for `0 ≤ i < L`:
* `i = 0`: `V'_0` is the origin and the zero strip gives `0`.
* `i = L − 1`: `V'_{L−1} = (1,−1) + V'`, so `D_− = D_−(1,−1) − 2 = −2`.
* `1 ≤ i ≤ L − 2`: the clipped identity at `X = conjWord word` (`ClippedFreeV`) gives `−min(g, 2)` with `g = ⌈i/r⌉` by
  `psi_lift` at `X`, which needs the strictly earlier trace `TraceAt (conjWord X)` (named) and `StrongEstimates (conjWord X)`
  (named), and `X` proper (named: `∃ x ∈ X, x ≠ three`). -/

namespace FLatticePaper.RowMinus

open Farey FLatticePaper FLatticePaper.Induction

theorem ceil_one (i r : ℤ) (hr : 0 < r) (h1 : 1 ≤ i) (h2 : i ≤ r) : ArcCut.ceilDiv i r = 1 := by
  unfold ArcCut.ceilDiv
  have a : 1 ≤ (i + r - 1) / r := by
    rw [Int.le_ediv_iff_mul_le hr]
    omega
  have b : (i + r - 1) / r < 2 := by
    rw [Int.ediv_lt_iff_lt_mul hr]
    omega
  omega

theorem ceil_two (i r : ℤ) (hr : 0 < r) (h : r < i) : 2 ≤ ArcCut.ceilDiv i r := by
  unfold ArcCut.ceilDiv
  rw [Int.le_ediv_iff_mul_le hr]
  omega

theorem rowVal_neg (r L i : ℤ) :
    StepTwoC.rowVal (-1) r L i = if i = 0 then 0 else if i ≤ r then -1 else -2 := by
  unfold StepTwoC.rowVal
  simp

/-- On one period the labelled cut is the base. -/
theorem vAt_eq_base (C : ChildFrame) (base : ℤ → Site) (i : ℤ) (hi0 : 0 ≤ i) (hiL : i < FreeEnum.period C) :
    FreeEnum.vAt C base i = base i := by
  unfold FreeEnum.vAt
  rw [Int.emod_eq_of_lt hi0 hiL, Int.ediv_eq_zero_of_lt hi0 hiL]
  simp

/-- The origin is the labelled V point of ordinate `0`. -/
theorem vAt_zero (C : ChildFrame) (base : ℤ → Site)
    (hbase : ∀ r : ℤ, 0 ≤ r → r < FreeEnum.period C → base r ∈ C.freeV ∧ (base r).2 = r) :
    FreeEnum.vAt C base 0 = (0, 0) := by
  obtain ⟨hn0, -, -, -, -⟩ := C.child_facts
  apply VWindow.row_unique C (FreeEnum.vAt_snd C base (fun r h0 h1 => (hbase r h0 h1).2) 0)
  · exact VWindow.vAt_window C base hbase 0
  · have hs : C.sGrade (0, 0) = 0 := by
      unfold ChildFrame.sGrade
      simp
    refine ⟨fun _ => ⟨by rw [hs], by rw [hs]; omega⟩, fun hn => absurd ?_ hn⟩
    unfold EvenSite
    norm_num

/-- `V'_{−1} = (1,−1)`. -/
theorem vAt_minus_one (C : ChildFrame) (base : ℤ → Site)
    (hbase : ∀ r : ℤ, 0 ≤ r → r < FreeEnum.period C → base r ∈ C.freeV ∧ (base r).2 = r) :
    FreeEnum.vAt C base (-1) = ((1 : ℤ), (-1 : ℤ)) := by
  obtain ⟨hn0, -, -, -, -⟩ := C.child_facts
  apply VWindow.row_unique C
  · rw [FreeEnum.vAt_snd C base (fun r h0 h1 => (hbase r h0 h1).2)]
  · exact VWindow.vAt_window C base hbase (-1)
  · have hsq : C.sGrade ((1 : ℤ), (-1 : ℤ)) = 2 * C.child.num := by
      unfold ChildFrame.sGrade
      ring
    refine ⟨fun _ => ⟨by rw [hsq]; omega, by rw [hsq]⟩, fun hne => absurd ?_ hne⟩
    unfold EvenSite
    norm_num

/-- **E4: the minus row of the conjugate's raw slip.** -/
theorem rowMinus {word : Word} (hX : ∃ x ∈ conjWord word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word))
    (hSE' : StrongEstimates (conjWord (conjWord word)))
    (hTrace' : TraceFromPsi.TraceAt (conjWord (conjWord word)))
    (base : ℤ → Site)
    (hbase : ∀ r : ℤ, 0 ≤ r → r < FreeEnum.period (frameAt (conjWord word)) →
      base r ∈ (frameAt (conjWord word)).freeV ∧ (base r).2 = r) :
    StepTwoC.RawRow (fun i => EndpointDeck.Dq (frameAt (conjWord word)) (standardField (conjWord word)) (-1)
        (FreeEnum.vAt (frameAt (conjWord word)) base i)) (-1)
      ((frameAt (conjWord word)).parents.odd.den + (frameAt (conjWord word)).parents.odd.num)
      (FreeEnum.period (frameAt (conjWord word))) := by
  have hP : (frameAt (conjWord word)).Packet (standardField (conjWord word)) := hSE.packet
  have hS := hP.strips
  obtain ⟨hn0, hnd, hdn, hd3, -⟩ := (frameAt (conjWord word)).child_facts
  have hr1 : 1 ≤ (frameAt (conjWord word)).parents.odd.den + (frameAt (conjWord word)).parents.odd.num ∧
      (frameAt (conjWord word)).parents.odd.den + (frameAt (conjWord word)).parents.odd.num + 2 ≤
        FreeEnum.period (frameAt (conjWord word)) := by
    have hb := (frameAt (conjWord word)).valid.odd_bounds
    have he := (frameAt (conjWord word)).valid.even_bounds
    unfold Fraction.InUnitInterval at hb he
    have hd := ZoneI1.child_den_eq (frameAt (conjWord word))
    have hn := ZoneI1.child_num_eq (frameAt (conjWord word))
    unfold FreeEnum.period
    omega
  obtain ⟨hr1', hr2'⟩ := hr1
  intro i hi0 hiL
  dsimp only
  rw [rowVal_neg]
  by_cases h0 : i = 0
  · subst h0
    have hD0 : EndpointDeck.Dq (frameAt (conjWord word)) (standardField (conjWord word)) (-1) (0, 0) = 0 := by
      have ht : (frameAt (conjWord word)).tGrade (0, 0) = 0 := by
        unfold ChildFrame.tGrade
        ring
      apply EndpointDeck.Dq_zero (frameAt (conjWord word)) hS (-1) (0, 0) <;> rw [ht] <;> omega
    rw [vAt_zero (frameAt (conjWord word)) base hbase, hD0]
    simp
  · by_cases hl : i = FreeEnum.period (frameAt (conjWord word)) - 1
    · have hv : FreeEnum.vAt (frameAt (conjWord word)) base i =
          ((1 : ℤ), (-1 : ℤ)) + (1 : ℤ) • Vdeck (frameAt (conjWord word)) := by
        have e : i = -1 + 1 * FreeEnum.period (frameAt (conjWord word)) := by omega
        rw [e, EarlierValues.vAt_add_mul_period, vAt_minus_one (frameAt (conjWord word)) base hbase]
      rw [hv, EndpointDeck.Dq_smul_transverse (frameAt (conjWord word)) hP (-1) 1 ((1 : ℤ), (-1 : ℤ)),
        EndpointDeck.Dq_diag (frameAt (conjWord word)) hS (-1) (Or.inr rfl)]
      rw [if_neg h0, if_neg (show ¬ i ≤ (frameAt (conjWord word)).parents.odd.den +
        (frameAt (conjWord word)).parents.odd.num by omega)]
      norm_num
    · have hi1 : 1 ≤ i := by omega
      have hiL' : i ≤ FreeEnum.period (frameAt (conjWord word)) - 2 := by omega
      rw [vAt_eq_base (frameAt (conjWord word)) base i hi0 hiL]
      have hz := (hbase i hi0 hiL).1
      have hzi := (hbase i hi0 hiL).2
      have hcl := ClippedFreeV.clipped_identity_freeV (word := conjWord word) hX hSE' hP hz
      have hne : base i ≠ (frameAt (conjWord word)).vLast := by
        intro heq
        have h2 := congrArg Prod.snd heq
        have h3 : (frameAt (conjWord word)).vLast.2 =
            (frameAt (conjWord word)).child.num + (frameAt (conjWord word)).child.den - 1 := rfl
        rw [h3, hzi] at h2
        unfold FreeEnum.period at hiL'
        omega
      have hpl := LiftPsi.psi_lift (word := conjWord word) hX hSE' hTrace' hz hne
      rw [hzi] at hpl
      unfold ChildFrame.uq at hpl
      unfold EndpointDeck.Dq
      have e : base i + (-1 : ℤ) • (frameAt (conjWord word)).shortShift =
          base i - (frameAt (conjWord word)).shortShift := by
        ext <;> simp <;> ring
      rw [e, hcl, hpl]
      rw [if_neg h0]
      by_cases hir : i ≤ (frameAt (conjWord word)).parents.odd.den +
          (frameAt (conjWord word)).parents.odd.num
      · rw [if_pos hir, ceil_one i _ (by omega) hi1 hir]
        norm_num
      · rw [if_neg hir, min_eq_right (ceil_two i _ (by omega) (by omega))]

end FLatticePaper.RowMinus
