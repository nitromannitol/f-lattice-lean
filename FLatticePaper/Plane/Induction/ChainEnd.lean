import FLatticePaper.Plane.Induction.NominalValues
import FLatticePaper.Plane.Induction.RowMinus
import FLatticePaper.Plane.Induction.EarlierV
import FLatticePaper.Plane.Induction.CanonicalSigned
import FLatticePaper.Plane.Induction.QueryClassMain
import FLatticePaper.Plane.Induction.CutRowsAll
import FLatticePaper.Plane.Induction.VWhite
import FLatticePaper.Plane.Induction.StepTwoC

/-! Task w3, step C: the endpoint bound `hEnd` from the chain monotonicity of the conjugate's policy.

* `earlierP_eq_chainPotential`: the earlier chain price is the chain potential `Φ_η = D_η + P(· + ησ')` of the conjugate's field.
* `vAt_one_eq`: the labelled cut has `V'_1 = (0,1)`.
* `origin_le_one`: with the plus prescription at the white point `V'_1` (so the policy retains `V'_1 → V'_0`), the chain
  monotonicity `Φ(V'_0) ≤ Φ(V'_1)` gives `Φ'(V'_0) ≤ nominal 1`. The prescription and the monotonicity are named inputs
  (they are the policy's properties; `hpol` as stated gives monotonicity but not the prescription). -/

namespace FLatticePaper.ChainEnd

open Farey FLatticePaper FLatticePaper.Induction

/-- The earlier chain price is the chain potential of the conjugate's field: `earlierChainPrice = D_η + P(· + ησ')`. -/
theorem earlierP_eq_chainPotential (word : Word) (z : Site) :
    FLatticePaper.earlierChainPrice (standardField (conjWord word)) (frameAt (conjWord word)).parents.odd
        (frameAt (oddBirthPrefix word)).eps (frameAt word).eps z =
      (frameAt (conjWord word)).chainPotential (standardField (conjWord word)) (frameAt word).eps z := by
  rw [EarlierV.eps_old_eq_conj word]
  unfold FLatticePaper.earlierChainPrice ChildFrame.chainPotential ChildFrame.slip ChildFrame.price
  have hshift : Farey.earlierChainShift (frameAt (conjWord word)).parents.odd (frameAt (conjWord word)).eps
      (frameAt word).eps = (frameAt word).eps • (frameAt (conjWord word)).shortShift -
        (frameAt (conjWord word)).parentShift := by
    unfold Farey.earlierChainShift ChildFrame.shortShift ChildFrame.parentShift
    ext <;> simp <;> ring
  rw [hshift, ← add_sub_assoc]
  unfold Fraction.transverseGrade
  simp only [ChildFrame.parentSlope, ChildFrame.shortShift, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  ring

/-- The labelled cut has `V'_1 = (0,1)`: the point `(0,1)` is odd with `s = 2n'` in the odd window. -/
theorem vAt_one_eq (C : ChildFrame) (base : ℤ → Site)
    (hbase : ∀ r : ℤ, 0 ≤ r → r < FreeEnum.period C → base r ∈ C.freeV ∧ (base r).2 = r) :
    FreeEnum.vAt C base 1 = ((0 : ℤ), (1 : ℤ)) := by
  obtain ⟨hn0, hnd, hdn, hd3, -⟩ := C.child_facts
  apply VWindow.row_unique C
  · exact FreeEnum.vAt_snd C base (fun r h0 h1 => (hbase r h0 h1).2) 1
  · exact VWindow.vAt_window C base hbase 1
  · have hs : C.sGrade ((0 : ℤ), (1 : ℤ)) = C.child.den - C.child.num := by
      unfold ChildFrame.sGrade
      ring
    refine ⟨fun he => absurd he (by unfold EvenSite; norm_num), fun _ => ⟨by rw [hs]; omega, by rw [hs]; omega⟩⟩

/-- **The endpoint bound.** With the plus prescription at the white point `V'_1` (so the policy retains `V'_1 → V'_0`) and the
chain monotonicity of the policy, `Φ'(V'_0) ≤ nominal 1`. -/
theorem origin_le_one {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hη : (frameAt word).eps = 1)
    (base : ℤ → Site)
    (hbase : ∀ r : ℤ, 0 ≤ r → r < FreeEnum.period (frameAt (conjWord word)) →
      base r ∈ (frameAt (conjWord word)).freeV ∧ (base r).2 = r)
    (P : Site → Site → Prop)
    (hPres : PrescribedAt (frameAt (conjWord word)) (standardField (conjWord word)) 1 P)
    (hNon : NonincreasingAlong ((frameAt (conjWord word)).chainPotential (standardField (conjWord word)) 1) P) :
    FLatticePaper.earlierChainPrice (standardField (conjWord word)) (frameAt (conjWord word)).parents.odd
        (frameAt (oddBirthPrefix word)).eps (frameAt word).eps (FreeEnum.vAt (frameAt (conjWord word)) base 0) ≤
      NominalValues.nominal (word := word) base 1 := by
  obtain ⟨hn0, hnd, hdn, hd3, -⟩ := (frameAt (conjWord word)).child_facts
  have hper : 2 ≤ FreeEnum.period (frameAt (conjWord word)) := by
    unfold FreeEnum.period
    omega
  have hv1 := vAt_one_eq (frameAt (conjWord word)) base hbase
  have hmem : ((0 : ℤ), (1 : ℤ)) ∈ (frameAt (conjWord word)).freeV := by
    rw [← hv1, RowMinus.vAt_eq_base (frameAt (conjWord word)) base 1 (by omega) (by omega)]
    exact (hbase 1 (by omega) (by omega)).1
  have hwhite := VWhite.laplacian_V1_zero (frameAt (conjWord word)) hSE.packet.strips
  have hP : P ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (0 : ℤ)) := by
    have hiff := hPres.2 ((0 : ℤ), (1 : ℤ)) hmem hwhite ((0 : ℤ), (0 : ℤ))
    rw [hiff]
    unfold ChildFrame.prescribedV
    have hne1 : ((0 : ℤ), (1 : ℤ)) ≠ vFirst := by
      unfold vFirst
      intro e
      have := congrArg Prod.snd e
      norm_num at this
    have hne2 : ((0 : ℤ), (1 : ℤ)) ≠ (frameAt (conjWord word)).vLast := by
      intro e
      have := congrArg Prod.snd e
      have h3 : (frameAt (conjWord word)).vLast.2 =
          (frameAt (conjWord word)).child.num + (frameAt (conjWord word)).child.den - 1 := rfl
      rw [h3] at this
      omega
    have hodd : ¬ EvenSite ((0 : ℤ), (1 : ℤ)) := by
      unfold EvenSite
      norm_num
    rw [if_neg hne1, if_neg hne2, if_neg hodd]
    ext <;> simp
  have hle := hNon ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (0 : ℤ)) hP
  have hk : (1 : ℤ) % FreeEnum.period (frameAt (conjWord word)) ≠ 0 := by
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    norm_num
  have e1 : FLatticePaper.earlierChainPrice (standardField (conjWord word)) (frameAt (conjWord word)).parents.odd
      (frameAt (oddBirthPrefix word)).eps (frameAt word).eps (FreeEnum.vAt (frameAt (conjWord word)) base 0) =
      (frameAt (conjWord word)).chainPotential (standardField (conjWord word)) 1 ((0 : ℤ), (0 : ℤ)) := by
    rw [RowMinus.vAt_zero (frameAt (conjWord word)) base hbase, earlierP_eq_chainPotential word _, hη]
  have e2 : FLatticePaper.earlierChainPrice (standardField (conjWord word)) (frameAt (conjWord word)).parents.odd
      (frameAt (oddBirthPrefix word)).eps (frameAt word).eps (FreeEnum.vAt (frameAt (conjWord word)) base 1) =
      (frameAt (conjWord word)).chainPotential (standardField (conjWord word)) 1 ((0 : ℤ), (1 : ℤ)) := by
    rw [hv1, earlierP_eq_chainPotential word _, hη]
  have e3 := NominalValues.nominal_V h hSE base hbase 1 hk
  rw [e1]
  rw [← e3, e2]
  exact hle

/-- **hEnd.** In phase one, every query at ordinate `0` has `Φ' ≤ nominal 1`: the query is the origin (the V branch,
`origin_le_one`) or `(1,0)` (the H branch with `m = 0`, value `nominal 0 ≤ nominal 1`). -/
theorem hEnd_of_chain {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hTraceW : TraceFromPsi.TraceAt (conjWord word))
    (hX : ∃ x ∈ conjWord word, x ≠ Digit.three)
    (hSE' : StrongEstimates (conjWord (conjWord word)))
    (hTrace' : TraceFromPsi.TraceAt (conjWord (conjWord word)))
    (hη : (frameAt word).eps = 1)
    (base : ℤ → Site)
    (hbase : ∀ r : ℤ, 0 ≤ r → r < FreeEnum.period (frameAt (conjWord word)) →
      base r ∈ (frameAt (conjWord word)).freeV ∧ (base r).2 = r)
    (H : ℕ → Site) (N : ℕ) (hHmem : ∀ j : ℕ, j < N → H j ∈ (frameAt word).freeH)
    (hHabs : ∀ j : ℕ, j < N → (H j).1 = (j : ℤ) + 1)
    (P : Site → Site → Prop)
    (hPres : PrescribedAt (frameAt (conjWord word)) (standardField (conjWord word)) 1 P)
    (hNon : NonincreasingAlong ((frameAt (conjWord word)).chainPotential (standardField (conjWord word)) 1) P) :
    ∀ j : ℕ, 1 ≤ j → j < N → (PsiMonoReal.qry word (ArcPsi.reflH word (H j))).2 = 0 →
      PsiMonoReal.earlierP word (PsiMonoReal.qry word (ArcPsi.reflH word (H j))) ≤
        NominalValues.nominal (word := word) base 1 := by
  intro j hj hjN h0
  have hcutC := CutRowsAll.cut_one_per_ordinate_all (frameAt (conjWord word))
  have hmem : ArcPsi.reflH word (H j) ∈ (frameAt word).freeH := QueryClassMain.reflH_mem_freeH (hHmem j hjN)
  have hW1' : (frameAt word).eps = 1 → (ArcPsi.reflH word (H j)).1 ≠ (frameAt word).child.den := by
    intro _
    unfold ArcPsi.reflH
    rw [hHabs j hjN]
    omega
  rcases QueryClassMain.transport_class h hcutC hmem hW1' hbase with ⟨hv, hnz⟩ | ⟨m, hm1, hm2⟩
  · -- the V branch: the query is `vAt base 0`, the origin
    have hq : PsiMonoReal.qry word (ArcPsi.reflH word (H j)) = FreeEnum.vAt (frameAt (conjWord word)) base 0 := by
      calc PsiMonoReal.qry word (ArcPsi.reflH word (H j))
          = FreeEnum.vAt (frameAt (conjWord word)) base (PsiMonoReal.qry word (ArcPsi.reflH word (H j))).2 := hv.symm
        _ = FreeEnum.vAt (frameAt (conjWord word)) base 0 := congrArg (FreeEnum.vAt (frameAt (conjWord word)) base) h0
    unfold PsiMonoReal.earlierP
    rw [hq]
    exact origin_le_one h hSE hη base hbase P hPres hNon
  · -- the H branch: `m L' = 0` forces `m = 0`, the query is `(1,0)`
    have hper : FreeEnum.period (frameAt (conjWord word)) ≠ 0 := (FreeEnum.period_pos _).ne'
    have hm0 : m = 0 := by
      have : m * FreeEnum.period (frameAt (conjWord word)) = 0 := by rw [← hm2]; exact h0
      rcases mul_eq_zero.mp this with h1 | h1
      · exact h1
      · exact absurd h1 hper
    have hq : PsiMonoReal.qry word (ArcPsi.reflH word (H j)) = ((1 : ℤ), (0 : ℤ)) := by
      calc PsiMonoReal.qry word (ArcPsi.reflH word (H j))
          = ((1 : ℤ), (0 : ℤ)) + m • Vdeck (frameAt (conjWord word)) := hm1
        _ = ((1 : ℤ), (0 : ℤ)) := by rw [hm0]; simp
    have hval := NominalValues.nominal_H h hSE hTraceW base hbase 0
    have e : ((1 : ℤ), (0 : ℤ)) + (0 : ℤ) • Vdeck (frameAt (conjWord word)) = ((1 : ℤ), (0 : ℤ)) := by simp
    rw [e, zero_mul] at hval
    unfold PsiMonoReal.earlierP
    rw [hq, hval]
    have hstep := NominalValues.nominal_step_E4 hX hSE hSE' hTrace' base hbase 0
    rw [hη] at hstep
    simp only [zero_add] at hstep
    rcases hstep with h2 | h2 <;> linarith

/-- **hEnd, row form.** As `hEnd_of_chain`, with the minus row as the input of the H branch (`nominal_step`). -/
theorem hEnd_of_chain_row {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hTraceW : TraceFromPsi.TraceAt (conjWord word))
    (hη : (frameAt word).eps = 1)
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
    (P : Site → Site → Prop)
    (hPres : PrescribedAt (frameAt (conjWord word)) (standardField (conjWord word)) 1 P)
    (hNon : NonincreasingAlong ((frameAt (conjWord word)).chainPotential (standardField (conjWord word)) 1) P) :
    ∀ j : ℕ, 1 ≤ j → j < N → (PsiMonoReal.qry word (ArcPsi.reflH word (H j))).2 = 0 →
      PsiMonoReal.earlierP word (PsiMonoReal.qry word (ArcPsi.reflH word (H j))) ≤
        NominalValues.nominal (word := word) base 1 := by
  intro j hj hjN h0
  have hcutC := CutRowsAll.cut_one_per_ordinate_all (frameAt (conjWord word))
  have hmem : ArcPsi.reflH word (H j) ∈ (frameAt word).freeH := QueryClassMain.reflH_mem_freeH (hHmem j hjN)
  have hW1' : (frameAt word).eps = 1 → (ArcPsi.reflH word (H j)).1 ≠ (frameAt word).child.den := by
    intro _
    unfold ArcPsi.reflH
    rw [hHabs j hjN]
    omega
  rcases QueryClassMain.transport_class h hcutC hmem hW1' hbase with ⟨hv, hnz⟩ | ⟨m, hm1, hm2⟩
  · have hq : PsiMonoReal.qry word (ArcPsi.reflH word (H j)) = FreeEnum.vAt (frameAt (conjWord word)) base 0 := by
      calc PsiMonoReal.qry word (ArcPsi.reflH word (H j))
          = FreeEnum.vAt (frameAt (conjWord word)) base (PsiMonoReal.qry word (ArcPsi.reflH word (H j))).2 := hv.symm
        _ = FreeEnum.vAt (frameAt (conjWord word)) base 0 := congrArg (FreeEnum.vAt (frameAt (conjWord word)) base) h0
    unfold PsiMonoReal.earlierP
    rw [hq]
    exact origin_le_one h hSE hη base hbase P hPres hNon
  · have hper : FreeEnum.period (frameAt (conjWord word)) ≠ 0 := (FreeEnum.period_pos _).ne'
    have hm0 : m = 0 := by
      have : m * FreeEnum.period (frameAt (conjWord word)) = 0 := by rw [← hm2]; exact h0
      rcases mul_eq_zero.mp this with h1 | h1
      · exact h1
      · exact absurd h1 hper
    have hq : PsiMonoReal.qry word (ArcPsi.reflH word (H j)) = ((1 : ℤ), (0 : ℤ)) := by
      calc PsiMonoReal.qry word (ArcPsi.reflH word (H j))
          = ((1 : ℤ), (0 : ℤ)) + m • Vdeck (frameAt (conjWord word)) := hm1
        _ = ((1 : ℤ), (0 : ℤ)) := by rw [hm0]; simp
    have hval := NominalValues.nominal_H h hSE hTraceW base hbase 0
    have e : ((1 : ℤ), (0 : ℤ)) + (0 : ℤ) • Vdeck (frameAt (conjWord word)) = ((1 : ℤ), (0 : ℤ)) := by simp
    rw [e, zero_mul] at hval
    unfold PsiMonoReal.earlierP
    rw [hq, hval]
    have hstep := NominalValues.nominal_step hSE base hbase hrowM 0
    rw [hη] at hstep
    simp only [zero_add] at hstep
    rcases hstep with h2 | h2 <;> linarith

end FLatticePaper.ChainEnd
