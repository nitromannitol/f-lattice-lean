import FLatticePaper.Plane.Induction.EarlierValues
import FLatticePaper.Plane.Induction.EndpointDeck
import FLatticePaper.Plane.Induction.StepTwoC
import FLatticePaper.Plane.Induction.TraceFromPsi
import FLatticePaper.Plane.Induction.RowMinus
import FLatticePaper.Plane.Induction.PsiMonoReal

/-! Task w3, step 2(a) assembled and 2(c) in the nominal form.

`nominal base k = c₀' + D'_η(V'_{k − ε'r'})` is the nominal earlier value of the word.
* `nominal_V`: at a labelled V point of ordinate `k ∉ L'Z`, `Φ'(V'_k) = nominal k`. The even endpoints have `s = 0` and sit
  on `L'Z` (`EndpointDeck.even_zero_period`); the odd lower endpoint is `valOdd`; the rest is `valV`.
* `nominal_H`: at the H-form `(1,0) + m V'`, `Φ' = nominal (m L')` (`valH`, with the conjugate's trace `TraceAt (conjWord word)`).
* `nominal_step`: `nominal (k+1) − nominal k ∈ {0, η}` from `step_two_c`; only the minus row (E4) is named. -/

namespace FLatticePaper.NominalValues

open Farey FLatticePaper FLatticePaper.Induction

/-- The nominal earlier value `c₀' + D'_η(V'_{k − ε'r'})` of the word, with `η = ε(word)`. -/
noncomputable def nominal {word : Word} (base : ℤ → Site) (k : ℤ) : ℤ :=
  (frameAt (conjWord word)).cutPrice +
    (standardField (conjWord word) (FreeEnum.vAt (frameAt (conjWord word)) base
        (k - (frameAt (conjWord word)).eps * ((frameAt (conjWord word)).parents.odd.den +
          (frameAt (conjWord word)).parents.odd.num))) -
      standardField (conjWord word) (FreeEnum.vAt (frameAt (conjWord word)) base
        (k - (frameAt (conjWord word)).eps * ((frameAt (conjWord word)).parents.odd.den +
          (frameAt (conjWord word)).parents.odd.num)) +
        (frameAt word).eps • (frameAt (conjWord word)).shortShift))

/-- **2(a), the labelled V points off `L'Z`.** -/
theorem nominal_V {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (base : ℤ → Site)
    (hbase : ∀ r : ℤ, 0 ≤ r → r < FreeEnum.period (frameAt (conjWord word)) →
      base r ∈ (frameAt (conjWord word)).freeV ∧ (base r).2 = r) (k : ℤ)
    (hk : k % FreeEnum.period (frameAt (conjWord word)) ≠ 0) :
    FLatticePaper.earlierChainPrice (standardField (conjWord word)) (frameAt (conjWord word)).parents.odd
        (frameAt (oddBirthPrefix word)).eps (frameAt word).eps (FreeEnum.vAt (frameAt (conjWord word)) base k) =
      nominal (word := word) base k := by
  have hsn := FreeEnum.vAt_snd (frameAt (conjWord word)) base (fun r h0 h1 => (hbase r h0 h1).2) k
  by_cases he : EvenSite (FreeEnum.vAt (frameAt (conjWord word)) base k)
  · have hns0 : (frameAt (conjWord word)).sGrade (FreeEnum.vAt (frameAt (conjWord word)) base k) ≠ 0 := by
      intro h0
      obtain ⟨m, hm⟩ := EndpointDeck.even_zero_period h _ he h0
      apply hk
      have hkm : k = m * FreeEnum.period (frameAt (conjWord word)) := by linarith
      rw [hkm]
      simp
    exact EarlierValues.valV hSE base hbase k ⟨fun _ => hns0, fun hn => absurd he hn⟩
  · by_cases hlo : (frameAt (conjWord word)).sGrade (FreeEnum.vAt (frameAt (conjWord word)) base k) =
        2 - ((frameAt (conjWord word)).child.den - (frameAt (conjWord word)).child.num)
    · exact EndpointDeck.valOdd h hSE base hbase k he hlo
    · have hns2 : (frameAt (conjWord word)).sGrade (FreeEnum.vAt (frameAt (conjWord word)) base k) ≠
          2 - (frameAt (conjWord word)).child.den + (frameAt (conjWord word)).child.num := by
        intro h'
        apply hlo
        linarith
      exact EarlierValues.valV hSE base hbase k ⟨fun he' => absurd he' he, fun _ => hns2⟩

/-- **2(a), the H-form.** -/
theorem nominal_H {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hTrace : TraceFromPsi.TraceAt (conjWord word))
    (base : ℤ → Site)
    (hbase : ∀ r : ℤ, 0 ≤ r → r < FreeEnum.period (frameAt (conjWord word)) →
      base r ∈ (frameAt (conjWord word)).freeV ∧ (base r).2 = r) (m : ℤ) :
    FLatticePaper.earlierChainPrice (standardField (conjWord word)) (frameAt (conjWord word)).parents.odd
        (frameAt (oddBirthPrefix word)).eps (frameAt word).eps
        (((1 : ℤ), (0 : ℤ)) + m • Vdeck (frameAt (conjWord word))) =
      nominal (word := word) base (m * FreeEnum.period (frameAt (conjWord word))) :=
  EarlierValues.valH h hSE hTrace base hbase m

/-- **2(c) in the nominal form.** Given the minus row (E4), `nominal` steps by `0` or `η` from `k` to `k + 1`. -/
theorem nominal_step {word : Word} (hSE : StrongEstimates (conjWord word))
    (base : ℤ → Site)
    (hbase : ∀ r : ℤ, 0 ≤ r → r < FreeEnum.period (frameAt (conjWord word)) →
      base r ∈ (frameAt (conjWord word)).freeV ∧ (base r).2 = r)
    (hrowM : StepTwoC.RawRow
      (fun i => EndpointDeck.Dq (frameAt (conjWord word)) (standardField (conjWord word)) (-1)
        (FreeEnum.vAt (frameAt (conjWord word)) base i)) (-1)
      ((frameAt (conjWord word)).parents.odd.den + (frameAt (conjWord word)).parents.odd.num)
      (FreeEnum.period (frameAt (conjWord word))))
    (k : ℤ) :
    nominal (word := word) base (k + 1) - nominal (word := word) base k = 0 ∨
      nominal (word := word) base (k + 1) - nominal (word := word) base k = (frameAt word).eps := by
  have hη := (frameAt word).eps_unit
  have key := StepTwoC.step_two_c (frameAt (conjWord word)) hSE.packet
    (standardField_reflectI_conj word hSE) (frameAt word).eps hη base hbase hrowM
    ((frameAt (conjWord word)).eps * ((frameAt (conjWord word)).parents.odd.den +
      (frameAt (conjWord word)).parents.odd.num)) k
  unfold EndpointDeck.Dq at key
  unfold nominal
  rcases key with hk | hk
  · left
    linarith
  · right
    linarith

/-- **2(c) with E4 discharged.** `nominal` steps by `0` or `η`, from the named inputs of `RowMinus.rowMinus`. -/
theorem nominal_step_E4 {word : Word} (hX : ∃ x ∈ conjWord word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word))
    (hSE' : StrongEstimates (conjWord (conjWord word)))
    (hTrace' : TraceFromPsi.TraceAt (conjWord (conjWord word)))
    (base : ℤ → Site)
    (hbase : ∀ r : ℤ, 0 ≤ r → r < FreeEnum.period (frameAt (conjWord word)) →
      base r ∈ (frameAt (conjWord word)).freeV ∧ (base r).2 = r) (k : ℤ) :
    nominal (word := word) base (k + 1) - nominal (word := word) base k = 0 ∨
      nominal (word := word) base (k + 1) - nominal (word := word) base k = (frameAt word).eps :=
  nominal_step hSE base hbase (RowMinus.rowMinus hX hSE hSE' hTrace' base hbase) k

/-- **Phase zero, with the nominal values.** `Ψ` is nondecreasing along the free H arc (`PsiMonoReal.psi_mono_W0`), with the
values `hVal`, `hHval` and the step `hstep` discharged by `nominal_V`, `nominal_H`, `nominal_step_E4`. The named inputs are
the earlier traces, the conjugate's properness and strong estimates, the index (1a) and the class (1b). -/
theorem psi_mono_nominal_W0 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hX : ∃ x ∈ conjWord word, x ≠ Digit.three)
    (hSE' : StrongEstimates (conjWord (conjWord word)))
    (hTrace' : TraceFromPsi.TraceAt (conjWord (conjWord word)))
    (hTraceW : TraceFromPsi.TraceAt (conjWord word))
    (hpar : (frameAt word).eps = -1)
    (base : ℤ → Site)
    (hbase : ∀ r : ℤ, 0 ≤ r → r < FreeEnum.period (frameAt (conjWord word)) →
      base r ∈ (frameAt (conjWord word)).freeV ∧ (base r).2 = r)
    (H : ℕ → Site) (N : ℕ)
    (hIdx : ∀ j : ℕ, 1 ≤ j → j < N → (PsiMonoReal.qry word (H j)).2 =
      (j : ℤ) - (frameAt word).parents.even.den)
    (hClass : ∀ j : ℕ, 1 ≤ j → j < N →
      (PsiMonoReal.qry word (H j) = FreeEnum.vAt (frameAt (conjWord word)) base (PsiMonoReal.qry word (H j)).2 ∧
        (PsiMonoReal.qry word (H j)).2 % FreeEnum.period (frameAt (conjWord word)) ≠ 0) ∨
      ∃ m : ℤ, PsiMonoReal.qry word (H j) = ((1 : ℤ), (0 : ℤ)) + m • Vdeck (frameAt (conjWord word)) ∧
        (PsiMonoReal.qry word (H j)).2 = m * FreeEnum.period (frameAt (conjWord word))) :
    ∀ j : ℕ, 1 ≤ j → j + 1 < N → W1Step.sheetPsi word (H j) ≤ W1Step.sheetPsi word (H (j + 1)) := by
  have hstep : ∀ k, nominal (word := word) base (k + 1) ≤ nominal (word := word) base k := by
    intro k
    rcases nominal_step_E4 hX hSE hSE' hTrace' base hbase k with h0 | h0
    · linarith
    · rw [hpar] at h0
      linarith
  exact PsiMonoReal.psi_mono_W0 h hSE base H N (nominal (word := word) base) hstep hIdx hClass
    (fun k hk => nominal_V h hSE base hbase k hk)
    (fun m => nominal_H h hSE hTraceW base hbase m)

/-- **Phase one, with the nominal values.** `Ψ` is nondecreasing along the reflected free H arc (`PsiMonoReal.psi_mono_W1`),
with `hVal`, `hHval`, `hstep` discharged. The named inputs are the earlier traces, the conjugate's properness and strong
estimates, the bound `N ≤ d`, the index (1a), the class (1b) and the endpoint bound `hEnd`. -/
theorem psi_mono_nominal_W1 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hX : ∃ x ∈ conjWord word, x ≠ Digit.three)
    (hSE' : StrongEstimates (conjWord (conjWord word)))
    (hTrace' : TraceFromPsi.TraceAt (conjWord (conjWord word)))
    (hTraceW : TraceFromPsi.TraceAt (conjWord word))
    (hpar : (frameAt word).eps = 1)
    (base : ℤ → Site)
    (hbase : ∀ r : ℤ, 0 ≤ r → r < FreeEnum.period (frameAt (conjWord word)) →
      base r ∈ (frameAt (conjWord word)).freeV ∧ (base r).2 = r)
    (H : ℕ → Site) (N : ℕ) (hN : (N : ℤ) ≤ (frameAt word).child.den)
    (hIdx : ∀ j : ℕ, 1 ≤ j → j < N →
      (PsiMonoReal.qry word (ArcPsi.reflH word (H j))).2 = (frameAt word).child.den - 1 - (j : ℤ))
    (hClass : ∀ j : ℕ, 1 ≤ j → j < N →
      (PsiMonoReal.qry word (ArcPsi.reflH word (H j)) =
          FreeEnum.vAt (frameAt (conjWord word)) base (PsiMonoReal.qry word (ArcPsi.reflH word (H j))).2 ∧
        ((PsiMonoReal.qry word (ArcPsi.reflH word (H j))).2 % FreeEnum.period (frameAt (conjWord word)) ≠ 0 ∨
          (PsiMonoReal.qry word (ArcPsi.reflH word (H j))).2 = 0)) ∨
      ∃ m : ℤ, PsiMonoReal.qry word (ArcPsi.reflH word (H j)) = ((1 : ℤ), (0 : ℤ)) + m • Vdeck (frameAt (conjWord word)) ∧
        (PsiMonoReal.qry word (ArcPsi.reflH word (H j))).2 = m * FreeEnum.period (frameAt (conjWord word)))
    (hEnd : ∀ j : ℕ, 1 ≤ j → j < N → (PsiMonoReal.qry word (ArcPsi.reflH word (H j))).2 = 0 →
      PsiMonoReal.earlierP word (PsiMonoReal.qry word (ArcPsi.reflH word (H j))) ≤
        nominal (word := word) base 1) :
    ∀ j : ℕ, 1 ≤ j → j + 1 < N →
      W1Step.sheetPsi word (ArcPsi.reflH word (H j)) ≤ W1Step.sheetPsi word (ArcPsi.reflH word (H (j + 1))) := by
  have hstep : ∀ k, nominal (word := word) base k ≤ nominal (word := word) base (k + 1) := by
    intro k
    rcases nominal_step_E4 hX hSE hSE' hTrace' base hbase k with h0 | h0
    · linarith
    · rw [hpar] at h0
      linarith
  exact PsiMonoReal.psi_mono_W1 h hSE base H N (nominal (word := word) base) hstep hN hIdx hClass
    (fun k hk => nominal_V h hSE base hbase k hk)
    (fun m => nominal_H h hSE hTraceW base hbase m) hEnd

end FLatticePaper.NominalValues
