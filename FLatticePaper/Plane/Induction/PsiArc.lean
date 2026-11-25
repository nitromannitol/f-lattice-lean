import FLatticePaper.Plane.Induction.PsiMonoReal
import FLatticePaper.Plane.Induction.TraceFromPsi
import FLatticePaper.Plane.Induction.PsiCalibration
import FLatticePaper.Plane.Induction.ArcPsi
import FLatticePaper.Plane.Induction.QueryClassMain

/-! Task w3, steps 3 and 4 composed: from the named earlier-trace inputs to the word's own freeH trace `TraceAt word`.

The transport classification (1b) is now proved (`QueryClassMain.transport_class`), so the query hypothesis of the monotonicity is
derived here. The named inputs left are: the conjugate's one-point-per-ordinate cut `hcutC` and the labelling `base`, the
enumeration of the free H cut (membership, abscissae, cover, `H 0 = (1,0)`, `H 1 = (2,0)`), the phase index `hIdx` (1a), the
earlier values `hVal`, `hHval`, the step `hstep` (2c), and the phase-one endpoint bound `hEnd` (2a). -/

namespace FLatticePaper.PsiArc

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1MSheet W1Step

/-- **Phase zero: `TraceAt` from the named inputs.** The transport classification is proved; the earlier trace is named. -/
theorem traceAt_W0_of_named {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hW0 : (frameAt word).eps = -1)
    (hcutC : FreeEnum.CutOnePerOrdinate (frameAt (conjWord word)))
    (base : ℤ → Site)
    (hbase : ∀ r : ℤ, 0 ≤ r → r < FreeEnum.period (frameAt (conjWord word)) →
      base r ∈ (frameAt (conjWord word)).freeV ∧ (base r).2 = r)
    (H : ℕ → Site) (N : ℕ)
    (hHmem : ∀ j : ℕ, j < N → H j ∈ (frameAt word).freeH)
    (f : ℤ → ℤ) (hstep : ∀ k, f (k + 1) ≤ f k)
    (hIdx : ∀ j : ℕ, 1 ≤ j → j < N → (PsiMonoReal.qry word (H j)).2 = (j : ℤ) - (frameAt word).parents.even.den)
    (hVal : ∀ k : ℤ, k % FreeEnum.period (frameAt (conjWord word)) ≠ 0 →
      PsiMonoReal.earlierP word (FreeEnum.vAt (frameAt (conjWord word)) base k) = f k)
    (hHval : ∀ m : ℤ, PsiMonoReal.earlierP word (((1 : ℤ), (0 : ℤ)) + m • Vdeck (frameAt (conjWord word))) =
      f (m * FreeEnum.period (frameAt (conjWord word))))
    (hcover : ∀ z ∈ (frameAt word).freeH, ∃ j : ℕ, j < N ∧ z = H j)
    (hH0 : H 0 = ((1 : ℤ), (0 : ℤ))) (hH1 : H 1 = ((2 : ℤ), (0 : ℤ))) :
    TraceFromPsi.TraceAt word := by
  have hClass : ∀ j : ℕ, 1 ≤ j → j < N →
      (PsiMonoReal.qry word (H j) = FreeEnum.vAt (frameAt (conjWord word)) base (PsiMonoReal.qry word (H j)).2 ∧
        (PsiMonoReal.qry word (H j)).2 % FreeEnum.period (frameAt (conjWord word)) ≠ 0) ∨
      ∃ m : ℤ, PsiMonoReal.qry word (H j) = ((1 : ℤ), (0 : ℤ)) + m • Vdeck (frameAt (conjWord word)) ∧
        (PsiMonoReal.qry word (H j)).2 = m * FreeEnum.period (frameAt (conjWord word)) := by
    intro j _ hjN
    have hW1 : (frameAt word).eps = 1 → (H j).1 ≠ (frameAt word).child.den :=
      fun he => absurd (he.symm.trans hW0) (by norm_num)
    rcases QueryClassMain.transport_class h hcutC (hHmem j hjN) hW1 hbase with ⟨hv, hnz⟩ | ⟨m, hm1, hm2⟩
    · left
      refine ⟨hv.symm, ?_⟩
      rcases hnz with hnz | ⟨he, _⟩
      · exact hnz
      · exact absurd (he.symm.trans hW0) (by norm_num)
    · right
      exact ⟨m, hm1, hm2⟩
  have hmono := PsiMonoReal.psi_mono_W0 h hSE base H N f hstep hIdx hClass hVal hHval
  have hPSI : ∀ z ∈ (frameAt word).freeH, z ≠ ((1 : ℤ), (0 : ℤ)) → 1 ≤ sheetPsi word z := by
    intro z hz hz1
    obtain ⟨j, hjN, rfl⟩ := hcover z hz
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hz1 hH0
    have h1 : sheetPsi word (H 1) = 1 := by
      rw [hH1]
      exact PsiCalibration.sheetPsi_H1_W0 word h hSE hW0
    exact ArcPsi.arc_ge_one (fun j => sheetPsi word (H j)) N h1 hmono j (Nat.one_le_iff_ne_zero.mpr hj0) hjN
  exact TraceFromPsi.traceAt_W0 h hSE hW0 hPSI

/-- **Phase one: `TraceAt` from the named inputs.** The query is `reflH (H j)`, a free H point with abscissa `d − j ≠ d`. -/
theorem traceAt_W1_of_named {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hW1 : (frameAt word).eps = 1)
    (hcutC : FreeEnum.CutOnePerOrdinate (frameAt (conjWord word)))
    (base : ℤ → Site)
    (hbase : ∀ r : ℤ, 0 ≤ r → r < FreeEnum.period (frameAt (conjWord word)) →
      base r ∈ (frameAt (conjWord word)).freeV ∧ (base r).2 = r)
    (H : ℕ → Site) (N : ℕ)
    (hHmem : ∀ j : ℕ, j < N → H j ∈ (frameAt word).freeH)
    (hHabs : ∀ j : ℕ, j < N → (H j).1 = (j : ℤ) + 1)
    (f : ℤ → ℤ) (hstep : ∀ k, f k ≤ f (k + 1)) (hN : (N : ℤ) ≤ (frameAt word).child.den)
    (hIdx : ∀ j : ℕ, 1 ≤ j → j < N →
      (PsiMonoReal.qry word (ArcPsi.reflH word (H j))).2 = (frameAt word).child.den - 1 - (j : ℤ))
    (hVal : ∀ k : ℤ, k % FreeEnum.period (frameAt (conjWord word)) ≠ 0 →
      PsiMonoReal.earlierP word (FreeEnum.vAt (frameAt (conjWord word)) base k) = f k)
    (hHval : ∀ m : ℤ, PsiMonoReal.earlierP word (((1 : ℤ), (0 : ℤ)) + m • Vdeck (frameAt (conjWord word))) =
      f (m * FreeEnum.period (frameAt (conjWord word))))
    (hEnd : ∀ j : ℕ, 1 ≤ j → j < N → (PsiMonoReal.qry word (ArcPsi.reflH word (H j))).2 = 0 →
      PsiMonoReal.earlierP word (PsiMonoReal.qry word (ArcPsi.reflH word (H j))) ≤ f 1)
    (hcover : ∀ z ∈ (frameAt word).freeH, ∃ j : ℕ, j < N ∧ z = H j)
    (hH0 : H 0 = ((1 : ℤ), (0 : ℤ))) (hH1 : H 1 = ((2 : ℤ), (0 : ℤ))) :
    TraceFromPsi.TraceAt word := by
  have hClass : ∀ j : ℕ, 1 ≤ j → j < N →
      (PsiMonoReal.qry word (ArcPsi.reflH word (H j)) = FreeEnum.vAt (frameAt (conjWord word)) base
          (PsiMonoReal.qry word (ArcPsi.reflH word (H j))).2 ∧
        ((PsiMonoReal.qry word (ArcPsi.reflH word (H j))).2 % FreeEnum.period (frameAt (conjWord word)) ≠ 0 ∨
          (PsiMonoReal.qry word (ArcPsi.reflH word (H j))).2 = 0)) ∨
      ∃ m : ℤ, PsiMonoReal.qry word (ArcPsi.reflH word (H j)) = ((1 : ℤ), (0 : ℤ)) + m • Vdeck (frameAt (conjWord word)) ∧
        (PsiMonoReal.qry word (ArcPsi.reflH word (H j))).2 = m * FreeEnum.period (frameAt (conjWord word)) := by
    intro j hj hjN
    have hmem : ArcPsi.reflH word (H j) ∈ (frameAt word).freeH := QueryClassMain.reflH_mem_freeH (hHmem j hjN)
    have hW1' : (frameAt word).eps = 1 → (ArcPsi.reflH word (H j)).1 ≠ (frameAt word).child.den := by
      intro _
      unfold ArcPsi.reflH
      rw [hHabs j hjN]
      omega
    rcases QueryClassMain.transport_class h hcutC hmem hW1' hbase with ⟨hv, hnz⟩ | ⟨m, hm1, hm2⟩
    · left
      refine ⟨hv.symm, ?_⟩
      rcases hnz with hnz | ⟨_, hk⟩
      · exact Or.inl hnz
      · exact Or.inr hk
    · right
      exact ⟨m, hm1, hm2⟩
  have hmono := PsiMonoReal.psi_mono_W1 h hSE base H N f hstep hN hIdx hClass hVal hHval hEnd
  have hPSI : ∀ z ∈ (frameAt word).freeH, z ≠ ((1 : ℤ), (0 : ℤ)) → 1 ≤ sheetPsi word (ArcPsi.reflH word z) := by
    intro z hz hz1
    obtain ⟨j, hjN, rfl⟩ := hcover z hz
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hz1 hH0
    have h1 : sheetPsi word (ArcPsi.reflH word (H 1)) = 1 := by
      rw [hH1]
      have e : ArcPsi.reflH word ((2 : ℤ), (0 : ℤ)) =
          ((frameAt word).child.den - 1, (frameAt word).child.num - 1) := by
        unfold ArcPsi.reflH
        ext
        · simp only
          ring
        · simp
      rw [e]
      exact PsiCalibration.sheetPsi_hMinus2_W1 word h hSE hW1
    exact ArcPsi.arc_ge_one (fun j => sheetPsi word (ArcPsi.reflH word (H j))) N h1 hmono j
      (Nat.one_le_iff_ne_zero.mpr hj0) hjN
  exact TraceFromPsi.traceAt_W1 h hSE hW1 hPSI

end FLatticePaper.PsiArc
