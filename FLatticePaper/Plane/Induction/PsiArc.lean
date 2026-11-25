import FLatticePaper.Plane.Induction.PsiMonoReal
import FLatticePaper.Plane.Induction.TraceFromPsi
import FLatticePaper.Plane.Induction.PsiCalibration
import FLatticePaper.Plane.Induction.ArcPsi

/-! Task w3, steps 3 and 4 composed: from the named transport and earlier-trace inputs to the word's own freeH trace `TraceAt word`.

The arc: `Ψ(H_1) = 1` (calibration), monotonicity for `j ≥ 1` (`PsiMonoReal`), and `ArcPsi.arc_ge_one` give `Ψ(H_j) ≥ 1` for `1 ≤ j < d`.
Every free H point other than `(1,0) = H_0` is such an `H_j` (`HEnum.freeH_enumeration`, cover hypothesis `hcover`).
`TraceFromPsi.traceAt_W0 / traceAt_W1` then give `TraceAt word`. -/

namespace FLatticePaper.PsiArc

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1MSheet W1Step

/-- **Phase zero: `TraceAt` from the named inputs.** -/
theorem traceAt_W0_of_named {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hW0 : (frameAt word).eps = -1)
    (base : ℤ → Site) (H : ℕ → Site) (N : ℕ)
    (f : ℤ → ℤ) (hstep : ∀ k, f (k + 1) ≤ f k)
    (hIdx : ∀ j : ℕ, 1 ≤ j → j < N → (PsiMonoReal.qry word (H j)).2 = (j : ℤ) - (frameAt word).parents.even.den)
    (hClass : ∀ j : ℕ, 1 ≤ j → j < N →
      PsiMonoReal.qry word (H j) = FreeEnum.vAt (frameAt (conjWord word)) base (PsiMonoReal.qry word (H j)).2 ∨
      ∃ m : ℤ, PsiMonoReal.qry word (H j) = ((1 : ℤ), (0 : ℤ)) + m • Vdeck (frameAt (conjWord word)) ∧
        (PsiMonoReal.qry word (H j)).2 = m * FreeEnum.period (frameAt (conjWord word)))
    (hVal : ∀ k : ℤ, PsiMonoReal.earlierP word (FreeEnum.vAt (frameAt (conjWord word)) base k) = f k)
    (hHval : ∀ m : ℤ, PsiMonoReal.earlierP word (((1 : ℤ), (0 : ℤ)) + m • Vdeck (frameAt (conjWord word))) =
      f (m * FreeEnum.period (frameAt (conjWord word))))
    (hcover : ∀ z ∈ (frameAt word).freeH, ∃ j : ℕ, j < N ∧ z = H j)
    (hH0 : H 0 = ((1 : ℤ), (0 : ℤ))) (hH1 : H 1 = ((2 : ℤ), (0 : ℤ))) :
    TraceFromPsi.TraceAt word := by
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

/-- **Phase one: `TraceAt` from the named inputs.** -/
theorem traceAt_W1_of_named {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hW1 : (frameAt word).eps = 1)
    (base : ℤ → Site) (H : ℕ → Site) (N : ℕ)
    (f : ℤ → ℤ) (hstep : ∀ k, f k ≤ f (k + 1))
    (hIdx : ∀ j : ℕ, 1 ≤ j → j < N →
      (PsiMonoReal.qry word (ArcPsi.reflH word (H j))).2 = (frameAt word).child.den - 1 - (j : ℤ))
    (hClass : ∀ j : ℕ, 1 ≤ j → j < N →
      PsiMonoReal.qry word (ArcPsi.reflH word (H j)) = FreeEnum.vAt (frameAt (conjWord word)) base
        (PsiMonoReal.qry word (ArcPsi.reflH word (H j))).2 ∨
      ∃ m : ℤ, PsiMonoReal.qry word (ArcPsi.reflH word (H j)) = ((1 : ℤ), (0 : ℤ)) + m • Vdeck (frameAt (conjWord word)) ∧
        (PsiMonoReal.qry word (ArcPsi.reflH word (H j))).2 = m * FreeEnum.period (frameAt (conjWord word)))
    (hVal : ∀ k : ℤ, PsiMonoReal.earlierP word (FreeEnum.vAt (frameAt (conjWord word)) base k) = f k)
    (hHval : ∀ m : ℤ, PsiMonoReal.earlierP word (((1 : ℤ), (0 : ℤ)) + m • Vdeck (frameAt (conjWord word))) =
      f (m * FreeEnum.period (frameAt (conjWord word))))
    (hcover : ∀ z ∈ (frameAt word).freeH, ∃ j : ℕ, j < N ∧ z = H j)
    (hH0 : H 0 = ((1 : ℤ), (0 : ℤ))) (hH1 : H 1 = ((2 : ℤ), (0 : ℤ))) :
    TraceFromPsi.TraceAt word := by
  have hmono := PsiMonoReal.psi_mono_W1 h hSE base H N f hstep hIdx hClass hVal hHval
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
