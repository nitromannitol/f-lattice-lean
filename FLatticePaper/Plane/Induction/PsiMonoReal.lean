import FLatticePaper.Plane.Induction.PsiMono
import FLatticePaper.Plane.Induction.SheetDifference
import FLatticePaper.Plane.Induction.HEnum
import FLatticePaper.Plane.Induction.FreeEnum
import FLatticePaper.Plane.Induction.W1Step
import FLatticePaper.Plane.Induction.ArcPsi
import FLatticePaper.Plane.Induction.CutOnePerProper
import FLatticePaper.Plane.Induction.NonfreeBridge

/-! Task w3, step 3 at the real objects: `Ψ` is nondecreasing along the free H arc for `j ≥ 1`.

The sheet potential is `Ψ(z) = K − Φ'(qry z)` (`sheetDifference_identifies`), with `Φ'` the earlier chain price of the conjugate.
The named inputs are the two steps of the transport and earlier trace:
* (1b) `hClass`: each query is an earlier V point `V'_{k}` (`FreeEnum.vAt`, `k` its ordinate), or `H'_0 + m V'` with `k = m L'`;
* (1a) `hIdx`: the ordinate of the query is `j − d_q` (phase zero) or `d − 1 − j` (phase one);
* (2a) `hVal`, `hHval`: `Φ'` equals `f(k)` at the V points and `f(m L')` at `H'_0 + m V'`;
* (2c) `hstep`: the step `f` is nonincreasing (phase zero) or nondecreasing (phase one).
The pure monotonicity is `PsiMono.mono_W0` / `mono_W1`. -/

namespace FLatticePaper.PsiMonoReal

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1MSheet W1Step

/-- The sheet query `Z(z − sheetShift)` of `sheetDifference_identifies`. -/
def qry (word : Word) (z : Site) : Site :=
  (-((z - (frameAt word).sheetShift).2), (z - (frameAt word).sheetShift).1 - 1)

/-- The earlier chain price `Φ'` of the word (`sheetDifference_identifies`). -/
noncomputable def earlierP (word : Word) (z : Site) : ℤ :=
  FLatticePaper.earlierChainPrice (standardField (conjWord word)) (frameAt (conjWord word)).parents.odd
    (frameAt (oddBirthPrefix word)).eps (frameAt word).eps z

/-- **The sheet identity:** `Ψ(z) = K − Φ'(qry z)` with one constant `K`. -/
theorem psi_eq_K {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word)) :
    ∃ K : ℤ, ∀ z : Site, sheetPsi word z = K - earlierP word (qry word z) := by
  obtain ⟨K, hK⟩ := sheetDifference_identifies h hSE.packet
  refine ⟨K, fun z => ?_⟩
  have := hK z
  unfold sheetPsi earlierP qry
  linarith

/-- **Monotonicity, phase zero** (`η = −1`), from the named (1a), (1b), (2a), (2c). -/
theorem psi_mono_W0 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (base : ℤ → Site)
    (H : ℕ → Site) (N : ℕ)
    (f : ℤ → ℤ) (hstep : ∀ k, f (k + 1) ≤ f k)
    (hIdx : ∀ j : ℕ, 1 ≤ j → j < N → (qry word (H j)).2 = (j : ℤ) - (frameAt word).parents.even.den)
    (hClass : ∀ j : ℕ, 1 ≤ j → j < N →
      qry word (H j) = FreeEnum.vAt (frameAt (conjWord word)) base (qry word (H j)).2 ∨
      ∃ m : ℤ, qry word (H j) = ((1 : ℤ), (0 : ℤ)) + m • Vdeck (frameAt (conjWord word)) ∧
        (qry word (H j)).2 = m * FreeEnum.period (frameAt (conjWord word)))
    (hVal : ∀ k : ℤ, earlierP word (FreeEnum.vAt (frameAt (conjWord word)) base k) = f k)
    (hHval : ∀ m : ℤ, earlierP word (((1 : ℤ), (0 : ℤ)) + m • Vdeck (frameAt (conjWord word))) =
      f (m * FreeEnum.period (frameAt (conjWord word)))) :
    ∀ j : ℕ, 1 ≤ j → j + 1 < N → sheetPsi word (H j) ≤ sheetPsi word (H (j + 1)) := by
  obtain ⟨K, hK⟩ := psi_eq_K h hSE
  have hΦ : ∀ j : ℕ, 1 ≤ j → j < N →
      earlierP word (qry word (H j)) = f ((j : ℤ) - (frameAt word).parents.even.den) := by
    intro j hj hjN
    rcases hClass j hj hjN with h1 | ⟨m, h1, h2⟩
    · rw [← hIdx j hj hjN]
      rw [← hVal (qry word (H j)).2]
      congr 1
    · rw [← hIdx j hj hjN, h2, ← hHval m, ← h1]
  intro j hj hjN
  rw [hK (H j), hK (H (j + 1))]
  have hm := PsiMono.mono_W0 f hstep ((frameAt word).parents.even.den) K N
    (fun j => earlierP word (qry word (H j))) hΦ j hj hjN
  linarith

/-- **Monotonicity, phase one** (`η = +1`), from the named (1a), (1b), (2a), (2c). The points are `reflH (H j)`. -/
theorem psi_mono_W1 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (base : ℤ → Site)
    (H : ℕ → Site) (N : ℕ)
    (f : ℤ → ℤ) (hstep : ∀ k, f k ≤ f (k + 1))
    (hIdx : ∀ j : ℕ, 1 ≤ j → j < N → (qry word (ArcPsi.reflH word (H j))).2 = (frameAt word).child.den - 1 - (j : ℤ))
    (hClass : ∀ j : ℕ, 1 ≤ j → j < N →
      qry word (ArcPsi.reflH word (H j)) = FreeEnum.vAt (frameAt (conjWord word)) base (qry word (ArcPsi.reflH word (H j))).2 ∨
      ∃ m : ℤ, qry word (ArcPsi.reflH word (H j)) = ((1 : ℤ), (0 : ℤ)) + m • Vdeck (frameAt (conjWord word)) ∧
        (qry word (ArcPsi.reflH word (H j))).2 = m * FreeEnum.period (frameAt (conjWord word)))
    (hVal : ∀ k : ℤ, earlierP word (FreeEnum.vAt (frameAt (conjWord word)) base k) = f k)
    (hHval : ∀ m : ℤ, earlierP word (((1 : ℤ), (0 : ℤ)) + m • Vdeck (frameAt (conjWord word))) =
      f (m * FreeEnum.period (frameAt (conjWord word)))) :
    ∀ j : ℕ, 1 ≤ j → j + 1 < N →
      sheetPsi word (ArcPsi.reflH word (H j)) ≤ sheetPsi word (ArcPsi.reflH word (H (j + 1))) := by
  obtain ⟨K, hK⟩ := psi_eq_K h hSE
  have hΦ : ∀ j : ℕ, 1 ≤ j → j < N →
      earlierP word (qry word (ArcPsi.reflH word (H j))) = f ((frameAt word).child.den - 1 - (j : ℤ)) := by
    intro j hj hjN
    rcases hClass j hj hjN with h1 | ⟨m, h1, h2⟩
    · rw [← hIdx j hj hjN]
      rw [← hVal (qry word (ArcPsi.reflH word (H j))).2]
      congr 1
    · rw [← hIdx j hj hjN, h2, ← hHval m, ← h1]
  intro j hj hjN
  rw [hK (ArcPsi.reflH word (H j)), hK (ArcPsi.reflH word (H (j + 1)))]
  have hm := PsiMono.mono_W1 f hstep ((frameAt word).child.den) K N
    (fun j => earlierP word (qry word (ArcPsi.reflH word (H j)))) hΦ j hj hjN
  linarith

end FLatticePaper.PsiMonoReal
