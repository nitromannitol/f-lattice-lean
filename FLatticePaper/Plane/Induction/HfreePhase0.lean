import FLatticePaper.Plane.Induction.PsiMonoOffset
import FLatticePaper.Plane.Induction.H0Neigh
import FLatticePaper.Plane.Induction.FreeHPrice
import FLatticePaper.Plane.Induction.FreeVCover
import FLatticePaper.Plane.Induction.ChainDeck
import FLatticePaper.Plane.Induction.TieReduce

/-! The phase-zero premise `hfreeP` of the word policy (`WordPolicy.word_price_nonincreasing`).

For a free H root `x` (any `x ∈ freeH`, including `H_0` for both signs), `Ψ(x) ≤ Ψ(x + prescribedH η x)` (`psi_le_W0`), hence
`P(x + prescribedH η x) ≤ P(x)` (`price_le_W0`). For a free-presc input `i = c + prescribedH η x` with `x = c + t`, `t = combine a b`, the
price shifts by `a` on both `c` and `i`: `P(i) = P(x + prescribedH η x) + a ≤ P(x) + a = P(c)`. The V branch is `freePresc_V_price_eq`. -/

namespace FLatticePaper.HfreePhase0

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1Step FLatticePaper.W1MSheet FLatticePaper.FreePolicy

theorem psi_le_W0 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hW0 : (frameAt word).eps = -1) (hG : GamesWithRank (conjWord word))
    {base : ℤ → Site}
    (hbase : ∀ r : ℤ, 0 ≤ r → r < FreeEnum.period (frameAt (conjWord word)) →
      base r ∈ (frameAt (conjWord word)).freeV ∧ (base r).2 = r)
    {x : Site} (hx : x ∈ (frameAt word).freeH) {η : ℤ} (hη : η = 1 ∨ η = -1) :
    sheetPsi word x ≤ sheetPsi word (x + (frameAt word).prescribedH η x) := by
  by_cases hx1 : x = hFirst
  · subst hx1
    rcases hη with rfl | rfl
    · have h0 := FLatticePaper.H0Neigh.sheetPsi_H0_neighbour_W0 h hSE hW0 1 (Or.inl rfl)
      have hz : sheetPsi word FLatticePaper.Induction.hFirst = 0 :=
        FLatticePaper.PsiCalibration.sheetPsi_H0_W0 word h hSE hW0
      simp only [ChildFrame.prescribedH_hFirst, hz, h0, le_refl]
    · exact FLatticePaper.PsiMonoOffset.psi_mono_H0_neg h hSE hW0 hG hbase (-1) rfl
  · exact FLatticePaper.PsiMonoOffset.psi_mono_phase0 h hSE hW0 hG hbase hx η
      (fun hodd => pH_odd' (frameAt word) η hodd hx1)

theorem price_le_W0 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hW0 : (frameAt word).eps = -1) (hG : GamesWithRank (conjWord word))
    {base : ℤ → Site}
    (hbase : ∀ r : ℤ, 0 ≤ r → r < FreeEnum.period (frameAt (conjWord word)) →
      base r ∈ (frameAt (conjWord word)).freeV ∧ (base r).2 = r)
    {x : Site} (hx : x ∈ (frameAt word).freeH) {η : ℤ} (hη : η = 1 ∨ η = -1) :
    (frameAt word).price (standardField word) (x + (frameAt word).prescribedH η x) ≤
      (frameAt word).price (standardField word) x := by
  rw [FLatticePaper.FreeHPrice.price_neighbour_W0 h hSE hW0 hx hη, FLatticePaper.PriceInputs.price_W0_trace h hSE hW0 x hx]
  have hpsi := psi_le_W0 h hSE hW0 hG hbase hx hη
  have hm : min 0 (sheetPsi word x - 1) ≤ min 0 (sheetPsi word (x + (frameAt word).prescribedH η x) - 1) :=
    min_le_min le_rfl (by linarith)
  linarith

/-- **The phase-zero `hfreeP`.** A free-presc input of a free white has price at most the price of the white. -/
theorem hfreeP_W0 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hW0 : (frameAt word).eps = -1) (hG : GamesWithRank (conjWord word))
    {base : ℤ → Site}
    (hbase : ∀ r : ℤ, 0 ≤ r → r < FreeEnum.period (frameAt (conjWord word)) →
      base r ∈ (frameAt (conjWord word)).freeV ∧ (base r).2 = r)
    {η : ℤ} (hη : η = 1 ∨ η = -1) {c i : Site} (hcp : FreePresc (frameAt word) η c i) :
    (frameAt word).price (standardField word) i ≤ (frameAt word).price (standardField word) c := by
  have hpk := packet_of_strong h hSE
  obtain ⟨t, ht, hcase⟩ := hcp
  rcases hcase with ⟨hx, hi⟩ | ⟨hx, hi⟩
  · obtain ⟨a, b, rfl⟩ := ht
    have h1 := FLatticePaper.ChainDeck.price_combine (frameAt word) hpk a b c
    have h2 := FLatticePaper.ChainDeck.price_combine (frameAt word) hpk a b i
    have e : i + (frameAt word).child.modifiedDeck.combine a b =
        (c + (frameAt word).child.modifiedDeck.combine a b) +
          (frameAt word).prescribedH η (c + (frameAt word).child.modifiedDeck.combine a b) := by
      rw [hi]
      abel
    rw [e] at h2
    have hle := price_le_W0 h hSE hW0 hG hbase hx hη
    linarith
  · rw [hi]
    exact (FLatticePaper.FreeVCover.freePresc_V_price_eq (frameAt word) hpk hη ht hx).le

end FLatticePaper.HfreePhase0
