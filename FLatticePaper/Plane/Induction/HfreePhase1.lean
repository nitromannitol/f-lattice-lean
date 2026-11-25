import FLatticePaper.Plane.Induction.HfreePhase0
import FLatticePaper.Plane.Induction.PsiMonoPhase1
import FLatticePaper.Plane.Induction.H0Price1
import FLatticePaper.Plane.Induction.FreeVCover

/-! The phase-one premise `hfreeP` of the word policy, and the phase split of `hfreeP`.

Phase one (`eps = 1`), for a free-presc input `i` of a free white `c`, `i = c + t + prescribedH` (H branch) or `c + t + prescribedV`:
* H branch, root `x ≠ hFirst`: `P(x + prescribedH η x) ≤ P(x)` from the two phase-one price formulas (`price_neighbour_W1`,
  `price_W1_trace`) and the phase-one Ψ monotonicity (`psi_mono_phase1`, which takes the conjugate's games `hG` and base `hbase`).
* H branch, root `H_0`: the price equality at `H_0 + (0,−η)` (`price_H0_eq_of_corner`), where the N = 1 corner is the named pair
  `Ψ(reflH(H_0 + (0,−η))) = 0` and `A(reflH(H_0 + (0,−η))) = 0` (for η = −1 with N = 1; for the other cases `hN2` gives the pair).
* V branch: `FreeVCover.freePresc_V_price_eq`, which is phase-independent.

Phase zero is `HfreePhase0.hfreeP_W0`, with the conjugate's games and base. -/

namespace FLatticePaper.HfreePhase1

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1Step FLatticePaper.W1MSheet FLatticePaper.FreePolicy
  FLatticePaper.PriceInputs

/-- The cut base of a frame: one free V white per ordinate `r ∈ [0, period)`, with that ordinate (`CutRowsAll`, unconditional). -/
theorem conj_base (frame : ChildFrame) :
    ∃ base : ℤ → Site, ∀ r : ℤ, 0 ≤ r → r < FreeEnum.period frame → base r ∈ frame.freeV ∧ (base r).2 = r := by
  have hex : ∀ r : ℤ, ∃ x : ℤ, 0 ≤ r → r < FreeEnum.period frame → (x, r) ∈ frame.freeV := by
    intro r
    by_cases hr : 0 ≤ r ∧ r < FreeEnum.period frame
    · obtain ⟨x, hx, -⟩ := FLatticePaper.CutRowsAll.cut_one_per_ordinate_all frame r hr.1 hr.2
      exact ⟨x, fun _ _ => hx⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hr⟩
  choose xs hxs using hex
  exact ⟨fun r => (xs r, r), fun r h1 h2 => ⟨hxs r h1 h2, rfl⟩⟩

/-- The H_0 price equality at phase one, from the corner pair at `reflH(H_0 + (0,−η))`: `Ψ = 0` and `A = 0`. -/
theorem price_H0_eq_of_corner {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hW1 : (frameAt word).eps = 1) {η : ℤ} (hη : η = 1 ∨ η = -1)
    (hPsi : sheetPsi word (FLatticePaper.ArcPsi.reflH word (hFirst + (0, -η))) = 0)
    (hA0 : (frameAt word).sheetA (FqW word) (FLatticePaper.ArcPsi.reflH word (hFirst + (0, -η))) = 0) :
    (frameAt word).price (standardField word) (hFirst + (0, -η)) =
      (frameAt word).price (standardField word) hFirst := by
  obtain ⟨hN1, hND, hD2, hnq, hdq, hn_eq, hd_eq, heps, -⟩ := PriceInputs.pdata h
  have hpk := packet_of_strong h hSE
  have hF0 := FLatticePaper.PsiMonoOffset.hFirst_mem_freeH (frameAt word)
  have hz0 := FLatticePaper.FreeHPrice.neighbour_F_zero (frameAt word) hpk.strips hF0 hη
  rw [ChildFrame.prescribedH_hFirst] at hz0
  have hR := refl_tip (frameAt word) (standardField word) hpk (hFirst + (0, -η))
  have hcl := FLatticePaper.TipReflect.tip_closed_reflH_W1 (frameAt word) hN1 hND hD2 hnq hdq hn_eq hd_eq heps hW1 hF0 hη
  have hFV := standardField_eq_sheetMin_of_strong h hSE hcl
  have hP := FLatticePaper.EHPrice.price_W1 h hSE hW1 (hFirst + (0, -η)) hz0 hR hA0 hFV
  have hH : (frameAt word).price (standardField word) hFirst = (frameAt word).cutPrice :=
    FLatticePaper.W1BottomValue.price_hFirst h hSE
  rw [hP, hPsi, hH]
  norm_num

/-- The H_0 neighbour does not increase the price at phase one: equality when `hN2` holds (`H0Price1`), and otherwise (η = −1,
N = 1) the named corner pair. -/
theorem price_H0_le_W1 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hW1 : (frameAt word).eps = 1) {η : ℤ} (hη : η = 1 ∨ η = -1)
    (hcorner : η = -1 → (frameAt word).parents.odd.num = 1 →
      sheetPsi word (FLatticePaper.ArcPsi.reflH word (hFirst + (0, -η))) = 0 ∧
        (frameAt word).sheetA (FqW word) (FLatticePaper.ArcPsi.reflH word (hFirst + (0, -η))) = 0) :
    (frameAt word).price (standardField word) (hFirst + (0, -η)) ≤
      (frameAt word).price (standardField word) hFirst := by
  by_cases hN2 : η = 1 ∨ 2 ≤ (frameAt word).parents.odd.num
  · exact (H0Price1.price_H0_neighbour_W1 h hSE hW1 η hη hN2).le
  · have hNpos : 0 < (frameAt word).parents.odd.num := by
      obtain ⟨hN1, -⟩ := PriceInputs.pdata h
      omega
    obtain ⟨hne, hlt⟩ := not_or.mp hN2
    have hη' : η = -1 := by omega
    have hN1' : (frameAt word).parents.odd.num = 1 := by omega
    obtain ⟨hPsi, hA0⟩ := hcorner hη' hN1'
    exact (price_H0_eq_of_corner h hSE hW1 hη hPsi hA0).le

/-- **The H branch at phase one**: a free H root's prescribed image has price at most the root's. -/
theorem price_le_W1 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hW1 : (frameAt word).eps = 1) (hG : GamesWithRank (conjWord word))
    {base : ℤ → Site}
    (hbase : ∀ r : ℤ, 0 ≤ r → r < FreeEnum.period (frameAt (conjWord word)) →
      base r ∈ (frameAt (conjWord word)).freeV ∧ (base r).2 = r)
    {η : ℤ} (hη : η = 1 ∨ η = -1)
    (hcorner : η = -1 → (frameAt word).parents.odd.num = 1 →
      sheetPsi word (FLatticePaper.ArcPsi.reflH word (hFirst + (0, -η))) = 0 ∧
        (frameAt word).sheetA (FqW word) (FLatticePaper.ArcPsi.reflH word (hFirst + (0, -η))) = 0)
    {x : Site} (hx : x ∈ (frameAt word).freeH) :
    (frameAt word).price (standardField word) (x + (frameAt word).prescribedH η x) ≤
      (frameAt word).price (standardField word) x := by
  by_cases hx1 : x = hFirst
  · subst hx1
    rw [ChildFrame.prescribedH_hFirst]
    exact price_H0_le_W1 h hSE hW1 hη hcorner
  · rw [FLatticePaper.PhaseOnePrice.price_neighbour_W1 h hSE hW1 hx hx1 hη, price_W1_trace h hSE hW1 x hx]
    have hpsi := FLatticePaper.PsiMonoPhase1.psi_mono_phase1 h hSE hW1 hG hbase hx hx1 η
    have hm : min 0 (sheetPsi word (FLatticePaper.ArcPsi.reflH word x) - 1) ≤
        min 0 (sheetPsi word (FLatticePaper.ArcPsi.reflH word (x + (frameAt word).prescribedH η x)) - 1) :=
      min_le_min le_rfl (by linarith)
    linarith

/-- **The phase-one `hfreeP`.** A free-presc input of a free white has price at most the price of the white. -/
theorem hfreeP_W1 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hW1 : (frameAt word).eps = 1) (hG : GamesWithRank (conjWord word))
    {base : ℤ → Site}
    (hbase : ∀ r : ℤ, 0 ≤ r → r < FreeEnum.period (frameAt (conjWord word)) →
      base r ∈ (frameAt (conjWord word)).freeV ∧ (base r).2 = r)
    {η : ℤ} (hη : η = 1 ∨ η = -1)
    (hcorner : η = -1 → (frameAt word).parents.odd.num = 1 →
      sheetPsi word (FLatticePaper.ArcPsi.reflH word (hFirst + (0, -η))) = 0 ∧
        (frameAt word).sheetA (FqW word) (FLatticePaper.ArcPsi.reflH word (hFirst + (0, -η))) = 0)
    {c i : Site} (hcp : FreePresc (frameAt word) η c i) :
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
    have hle := price_le_W1 h hSE hW1 hG hbase hη hcorner hx
    linarith
  · rw [hi]
    exact (FLatticePaper.FreeVCover.freePresc_V_price_eq (frameAt word) hpk hη ht hx).le

/-- **The `hfreeP` of the word, by phase.** Phase zero is `HfreePhase0.hfreeP_W0` (the conjugate's games and base); phase one is
`hfreeP_W1`, which needs the named N = 1 corner `hcorner` (only at phase one). -/
theorem hfreeP_of_phases {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hG : GamesWithRank (conjWord word))
    {base : ℤ → Site}
    (hbase : ∀ r : ℤ, 0 ≤ r → r < FreeEnum.period (frameAt (conjWord word)) →
      base r ∈ (frameAt (conjWord word)).freeV ∧ (base r).2 = r)
    {η : ℤ} (hη : η = 1 ∨ η = -1)
    (hcorner : (frameAt word).eps = 1 → η = -1 → (frameAt word).parents.odd.num = 1 →
      sheetPsi word (FLatticePaper.ArcPsi.reflH word (hFirst + (0, -η))) = 0 ∧
        (frameAt word).sheetA (FqW word) (FLatticePaper.ArcPsi.reflH word (hFirst + (0, -η))) = 0)
    {c i : Site} (hcp : FreePresc (frameAt word) η c i) :
    (frameAt word).price (standardField word) i ≤ (frameAt word).price (standardField word) c := by
  rcases ChildFrame.eps_unit (frameAt word) with he | he
  · exact hfreeP_W1 h hSE he hG hbase hη (hcorner he) hcp
  · exact FLatticePaper.HfreePhase0.hfreeP_W0 h hSE he hG hbase hη hcp

end FLatticePaper.HfreePhase1
