import FLatticePaper.Plane.Induction.NegTieTranslate
import FLatticePaper.Plane.Induction.NegTieNonfree
import FLatticePaper.Plane.Induction.NegTieFreeV

/-! Task 72 (hNegTie, the reduction to the V block Q21).

`negTie_false_of_V_block`: the negative tied target is impossible, given only the named V-block input `hQ21` (no deck translate of the
root in the H cut of the conjugate frame, the old V star of Q3 paragraph 8). The cases of the root `zTurn (c − sheetShift)`:
* no deck translate is free: `negTie_drop_of_nonfree` (committed);
* a deck translate is free in the V cut: `negTie_translate_V_false` (the translate case, with `jumpA` of the parity input `0`);
* a deck translate is free in the H cut: the V-block step, the named input `hQ21`. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- **The negative tied target reduced to the V block (Q21).** -/
theorem negTie_false_of_V_block {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpk : (frameAt word).Packet (standardField word))
    (hpar : FLatticePaper.W1Seeds.SeedFields (conjWord word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num
      (frameAt (conjWord word)).child.den (standardField (conjWord word)))
    (hslip : ∀ z ∈ (frameAt word).closedPolygon,
      0 ≤ standardField word z - standardField word (z + (frameAt word).shortShift) ∧
        standardField word z - standardField word (z + (frameAt word).shortShift) ≤ 2)
    {c i j : Site} (hr : RisingBlackPair (standardField word) (-(frameAt word).shortShift) c i)
    (hcE : c ∈ (frameAt word).closedPolygon) (hiE : i ∈ (frameAt word).closedPolygon)
    (hcu : c + (frameAt word).uq ∈ (frameAt word).closedPolygon)
    (hiu : i + (frameAt word).uq ∈ (frameAt word).closedPolygon)
    (hΨc : sheetDiffW word c = 0) (hj : FLatticePaper.Edge j c) (hjΨ : sheetDiffW word j ≤ -1)
    (hΨi : 0 ≤ sheetDiffW word i)
    (hQ21 : ∀ v ∈ (frameAt (conjWord word)).child.modifiedDeck.span,
      zTurn (c - (frameAt word).sheetShift) + v ∈ (frameAt (conjWord word)).freeH → False) : False := by
  by_cases hnf : Nonfree (frameAt (conjWord word)) (zTurn (c - (frameAt word).sheetShift))
  · exact negTie_drop_of_nonfree h hSE hpk P hW1 hslip hr hcE hiE hcu hiu hΨc hj hjΨ hΨi hnf
  · have hex : ∃ v ∈ (frameAt (conjWord word)).child.modifiedDeck.span,
        zTurn (c - (frameAt word).sheetShift) + v ∈ (frameAt (conjWord word)).freeH ∪ (frameAt (conjWord word)).freeV := by
      by_contra hc
      exact hnf (fun v hv hmem => hc ⟨v, hv, hmem⟩)
    obtain ⟨v, hv, hfree⟩ := hex
    -- the parity input: `i − sheetShift` is an input of `c − sheetShift`
    have hsn : EvenSite (frameAt word).sheetShift := (frameAt word).evenSite_sheetShift
    have hsneg : ((-(frameAt word).sheetShift).1 + (-(frameAt word).sheetShift).2) % 2 = 0 := by
      have hs := hsn
      unfold EvenSite at hs
      simp only [Prod.fst_neg, Prod.snd_neg]
      omega
    have hyx : i - (frameAt word).sheetShift = incomingNeg (c - (frameAt word).sheetShift) ∨
        i - (frameAt word).sheetShift = incomingPos (c - (frameAt word).sheetShift) := by
      rcases hr.1 with h1 | h1
      · left
        rw [sub_eq_add_neg c, incomingNeg_add_even _ _ hsneg, h1, sub_eq_add_neg]
      · right
        rw [sub_eq_add_neg c, incomingPos_add_even _ _ hsneg, h1, sub_eq_add_neg]
    obtain ⟨hx, hy⟩ := negTie_jumps h hSE hpk P hslip hr hcE hiE hcu hiu hΨc hj hjΨ hΨi
    rcases hfree with hH | hV
    · exact hQ21 v hv hH
    · obtain ⟨i', j', rfl⟩ := hv
      exact negTie_translate_V_false h hSE hpar hx hy hyx hV

end FLatticePaper.Induction
