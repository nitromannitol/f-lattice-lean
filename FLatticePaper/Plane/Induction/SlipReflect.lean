import FLatticePaper.Plane.Induction.RepInputs
import FLatticePaper.Plane.Induction.SheetReflection
import FLatticePaper.Plane.Induction.ChartCommon

/-! Task 68: the reflection `R z = centre − z` and the two signs of the slip.

* `D_{−σ}(R z) = D_σ(z) − 2` (`slip_reflect`, checked numerically: `scripts/slip_reflect_check.py`), since the packet
  reflection `F (R z) = F z − tGrade z + k` and `tGrade σ = −2`.
* `R` preserves the Laplacian (`laplacian_reflect`), the closed polygon `E` (`reflect_mem_closedPolygon`), and turns a
  rising pair for `σ` into a rising pair for `−σ` at `(R c, R i)` (`rising_reflect`).
* `Ψ (R z) = −Ψ z` (`sheetDiffW_reflect`, the sheet exchange).

The cases for a rising pair `(c, i)` with `c ∈ E`: both `Ψ ≥ 1` is the chart exclusion (`chart_excluded_of_bounds`,
proved); both `Ψ ≤ −1` reflects to a rising pair for `−σ` with both `Ψ ≥ 1`; a tie is a named leaf; mixed signs are
impossible by the unit bound. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- `centre − incomingNeg z = incomingPos (centre − z)`: the reflection swaps the two inputs. -/
theorem ChildFrame.reflect_input_neg (frame : ChildFrame) (z : Site) :
    frame.centre - FLatticePaper.incomingNeg z = FLatticePaper.incomingPos (frame.centre - z) := by
  have hiff := frame.evenSite_centre_sub z
  unfold FLatticePaper.incomingNeg FLatticePaper.incomingPos
  by_cases he : EvenSite z
  · rw [if_pos he, if_pos (hiff.2 he)]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_sub]; ring
    · simp only [Prod.snd_sub]
  · rw [if_neg he, if_neg (fun h => he (hiff.1 h))]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_sub]
    · simp only [Prod.snd_sub]; ring

theorem ChildFrame.reflect_input_pos (frame : ChildFrame) (z : Site) :
    frame.centre - FLatticePaper.incomingPos z = FLatticePaper.incomingNeg (frame.centre - z) := by
  have hiff := frame.evenSite_centre_sub z
  unfold FLatticePaper.incomingNeg FLatticePaper.incomingPos
  by_cases he : EvenSite z
  · rw [if_pos he, if_pos (hiff.2 he)]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_sub]; ring
    · simp only [Prod.snd_sub]
  · rw [if_neg he, if_neg (fun h => he (hiff.1 h))]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_sub]
    · simp only [Prod.snd_sub]; ring

/-- **The reflected slip (task 68):** `D_{−σ}(R z) = D_σ(z) − 2`. -/
theorem ChildFrame.slip_reflect {F : Field} (frame : ChildFrame) (hP : frame.Packet F) (z : Site) :
    F (frame.centre - z) - F (frame.centre - z + -frame.shortShift) =
      (F z - F (z + frame.shortShift)) - 2 := by
  have e : frame.centre - z + -frame.shortShift = frame.centre - (z + frame.shortShift) := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.fst_sub, Prod.fst_neg]; ring
    · simp only [Prod.snd_add, Prod.snd_sub, Prod.snd_neg]; ring
  rw [e, hP.reflection z, hP.reflection (z + frame.shortShift), frame.tGrade_add z frame.shortShift,
    frame.tGrade_shortShift]
  ring

/-- `R` preserves the Laplacian. -/
theorem ChildFrame.laplacian_reflect {F : Field} (frame : ChildFrame) (hP : frame.Packet F) (z : Site) :
    laplacian F (frame.centre - z) = laplacian F z := by
  unfold laplacian
  rw [← frame.reflect_input_pos z, ← frame.reflect_input_neg z]
  rw [hP.reflection (FLatticePaper.incomingPos z), hP.reflection (FLatticePaper.incomingNeg z),
    hP.reflection z]
  linarith [frame.tGrade_incomingNeg_add_pos z]

theorem ChildFrame.reflect_mem_closedPolygon (frame : ChildFrame) {z : Site} (hz : z ∈ frame.closedPolygon) :
    frame.centre - z ∈ frame.closedPolygon := by
  have hiff := frame.evenSite_centre_sub z
  have tR : frame.tGrade (frame.centre - z) = frame.tGrade frame.centre - frame.tGrade z := by
    unfold ChildFrame.tGrade
    simp only [Prod.fst_sub, Prod.snd_sub]
    ring
  have sR : frame.sGrade (frame.centre - z) = frame.sGrade frame.centre - frame.sGrade z := by
    unfold ChildFrame.sGrade
    simp only [Prod.fst_sub, Prod.snd_sub]
    ring
  have hT := frame.tGrade_centre
  have hS := frame.sGrade_centre
  by_cases he : EvenSite z
  · obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := ChildFrame.closedPolygon_even_bounds (frame := frame) he hz
    refine ChildFrame.mem_closedPolygon_of_even (frame := frame) (hiff.2 he) ⟨?_, ?_⟩ ⟨?_, ?_⟩
    · rw [tR, hT]
      omega
    · rw [tR, hT]
      omega
    · rw [sR, hS]
      omega
    · rw [sR, hS]
      omega
  · obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := ChildFrame.closedPolygon_odd_bounds (frame := frame) he hz
    refine ChildFrame.mem_closedPolygon_of_odd (frame := frame) (fun h => he (hiff.1 h)) ⟨?_, ?_⟩ ⟨?_, ?_⟩
    · rw [tR, hT]
      omega
    · rw [tR, hT]
      omega
    · rw [sR, hS]
      omega
    · rw [sR, hS]
      omega

/-- A rising pair for `σ` reflects to a rising pair for `−σ` at `(R c, R i)`. -/
theorem ChildFrame.rising_reflect {G : Field} (frame : ChildFrame) (hP : frame.Packet G) {c i : Site}
    (hr : RisingBlackPair G frame.shortShift c i) :
    RisingBlackPair G (-frame.shortShift) (frame.centre - c) (frame.centre - i) := by
  obtain ⟨hin, hlap, hpar, hlap', hslip⟩ := hr
  have e : frame.centre - c + -frame.shortShift = frame.centre - (c + frame.shortShift) := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.fst_sub, Prod.fst_neg]; ring
    · simp only [Prod.snd_add, Prod.snd_sub, Prod.snd_neg]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rcases hin with h1 | h1
    · right
      rw [h1]
      exact frame.reflect_input_neg c
    · left
      rw [h1]
      exact frame.reflect_input_pos c
  · rw [frame.laplacian_reflect hP]
    exact hlap
  · rw [frame.slip_reflect hP c]
    omega
  · rw [e, frame.laplacian_reflect hP]
    exact hlap'
  · unfold slipIncrement at hslip ⊢
    dsimp only at hslip ⊢
    rw [frame.slip_reflect hP i, frame.slip_reflect hP c]
    linarith

/-- The sheet exchange: `Ψ (R z) = −Ψ z`. -/
theorem sheetDiffW_reflect {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hG : (frameAt (conjWord word)).Packet (standardField (conjWord word))) (z : Site) :
    sheetDiffW word ((frameAt word).centre - z) = -sheetDiffW word z :=
  sheetDiff_antisymm_of_exchange (frameAt word) _ (sheetExchange_of_packet h hG) z

/-- The chart exclusion for a rising pair with centre in `E` and both strict bounds `Ψ ≥ 1` (the cover's argument, with
the retention `hret` derived from the centre bound). -/
theorem chart_excluded_of_bounds {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpk : (frameAt word).Packet (standardField word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    {c i : Site} (hr : RisingBlackPair (standardField word) (frameAt word).shortShift c i)
    (hcE : c ∈ (frameAt word).closedPolygon) (hΨc : 1 ≤ sheetDiffW word c) (hΨi : 1 ≤ sheetDiffW word i) :
    False := by
  have hn3 : 3 ≤ (frameAt word).child.num := child_num_ge_three h
  have hnd : (frameAt word).child.num + 2 ≤ (frameAt word).child.den := by
    have := (frameAt word).child_facts.2.2.1
    omega
  have hiE := (frameAt word).rising_centre_input_mem hpk hcE hr
  have hEdge : Edge i c := hr.1
  have hret := sheetPolicyA_of_strict h hSE hpk P hcE hr hΨc
  by_cases hnc : (frameAt word).tGrade c - 2 ≥
      (if EvenSite c then 2 else (frameAt word).child.num) - (frameAt word).child.periodDenominator
  · by_cases hni : (frameAt word).tGrade i - 2 ≥
        (if EvenSite i then 2 else (frameAt word).child.num) - (frameAt word).child.periodDenominator
    · rcases common_chart_option (frameAt word) hn3 hnd hcE hiE hEdge hnc hni with ⟨hcs, his⟩ | ⟨hcq, hiq⟩
      · exact first_chart_excluded h hSE P
          (firstChart_witness h hSE P hcE hiE hEdge hcs his hΨc hret) hr
      · exact adjacent_chart_excluded h hSE P
          (adjacentChart_witness h hSE hpk P hcE hiE hcq hiq (by linarith) hΨi hret) hr
    · exact (frameAt word).not_rising_of_input_exit hpk hn3 hnd
        ⟨hcE, hiE, hEdge, not_le.mp hni⟩ hr
  · exact (frameAt word).not_rising_of_centre_exit hpk hn3 hnd
      ⟨hcE, hiE, hEdge, not_le.mp hnc⟩ hr

/-- **The reduction of `NoBlackPairRise` (task 68).** Mixed signs are impossible by the unit bound. Both strict
positive is the chart exclusion (proved). Both negative reflects (`rising_reflect`, `sheetDiffW_reflect`) to the
`−σ`-pair with both bounds positive: the leaf `hNeg`, the A-case for `−σ`. A tie at the centre or the input is the leaf
`hTie`. -/
theorem noBlackPairRise_of_signs {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpk : (frameAt word).Packet (standardField word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hNeg : ∀ c i, RisingBlackPair (standardField word) (-(frameAt word).shortShift) c i →
      c ∈ (frameAt word).closedPolygon → 1 ≤ sheetDiffW word c → 1 ≤ sheetDiffW word i → False)
    (hTie : ∀ c i, RisingBlackPair (standardField word) (frameAt word).shortShift c i →
      c ∈ (frameAt word).closedPolygon → (sheetDiffW word c = 0 ∨ sheetDiffW word i = 0) → False) :
    NoBlackPairRise (standardField word) (frameAt word).shortShift := by
  refine (frameAt word).noBlackPairRise_of_E hpk ?_
  intro c i hr hcE
  have hunit := sheetDiff_unit h hSE c i hr.1
  by_cases hA : 1 ≤ sheetDiffW word c ∧ 1 ≤ sheetDiffW word i
  · exact chart_excluded_of_bounds h hSE hpk P hr hcE hA.1 hA.2
  by_cases hT : sheetDiffW word c = 0 ∨ sheetDiffW word i = 0
  · exact hTie c i hr hcE hT
  by_cases hN : sheetDiffW word c ≤ -1 ∧ sheetDiffW word i ≤ -1
  · have hr' := (frameAt word).rising_reflect hpk hr
    refine hNeg _ _ hr' ((frameAt word).reflect_mem_closedPolygon hcE) ?_ ?_
    · rw [sheetDiffW_reflect h hSE.packet]
      omega
    · rw [sheetDiffW_reflect h hSE.packet]
      omega
  · exfalso
    omega

end FLatticePaper.Induction
