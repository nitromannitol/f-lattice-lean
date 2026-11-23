import FLatticePaper.Plane.Induction.NegChart

/-! Task 69 (b): ties in option 2 (`c − εU_q, i − εU_q ∈ E`) for a rising `σ` pair.

* A centre star with `Ψ ≤ 0` (the centre and its inputs) reflects to a rising `−σ` pair whose star has `Ψ ≥ 0`, which
  `neg_adjacent_nonneg` excludes (`plus_adjacent_nonpos_excluded`).
* A strict target `Ψ i ≥ 1` with a centre star `Ψ ≥ 0` is excluded by the positive adjacent chart, with the centre's retention
  from `sheetPolicyA_of_nonneg` (`plus_adjacent_target_excluded`).

The remaining option-2 ties (a centre star with a `Ψ = −1` input and a tied endpoint, or a tied target under a strict centre)
are not covered: they need the winner-retention argument of the fix's l.13 and the tied-target statement of l.21. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- A rising `σ` pair in option 2 whose centre star has `Ψ ≤ 0` is excluded (reflect to the negative lemma). -/
theorem plus_adjacent_nonpos_excluded {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpk : (frameAt word).Packet (standardField word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hslip : ∀ z ∈ (frameAt word).closedPolygon,
      0 ≤ standardField word z - standardField word (z + (frameAt word).shortShift) ∧
        standardField word z - standardField word (z + (frameAt word).shortShift) ≤ 2)
    {c i : Site} (hr : RisingBlackPair (standardField word) (frameAt word).shortShift c i)
    (hcE : c ∈ (frameAt word).closedPolygon) (hiE : i ∈ (frameAt word).closedPolygon)
    (hcq : c - ((frameAt word).eps * (frameAt word).parents.even.den,
      (frameAt word).eps * (frameAt word).parents.even.num) ∈ (frameAt word).closedPolygon)
    (hiq : i - ((frameAt word).eps * (frameAt word).parents.even.den,
      (frameAt word).eps * (frameAt word).parents.even.num) ∈ (frameAt word).closedPolygon)
    (hΨc : sheetDiffW word c ≤ 0) (hstarNeg : ∀ j, Edge j c → sheetDiffW word j ≤ 0) : False := by
  have hτ : (frameAt word).tGrade (frameAt word).shortShift % 2 = 0 := by
    rw [(frameAt word).tGrade_shortShift]
    norm_num
  have hr' := (frameAt word).rising_reflect_gen hpk (frameAt word).shortShift hτ hr
  have hcE' := (frameAt word).reflect_mem_closedPolygon hcE
  have hiE' := (frameAt word).reflect_mem_closedPolygon hiE
  have hcu : (frameAt word).centre - c + ((frameAt word).eps * (frameAt word).parents.even.den,
      (frameAt word).eps * (frameAt word).parents.even.num) ∈ (frameAt word).closedPolygon := by
    have h3 := (frameAt word).reflect_mem_iff.mpr hcq
    have e : (frameAt word).centre - (c - ((frameAt word).eps * (frameAt word).parents.even.den,
        (frameAt word).eps * (frameAt word).parents.even.num)) =
        (frameAt word).centre - c + ((frameAt word).eps * (frameAt word).parents.even.den,
          (frameAt word).eps * (frameAt word).parents.even.num) := by
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_sub, Prod.fst_add]
        ring
      · simp only [Prod.snd_sub, Prod.snd_add]
        ring
    rwa [e] at h3
  have hiu : (frameAt word).centre - i + ((frameAt word).eps * (frameAt word).parents.even.den,
      (frameAt word).eps * (frameAt word).parents.even.num) ∈ (frameAt word).closedPolygon := by
    have h3 := (frameAt word).reflect_mem_iff.mpr hiq
    have e : (frameAt word).centre - (i - ((frameAt word).eps * (frameAt word).parents.even.den,
        (frameAt word).eps * (frameAt word).parents.even.num)) =
        (frameAt word).centre - i + ((frameAt word).eps * (frameAt word).parents.even.den,
          (frameAt word).eps * (frameAt word).parents.even.num) := by
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_sub, Prod.fst_add]
        ring
      · simp only [Prod.snd_sub, Prod.snd_add]
        ring
    rwa [e] at h3
  -- the star of the reflected centre `R c`: every neighbour `j` of `R c` reflects to a neighbour of `c`
  have hstar' : ∀ j, Edge j ((frameAt word).centre - c) → 0 ≤ sheetDiffW word j := by
    intro j hj
    have hj' := reflect_edge_even _ (frameAt word).evenSite_centre hj
    rw [sub_sub_cancel] at hj'
    have h0 := hstarNeg _ hj'
    rw [sheetDiffW_reflect h hSE.packet] at h0
    linarith
  have hΨRc : 0 ≤ sheetDiffW word ((frameAt word).centre - c) := by
    rw [sheetDiffW_reflect h hSE.packet]
    linarith
  exact neg_adjacent_nonneg h hSE hpk P hslip hr' hcE' hiE' hcu hiu hΨRc hstar'

/-- A rising `σ` pair in option 2 with a strict target `Ψ i ≥ 1`, a centre `Ψ c ≥ 0` and a centre star `Ψ ≥ 0` is excluded
(the positive adjacent chart, with the centre's retention `sheetPolicyA_of_nonneg`). -/
theorem plus_adjacent_target_excluded {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpk : (frameAt word).Packet (standardField word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    {c i : Site} (hr : RisingBlackPair (standardField word) (frameAt word).shortShift c i)
    (hcE : c ∈ (frameAt word).closedPolygon) (hiE : i ∈ (frameAt word).closedPolygon)
    (hcq : c - ((frameAt word).eps * (frameAt word).parents.even.den,
      (frameAt word).eps * (frameAt word).parents.even.num) ∈ (frameAt word).closedPolygon)
    (hiq : i - ((frameAt word).eps * (frameAt word).parents.even.den,
      (frameAt word).eps * (frameAt word).parents.even.num) ∈ (frameAt word).closedPolygon)
    (hΨc : 0 ≤ sheetDiffW word c) (hΨi : 1 ≤ sheetDiffW word i)
    (hstar : ∀ j, Edge j c → 0 ≤ sheetDiffW word j) : False :=
  adjacent_chart_excluded h hSE P
    (adjacentChart_witness h hSE hpk P hcE hiE hcq hiq hΨc hΨi
      (sheetPolicyA_of_nonneg h hSE hpk P hcE hr.1 hr.2.1 hΨc hstar)) hr

end FLatticePaper.Induction
