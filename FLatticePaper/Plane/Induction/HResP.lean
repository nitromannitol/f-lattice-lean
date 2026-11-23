import FLatticePaper.Plane.Induction.TieCentre
import FLatticePaper.Plane.Induction.TieOpt2
import FLatticePaper.Plane.Induction.ChartWitness
import FLatticePaper.Plane.Induction.SheetCharts
import FLatticePaper.Plane.Induction.TieReduce

/-! Task 72 (hResP, the case reduction of the positive rising pair with a tied centre).

Setting: a rising `σ` pair `(c, i)` with `Ψ c = 0` and an input `j` of `c` with `Ψ j ≤ −1`; the centre and the endpoints are in the
polygon, with `c − εU_q, i − εU_q ∈ E`. Cases:

* `i ≠ j`, `Ψ i ≥ 1`: the other input is `i`, retained by `sheetPolicyA_of_tie`; the positive adjacent chart excludes it
  (`adjacentChart_witness`, `adjacent_chart_excluded`).
* `i ≠ j`, `Ψ i = 0`: the star `{i, j}` has `Ψ ≤ 0`; `plus_adjacent_nonpos_excluded`.
* `i = j`, the other input `k` has `Ψ k = 0`: the star is `≤ 0`; `plus_adjacent_nonpos_excluded`.
* `i = j`, `Ψ k ≥ 1`: reflect to the negative sign. The reflected centre is tied, its target `I i` is strict and `I k` has
  `Ψ ≤ −1`. This is the negative tied-target exclusion `hNegTie`, whose old-root analysis is the remaining step. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

theorem incomingNeg_ne_incomingPos (c : Site) : FLatticePaper.incomingNeg c ≠ FLatticePaper.incomingPos c := by
  unfold FLatticePaper.incomingNeg FLatticePaper.incomingPos
  split_ifs <;> intro h <;> simp only [Prod.ext_iff] at h <;> omega

/-- The inputs of a site are two distinct sites, and every input is one of them. -/
theorem inputs_cover {c i j m : Site} (hi : FLatticePaper.Edge i c) (hj : FLatticePaper.Edge j c) (hij : i ≠ j)
    (hm : FLatticePaper.Edge m c) : m = i ∨ m = j := by
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact absurd rfl hij
  · exact hm
  · unfold FLatticePaper.Edge at hm
    tauto
  · exact absurd rfl hij

/-- The other input of a site. -/
theorem exists_other_input {c i : Site} (hi : FLatticePaper.Edge i c) :
    ∃ k, FLatticePaper.Edge k c ∧ k ≠ i ∧ ∀ m, FLatticePaper.Edge m c → m = i ∨ m = k := by
  rcases hi with rfl | rfl
  · exact ⟨FLatticePaper.incomingPos c, Or.inr rfl, (incomingNeg_ne_incomingPos c).symm, fun m hm => hm⟩
  · exact ⟨FLatticePaper.incomingNeg c, Or.inl rfl, incomingNeg_ne_incomingPos c, fun m hm => by unfold FLatticePaper.Edge at hm; tauto⟩

/-- **The tied rising pair (hResP), reduced to the negative tied-target exclusion.** -/
theorem hResP_of_negTie {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpk : (frameAt word).Packet (standardField word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed)
    (hNegTie : ∀ c i, RisingBlackPair (standardField word) (-(frameAt word).shortShift) c i →
      c ∈ (frameAt word).closedPolygon → i ∈ (frameAt word).closedPolygon →
      c + (frameAt word).uq ∈ (frameAt word).closedPolygon → i + (frameAt word).uq ∈ (frameAt word).closedPolygon →
      sheetDiffW word c = 0 → (∃ j, FLatticePaper.Edge j c ∧ sheetDiffW word j ≤ -1) → 1 ≤ sheetDiffW word i → False)
    {c i : Site} (hr : RisingBlackPair (standardField word) (frameAt word).shortShift c i)
    (hcE : c ∈ (frameAt word).closedPolygon) (hiE : i ∈ (frameAt word).closedPolygon)
    (hcq : c - ((frameAt word).eps * (frameAt word).parents.even.den,
      (frameAt word).eps * (frameAt word).parents.even.num) ∈ (frameAt word).closedPolygon)
    (hiq : i - ((frameAt word).eps * (frameAt word).parents.even.den,
      (frameAt word).eps * (frameAt word).parents.even.num) ∈ (frameAt word).closedPolygon)
    (hΨc : sheetDiffW word c = 0) (hj : ∃ j, FLatticePaper.Edge j c ∧ sheetDiffW word j = -1) : False := by
  obtain ⟨j, hjEdge, hjΨ⟩ := hj
  have hτ : (frameAt word).tGrade (frameAt word).shortShift % 2 = 0 := by
    rw [(frameAt word).tGrade_shortShift]
    norm_num
  by_cases hij : i = j
  · subst hij
    obtain ⟨k, hkEdge, hki, hcover⟩ := exists_other_input hr.1
    have hkA := tie_sheetA_white h hSE hpk hcE hkEdge hr.1 hki hr.2.1 hΨc hjΨ.le
    have hkΨ : 0 ≤ sheetDiffW word k := by
      unfold sheetDiffW
      omega
    rcases (show sheetDiffW word k = 0 ∨ 1 ≤ sheetDiffW word k by omega) with hk0 | hk1
    · exact plus_adjacent_nonpos_excluded h hSE hpk P (slipRange_of_strong h hSE) hr hcE hiE hcq hiq
        (le_of_eq hΨc) (fun m hm => by
          rcases hcover m hm with rfl | rfl
          · omega
          · omega)
    · -- reflect to the negative sign: the tied centre has the strict target `I i` and the input `I k` with `Ψ ≤ −1`
      have hrr := (frameAt word).rising_reflect_gen hpk _ hτ hr
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
      have hΨ'c : sheetDiffW word ((frameAt word).centre - c) = 0 := by
        rw [sheetDiffW_reflect h hSE.packet, hΨc, neg_zero]
      have hΨ'i : 1 ≤ sheetDiffW word ((frameAt word).centre - i) := by
        rw [sheetDiffW_reflect h hSE.packet]
        omega
      have hk' := reflect_edge_even (frameAt word).centre (frameAt word).evenSite_centre hkEdge
      have hΨ'k : sheetDiffW word ((frameAt word).centre - k) ≤ -1 := by
        rw [sheetDiffW_reflect h hSE.packet]
        omega
      exact hNegTie _ _ hrr hcE' hiE' hcu hiu hΨ'c ⟨(frameAt word).centre - k, hk', hΨ'k⟩ hΨ'i
  · have hA := tie_sheetA_white h hSE hpk hcE hr.1 hjEdge hij hr.2.1 hΨc hjΨ.le
    have hΨi : 0 ≤ sheetDiffW word i := by
      unfold sheetDiffW
      omega
    rcases (show sheetDiffW word i = 0 ∨ 1 ≤ sheetDiffW word i by omega) with hi0 | hi1
    · exact plus_adjacent_nonpos_excluded h hSE hpk P (slipRange_of_strong h hSE) hr hcE hiE hcq hiq
        (le_of_eq hΨc) (fun m hm => by
          rcases inputs_cover hr.1 hjEdge hij hm with rfl | rfl
          · omega
          · omega)
    · exact adjacent_chart_excluded h hSE P
        (adjacentChart_witness h hSE hpk P hcE hiE hcq hiq (le_of_eq hΨc.symm) hi1
          (sheetPolicyA_of_tie h hSE hpk P hcE hr.1 hjEdge hij hr.2.1 hΨc hjΨ.le)) hr

end FLatticePaper.Induction
