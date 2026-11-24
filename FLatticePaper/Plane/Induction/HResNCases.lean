import FLatticePaper.Plane.Induction.HResPWire

/-! Task 72 (hResN, the case reduction to the negative tie).

`hResN_of_cases`: the negative tied rising pair `hResN` (`−σ`, tied centre, an input `j` with `Ψ j = −1`), by the sign of the target:
* `Ψ i ≥ 0` (strict or tied target): the negative tie `hNeg` (the configuration of `hNegTie`, target allowed to tie; reduced to the
  V-block input Q21 by `hNegTie_of_Q21`);
* `Ψ i ≤ −1`: reflect about the centre to a `σ` pair with target `Ψ ≥ 1`. If the other input has `Ψ > 0`, the positive adjacent chart
  excludes it (`adjacent_chart_excluded`); otherwise every input of the reflected centre is nonnegative and
  `plus_adjacent_target_excluded` applies. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

theorem hResN_of_cases {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpk : (frameAt word).Packet (standardField word))
    {seed : Site → Site → Prop}
    (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hNeg : ∀ c i, RisingBlackPair (standardField word) (-(frameAt word).shortShift) c i →
      c ∈ (frameAt word).closedPolygon → i ∈ (frameAt word).closedPolygon →
      c + (frameAt word).uq ∈ (frameAt word).closedPolygon → i + (frameAt word).uq ∈ (frameAt word).closedPolygon →
      sheetDiffW word c = 0 → (∃ j, FLatticePaper.Edge j c ∧ sheetDiffW word j ≤ -1) → 0 ≤ sheetDiffW word i → False)
    {c i : Site} (hr : RisingBlackPair (standardField word) (-(frameAt word).shortShift) c i)
    (hcE : c ∈ (frameAt word).closedPolygon)
    (hcu : c + (frameAt word).uq ∈ (frameAt word).closedPolygon)
    (hiu : i + (frameAt word).uq ∈ (frameAt word).closedPolygon)
    (hΨc : sheetDiffW word c = 0) (hj : ∃ j, FLatticePaper.Edge j c ∧ sheetDiffW word j = -1) : False := by
  obtain ⟨j, hjE, hjΨ⟩ := hj
  have hiE := (frameAt word).black_input_mem hpk hcE hr.2.1 hr.1
  by_cases hneg : sheetDiffW word i < 0
  · -- the target is negative: reflect the configuration about the centre
    have hrr := (frameAt word).rising_reflect_neg hpk hr
    have hcE' := (frameAt word).reflect_mem_closedPolygon hcE
    have hiE' := (frameAt word).reflect_mem_closedPolygon hiE
    have hcq : (frameAt word).centre - c - (frameAt word).uq ∈ (frameAt word).closedPolygon := by
      have h3 := (frameAt word).reflect_mem_iff.mpr hcu
      have e : (frameAt word).centre - (c + (frameAt word).uq) =
          (frameAt word).centre - c - (frameAt word).uq := by abel
      rwa [e] at h3
    have hiq : (frameAt word).centre - i - (frameAt word).uq ∈ (frameAt word).closedPolygon := by
      have h3 := (frameAt word).reflect_mem_iff.mpr hiu
      have e : (frameAt word).centre - (i + (frameAt word).uq) =
          (frameAt word).centre - i - (frameAt word).uq := by abel
      rwa [e] at h3
    have hΨ'c : sheetDiffW word ((frameAt word).centre - c) = 0 := by
      rw [sheetDiffW_reflect h hSE.packet, hΨc, neg_zero]
    have hΨ'i : 1 ≤ sheetDiffW word ((frameAt word).centre - i) := by
      rw [sheetDiffW_reflect h hSE.packet]
      omega
    obtain ⟨k, hkE, hki, hcover⟩ := exists_other_input hr.1
    have hk' := reflect_edge_even (frameAt word).centre (frameAt word).evenSite_centre hkE
    by_cases hkpos : 0 < sheetDiffW word k
    · -- the other input is positive: its reflection is the negative input of the reflected pair
      have hΨ'k : sheetDiffW word ((frameAt word).centre - k) ≤ -1 := by
        rw [sheetDiffW_reflect h hSE.packet]
        omega
      have hij' : (frameAt word).centre - i ≠ (frameAt word).centre - k := by
        intro e
        apply hki
        have := congrArg (fun z => (frameAt word).centre - z) e
        simpa using this.symm
      exact adjacent_chart_excluded h hSE P
        (adjacentChart_witness h hSE hpk P hcE' hiE' hcq hiq (le_of_eq hΨ'c.symm) hΨ'i
          (sheetPolicyA_of_tie h hSE hpk P hcE' hrr.1 hk' hij' hrr.2.1 hΨ'c hΨ'k)) hrr
    · -- the other input is nonpositive: every input of the reflected centre is nonnegative
      have hstar : ∀ m, FLatticePaper.Edge m ((frameAt word).centre - c) →
          0 ≤ sheetDiffW word m := by
        intro m hm
        have hm0 := reflect_edge_even (frameAt word).centre (frameAt word).evenSite_centre hm
        rw [sub_sub_cancel] at hm0
        have hsym := sheetDiffW_reflect h hSE.packet m
        rcases hcover _ hm0 with h1 | h1
        · rw [h1] at hsym
          omega
        · rw [h1] at hsym
          omega
      exact plus_adjacent_target_excluded h hSE hpk P hrr hcE' hiE' hcq hiq (le_of_eq hΨ'c.symm) hΨ'i hstar
  · exact hNeg c i hr hcE hiE hcu hiu hΨc ⟨j, hjE, by omega⟩ (by omega)

end FLatticePaper.Induction
