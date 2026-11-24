import FLatticePaper.Plane.Induction.HResP

/-! Task 72 (hResN, the reduction to the positive tie with a positive input).

`hResN` concerns a rising pair of the shift `−σ` with a tied centre and an input of value `−1`. Reflecting the whole configuration
about the centre (`rising_reflect_neg`, `sheetDiffW_reflect`) gives a rising pair of the shift `σ` with a tied centre and an input of
value `+1`, whose endpoints are shifted by `−uq` in the polygon. So `hResN` follows from the positive tie statement `hPosTie`, which is
the positive-chart input `≥ 1` case (the mirror of `hResP_of_negTie`'s negative tie). No case split is needed: the value `−1` maps
exactly to `+1`. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- **The tied rising pair of the shift `−σ` (hResN), reduced to the positive tie with a positive input (hPosTie).** -/
theorem hResN_of_posTie {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpk : (frameAt word).Packet (standardField word))
    (hPosTie : ∀ c i, RisingBlackPair (standardField word) (frameAt word).shortShift c i →
      c ∈ (frameAt word).closedPolygon →
      (c - (frameAt word).uq ∈ (frameAt word).closedPolygon ∧ i - (frameAt word).uq ∈ (frameAt word).closedPolygon) →
      sheetDiffW word c = 0 → (∃ j, FLatticePaper.Edge j c ∧ 1 ≤ sheetDiffW word j) → False)
    {c i : Site} (hr : RisingBlackPair (standardField word) (-(frameAt word).shortShift) c i)
    (hcE : c ∈ (frameAt word).closedPolygon)
    (hcu : c + (frameAt word).uq ∈ (frameAt word).closedPolygon)
    (hiu : i + (frameAt word).uq ∈ (frameAt word).closedPolygon)
    (hΨc : sheetDiffW word c = 0) (hj : ∃ j, FLatticePaper.Edge j c ∧ sheetDiffW word j = -1) : False := by
  obtain ⟨j, hjEdge, hjΨ⟩ := hj
  have hrr := (frameAt word).rising_reflect_neg hpk hr
  have hcE' := (frameAt word).reflect_mem_closedPolygon hcE
  have hcq : (frameAt word).centre - c - (frameAt word).uq ∈ (frameAt word).closedPolygon := by
    have h3 := (frameAt word).reflect_mem_iff.mpr hcu
    have e : (frameAt word).centre - (c + (frameAt word).uq) =
        (frameAt word).centre - c - (frameAt word).uq := by
      abel
    rwa [e] at h3
  have hiq : (frameAt word).centre - i - (frameAt word).uq ∈ (frameAt word).closedPolygon := by
    have h3 := (frameAt word).reflect_mem_iff.mpr hiu
    have e : (frameAt word).centre - (i + (frameAt word).uq) =
        (frameAt word).centre - i - (frameAt word).uq := by
      abel
    rwa [e] at h3
  have hΨ'c : sheetDiffW word ((frameAt word).centre - c) = 0 := by
    rw [sheetDiffW_reflect h hSE.packet, hΨc, neg_zero]
  have hk' := reflect_edge_even (frameAt word).centre (frameAt word).evenSite_centre hjEdge
  have hΨ'k : 1 ≤ sheetDiffW word ((frameAt word).centre - j) := by
    rw [sheetDiffW_reflect h hSE.packet]
    omega
  exact hPosTie _ _ hrr hcE' ⟨hcq, hiq⟩ hΨ'c ⟨(frameAt word).centre - j, hk', hΨ'k⟩

end FLatticePaper.Induction
