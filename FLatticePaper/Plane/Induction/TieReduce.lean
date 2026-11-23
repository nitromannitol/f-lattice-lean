import FLatticePaper.Plane.Induction.TieOpt2
import FLatticePaper.Plane.Induction.TieParity
import FLatticePaper.Plane.Induction.StrongBridge

/-! Task 69: the discharged slip range, the strict-centre monotonicity, and the reduction of the tie hypothesis to the two
narrowed leaves `hResP` (σ) and `hResN` (−σ).

* `slipRange_of_strong`, `hU_of_strong`: the word's slip range on `E` and its unit slip, from the conjugate's strong
  estimates (`slipFields_of_strong` with `arcInputs_of_strong`, which use `openInputs_of_strong`).
* `strict_centre_target`: a rising pair (for either sign) with `Ψ c ≥ 1` has `Ψ i ≥ 1`: retention (`sheetPolicyA_of_black`)
  and `sheetDiff_mono_A`. This closes the configuration `Ψ c = 1, Ψ i = 0`.
* `tie_excluded_of_narrow`: every tie `Ψ c = 0 ∨ Ψ i = 0` is excluded, except the option-2 ties with a `Ψ = −1` input
  (the leaves `hResP`, `hResN`); the other option-2 ties reflect to those leaves or are excluded by `plus_adjacent_nonpos_excluded`.
* `oddBlackNoRise_of_narrow`: `OddBlackNoRise` with the leaves `hResP`, `hResN` only. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- The word's slip range on `E`, from the conjugate's strong estimates (the slip fields of `StrongBridge`). -/
theorem slipRange_of_strong {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) :
    ∀ z ∈ (frameAt word).closedPolygon,
      0 ≤ standardField word z - standardField word (z + (frameAt word).shortShift) ∧
        standardField word z - standardField word (z + (frameAt word).shortShift) ≤ 2 := by
  intro z hz
  have hs := (slipFields_of_strong h hSE (arcInputs_of_strong h hSE)).2.2 z hz
  unfold ChildFrame.slip at hs
  simpa only [one_smul] using hs

/-- The word's unit slip, from the conjugate's strong estimates. -/
theorem hU_of_strong {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) :
    HasUnitSlip (standardField word) (fun z => standardField word (z + (frameAt word).shortShift)) :=
  (slipFields_of_strong h hSE (arcInputs_of_strong h hSE)).1

/-- The word's packet, from the conjugate's packet and the open inputs (`StrongInduction`). -/
theorem packet_of_strong {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) : (frameAt word).Packet (standardField word) :=
  packet_of_openInputs_step h hSE.packet (openInputs_of_strong h hSE)

/-- A strict centre forces a strict target on a rising pair (either sign): the centre's retention and the monotonicity of
`Ψ` along the retained edges (`sheetDiff_mono_A`). -/
theorem strict_centre_target {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpk : (frameAt word).Packet (standardField word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    {τ c i : Site} (hr : RisingBlackPair (standardField word) τ c i)
    (hcE : c ∈ (frameAt word).closedPolygon) (hΨc : 1 ≤ sheetDiffW word c) : 1 ≤ sheetDiffW word i := by
  have hret := sheetPolicyA_of_black hw hSE hpk P hcE hr.1 hr.2.1 hΨc
  have hm := sheetDiff_mono_A hw hSE P hret
  omega

/-- `c − τ` reflected: `centre − (c − τ) = centre − c + τ`. -/
theorem ChildFrame.reflect_sub_eq_add (frame : ChildFrame) (c τ : Site) :
    frame.centre - (c - τ) = frame.centre - c + τ := by
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_sub, Prod.fst_add]
    ring
  · simp only [Prod.snd_sub, Prod.snd_add]
    ring

/-- **The tie reduction.** Every tie `Ψ c = 0 ∨ Ψ i = 0` on a rising `σ` pair with centre in `E` is excluded, given only
the two narrowed leaves: option-2 ties whose centre has an input with `Ψ = −1`, for σ (`hResP`) and for −σ (`hResN`). -/
theorem tie_excluded_of_narrow {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpk : (frameAt word).Packet (standardField word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hResP : ∀ c i, RisingBlackPair (standardField word) (frameAt word).shortShift c i →
      c ∈ (frameAt word).closedPolygon →
      (c - (frameAt word).uq ∈ (frameAt word).closedPolygon ∧ i - (frameAt word).uq ∈ (frameAt word).closedPolygon) →
      sheetDiffW word c = 0 → (∃ j, FLatticePaper.Edge j c ∧ sheetDiffW word j = -1) → False)
    (hResN : ∀ c i, RisingBlackPair (standardField word) (-(frameAt word).shortShift) c i →
      c ∈ (frameAt word).closedPolygon →
      (c + (frameAt word).uq ∈ (frameAt word).closedPolygon ∧ i + (frameAt word).uq ∈ (frameAt word).closedPolygon) →
      sheetDiffW word c = 0 → (∃ j, FLatticePaper.Edge j c ∧ sheetDiffW word j = -1) → False) :
    ∀ c i, RisingBlackPair (standardField word) (frameAt word).shortShift c i →
      c ∈ (frameAt word).closedPolygon → (sheetDiffW word c = 0 ∨ sheetDiffW word i = 0) → False := by
  intro c i hr hcE hT
  have hiE := (frameAt word).black_input_mem hpk hcE hr.2.1 hr.1
  have hn3 : 3 ≤ (frameAt word).child.num := child_num_ge_three h
  have hnd : (frameAt word).child.num + 2 ≤ (frameAt word).child.den := by
    have := (frameAt word).child_facts.2.2.1
    omega
  have hτ : (frameAt word).tGrade (frameAt word).shortShift % 2 = 0 := by
    rw [(frameAt word).tGrade_shortShift]
    norm_num
  rcases lt_trichotomy (sheetDiffW word c) 0 with hneg | hzero | hpos
  · -- `Ψ c ≤ −1`: the tie is at the target, `Ψ i = 0`; the reflected pair has `Ψ (R c) ≥ 1`, forcing `Ψ (R i) ≥ 1`
    have hΨi0 : sheetDiffW word i = 0 := by omega
    have hr' := (frameAt word).rising_reflect_gen hpk (frameAt word).shortShift hτ hr
    have hRc := strict_centre_target h hSE hpk P hr' ((frameAt word).reflect_mem_closedPolygon hcE)
      (by rw [sheetDiffW_reflect h hSE.packet]; omega)
    rw [sheetDiffW_reflect h hSE.packet] at hRc
    omega
  · -- `Ψ c = 0`: the common chart, with the exits
    by_cases hnc : (frameAt word).tGrade c - 2 ≥
        (if EvenSite c then 2 else (frameAt word).child.num) - (frameAt word).child.periodDenominator
    · by_cases hni : (frameAt word).tGrade i - 2 ≥
          (if EvenSite i then 2 else (frameAt word).child.num) - (frameAt word).child.periodDenominator
      · rcases common_chart_option (frameAt word) hn3 hnd hcE hiE hr.1 hnc hni with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact rising_option1_excluded h hSE hpk P hr hcE hiE h1 h2
        · -- option 2: the tied centre
          by_cases hneg1 : ∃ j, FLatticePaper.Edge j c ∧ sheetDiffW word j = -1
          · exact hResP c i hr hcE ⟨h1, h2⟩ hzero hneg1
          · by_cases hpos1 : ∃ j, FLatticePaper.Edge j c ∧ sheetDiffW word j = 1
            · obtain ⟨j, hj, hjv⟩ := hpos1
              -- reflect: the reflected pair is a −σ option-2 pair with a `Ψ = −1` input
              have hr' := (frameAt word).rising_reflect_gen hpk (frameAt word).shortShift hτ hr
              have hcu : (frameAt word).centre - c + (frameAt word).uq ∈ (frameAt word).closedPolygon := by
                have h3 := (frameAt word).reflect_mem_iff.mpr h1
                rwa [(frameAt word).reflect_sub_eq_add c _] at h3
              have hiu : (frameAt word).centre - i + (frameAt word).uq ∈ (frameAt word).closedPolygon := by
                have h3 := (frameAt word).reflect_mem_iff.mpr h2
                rwa [(frameAt word).reflect_sub_eq_add i _] at h3
              have hjR : FLatticePaper.Edge ((frameAt word).centre - j) ((frameAt word).centre - c) :=
                reflect_edge_even _ (frameAt word).evenSite_centre hj
              exact hResN ((frameAt word).centre - c) ((frameAt word).centre - i) hr'
                ((frameAt word).reflect_mem_closedPolygon hcE) ⟨hcu, hiu⟩
                (by rw [sheetDiffW_reflect h hSE.packet]; omega)
                ⟨(frameAt word).centre - j, hjR, by rw [sheetDiffW_reflect h hSE.packet]; omega⟩
            · -- no input at `±1`: the star is `≤ 0`, and the plus-adjacent lemma applies
              have hstarNeg : ∀ j, FLatticePaper.Edge j c → sheetDiffW word j ≤ 0 := by
                intro j hj
                have hu := sheetDiff_unit h hSE c j hj
                by_contra hgt
                exact hpos1 ⟨j, hj, by omega⟩
              exact plus_adjacent_nonpos_excluded h hSE hpk P (slipRange_of_strong h hSE) hr hcE hiE h1 h2
                hzero.le hstarNeg
      · exact (frameAt word).not_rising_of_input_exit hpk hn3 hnd ⟨hcE, hiE, hr.1, not_le.mp hni⟩ hr
    · exact (frameAt word).not_rising_of_centre_exit hpk hn3 hnd ⟨hcE, hiE, hr.1, not_le.mp hnc⟩ hr
  · -- `Ψ c ≥ 1`: the target is strict too, contradicting the tie
    have hi1 := strict_centre_target h hSE hpk P hr hcE (by omega)
    omega

/-- **`OddBlackNoRise` (task 69 (c)), from the strong estimates of the conjugate and the old policy, with the two narrowed
leaves `hResP`, `hResN` as the only remaining inputs.** -/
theorem oddBlackNoRise_of_narrow {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hResP : ∀ c i, RisingBlackPair (standardField word) (frameAt word).shortShift c i →
      c ∈ (frameAt word).closedPolygon →
      (c - (frameAt word).uq ∈ (frameAt word).closedPolygon ∧ i - (frameAt word).uq ∈ (frameAt word).closedPolygon) →
      sheetDiffW word c = 0 → (∃ j, FLatticePaper.Edge j c ∧ sheetDiffW word j = -1) → False)
    (hResN : ∀ c i, RisingBlackPair (standardField word) (-(frameAt word).shortShift) c i →
      c ∈ (frameAt word).closedPolygon →
      (c + (frameAt word).uq ∈ (frameAt word).closedPolygon ∧ i + (frameAt word).uq ∈ (frameAt word).closedPolygon) →
      sheetDiffW word c = 0 → (∃ j, FLatticePaper.Edge j c ∧ sheetDiffW word j = -1) → False) :
    OddBlackNoRise (standardField word) (frameAt word).shortShift :=
  oddBlackNoRise_standard word (packet_of_strong h hSE) (hU_of_strong h hSE)
    (noBlackPairRise_of_signs h hSE (packet_of_strong h hSE) P
      (fun _ _ hr hc hΨc hΨi => neg_sign_excluded h hSE (packet_of_strong h hSE) P
        (slipRange_of_strong h hSE) hr hc hΨc hΨi)
      (tie_excluded_of_narrow h hSE (packet_of_strong h hSE) P hResP hResN))

end FLatticePaper.Induction
