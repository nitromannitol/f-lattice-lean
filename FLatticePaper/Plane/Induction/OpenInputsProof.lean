import FLatticePaper.Plane.Induction.LocalPremisesRestricted

/-! Task 24: the open inputs (I1), (I2), (I3) of the induction step, reduced to named local inputs.

The written arguments give the following, and each named input below is one of them.
* (I3a) unit increments of the chain potential `Ξ` on edges: the archive's STRONG_PRICE_AND_ALTERNATE_STEP §4, with
  the two-rank lemma (TWO_RANK_RAW_PHI_AUDIT) and the both-free exclusion (BOTH_FREE_RAW_PHI_EXCLUSION). These are
  conditional on the earlier monotone policies and the binary and raw-D prerequisites, which the archive lists.
* (I1) the star step: the sheet difference `Ψ = C − A` is nonnegative at each input of a root with `Ψ ≥ 1`, by unit
  increments (H_SOURCE_ANCESTRAL_CLOSURE §3–4). The roots' values `Ψ ≥ 1` and the directly calibrated points are the
  named inputs `R`, `G`, and the covering of the zone by root stars is the named input `hcover`.
* (I2) the same star step on the harmonic region, for `ε = 1` (the nontied-root argument of the sheet notes).
* (I3) the binarity of `min(A, C)`: the admission lemma of TWO_RANK_RAW_PHI_AUDIT, in the form of
  `sheetMin_binary_recurrent_of_chain`, fed by the restricted ranks of `constrainedRank_of_variant`.

Nothing here is a new mathematical claim: each theorem is the archive's argument with its inputs made explicit. -/

namespace FLatticePaper.Induction
open Farey FLatticePaper

/-- The sheet difference `Ψ = C − A` of the conjugate field, the quantity of the premises (I1) and (I2). -/
noncomputable def sheetDiff (word : Word) (z : Site) : ℤ :=
  (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) z -
    (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) z

/-- (I3a) gives unit increments of `Ψ`: the identity `Ψ(z) = K − Ξ(z − lv)` of `sheetDifference_identifies`
turns each edge of `Ψ` into an edge of `Ξ`, since the shift `lv` is even. -/
theorem sheetDiff_unit_of_chain {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hG : (frameAt (conjWord word)).Packet (standardField (conjWord word)))
    (hunit : ∀ c i : Site, FLatticePaper.Edge i c →
      -1 ≤ sheetChainPotential word (standardField (conjWord word)) i -
          sheetChainPotential word (standardField (conjWord word)) c ∧
        sheetChainPotential word (standardField (conjWord word)) i -
          sheetChainPotential word (standardField (conjWord word)) c ≤ 1) :
    ∀ c i : Site, FLatticePaper.Edge i c →
      -1 ≤ sheetDiff word i - sheetDiff word c ∧ sheetDiff word i - sheetDiff word c ≤ 1 := by
  obtain ⟨K, hK⟩ := sheetDifference_identifies h hG
  have hs : EvenSite (frameAt word).sheetShift := (frameAt word).evenSite_sheetShift
  have hid : ∀ z : Site, sheetDiff word z =
      K - sheetChainPotential word (standardField (conjWord word)) (z - (frameAt word).sheetShift) := by
    intro z
    have := hK z
    unfold sheetDiff sheetChainPotential
    linarith
  intro c i hE
  have hu := hunit (c - (frameAt word).sheetShift) (i - (frameAt word).sheetShift)
    (edge_sub_even i c (frameAt word).sheetShift hs hE)
  rw [hid i, hid c]
  constructor <;> linarith [hu.1, hu.2]

/-- The star step on an arbitrary zone. A zone point is a root with `Ψ ≥ 1`, an input of such a root, or a directly
calibrated point with `Ψ ≥ 0`. Unit increments of `Ψ` make every input of a root nonnegative. -/
theorem sheetDiff_nonneg_of_stars {word : Word}
    (hunit : ∀ c i : Site, FLatticePaper.Edge i c →
      -1 ≤ sheetDiff word i - sheetDiff word c ∧ sheetDiff word i - sheetDiff word c ≤ 1)
    {R G Zone : Site → Prop} (hR : ∀ c, R c → 1 ≤ sheetDiff word c)
    (hG : ∀ z, G z → 0 ≤ sheetDiff word z)
    (hcover : ∀ z, Zone z → R z ∨ (∃ c, R c ∧ FLatticePaper.Edge z c) ∨ G z) :
    ∀ z, Zone z → 0 ≤ sheetDiff word z := by
  intro z hz
  rcases hcover z hz with hRz | ⟨c, hc, hE⟩ | hGz
  · linarith [hR z hRz]
  · linarith [hR c hc, (hunit c z hE).1]
  · exact hG z hGz

/-- (I1), the zero region. Given unit increments (I3a), calibrated roots, directly calibrated points, and the covering
of the zone `E ∩ {t ≥ 1 − d}` by root stars and calibrated points, the premise `0 ≤ C − A` holds there.
The covering hypothesis `hcover` is the archive's gap: no archive statement covers the zone as one lemma. -/
theorem i1_of_root_stars {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hG : (frameAt (conjWord word)).Packet (standardField (conjWord word)))
    (hunit : ∀ c i : Site, FLatticePaper.Edge i c →
      -1 ≤ sheetChainPotential word (standardField (conjWord word)) i -
          sheetChainPotential word (standardField (conjWord word)) c ∧
        sheetChainPotential word (standardField (conjWord word)) i -
          sheetChainPotential word (standardField (conjWord word)) c ≤ 1)
    {R G : Site → Prop} (hR : ∀ c, R c → 1 ≤ sheetDiff word c) (hGd : ∀ z, G z → 0 ≤ sheetDiff word z)
    (hcover : ∀ z ∈ (frameAt word).closedPolygon, 1 - (frameAt word).child.den ≤ (frameAt word).tGrade z →
      R z ∨ (∃ c, R c ∧ FLatticePaper.Edge z c) ∨ G z) :
    ∀ z ∈ (frameAt word).closedPolygon, 1 - (frameAt word).child.den ≤ (frameAt word).tGrade z →
      0 ≤ (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) z -
        (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) z := by
  intro z hz ht
  exact sheetDiff_nonneg_of_stars (sheetDiff_unit_of_chain h hG hunit) hR hGd
    (Zone := fun z => z ∈ (frameAt word).closedPolygon ∧ 1 - (frameAt word).child.den ≤ (frameAt word).tGrade z)
    (fun z hz' => hcover z hz'.1 hz'.2) z ⟨hz, ht⟩

/-- (I2), the harmonic region, for the branch `ε = 1`. The same star step gives `0 ≤ C − A` on the harmonic zone.
The branch `ε = −1` is not covered: its mirror step is not written out in the archive. -/
theorem i2_pos_of_root_stars {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hG : (frameAt (conjWord word)).Packet (standardField (conjWord word)))
    (hunit : ∀ c i : Site, FLatticePaper.Edge i c →
      -1 ≤ sheetChainPotential word (standardField (conjWord word)) i -
          sheetChainPotential word (standardField (conjWord word)) c ∧
        sheetChainPotential word (standardField (conjWord word)) i -
          sheetChainPotential word (standardField (conjWord word)) c ≤ 1)
    {R G : Site → Prop} (hR : ∀ c, R c → 1 ≤ sheetDiff word c) (hGd : ∀ z, G z → 0 ≤ sheetDiff word z)
    (hcover : ∀ z ∈ (frameAt word).closedPolygon,
      (frameAt word).sGrade z ≤ 2 * ((frameAt word).child.den + (frameAt word).child.num) - 1 →
        R z ∨ (∃ c, R c ∧ FLatticePaper.Edge z c) ∨ G z) :
    (frameAt word).eps = 1 → ∀ z ∈ (frameAt word).closedPolygon,
      (frameAt word).sGrade z ≤ 2 * ((frameAt word).child.den + (frameAt word).child.num) - 1 →
      0 ≤ (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) z -
        (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) z := by
  intro _ z hz hs
  exact sheetDiff_nonneg_of_stars (sheetDiff_unit_of_chain h hG hunit) hR hGd
    (Zone := fun z => z ∈ (frameAt word).closedPolygon ∧
      (frameAt word).sGrade z ≤ 2 * ((frameAt word).child.den + (frameAt word).child.num) - 1)
    (fun z hz' => hcover z hz'.1 hz'.2) z ⟨hz, hs⟩

/-- (I3), binarity and recurrence of `min(A, C)`. The named inputs are the unit increments (I3a) and the two
permit systems with their restricted-fort conditions; the ranks come from `constrainedRank_of_variant`, and the
binarity from the admission lemma `sheetMin_binary_recurrent_of_chain`. -/
theorem i3_binary_of_local_inputs {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hG : (frameAt (conjWord word)).Packet (standardField (conjWord word)))
    (hunit : ∀ c i : Site, FLatticePaper.Edge i c →
      -1 ≤ sheetChainPotential word (standardField (conjWord word)) i -
          sheetChainPotential word (standardField (conjWord word)) c ∧
        sheetChainPotential word (standardField (conjWord word)) i -
          sheetChainPotential word (standardField (conjWord word)) c ≤ 1)
    (hlocA : PermitLocal (quarterTurnField (standardField (conjWord word)))
      (fun c i => sheetChainPotential word (standardField (conjWord word)) i ≤
        sheetChainPotential word (standardField (conjWord word)) c))
    (hnoA : RestrictedNoFort (quarterTurnField (standardField (conjWord word))) (i3aGrade word)
      (fun c i => sheetChainPotential word (standardField (conjWord word)) i ≤
        sheetChainPotential word (standardField (conjWord word)) c))
    (hlocC : PermitLocal (quarterTurnField (standardField (conjWord word)))
      (fun c i => sheetChainPotential word (standardField (conjWord word)) (c + (frameAt word).sheetOffset) ≤
        sheetChainPotential word (standardField (conjWord word)) (i + (frameAt word).sheetOffset)))
    (hnoC : RestrictedNoFort (quarterTurnField (standardField (conjWord word))) (frameAt word).tGrade
      (fun c i => sheetChainPotential word (standardField (conjWord word)) (c + (frameAt word).sheetOffset) ≤
        sheetChainPotential word (standardField (conjWord word)) (i + (frameAt word).sheetOffset))) :
    (∀ z ∈ (frameAt word).closedPolygon,
        laplacian ((frameAt word).sheetMin (quarterTurnField (standardField (conjWord word)))) z = -1 ∨
          laplacian ((frameAt word).sheetMin (quarterTurnField (standardField (conjWord word)))) z = 0) ∧
      Recurrent ((frameAt word).sheetMin (quarterTurnField (standardField (conjWord word)))) := by
  obtain ⟨rankA, hrankA⟩ := constrainedRank_of_variant h hG (i3aGrade_deck h hG) (permitA_invariant h hG) hlocA hnoA
  obtain ⟨rankC, hrankC⟩ := constrainedRank_of_variant h hG (tGrade_add_odd_deck word) (permitC_invariant h hG)
    hlocC hnoC
  obtain ⟨hbin, hrec⟩ := sheetMin_binary_recurrent_of_chain h hG hunit rankA rankC hrankA hrankC
  exact ⟨fun z _ => hbin z, hrec⟩

end FLatticePaper.Induction
