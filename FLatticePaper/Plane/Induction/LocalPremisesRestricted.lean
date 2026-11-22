import FLatticePaper.Plane.Induction.LocalPremises
import FLatticePaper.Plane.RestrictedBellmanRank
import FLatticePaper.Plane.Induction.SheetMinFromConj
import FLatticePaper.Plane.Induction.Packet
import FLatticePaper.Plane.Induction.OddStep
import FLatticePaper.Plane.Induction.SheetDifference
import FLatticePaper.Plane.Induction.Seams
import FLatticePaper.Plane.QuarterTurn
import FLatticePaper.Plane.OdometerTheorem

/-! The variant of the local premises with restricted forts (task 27).

`LocalPremises'` keeps every clause of `LocalPremises` except the two signed ranks of (I3). Each of those is replaced by
the local permits `PermitLocal` and the absence of restricted forts `RestrictedNoFort`, for the same permit relation on
the quarter-turned parent `Fp`, in the transverse grade of the frame (the grade of I1 and S3).

`localPremises_of_variant` shows that the variant implies the original premises at a proper word. The two ranks are
produced by `exists_constrainedBurningRank_of_restrictedNoFort`. Its deck is the period lattice of the odd parent
`(parentsAt word).odd`, and the proof uses only the conjugate packet: the periods of the conjugate standard field, the
binary Laplacian, and the sheet difference identity. The two permit relations are invariant under that deck, because the
chain potential `Ξ` shifts by a constant under each deck vector. -/

namespace FLatticePaper.Induction
open Farey FLatticePaper
open scoped Matrix

/-- The local premises at a proper word, with the two signed ranks of (I3) replaced by the restricted-fort form: the
local permits and the absence of restricted forts, for the two permit relations of `Fp`, in the frame's transverse
grade. Every other clause is that of `LocalPremises`. -/
def LocalPremises' (word : Word) : Prop :=
  let frame := frameAt word
  let Fp := quarterTurnField (standardField (conjWord word))
  let F := standardField word
  let Ξ := sheetChainPotential word (standardField (conjWord word))
  -- I1: the sheet difference is nonnegative on the zero region of the closed polygon
  (∀ z ∈ frame.closedPolygon, 1 - frame.child.den ≤ frame.tGrade z →
      0 ≤ frame.sheetC Fp z - frame.sheetA Fp z) ∧
  -- I2: the sheet difference has the sign of `ε` on the harmonic region
  (∀ z ∈ frame.closedPolygon, frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 1 →
      (frame.eps = 1 → 0 ≤ frame.sheetC Fp z - frame.sheetA Fp z) ∧
      (frame.eps = -1 → frame.sheetC Fp z - frame.sheetA Fp z ≤ 0)) ∧
  -- I3: the chain potential has unit increments on edges; the two permitted sides have local permits and no
  -- restricted forts in the transverse grade
  (∀ c i : Site, FLatticePaper.Edge i c → -1 ≤ Ξ i - Ξ c ∧ Ξ i - Ξ c ≤ 1) ∧
  PermitLocal Fp (fun c i => Ξ i ≤ Ξ c) ∧
  RestrictedNoFort Fp frame.tGrade (fun c i => Ξ i ≤ Ξ c) ∧
  PermitLocal Fp (fun c i => Ξ (c + frame.sheetOffset) ≤ Ξ (i + frame.sheetOffset)) ∧
  RestrictedNoFort Fp frame.tGrade (fun c i => Ξ (c + frame.sheetOffset) ≤ Ξ (i + frame.sheetOffset)) ∧
  -- S1, S2: the difference `D = F − F(· + σ)` takes values in {0, 1, 2} on E and its inputs, with no 0–2 edge
  (∀ e ∈ frame.closedPolygon, starDiff F frame.shortShift e = 0 ∨ starDiff F frame.shortShift e = 1 ∨
      starDiff F frame.shortShift e = 2) ∧
  (∀ e ∈ frame.closedPolygon, ∀ u, FLatticePaper.Edge u e →
      (starDiff F frame.shortShift u = 0 ∨ starDiff F frame.shortShift u = 1 ∨
        starDiff F frame.shortShift u = 2)) ∧
  (∀ e ∈ frame.closedPolygon, ∀ u, FLatticePaper.Edge u e →
      ¬((starDiff F frame.shortShift e = 0 ∧ starDiff F frame.shortShift u = 2) ∨
        (starDiff F frame.shortShift e = 2 ∧ starDiff F frame.shortShift u = 0))) ∧
  -- S3: the local permits and the absence of restricted forts in the grade half-spaces
  PermitLocal F (slipPermits F (fun z => F (z + frame.shortShift))) ∧
  RestrictedNoFort F (frame.cutGrade F 1 1 1) (slipPermits F (fun z => F (z + frame.shortShift)))

/-- The conjugate of a proper word has its chain potential with the stated closed form: `Ξ` is `Fp` minus its
translate by the sheet offset, minus the sibling slope, up to a constant. -/
theorem sheetChainPotential_eq {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hG : (frameAt (conjWord word)).Packet (standardField (conjWord word))) :
    ∃ C0 : ℤ, ∀ z : Site, sheetChainPotential word (standardField (conjWord word)) z =
      quarterTurnField (standardField (conjWord word)) z -
        quarterTurnField (standardField (conjWord word)) (z - (frameAt word).sheetOffset) -
        (frameAt word).siblingSlope z + C0 := by
  obtain ⟨K, hK⟩ := sheetDifference_identifies h hG
  refine ⟨K - (frameAt word).sheetConstant, fun z => ?_⟩
  have hz := hK (z + (frameAt word).sheetShift)
  simp only [add_sub_cancel_right] at hz
  unfold ChildFrame.sheetC ChildFrame.sheetA at hz
  simp only [add_sub_cancel_right] at hz
  unfold sheetChainPotential
  linarith

/-- The quarter-turned parent is periodic on the period lattice of the odd parent, with the matrix of that parent. -/
theorem satisfiesPeriodicity_fp {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hG : (frameAt (conjWord word)).Packet (standardField (conjWord word))) :
    SatisfiesPeriodicity (parentsAt word).odd (quarterTurnField (standardField (conjWord word))) := by
  have hodd : (parentsAt word).odd.Odd := (parentsAt_valid word).odd_parity
  have hint : (parentsAt word).odd.InUnitInterval := (parentsAt_valid word).odd_bounds
  have hchild : (frameAt (conjWord word)).child = (parentsAt word).odd.rotate := frameAt_conj_child h
  have hintR : (parentsAt word).odd.rotate.InUnitInterval := by
    rw [← hchild]
    exact ((frameAt (conjWord word)).valid.current_interior .even).inUnitInterval
  have hper : HasGeneratorPeriods (parentsAt word).odd.rotate (standardField (conjWord word))
      (frameAt (conjWord word)).coherentConstantU (frameAt (conjWord word)).coherentConstantV := by
    rw [← hchild]
    exact hG.periods
  have hps := satisfiesPeriodicity_of_generatorPeriods hintR hper
  have hT : (((parentsAt word).odd.periodDenominator : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast (Fraction.periodDenominator_pos hint).ne'
  exact satisfiesPeriodicity_quarterTurn hodd hT hps

/-- The site vector of a difference of sites. -/
theorem siteVector_sub_site (a b : Site) : siteVector (a - b) = siteVector a - siteVector b := by
  ext i
  fin_cases i <;> simp [siteVector]

/-- The chain potential shifts by a constant under each deck vector of the odd parent: its increments along the
deck are the sheet-offset term of the quarter-turned parent, which does not depend on the site. -/
theorem sheetChainPotential_shift {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hG : (frameAt (conjWord word)).Packet (standardField (conjWord word)))
    {v : Site} (hv : v ∈ (parentsAt word).odd.modifiedDeck.span) :
    ∃ δ : ℤ, ∀ z : Site, sheetChainPotential word (standardField (conjWord word)) (z + v) =
      sheetChainPotential word (standardField (conjWord word)) z + δ := by
  obtain ⟨C0, hC0⟩ := sheetChainPotential_eq h hG
  obtain ⟨c, hc⟩ := satisfiesPeriodicity_fp h hG v hv
  have key : ∀ z : Site,
      ((sheetChainPotential word (standardField (conjWord word)) (z + v) -
          sheetChainPotential word (standardField (conjWord word)) z : ℤ) : ℝ) =
        siteVector (frameAt word).sheetOffset ⬝ᵥ ((parentsAt word).odd.matrix *ᵥ siteVector v) -
          (((frameAt word).siblingSlope v : ℤ) : ℝ) := by
    intro z
    rw [hC0 (z + v), hC0 z]
    have hP1 := hc z
    have hP2 := hc (z - (frameAt word).sheetOffset)
    have e1 : z + v - (frameAt word).sheetOffset = z - (frameAt word).sheetOffset + v := by abel
    rw [e1]
    have hL : (((frameAt word).siblingSlope (z + v) : ℤ) : ℝ) =
        (((frameAt word).siblingSlope z : ℤ) : ℝ) + (((frameAt word).siblingSlope v : ℤ) : ℝ) := by
      unfold ChildFrame.siblingSlope
      simp only [Prod.fst_add, Prod.snd_add]
      push_cast
      ring
    have hsub : siteVector z - siteVector (z - (frameAt word).sheetOffset) =
        siteVector (frameAt word).sheetOffset := by
      rw [← siteVector_sub_site, sub_sub_cancel]
    have hdot : siteVector z ⬝ᵥ ((parentsAt word).odd.matrix *ᵥ siteVector v) -
        siteVector (z - (frameAt word).sheetOffset) ⬝ᵥ ((parentsAt word).odd.matrix *ᵥ siteVector v) =
        siteVector (frameAt word).sheetOffset ⬝ᵥ ((parentsAt word).odd.matrix *ᵥ siteVector v) := by
      rw [← sub_dotProduct, hsub]
    push_cast
    linarith
  refine ⟨sheetChainPotential word (standardField (conjWord word)) v -
    sheetChainPotential word (standardField (conjWord word)) 0, fun z => ?_⟩
  have hz := key z
  have h0 := key 0
  rw [zero_add] at h0
  have hcast : ((sheetChainPotential word (standardField (conjWord word)) (z + v) -
      sheetChainPotential word (standardField (conjWord word)) z : ℤ) : ℝ) =
      ((sheetChainPotential word (standardField (conjWord word)) v -
        sheetChainPotential word (standardField (conjWord word)) 0 : ℤ) : ℝ) := by
    rw [hz, h0]
  have hint := Int.cast_injective hcast
  linarith

/-- The first permit relation `Ξ i ≤ Ξ c` is invariant under the deck of the odd parent. -/
theorem permitA_invariant {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hG : (frameAt (conjWord word)).Packet (standardField (conjWord word))) :
    ∀ step ∈ (parentsAt word).odd.modifiedDeck.span, ∀ site input : Site,
      sheetChainPotential word (standardField (conjWord word)) (input + step) ≤
          sheetChainPotential word (standardField (conjWord word)) (site + step) ↔
        sheetChainPotential word (standardField (conjWord word)) input ≤
          sheetChainPotential word (standardField (conjWord word)) site := by
  intro step hstep site input
  obtain ⟨δ, hδ⟩ := sheetChainPotential_shift h hG hstep
  rw [hδ input, hδ site]
  exact add_le_add_iff_right δ

/-- The second permit relation `Ξ (c + e) ≤ Ξ (i + e)` is invariant under the deck of the odd parent. -/
theorem permitC_invariant {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hG : (frameAt (conjWord word)).Packet (standardField (conjWord word))) :
    ∀ step ∈ (parentsAt word).odd.modifiedDeck.span, ∀ site input : Site,
      sheetChainPotential word (standardField (conjWord word)) (site + step + (frameAt word).sheetOffset) ≤
          sheetChainPotential word (standardField (conjWord word)) (input + step + (frameAt word).sheetOffset) ↔
        sheetChainPotential word (standardField (conjWord word)) (site + (frameAt word).sheetOffset) ≤
          sheetChainPotential word (standardField (conjWord word)) (input + (frameAt word).sheetOffset) := by
  intro step hstep site input
  obtain ⟨δ, hδ⟩ := sheetChainPotential_shift h hG hstep
  rw [add_right_comm site step, add_right_comm input step, hδ, hδ]
  exact add_le_add_iff_right δ

/-- The quarter-turned parent's Laplacian is invariant under the deck of the odd parent. -/
theorem laplacian_fp_add_deck {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hG : (frameAt (conjWord word)).Packet (standardField (conjWord word)))
    {step : Site} (hstep : step ∈ (parentsAt word).odd.modifiedDeck.span) (site : Site) :
    laplacian (quarterTurnField (standardField (conjWord word))) (site + step) =
      laplacian (quarterTurnField (standardField (conjWord word))) site := by
  have hodd : (parentsAt word).odd.Odd := (parentsAt_valid word).odd_parity
  have hchild : (frameAt (conjWord word)).child = (parentsAt word).odd.rotate := frameAt_conj_child h
  have hper : HasGeneratorPeriods (parentsAt word).odd.rotate (standardField (conjWord word))
      (frameAt (conjWord word)).coherentConstantU (frameAt (conjWord word)).coherentConstantV := by
    rw [← hchild]
    exact hG.periods
  have hoff : ¬ EvenSite ((0 : ℤ), (-1 : ℤ)) := by
    unfold EvenSite
    norm_num
  have hq : ∀ x : Site, laplacian (quarterTurnField (standardField (conjWord word))) x =
      laplacian (standardField (conjWord word)) (QuarterTurn.counterclockwise.mapSite (0, -1) x) :=
    fun x => laplacian_quarterTurn_add_harmonic QuarterTurn.counterclockwise (0, -1) hoff
      (standardField (conjWord word)) harmonicGrid harmonicGrid_harmonic x
  obtain ⟨i, j, hij⟩ := mulI_mem_span_rotate hodd hstep
  rw [hq, hq, quarterTurn_site, quarterTurn_site]
  have hZ : (-(site + step).2, (site + step).1 - 1) = (-site.2, site.1 - 1) + mulI step := by
    ext <;> simp [mulI] <;> ring
  rw [hZ, hij, laplacian_add_combine hper]

/-- The constrained burning rank of the quarter-turned parent for a deck-invariant permit relation, from its local
permits and the absence of restricted forts (`exists_constrainedBurningRank_of_restrictedNoFort`). -/
theorem constrainedRank_of_variant {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hG : (frameAt (conjWord word)).Packet (standardField (conjWord word)))
    {permits : Site → Site → Prop}
    (hperm : ∀ step ∈ (parentsAt word).odd.modifiedDeck.span, ∀ site input : Site,
      permits (site + step) (input + step) ↔ permits site input)
    (hlocal : PermitLocal (quarterTurnField (standardField (conjWord word))) permits)
    (hno : RestrictedNoFort (quarterTurnField (standardField (conjWord word)))
      (frameAt word).tGrade permits) :
    ∃ rank : Site → ℤ, IsConstrainedBurningRank (quarterTurnField (standardField (conjWord word))) rank permits := by
  have hodd : (parentsAt word).odd.Odd := (parentsAt_valid word).odd_parity
  have hint : (parentsAt word).odd.InUnitInterval := (parentsAt_valid word).odd_bounds
  have hpos : 0 < (parentsAt word).odd.modifiedDeck.det := Fraction.det_modifiedDeck_pos hint
  have hcover : (parentsAt word).odd.modifiedDeck.Covers (parentsAt word).odd.modifiedDeck.residueSquare :=
    (PeriodDeck.covers_iff_square_codes_subset _ hpos _).mpr subset_rfl
  have hbin : ∀ site, laplacian (quarterTurnField (standardField (conjWord word))) site = -1 ∨
      laplacian (quarterTurnField (standardField (conjWord word))) site = 0 :=
    fun site => quarterTurnField_binary hG.binary site
  have hgrade : ∀ step ∈ (parentsAt word).odd.modifiedDeck.span, ∃ increment : ℤ,
      ∀ site, (frameAt word).tGrade (site + step) = (frameAt word).tGrade site + increment :=
    fun step _ => ⟨(frameAt word).tGrade step, fun site => by
      unfold ChildFrame.tGrade
      simp only [Prod.fst_add, Prod.snd_add]
      ring⟩
  obtain ⟨scale, remainder, budget, -, -, -, hrank⟩ := exists_constrainedBurningRank_of_restrictedNoFort hcover
    (fun step hstep => evenSite_of_mem_span_odd hodd hstep)
    (fun step hstep site => laplacian_fp_add_deck h hG hstep site) hgrade hperm hlocal hbin hno
  exact ⟨_, hrank⟩

/-- The variant implies the original local premises at a proper word, given the conjugate packet. -/
theorem localPremises_of_variant {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hG : (frameAt (conjWord word)).Packet (standardField (conjWord word)))
    (hloc : LocalPremises' word) : LocalPremises word := by
  dsimp only [LocalPremises'] at hloc
  obtain ⟨hI1, hI2, hunit, hlocA, hnoA, hlocC, hnoC, hS1, hS2, hS2', hS3a, hS3b⟩ := hloc
  dsimp only [LocalPremises]
  refine ⟨hI1, hI2, hunit, ?_, ?_, hS1, hS2, hS2', hS3a, hS3b⟩
  · exact constrainedRank_of_variant h hG (permitA_invariant h hG) hlocA hnoA
  · exact constrainedRank_of_variant h hG (permitC_invariant h hG) hlocC hnoC

/-- The packets of all words, from the variant of the local premises at every proper word. -/
theorem packet_of_localPremises' (h : ∀ w : Word, (∃ x ∈ w, x ≠ Digit.three) → LocalPremises' w) :
    ∀ w : Word, (frameAt w).Packet (standardField w) := by
  refine word_induction (P := fun w => (frameAt w).Packet (standardField w)) ?_ ?_
  · intro k
    exact reciprocal_packet k
  · intro word hproper hIH
    obtain ⟨hA0, hEq, hrefl, -⟩ := sheetFacts_of_conjPacket hproper hIH
    obtain ⟨hC0, hGe, hbin⟩ :=
      openInputs_of_localPremises hproper hIH (localPremises_of_variant hproper hIH (h word hproper))
    have hP := (frameAt word).packet_of_sheets (Fp := quarterTurnField (standardField (conjWord word)))
      hA0 hC0 hEq hGe hrefl hbin
    rw [standardField_proper hproper]
    exact hP

end FLatticePaper.Induction
