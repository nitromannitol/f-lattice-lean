import FLatticePaper.Construction.RawOrigin
import FLatticePaper.Plane.Induction.OpenLocal

/-! Nominal agreement of the even ordinary standard copies with the plane sheets (task 45).

The sheet shifts of the frame of a word are the jet offsets of its ordinary even copies: `lv = (1 - W) K_e` and
`e = T_e + ε K_e`, with `ε = -1` exactly for even phase (`det_walk`). Attainment of the minimum by the sheet of a copy is
a sign of `Ψ = C - A`: `A ≤ C` on the zones `R`, `G` of the star-zone inputs, and `C ≤ A` on the mirror branch `ε = -1`.
The statements below take the donor identification, containment in `E`, the attainment on the copy's sites and the
height-input periodicity of the sheet minimum as named hypotheses. -/

namespace FLatticePaper.Construction

open Farey HeightTile
open FLatticePaper.Induction

/-- The determinant of the parents of a word is `-1` exactly for even phase. -/
theorem eps_parentsAt (word : Word) :
    (parentsAt word).odd.det (parentsAt word).even = if phase word = 0 then -1 else 1 := by
  have hroot : root.odd.det root.even = -1 := by norm_num [root, Fraction.det]
  rw [parentsAt, Parents.det_walk root word, hroot]
  unfold phase
  rcases Nat.even_or_odd (word.count Digit.one) with he | ho
  · rw [he.neg_one_pow, if_pos (Nat.even_iff.mp he)]
    norm_num
  · rw [ho.neg_one_pow, if_neg (by have := Nat.odd_iff.mp ho; omega)]
    norm_num

theorem frameAt_parents (word : Word) : (frameAt word).parents = parentsAt word := rfl

theorem frameAt_eps (word : Word) : (frameAt word).eps = if phase word = 0 then -1 else 1 :=
  eps_parentsAt word

theorem frameAt_phaseW (word : Word) :
    (frameAt word).phaseW = if phase word = 0 then 0 else 1 := by
  unfold ChildFrame.phaseW
  rw [frameAt_eps]
  split_ifs <;> norm_num

theorem sheetShift_eq (word : Word) :
    (frameAt word).sheetShift = (1 - (frameAt word).phaseW) • (kernelJet (parentsAt word).even).1 := by
  rfl

theorem sheetOffset_eq (word : Word) :
    (frameAt word).sheetOffset = (transverseJet (parentsAt word).even).1 +
      (frameAt word).eps • (kernelJet (parentsAt word).even).1 := by
  rfl

/-- The third standard jet of an even output is the sheet shift `lv`. -/
theorem standardJets_even_two_fst (word : Word) :
    (standardJets word .even 2).1 = (frameAt word).sheetShift := by
  rw [sheetShift_eq, frameAt_phaseW]
  by_cases hp : phase word = 0 <;> simp [standardJets, doubleLast, hp]

theorem standardJets_even_two_snd (word : Word) : (standardJets word .even 2).2 = 0 := by
  by_cases hp : phase word = 0 <;> simp [standardJets, doubleLast, hp, kernelJet]

/-- The fifth standard jet of an even output is the sheet translation `lv + e`. -/
theorem standardJets_even_four_fst (word : Word) :
    (standardJets word .even 4).1 = (frameAt word).sheetShift + (frameAt word).sheetOffset := by
  rw [sheetShift_eq, sheetOffset_eq, frameAt_phaseW, frameAt_eps]
  by_cases hp : phase word = 0 <;> simp [standardJets, doubleLast, hp, neg_smul, one_smul]

theorem standardJets_even_four_snd (word : Word) :
    (standardJets word .even 4).2 = ((parentsAt word).even.num, -(parentsAt word).even.den) := by
  by_cases hp : phase word = 0 <;> simp [standardJets, doubleLast, hp, transverseJet, kernelJet]

/-- Attainment `A ≤ C` on the zones `R` (where `Ψ ≥ 1`) and `G` (where `Ψ ≥ 0`) of the star-zone inputs. -/
theorem sheetA_le_sheetC_of_zone {word : Word} {R G : Site → Prop}
    (hR : ∀ c, R c → 1 ≤ sheetDiff word c) (hG : ∀ z, G z → 0 ≤ sheetDiff word z) {z : Site}
    (hz : R z ∨ G z) :
    (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) z ≤
      (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) z := by
  unfold sheetDiff at hR hG
  rcases hz with h | h
  · have := hR z h
    linarith
  · have := hG z h
    linarith

/-- The mirror branch of the star-zone inputs: `C ≤ A` on the lower part of `E` when `ε = -1`. -/
theorem sheetC_le_sheetA_of_mirror {word : Word} (h : StarZoneInputs word) (heps : (frameAt word).eps = -1)
    {z : Site} (hz : z ∈ (frameAt word).closedPolygon)
    (hs : (frameAt word).sGrade z ≤ 2 * ((frameAt word).child.den + (frameAt word).child.num) - 1) :
    (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) z ≤
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) z := by
  obtain ⟨R, G, -, -, -, -, hmirror⟩ := h
  have := hmirror heps z hz hs
  linarith

/-- On `E`, the standard field of a proper word is its sheet minimum (the sewn field of `sewnField_spec`). -/
theorem standardField_eq_sheetMin {word : Word} (hproper : ∃ x ∈ word, x ≠ Digit.three) {s : Site}
    (hs : s ∈ (frameAt word).closedPolygon)
    (hper : RespectsPeriodsOn (frameAt word).child (frameAt word).coherentConstantU
      (frameAt word).coherentConstantV (frameAt word).closedPolygon
      ((frameAt word).sheetMin (quarterTurnField (standardField (conjWord word))))) :
    standardField word s = (frameAt word).sheetMin (quarterTurnField (standardField (conjWord word))) s := by
  rw [standardField_proper hproper]
  exact ((frameAt word).sewnField_spec hper).1 s hs

/-- Nominal agreement of the third-slot copy `A` of an even ordinary standard: the copy is the sheet `A` on its sites,
and `A` is the minimum there. -/
theorem nominal_even_two (parents : TileParents) (word : Word) (hproper : ∃ x ∈ word, x ≠ Digit.three)
    (hodd : ∃ g : ℤ, parents.odd.val.Agrees (quarterTurnField (standardField (conjWord word))) g)
    (hper : RespectsPeriodsOn (frameAt word).child (frameAt word).coherentConstantU
      (frameAt word).coherentConstantV (frameAt word).closedPolygon
      ((frameAt word).sheetMin (quarterTurnField (standardField (conjWord word)))))
    (hE : ∀ s ∈ (ordinaryStandardCopy parents word .even 2).val.sites, s ∈ (frameAt word).closedPolygon)
    (hA : ∀ s ∈ (ordinaryStandardCopy parents word .even 2).val.sites,
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) s ≤
        (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) s) :
    ∃ g : ℤ, (ordinaryStandardCopy parents word .even 2).val.Agrees (standardField word) g := by
  obtain ⟨g, hg⟩ := hodd
  have hcopy : (ordinaryStandardCopy parents word .even 2).val.Agrees
      (fun s => quarterTurnField (standardField (conjWord word)) (s - (standardJets word .even 2).1) +
        ((standardJets word .even 2).2.1 * s.1 + (standardJets word .even 2).2.2 * s.2)) g :=
    Agrees.place hg _ _
  rw [standardJets_even_two_fst, standardJets_even_two_snd] at hcopy
  refine ⟨g, fun s => ?_⟩
  have h1 := hcopy s
  have hsE := hE s.1 s.2
  have hsA := hA s.1 s.2
  rw [h1, standardField_eq_sheetMin hproper hsE hper]
  show _ = min _ _ + g
  rw [min_eq_left hsA]
  simp [ChildFrame.sheetA]

/-- The fourth standard jet of an even output is the sheet translation `lv + e` with the slope of the sibling sheet. -/
theorem standardJets_even_four_snd_eq (word : Word) :
    (standardJets word .even 4).2 = ((parentsAt word).even.num, -(parentsAt word).even.den) :=
  standardJets_even_four_snd word

/-- The third standard jet of an even output is `lv` plus the odd transverse vector `T_o`. -/
theorem standardJets_even_three_fst (word : Word) :
    (standardJets word .even 3).1 = (frameAt word).sheetShift + (transverseJet (parentsAt word).odd).1 := by
  rw [sheetShift_eq, frameAt_phaseW]
  by_cases hp : phase word = 0 <;> simp [standardJets, doubleLast, hp, transverseJet, kernelJet]

theorem standardJets_even_three_snd (word : Word) :
    (standardJets word .even 3).2 = ((parentsAt word).odd.num, -(parentsAt word).odd.den) := by
  by_cases hp : phase word = 0 <;> simp [standardJets, doubleLast, hp, transverseJet, kernelJet]

/-- The fifth standard jet of an even output is `lv + e + T_o`. -/
theorem standardJets_even_five_fst (word : Word) :
    (standardJets word .even 5).1 = (frameAt word).sheetShift + (frameAt word).sheetOffset +
      (transverseJet (parentsAt word).odd).1 := by
  rw [sheetShift_eq, sheetOffset_eq, frameAt_phaseW, frameAt_eps]
  by_cases hp : phase word = 0 <;> simp [standardJets, doubleLast, hp, neg_smul, one_smul]

theorem standardJets_even_five_snd (word : Word) :
    (standardJets word .even 5).2 = ((parentsAt word).even.num + (parentsAt word).odd.num,
      -(parentsAt word).even.den + -(parentsAt word).odd.den) := by
  by_cases hp : phase word = 0 <;> simp [standardJets, doubleLast, hp, transverseJet, kernelJet]

/-- The generator-period law of the odd parent in the form used by the slots three and five. -/
theorem period_transverse {Fp : Field} {cU cV : ℤ} (hp : HasGeneratorPeriods (parentsAt word).odd Fp cU cV)
    (z : Site) :
    Fp (z + (transverseJet (parentsAt word).odd).1) =
      Fp z + ((parentsAt word).odd.num * z.1 - (parentsAt word).odd.den * z.2) + cV := by
  have h := hp.2 z
  unfold Fraction.transverseGrade at h
  have hT : (transverseJet (parentsAt word).odd).1 = (parentsAt word).odd.modifiedDeck.transverse := rfl
  rw [hT]
  linarith

/-- Nominal agreement of the copy in slot four, with the sheet `C` as the minimum on its sites. -/
theorem nominal_even_four (parents : TileParents) (word : Word) (hproper : ∃ x ∈ word, x ≠ Digit.three)
    (hodd : ∃ g : ℤ, parents.odd.val.Agrees (quarterTurnField (standardField (conjWord word))) g)
    (hper : RespectsPeriodsOn (frameAt word).child (frameAt word).coherentConstantU
      (frameAt word).coherentConstantV (frameAt word).closedPolygon
      ((frameAt word).sheetMin (quarterTurnField (standardField (conjWord word)))))
    (hE : ∀ s ∈ (ordinaryStandardCopy parents word .even 4).val.sites, s ∈ (frameAt word).closedPolygon)
    (hC : ∀ s ∈ (ordinaryStandardCopy parents word .even 4).val.sites,
      (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) s ≤
        (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) s) :
    ∃ g : ℤ, (ordinaryStandardCopy parents word .even 4).val.Agrees (standardField word) g := by
  obtain ⟨g, hg⟩ := hodd
  have hcopy : (ordinaryStandardCopy parents word .even 4).val.Agrees
      (fun s => quarterTurnField (standardField (conjWord word)) (s - (standardJets word .even 4).1) +
        ((standardJets word .even 4).2.1 * s.1 + (standardJets word .even 4).2.2 * s.2)) g :=
    Agrees.place hg _ _
  rw [standardJets_even_four_fst, standardJets_even_four_snd] at hcopy
  refine ⟨g + (frameAt word).siblingSlope (frameAt word).sheetShift - (frameAt word).sheetConstant, fun s => ?_⟩
  have h1 := hcopy s
  have hsE := hE s.1 s.2
  have hsC := hC s.1 s.2
  rw [h1, standardField_eq_sheetMin hproper hsE hper]
  show _ = min _ _ + _
  rw [min_eq_right hsC]
  have harg : (s.1 - (frameAt word).sheetShift - (frameAt word).sheetOffset : Site) =
      s.1 - ((frameAt word).sheetShift + (frameAt word).sheetOffset) := by abel
  simp only [ChildFrame.sheetC, ChildFrame.siblingSlope, ChildFrame.sheetConstant, Prod.fst_sub, Prod.snd_sub]
  rw [harg, frameAt_parents]
  ring


/-- Nominal agreement of the copy in slot three, with the sheet `A` (translated by the odd transverse vector). -/
theorem nominal_even_three (parents : TileParents) (word : Word) (hproper : ∃ x ∈ word, x ≠ Digit.three)
    (hodd : ∃ g : ℤ, parents.odd.val.Agrees (quarterTurnField (standardField (conjWord word))) g)
    {cU cV : ℤ} (hperO : HasGeneratorPeriods (parentsAt word).odd
      (quarterTurnField (standardField (conjWord word))) cU cV)
    (hper : RespectsPeriodsOn (frameAt word).child (frameAt word).coherentConstantU
      (frameAt word).coherentConstantV (frameAt word).closedPolygon
      ((frameAt word).sheetMin (quarterTurnField (standardField (conjWord word)))))
    (hE : ∀ s ∈ (ordinaryStandardCopy parents word .even 3).val.sites, s ∈ (frameAt word).closedPolygon)
    (hA : ∀ s ∈ (ordinaryStandardCopy parents word .even 3).val.sites,
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) s ≤
        (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) s) :
    ∃ g : ℤ, (ordinaryStandardCopy parents word .even 3).val.Agrees (standardField word) g := by
  obtain ⟨g, hg⟩ := hodd
  have hcopy : (ordinaryStandardCopy parents word .even 3).val.Agrees
      (fun s => quarterTurnField (standardField (conjWord word)) (s - (standardJets word .even 3).1) +
        ((standardJets word .even 3).2.1 * s.1 + (standardJets word .even 3).2.2 * s.2)) g :=
    Agrees.place hg _ _
  rw [standardJets_even_three_fst, standardJets_even_three_snd] at hcopy
  refine ⟨g + ((parentsAt word).odd.num * ((frameAt word).sheetShift + (transverseJet (parentsAt word).odd).1).1 -
    (parentsAt word).odd.den * ((frameAt word).sheetShift + (transverseJet (parentsAt word).odd).1).2) - cV,
    fun s => ?_⟩
  have h1 := hcopy s
  have hsE := hE s.1 s.2
  have hsA := hA s.1 s.2
  have hP := period_transverse hperO (s.1 - ((frameAt word).sheetShift + (transverseJet (parentsAt word).odd).1))
  rw [show s.1 - ((frameAt word).sheetShift + (transverseJet (parentsAt word).odd).1) +
      (transverseJet (parentsAt word).odd).1 = s.1 - (frameAt word).sheetShift by abel] at hP
  rw [h1, standardField_eq_sheetMin hproper hsE hper]
  show _ = min _ _ + _
  rw [min_eq_left hsA]
  simp only [ChildFrame.sheetA, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hP ⊢
  linear_combination (-1 : ℤ) * hP

/-- Nominal agreement of the copy in slot five, with the sheet `C` translated by the odd transverse vector. -/
theorem nominal_even_five (parents : TileParents) (word : Word) (hproper : ∃ x ∈ word, x ≠ Digit.three)
    (hodd : ∃ g : ℤ, parents.odd.val.Agrees (quarterTurnField (standardField (conjWord word))) g)
    {cU cV : ℤ} (hperO : HasGeneratorPeriods (parentsAt word).odd
      (quarterTurnField (standardField (conjWord word))) cU cV)
    (hper : RespectsPeriodsOn (frameAt word).child (frameAt word).coherentConstantU
      (frameAt word).coherentConstantV (frameAt word).closedPolygon
      ((frameAt word).sheetMin (quarterTurnField (standardField (conjWord word)))))
    (hE : ∀ s ∈ (ordinaryStandardCopy parents word .even 5).val.sites, s ∈ (frameAt word).closedPolygon)
    (hC : ∀ s ∈ (ordinaryStandardCopy parents word .even 5).val.sites,
      (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) s ≤
        (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) s) :
    ∃ g : ℤ, (ordinaryStandardCopy parents word .even 5).val.Agrees (standardField word) g := by
  obtain ⟨g, hg⟩ := hodd
  have hcopy : (ordinaryStandardCopy parents word .even 5).val.Agrees
      (fun s => quarterTurnField (standardField (conjWord word)) (s - (standardJets word .even 5).1) +
        ((standardJets word .even 5).2.1 * s.1 + (standardJets word .even 5).2.2 * s.2)) g :=
    Agrees.place hg _ _
  rw [standardJets_even_five_fst, standardJets_even_five_snd] at hcopy
  refine ⟨g + ((parentsAt word).odd.num * ((frameAt word).sheetShift + (frameAt word).sheetOffset +
      (transverseJet (parentsAt word).odd).1).1 -
    (parentsAt word).odd.den * ((frameAt word).sheetShift + (frameAt word).sheetOffset +
      (transverseJet (parentsAt word).odd).1).2) +
    ((parentsAt word).even.num * (frameAt word).sheetShift.1 -
      (parentsAt word).even.den * (frameAt word).sheetShift.2) - cV - (frameAt word).sheetConstant,
    fun s => ?_⟩
  have h1 := hcopy s
  have hsE := hE s.1 s.2
  have hsC := hC s.1 s.2
  have hP := period_transverse hperO (s.1 - ((frameAt word).sheetShift + (frameAt word).sheetOffset +
    (transverseJet (parentsAt word).odd).1))
  rw [show s.1 - ((frameAt word).sheetShift + (frameAt word).sheetOffset +
      (transverseJet (parentsAt word).odd).1) + (transverseJet (parentsAt word).odd).1 =
      s.1 - ((frameAt word).sheetShift + (frameAt word).sheetOffset) by abel] at hP
  rw [h1, standardField_eq_sheetMin hproper hsE hper]
  show _ = min _ _ + _
  rw [min_eq_right hsC]
  have harg : (s.1 - (frameAt word).sheetShift - (frameAt word).sheetOffset : Site) =
      s.1 - ((frameAt word).sheetShift + (frameAt word).sheetOffset) := by abel
  simp only [ChildFrame.sheetC, ChildFrame.siblingSlope, ChildFrame.sheetConstant, Prod.fst_sub, Prod.snd_sub,
    Prod.fst_add, Prod.snd_add] at hP ⊢
  rw [harg, frameAt_parents]
  linear_combination (-1 : ℤ) * hP


/-- Slot two with attainment derived from the zones `R`, `G` of the star-zone inputs: the copy sites lie in the zones. -/
theorem nominal_even_two_of_zone (parents : TileParents) (word : Word) (hproper : ∃ x ∈ word, x ≠ Digit.three)
    (hodd : ∃ g : ℤ, parents.odd.val.Agrees (quarterTurnField (standardField (conjWord word))) g)
    (hper : RespectsPeriodsOn (frameAt word).child (frameAt word).coherentConstantU
      (frameAt word).coherentConstantV (frameAt word).closedPolygon
      ((frameAt word).sheetMin (quarterTurnField (standardField (conjWord word)))))
    (hE : ∀ s ∈ (ordinaryStandardCopy parents word .even 2).val.sites, s ∈ (frameAt word).closedPolygon)
    {R G : Site → Prop} (hR : ∀ c, R c → 1 ≤ sheetDiff word c) (hG : ∀ z, G z → 0 ≤ sheetDiff word z)
    (hzone : ∀ s ∈ (ordinaryStandardCopy parents word .even 2).val.sites, R s ∨ G s) :
    ∃ g : ℤ, (ordinaryStandardCopy parents word .even 2).val.Agrees (standardField word) g :=
  nominal_even_two parents word hproper hodd hper hE
    (fun s hs => sheetA_le_sheetC_of_zone hR hG (hzone s hs))

/-- Slot three with attainment from the zones. -/
theorem nominal_even_three_of_zone (parents : TileParents) (word : Word) (hproper : ∃ x ∈ word, x ≠ Digit.three)
    (hodd : ∃ g : ℤ, parents.odd.val.Agrees (quarterTurnField (standardField (conjWord word))) g)
    {cU cV : ℤ} (hperO : HasGeneratorPeriods (parentsAt word).odd
      (quarterTurnField (standardField (conjWord word))) cU cV)
    (hper : RespectsPeriodsOn (frameAt word).child (frameAt word).coherentConstantU
      (frameAt word).coherentConstantV (frameAt word).closedPolygon
      ((frameAt word).sheetMin (quarterTurnField (standardField (conjWord word)))))
    (hE : ∀ s ∈ (ordinaryStandardCopy parents word .even 3).val.sites, s ∈ (frameAt word).closedPolygon)
    {R G : Site → Prop} (hR : ∀ c, R c → 1 ≤ sheetDiff word c) (hG : ∀ z, G z → 0 ≤ sheetDiff word z)
    (hzone : ∀ s ∈ (ordinaryStandardCopy parents word .even 3).val.sites, R s ∨ G s) :
    ∃ g : ℤ, (ordinaryStandardCopy parents word .even 3).val.Agrees (standardField word) g :=
  nominal_even_three parents word hproper hodd hperO hper hE
    (fun s hs => sheetA_le_sheetC_of_zone hR hG (hzone s hs))

/-- Slot four with attainment from the mirror branch `ε = -1` of the star-zone inputs. -/
theorem nominal_even_four_of_mirror (parents : TileParents) (word : Word) (hproper : ∃ x ∈ word, x ≠ Digit.three)
    (hodd : ∃ g : ℤ, parents.odd.val.Agrees (quarterTurnField (standardField (conjWord word))) g)
    (hper : RespectsPeriodsOn (frameAt word).child (frameAt word).coherentConstantU
      (frameAt word).coherentConstantV (frameAt word).closedPolygon
      ((frameAt word).sheetMin (quarterTurnField (standardField (conjWord word)))))
    (hE : ∀ s ∈ (ordinaryStandardCopy parents word .even 4).val.sites, s ∈ (frameAt word).closedPolygon)
    (hstar : StarZoneInputs word) (heps : (frameAt word).eps = -1)
    (hsG : ∀ s ∈ (ordinaryStandardCopy parents word .even 4).val.sites,
      (frameAt word).sGrade s ≤ 2 * ((frameAt word).child.den + (frameAt word).child.num) - 1) :
    ∃ g : ℤ, (ordinaryStandardCopy parents word .even 4).val.Agrees (standardField word) g :=
  nominal_even_four parents word hproper hodd hper hE
    (fun s hs => sheetC_le_sheetA_of_mirror hstar heps (hE s hs) (hsG s hs))

/-- Slot five with attainment from the mirror branch `ε = -1` of the star-zone inputs. -/
theorem nominal_even_five_of_mirror (parents : TileParents) (word : Word) (hproper : ∃ x ∈ word, x ≠ Digit.three)
    (hodd : ∃ g : ℤ, parents.odd.val.Agrees (quarterTurnField (standardField (conjWord word))) g)
    {cU cV : ℤ} (hperO : HasGeneratorPeriods (parentsAt word).odd
      (quarterTurnField (standardField (conjWord word))) cU cV)
    (hper : RespectsPeriodsOn (frameAt word).child (frameAt word).coherentConstantU
      (frameAt word).coherentConstantV (frameAt word).closedPolygon
      ((frameAt word).sheetMin (quarterTurnField (standardField (conjWord word)))))
    (hE : ∀ s ∈ (ordinaryStandardCopy parents word .even 5).val.sites, s ∈ (frameAt word).closedPolygon)
    (hstar : StarZoneInputs word) (heps : (frameAt word).eps = -1)
    (hsG : ∀ s ∈ (ordinaryStandardCopy parents word .even 5).val.sites,
      (frameAt word).sGrade s ≤ 2 * ((frameAt word).child.den + (frameAt word).child.num) - 1) :
    ∃ g : ℤ, (ordinaryStandardCopy parents word .even 5).val.Agrees (standardField word) g :=
  nominal_even_five parents word hproper hodd hperO hper hE
    (fun s hs => sheetC_le_sheetA_of_mirror hstar heps (hE s hs) (hsG s hs))


/-- **The upper attainment premise, on the copy sites it is used on (task 48).** For the ordinary even standard output of `word`, on the
sites of its slot-`slot` copy that lie in the upper part `2(d+n) − 1 < sGrade` of the child frame of `word`, `C ≤ A` for the sheets of
`quarterTurnField (standardField (conjWord word))`. Checked on the words of length at most three that have an ordinary even copy
(`scripts/upper_attainment_on_copies.py`, data `ordinary_copy_dump.log` and `ordinary_copy_dump_two.log`): slot five holds on all 36
such words, both phases; slot four holds on the 23 words ending in one or three and fails on the 13 words ending in two, whose even
standard tile is the corrected one (`tableKind .two .standardEven = .shortL`), so the premise does not apply to them. -/
def UpperAttainmentOn (parents : TileParents) (word : Word) (slot : Fin 6) : Prop :=
  ∀ s ∈ (ordinaryStandardCopy parents word .even slot).val.sites,
    2 * ((frameAt word).child.den + (frameAt word).child.num) - 1 < (frameAt word).sGrade s →
      (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) s ≤
        (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) s

/-- The words whose even standard output is the ordinary tile: the last digit is one or three. The table of kinds gives
`tableKind .one _ = .ordinary` and `tableKind .three .standardEven = .ordinary`, while `tableKind .two .standardEven = .shortL`
(the corrected tile), so the ordinary even copies of a word ending in two are not its output. -/
def OrdinaryEvenWord (word : Word) : Prop :=
  word.getLast? = some Digit.one ∨ word.getLast? = some Digit.three

/-- Slot four for `ε = +1` on a word ending in one or three, with the named premise `UpperAttainmentOn` on the copy sites in the
upper part. -/
theorem nominal_even_four_of_upper (parents : TileParents) (word : Word) (hproper : ∃ x ∈ word, x ≠ Digit.three)
    (hodd : ∃ g : ℤ, parents.odd.val.Agrees (quarterTurnField (standardField (conjWord word))) g)
    (hper : RespectsPeriodsOn (frameAt word).child (frameAt word).coherentConstantU
      (frameAt word).coherentConstantV (frameAt word).closedPolygon
      ((frameAt word).sheetMin (quarterTurnField (standardField (conjWord word)))))
    (hE : ∀ s ∈ (ordinaryStandardCopy parents word .even 4).val.sites, s ∈ (frameAt word).closedPolygon)
    (hU : OrdinaryEvenWord word ∧ UpperAttainmentOn parents word 4)
    (hsU : ∀ s ∈ (ordinaryStandardCopy parents word .even 4).val.sites,
      2 * ((frameAt word).child.den + (frameAt word).child.num) - 1 < (frameAt word).sGrade s) :
    ∃ g : ℤ, (ordinaryStandardCopy parents word .even 4).val.Agrees (standardField word) g :=
  nominal_even_four parents word hproper hodd hper hE
    (fun s hs => hU.2 s hs (hsU s hs))

/-- Slot five for `ε = +1` on a word ending in one or three, with the named premise `UpperAttainmentOn` on the copy sites in the
upper part. -/
theorem nominal_even_five_of_upper (parents : TileParents) (word : Word) (hproper : ∃ x ∈ word, x ≠ Digit.three)
    (hodd : ∃ g : ℤ, parents.odd.val.Agrees (quarterTurnField (standardField (conjWord word))) g)
    {cU cV : ℤ} (hperO : HasGeneratorPeriods (parentsAt word).odd
      (quarterTurnField (standardField (conjWord word))) cU cV)
    (hper : RespectsPeriodsOn (frameAt word).child (frameAt word).coherentConstantU
      (frameAt word).coherentConstantV (frameAt word).closedPolygon
      ((frameAt word).sheetMin (quarterTurnField (standardField (conjWord word)))))
    (hE : ∀ s ∈ (ordinaryStandardCopy parents word .even 5).val.sites, s ∈ (frameAt word).closedPolygon)
    (hU : OrdinaryEvenWord word ∧ UpperAttainmentOn parents word 5)
    (hsU : ∀ s ∈ (ordinaryStandardCopy parents word .even 5).val.sites,
      2 * ((frameAt word).child.den + (frameAt word).child.num) - 1 < (frameAt word).sGrade s) :
    ∃ g : ℤ, (ordinaryStandardCopy parents word .even 5).val.Agrees (standardField word) g :=
  nominal_even_five parents word hproper hodd hperO hper hE
    (fun s hs => hU.2 s hs (hsU s hs))


end FLatticePaper.Construction
