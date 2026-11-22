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

end FLatticePaper.Construction
