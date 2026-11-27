import FLatticePaper.Plane.Induction.FreeSchedule
import FLatticePaper.Plane.Induction.PassageRank
import FLatticePaper.Plane.Induction.PassagePR
import FLatticePaper.Plane.Induction.ComparisonTransfer
import FLatticePaper.Plane.Induction.MinPassage
import FLatticePaper.Plane.Induction.KMinBridge
import FLatticePaper.Plane.Induction.TransferW1
import FLatticePaper.Plane.Induction.FortAtRestricted

/-! # The passage keeps the pair: `P ≤ cutPrice` and `J_η ≤ 0` along the passage (no polygon bound on the endpoint)

Along a passage step (a black edge or a forced white edge, both signs) the price and the rounded slip do not increase
(`price_nonincrease_black_PR`, `jminus/jplus_nonincrease_black`, `price_nonincrease_forced_of_sat_PR`,
`jminus/jplus_nonincrease_forced_of_sat_PR`). The invariant `P ≤ cutPrice ∧ J_η ≤ 0` therefore holds at every point of the
passage from the minimum `(cutPrice, 0)`, and at the endpoint `K = cutPrice` forces the pair `(cutPrice, 0)`. -/

namespace FLatticePaper.PassageInv

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank
  FLatticePaper.KMinBridge FLatticePaper.MinPassage FLatticePaper.TransferW1 FLatticePaper.FreeSchedule
  FLatticePaper.PassagePR FLatticePaper.PassageRank

/-- The invariant for the minus sign: `P ≤ cutPrice` and `J_- ≤ 0`. -/
def InvM (word : Word) (z : Site) : Prop :=
  (frameAt word).price (standardField word) z ≤ (frameAt word).cutPrice ∧
    (frameAt word).roundedSlip (standardField word) (-1) z ≤ 0

/-- The invariant for the plus sign: `P ≤ cutPrice` and `J_+ ≤ 0`. -/
def InvP (word : Word) (z : Site) : Prop :=
  (frameAt word).price (standardField word) z ≤ (frameAt word).cutPrice ∧
    (frameAt word).roundedSlip (standardField word) 1 z ≤ 0

theorem roundedSlip_neg_eq (word : Word) (z : Site) :
    (frameAt word).roundedSlip (standardField word) (-1) z =
      (standardField word z - standardField word (z + -(frameAt word).shortShift) + 1) / 2 := by
  unfold ChildFrame.roundedSlip ChildFrame.slip
  simp only [neg_one_smul]

theorem roundedSlip_pos_eq (word : Word) (z : Site) :
    (frameAt word).roundedSlip (standardField word) 1 z =
      (standardField word z - standardField word (z + (frameAt word).shortShift) + 1) / 2 := by
  unfold ChildFrame.roundedSlip ChildFrame.slip
  simp only [one_smul]

/-- **The reach lemma with an invariant.** The reach of `reach_nonfree` keeps an invariant that propagates along the steps. -/
theorem reach_nonfree_inv {α : Type*} (valid nf Inv : α → Prop) (Step : α → α → Prop)
    (hsucc : ∀ z, valid z → nf z → ∃ o, Step z o ∧ valid o)
    (hrank : ∃ ρ : α → ℕ, ∀ z o, valid z → nf z → Step z o → valid o → nf o → ρ o < ρ z)
    (hinv : ∀ z o, valid z → nf z → Step z o → valid o → Inv z → Inv o) :
    ∀ z0, valid z0 → nf z0 → Inv z0 → ∃ f, valid f ∧ ¬ nf f ∧ Inv f := by
  obtain ⟨ρ, hρ⟩ := hrank
  suffices H : ∀ n : ℕ, ∀ z, ρ z ≤ n → valid z → nf z → Inv z → ∃ f, valid f ∧ ¬ nf f ∧ Inv f from
    fun z0 hv hn hI => H (ρ z0) z0 le_rfl hv hn hI
  intro n
  induction n with
  | zero =>
    intro z hz hv hn hI
    obtain ⟨o, hS, hvo⟩ := hsucc z hv hn
    by_cases hno : nf o
    · have := hρ z o hv hn hS hvo hno
      omega
    · exact ⟨o, hvo, hno, hinv z o hv hn hS hvo hI⟩
  | succ n ih =>
    intro z hz hv hn hI
    obtain ⟨o, hS, hvo⟩ := hsucc z hv hn
    by_cases hno : nf o
    · exact ih o (by have := hρ z o hv hn hS hvo hno; omega) hvo hno (hinv z o hv hn hS hvo hI)
    · exact ⟨o, hvo, hno, hinv z o hv hn hS hvo hI⟩

/-- **A passage step does not increase `(P, J_-)`** (minus), from a nonfree polygon point to a polygon point. -/
theorem step_inv_minus {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hPR : FLatticePaper.PassagePR.PriceRangeOn word)
    (hW : HasSatSelection (standardField word))
    (hW1 : FLatticePaper.W1.W1Forced (frameAt word).child.num (frameAt word).child.den (standardField word))
    {z o : Site} (hzE : z ∈ (frameAt word).closedPolygon) (hNF : Nonfree (frameAt word) z)
    (hPS : PassageStep (frameAt word).child.num (frameAt word).child.den (standardField word) z o)
    (hoE : o ∈ (frameAt word).closedPolygon) :
    (frameAt word).price (standardField word) o ≤ (frameAt word).price (standardField word) z ∧
      (frameAt word).roundedSlip (standardField word) (-1) o ≤ (frameAt word).roundedSlip (standardField word) (-1) z := by
  have hpk := packet_of_strong h hSE
  rcases hPS with ⟨hb, hi⟩ | ⟨hw, hF⟩
  · have hP := price_nonincrease_black_PR h hSE hPR hpk hzE hb hi
    have hJ := jminus_nonincrease_black h hSE hpk hzE hb hi
    rw [roundedSlip_neg_eq, roundedSlip_neg_eq]
    exact ⟨hP, hJ⟩
  · have hf := FLatticePaper.W1.forcedEdgeIn_forced hF
    have hSIz := nonfree_strictInterior (frameAt word) hzE hNF
    have hT := hT_of_W1 h hSE hPR hW hW1
    have hP := price_nonincrease_forced_of_sat_PR h hSE hPR hT hSIz hw hzE hf hoE
    have hJ := jminus_nonincrease_forced_of_sat_PR h hSE hPR hT hSIz hw hzE hf hoE
    rw [roundedSlip_neg_eq, roundedSlip_neg_eq]
    exact ⟨hP, hJ⟩

/-- **A passage step does not increase `(P, J_+)`** (plus). -/
theorem step_inv_plus {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hPR : FLatticePaper.PassagePR.PriceRangeOn word)
    (hW : HasSatSelection (standardField word))
    (hW1 : FLatticePaper.W1.W1Forced (frameAt word).child.num (frameAt word).child.den (standardField word))
    {z o : Site} (hzE : z ∈ (frameAt word).closedPolygon) (hNF : Nonfree (frameAt word) z)
    (hPS : PassageStep (frameAt word).child.num (frameAt word).child.den (standardField word) z o)
    (hoE : o ∈ (frameAt word).closedPolygon) :
    (frameAt word).price (standardField word) o ≤ (frameAt word).price (standardField word) z ∧
      (frameAt word).roundedSlip (standardField word) 1 o ≤ (frameAt word).roundedSlip (standardField word) 1 z := by
  have hpk := packet_of_strong h hSE
  rcases hPS with ⟨hb, hi⟩ | ⟨hw, hF⟩
  · have hP := price_nonincrease_black_PR h hSE hPR hpk hzE hb hi
    have hJ := jplus_nonincrease_black h hSE hpk hzE hb hi
    rw [roundedSlip_pos_eq, roundedSlip_pos_eq]
    exact ⟨hP, hJ⟩
  · have hf := FLatticePaper.W1.forcedEdgeIn_forced hF
    have hSIz := nonfree_strictInterior (frameAt word) hzE hNF
    have hT := hT_of_W1 h hSE hPR hW hW1
    have hP := price_nonincrease_forced_of_sat_PR h hSE hPR hT hSIz hw hzE hf hoE
    have hJ := jplus_nonincrease_forced_of_sat_PR h hSE hPR hT hSIz hw hzE hf hoE
    rw [roundedSlip_pos_eq, roundedSlip_pos_eq]
    exact ⟨hP, hJ⟩

theorem kMinusW_eq' (word : Word) (z : Site) :
    kMinusW word z = (frameAt word).price (standardField word) z +
      (frameAt word).roundedSlip (standardField word) (-1) z := by
  unfold kMinusW jMinusW ChildFrame.roundedSlip ChildFrame.slip
  simp only [neg_one_smul]

theorem kPlusW_eq' (word : Word) (z : Site) :
    kPlusW word z = (frameAt word).price (standardField word) z +
      (frameAt word).roundedSlip (standardField word) 1 z := by
  unfold kPlusW jPlusW ChildFrame.roundedSlip ChildFrame.slip
  simp only [one_smul]

/-- **The minus pair from the invariant** (no polygon bound): `K_- = cutPrice` and `P ≤ cutPrice`, `J_- ≤ 0` give `(cutPrice, 0)`. -/
theorem minus_pair_of_inv {word : Word} {f : Site} (hI : InvM word f) (hK : kMinusW word f = (frameAt word).cutPrice) :
    (frameAt word).price (standardField word) f = (frameAt word).cutPrice ∧
      (frameAt word).roundedSlip (standardField word) (-1) f = 0 := by
  rw [kMinusW_eq'] at hK
  have := hI.1
  have := hI.2
  constructor <;> omega

/-- **The plus pair from the invariant**. -/
theorem plus_pair_of_inv {word : Word} {f : Site} (hI : InvP word f) (hK : kPlusW word f = (frameAt word).cutPrice) :
    (frameAt word).price (standardField word) f = (frameAt word).cutPrice ∧
      (frameAt word).roundedSlip (standardField word) 1 f = 0 := by
  rw [kPlusW_eq'] at hK
  have := hI.1
  have := hI.2
  constructor <;> omega

/-- **The minus passage keeps the invariant**: the free endpoint `f` of the passage from `z₀` (with the invariant at `z₀`) is
in the polygon, has `kMinusW f = kMinusW z₀`, is not nonfree, and satisfies `InvM f`. -/
theorem minus_passage_inv {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hPR : FLatticePaper.PassagePR.PriceRangeOn word)
    (hW : HasSatSelection (standardField word))
    (hW1 : FLatticePaper.W1.W1Forced (frameAt word).child.num (frameAt word).child.den (standardField word))
    {S : Set Site} (hfort : FortAt (Nonfree (frameAt word)) (standardField word) S) {z₀ : Site} (hz₀S : z₀ ∈ S)
    (hz₀E : z₀ ∈ (frameAt word).closedPolygon)
    (hmin : ∀ w ∈ S, kMinusW word z₀ ≤ kMinusW word w) (hI0 : InvM word z₀) :
    ∃ f, f ∈ S ∧ f ∈ (frameAt word).closedPolygon ∧ kMinusW word f = kMinusW word z₀ ∧ ¬ Nonfree (frameAt word) f ∧
      InvM word f := by
  by_cases hnf₀ : Nonfree (frameAt word) z₀
  · have hpk := packet_of_strong h hSE
    obtain ⟨R, hR⟩ := sheetMin_burning_of_strong h hSE
    obtain ⟨ρ, hρ⟩ := passage_rank (frameAt word) (fun s hs => standardField_eq_sheetMin_of_strong h hSE hs) hR
    obtain ⟨f, ⟨hfS, hfE, hfK⟩, hfn, hfI⟩ := reach_nonfree_inv
      (fun z => z ∈ S ∧ z ∈ (frameAt word).closedPolygon ∧ kMinusW word z = kMinusW word z₀)
      (fun z => Nonfree (frameAt word) z)
      (fun z => InvM word z)
      (PassageStep (frameAt word).child.num (frameAt word).child.den (standardField word))
      (by
        intro z hv hnfz
        obtain ⟨hzS, hzE, hzK⟩ := hv
        have hSI := nonfree_strictInterior (frameAt word) hzE hnfz
        have hstar := strictInterior_star (frameAt word) hSI
        have hminz : ∀ w ∈ S, kMinusW word z ≤ kMinusW word w := fun w hw => by
          rw [hzK]
          exact hmin w hw
        rcases hpk.binary z with hb | hb
        · obtain ⟨i, hi, hiS, hiK⟩ := minK_black_input_minus h hSE hPR hpk hfort hzS hnfz hzE hb hminz
          have hiE : i ∈ (frameAt word).closedPolygon := by
            rcases hi with rfl | rfl
            · exact hstar.2.1
            · exact hstar.2.2
          exact ⟨i, Or.inl ⟨hb, hi⟩, ⟨hiS, hiE, by rw [hiK, hzK]⟩⟩
        · obtain ⟨o', hf'⟩ := hW1 z hSI hb
          have hf := FLatticePaper.W1.forcedEdgeIn_forced hf'
          have hio := forced_input_of_unseeded hf
          have hoE : o' ∈ (frameAt word).closedPolygon := by
            rcases hio with rfl | rfl
            · exact hstar.2.1
            · exact hstar.2.2
          obtain ⟨hoS, hoK⟩ := minK_white_forced_minus h hSE hPR hW hW1 hfort hzS hzE hnfz hb hf hoE hminz
          exact ⟨o', Or.inr ⟨hb, hf'⟩, ⟨hoS, hoE, by rw [hoK, hzK]⟩⟩)
      ⟨ρ, fun z o hz hnz hG ho hno => hρ z o ⟨hz.2.1, hnz⟩ ⟨ho.2.1, hno⟩ hG⟩
      (fun z o hv hnz hG ho hI => by
        have hs := step_inv_minus h hSE hPR hW hW1 hv.2.1 hnz hG ho.2.1
        exact ⟨hs.1.trans hI.1, hs.2.trans hI.2⟩)
      z₀ ⟨hz₀S, hz₀E, rfl⟩ hnf₀ hI0
    exact ⟨f, hfS, hfE, hfK, hfn, hfI⟩
  · exact ⟨z₀, hz₀S, hz₀E, rfl, hnf₀, hI0⟩


/-- **The plus passage keeps the invariant**: the free endpoint `f` of the `K_+`-passage from `z₀` (with `InvP z₀`) is in the
polygon, has `kPlusW f = kPlusW z₀`, is not nonfree, and satisfies `InvP f`. -/
theorem plus_passage_inv {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hPR : FLatticePaper.PassagePR.PriceRangeOn word)
    (hW : HasSatSelection (standardField word))
    (hW1 : FLatticePaper.W1.W1Forced (frameAt word).child.num (frameAt word).child.den (standardField word))
    {S : Set Site} (hfort : FortAt (Nonfree (frameAt word)) (standardField word) S) {z₀ : Site} (hz₀S : z₀ ∈ S)
    (hz₀E : z₀ ∈ (frameAt word).closedPolygon)
    (hmin : ∀ w ∈ S, kPlusW word z₀ ≤ kPlusW word w) (hI0 : InvP word z₀) :
    ∃ f, f ∈ S ∧ f ∈ (frameAt word).closedPolygon ∧ kPlusW word f = kPlusW word z₀ ∧ ¬ Nonfree (frameAt word) f ∧
      InvP word f := by
  by_cases hnf₀ : Nonfree (frameAt word) z₀
  · have hpk := packet_of_strong h hSE
    obtain ⟨R, hR⟩ := sheetMin_burning_of_strong h hSE
    obtain ⟨ρ, hρ⟩ := passage_rank (frameAt word) (fun s hs => standardField_eq_sheetMin_of_strong h hSE hs) hR
    obtain ⟨f, ⟨hfS, hfE, hfK⟩, hfn, hfI⟩ := reach_nonfree_inv
      (fun z => z ∈ S ∧ z ∈ (frameAt word).closedPolygon ∧ kPlusW word z = kPlusW word z₀)
      (fun z => Nonfree (frameAt word) z)
      (fun z => InvP word z)
      (PassageStep (frameAt word).child.num (frameAt word).child.den (standardField word))
      (by
        intro z hv hnfz
        obtain ⟨hzS, hzE, hzK⟩ := hv
        have hSI := nonfree_strictInterior (frameAt word) hzE hnfz
        have hstar := strictInterior_star (frameAt word) hSI
        have hminz : ∀ w ∈ S, kPlusW word z ≤ kPlusW word w := fun w hw => by
          rw [hzK]
          exact hmin w hw
        rcases hpk.binary z with hb | hb
        · obtain ⟨i, hi, hiS, hiK⟩ := minK_black_input_plus h hSE hPR hpk hfort hzS hnfz hzE hb hminz
          have hiE : i ∈ (frameAt word).closedPolygon := by
            rcases hi with rfl | rfl
            · exact hstar.2.1
            · exact hstar.2.2
          exact ⟨i, Or.inl ⟨hb, hi⟩, ⟨hiS, hiE, by rw [hiK, hzK]⟩⟩
        · obtain ⟨o', hf'⟩ := hW1 z hSI hb
          have hf := FLatticePaper.W1.forcedEdgeIn_forced hf'
          have hio := forced_input_of_unseeded hf
          have hoE : o' ∈ (frameAt word).closedPolygon := by
            rcases hio with rfl | rfl
            · exact hstar.2.1
            · exact hstar.2.2
          obtain ⟨hoS, hoK⟩ := minK_white_forced_plus h hSE hPR hW hW1 hfort hzS hzE hnfz hb hf hoE hminz
          exact ⟨o', Or.inr ⟨hb, hf'⟩, ⟨hoS, hoE, by rw [hoK, hzK]⟩⟩)
      ⟨ρ, fun z o hz hnz hG ho hno => hρ z o ⟨hz.2.1, hnz⟩ ⟨ho.2.1, hno⟩ hG⟩
      (fun z o hv hnz hG ho hI => by
        have hs := step_inv_plus h hSE hPR hW hW1 hv.2.1 hnz hG ho.2.1
        exact ⟨hs.1.trans hI.1, hs.2.trans hI.2⟩)
      z₀ ⟨hz₀S, hz₀E, rfl⟩ hnf₀ hI0
    exact ⟨f, hfS, hfE, hfK, hfn, hfI⟩
  · exact ⟨z₀, hz₀S, hz₀E, rfl, hnf₀, hI0⟩


end FLatticePaper.PassageInv
