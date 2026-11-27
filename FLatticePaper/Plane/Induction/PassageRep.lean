import FLatticePaper.Plane.Induction.RepRank
import FLatticePaper.Plane.Induction.KMinBridge
import FLatticePaper.Plane.Induction.FortAt
import FLatticePaper.Plane.Induction.PairTranslate
import FLatticePaper.Plane.Induction.Potentials
import FLatticePaper.Plane.Induction.MinPassage
import FLatticePaper.Plane.Induction.TieReduce
import FLatticePaper.Plane.Induction.PassageInv
import FLatticePaper.Plane.Induction.WordWebHyp

/-! # The passage from an arbitrary start on strict representatives (Q36, T1–T2)

* `fortAt_span_translate`: a fort for the nonfree condition is carried by span translations (T1).
* `price_span`, `slip_span`, `kMinus_span`, `kPlus_span`: the price, the slip and the potentials `K_±` shift additively along the
  span (T2). The shift of `K_−` is `−i − j`, the shift of `K_+` is `−i + j`, for the span vector `combine i j`. -/

namespace FLatticePaper.PassageRep

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.FreeClosure FLatticePaper.SquareClauses
  FLatticePaper.AndOrRank FLatticePaper.BulkForced FLatticePaper.KMinBridge FLatticePaper.PassageRank
  FLatticePaper.ChainDeck FLatticePaper.RepRank FLatticePaper.MinPassage FLatticePaper.TransferW1
  FLatticePaper.ProtectedWeb FLatticePaper.PassagePR

theorem span_neg_mem (frame : ChildFrame) {v : Site} (hv : v ∈ frame.child.modifiedDeck.span) :
    -v ∈ frame.child.modifiedDeck.span := by
  obtain ⟨i, j, rfl⟩ := hv
  refine ⟨-i, -j, ?_⟩
  ext <;> simp [PeriodDeck.combine]
  all_goals ring

/-- **T1.** A fort for the nonfree condition is carried by a span translation. -/
theorem fortAt_span_translate (frame : ChildFrame) {F : Field}
    (hinv : ∀ z v, v ∈ frame.child.modifiedDeck.span → laplacian F (z + v) = laplacian F z)
    {S : Set Site} (hS : FortAt (fun z => Nonfree frame z) F S) {v : Site}
    (hv : v ∈ frame.child.modifiedDeck.span) :
    FortAt (fun z => Nonfree frame z) F {w | w - v ∈ S} := by
  intro site hsite hnf
  have hsite' : site - v ∈ S := hsite
  have hnf' : Nonfree frame (site - v) := by
    have h := nonfree_add_span frame hnf (span_neg_mem frame hv)
    rw [← sub_eq_add_neg] at h
    exact h
  have H := hS (site - v) hsite' hnf'
  have hlap : laplacian F site = laplacian F (site - v) := by
    rw [← hinv (site - v) v hv, sub_add_cancel]
  have hEvn : EvenSite (-v) := by
    have := ProtectedWeb.span_even frame (span_neg_mem frame hv)
    exact this
  have hn : incomingNeg (site - v) = incomingNeg site - v := by
    rw [sub_eq_add_neg, incomingNeg_add site (-v) hEvn, ← sub_eq_add_neg]
  have hp : incomingPos (site - v) = incomingPos site - v := by
    rw [sub_eq_add_neg, incomingPos_add site (-v) hEvn, ← sub_eq_add_neg]
  rcases H with ⟨hl, hin⟩ | ⟨hl, hinN, hinP⟩
  · left
    refine ⟨by rw [hlap, hl], ?_⟩
    simp only [Set.mem_setOf_eq]
    rw [← hn, ← hp]
    exact hin
  · right
    refine ⟨by rw [hlap, hl], ?_, ?_⟩
    · simp only [Set.mem_setOf_eq]
      rw [← hn]
      exact hinN
    · simp only [Set.mem_setOf_eq]
      rw [← hp]
      exact hinP

theorem combine_eq_smul (frame : ChildFrame) (i j : ℤ) :
    frame.child.modifiedDeck.combine i j = i • frame.child.modifiedDeck.kernel + j • frame.child.modifiedDeck.transverse := by
  ext <;> simp [PeriodDeck.combine]

/-- **T2.** The price shifts by `−i` along `combine i j`. -/
theorem price_span (frame : ChildFrame) {F : Field} (hP : frame.Packet F) (i j : ℤ) (x : Site) :
    frame.price F (x + frame.child.modifiedDeck.combine i j) = frame.price F x - i := by
  rw [combine_eq_smul, ← add_assoc, price_transverse_mul frame hP, price_kernel_mul frame hP]

/-- **T2.** The slip `D_η` shifts by `2η j` along `combine i j`. -/
theorem slip_span (frame : ChildFrame) {F : Field} {cU cV : ℤ} (h : HasGeneratorPeriods frame.child F cU cV)
    (η : ℤ) (i j : ℤ) (x : Site) :
    frame.slip F η (x + frame.child.modifiedDeck.combine i j) = frame.slip F η x + j * (2 * η) := by
  rw [combine_eq_smul, ← add_assoc]
  have hK : ∀ z, frame.slip F η (z + frame.child.modifiedDeck.kernel) = frame.slip F η z + 0 := fun z => by
    rw [ChildFrame.slip_kernel frame F h η z]
    ring
  have hT : ∀ z, frame.slip F η (z + frame.child.modifiedDeck.transverse) = frame.slip F η z + 2 * η :=
    fun z => ChildFrame.slip_transverse frame F h η z
  have h1 := PairTranslate.drift_zsmul (frame.slip F η) frame.child.modifiedDeck.kernel 0 hK i x
  have h2 := PairTranslate.drift_zsmul (frame.slip F η) frame.child.modifiedDeck.transverse (2 * η) hT j
    (x + i • frame.child.modifiedDeck.kernel)
  rw [h2, h1]
  ring

/-- The minus rounded slip is the half of the slip at `η = −1` plus one. -/
theorem jMinusW_eq_slip (word : Word) (z : Site) :
    jMinusW word z = ((frameAt word).slip (standardField word) (-1) z + 1) / 2 := by
  unfold jMinusW ChildFrame.slip
  simp

/-- The plus rounded slip is the half of the slip at `η = +1` plus one. -/
theorem jPlusW_eq_slip (word : Word) (z : Site) :
    jPlusW word z = ((frameAt word).slip (standardField word) 1 z + 1) / 2 := by
  unfold jPlusW ChildFrame.slip
  simp

/-- **T2.** `K_− = P + J_−` shifts by `−i − j` along `combine i j`. -/
theorem kMinus_span (word : Word) (hS : StrongCore word) (i j : ℤ) (x : Site) :
    kMinusW word (x + (frameAt word).child.modifiedDeck.combine i j) = kMinusW word x - i - j := by
  unfold kMinusW
  rw [jMinusW_eq_slip, jMinusW_eq_slip, price_span (frameAt word) hS.packet i j x,
    slip_span (frameAt word) hS.packet.periods (-1) i j x]
  have : (frameAt word).slip (standardField word) (-1) x + j * (2 * -1) =
      (frameAt word).slip (standardField word) (-1) x - 2 * j := by ring
  rw [this]
  omega

/-- **T2.** `K_+ = P + J_+` shifts by `−i + j` along `combine i j`. -/
theorem kPlus_span (word : Word) (hS : StrongCore word) (i j : ℤ) (x : Site) :
    kPlusW word (x + (frameAt word).child.modifiedDeck.combine i j) = kPlusW word x - i + j := by
  unfold kPlusW
  rw [jPlusW_eq_slip, jPlusW_eq_slip, price_span (frameAt word) hS.packet i j x,
    slip_span (frameAt word) hS.packet.periods 1 i j x]
  have : (frameAt word).slip (standardField word) 1 x + j * (2 * 1) =
      (frameAt word).slip (standardField word) 1 x + 2 * j := by ring
  rw [this]
  omega


theorem span_nonneg_neg_mem (frame : ChildFrame) {v : Site} (hv : v ∈ frame.child.modifiedDeck.span) :
    -v ∈ frame.child.modifiedDeck.span := span_neg_mem frame hv

/-- The input of the representative translates back to an input of the site. -/
theorem input_back (frame : ChildFrame) {z x : Site} (hv : EvenSite (repShift frame z))
    (hi : x = incomingNeg (z + repShift frame z) ∨ x = incomingPos (z + repShift frame z)) :
    (x - repShift frame z = incomingNeg z ∨ x - repShift frame z = incomingPos z) := by
  rcases hi with hi | hi
  · left
    rw [hi, incomingNeg_add z _ hv, add_sub_cancel_right]
  · right
    rw [hi, incomingPos_add z _ hv, add_sub_cancel_right]

/-- **T3 (minus).** A nonfree minimiser of `K_−` in a fort has a successor in the fort with the same `K_−`, along a
black input or an unseeded forced white step. The fort is translated so that the site lands in `E°`. -/
theorem succ_rep_minus {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hcore : StrongCore word)
    (hPR : FLatticePaper.PassagePR.PriceRangeOn word)
    (hW : HasSatSelection (standardField word))
    (hW1 : FLatticePaper.W1.W1Forced (frameAt word).child.num (frameAt word).child.den (standardField word))
    {S : Set Site} (hfort : FortAt (Nonfree (frameAt word)) (standardField word) S) {z : Site}
    (hzS : z ∈ S) (hnf : Nonfree (frameAt word) z)
    (hmin : ∀ w ∈ S, kMinusW word z ≤ kMinusW word w) :
    ∃ o, RepStep (standardField word) z o ∧ o ∈ S ∧ kMinusW word o = kMinusW word z := by
  have hpk := hcore.packet
  have hinv : ∀ w v, v ∈ (frameAt word).child.modifiedDeck.span →
      laplacian (standardField word) (w + v) = laplacian (standardField word) w := by
    intro w v hv
    obtain ⟨i, j, rfl⟩ := hv
    exact laplacian_add_combine hpk.periods w i j
  obtain ⟨hv, hsi⟩ := repShift_spec (frameAt word) hnf
  have hEv : EvenSite (repShift (frameAt word) z) := ProtectedWeb.span_even (frameAt word) hv
  have hv2 := hv
  have hv3 := hv
  obtain ⟨i0, j0, hij⟩ := hv
  have hfort' := fortAt_span_translate (frameAt word) hinv hfort hv2
  have hz'S : z + repShift (frameAt word) z ∈ {w | w - repShift (frameAt word) z ∈ S} := by
    show z + repShift (frameAt word) z - repShift (frameAt word) z ∈ S
    rw [add_sub_cancel_right]
    exact hzS
  have hnf' : Nonfree (frameAt word) (z + repShift (frameAt word) z) :=
    nonfree_add_span (frameAt word) hnf hv3
  have hstar := TransferW1.strictInterior_star (frameAt word) hsi
  have hzE' : z + repShift (frameAt word) z ∈ (frameAt word).closedPolygon := hstar.1
  have hminz' : ∀ w ∈ {w | w - repShift (frameAt word) z ∈ S},
      kMinusW word (z + repShift (frameAt word) z) ≤ kMinusW word w := by
    intro w hw
    have hw0 := hmin (w - repShift (frameAt word) z) hw
    have k1 := kMinus_span word hcore i0 j0 z
    have k2 := kMinus_span word hcore i0 j0 (w - repShift (frameAt word) z)
    rw [← hij] at k1 k2
    rw [sub_add_cancel] at k2
    linarith
  have hw' : laplacian (standardField word) (z + repShift (frameAt word) z) = laplacian (standardField word) z :=
    hinv z _ hv2
  have k1 := kMinus_span word hcore i0 j0 z
  rw [← hij] at k1
  rcases hpk.binary z with hb | hb
  · -- black: the minimal input in the translated fort
    have hb' : laplacian (standardField word) (z + repShift (frameAt word) z) = -1 := by
      rw [hw']
      exact hb
    obtain ⟨i, hi, hiS, hiK⟩ :=
      FLatticePaper.KMinBridge.minK_black_input_minus h hSE hPR hpk hfort' hz'S hnf' hzE' hb' hminz'
    have hoS : i - repShift (frameAt word) z ∈ S := hiS
    refine ⟨i - repShift (frameAt word) z, Or.inl ⟨hb, input_back (frameAt word) hEv hi⟩, hoS, ?_⟩
    have k3 := kMinus_span word hcore i0 j0 (i - repShift (frameAt word) z)
    rw [← hij, sub_add_cancel] at k3
    linarith
  · -- white: the forced input of the representative, forced by `W1`
    have hw0 : laplacian (standardField word) (z + repShift (frameAt word) z) = 0 := by
      rw [hw']
      exact hb
    obtain ⟨o', hf'⟩ := hW1 (z + repShift (frameAt word) z) hsi hw0
    have hf := FLatticePaper.W1.forcedEdgeIn_forced hf'
    have hio := forced_input_of_unseeded hf
    have hoE : o' ∈ (frameAt word).closedPolygon := by
      rcases hio with hio | hio
      · rw [hio]
        exact hstar.2.1
      · rw [hio]
        exact hstar.2.2
    obtain ⟨hoS', hoK⟩ := FLatticePaper.MinPassage.minK_white_forced_minus h hSE hPR hW hW1 hfort' hz'S hzE' hnf'
      hw0 hf hoE hminz'
    have hEvN : EvenSite (-repShift (frameAt word) z) := ProtectedWeb.span_even (frameAt word)
      (span_neg_mem (frameAt word) hv3)
    have hLN : ∀ x, laplacian (standardField word) (x + -repShift (frameAt word) z) =
        laplacian (standardField word) x := fun x => hinv x _ (span_neg_mem (frameAt word) hv3)
    have hfz := forcedEdge_add (standardField word) hEvN hLN hf
    rw [add_neg_cancel_right, ← sub_eq_add_neg] at hfz
    refine ⟨o' - repShift (frameAt word) z, Or.inr ⟨hb, hfz⟩, hoS', ?_⟩
    have k3 := kMinus_span word hcore i0 j0 (o' - repShift (frameAt word) z)
    rw [← hij, sub_add_cancel] at k3
    linarith

/-- **T3 (plus).** The plus analogue of `succ_rep_minus`. -/
theorem succ_rep_plus {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hcore : StrongCore word)
    (hPR : FLatticePaper.PassagePR.PriceRangeOn word)
    (hW : HasSatSelection (standardField word))
    (hW1 : FLatticePaper.W1.W1Forced (frameAt word).child.num (frameAt word).child.den (standardField word))
    {S : Set Site} (hfort : FortAt (Nonfree (frameAt word)) (standardField word) S) {z : Site}
    (hzS : z ∈ S) (hnf : Nonfree (frameAt word) z)
    (hmin : ∀ w ∈ S, kPlusW word z ≤ kPlusW word w) :
    ∃ o, RepStep (standardField word) z o ∧ o ∈ S ∧ kPlusW word o = kPlusW word z := by
  have hpk := hcore.packet
  have hinv : ∀ w v, v ∈ (frameAt word).child.modifiedDeck.span →
      laplacian (standardField word) (w + v) = laplacian (standardField word) w := by
    intro w v hv
    obtain ⟨i, j, rfl⟩ := hv
    exact laplacian_add_combine hpk.periods w i j
  obtain ⟨hv, hsi⟩ := repShift_spec (frameAt word) hnf
  have hEv : EvenSite (repShift (frameAt word) z) := ProtectedWeb.span_even (frameAt word) hv
  have hv2 := hv
  have hv3 := hv
  obtain ⟨i0, j0, hij⟩ := hv
  have hfort' := fortAt_span_translate (frameAt word) hinv hfort hv2
  have hz'S : z + repShift (frameAt word) z ∈ {w | w - repShift (frameAt word) z ∈ S} := by
    show z + repShift (frameAt word) z - repShift (frameAt word) z ∈ S
    rw [add_sub_cancel_right]
    exact hzS
  have hnf' : Nonfree (frameAt word) (z + repShift (frameAt word) z) :=
    nonfree_add_span (frameAt word) hnf hv3
  have hstar := TransferW1.strictInterior_star (frameAt word) hsi
  have hzE' : z + repShift (frameAt word) z ∈ (frameAt word).closedPolygon := hstar.1
  have hminz' : ∀ w ∈ {w | w - repShift (frameAt word) z ∈ S},
      kPlusW word (z + repShift (frameAt word) z) ≤ kPlusW word w := by
    intro w hw
    have hw0 := hmin (w - repShift (frameAt word) z) hw
    have k1 := kPlus_span word hcore i0 j0 z
    have k2 := kPlus_span word hcore i0 j0 (w - repShift (frameAt word) z)
    rw [← hij] at k1 k2
    rw [sub_add_cancel] at k2
    linarith
  have hw' : laplacian (standardField word) (z + repShift (frameAt word) z) = laplacian (standardField word) z :=
    hinv z _ hv2
  have k1 := kPlus_span word hcore i0 j0 z
  rw [← hij] at k1
  rcases hpk.binary z with hb | hb
  · have hb' : laplacian (standardField word) (z + repShift (frameAt word) z) = -1 := by
      rw [hw']
      exact hb
    obtain ⟨i, hi, hiS, hiK⟩ :=
      FLatticePaper.KMinBridge.minK_black_input_plus h hSE hPR hpk hfort' hz'S hnf' hzE' hb' hminz'
    have hoS : i - repShift (frameAt word) z ∈ S := hiS
    refine ⟨i - repShift (frameAt word) z, Or.inl ⟨hb, input_back (frameAt word) hEv hi⟩, hoS, ?_⟩
    have k3 := kPlus_span word hcore i0 j0 (i - repShift (frameAt word) z)
    rw [← hij, sub_add_cancel] at k3
    linarith
  · have hw0 : laplacian (standardField word) (z + repShift (frameAt word) z) = 0 := by
      rw [hw']
      exact hb
    obtain ⟨o', hf'⟩ := hW1 (z + repShift (frameAt word) z) hsi hw0
    have hf := FLatticePaper.W1.forcedEdgeIn_forced hf'
    have hio := forced_input_of_unseeded hf
    have hoE : o' ∈ (frameAt word).closedPolygon := by
      rcases hio with hio | hio
      · rw [hio]
        exact hstar.2.1
      · rw [hio]
        exact hstar.2.2
    obtain ⟨hoS', hoK⟩ := FLatticePaper.MinPassage.minK_white_forced_plus h hSE hPR hW hW1 hfort' hz'S hzE' hnf'
      hw0 hf hoE hminz'
    have hEvN : EvenSite (-repShift (frameAt word) z) := ProtectedWeb.span_even (frameAt word)
      (span_neg_mem (frameAt word) hv3)
    have hLN : ∀ x, laplacian (standardField word) (x + -repShift (frameAt word) z) =
        laplacian (standardField word) x := fun x => hinv x _ (span_neg_mem (frameAt word) hv3)
    have hfz := forcedEdge_add (standardField word) hEvN hLN hf
    rw [add_neg_cancel_right, ← sub_eq_add_neg] at hfz
    refine ⟨o' - repShift (frameAt word) z, Or.inr ⟨hb, hfz⟩, hoS', ?_⟩
    have k3 := kPlus_span word hcore i0 j0 (o' - repShift (frameAt word) z)
    rw [← hij, sub_add_cancel] at k3
    linarith


/-- The rounded slip at `η = −1` shifts by `−j` along `combine i j`. -/
theorem rs_minus_span (frame : ChildFrame) {F : Field} {cU cV : ℤ} (h : HasGeneratorPeriods frame.child F cU cV)
    (i j : ℤ) (x : Site) :
    frame.roundedSlip F (-1) (x + frame.child.modifiedDeck.combine i j) = frame.roundedSlip F (-1) x - j := by
  unfold ChildFrame.roundedSlip
  rw [slip_span frame h (-1) i j x]
  have e : frame.slip F (-1) x + j * (2 * -1) = frame.slip F (-1) x - 2 * j := by ring
  rw [e]
  omega

/-- The rounded slip at `η = +1` shifts by `+j` along `combine i j`. -/
theorem rs_plus_span (frame : ChildFrame) {F : Field} {cU cV : ℤ} (h : HasGeneratorPeriods frame.child F cU cV)
    (i j : ℤ) (x : Site) :
    frame.roundedSlip F 1 (x + frame.child.modifiedDeck.combine i j) = frame.roundedSlip F 1 x + j := by
  unfold ChildFrame.roundedSlip
  rw [slip_span frame h 1 i j x]
  have e : frame.slip F 1 x + j * (2 * 1) = frame.slip F 1 x + 2 * j := by ring
  rw [e]
  omega

/-- The minus rounded slip in the explicit form of the monotonicity lemmas. -/
theorem rs_minus_eq (word : Word) (x : Site) :
    (frameAt word).roundedSlip (standardField word) (-1) x =
      (standardField word x - standardField word (x + -(frameAt word).shortShift) + 1) / 2 := by
  unfold ChildFrame.roundedSlip ChildFrame.slip
  simp

/-- The plus rounded slip in the explicit form of the monotonicity lemmas. -/
theorem rs_plus_eq (word : Word) (x : Site) :
    (frameAt word).roundedSlip (standardField word) 1 x =
      (standardField word x - standardField word (x + (frameAt word).shortShift) + 1) / 2 := by
  unfold ChildFrame.roundedSlip ChildFrame.slip
  simp

/-- **Monotonicity along a representative step (minus).** `P` and the rounded slip `J_−` do not increase along a passage
step, at any nonfree site: the step is translated to the strict representative, where the polygon step lemmas apply. -/
theorem rep_mono_minus {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hcore : StrongCore word)
    (hPR : FLatticePaper.PassagePR.PriceRangeOn word)
    (hW : HasSatSelection (standardField word))
    (hW1 : FLatticePaper.W1.W1Forced (frameAt word).child.num (frameAt word).child.den (standardField word))
    {z o : Site} (hnf : Nonfree (frameAt word) z) (hG : RepStep (standardField word) z o) :
    (frameAt word).price (standardField word) o ≤ (frameAt word).price (standardField word) z ∧
      (frameAt word).roundedSlip (standardField word) (-1) o ≤
        (frameAt word).roundedSlip (standardField word) (-1) z := by
  have hpk := hcore.packet
  have hinv : ∀ w v, v ∈ (frameAt word).child.modifiedDeck.span →
      laplacian (standardField word) (w + v) = laplacian (standardField word) w := by
    intro w v hv
    obtain ⟨i, j, rfl⟩ := hv
    exact laplacian_add_combine hpk.periods w i j
  obtain ⟨hv, hsi⟩ := repShift_spec (frameAt word) hnf
  have hEv : EvenSite (repShift (frameAt word) z) := ProtectedWeb.span_even (frameAt word) hv
  have hv2 := hv
  obtain ⟨i0, j0, hij⟩ := hv
  have hstar := TransferW1.strictInterior_star (frameAt word) hsi
  have hzE' : z + repShift (frameAt word) z ∈ (frameAt word).closedPolygon := hstar.1
  have hpz := price_span (frameAt word) hcore.packet i0 j0 z
  have hpo := price_span (frameAt word) hcore.packet i0 j0 o
  have hrz := rs_minus_span (frameAt word) hcore.packet.periods i0 j0 z
  have hro := rs_minus_span (frameAt word) hcore.packet.periods i0 j0 o
  rw [← hij] at hpz hpo hrz hro
  rcases hG with ⟨hb, hadj⟩ | ⟨hw0, hf⟩
  · -- black step
    have hb' : laplacian (standardField word) (z + repShift (frameAt word) z) = -1 := by
      rw [hinv z _ hv2]
      exact hb
    have hadj' : o + repShift (frameAt word) z = incomingNeg (z + repShift (frameAt word) z) ∨
        o + repShift (frameAt word) z = incomingPos (z + repShift (frameAt word) z) := by
      rcases hadj with h1 | h1
      · left
        rw [h1, incomingNeg_add z _ hEv]
      · right
        rw [h1, incomingPos_add z _ hEv]
    have hP := price_nonincrease_black_PR h hSE hPR hpk hzE' hb' hadj'
    have hJ := jminus_nonincrease_black h hSE hpk hzE' hb' hadj'
    simp only [rs_minus_eq] at hrz hro ⊢
    constructor
    · linarith
    · linarith
  · -- forced white step
    have hLv : ∀ x, laplacian (standardField word) (x + repShift (frameAt word) z) =
        laplacian (standardField word) x := fun x => hinv x _ hv2
    have hf' := forcedEdge_add (standardField word) hEv hLv hf
    have hw' : laplacian (standardField word) (z + repShift (frameAt word) z) = 0 := by
      rw [hLv z]
      exact hw0
    have hSIz : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den
        (z + repShift (frameAt word) z) := hsi
    have hio := forced_input_of_unseeded hf
    have hoE : o + repShift (frameAt word) z ∈ (frameAt word).closedPolygon := by
      rcases hio with hio | hio
      · rw [hio, ← incomingNeg_add z _ hEv]
        exact hstar.2.1
      · rw [hio, ← incomingPos_add z _ hEv]
        exact hstar.2.2
    have hT := hT_of_W1 h hSE hPR hW hW1
    have hP := price_nonincrease_forced_of_sat_PR h hSE hPR hT hSIz hw' hzE' hf' hoE
    have hJ := jminus_nonincrease_forced_of_sat_PR h hSE hPR hT hSIz hw' hzE' hf' hoE
    simp only [rs_minus_eq] at hrz hro ⊢
    constructor
    · linarith
    · linarith

/-- **Monotonicity along a representative step (plus).** -/
theorem rep_mono_plus {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hcore : StrongCore word)
    (hPR : FLatticePaper.PassagePR.PriceRangeOn word)
    (hW : HasSatSelection (standardField word))
    (hW1 : FLatticePaper.W1.W1Forced (frameAt word).child.num (frameAt word).child.den (standardField word))
    {z o : Site} (hnf : Nonfree (frameAt word) z) (hG : RepStep (standardField word) z o) :
    (frameAt word).price (standardField word) o ≤ (frameAt word).price (standardField word) z ∧
      (frameAt word).roundedSlip (standardField word) 1 o ≤
        (frameAt word).roundedSlip (standardField word) 1 z := by
  have hpk := hcore.packet
  have hinv : ∀ w v, v ∈ (frameAt word).child.modifiedDeck.span →
      laplacian (standardField word) (w + v) = laplacian (standardField word) w := by
    intro w v hv
    obtain ⟨i, j, rfl⟩ := hv
    exact laplacian_add_combine hpk.periods w i j
  obtain ⟨hv, hsi⟩ := repShift_spec (frameAt word) hnf
  have hEv : EvenSite (repShift (frameAt word) z) := ProtectedWeb.span_even (frameAt word) hv
  have hv2 := hv
  obtain ⟨i0, j0, hij⟩ := hv
  have hstar := TransferW1.strictInterior_star (frameAt word) hsi
  have hzE' : z + repShift (frameAt word) z ∈ (frameAt word).closedPolygon := hstar.1
  have hpz := price_span (frameAt word) hcore.packet i0 j0 z
  have hpo := price_span (frameAt word) hcore.packet i0 j0 o
  have hrz := rs_plus_span (frameAt word) hcore.packet.periods i0 j0 z
  have hro := rs_plus_span (frameAt word) hcore.packet.periods i0 j0 o
  rw [← hij] at hpz hpo hrz hro
  rcases hG with ⟨hb, hadj⟩ | ⟨hw0, hf⟩
  · have hb' : laplacian (standardField word) (z + repShift (frameAt word) z) = -1 := by
      rw [hinv z _ hv2]
      exact hb
    have hadj' : o + repShift (frameAt word) z = incomingNeg (z + repShift (frameAt word) z) ∨
        o + repShift (frameAt word) z = incomingPos (z + repShift (frameAt word) z) := by
      rcases hadj with h1 | h1
      · left
        rw [h1, incomingNeg_add z _ hEv]
      · right
        rw [h1, incomingPos_add z _ hEv]
    have hP := price_nonincrease_black_PR h hSE hPR hpk hzE' hb' hadj'
    have hJ := jplus_nonincrease_black h hSE hpk hzE' hb' hadj'
    simp only [rs_plus_eq] at hrz hro ⊢
    constructor
    · linarith
    · linarith
  · have hLv : ∀ x, laplacian (standardField word) (x + repShift (frameAt word) z) =
        laplacian (standardField word) x := fun x => hinv x _ hv2
    have hf' := forcedEdge_add (standardField word) hEv hLv hf
    have hw' : laplacian (standardField word) (z + repShift (frameAt word) z) = 0 := by
      rw [hLv z]
      exact hw0
    have hSIz : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den
        (z + repShift (frameAt word) z) := hsi
    have hio := forced_input_of_unseeded hf
    have hoE : o + repShift (frameAt word) z ∈ (frameAt word).closedPolygon := by
      rcases hio with hio | hio
      · rw [hio, ← incomingNeg_add z _ hEv]
        exact hstar.2.1
      · rw [hio, ← incomingPos_add z _ hEv]
        exact hstar.2.2
    have hT := hT_of_W1 h hSE hPR hW hW1
    have hP := price_nonincrease_forced_of_sat_PR h hSE hPR hT hSIz hw' hzE' hf' hoE
    have hJ := jplus_nonincrease_forced_of_sat_PR h hSE hPR hT hSIz hw' hzE' hf' hoE
    simp only [rs_plus_eq] at hrz hro ⊢
    constructor
    · linarith
    · linarith


/-- **T5 (minus).** From a minimiser of `K_−` at level `cutPrice` in a fort, with the pair invariant at the start, the
passage reaches a free site of the fort with the invariant. No start in the closed polygon is needed. -/
theorem passage_rep_minus {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hcore : StrongCore word) (hseed : FLatticePaper.W1Seeds.SeedFields word)
    (hPR : FLatticePaper.PassagePR.PriceRangeOn word)
    (hW : HasSatSelection (standardField word))
    (hW1 : FLatticePaper.W1.W1Forced (frameAt word).child.num (frameAt word).child.den (standardField word))
    {S : Set Site} (hfort : FortAt (Nonfree (frameAt word)) (standardField word) S)
    (hcut : ∀ w ∈ S, (frameAt word).cutPrice ≤ kMinusW word w)
    {z0 : Site} (hz0S : z0 ∈ S) (hK0 : kMinusW word z0 = (frameAt word).cutPrice)
    (hI0 : PassageInv.InvM word z0) :
    ∃ f, f ∈ S ∧ kMinusW word f = (frameAt word).cutPrice ∧ ¬ Nonfree (frameAt word) f ∧
      PassageInv.InvM word f := by
  by_cases hnf0 : Nonfree (frameAt word) z0
  · have hWeb : ProtectedWeb.WebHyp (frameAt word) (standardField word) :=
      WordWebHyp.webHyp_word hcore hseed
    obtain ⟨R, hR⟩ := sheetMin_burning_of_strong h hSE
    have hFM := fun (z : Site) (hz : z ∈ (frameAt word).closedPolygon) =>
      standardField_eq_sheetMin_of_strong h hSE (s := z) hz
    obtain ⟨ρ, hρ⟩ := rep_rank (frameAt word) hWeb hFM hR
    have key := PassageInv.reach_nonfree_inv
      (fun z => z ∈ S ∧ kMinusW word z = (frameAt word).cutPrice)
      (fun z => Nonfree (frameAt word) z) (PassageInv.InvM word) (RepStep (standardField word))
      (fun z hv hn => by
        obtain ⟨hzS, hzK⟩ := hv
        obtain ⟨o, hG, hoS, hoK⟩ := succ_rep_minus h hSE hcore hPR hW hW1 hfort hzS hn
          (fun w hw => by
            rw [hzK]
            exact hcut w hw)
        exact ⟨o, hG, hoS, by rw [hoK, hzK]⟩)
      ⟨ρ, fun z o _ hnz hG _ hno => hρ z o hnz hno hG⟩
      (fun z o _ hnz hG _ hI => by
        have m := rep_mono_minus h hSE hcore hPR hW hW1 hnz hG
        unfold PassageInv.InvM at hI ⊢
        exact ⟨le_trans m.1 hI.1, le_trans m.2 hI.2⟩)
      z0 ⟨hz0S, hK0⟩ hnf0 hI0
    obtain ⟨f, hfv, hfn, hfI⟩ := key
    exact ⟨f, hfv.1, hfv.2, hfn, hfI⟩
  · exact ⟨z0, hz0S, hK0, hnf0, hI0⟩

/-- **T5 (plus).** The plus analogue of `passage_rep_minus`. -/
theorem passage_rep_plus {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hcore : StrongCore word) (hseed : FLatticePaper.W1Seeds.SeedFields word)
    (hPR : FLatticePaper.PassagePR.PriceRangeOn word)
    (hW : HasSatSelection (standardField word))
    (hW1 : FLatticePaper.W1.W1Forced (frameAt word).child.num (frameAt word).child.den (standardField word))
    {S : Set Site} (hfort : FortAt (Nonfree (frameAt word)) (standardField word) S)
    (hcut : ∀ w ∈ S, (frameAt word).cutPrice ≤ kPlusW word w)
    {z0 : Site} (hz0S : z0 ∈ S) (hK0 : kPlusW word z0 = (frameAt word).cutPrice)
    (hI0 : PassageInv.InvP word z0) :
    ∃ f, f ∈ S ∧ kPlusW word f = (frameAt word).cutPrice ∧ ¬ Nonfree (frameAt word) f ∧
      PassageInv.InvP word f := by
  by_cases hnf0 : Nonfree (frameAt word) z0
  · have hWeb : ProtectedWeb.WebHyp (frameAt word) (standardField word) :=
      WordWebHyp.webHyp_word hcore hseed
    obtain ⟨R, hR⟩ := sheetMin_burning_of_strong h hSE
    have hFM := fun (z : Site) (hz : z ∈ (frameAt word).closedPolygon) =>
      standardField_eq_sheetMin_of_strong h hSE (s := z) hz
    obtain ⟨ρ, hρ⟩ := rep_rank (frameAt word) hWeb hFM hR
    have key := PassageInv.reach_nonfree_inv
      (fun z => z ∈ S ∧ kPlusW word z = (frameAt word).cutPrice)
      (fun z => Nonfree (frameAt word) z) (PassageInv.InvP word) (RepStep (standardField word))
      (fun z hv hn => by
        obtain ⟨hzS, hzK⟩ := hv
        obtain ⟨o, hG, hoS, hoK⟩ := succ_rep_plus h hSE hcore hPR hW hW1 hfort hzS hn
          (fun w hw => by
            rw [hzK]
            exact hcut w hw)
        exact ⟨o, hG, hoS, by rw [hoK, hzK]⟩)
      ⟨ρ, fun z o _ hnz hG _ hno => hρ z o hnz hno hG⟩
      (fun z o _ hnz hG _ hI => by
        have m := rep_mono_plus h hSE hcore hPR hW hW1 hnz hG
        unfold PassageInv.InvP at hI ⊢
        exact ⟨le_trans m.1 hI.1, le_trans m.2 hI.2⟩)
      z0 ⟨hz0S, hK0⟩ hnf0 hI0
    obtain ⟨f, hfv, hfn, hfI⟩ := key
    exact ⟨f, hfv.1, hfv.2, hfn, hfI⟩
  · exact ⟨z0, hz0S, hK0, hnf0, hI0⟩

end FLatticePaper.PassageRep
