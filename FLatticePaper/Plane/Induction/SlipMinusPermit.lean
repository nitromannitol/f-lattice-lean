import FLatticePaper.Plane.Induction.FreeVReflect
import FLatticePaper.Plane.Induction.SlipReflectMinus
import FLatticePaper.Plane.Induction.CanonicalPermit
import FLatticePaper.Plane.Induction.FinalRootSlip
import FLatticePaper.Plane.Induction.SheetStars
import FLatticePaper.Plane.Induction.StrongCoreDef

/-! The sign −1 V slip permit for free V whites.

For `w ≠ V_0`, the sign −1 increment at `w` along `prescribedV (−1) w` is the sign +1 increment at `R w = (1,−1) + V − w`
(`minus_increment_eq_plus`), and `R w` is a free V white different from `V_end` (`freeV_reflect_word`), so the canonical sign +1 permit
(`slip_permit_freeV_canonical`) applies. For `w = V_0` the prescribed input is `H_0 = (1,0)`, and both `V_0` and `H_0` lie in the zero
strip (`tGrade ∈ [1−d, n+2d−1]`), so both sign −1 slips vanish. -/

namespace FLatticePaper.SlipMinusPermit

open Farey FLatticePaper FLatticePaper.Induction

theorem slip_zero_V0_H0 {word : Word} (hW : StrongCore word) (z : Site)
    (hz : z = (0, 0) ∨ z = (1, 0)) :
    (frameAt word).slip (standardField word) (-1) z = 0 := by
  obtain ⟨hn0, hnd, hd2, hd3, -⟩ := (frameAt word).child_facts
  have hS := hW.packet.strips.1
  have hsh : (frameAt word).tGrade ((frameAt word).shortShift) = -2 := by
    exact (frameAt word).tGrade_shortShift
  unfold ChildFrame.slip
  have hneg : (frameAt word).tGrade (-(frameAt word).shortShift) = -(frameAt word).tGrade ((frameAt word).shortShift) := by
    unfold ChildFrame.tGrade
    simp
    ring
  have hpt : ∀ x : Site, (frameAt word).tGrade (x + (-1 : ℤ) • (frameAt word).shortShift) =
      (frameAt word).tGrade x + 2 := by
    intro x
    rw [(frameAt word).tGrade_add_pt, neg_one_smul, hneg, hsh]
    ring
  rcases hz with rfl | rfl
  · have h0 : standardField word (0, 0) = 0 := by
      apply hS
      · unfold ChildFrame.tGrade; simp; omega
      · unfold ChildFrame.tGrade; simp; omega
    have h1 : standardField word ((0, 0) + (-1 : ℤ) • (frameAt word).shortShift) = 0 := by
      apply hS
      · rw [hpt]; unfold ChildFrame.tGrade; simp; omega
      · rw [hpt]; unfold ChildFrame.tGrade; simp; omega
    rw [h0, h1]; ring
  · have h0 : standardField word (1, 0) = 0 := by
      apply hS
      · unfold ChildFrame.tGrade; simp; omega
      · unfold ChildFrame.tGrade; simp; omega
    have h1 : standardField word ((1, 0) + (-1 : ℤ) • (frameAt word).shortShift) = 0 := by
      apply hS
      · rw [hpt]; unfold ChildFrame.tGrade; simp; omega
      · rw [hpt]; unfold ChildFrame.tGrade; simp; omega
    rw [h0, h1]; ring

/-- **The sign −1 V permit.** For a free V white `w`, `D₋(w + prescribedV (−1) w) ≤ D₋(w)`. -/
theorem slip_permit_freeV_minus {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hW : StrongCore word)
    (hSE : StrongEstimates (conjWord word))
    (G : CanonicalSignedGames (frameAt (conjWord word)) (standardField (conjWord word)))
    {w : Site} (hw : w ∈ (frameAt word).freeV) :
    (frameAt word).slip (standardField word) (-1) (w + (frameAt word).prescribedV (-1) w) ≤
      (frameAt word).slip (standardField word) (-1) w := by
  by_cases hv : w = FLatticePaper.Induction.vFirst
  · subst hv
    rw [ChildFrame.prescribedV_vFirst]
    have h1 := slip_zero_V0_H0 hW (FLatticePaper.Induction.vFirst + (1, 0)) (Or.inr (by simp [FLatticePaper.Induction.vFirst]))
    have h2 := slip_zero_V0_H0 hW FLatticePaper.Induction.vFirst (Or.inl (by simp [FLatticePaper.Induction.vFirst]))
    linarith
  · have hRw := FreeVReflect.freeV_reflect_word h hw
    have hne : (1, -1) + (frameAt word).child.modifiedDeck.transverse - w ≠ (frameAt word).vLast := by
      intro e
      rw [FinalRootSlip.vLast_eq_I_add_transverse] at e
      have e1 := congrArg Prod.fst e
      have e2 := congrArg Prod.snd e
      simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] at e1 e2
      apply hv
      unfold FLatticePaper.Induction.vFirst
      ext
      · simp only; linarith
      · simp only; linarith
    have hinc := SlipReflectMinus.minus_increment_eq_plus (frameAt word) hW.packet hv
    have hperm := CanonicalPermit.slip_permit_freeV_canonical h hW hSE G hRw hne
    linarith [hinc, hperm]

end FLatticePaper.SlipMinusPermit
