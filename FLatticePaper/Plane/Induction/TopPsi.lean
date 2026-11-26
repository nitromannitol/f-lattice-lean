import FLatticePaper.Plane.Induction.StripsM
import FLatticePaper.Plane.Induction.HtopCross
import FLatticePaper.Plane.Induction.TopBounds
import FLatticePaper.Plane.Induction.TopParentZero
import FLatticePaper.Plane.Induction.TopParentArith
import FLatticePaper.Plane.Induction.FaceWitness
import FLatticePaper.Plane.Induction.W1Step
import FLatticePaper.Plane.Induction.W1Strips
import FLatticePaper.Plane.Induction.W1ArcBottom
import FLatticePaper.Plane.Induction.Q3VStar

/-! # The top sign: `sheetPsi word c ≤ 0` on a strict top witness (step 2 of PsiFaceSign)

For a strict centre `c` with a top witness and `y = c − V`:
* `F(y) = 0` (the word's zero intervals on the top collar, `W1Strips.top_collar_zero_full`, with the even seed of the conjugate);
* the cross identity (`HtopCross`): `C(c) = Fq(w) + (n y₁ − d y₂) + c_V` with the parent query `w = y − ε K − (1 − W)(d_q, n_q)`;
* `Fq(w) = 0`: `TopParentZero.parent_even_zero` on even `w`, the conjugate's zero strip on odd `w`, the window from `TopParentArith`;
* hence `C(c) = F(c) = min(A(c), C(c)) ≤ A(c)`, i.e. `Ψ(c) ≤ 0`. -/

namespace FLatticePaper.TopPsi

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1 FLatticePaper.W1Step FLatticePaper.FaceWitness FLatticePaper.W1Seeds

theorem eps_cases (frame : ChildFrame) : frame.eps = 1 ∨ frame.eps = -1 := by
  have h := FLatticePaper.W1Strips.shortShift_eps_sq frame
  have h2 : (frame.eps - 1) * (frame.eps + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h2 with h1 | h1
  · left
    linarith
  · right
    linarith

/-- **`Ψ ≤ 0` at a strict top witness.** -/
theorem top_sheetPsi_le {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpar : SeedFields (conjWord word))
    (hn3 : 3 ≤ (frameAt word).child.num) {c : Site}
    (hc : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hTop : TopWit (frameAt word) c) :
    sheetPsi word c ≤ 0 := by
  obtain ⟨v, hv1, hv2, hu⟩ := hTop
  have hyb := FLatticePaper.TopBounds.top_bounds (frameAt word) hn3 hc hv1 hv2 hu
  obtain ⟨h0, hnd, hd2, hd3, -⟩ := (frameAt word).child_facts
  obtain ⟨hnO, hdO⟩ := (frameAt word).child_odd
  have hD2 := FLatticePaper.W1ArcBottom.odd_den_ge_two (frameAt word) hn3
  obtain ⟨hDo, hN0, -⟩ := (frameAt word).valid.odd_bounds
  obtain ⟨hEDp, hENn, -⟩ := (frameAt word).valid.even_bounds
  have hden := FLatticePaper.Induction.ZoneI1.child_den_eq (frameAt word)
  have hnum := FLatticePaper.Induction.ZoneI1.child_num_eq (frameAt word)
  have hdq0 : 2 * (frameAt word).parents.odd.den ≤ (frameAt word).child.den := by omega
  have hnq0 : 2 * (frameAt word).parents.odd.num ≤ (frameAt word).child.num := by omega
  have hnd' : (frameAt word).child.num + 2 ≤ (frameAt word).child.den := by omega
  -- the conjugate's parent parameters
  obtain ⟨hcn, hcd⟩ := FLatticePaper.Induction.frameAt_conj_num_den hw
  have hpN : parentN (conjWord word) = (frameAt word).parents.odd.num := by
    unfold parentN
    rw [hcn, hcd]
    omega
  have hpD : parentD (conjWord word) = (frameAt word).parents.odd.den := by
    unfold parentD
    rw [hcn, hcd]
    omega
  -- the zero of the word's field on `y = c − V`
  have hFy : standardField word (c - (frameAt word).child.modifiedDeck.transverse) = 0 := by
    by_cases he : EvenSite (c - (frameAt word).child.modifiedDeck.transverse)
    · exact FLatticePaper.W1Strips.top_collar_zero_full (frameAt word) (FLatticePaper.StripsM.hper_word hw hSE)
        (packet_of_strong hw hSE).strips (FLatticePaper.StripsM.hslip_word hw hSE)
        (FLatticePaper.StripsM.hseed_word hw hSE hpar) (fun z => FLatticePaper.StripsM.hIsym_word hw hSE z) _
        (Or.inl ⟨he, (hyb.1 he).1.1, (hyb.1 he).1.2⟩)
    · exact FLatticePaper.W1Strips.top_collar_zero_full (frameAt word) (FLatticePaper.StripsM.hper_word hw hSE)
        (packet_of_strong hw hSE).strips (FLatticePaper.StripsM.hslip_word hw hSE)
        (FLatticePaper.StripsM.hseed_word hw hSE hpar) (fun z => FLatticePaper.StripsM.hIsym_word hw hSE z) _
        (Or.inr ⟨he, (hyb.2 he).1.1, (hyb.2 he).1.2⟩)
  -- the period of the word's field along the transverse vector
  have hper := (FLatticePaper.StripsM.hper_word hw hSE).2 (c - (frameAt word).child.modifiedDeck.transverse)
  rw [sub_add_cancel, hFy] at hper
  unfold Fraction.transverseGrade at hper
  -- `c` lies in the closed polygon, and the sheet minimum identity
  have hcl : c ∈ (frameAt word).closedPolygon := by
    rw [FLatticePaper.W1.closedPolygon_eq_closedRect (frameAt word)]
    exact FLatticePaper.W1.strictInterior_closedRect (by omega) (by omega) c hc
  have hmin := standardField_eq_sheetMin_of_strong hw hSE hcl
  unfold ChildFrame.sheetMin at hmin
  -- `C(c) = F(c)`
  have hCc : (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) c =
      standardField word c := by
    rcases eps_cases (frameAt word) with hε | hε
    · -- `ε = 1`: the parent query is `w = y − K`
      have hC := HtopCross.sheetC_cross_plus hw hSE hε (c - (frameAt word).child.modifiedDeck.transverse)
      rw [sub_add_cancel] at hC
      have hWz := (frameAt word).eps_eq
      rw [hε] at hWz
      have hP := (frameAt word).periodDenominator_parentTGrade (c - (frameAt word).child.modifiedDeck.transverse)
      rw [hε] at hP
      unfold Fraction.periodDenominator ChildFrame.parentC at hP
      have hWz1 : (frameAt word).parents.odd.num * (frameAt word).child.den -
          (frameAt word).parents.odd.den * (frameAt word).child.num = 1 := by
        rw [← hWz]
      have hPw : (frameAt word).parentTGrade ((c - (frameAt word).child.modifiedDeck.transverse) -
          (frameAt word).child.modifiedDeck.kernel) =
          (frameAt word).parentTGrade (c - (frameAt word).child.modifiedDeck.transverse) - 1 := by
        unfold ChildFrame.parentTGrade
        rw [ChildFrame.child_modifiedDeck_kernel]
        simp only [Prod.fst_sub, Prod.snd_sub]
        linear_combination (-1 : ℤ) * hWz1
      have hwe : EvenSite ((c - (frameAt word).child.modifiedDeck.transverse) -
          (frameAt word).child.modifiedDeck.kernel) ↔
          EvenSite (c - (frameAt word).child.modifiedDeck.transverse) := by
        unfold EvenSite
        rw [ChildFrame.child_modifiedDeck_kernel]
        simp only [Prod.fst_sub, Prod.snd_sub]
        omega
      have hzero : quarterTurnField (standardField (conjWord word))
          ((c - (frameAt word).child.modifiedDeck.transverse) -
            (frameAt word).child.modifiedDeck.kernel) = 0 := by
        by_cases he : EvenSite (c - (frameAt word).child.modifiedDeck.transverse)
        · obtain ⟨hA1, hA2⟩ := hyb.1 he
          have hbd := FLatticePaper.TopParentArith.even_plus (frameAt word).parents.odd.num
            (frameAt word).parents.odd.den (frameAt word).child.num (frameAt word).child.den
            ((frameAt word).parentTGrade (c - (frameAt word).child.modifiedDeck.transverse))
            ((frameAt word).tGrade (c - (frameAt word).child.modifiedDeck.transverse))
            ((frameAt word).sGrade (c - (frameAt word).child.modifiedDeck.transverse))
            hn3 hnd' hD2 hN0 hdq0 hnq0 hWz1.symm hP hA1.1 hA1.2 hA2.1 hA2.2
          have hlo' : 1 - ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den) ≤
              (frameAt word).parentTGrade ((c - (frameAt word).child.modifiedDeck.transverse) -
                (frameAt word).child.modifiedDeck.kernel) := by
            rw [hPw]
            linarith [hbd.1]
          have hhi' : (frameAt word).parentTGrade ((c - (frameAt word).child.modifiedDeck.transverse) -
                (frameAt word).child.modifiedDeck.kernel) ≤
              2 * ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den) - 1 := by
            rw [hPw]
            linarith [hbd.2]
          exact FLatticePaper.TopParentZero.parent_even_zero hw hSE hpar hn3 _ (hwe.2 he) hlo' hhi'
        · obtain ⟨hA1, hA2⟩ := hyb.2 he
          have hbd := FLatticePaper.TopParentArith.odd_plus (frameAt word).parents.odd.num
            (frameAt word).parents.odd.den (frameAt word).child.num (frameAt word).child.den
            ((frameAt word).parentTGrade (c - (frameAt word).child.modifiedDeck.transverse))
            ((frameAt word).tGrade (c - (frameAt word).child.modifiedDeck.transverse))
            ((frameAt word).sGrade (c - (frameAt word).child.modifiedDeck.transverse))
            hn3 hnd' hD2 hN0 hdq0 hnq0 hWz1.symm hP hA1.1 hA1.2 hA2.1
            (by unfold w1T at hA2; linarith [hA2.2])
          have hs := hSE.zeroStripInterval ((c - (frameAt word).child.modifiedDeck.transverse) -
              (frameAt word).child.modifiedDeck.kernel)
          rw [hpN, hpD] at hs
          have hlo' : 1 - (frameAt word).parents.odd.den ≤
              (frameAt word).parentTGrade ((c - (frameAt word).child.modifiedDeck.transverse) -
                (frameAt word).child.modifiedDeck.kernel) := by
            rw [hPw]
            linarith [hbd.1]
          have hhi' : (frameAt word).parentTGrade ((c - (frameAt word).child.modifiedDeck.transverse) -
                (frameAt word).child.modifiedDeck.kernel) ≤
              (frameAt word).parents.odd.num + 2 * (frameAt word).parents.odd.den - 1 := by
            rw [hPw]
            linarith [hbd.2]
          exact hs hlo' hhi'
      rw [hC, hzero, zero_add, hper]
      ring
    · -- `ε = −1`: the parent query is `w = y + K − (d_q, n_q)`
      have hC := HtopCross.sheetC_cross_minus hw hSE hε (c - (frameAt word).child.modifiedDeck.transverse)
      rw [sub_add_cancel] at hC
      have hWz := (frameAt word).eps_eq
      rw [hε] at hWz
      have hP := (frameAt word).periodDenominator_parentTGrade (c - (frameAt word).child.modifiedDeck.transverse)
      rw [hε] at hP
      unfold Fraction.periodDenominator ChildFrame.parentC at hP
      have hWzm : (frameAt word).parents.odd.num * (frameAt word).child.den -
          (frameAt word).parents.odd.den * (frameAt word).child.num = -1 := by
        rw [← hWz]
      have hPw : (frameAt word).parentTGrade ((c - (frameAt word).child.modifiedDeck.transverse) +
          (frameAt word).child.modifiedDeck.kernel -
            ((frameAt word).parents.even.den, (frameAt word).parents.even.num)) =
          (frameAt word).parentTGrade (c - (frameAt word).child.modifiedDeck.transverse) := by
        unfold ChildFrame.parentTGrade
        rw [ChildFrame.child_modifiedDeck_kernel]
        simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
        linear_combination (frameAt word).parents.odd.num * hden - (frameAt word).parents.odd.den * hnum
      have hwe : EvenSite ((c - (frameAt word).child.modifiedDeck.transverse) +
          (frameAt word).child.modifiedDeck.kernel -
            ((frameAt word).parents.even.den, (frameAt word).parents.even.num)) ↔
          EvenSite (c - (frameAt word).child.modifiedDeck.transverse) := by
        unfold EvenSite
        rw [ChildFrame.child_modifiedDeck_kernel]
        simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
        omega
      have hzero : quarterTurnField (standardField (conjWord word))
          ((c - (frameAt word).child.modifiedDeck.transverse) +
            (frameAt word).child.modifiedDeck.kernel -
              ((frameAt word).parents.even.den, (frameAt word).parents.even.num)) = 0 := by
        by_cases he : EvenSite (c - (frameAt word).child.modifiedDeck.transverse)
        · obtain ⟨hA1, hA2⟩ := hyb.1 he
          have hbd := FLatticePaper.TopParentArith.even_minus (frameAt word).parents.odd.num
            (frameAt word).parents.odd.den (frameAt word).child.num (frameAt word).child.den
            ((frameAt word).parentTGrade (c - (frameAt word).child.modifiedDeck.transverse))
            ((frameAt word).tGrade (c - (frameAt word).child.modifiedDeck.transverse))
            ((frameAt word).sGrade (c - (frameAt word).child.modifiedDeck.transverse))
            hn3 hnd' hD2 hN0 hdq0 hnq0 hWzm.symm hP hA1.1 hA1.2 hA2.1 hA2.2
          have hlo' : 1 - ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den) ≤
              (frameAt word).parentTGrade ((c - (frameAt word).child.modifiedDeck.transverse) +
                (frameAt word).child.modifiedDeck.kernel -
                  ((frameAt word).parents.even.den, (frameAt word).parents.even.num)) := by
            rw [hPw]
            linarith [hbd.1]
          have hhi' : (frameAt word).parentTGrade ((c - (frameAt word).child.modifiedDeck.transverse) +
                (frameAt word).child.modifiedDeck.kernel -
                  ((frameAt word).parents.even.den, (frameAt word).parents.even.num)) ≤
              2 * ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den) - 1 := by
            rw [hPw]
            linarith [hbd.2]
          exact FLatticePaper.TopParentZero.parent_even_zero hw hSE hpar hn3 _ (hwe.2 he) hlo' hhi'
        · obtain ⟨hA1, hA2⟩ := hyb.2 he
          have hbd := FLatticePaper.TopParentArith.odd_minus (frameAt word).parents.odd.num
            (frameAt word).parents.odd.den (frameAt word).child.num (frameAt word).child.den
            ((frameAt word).parentTGrade (c - (frameAt word).child.modifiedDeck.transverse))
            ((frameAt word).tGrade (c - (frameAt word).child.modifiedDeck.transverse))
            ((frameAt word).sGrade (c - (frameAt word).child.modifiedDeck.transverse))
            hn3 hnd' hD2 hN0 hdq0 hnq0 hWzm.symm hP hA1.1 hA1.2 hA2.1
            (by unfold w1T at hA2; linarith [hA2.2])
          have hs := hSE.zeroStripInterval ((c - (frameAt word).child.modifiedDeck.transverse) +
              (frameAt word).child.modifiedDeck.kernel -
                ((frameAt word).parents.even.den, (frameAt word).parents.even.num))
          rw [hpN, hpD] at hs
          have hlo' : 1 - (frameAt word).parents.odd.den ≤
              (frameAt word).parentTGrade ((c - (frameAt word).child.modifiedDeck.transverse) +
                (frameAt word).child.modifiedDeck.kernel -
                  ((frameAt word).parents.even.den, (frameAt word).parents.even.num)) := by
            rw [hPw]
            linarith [hbd.1]
          have hhi' : (frameAt word).parentTGrade ((c - (frameAt word).child.modifiedDeck.transverse) +
                (frameAt word).child.modifiedDeck.kernel -
                  ((frameAt word).parents.even.den, (frameAt word).parents.even.num)) ≤
              (frameAt word).parents.odd.num + 2 * (frameAt word).parents.odd.den - 1 := by
            rw [hPw]
            linarith [hbd.2]
          exact hs hlo' hhi'
      rw [hC, hzero, zero_add, hper]
      ring
  have hle : (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) c ≤
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) c := by
    rw [hCc, hmin]
    exact min_le_left _ _
  unfold FLatticePaper.W1Step.sheetPsi
  linarith

end FLatticePaper.TopPsi
