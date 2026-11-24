import FLatticePaper.Plane.Induction.HResP

/-! Task 72 (hNegTie, case (a): the nonfree old root).

The negative tied-target configuration: a rising `−σ` pair `(c, i)`, the centre tied (`Ψ c = 0`), the target strict
(`Ψ i ≥ 1`), an input `j` of `c` with `Ψ j ≤ −1`, and both endpoints shifted by `+uq` in `E`.

With the A-policy retaining `c → i` (`sheetPolicyA_of_tie`), the negative-chart arithmetic of `neg_adjacent_excluded` gives the
jumps `a(c − l_v) = 1` and `a(i − l_v) = 0`. If the old root `zTurn (c − l_v)` is nonfree in the conjugate frame, then
`nonfree_root_forced_nonfree` gives black or the forced retained edge, which is the `hroot` of `nonfree_drop_excluded`. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- **Case (a) of the negative tied target: a nonfree old root.** -/
theorem negTie_drop_of_nonfree {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpk : (frameAt word).Packet (standardField word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num
      (frameAt (conjWord word)).child.den (standardField (conjWord word)))
    (hslip : ∀ z ∈ (frameAt word).closedPolygon,
      0 ≤ standardField word z - standardField word (z + (frameAt word).shortShift) ∧
        standardField word z - standardField word (z + (frameAt word).shortShift) ≤ 2)
    {c i j : Site} (hr : RisingBlackPair (standardField word) (-(frameAt word).shortShift) c i)
    (hcE : c ∈ (frameAt word).closedPolygon) (hiE : i ∈ (frameAt word).closedPolygon)
    (hcu : c + (frameAt word).uq ∈ (frameAt word).closedPolygon)
    (hiu : i + (frameAt word).uq ∈ (frameAt word).closedPolygon)
    (hΨc : sheetDiffW word c = 0) (hj : FLatticePaper.Edge j c) (hjΨ : sheetDiffW word j ≤ -1)
    (hΨi : 0 ≤ sheetDiffW word i)
    (hnf : Nonfree (frameAt (conjWord word)) (zTurn (c - (frameAt word).sheetShift))) : False := by
  have hij : i ≠ j := by
    intro e
    subst e
    omega
  have hret : sheetPolicyA P (frameAt word).sheetShift c i :=
    sheetPolicyA_of_tie h hSE hpk P hcE hr.1 hj hij hr.2.1 hΨc hjΨ
  -- the sheet minimum on `E`
  have hG : ∀ z ∈ (frameAt word).closedPolygon,
      standardField word z = min ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) z)
        ((frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) z) := fun z hz =>
    standardField_eq_sheetMin_of_strong h hSE hz
  have hΨc' : (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) c -
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) c = 0 := hΨc
  have hΨi' : 0 ≤ (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) i -
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) i := hΨi
  have hFc : standardField word c =
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) c := by
    rw [hG c hcE]
    exact min_eq_left (by omega)
  have hFi : standardField word i =
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) i := by
    rw [hG i hiE]
    exact min_eq_left (by omega)
  -- the rise `D_−(i) − D_−(c) = 1` with `D_−(z) = F z − F (z − σ)`
  have e1 : c + -(frameAt word).shortShift = c - (frameAt word).shortShift :=
    (sub_eq_add_neg c _).symm
  have e2 : i + -(frameAt word).shortShift = i - (frameAt word).shortShift :=
    (sub_eq_add_neg i _).symm
  have hrise := hr.2.2.2.2
  unfold slipIncrement at hrise
  dsimp only at hrise
  rw [e1, e2] at hrise
  have hpar := hr.2.2.1
  rw [e1] at hpar
  -- the reflected slip range: `D_−(c) = D_+(R c) − 2 ∈ [−2, 0]`
  have hR := (frameAt word).slip_reflect_gen hpk (frameAt word).shortShift ((frameAt word).centre - c)
  rw [sub_sub_cancel, e1, (frameAt word).tGrade_shortShift] at hR
  obtain ⟨hr0, hr2⟩ := hslip _ ((frameAt word).reflect_mem_closedPolygon hcE)
  -- odd parity and the range give `D_−(c) = −1`; the rise then gives `D_−(i) = 0`
  have hDc : standardField word c - standardField word (c - (frameAt word).shortShift) = -1 := by
    omega
  have hDi : standardField word i - standardField word (i - (frameAt word).shortShift) = 0 := by
    omega
  have hqc : standardField word (c - (frameAt word).shortShift) =
      standardField word (c + (frameAt word).uq) := (frameAt word).F_sub_shortShift hpk c
  have hqi : standardField word (i - (frameAt word).shortShift) =
      standardField word (i + (frameAt word).uq) := (frameAt word).F_sub_shortShift hpk i
  have hp : min ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) (c + (frameAt word).uq))
      ((frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) (c + (frameAt word).uq)) -
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) c = 1 := by
    have := hG _ hcu
    omega
  have hq : min ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) (i + (frameAt word).uq))
      ((frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) (i + (frameAt word).uq)) -
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) i = 0 := by
    have := hG _ hiu
    omega
  -- the unit increment, the monotonicity of `B` along the retained edge, and the arithmetic
  have hb := hbmono_of_raw h hSE P c i hret
  have hunit := (a_unit_bound h hSE hr.1).1
  obtain ⟨h1, h0⟩ := neg_chart_arith
    ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) c)
    ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) i)
    ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) (c + (frameAt word).uq))
    ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) (i + (frameAt word).uq))
    ((frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) (c + (frameAt word).uq))
    ((frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) (i + (frameAt word).uq))
    (min ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) (c + (frameAt word).uq))
      ((frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) (c + (frameAt word).uq)))
    (min ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) (i + (frameAt word).uq))
      ((frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) (i + (frameAt word).uq)))
    (min_le_left _ _) (min_le_right _ _) (min_choice _ _)
    (by linarith [hunit]) hb hp hq
  have j1 : jumpA (frameAt word) (quarterTurnField (standardField (conjWord word)))
      (c - (frameAt word).sheetShift) = 1 := by
    rw [← sheetA_uq_eq_jumpA c]
    exact h1
  have j0 : jumpA (frameAt word) (quarterTurnField (standardField (conjWord word)))
      (i - (frameAt word).sheetShift) = 0 := by
    rw [← sheetA_uq_eq_jumpA i]
    exact h0
  have hroot := nonfree_root_forced_nonfree P hSE.packet hW1 hnf hret
  exact nonfree_drop_excluded (x := c - (frameAt word).sheetShift) (x' := i - (frameAt word).sheetShift)
    h hSE P hret j1 j0 hroot

end FLatticePaper.Induction
