import FLatticePaper.Plane.Induction.NegTieNonfree
import FLatticePaper.Plane.Induction.ConjFreeRoot

/-! Task 72 (hNegTie, case (a'): the free root of the V cut is impossible; the H cut is excluded by the web).

`negTie_jumps`: the negative tied-target configuration gives the jumps `a(c − l_v) = 1` and `a(i − l_v) = 0` (the first half of
`negTie_drop_of_nonfree`, which does not use the nonfree hypothesis).

`jumpA_ne_one_of_freeV`: at a free conjugate V root `zTurn x` the jump is not `1`. The web `HRootWeb (t_p x)` is `conj_freeV_hweb` at
translate `0` (the H-web of the conjugate V cut), and `H_drop_excluded` gives the contradiction.

`negTie_drop_of_freeV`: the free root of the V cut at `zTurn (c − l_v)` is impossible. The remaining free-root cases of hNegTie are the
free H cut (the V-block step Q21) and the free deck translates of the root (not yet reduced). -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- **The negative tied-target jumps.** The first half of `negTie_drop_of_nonfree`: `a(c − l_v) = 1` and `a(i − l_v) = 0`. -/
theorem negTie_jumps {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpk : (frameAt word).Packet (standardField word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hslip : ∀ z ∈ (frameAt word).closedPolygon,
      0 ≤ standardField word z - standardField word (z + (frameAt word).shortShift) ∧
        standardField word z - standardField word (z + (frameAt word).shortShift) ≤ 2)
    {c i j : Site} (hr : RisingBlackPair (standardField word) (-(frameAt word).shortShift) c i)
    (hcE : c ∈ (frameAt word).closedPolygon) (hiE : i ∈ (frameAt word).closedPolygon)
    (hcu : c + (frameAt word).uq ∈ (frameAt word).closedPolygon)
    (hiu : i + (frameAt word).uq ∈ (frameAt word).closedPolygon)
    (hΨc : sheetDiffW word c = 0) (hj : FLatticePaper.Edge j c) (hjΨ : sheetDiffW word j ≤ -1)
    (hΨi : 1 ≤ sheetDiffW word i) :
    jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) (c - (frameAt word).sheetShift) = 1 ∧
      jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) (i - (frameAt word).sheetShift) = 0 := by
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
  have hΨi' : 1 ≤ (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) i -
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
  exact ⟨j1, j0⟩

/-- **A jump `1` is not at a free V root.** At a free conjugate V site `zTurn x`, the web `HRootWeb (t_p x)` holds
(`conj_freeV_hweb` at translate `0`), so `a(x) = 0` by `H_drop_excluded`. -/
theorem jumpA_ne_one_of_freeV {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) {x : Site}
    (hf : zTurn x ∈ (frameAt (conjWord word)).freeV)
    (h1 : jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x = 1) : False := by
  have hf' : zTurn x + (frameAt (conjWord word)).child.modifiedDeck.combine 0 0 ∈
      (frameAt (conjWord word)).freeV := by
    rw [ChildFrame.combine_zero_zero (frameAt (conjWord word))]
    simpa using hf
  have hw := conj_freeV_hweb h hf'
  simp only [zero_mul, add_zero] at hw
  exact H_drop_excluded h hSE x hw h1

/-- **The free V root of the negative tied target is impossible.** If the root `zTurn (c − l_v)` is a free V site of the conjugate
frame, the jump `a(c − l_v) = 1` contradicts the web. -/
theorem negTie_drop_of_freeV {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpk : (frameAt word).Packet (standardField word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hslip : ∀ z ∈ (frameAt word).closedPolygon,
      0 ≤ standardField word z - standardField word (z + (frameAt word).shortShift) ∧
        standardField word z - standardField word (z + (frameAt word).shortShift) ≤ 2)
    {c i j : Site} (hr : RisingBlackPair (standardField word) (-(frameAt word).shortShift) c i)
    (hcE : c ∈ (frameAt word).closedPolygon) (hiE : i ∈ (frameAt word).closedPolygon)
    (hcu : c + (frameAt word).uq ∈ (frameAt word).closedPolygon)
    (hiu : i + (frameAt word).uq ∈ (frameAt word).closedPolygon)
    (hΨc : sheetDiffW word c = 0) (hj : FLatticePaper.Edge j c) (hjΨ : sheetDiffW word j ≤ -1)
    (hΨi : 1 ≤ sheetDiffW word i)
    (hfV : zTurn (c - (frameAt word).sheetShift) ∈ (frameAt (conjWord word)).freeV) : False :=
  jumpA_ne_one_of_freeV h hSE hfV
    (negTie_jumps h hSE hpk P hslip hr hcE hiE hcu hiu hΨc hj hjΨ hΨi).1

end FLatticePaper.Induction
