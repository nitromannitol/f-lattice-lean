import FLatticePaper.Plane.Induction.W4Reduction

/-! # The sign -1 adjacent chart of the forced permit, with the rounded inequality of the edge as a premise

Same proof as `W4Reduction.slip_minus_forced_adjacent_rise`, with the rounded monotonicity of the forced edge `c → i` (the `RoundedMonoForced`
inequality for that pair) given directly. Its instance at a strict-interior forced white is `RoundedLocal.rounded_forced_SI`. The rise premise
`NoRiseForced` is still an input here (its proof needs `StrongEstimates (conjWord (conjWord word))`). -/

namespace FLatticePaper.AdjacentMinus

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W4Reduction FLatticePaper.W1MSheet FLatticePaper.W1Step

theorem slip_minus_forced_adjacent_rise_at {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hW : StrongCore word) (hSE : StrongEstimates (conjWord word))
    (hpk : (frameAt word).Packet (standardField word))
    {seed : Site → Site → Prop}
    (P : FLatticePaper.W1Phase.OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hrise : NoRiseForced P.toOldPolicyWitness.toOldPolicyData) {c i : Site}
    (hr : (standardField word i - standardField word (i + -(frameAt word).shortShift) + 1) / 2 ≤
      (standardField word c - standardField word (c + -(frameAt word).shortShift) + 1) / 2)
    (hSI : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hc : c ∈ (frameAt word).closedPolygon) (hi : i ∈ (frameAt word).closedPolygon)
    (hcu : c + (frameAt word).uq ∈ (frameAt word).closedPolygon)
    (hiu : i + (frameAt word).uq ∈ (frameAt word).closedPolygon)
    (hΨc : 0 ≤ sheetPsi word c) (hΨi : 0 ≤ sheetPsi word i) (hEdge : Edge i c)
    (hfor : SquareClauses.ForcedEdge (standardField word) (fun _ _ => False) c i)
    (hlap : laplacian (standardField word) c = 0) (hnf : FLatticePaper.Induction.Nonfree (frameAt word) c)
    (hout : FLatticePaper.W1Step.sheetOut P (frameAt word).sheetShift (frameAt word).centre (sheetPsi word) c = i) :
    (frameAt word).slip (standardField word) (-1) i ≤ (frameAt word).slip (standardField word) (-1) c := by
  have hret := hret_of_sheetOut hSE P hΨc hout
  have hB := hbmono_of_raw h hSE P.toOldPolicyWitness.toOldPolicyData c i hret
  have hkey : ¬ (1 ≤ aJump word c ∧ aJump word i = 0 ∧ 1 ≤ BOffer word c) :=
    fun hh => hrise c i hSI hc hi hcu hiu hΨc hΨi hEdge hfor hlap hnf hret hh.1 hh.2.1 hh.2.2
  have hr' : ((frameAt word).slip (standardField word) (-1) i + 1) / 2 ≤
      ((frameAt word).slip (standardField word) (-1) c + 1) / 2 := by
    unfold ChildFrame.slip
    rw [neg_one_smul]
    exact hr
  have hDc := slip_minus_range h hSE hpk c hc
  have hDi := slip_minus_range h hSE hpk i hi
  have hDc' : -2 ≤ (frameAt word).slip (standardField word) (-1) c ∧
      (frameAt word).slip (standardField word) (-1) c ≤ 0 := by
    unfold ChildFrame.slip
    rw [neg_one_smul, ← sub_eq_add_neg]
    exact hDc
  have hDi' : -2 ≤ (frameAt word).slip (standardField word) (-1) i ∧
      (frameAt word).slip (standardField word) (-1) i ≤ 0 := by
    unfold ChildFrame.slip
    rw [neg_one_smul, ← sub_eq_add_neg]
    exact hDi
  rw [SignMinusAdjacent.slip_minus_adj_eq h hW hSE hi hiu hΨi] at hr' hDi' ⊢
  rw [SignMinusAdjacent.slip_minus_adj_eq h hW hSE hc hcu hΨc] at hr' hDc' ⊢
  unfold aJump BOffer at hkey
  simp only [FqW] at *
  omega

end FLatticePaper.AdjacentMinus
