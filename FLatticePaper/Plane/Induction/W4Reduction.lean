import FLatticePaper.Plane.Induction.SignMinusAdjacent
import FLatticePaper.Plane.Induction.RawB
import FLatticePaper.Plane.Induction.NonfreeBridge
import FLatticePaper.Plane.Induction.W1Step
import FLatticePaper.Plane.Induction.W1HagreeNonfree

/-! # W4 (Q34): the sign `−1` permit at a forced nonfree white, adjacent chart, from one named input

With `uq = ε U_q`, the sheet quantities of the negative chart are

* `aJump z = A(z + uq) − A z` (the jump `a`, unit increments along edges: `a_unit_bound`),
* `BOffer z = C(z + uq) − A z` (the offer `B`, monotone along the retained `A`-edges: `hbmono_of_raw`).

At an `A`-root `c` with `c + uq` in the polygon, `D₋(c) = −min(a c, B c)` (`SignMinusAdjacent.slip_minus_adj_eq`). The permit
`D₋(i) ≤ D₋(c)` at an input `i` of `c` is `min(a i, B i) ≥ min(a c, B c)`. Given `B c ≤ B i`, the unit bound `|a c − a i| ≤ 1`
and the a-fall exclusion `NoAFallForced` (the named input, the statement `hnofall_forced`) this holds.

`NoAFallForced` is the only input that is not a theorem here; the retained-edge hypothesis `hret` is the `A`-edge of the W4
statement (monotonicity of `B` along it, `hbmono_of_raw`). -/

namespace FLatticePaper.W4Reduction

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1MSheet FLatticePaper.W1Step

/-- The negative-chart jump `a z = A(z + uq) − A z`. -/
noncomputable def aJump (word : Word) (z : Site) : ℤ :=
  (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) (z + (frameAt word).uq) -
    (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) z

/-- The negative-chart offer `B z = C(z + uq) − A z`. -/
noncomputable def BOffer (word : Word) (z : Site) : ℤ :=
  (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) (z + (frameAt word).uq) -
    (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) z

/-- **The named input `hnofall_forced`: the a-fall exclusion on a forced edge at a nonfree white.** For `A`-roots `c` and `i`
(with `i` an input of `c`, both adjacent points in the polygon), `ForcedEdge (standardField word) ∅ c i`, `laplacian c = 0` and
`Nonfree (frameAt word) c`, the a-fall `a i < a c` with `a c ≤ B c` does not occur. Numerically: no counterexample among 1378
forced nonfree-white pairs (window 48, converged). -/
noncomputable def NoAFallForced (word : Word) : Prop :=
  ∀ c i : Site,
    c ∈ (frameAt word).closedPolygon → i ∈ (frameAt word).closedPolygon →
    c + (frameAt word).uq ∈ (frameAt word).closedPolygon → i + (frameAt word).uq ∈ (frameAt word).closedPolygon →
    0 ≤ sheetPsi word c → 0 ≤ sheetPsi word i → Edge i c →
    SquareClauses.ForcedEdge (standardField word) (fun _ _ => False) c i →
    laplacian (standardField word) c = 0 → FLatticePaper.Induction.Nonfree (frameAt word) c →
    ¬ (aJump word i < aJump word c ∧ aJump word c ≤ BOffer word c)

/-- **The sign `−1` permit at a forced nonfree white, adjacent chart.** The slip is `D₋`; the conclusion is the permit
`D₋(i) ≤ D₋(c)` for the input `i` of `c`, from the named input `hnofall`, the monotonicity of `B` along the retained edge `hret`,
and the unit bound on `a`. -/
theorem slip_minus_forced_adjacent {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hW : StrongEstimates word) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop}
    (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hnofall : NoAFallForced word) {c i : Site}
    (hc : c ∈ (frameAt word).closedPolygon) (hi : i ∈ (frameAt word).closedPolygon)
    (hcu : c + (frameAt word).uq ∈ (frameAt word).closedPolygon)
    (hiu : i + (frameAt word).uq ∈ (frameAt word).closedPolygon)
    (hΨc : 0 ≤ sheetPsi word c) (hΨi : 0 ≤ sheetPsi word i) (hEdge : Edge i c)
    (hfor : SquareClauses.ForcedEdge (standardField word) (fun _ _ => False) c i)
    (hlap : laplacian (standardField word) c = 0) (hnf : FLatticePaper.Induction.Nonfree (frameAt word) c)
    (hret : sheetPolicyA P (frameAt word).sheetShift c i) :
    (frameAt word).slip (standardField word) (-1) i ≤ (frameAt word).slip (standardField word) (-1) c := by
  rw [SignMinusAdjacent.slip_minus_adj_eq h hW hSE hc hcu hΨc,
    SignMinusAdjacent.slip_minus_adj_eq h hW hSE hi hiu hΨi]
  have hB := hbmono_of_raw h hSE P c i hret
  obtain ⟨hu1, hu2⟩ := a_unit_bound h hSE hEdge
  have hn := hnofall c i hc hi hcu hiu hΨc hΨi hEdge hfor hlap hnf
  unfold aJump BOffer at hn
  simp only [FqW] at *
  omega

/-- **The retention from the W1 identification.** At an `A`-root `c` (`Ψ c ≥ 0`) the W1 pointer `sheetOut c` is the `A`-pointer, which
is a retained `sheetPolicyA` edge (`sheetPolicyA_pointer_retained`). So the forced input `i = sheetOut c` gives `hret`. -/
theorem hret_of_sheetOut {word : Word} (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop}
    (P : FLatticePaper.W1Phase.OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    {c i : Site} (hΨ : 0 ≤ sheetPsi word c)
    (hout : FLatticePaper.W1Step.sheetOut P (frameAt word).sheetShift (frameAt word).centre (sheetPsi word) c = i) :
    sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift c i := by
  subst hout
  unfold FLatticePaper.W1Step.sheetOut
  rw [if_pos hΨ]
  exact FLatticePaper.W1HagreeNonfree.sheetPolicyA_pointer_retained P.toOldPolicyWitness.toOldPolicyData
    hSE.packet.binary (frameAt word).sheetShift (frameAt word).evenSite_sheetShift c

/-- **The sign `−1` permit at a forced nonfree white, through the W1 identification.** The forced input is `sheetOut c`
(`hout`, the W1 identification from the square data of `sheetOut_forcedIn`); the retention `hret` is then derived by
`hret_of_sheetOut`. The named input is still `NoAFallForced`. -/
theorem slip_minus_forced_adjacent_sheetOut {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hW : StrongEstimates word) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop}
    (P : FLatticePaper.W1Phase.OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hnofall : NoAFallForced word) {c i : Site}
    (hc : c ∈ (frameAt word).closedPolygon) (hi : i ∈ (frameAt word).closedPolygon)
    (hcu : c + (frameAt word).uq ∈ (frameAt word).closedPolygon)
    (hiu : i + (frameAt word).uq ∈ (frameAt word).closedPolygon)
    (hΨc : 0 ≤ sheetPsi word c) (hΨi : 0 ≤ sheetPsi word i) (hEdge : Edge i c)
    (hfor : SquareClauses.ForcedEdge (standardField word) (fun _ _ => False) c i)
    (hlap : laplacian (standardField word) c = 0) (hnf : FLatticePaper.Induction.Nonfree (frameAt word) c)
    (hout : FLatticePaper.W1Step.sheetOut P (frameAt word).sheetShift (frameAt word).centre (sheetPsi word) c = i) :
    (frameAt word).slip (standardField word) (-1) i ≤ (frameAt word).slip (standardField word) (-1) c :=
  slip_minus_forced_adjacent h hW hSE P.toOldPolicyWitness.toOldPolicyData hnofall hc hi hcu hiu hΨc hΨi hEdge hfor hlap hnf
    (hret_of_sheetOut hSE P hΨc hout)

/-- **The rise form of the a-fall exclusion (the named input `hnofall_forced`, rise form).** A rise `a(x) ≥ 1`, `a(x') = 0`,
`B(x) ≥ 1` on a forced nonfree `A`-edge does not occur. Numerically the rise population is empty (no pair among 1378). The reduction
`slip_minus_forced_adjacent` still uses `NoAFallForced`: a fall `2 → 1` with `B ≥ 2` is not a rise and needs the rounding argument. -/
noncomputable def NoRiseForced {word : Word} {seed : Site → Site → Prop}
    (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps) : Prop :=
  ∀ c i : Site,
    FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c →
    c ∈ (frameAt word).closedPolygon → i ∈ (frameAt word).closedPolygon →
    c + (frameAt word).uq ∈ (frameAt word).closedPolygon → i + (frameAt word).uq ∈ (frameAt word).closedPolygon →
    0 ≤ sheetPsi word c → 0 ≤ sheetPsi word i → Edge i c →
    SquareClauses.ForcedEdge (standardField word) (fun _ _ => False) c i →
    laplacian (standardField word) c = 0 → FLatticePaper.Induction.Nonfree (frameAt word) c →
    sheetPolicyA P (frameAt word).sheetShift c i →
    1 ≤ aJump word c → aJump word i = 0 → 1 ≤ BOffer word c → False

/-- **The rounded monotonicity on forced edges (named input `RoundedMonoForced`).** The statement of
`jminus_nonincrease_forced_of_sat` (ComparisonEmpty.lean:183): for a forced white `c` with forced input `o` in the polygon,
`roundedSlip(−1)(o) ≤ roundedSlip(−1)(c)`, with `roundedSlip(η)(z) = (slip η z + 1)/2`. Its hypotheses are `HasSatSelection`
(the Q1 no-fort item) and `hT` of the source lemma. -/
noncomputable def RoundedMonoForced (word : Word) : Prop :=
  ∀ c o : Site, c ∈ (frameAt word).closedPolygon → o ∈ (frameAt word).closedPolygon →
    laplacian (standardField word) c = 0 → SquareClauses.ForcedEdge (standardField word) (fun _ _ => False) c o →
    (standardField word o - standardField word (o + -(frameAt word).shortShift) + 1) / 2 ≤
      (standardField word c - standardField word (c + -(frameAt word).shortShift) + 1) / 2

/-- **The sign `−1` permit at a forced nonfree white, from the rise form and the rounding.** The cap `D₋ ∈ [−2, 0]` on the
polygon (`slip_minus_range`) leaves the drops `2 → 1` (excluded by the rounding) and `1 → 0` (excluded by `NoRiseForced`). -/
theorem slip_minus_forced_adjacent_rise {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hW : StrongEstimates word) (hSE : StrongEstimates (conjWord word))
    (hpk : (frameAt word).Packet (standardField word))
    {seed : Site → Site → Prop}
    (P : FLatticePaper.W1Phase.OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hrise : NoRiseForced P.toOldPolicyWitness.toOldPolicyData) (hround : RoundedMonoForced word) {c i : Site}
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
  have hr := hround c i hc hi hlap hfor
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

end FLatticePaper.W4Reduction
