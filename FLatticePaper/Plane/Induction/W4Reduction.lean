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
noncomputable def NoRiseForced (word : Word) : Prop :=
  ∀ c i : Site,
    c ∈ (frameAt word).closedPolygon → i ∈ (frameAt word).closedPolygon →
    c + (frameAt word).uq ∈ (frameAt word).closedPolygon → i + (frameAt word).uq ∈ (frameAt word).closedPolygon →
    0 ≤ sheetPsi word c → 0 ≤ sheetPsi word i → Edge i c →
    SquareClauses.ForcedEdge (standardField word) (fun _ _ => False) c i →
    laplacian (standardField word) c = 0 → FLatticePaper.Induction.Nonfree (frameAt word) c →
    1 ≤ aJump word c → aJump word i = 0 → 1 ≤ BOffer word c → False

end FLatticePaper.W4Reduction
