import FLatticePaper.Plane.Induction.W4Reduction
import FLatticePaper.Plane.Induction.W4Cases

/-! # W4 (Q34): the rise exclusion, by the conjugate class (i) and the named free-tail input

`NoRiseForced P` (W4Reduction) says that a rise `a(x) ≥ 1`, `a(x') = 0`, `B(x) ≥ 1` does not occur on a forced nonfree
`A`-edge with retained policy `P`. The conjugate Nonfree dichotomy splits the proof:

* **Class (i)** (proved here, `jumpA_mono_of_root`, `rise_excluded_nonfree`): if `zTurn x` is nonfree in the conjugate frame, the
  root condition `laplacian (zTurn x) = −1 ∨ ForcedEdge (zTurn x) (zTurn x')` holds (`nonfree_root_forced_nonfree`, from the
  conjugate W1 forcing `hW1`), and the retained edge is then monotone: `a(x) ≤ a(x')`. A fall `a(x') = 0` is impossible.
* **Free tail** (the named input `FreeTailRise`): if `zTurn x` is not conjugate nonfree, some deck translate `zTurn x + t` is a
  conjugate free point (freeH or freeV). This is the free-tail case of Q34's class (i) sentence, *reflection preserves the
  intrinsically forced input, so P' is nonincreasing on this reflected old edge*, with the intrinsic forced input read at a
  conjugate free point as the prescribed input. It is not a theorem here: at a free tail the root condition of the reflection
  fails, so the reflection of the retained edge is not available from `hpol` alone (Q35 files the gap).

`noRiseForced_of_free_tail` proves `NoRiseForced P` from `FreeTailRise P` and the proved class (i).

**Superseded:** `FreeTailRise` is no longer needed. `W4Guard.noRiseForced_proved` proves `NoRiseForced` from the unit price bound
(`aJump_sub_le_one`, so `a(c) = 1`), the class (i) (`rise_excluded_nonfree`) and the free-tail theorem `W4Guard.freeTail_a1` (the old H star,
the old V with `j = 0`, `j > 0` by the guard, and the exceptional endpoint). -/

namespace FLatticePaper.W4FreeTail

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1MSheet FLatticePaper.W1Step FLatticePaper.W4Reduction

/-- **The monotone form of `nonfree_drop_excluded`.** With the root condition at `zTurn x`, the retained edge `x → x'` gives
`jumpA x ≤ jumpA x'` (the reflected price permit, with `Q31` in `jumpA_eq_cutPrice`). The argument is the one of
`nonfree_drop_excluded`, without the assumption `jumpA x = 1`. -/
theorem jumpA_mono_of_root {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop}
    (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    {x x' : Site} (hpol : parentPolicy P x x')
    (hroot : laplacian (standardField (conjWord word)) (zTurn x) = -1 ∨
      SquareClauses.ForcedEdge (standardField (conjWord word)) (fun _ _ => False) (zTurn x) (zTurn x')) :
    jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x ≤
      jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x' := by
  have hrefl := parentPolicy_reflection P hpol hroot
  have hmono : (frameAt (conjWord word)).cutPrice -
        (frameAt (conjWord word)).price (standardField (conjWord word)) (zTurn ((1, -1) - x)) ≤
      (frameAt (conjWord word)).cutPrice -
        (frameAt (conjWord word)).price (standardField (conjWord word)) (zTurn ((1, -1) - x')) :=
    parentPolicy_price P _ _ hrefl
  rw [← jumpA_eq_cutPrice h hSE x, ← jumpA_eq_cutPrice h hSE x'] at hmono
  omega

/-- **Class (i) of the rise exclusion.** A conjugate-nonfree old root `zTurn x` excludes the rise `a(x) ≥ 1`, `a(x') = 0`. -/
theorem rise_excluded_nonfree {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop}
    (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
      (standardField (conjWord word)))
    {x x' : Site}
    (hnf : FLatticePaper.Induction.Nonfree (frameAt (conjWord word)) (zTurn x))
    (hpol : parentPolicy P x x')
    (h1 : 1 ≤ jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x)
    (h0 : jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x' = 0) : False := by
  have hmono := jumpA_mono_of_root h hSE P hpol (nonfree_root_forced_nonfree P hSE.packet hW1 hnf hpol)
  omega

/-- **The free-tail input (named, Q35).** At a forced nonfree white `c` with forced input `i` (both in the polygon, retained
`sheetPolicyA P` edge, `laplacian c = 0`, `c` nonfree), where the conjugate tail `zTurn (c − shift)` is a deck translate of a free
point (freeH or freeV) of the conjugate frame, a rise does not occur: `a(c) ≤ a(i)` with `a(c) ≥ 1`, `B(c) ≥ 1`.
Quoted from Q34's class (i) sentence: *reflection preserves the intrinsically forced input, so P' is nonincreasing on this
reflected old edge*, with the intrinsic input read at a conjugate free point as the prescribed input. -/
def FreeTailRise {word : Word} {seed : Site → Site → Prop}
    (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps) : Prop :=
  ∀ c i : Site,
    FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c →
    c ∈ (frameAt word).closedPolygon → i ∈ (frameAt word).closedPolygon →
    c + (frameAt word).uq ∈ (frameAt word).closedPolygon → i + (frameAt word).uq ∈ (frameAt word).closedPolygon →
    0 ≤ sheetPsi word c → 0 ≤ sheetPsi word i → Edge i c →
    SquareClauses.ForcedEdge (standardField word) (fun _ _ => False) c i →
    laplacian (standardField word) c = 0 → FLatticePaper.Induction.Nonfree (frameAt word) c →
    sheetPolicyA P (frameAt word).sheetShift c i →
    (∃ t ∈ (frameAt (conjWord word)).child.modifiedDeck.span,
      zTurn (c - (frameAt word).sheetShift) + t ∈
        (frameAt (conjWord word)).freeH ∪ (frameAt (conjWord word)).freeV) →
    1 ≤ aJump word c → 1 ≤ BOffer word c → aJump word c ≤ aJump word i

/-- The sheet jump at `c` is the parent jump at `c − l_v`. -/
theorem aJump_eq_jumpA (word : Word) (z : Site) :
    aJump word z = jumpA (frameAt word) (quarterTurnField (standardField (conjWord word)))
      (z - (frameAt word).sheetShift) := by
  unfold aJump
  exact sheetA_uq_eq_jumpA z

/-- **`NoRiseForced` from the conjugate class (i) and the free-tail input.** The conjugate nonfree case is
`rise_excluded_nonfree`; otherwise `zTurn x` has a free translate (the Nonfree dichotomy) and `FreeTailRise` gives `a(c) ≤ a(i)`,
which contradicts `a(i) = 0 < 1 ≤ a(c)`. -/
theorem noRiseForced_of_free_tail {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop}
    (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
      (standardField (conjWord word)))
    (hFree : FreeTailRise P) : NoRiseForced P := by
  intro c i hSI hc hi hcu hiu hΨc hΨi hEdge hfor hlap hnf hret h1 h0 hB
  by_cases hconj : FLatticePaper.Induction.Nonfree (frameAt (conjWord word))
      (zTurn (c - (frameAt word).sheetShift))
  · rw [aJump_eq_jumpA] at h1 h0
    exact rise_excluded_nonfree h hSE P hW1 hconj hret h1 h0
  · have hfree : ∃ t ∈ (frameAt (conjWord word)).child.modifiedDeck.span,
        zTurn (c - (frameAt word).sheetShift) + t ∈
          (frameAt (conjWord word)).freeH ∪ (frameAt (conjWord word)).freeV := by
      unfold FLatticePaper.Induction.Nonfree at hconj
      push Not at hconj
      obtain ⟨v, hv, hmem⟩ := hconj
      exact ⟨v, hv, hmem⟩
    have hle := hFree c i hSI hc hi hcu hiu hΨc hΨi hEdge hfor hlap hnf hret hfree h1 hB
    omega

end FLatticePaper.W4FreeTail
