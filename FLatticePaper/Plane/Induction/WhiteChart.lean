import FLatticePaper.Plane.Induction.WhiteNative
import FLatticePaper.Plane.Induction.MatchedPolicy
import FLatticePaper.Plane.Induction.W1HagreeNonfree
import FLatticePaper.Plane.Induction.RepClasses

/-! # The chart coordinates of the sheet pointer (W1 identification), and the native white W2 with the pointer as premise

At `ε = +1` the sheet shift is `0` and `Y = X − sheetShift = (2D, 2N)` (`RepClasses.Y_eq`). Then for every `a`,
`zTurn (a + Y) = zTurn a + transverse`, the conjugate's transverse `(−2N, 2D)` (`RepClasses.conj_transverse`), a deck vector.
So the retained relation at the chart points `zTurn (z + X − lv)` is the retained relation at `zTurn (z − lv)` shifted by the
transverse, and span invariance of the retained relation (a premise, `deck_of_games` for the canonical witness) makes the two
equivalent. The sheet pointer `u = pointerOf (sheetPolicyA P lv) z` is retained at `zTurn (z − lv)`
(`W1HagreeNonfree.sheetPolicyA_pointer_retained`), which gives the chart retained relation. -/

namespace FLatticePaper.WhiteChart

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1MSheet FLatticePaper.Sec3Shift

/-- `zTurn (a + Y) = zTurn a + transverse` for the chart shift `Y = (2D, 2N)`. -/
theorem zTurn_add_Y (a : Site) (D N : ℤ) :
    zTurn (a + (2 * D, 2 * N)) = zTurn a + (-2 * N, 2 * D) := by
  unfold zTurn
  ext <;> simp <;> ring

/-- **Reconciliation.** At `ε = +1`, the retained relation at the chart points is the retained relation at the sheet points,
given span invariance of the retained relation under the conjugate's deck vectors. -/
theorem chart_retained_iff {word : Word} (hε : (frameAt word).eps = 1) {seed : Site → Site → Prop}
    (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hspan : ∀ (i j : ℤ) (a b : Site), P.retained a b →
      P.retained (a - (frameAt (conjWord word)).child.modifiedDeck.combine i j)
        (b - (frameAt (conjWord word)).child.modifiedDeck.combine i j))
    (h : ∃ x ∈ word, x ≠ Digit.three) (z u : Site) :
    P.retained (zTurn (z + sec3X word - (frameAt word).sheetShift))
        (zTurn (u + sec3X word - (frameAt word).sheetShift)) ↔
      P.retained (zTurn (z - (frameAt word).sheetShift))
        (zTurn (u - (frameAt word).sheetShift)) := by
  have hY : sec3X word = (2 * (frameAt word).parents.odd.den, 2 * (frameAt word).parents.odd.num) := by
    unfold sec3X
    rw [if_pos hε]
  have hTr := FLatticePaper.RepClasses.conj_transverse h
  have hT : (frameAt (conjWord word)).child.modifiedDeck.combine 0 1 =
      (frameAt (conjWord word)).child.modifiedDeck.transverse := by
    unfold PeriodDeck.combine
    ext <;> simp
  have hT' : (frameAt (conjWord word)).child.modifiedDeck.combine 0 (-1) =
      -(frameAt (conjWord word)).child.modifiedDeck.transverse := by
    unfold PeriodDeck.combine
    ext <;> simp
  have e : ∀ x : Site, zTurn (x + sec3X word - (frameAt word).sheetShift) =
      zTurn (x - (frameAt word).sheetShift) + (frameAt (conjWord word)).child.modifiedDeck.transverse := by
    intro x
    have hx : x + sec3X word - (frameAt word).sheetShift = (x - (frameAt word).sheetShift) + sec3X word := by abel
    rw [hx, hY, zTurn_add_Y, hTr]
  rw [e z, e u]
  constructor
  · intro hc
    have key := hspan 0 1 _ _ hc
    rw [hT, add_sub_cancel_right, add_sub_cancel_right] at key
    exact key
  · intro h0
    have key := hspan 0 (-1) _ _ h0
    rw [hT', sub_neg_eq_add, sub_neg_eq_add] at key
    exact key

/-- **W2 with the W1 identification as the sheet pointer (`ε = +1`, sign `+1`).** The identification `hptr` is the A-branch of
`WestException.sheetOut_forcedIn`: the forced input is the sheet pointer of `sheetPolicyA`. The span invariance `hspan` is
`deck_of_games` for the canonical witness of `P`. -/
theorem forced_native_plus_ptr {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hW : StrongEstimates word) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hspan : ∀ (i j : ℤ) (a b : Site), P.retained a b →
      P.retained (a - (frameAt (conjWord word)).child.modifiedDeck.combine i j)
        (b - (frameAt (conjWord word)).child.modifiedDeck.combine i j))
    (hε : (frameAt word).eps = 1) {z u : Site}
    (hF : laplacian (standardField word) z = 0) (hA : standardField word z = FqW word z)
    (hi : ∀ i : Site, (i = incomingNeg z ∨ i = incomingPos z) → i ∈ (frameAt word).closedPolygon)
    (hu : u = incomingNeg z ∨ u = incomingPos z)
    (hsw : z + sec3X word ∈ (frameAt word).closedPolygon)
    (hsu : u + sec3X word ∈ (frameAt word).closedPolygon)
    (hptr : u = FLatticePaper.W1Pointers.pointerOf
      (sheetPolicyA P (frameAt word).sheetShift) z) :
    (frameAt word).slip (standardField word) 1 u ≤ (frameAt word).slip (standardField word) 1 z := by
  have hbin : ∀ x, laplacian (standardField (conjWord word)) x = -1 ∨ laplacian (standardField (conjWord word)) x = 0 :=
    fun x => hSE.packet.binary x
  have hlv : EvenSite (frameAt word).sheetShift := (frameAt word).evenSite_sheetShift
  have hp := FLatticePaper.W1HagreeNonfree.sheetPolicyA_pointer_retained P hbin (frameAt word).sheetShift hlv z
  rw [← hptr] at hp
  have hid := (chart_retained_iff hε P hspan h z u).mpr hp
  exact FLatticePaper.WhiteNative.forced_native_plus h hW hSE P hε hF hA hi hu hsw hsu hid

end FLatticePaper.WhiteChart
