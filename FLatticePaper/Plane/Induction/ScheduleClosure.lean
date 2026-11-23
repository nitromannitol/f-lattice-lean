import FLatticePaper.Plane.Induction.SheetFort
import FLatticePaper.Plane.Induction.S3FreeBoundary
import FLatticePaper.Plane.Induction.FanPropagation

/-! # Task 100 (c, the closing step of the minus schedule): the fort of the recurrent sheet minimum with only `H_0`, `V_0` left on the boundary

ALL_SLOPE_STEP, "Physical cut order and core": after the arcs are paid, the only boundary points of `E` not yet excluded are `H_0 = (1,0)` and
`V_0 = (0,0)`. Neither is an input of a strict-interior point: the points having `H_0` as an input are `V_0` and `H_1 = (2,0)`, and the
points having `V_0` as an input are `(0,1)` and `(0,−1)`, all outside the open rectangle. So the interior part of the fort is a finite fort
of the recurrent `M`, hence empty. Then the fort inside `E` lies in `{H_0, V_0}`, and the fort property at `H_0` and `V_0` forces their
inputs (`(1,±1)`, `(−1,0)`) into the fort, which is impossible. Hence the fort is empty (`minus_closure_empty`).

The hypotheses are the schedule's output: the fort lies in the closed polygon `E`, and every boundary point of `E` in the fort is `H_0` or
`V_0`. -/

namespace FLatticePaper.ScheduleClosure

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.FanPropagation FLatticePaper.SheetFort
open FLatticePaper.W1MSheet FLatticePaper.FanTerminal

/-- Points with `H_0 = (1,0)` as an input are `(0,0)` and `(2,0)`: the input relation at an odd point is vertical, so `H_0` is an input of an
even point only. -/
theorem hFirst_input_cases (x : Site) (h : hFirst = incomingNeg x ∨ hFirst = incomingPos x) :
    x = (2, 0) ∨ x = (0, 0) := by
  by_cases hev : EvenSite x
  · rcases h with h | h
    · rw [incomingNeg_of_even x hev] at h
      simp only [hFirst, Prod.mk.injEq] at h
      left
      exact Prod.ext (show x.1 = 2 by omega) (show x.2 = 0 by omega)
    · rw [incomingPos_of_even x hev] at h
      simp only [hFirst, Prod.mk.injEq] at h
      right
      exact Prod.ext (show x.1 = 0 by omega) (show x.2 = 0 by omega)
  · exfalso
    rcases h with h | h
    · rw [incomingNeg_of_odd x hev] at h
      simp only [hFirst, Prod.mk.injEq] at h
      unfold EvenSite at hev
      omega
    · rw [incomingPos_of_odd x hev] at h
      simp only [hFirst, Prod.mk.injEq] at h
      unfold EvenSite at hev
      omega

/-- Points with `V_0 = (0,0)` as an input are `(0,1)` and `(0,−1)`. -/
theorem vFirst_input_cases (x : Site) (h : vFirst = incomingNeg x ∨ vFirst = incomingPos x) :
    x = (0, 1) ∨ x = (0, -1) := by
  by_cases hev : EvenSite x
  · exfalso
    rcases h with h | h
    · rw [incomingNeg_of_even x hev] at h
      simp only [vFirst, Prod.mk.injEq] at h
      unfold EvenSite at hev
      omega
    · rw [incomingPos_of_even x hev] at h
      simp only [vFirst, Prod.mk.injEq] at h
      unfold EvenSite at hev
      omega
  · rcases h with h | h
    · rw [incomingNeg_of_odd x hev] at h
      simp only [vFirst, Prod.mk.injEq] at h
      left
      exact Prod.ext (show x.1 = 0 by omega) (show x.2 = 1 by omega)
    · rw [incomingPos_of_odd x hev] at h
      simp only [vFirst, Prod.mk.injEq] at h
      right
      exact Prod.ext (show x.1 = 0 by omega) (show x.2 = -1 by omega)

/-- `H_0` is not an input of a point of the open rectangle. -/
theorem hFirst_input_not_open (frame : ChildFrame) {x : Site} (h : hFirst = incomingNeg x ∨ hFirst = incomingPos x) :
    ¬ frame.openRect x := by
  obtain ⟨hpos, hnlt, hdn, hd3, -⟩ := frame.child_facts
  intro ho
  rcases hFirst_input_cases x h with rfl | rfl
  · unfold ChildFrame.openRect at ho
    rw [if_pos (by decide)] at ho
    simp only [ChildFrame.tGrade] at ho
    omega
  · unfold ChildFrame.openRect at ho
    rw [if_pos (by decide)] at ho
    simp only [ChildFrame.sGrade] at ho
    omega

/-- `V_0` is not an input of a point of the open rectangle. -/
theorem vFirst_input_not_open (frame : ChildFrame) {x : Site} (h : vFirst = incomingNeg x ∨ vFirst = incomingPos x) :
    ¬ frame.openRect x := by
  obtain ⟨hpos, hnlt, hdn, hd3, -⟩ := frame.child_facts
  intro ho
  rcases vFirst_input_cases x h with rfl | rfl
  · unfold ChildFrame.openRect at ho
    rw [if_neg (by decide)] at ho
    simp only [ChildFrame.tGrade, ChildFrame.sGrade] at ho
    omega
  · unfold ChildFrame.openRect at ho
    rw [if_neg (by decide)] at ho
    simp only [ChildFrame.tGrade, ChildFrame.sGrade] at ho
    omega

/-- **The closing step of the minus schedule**: a fort of the recurrent sheet minimum inside the closed polygon, whose boundary points are
`H_0` or `V_0` only, is empty. -/
theorem minus_closure_empty {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {S : Set Site} (hfort : IsIncomingFort (MW word) S) (hE : S ⊆ (frameAt word).closedPolygon)
    (hpaid : ∀ b, b ∈ (frameAt word).closedPolygon → ¬ (frameAt word).openRect b → b ∈ S → b = hFirst ∨ b = vFirst) :
    S = ∅ := by
  -- the interior part is a finite fort of the recurrent M, hence empty
  have hint : ∀ x ∈ S, ¬ (frameAt word).openRect x := by
    have hT : IsIncomingFort (MW word) {x | x ∈ S ∧ (frameAt word).openRect x} := by
      intro x hx
      obtain ⟨hxS, hxo⟩ := hx
      have inner : ∀ i, (i = incomingNeg x ∨ i = incomingPos x) → i ∈ S → (frameAt word).openRect i := by
        intro i hi hiS
        by_contra hnot
        have hcl := FLatticePaper.W1Exit.rectInputs (frameAt word) x hxo i hi
        rcases hpaid i hcl hnot hiS with h | h
        · rcases hi with hi | hi
          · exact hFirst_input_not_open (frameAt word) (Or.inl (h.symm.trans hi)) hxo
          · exact hFirst_input_not_open (frameAt word) (Or.inr (h.symm.trans hi)) hxo
        · rcases hi with hi | hi
          · exact vFirst_input_not_open (frameAt word) (Or.inl (h.symm.trans hi)) hxo
          · exact vFirst_input_not_open (frameAt word) (Or.inr (h.symm.trans hi)) hxo
      rcases hfort x hxS with ⟨hl, hsome⟩ | ⟨hl, hn, hp⟩
      · rcases hsome with hn | hp
        · exact Or.inl ⟨hl, Or.inl ⟨hn, inner _ (Or.inl rfl) hn⟩⟩
        · exact Or.inl ⟨hl, Or.inr ⟨hp, inner _ (Or.inr rfl) hp⟩⟩
      · exact Or.inr ⟨hl, ⟨hn, inner _ (Or.inl rfl) hn⟩, ⟨hp, inner _ (Or.inr rfl) hp⟩⟩
    have hfin : {x | x ∈ S ∧ (frameAt word).openRect x}.Finite :=
      (openRect_finite (frameAt word)).subset (fun y hy => hy.2)
    have hempty := no_finite_fort_of_recurrent (sheetMin_recurrentField hw hSE) hT hfin
    intro x hxS hxo
    have hmem : x ∈ {y | y ∈ S ∧ (frameAt word).openRect y} := ⟨hxS, hxo⟩
    rw [hempty] at hmem
    exact hmem
  -- `H_0` and `V_0` are not in the fort: their inputs would have to be in the fort, on the boundary, and different from `H_0`, `V_0`
  have hH : hFirst ∉ S := by
    intro hHS
    have hbdIn : ∀ i, (i = incomingNeg hFirst ∨ i = incomingPos hFirst) → i ∈ S → False := by
      intro i hi hiS
      have hcl := hE hiS
      have hnot := hint i hiS
      rcases hpaid i hcl hnot hiS with h | h
      · rw [h] at hi
        have hH0 : hFirst ≠ incomingNeg hFirst := by
          rw [incomingNeg_of_odd hFirst (by decide)]
          simp only [hFirst, ne_eq, Prod.mk.injEq]
          omega
        have hH1 : hFirst ≠ incomingPos hFirst := by
          rw [incomingPos_of_odd hFirst (by decide)]
          simp only [hFirst, ne_eq, Prod.mk.injEq]
          omega
        rcases hi with hi | hi
        · exact hH0 hi
        · exact hH1 hi
      · rw [h] at hi
        have hV0 : vFirst ≠ incomingNeg hFirst := by
          rw [incomingNeg_of_odd hFirst (by decide)]
          simp only [vFirst, hFirst, ne_eq, Prod.mk.injEq]
          omega
        have hV1 : vFirst ≠ incomingPos hFirst := by
          rw [incomingPos_of_odd hFirst (by decide)]
          simp only [vFirst, hFirst, ne_eq, Prod.mk.injEq]
          omega
        rcases hi with hi | hi
        · exact hV0 hi
        · exact hV1 hi
    rcases hfort hFirst hHS with ⟨hl, hsome⟩ | ⟨hl, hn, hp⟩
    · rcases hsome with hn | hp
      · exact hbdIn _ (Or.inl rfl) hn
      · exact hbdIn _ (Or.inr rfl) hp
    · exact hbdIn _ (Or.inl rfl) hn
  have hV : vFirst ∉ S := by
    intro hVS
    have hbdIn : ∀ i, (i = incomingNeg vFirst ∨ i = incomingPos vFirst) → i ∈ S → False := by
      intro i hi hiS
      have hcl := hE hiS
      have hnot := hint i hiS
      rcases hpaid i hcl hnot hiS with h | h
      · exact hH (h ▸ hiS)
      · rw [h] at hi
        have hV0 : vFirst ≠ incomingNeg vFirst := by
          rw [incomingNeg_of_even vFirst (by decide)]
          unfold vFirst
          decide
        have hV1 : vFirst ≠ incomingPos vFirst := by
          rw [incomingPos_of_even vFirst (by decide)]
          unfold vFirst
          decide
        rcases hi with hi | hi
        · exact hV0 hi
        · exact hV1 hi
    rcases hfort vFirst hVS with ⟨hl, hsome⟩ | ⟨hl, hn, hp⟩
    · rcases hsome with hn | hp
      · exact hbdIn _ (Or.inl rfl) hn
      · exact hbdIn _ (Or.inr rfl) hp
    · exact hbdIn _ (Or.inl rfl) hn
  -- so the fort is empty
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  by_cases hxo : (frameAt word).openRect x
  · exact hint x hx hxo
  · rcases hpaid x (hE hx) hxo hx with h | h
    · exact hH (h ▸ hx)
    · exact hV (h ▸ hx)

end FLatticePaper.ScheduleClosure
