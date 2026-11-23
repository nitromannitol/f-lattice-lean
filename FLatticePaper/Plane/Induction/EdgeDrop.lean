import FLatticePaper.Plane.Induction.NeighbourDrop

/-! Task 72 (case (b), the H drop along an edge, with the sharp conjugate band).

For an edge `i ∈ {incomingNeg c, incomingPos c}`, the parent `t`-grade changes by `±N` from an even centre (the neighbour is odd) and
by `±D` from an odd centre (the neighbour is even). With the sharp conjugate V band `1 ≤ t_p x + k T_p ≤ N + D − 1` at the root
`x = c − sheetShift`, the regular H drop `H_drop_regular` applies: the value `N + D` is outside the band, so the residual of
`H_drop_regular` does not occur. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper FLatticePaper.W1Seeds

/-- The parent `t`-grade difference along an edge: `±N` from an even centre, `±D` from an odd centre. -/
theorem edge_step_parent (frame : ChildFrame) {c i : Site}
    (hi : i = FLatticePaper.incomingNeg c ∨ i = FLatticePaper.incomingPos c) :
    (EvenSite c ∧ (frame.parentTGrade i - frame.parentTGrade c = frame.parents.odd.num ∨
        frame.parentTGrade i - frame.parentTGrade c = -frame.parents.odd.num)) ∨
      (¬ EvenSite c ∧ (frame.parentTGrade i - frame.parentTGrade c = frame.parents.odd.den ∨
        frame.parentTGrade i - frame.parentTGrade c = -frame.parents.odd.den)) := by
  by_cases hc : EvenSite c
  · left
    refine ⟨hc, ?_⟩
    simp only [FLatticePaper.incomingNeg, FLatticePaper.incomingPos, if_pos hc] at hi
    unfold ChildFrame.parentTGrade
    rcases hi with rfl | rfl
    · right
      try dsimp only
      ring
    · left
      try dsimp only
      ring
  · right
    refine ⟨hc, ?_⟩
    simp only [FLatticePaper.incomingNeg, FLatticePaper.incomingPos, if_neg hc] at hi
    unfold ChildFrame.parentTGrade
    rcases hi with rfl | rfl
    · left
      try dsimp only
      ring
    · right
      try dsimp only
      ring

/-- An edge flips the site parity. -/
theorem edge_parity_flip {c i : Site} (hi : i = FLatticePaper.incomingNeg c ∨ i = FLatticePaper.incomingPos c) :
    EvenSite i ↔ ¬ EvenSite c := by
  unfold FLatticePaper.incomingNeg FLatticePaper.incomingPos at hi
  by_cases hc : EvenSite c
  · simp only [if_pos hc] at hi
    have hc' : (c.1 + c.2) % 2 = 0 := hc
    rcases hi with rfl | rfl
    · show ((c.1 - 1) + c.2) % 2 = 0 ↔ ¬ ((c.1 + c.2) % 2 = 0)
      omega
    · show ((c.1 + 1) + c.2) % 2 = 0 ↔ ¬ ((c.1 + c.2) % 2 = 0)
      omega
  · simp only [if_neg hc] at hi
    have hc' : ¬ ((c.1 + c.2) % 2 = 0) := hc
    rcases hi with rfl | rfl
    · show (c.1 + (c.2 - 1)) % 2 = 0 ↔ ¬ ((c.1 + c.2) % 2 = 0)
      omega
    · show (c.1 + (c.2 + 1)) % 2 = 0 ↔ ¬ ((c.1 + c.2) % 2 = 0)
      omega

/-- Subtracting an even vector preserves site parity. -/
theorem evenSite_sub_even_iff {s c : Site} (hs : EvenSite s) : EvenSite (c - s) ↔ EvenSite c := by
  unfold EvenSite at hs ⊢
  simp only [Prod.fst_sub, Prod.snd_sub] at hs ⊢
  constructor <;> intro hh <;> omega

/-- **The H drop along an edge, with the sharp conjugate band.** If the root `x = c − sheetShift` has `t_p x + k T_p` in
`[1, N + D − 1]` (the conjugate V band), the edge drop `jump x = 1`, `jump (i − sheetShift) = 0` is impossible. -/
theorem H_drop_edge {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpar : SeedFields (conjWord word)) {c i : Site}
    (hi : i = FLatticePaper.incomingNeg c ∨ i = FLatticePaper.incomingPos c) {k : ℤ}
    (hx : jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) (c - (frameAt word).sheetShift) = 1)
    (hy : jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) (i - (frameAt word).sheetShift) = 0)
    (hband : 1 ≤ (frameAt word).parentTGrade (c - (frameAt word).sheetShift) +
        k * oddParentPeriod (frameAt word) ∧
      (frameAt word).parentTGrade (c - (frameAt word).sheetShift) + k * oddParentPeriod (frameAt word) ≤
        (frameAt word).parents.odd.num + (frameAt word).parents.odd.den - 1) : False := by
  have hsE := (frameAt word).evenSite_sheetShift
  have hyE : EvenSite (i - (frameAt word).sheetShift) ↔ EvenSite i := evenSite_sub_even_iff hsE
  have hflip := edge_parity_flip hi
  have hdiff : (frameAt word).parentTGrade (i - (frameAt word).sheetShift) -
      (frameAt word).parentTGrade (c - (frameAt word).sheetShift) =
      (frameAt word).parentTGrade i - (frameAt word).parentTGrade c := by
    unfold ChildFrame.parentTGrade
    simp only [Prod.fst_sub, Prod.snd_sub]
    ring
  have hstep : (EvenSite (i - (frameAt word).sheetShift) ∧
        ((frameAt word).parentTGrade (i - (frameAt word).sheetShift) -
          (frameAt word).parentTGrade (c - (frameAt word).sheetShift) = (frameAt word).parents.odd.den ∨
        (frameAt word).parentTGrade (i - (frameAt word).sheetShift) -
          (frameAt word).parentTGrade (c - (frameAt word).sheetShift) = -(frameAt word).parents.odd.den)) ∨
      (¬ EvenSite (i - (frameAt word).sheetShift) ∧
        ((frameAt word).parentTGrade (i - (frameAt word).sheetShift) -
          (frameAt word).parentTGrade (c - (frameAt word).sheetShift) = (frameAt word).parents.odd.num ∨
        (frameAt word).parentTGrade (i - (frameAt word).sheetShift) -
          (frameAt word).parentTGrade (c - (frameAt word).sheetShift) = -(frameAt word).parents.odd.num)) := by
    rw [hdiff]
    rcases edge_step_parent (frameAt word) hi with ⟨hc, hs⟩ | ⟨hc, hs⟩
    · right
      refine ⟨?_, hs⟩
      rw [hyE, hflip]
      exact not_not.mpr hc
    · left
      refine ⟨?_, hs⟩
      rw [hyE, hflip]
      exact hc
  have hu : (frameAt word).parentTGrade (c - (frameAt word).sheetShift) + k * oddParentPeriod (frameAt word) ≠
      (frameAt word).parents.odd.num + (frameAt word).parents.odd.den := by
    intro heq
    linarith [hband.2]
  exact H_drop_regular h hSE hpar hx hy (Or.inl hband) hstep hu

end FLatticePaper.Induction
