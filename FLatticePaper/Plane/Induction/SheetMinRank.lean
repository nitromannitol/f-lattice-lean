import FLatticePaper.Plane.Induction.Packet
import FLatticePaper.Plane.ThresholdMinimum
import FLatticePaper.Plane.Recurrence

namespace FLatticePaper.Induction
open Farey

theorem evenSite_neg_site (v : Site) (hv : EvenSite v) : EvenSite (-v) := by
  unfold EvenSite at hv ⊢
  simp only [Prod.fst_neg, Prod.snd_neg]
  omega

/-- A difference of two sheets is the minimum of the sheets at level zero. -/
theorem ChildFrame.sheetMin_eq_thresholdMin (frame : ChildFrame) (Fp : Field) :
    frame.sheetMin Fp = thresholdMin (frame.sheetA Fp) (frame.sheetC Fp) 0 := by
  funext z
  simp only [ChildFrame.sheetMin, thresholdMin, add_zero]

/-- The Laplacian of a field translated by an even vector is the Laplacian of the field at the translated site. -/
theorem laplacian_sub_even (Fp : Field) (v : Site) (hv : EvenSite v) (c : Site) :
    laplacian (fun w => Fp (w - v)) c = laplacian Fp (c - v) := by
  have h := laplacian_translate_of_even Fp c (-v) (evenSite_neg_site v hv)
  have hf : (fun w : Site => Fp (w - v)) = fun input => Fp (input + -v) := by
    funext w
    rw [sub_eq_add_neg]
  rw [hf, h, sub_eq_add_neg]

/-- Constrained burning ranks transport along an even translation of the field. -/
theorem isConstrained_translate {α : Type*} [LT α] {Fp G : Field} {rank : Site → α}
    {permits : Site → Site → Prop} (h : IsConstrainedBurningRank Fp rank permits) (v : Site)
    (hv : EvenSite v) (hlap : ∀ c, laplacian G c = laplacian Fp (c - v)) :
    IsConstrainedBurningRank G (fun w => rank (w - v)) (fun c i => permits (c - v) (i - v)) := by
  unfold IsConstrainedBurningRank at h ⊢
  intro c
  have hc := h (c - v)
  dsimp only at hc ⊢
  have hn : incomingNeg (c - v) = incomingNeg c - v := by
    rw [sub_eq_add_neg c v, incomingNeg_add_of_even c (-v) (evenSite_neg_site v hv),
      sub_eq_add_neg (incomingNeg c) v]
  have hp : incomingPos (c - v) = incomingPos c - v := by
    rw [sub_eq_add_neg c v, incomingPos_add_of_even c (-v) (evenSite_neg_site v hv),
      sub_eq_add_neg (incomingPos c) v]
  rw [hn, hp, ← hlap] at hc
  exact hc

theorem ChildFrame.evenSite_sheetShift (frame : ChildFrame) : EvenSite frame.sheetShift := by
  obtain ⟨k, hk, -, -, -, -, -, -, hsh, -⟩ := frame.sheet_facts
  refine evenSite_of_sum _ ((1 - frame.phaseW) * k) ?_
  rw [hsh]
  dsimp only
  linear_combination (1 - frame.phaseW) * hk

theorem ChildFrame.evenSite_sheetShift_add (frame : ChildFrame) :
    EvenSite (frame.sheetShift + frame.sheetOffset) := by
  obtain ⟨k, hk, -, -, -, -, -, -, hsh, hof⟩ := frame.sheet_facts
  refine evenSite_of_sum _ (frame.phaseW * k + frame.parents.even.num) ?_
  rw [hsh, hof]
  simp only [Prod.fst_add, Prod.snd_add]
  linear_combination frame.phaseW * hk

/-- The sheet C has the Laplacian of its quarter-turned parent at the translate `c − (sheetShift + sheetOffset)`:
the affine term of C is harmonic. -/
theorem ChildFrame.laplacian_sheetC (frame : ChildFrame) (Fp : Field) (c : Site) :
    laplacian (frame.sheetC Fp) c = laplacian Fp (c - (frame.sheetShift + frame.sheetOffset)) := by
  have hsplit : frame.sheetC Fp = fun w => Fp (w - frame.sheetShift - frame.sheetOffset) +
      (frame.siblingSlope (w - frame.sheetShift) + frame.sheetConstant) := by
    funext w
    unfold ChildFrame.sheetC
    ring
  have hlin : (fun w : Site => frame.siblingSlope (w - frame.sheetShift) + frame.sheetConstant) =
      fun w => frame.parents.even.num * w.1 + (-frame.parents.even.den) * w.2 +
        (frame.sheetConstant - frame.parents.even.num * frame.sheetShift.1 +
          frame.parents.even.den * frame.sheetShift.2) := by
    funext w
    unfold ChildFrame.siblingSlope
    simp only [Prod.fst_sub, Prod.snd_sub]
    ring
  have hadd : laplacian (frame.sheetC Fp) c =
      laplacian (fun w : Site => Fp (w - frame.sheetShift - frame.sheetOffset)) c +
        laplacian (fun w : Site => frame.siblingSlope (w - frame.sheetShift) + frame.sheetConstant) c := by
    rw [hsplit]
    exact laplacian_add_fn _ _ c
  have haff : laplacian (fun w : Site => frame.siblingSlope (w - frame.sheetShift) + frame.sheetConstant) c =
      0 := by
    rw [hlin]
    exact laplacian_affine _ _ _ c
  have hfun : (fun w : Site => Fp (w - frame.sheetShift - frame.sheetOffset)) =
      fun w => Fp (w - (frame.sheetShift + frame.sheetOffset)) := by
    funext w
    rw [sub_sub]
  rw [hadd, haff, add_zero, hfun,
    laplacian_sub_even Fp (frame.sheetShift + frame.sheetOffset) frame.evenSite_sheetShift_add c]

/-- The first sheet A has the constrained ranks of the quarter-turned parent, translated by the even shift. -/
theorem ChildFrame.sheetA_rank {frame : ChildFrame} {Fp : Field} {α : Type*} [LT α] {rank : Site → α}
    {permits : Site → Site → Prop} (h : IsConstrainedBurningRank Fp rank permits) :
    IsConstrainedBurningRank (frame.sheetA Fp) (fun z => rank (z - frame.sheetShift))
      (fun center input => permits (center - frame.sheetShift) (input - frame.sheetShift)) :=
  isConstrained_translate h frame.sheetShift frame.evenSite_sheetShift
    (fun c => laplacian_sub_even Fp frame.sheetShift frame.evenSite_sheetShift c)

/-- The second sheet C has the constrained ranks of the quarter-turned parent, translated by the even shift
`sheetShift + sheetOffset`. -/
theorem ChildFrame.sheetC_rank {frame : ChildFrame} {Fp : Field} {α : Type*} [LT α] {rank : Site → α}
    {permits : Site → Site → Prop} (h : IsConstrainedBurningRank Fp rank permits) :
    IsConstrainedBurningRank (frame.sheetC Fp) (fun z => rank (z - (frame.sheetShift + frame.sheetOffset)))
      (fun center input => permits (center - (frame.sheetShift + frame.sheetOffset))
        (input - (frame.sheetShift + frame.sheetOffset))) :=
  isConstrained_translate h (frame.sheetShift + frame.sheetOffset) frame.evenSite_sheetShift_add
    (fun c => frame.laplacian_sheetC Fp c)

/-- (I3) from unit slip and the two constrained ranks: the sheet minimum has a burning rank, hence is binary and
recurrent. -/
theorem ChildFrame.sheetMin_binary_recurrent (frame : ChildFrame) {Fp : Field} {α : Type*} [LinearOrder α]
    {rankA rankC : Site → α}
    (hunit : HasUnitSlip (frame.sheetA Fp) (frame.sheetC Fp))
    (hA : IsConstrainedBurningRank (frame.sheetA Fp) rankA
      (fun center input => slipIncrement (frame.sheetA Fp) (frame.sheetC Fp) center input ≤ 0))
    (hC : IsConstrainedBurningRank (frame.sheetC Fp) rankC
      (fun center input => 0 ≤ slipIncrement (frame.sheetA Fp) (frame.sheetC Fp) center input)) :
    (∀ z, laplacian (frame.sheetMin Fp) z = -1 ∨ laplacian (frame.sheetMin Fp) z = 0) ∧
      Recurrent (frame.sheetMin Fp) := by
  have hburn := isBurningRank_leftThreshold (level := 0) hunit hA hC
  rw [← frame.sheetMin_eq_thresholdMin Fp] at hburn
  refine ⟨fun z => ?_, hburn.recurrent⟩
  rcases hburn z with ⟨h, -, -⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h

end FLatticePaper.Induction
