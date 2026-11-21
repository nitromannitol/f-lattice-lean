import FLatticePaper.GeneralK.PeriodExtremum
import FLatticePaper.GeneralK.AxisWalkFlux

namespace FLatticePaper.GeneralK

open Farey

/-- The subgroup whose carrier is the integral span of the prescribed deck. -/
def periodSubgroup (deck : PeriodDeck) : AddSubgroup Site where
  carrier := deck.span
  zero_mem' := ⟨0, 0, by ext <;> simp [PeriodDeck.combine]⟩
  add_mem' := by
    rintro _ _ ⟨i, j, rfl⟩ ⟨p, q, rfl⟩
    refine ⟨i + p, j + q, Prod.ext ?_ ?_⟩ <;> simp [PeriodDeck.combine] <;> ring
  neg_mem' := by
    rintro _ ⟨i, j, rfl⟩
    refine ⟨-i, -j, Prod.ext ?_ ?_⟩ <;> simp [PeriodDeck.combine] <;> ring

theorem TightInput.add_of_period {k : ℤ} {negative positive : Field} {potential : Site → ℝ}
    {center input step : Site} {drift : ℝ} (h : TightInput k negative positive potential center input)
    (hphase : Retained k step) (hm : ∀ site, potential (site + step) = potential site + drift)
    (hn : Function.Periodic negative step) (hp : Function.Periodic positive step) :
    TightInput k negative positive potential (center + step) (input + step) := by
  rcases h with ⟨hinput, heq⟩ | ⟨hinput, heq⟩
  · have hslot := inputAt_add_of_retained hphase false center
    change incomingNeg k (center + step) = incomingNeg k center + step at hslot
    refine Or.inl ⟨by rw [hinput, hslot], ?_⟩
    rw [hm, hm, hn center]
    linarith only [heq]
  · have hslot := inputAt_add_of_retained hphase true center
    change incomingPos k (center + step) = incomingPos k center + step at hslot
    refine Or.inr ⟨by rw [hinput, hslot], ?_⟩
    rw [hm, hm, hp center]
    linarith only [heq]

theorem TightReaches.symm {k : ℤ} {negative positive : Field} {potential : Site → ℝ} {first last : Site}
    (h : TightReaches k negative positive potential first last) : TightReaches k negative positive potential last first := by
  induction h with
  | refl => exact .refl
  | tail _ hedge ih => exact ih.head hedge.symm

theorem TightReaches.add_of_period {k : ℤ} {negative positive : Field} {potential : Site → ℝ}
    {first last step : Site} {drift : ℝ} (h : TightReaches k negative positive potential first last)
    (hphase : Retained k step) (hm : ∀ site, potential (site + step) = potential site + drift)
    (hn : Function.Periodic negative step) (hp : Function.Periodic positive step) :
    TightReaches k negative positive potential (first + step) (last + step) := by
  induction h with
  | refl => exact .refl
  | tail _ hedge ih =>
    rcases hedge with h | h
    · exact ih.tail (Or.inl (h.add_of_period hphase hm hn hp))
    · exact ih.tail (Or.inr (h.add_of_period hphase hm hn hp))

private theorem TightInput.exists_axisStep {k : ℤ} {negative positive : Field} {potential : Site → ℝ} {x y : Site}
    (h : TightInput k negative positive potential x y) : ∃ direction : AxisStep, y = x + direction.vector := by
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · by_cases hx : Retained k x
    · exact ⟨.left, by apply Prod.ext <;> simp [incomingNeg, hx, AxisStep.vector, sub_eq_add_neg]⟩
    · exact ⟨.down, by apply Prod.ext <;> simp [incomingNeg, hx, AxisStep.vector, sub_eq_add_neg]⟩
  · by_cases hx : Retained k x
    · exact ⟨.right, by apply Prod.ext <;> simp [incomingPos, hx, AxisStep.vector]⟩
    · exact ⟨.up, by apply Prod.ext <;> simp [incomingPos, hx, AxisStep.vector]⟩

private def AxisStep.reverse : AxisStep → AxisStep
  | .left => .right
  | .right => .left
  | .up => .down
  | .down => .up

private theorem AxisStep.vector_reverse (direction : AxisStep) : direction.reverse.vector = -direction.vector := by
  cases direction <;> simp [AxisStep.reverse, AxisStep.vector]

/-- Tight physical reachability can be realized as a finite grid walk, with
every visited vertex in the same tight component. -/
theorem TightReaches.exists_axisWalk {k : ℤ} {negative positive : Field} {potential : Site → ℝ} {x y : Site}
    (h : TightReaches k negative positive potential x y) : ∃ walk : List AxisStep, walkEnd x walk = y ∧
      ∀ site ∈ walkVertices x walk, TightReaches k negative positive potential x site := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    refine ⟨[], rfl, ?_⟩
    intro site hsite
    have heq := Finset.mem_singleton.mp (show site ∈ ({y} : Finset Site) from hsite)
    subst site
    exact .refl
  | @head first second hedge _ ih =>
    obtain ⟨walk, hwalk, hvertices⟩ := ih
    have hstep : ∃ direction : AxisStep, second = first + direction.vector := by
      rcases hedge with h | h
      · exact h.exists_axisStep
      · obtain ⟨direction, hdir⟩ := h.exists_axisStep
        refine ⟨direction.reverse, ?_⟩
        rw [AxisStep.vector_reverse, hdir, add_assoc, add_neg_cancel, add_zero]
    obtain ⟨direction, hdir⟩ := hstep
    refine ⟨direction :: walk, by simpa only [walkEnd, ← hdir] using hwalk, ?_⟩
    intro site hsite
    simp only [walkVertices, ← hdir, Finset.mem_insert] at hsite
    rcases hsite with rfl | hsite
    · exact .refl
    · have hfirst : TightReaches k negative positive potential first second := .single hedge
      exact hfirst.trans (hvertices site hsite)

theorem TightReaches.nsmul_period {deck : PeriodDeck} {k : ℤ} {negative positive : Field} {potential : Site → ℝ}
    {slopeX slopeY : ℝ} (hslope : HasDeckSlope deck potential slopeX slopeY)
    (hphase : ∀ step ∈ deck.span, Retained k step) (hneg : ∀ step ∈ deck.span, Function.Periodic negative step)
    (hpos : ∀ step ∈ deck.span, Function.Periodic positive step) {start step : Site} (hstep : step ∈ deck.span)
    (h : TightReaches k negative positive potential start (start + step)) (count : ℕ) :
    TightReaches k negative positive potential start (start + count • step) := by
  induction count with
  | zero => simpa using (Relation.ReflTransGen.refl : TightReaches k negative positive potential start start)
  | succ count ih =>
    have hmem : count • step ∈ deck.span := (periodSubgroup deck).nsmul_mem hstep count
    have hshift := h.add_of_period (hphase _ hmem) (hslope _ hmem) (hneg _ hmem) (hpos _ hmem)
    have hend : (start + step) + count • step = start + (count + 1) • step := by
      rw [succ_nsmul]
      abel
    rw [hend] at hshift
    exact ih.trans hshift

end FLatticePaper.GeneralK
