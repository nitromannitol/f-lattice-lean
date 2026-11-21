import FLatticePaper.GeneralK.PeriodPotential

namespace FLatticePaper.GeneralK

open Farey

/-- A physical input edge on which the real difference constraint is tight. -/
def TightInput (k : ℤ) (negative positive : Field) (potential : Site → ℝ) (center input : Site) : Prop :=
  (input = incomingNeg k center ∧ potential input - potential center = (negative center : ℝ)) ∨
  (input = incomingPos k center ∧ potential input - potential center = (positive center : ℝ))

/-- A walk using tight edges with either orientation. -/
abbrev TightReaches (k : ℤ) (negative positive : Field) (potential : Site → ℝ) (first last : Site) : Prop :=
  Relation.ReflTransGen (fun x y => TightInput k negative positive potential x y ∨
    TightInput k negative positive potential y x) first last

theorem TightReaches.exists_int_sub {k : ℤ} {negative positive : Field} {potential : Site → ℝ}
    {first last : Site} (h : TightReaches k negative positive potential first last) :
    ∃ difference : ℤ, potential last - potential first = (difference : ℝ) := by
  induction h with
  | refl => exact ⟨0, by simp⟩
  | @tail center input _ edge ih =>
    obtain ⟨difference, hd⟩ := ih
    rcases edge with (⟨-, heq⟩ | ⟨-, heq⟩) | (⟨-, heq⟩ | ⟨-, heq⟩)
    · exact ⟨difference + negative center, by push_cast; linarith only [hd, heq]⟩
    · exact ⟨difference + positive center, by push_cast; linarith only [hd, heq]⟩
    · exact ⟨difference - negative input, by push_cast; linarith only [hd, heq]⟩
    · exact ⟨difference - positive input, by push_cast; linarith only [hd, heq]⟩

private theorem exists_rat_slopes_of_integral_basis {deck : PeriodDeck} (hdet : deck.det ≠ 0)
    {slopeX slopeY : ℝ} {m n : ℤ}
    (hm : slopeX * (deck.kernel.1 : ℝ) + slopeY * (deck.kernel.2 : ℝ) = (m : ℝ))
    (hn : slopeX * (deck.transverse.1 : ℝ) + slopeY * (deck.transverse.2 : ℝ) = (n : ℝ)) :
    ∃ qX qY : ℚ, (qX : ℝ) = slopeX ∧ (qY : ℝ) = slopeY := by
  let qX := ((m : ℚ) * (deck.transverse.2 : ℚ) - (n : ℚ) * (deck.kernel.2 : ℚ)) / (deck.det : ℚ)
  let qY := ((n : ℚ) * (deck.kernel.1 : ℚ) - (m : ℚ) * (deck.transverse.1 : ℚ)) / (deck.det : ℚ)
  have hd : (deck.det : ℝ) ≠ 0 := by exact_mod_cast hdet
  refine ⟨qX, qY, ?_, ?_⟩
  · push_cast [qX]
    apply (div_eq_iff hd).mpr
    simp only [PeriodDeck.det, Int.cast_sub, Int.cast_mul]
    linear_combination -(deck.transverse.2 : ℝ) * hm + (deck.kernel.2 : ℝ) * hn
  · push_cast [qY]
    apply (div_eq_iff hd).mpr
    simp only [PeriodDeck.det, Int.cast_sub, Int.cast_mul]
    linear_combination -(deck.kernel.1 : ℝ) * hn + (deck.transverse.1 : ℝ) * hm

/-- Tight walks along the two period generators force integral increments
on the entire deck and make both real slope coordinates rational. -/
theorem HasDeckSlope.exists_rat_of_tight_basis_walks {deck : PeriodDeck} (hdet : deck.det ≠ 0)
    {k : ℤ} {negative positive : Field} {potential : Site → ℝ} {slopeX slopeY : ℝ}
    (hslope : HasDeckSlope deck potential slopeX slopeY) {u v : Site}
    (hkernel : TightReaches k negative positive potential u (u + deck.kernel))
    (htransverse : TightReaches k negative positive potential v (v + deck.transverse)) :
    ∃ qX qY : ℚ, (qX : ℝ) = slopeX ∧ (qY : ℝ) = slopeY ∧
      ∀ step ∈ deck.span, ∃ increment : ℤ,
        (qX : ℝ) * (step.1 : ℝ) + (qY : ℝ) * (step.2 : ℝ) = (increment : ℝ) := by
  have hu : deck.kernel ∈ deck.span := ⟨1, 0, by simp [PeriodDeck.combine]⟩
  have hv : deck.transverse ∈ deck.span := ⟨0, 1, by simp [PeriodDeck.combine]⟩
  obtain ⟨m, hm⟩ := hkernel.exists_int_sub
  obtain ⟨n, hn⟩ := htransverse.exists_int_sub
  have hm' := hslope deck.kernel hu u
  have hn' := hslope deck.transverse hv v
  rw [hm', add_sub_cancel_left] at hm
  rw [hn', add_sub_cancel_left] at hn
  obtain ⟨qX, qY, hx, hy⟩ := exists_rat_slopes_of_integral_basis hdet hm hn
  refine ⟨qX, qY, hx, hy, ?_⟩
  rintro _ ⟨i, j, rfl⟩
  refine ⟨i * m + j * n, ?_⟩
  rw [hx, hy]
  simp only [PeriodDeck.combine, Int.cast_add, Int.cast_mul]
  linear_combination (i : ℝ) * hm + (j : ℝ) * hn

end FLatticePaper.GeneralK
