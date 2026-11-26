import FLatticePaper.Plane.Induction.AlignedClassSite

/-! # A closed non-strict site has an exterior 4-neighbour (step (b) of the top-square argument)

At grade level, for a closed grade point that is not strictly interior, one of its four neighbours (right, left, up, down) is not
closed. No strictness of the neighbours is assumed, so the statement applies to any corner of a unit square. -/

namespace FLatticePaper.ExteriorNbr

open FLatticePaper FLatticePaper.W1 FLatticePaper.CrossingLattice FLatticePaper.AlignedClassGrade FLatticePaper.AlignedClassSite

theorem exterior_grade (n d T t s : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hT : T % 2 = 0)
    (hNS : ¬ SIG n d T t s) :
    ¬ ClG n d T (t + n) (s + (d + n)) ∨ ¬ ClG n d T (t - n) (s - (d + n)) ∨
      ¬ ClG n d T (t + d) (s - (d - n)) ∨ ¬ ClG n d T (t - d) (s + (d - n)) := by
  by_contra h
  simp only [not_or, not_not] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [ClG, SIG] at h1 h2 h3 h4 hNS
  omega

theorem strict_iff_SIG' {n d : ℤ} (hn : n % 2 = 1) (hd : d % 2 = 1) (z : Site) :
    StrictInterior n d z ↔ SIG n d (w1T n d) (w1t n d z) (w1s n d z) := by
  have hp := parity_w1t hn hd z
  unfold SIG
  by_cases h : EvenSite z
  · rw [sI_even h]
    unfold EvenSite at h
    generalize w1t n d z = t at *
    generalize w1s n d z = s at *
    generalize w1T n d = T at *
    constructor <;> intro hh <;> omega
  · rw [sI_odd h]
    unfold EvenSite at h
    generalize w1t n d z = t at *
    generalize w1s n d z = s at *
    generalize w1T n d = T at *
    constructor <;> intro hh <;> omega

/-- **A closed non-strict site has an exterior 4-neighbour.** -/
theorem exterior_nbr {n d : ℤ} (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (z : Site)
    (hNS : ¬ StrictInterior n d z) :
    ¬ closedRect n d (z.1 + 1, z.2) ∨ ¬ closedRect n d (z.1 - 1, z.2) ∨
      ¬ closedRect n d (z.1, z.2 + 1) ∨ ¬ closedRect n d (z.1, z.2 - 1) := by
  have hT2 := parity_w1T hn hd
  have hNSg : ¬ SIG n d (w1T n d) (w1t n d z) (w1s n d z) :=
    fun h => hNS ((strict_iff_SIG' hn hd z).mpr h)
  rcases exterior_grade n d (w1T n d) (w1t n d z) (w1s n d z) hn hd hn1 hT2 hNSg with h | h | h | h
  · left
    have e1 : w1t n d (z.1 + 1, z.2) = w1t n d z + n := by unfold w1t; ring
    have e2 : w1s n d (z.1 + 1, z.2) = w1s n d z + (d + n) := by unfold w1s; ring
    intro hc
    apply h
    rw [← e1, ← e2]
    exact (closedRect_iff_ClG hn hd (z.1 + 1, z.2)).mp hc
  · right; left
    have e1 : w1t n d (z.1 - 1, z.2) = w1t n d z - n := by unfold w1t; ring
    have e2 : w1s n d (z.1 - 1, z.2) = w1s n d z - (d + n) := by unfold w1s; ring
    intro hc
    apply h
    rw [← e1, ← e2]
    exact (closedRect_iff_ClG hn hd (z.1 - 1, z.2)).mp hc
  · right; right; right
    have e1 : w1t n d (z.1, z.2 - 1) = w1t n d z + d := by unfold w1t; ring
    have e2 : w1s n d (z.1, z.2 - 1) = w1s n d z - (d - n) := by unfold w1s; ring
    intro hc
    apply h
    rw [← e1, ← e2]
    exact (closedRect_iff_ClG hn hd (z.1, z.2 - 1)).mp hc
  · right; right; left
    have e1 : w1t n d (z.1, z.2 + 1) = w1t n d z - d := by unfold w1t; ring
    have e2 : w1s n d (z.1, z.2 + 1) = w1s n d z + (d - n) := by unfold w1s; ring
    intro hc
    apply h
    rw [← e1, ← e2]
    exact (closedRect_iff_ClG hn hd (z.1, z.2 + 1)).mp hc

end FLatticePaper.ExteriorNbr
