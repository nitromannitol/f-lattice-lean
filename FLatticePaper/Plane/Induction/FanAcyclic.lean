import FLatticePaper.Plane.Induction.FanPropagation
import FLatticePaper.Plane.Induction.ContactCone

/-! # Contact-fan acyclicity (AUDIT_FREE_THREE_STEP_RETURNS §1, "Contact-fan acyclicity")

A fan step goes east from an even root and vertically from an odd root (`FanRules`). The rank `fanRank z = −2 x + parity` drops by one on
every fan step, so a fan never revisits a site. An even contact is white (its input excesses are nonnegative and the parabola has zero
Laplacian at even sites), so it has the east step of the fan. -/

namespace FLatticePaper.FanAcyclic

open FLatticePaper FLatticePaper.Induction FLatticePaper.ContactCone FLatticePaper.FanPropagation

/-- The fan rank: `−2 x` on even sites, `−2 x + 1` on odd sites. -/
noncomputable def fanRank (z : Site) : ℤ := -2 * z.1 + (if EvenSite z then 0 else 1)

theorem fanRank_east_of_even (z : Site) (hz : EvenSite z) : fanRank (incomingPos z) < fanRank z := by
  have hp : incomingPos z = (z.1 + 1, z.2) := by unfold incomingPos; rw [if_pos hz]
  have hodd : ¬ EvenSite (z.1 + 1, z.2) := by
    unfold EvenSite at hz ⊢
    simp only at hz ⊢
    omega
  rw [hp]
  unfold fanRank
  rw [if_pos hz, if_neg hodd]
  simp only
  omega

theorem fanRank_vertical_of_odd (z : Site) (hz : ¬ EvenSite z) (w : Site)
    (hw : w = incomingNeg z ∨ w = incomingPos z) : fanRank w < fanRank z := by
  have hev : EvenSite w := by
    rcases hw with rfl | rfl
    · unfold incomingNeg; rw [if_neg hz]; unfold EvenSite at hz ⊢; simp only at hz ⊢; omega
    · unfold incomingPos; rw [if_neg hz]; unfold EvenSite at hz ⊢; simp only at hz ⊢; omega
  have hx : w.1 = z.1 := by
    rcases hw with rfl | rfl
    · unfold incomingNeg; rw [if_neg hz]
    · unfold incomingPos; rw [if_neg hz]
  unfold fanRank
  rw [if_pos hev, if_neg hz, hx]
  omega

/-- One fan step strictly lowers the fan rank. -/
theorem fanRules_rank_lt {F m : Field} {S : Set Site} {next : FanT F m S → FanT F m S} {v : FanT F m S}
    (h : FanRules next v) : fanRank (next v).1 < fanRank v.1 := by
  obtain ⟨h1, h2⟩ := h
  by_cases hev : EvenSite v.1
  · rw [h1 hev]
    exact fanRank_east_of_even v.1 hev
  · exact fanRank_vertical_of_odd v.1 hev (next v).1 h2

/-- Along a fan orbit whose steps obey the rules, the fan rank strictly decreases: no site is visited twice. -/
theorem orbit_rank_lt {F m : Field} {S : Set Site} {next : FanT F m S → FanT F m S} (v0 : FanT F m S)
    (hr : ∀ k : ℕ, FanRules next (next^[k] v0)) :
    ∀ j k : ℕ, j < k → fanRank (next^[k] v0).1 < fanRank (next^[j] v0).1 := by
  have step : ∀ k : ℕ, fanRank (next^[k + 1] v0).1 < fanRank (next^[k] v0).1 := by
    intro k
    rw [Function.iterate_succ_apply']
    exact fanRules_rank_lt (hr k)
  intro j k hjk
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hjk with h | h
    · exact lt_trans (step k) (ih h)
    · subst h
      exact step j

/-- **The contact fan never returns**: the orbit of a fan from a contact has pairwise distinct sites. -/
theorem orbit_injective {F m : Field} {S : Set Site} {next : FanT F m S → FanT F m S} (v0 : FanT F m S)
    (hr : ∀ k : ℕ, FanRules next (next^[k] v0)) :
    ∀ j k : ℕ, j ≠ k → (next^[j] v0).1 ≠ (next^[k] v0).1 := by
  intro j k hjk heq
  rcases Nat.lt_or_gt_of_ne hjk with h | h
  · have := orbit_rank_lt v0 hr j k h
    rw [heq] at this
    exact lt_irrefl _ this
  · have := orbit_rank_lt v0 hr k j h
    rw [heq] at this
    exact lt_irrefl _ this

/-- **An even contact is white** (the even input excesses of the parabola are nonnegative and the even parabola has zero Laplacian, so
the Laplacian of `F` at an even contact is `≥ 0`, hence `= 0`). -/
theorem even_contact_white {F : Field} {b : ℤ} {c : Site} (hbin : laplacian F c = -1 ∨ laplacian F c = 0)
    (hc : F c = parabolaField b c) (he : EvenSite c)
    (h1 : parabolaField b (incomingNeg c) ≤ F (incomingNeg c))
    (h2 : parabolaField b (incomingPos c) ≤ F (incomingPos c)) : laplacian F c = 0 := by
  have hsum := excess_sum (F := F) (m := parabolaField b) hc
  rw [parabola_lap_even b c he] at hsum
  have hnn : 0 ≤ (F (incomingNeg c) - parabolaField b (incomingNeg c)) +
      (F (incomingPos c) - parabolaField b (incomingPos c)) := by linarith
  rcases hbin with h | h
  · rw [h] at hsum; omega
  · exact h

end FLatticePaper.FanAcyclic
