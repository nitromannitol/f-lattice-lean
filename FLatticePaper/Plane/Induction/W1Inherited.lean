import FLatticePaper.Plane.Induction.W1Phase
import FLatticePaper.Plane.Induction.StrongResidual
import FLatticePaper.Plane.Induction.StrongEstimates
import FLatticePaper.Plane.Induction.WeightPolicy

/-! # Task 86: the increments of the inherited policy data (the lead's (2))

The inherited policy `P : OldPolicyRanked frame G seed η` carries, on one relation `P.retained`: the quota, the price and raw-slip
monotonicity (`priceNonincreasing`, `rawSlipNonincreasing`), the base rank with increments `(−1, η)` (`rankIncr`), and the strict decrease
(`rank_decr`). With the drifts of the price (`−1` along the kernel, `0` along the transverse) and of the short slip (`0`, `2η`), the rounded
slip `J_η = (D_η + 1)/2` drifts by `0`, `η`, and the monotone hull lemma gives the increments `(−1, 2η)` for that same relation. -/

namespace FLatticePaper.W1Inherited

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1Phase

/-- **The `(−1, 2η)` increments of the inherited policy** (task 86). -/
theorem rankIncr_two_of_ranked {η : ℤ} {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (P : OldPolicyRanked frame G seed η)
    (hD : frame.child.modifiedDeck.kernel.1 * frame.child.modifiedDeck.transverse.2 -
      frame.child.modifiedDeck.kernel.2 * frame.child.modifiedDeck.transverse.1 ≠ 0)
    (hpd : ∀ z, frame.price G (z + frame.child.modifiedDeck.kernel) - frame.price G z = -1 ∧
      frame.price G (z + frame.child.modifiedDeck.transverse) - frame.price G z = 0)
    (hsd : ∀ η : ℤ, (η = 1 ∨ η = -1) → ∀ z,
      frame.slip G η (z + frame.child.modifiedDeck.kernel) - frame.slip G η z = 0 ∧
      frame.slip G η (z + frame.child.modifiedDeck.transverse) - frame.slip G η z = 2 * η)
    (hη : η = 1 ∨ η = -1) :
    RankWithIncrements P.retained frame.child.modifiedDeck.kernel frame.child.modifiedDeck.transverse (-1) (2 * η) := by
  have hPU : ∀ z, frame.price G (z + frame.child.modifiedDeck.kernel) = frame.price G z - 1 :=
    fun z => by linarith [(hpd z).1]
  have hPV : ∀ z, frame.price G (z + frame.child.modifiedDeck.transverse) = frame.price G z :=
    fun z => by linarith [(hpd z).2]
  have hJU : ∀ z, frame.roundedSlip G η (z + frame.child.modifiedDeck.kernel) = frame.roundedSlip G η z := by
    intro z
    have := (hsd η hη z).1
    unfold ChildFrame.roundedSlip
    omega
  have hJV : ∀ z, frame.roundedSlip G η (z + frame.child.modifiedDeck.transverse) = frame.roundedSlip G η z + η := by
    intro z
    have := (hsd η hη z).2
    unfold ChildFrame.roundedSlip
    omega
  have hmono : ∀ x y, P.retained x y →
      frame.price G y ≤ frame.price G x ∧ frame.roundedSlip G η y ≤ frame.roundedSlip G η x := by
    intro x y h
    refine ⟨P.priceNonincreasing x y h, ?_⟩
    have hs : G y - G (y + η • frame.shortShift) ≤ G x - G (x + η • frame.shortShift) :=
      P.rawSlipNonincreasing x y h
    unfold ChildFrame.roundedSlip ChildFrame.slip
    omega
  exact rankWithIncrements_of_monotone_hull hD hη hPU hPV hJU hJV hmono (P.rankIncr η hη) 1 2 one_pos two_pos

end FLatticePaper.W1Inherited
