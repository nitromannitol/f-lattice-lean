import FLatticePaper.Plane.Induction.TwosDrifts
import FLatticePaper.Plane.Induction.TwosZeroStrip
import FLatticePaper.Plane.Induction.StrongPriceRange
import FLatticePaper.Plane.Induction.BaseRecurrent
import FLatticePaper.Construction.LadderRank
import FLatticePaper.Construction.LadderRotation

/-! Task 72 / twos base: the price range `c₀ − 1 ≤ P ≤ c₀` of `standardField (2^(k+1))` on its closed polygon.

The standard field is recurrent: `ladderOdd_exists_recurrent_extension` gives a recurrent ladder extension `S` at `d = 2k+4`, the
rotation `rotateLadderField` keeps recurrence (`rotateLadderField_recurrent`), and `twos_standardField_eq_rotate` identifies the
twos field with that rotation. So `M = standardField (2^(k+1))` is a `RecurrentField` and `priceRange_of_recurrent` applies with
`M = F`, the packet binarity and reflection, and the twos price drifts (`TwosDrifts`).

The one named input is the boundary bound `hbd` (`P ≤ c₀` on `OnBoundary E`). It is checked numerically for `k = 0..4`
(boundary `P` takes the values `c₀ − 1` and `c₀` only), but it is not yet proved: the shift `z − v` leaves `E` for about half the
boundary points, and no constant deck shift returns it to `E` on a whole side. -/

namespace FLatticePaper.Induction
open Farey Construction

/-- **The standard field of `2^(k+1)` is recurrent.** -/
theorem twos_standardField_recurrentField (k : ℕ) :
    RecurrentField (standardField (List.replicate (k + 1) Digit.two)) := by
  have hvalid : BaseMask.ladderOdd.Valid (2 * (k : ℤ) + 4) := ⟨by omega, by omega⟩
  obtain ⟨S, hagree, hperiod, -, hsuper, hrec⟩ := ladderOdd_exists_recurrent_extension hvalid
  have hrot := (rotateLadderField_recurrent (den := 2 * (k : ℤ) + 4) hrec hsuper).2
  have heq : standardField (List.replicate (k + 1) Digit.two) = rotateLadderField (2 * (k : ℤ) + 4) S :=
    funext fun z => twos_standardField_eq_rotate k hagree hperiod z
  have hpk := twos_packet_standard k (fun _ hz ht => twos_zero_strip k hz ht) (fun _ hz hs => twos_harm_strip k hz hs)
  have hbin := hpk.binary
  rw [heq] at hbin ⊢
  exact recurrentField_of_recurrent hrot hbin

/-- **The price range of `2^(k+1)` on its closed polygon, from the boundary bound `hbd`.** -/
theorem twos_priceRange_of_boundary (k : ℕ)
    (hbd : ∀ z, OnBoundary (frameAt (List.replicate (k + 1) Digit.two)).closedPolygon z →
      (frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) z ≤
        (frameAt (List.replicate (k + 1) Digit.two)).cutPrice) :
    ∀ z ∈ (frameAt (List.replicate (k + 1) Digit.two)).closedPolygon,
      (frameAt (List.replicate (k + 1) Digit.two)).cutPrice - 1 ≤
          (frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) z ∧
        (frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) z ≤
          (frameAt (List.replicate (k + 1) Digit.two)).cutPrice := by
  have hpk := twos_packet_standard k (fun _ hz ht => twos_zero_strip k hz ht) (fun _ hz hs => twos_harm_strip k hz hs)
  exact FLatticePaper.StrongPriceRange.priceRange_of_recurrent (frameAt (List.replicate (k + 1) Digit.two))
    (fun _ _ => rfl) hpk.binary hpk.binary (twos_standardField_recurrentField k) hbd hpk.reflection
    (fun w => by have := twos_price_drift_kernel k w; linarith)
    (fun w => by have := twos_price_drift_transverse k w; linarith)

end FLatticePaper.Induction
