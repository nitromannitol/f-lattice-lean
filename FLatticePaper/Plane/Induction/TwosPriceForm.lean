import FLatticePaper.Plane.Induction.TwosPriceE
import FLatticePaper.Plane.Induction.TwosTileCover
import FLatticePaper.Plane.Induction.TwosDrifts

/-! Task 118, base inputs at `2^(k+1)` (the unit price): the explicit price of the twos standard field on the closed polygon.

On the closed polygon, which is the linear predicate `TwosKey` (`twos_E_key`), the field is the near-one closed form
`paperNearLadderValue` at `z + (0,1)` (`twos_F_E`), and the price `P z = F z − F(z − v) + slope z` is evaluated in one of the
three shift classes of `twos_cover_tree`:
* class `0`: `(z₁−1, z₂+d)` is in the tile, `F(z − v)` is the closed form there;
* class `U`: `(z₁+d, z₂+2d−1)` is in the tile, and `F(z − v) = F(z − v + U)` (the kernel period is `0`);
* class `V`: `(z₁+1, z₂−d)` is in the tile, and `F(z − v) = F(z − v − V) + cV − t(z − v − V)` (the transverse period).
Here `d = 2k+4`, `z − v = (z₁ − 1, z₂ + 2k+3)`, `t` is the transverse grade `(2k+5) z₂ − (2k+3) z₁` and `cV = 1 − d² − 3d`. -/

namespace FLatticePaper.Induction
open Farey Construction

/-- The exceptional point `(−1, d)` is in the closed polygon of `2^(k+1)` (an odd site). -/
theorem twos_closed_exc1 (k : ℕ) :
    ((-1 : ℤ), 2 * (k : ℤ) + 4) ∈ (frameAt (List.replicate (k + 1) Digit.two)).closedPolygon := by
  obtain ⟨hn, hd⟩ := twos_child_num_den k
  have hT : (frameAt (List.replicate (k + 1) Digit.two)).child.periodDenominator =
      2 * ((2 * (k : ℤ) + 4) * (2 * (k : ℤ) + 4) + 2 * (2 * (k : ℤ) + 4) - 1) := by
    simp only [Fraction.periodDenominator, hn, hd]
    ring
  rw [ChildFrame.mem_closedPolygon_iff]
  simp only [ChildFrame.tGrade, ChildFrame.sGrade, hn, hd, hT, EvenSite]
  right
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- The exceptional point `(d+1, 2d−2)` is in the closed polygon of `2^(k+1)` (an even site). -/
theorem twos_closed_exc2 (k : ℕ) :
    (2 * (k : ℤ) + 5, 4 * (k : ℤ) + 6) ∈ (frameAt (List.replicate (k + 1) Digit.two)).closedPolygon := by
  obtain ⟨hn, hd⟩ := twos_child_num_den k
  have hT : (frameAt (List.replicate (k + 1) Digit.two)).child.periodDenominator =
      2 * ((2 * (k : ℤ) + 4) * (2 * (k : ℤ) + 4) + 2 * (2 * (k : ℤ) + 4) - 1) := by
    simp only [Fraction.periodDenominator, hn, hd]
    ring
  rw [ChildFrame.mem_closedPolygon_iff]
  simp only [ChildFrame.tGrade, ChildFrame.sGrade, hn, hd, hT, EvenSite]
  right
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- The closed form at a `TwosKey` point of the closed polygon. The two exceptional points `(−1, d)` and `(d+1, 2d−2)` lie
outside the tile at `(z₁, z₂+1)`; there the closed form still holds by closed-polygon membership. -/
theorem twos_F_E (k : ℕ) {z1 z2 : ℤ} (hk : TwosKey (2 * (k : ℤ) + 4) z1 z2) :
    standardField (List.replicate (k + 1) Digit.two) (z1, z2) =
      paperNearLadderValue (2 * (k : ℤ) + 4) (z1, z2 + 1) := by
  by_cases hexc : (z1 = -1 ∧ z2 = 2 * (k : ℤ) + 4) ∨ (z1 = 2 * (k : ℤ) + 5 ∧ z2 = 4 * (k : ℤ) + 6)
  · have hmem : ((z1, z2) : Site) ∈ (frameAt (List.replicate (k + 1) Digit.two)).closedPolygon := by
      rcases hexc with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · subst h1 h2
        exact twos_closed_exc1 k
      · subst h1 h2
        exact twos_closed_exc2 k
    exact standardField_twos_eq_paperNear k hmem
  · have ht : (z1, z2 + 1) ∈ paperNearLadderTile (2 * (k : ℤ) + 4) := by
      unfold TwosKey at hk
      simp only [paperNearLadderTile, paperNearLadderA, paperNearLadderB, paperNearLadderC, paperNearLadderD,
        Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq,
        Prod.mk.injEq, not_or]
      omega
    exact standardField_twos_eq_tile k rfl ht


/-- **The price in class `0`.** `F(z − v)` is the closed form at `(z₁−1, z₂+2k+4)`. -/
theorem twos_price_class0 (k : ℕ) {z1 z2 : ℤ} (hk : TwosKey (2 * (k : ℤ) + 4) z1 z2)
    (h0 : (z1 - 1, z2 + (2 * (k : ℤ) + 3) + 1) ∈ paperNearLadderTile (2 * (k : ℤ) + 4)) :
    (frameAt (List.replicate (k + 1) Digit.two)).price
        (standardField (List.replicate (k + 1) Digit.two)) (z1, z2) =
      paperNearLadderValue (2 * (k : ℤ) + 4) (z1, z2 + 1) -
        paperNearLadderValue (2 * (k : ℤ) + 4) (z1 - 1, z2 + (2 * (k : ℤ) + 3) + 1) +
        (((k : ℤ) + 1) * z1 - ((k : ℤ) + 2) * z2) := by
  have e := twos_price_unfold k (z1, z2)
  have hF := standardField_twos_eq_tile k (w := (z1 - 1, z2 + (2 * (k : ℤ) + 3))) rfl h0
  rw [twos_F_E k hk] at e
  simp only at e
  rw [hF] at e
  exact e

/-- **The price in class `U`.** `F(z − v) = F(z − v + U)` by the kernel period, and `z − v + U + (0,1) = (z₁+d, z₂+2d−1)`. -/
theorem twos_price_classU (k : ℕ) {z1 z2 : ℤ} (hk : TwosKey (2 * (k : ℤ) + 4) z1 z2)
    (hU : (z1 + (2 * (k : ℤ) + 4), z2 + 2 * (2 * (k : ℤ) + 4) - 1) ∈ paperNearLadderTile (2 * (k : ℤ) + 4)) :
    (frameAt (List.replicate (k + 1) Digit.two)).price
        (standardField (List.replicate (k + 1) Digit.two)) (z1, z2) =
      paperNearLadderValue (2 * (k : ℤ) + 4) (z1, z2 + 1) -
        paperNearLadderValue (2 * (k : ℤ) + 4) (z1 + (2 * (k : ℤ) + 4), z2 + 2 * (2 * (k : ℤ) + 4) - 1) +
        (((k : ℤ) + 1) * z1 - ((k : ℤ) + 2) * z2) := by
  have e := twos_price_unfold k (z1, z2)
  have hP := twos_standardField_hasPeriods k
  have hK := period_kernel_apply hP (z1 - 1, z2 + (2 * (k : ℤ) + 3))
  rw [twos_kernel_explicit] at hK
  simp only [Prod.mk_add_mk] at hK
  have hU' : (z1 - 1 + (2 * (k : ℤ) + 5), z2 + (2 * (k : ℤ) + 3) + (2 * (k : ℤ) + 3) + 1) =
      (z1 + (2 * (k : ℤ) + 4), z2 + 2 * (2 * (k : ℤ) + 4) - 1) := by
    ext <;> simp only <;> ring
  have hF' := standardField_twos_eq_tile k (w := (z1 - 1 + (2 * (k : ℤ) + 5), z2 + (2 * (k : ℤ) + 3) + (2 * (k : ℤ) + 3)))
    rfl (by rw [hU']; exact hU)
  rw [hU'] at hF'
  rw [twos_F_E k hk] at e
  simp only at e
  rw [← hK, hF'] at e
  exact e

/-- **The price in class `V`.** `F(z − v) = F(z − v − V) + cV − t(z − v − V)` by the transverse period, with
`z − v − V + (0,1) = (z₁+1, z₂−d)`, `cV = 1 − d² − 3d` and `t(x) = (2k+5) x₂ − (2k+3) x₁`. -/
theorem twos_price_classV (k : ℕ) {z1 z2 : ℤ} (hk : TwosKey (2 * (k : ℤ) + 4) z1 z2)
    (hV : (z1 + 1, z2 - (2 * (k : ℤ) + 4)) ∈ paperNearLadderTile (2 * (k : ℤ) + 4)) :
    (frameAt (List.replicate (k + 1) Digit.two)).price
        (standardField (List.replicate (k + 1) Digit.two)) (z1, z2) =
      paperNearLadderValue (2 * (k : ℤ) + 4) (z1, z2 + 1) -
        (paperNearLadderValue (2 * (k : ℤ) + 4) (z1 + 1, z2 - (2 * (k : ℤ) + 4)) +
          (1 - (2 * (k : ℤ) + 4) ^ 2 - 3 * (2 * (k : ℤ) + 4)) -
          ((2 * (k : ℤ) + 5) * (z2 - (2 * (k : ℤ) + 4) - 1) - (2 * (k : ℤ) + 3) * (z1 + 1))) +
        (((k : ℤ) + 1) * z1 - ((k : ℤ) + 2) * z2) := by
  have e := twos_price_unfold k (z1, z2)
  have hP := twos_standardField_hasPeriods k
  have hT := period_transverse_apply hP (z1 + 1, z2 - (2 * (k : ℤ) + 4) - 1)
  rw [twos_transverse_explicit, twos_transverseGrade_explicit, ladderEvenConstantV_eq] at hT
  simp only [Prod.mk_add_mk] at hT
  have hT' : (z1 + 1 + -2, z2 - (2 * (k : ℤ) + 4) - 1 + (4 * (k : ℤ) + 8)) = (z1 - 1, z2 + (2 * (k : ℤ) + 3)) := by
    ext <;> simp only <;> ring
  rw [hT'] at hT
  have hV' := standardField_twos_eq_tile k (w := (z1 + 1, z2 - (2 * (k : ℤ) + 4) - 1))
    (x := (z1 + 1, z2 - (2 * (k : ℤ) + 4))) (Prod.ext rfl (by dsimp only; ring)) hV
  rw [twos_F_E k hk] at e
  simp only at e
  rw [hT, hV'] at e
  linarith

end FLatticePaper.Induction
