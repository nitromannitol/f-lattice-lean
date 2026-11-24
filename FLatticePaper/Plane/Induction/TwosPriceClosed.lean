import FLatticePaper.Plane.Induction.TwosPriceForm

/-! Task 118, base inputs at `2^(k+1)`: the closed forms of the twos price on the three shift classes, with the quadratic
terms of the near-one height cancelled by `sq_div4_add`. The closed forms are linear in `z` up to bounded pieces (`min`,
`max`, and the indicator of `A ∪ B`), which `omega` reads directly.

With `d = 2k+4`, `u = z₂ − z₁`, `ι(x) = 1_{A∪B}(x)`:
* class `0`:  `P z = (k²+5k+6) − z₁ + M₀ + ι(z₁, z₂+1) − ι(z₁−1, z₂+d)`;
* class `U`:  `P z = (k²+3k+2) − z₂ + M_U + ι(z₁, z₂+1) − ι(z₁+d, z₂+2d−1)`;
* class `V`:  `P z = (k²+5k+5) + z₁ + M_V + ι(z₁, z₂+1) − ι(z₁+1, z₂−d)`,
where the bounded parts are the `min`/`max` pieces of the two heights. -/

namespace FLatticePaper.Induction
open Farey Construction

/-- The indicator of `A ∪ B` of the near-one tile, as an integer. -/
noncomputable def twosInd (d : ℤ) (x : Site) : ℤ := (paperNearLadderA d ∪ paperNearLadderB d).indicator (fun _ => (1 : ℤ)) x

/-- Membership in `A ∪ B` as explicit linear conditions. -/
theorem twos_mem_AB_iff (d x1 x2 : ℤ) :
    ((x1, x2) ∈ paperNearLadderA d ∪ paperNearLadderB d) ↔
      ((x1 = -1 ∧ x2 = 2 * d + 1) ∨ (x1 = d + 1 ∧ x2 = d - 1) ∨ (x2 - x1 = d ∧ 0 < x1 ∧ x1 < d)) := by
  unfold paperNearLadderA paperNearLadderB
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
  constructor
  · rintro ((h | h) | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

/-- The indicator as a disjunction, for `omega`. -/
theorem twosInd_spec (d x1 x2 : ℤ) :
    (twosInd d (x1, x2) = 1 ∧ ((x1 = -1 ∧ x2 = 2 * d + 1) ∨ (x1 = d + 1 ∧ x2 = d - 1) ∨
        (x2 - x1 = d ∧ 0 < x1 ∧ x1 < d))) ∨
      (twosInd d (x1, x2) = 0 ∧ ¬ ((x1 = -1 ∧ x2 = 2 * d + 1) ∨ (x1 = d + 1 ∧ x2 = d - 1) ∨
        (x2 - x1 = d ∧ 0 < x1 ∧ x1 < d))) := by
  unfold twosInd
  by_cases hm : (x1, x2) ∈ paperNearLadderA d ∪ paperNearLadderB d
  · left
    exact ⟨by rw [Set.indicator_of_mem hm], (twos_mem_AB_iff d x1 x2).mp hm⟩
  · right
    exact ⟨by rw [Set.indicator_of_notMem hm], fun h => hm ((twos_mem_AB_iff d x1 x2).mpr h)⟩

/-- The near-one height as explicit pieces (definitional). -/
theorem twos_H_pieces (d : ℤ) (x : Site) :
    paperNearLadderValue d x = -((x.2 - x.1) ^ 2 / 4) + min 0 (d - x.2) + min 0 (2 * d - x.2) +
      max ((x.2 - x.1) - d) 0 + twosInd d x := rfl

/-- **The closed form of the price in class `0`.** -/
theorem twos_price_closed0 (k : ℕ) {z1 z2 : ℤ} (hk : TwosKey (2 * (k : ℤ) + 4) z1 z2)
    (h0 : (z1 - 1, z2 + (2 * (k : ℤ) + 3) + 1) ∈ paperNearLadderTile (2 * (k : ℤ) + 4)) :
    (frameAt (List.replicate (k + 1) Digit.two)).price
        (standardField (List.replicate (k + 1) Digit.two)) (z1, z2) =
      ((k : ℤ) ^ 2 + 5 * (k : ℤ) + 6) - z1 +
        (min 0 (2 * (k : ℤ) + 4 - (z2 + 1)) + min 0 (2 * (2 * (k : ℤ) + 4) - (z2 + 1)) -
          min 0 (-z2) - min 0 (2 * (k : ℤ) + 4 - z2) +
          max (z2 + 1 - z1 - (2 * (k : ℤ) + 4)) 0 - max (z2 + 1 - z1) 0) +
        (twosInd (2 * (k : ℤ) + 4) (z1, z2 + 1) - twosInd (2 * (k : ℤ) + 4) (z1 - 1, z2 + (2 * (k : ℤ) + 4))) := by
  rw [twos_price_class0 k hk h0, twos_H_pieces, twos_H_pieces]
  have q1 : (z2 + (2 * (k : ℤ) + 3) + 1 - (z1 - 1)) ^ 2 / 4 =
      (z2 + 1 - z1) ^ 2 / 4 + (z2 + 1 - z1) * ((k : ℤ) + 2) + ((k : ℤ) + 2) ^ 2 := by
    rw [show z2 + (2 * (k : ℤ) + 3) + 1 - (z1 - 1) = (z2 + 1 - z1) + 2 * ((k : ℤ) + 2) by ring]
    exact sq_div4_add _ _
  dsimp only
  rw [q1, show 2 * (k : ℤ) + 4 - (z2 + (2 * (k : ℤ) + 3) + 1) = -z2 by ring,
    show 2 * (2 * (k : ℤ) + 4) - (z2 + (2 * (k : ℤ) + 3) + 1) = 2 * (k : ℤ) + 4 - z2 by ring,
    show z2 + (2 * (k : ℤ) + 3) + 1 - (z1 - 1) - (2 * (k : ℤ) + 4) = z2 + 1 - z1 by ring]
  ring

/-- **The closed form of the price in class `U`.** -/
theorem twos_price_closedU (k : ℕ) {z1 z2 : ℤ} (hk : TwosKey (2 * (k : ℤ) + 4) z1 z2)
    (hU : (z1 + (2 * (k : ℤ) + 4), z2 + 2 * (2 * (k : ℤ) + 4) - 1) ∈ paperNearLadderTile (2 * (k : ℤ) + 4)) :
    (frameAt (List.replicate (k + 1) Digit.two)).price
        (standardField (List.replicate (k + 1) Digit.two)) (z1, z2) =
      ((k : ℤ) ^ 2 + 3 * (k : ℤ) + 2) - z2 +
        (min 0 (2 * (k : ℤ) + 4 - (z2 + 1)) + min 0 (2 * (2 * (k : ℤ) + 4) - (z2 + 1)) +
          max (z2 + 1 - z1 - (2 * (k : ℤ) + 4)) 0 -
          min 0 (1 - (2 * (k : ℤ) + 4) - z2) - min 0 (1 - z2) - max (z2 - z1 - 1) 0) +
        (twosInd (2 * (k : ℤ) + 4) (z1, z2 + 1) -
          twosInd (2 * (k : ℤ) + 4) (z1 + (2 * (k : ℤ) + 4), z2 + 2 * (2 * (k : ℤ) + 4) - 1)) := by
  rw [twos_price_classU k hk hU, twos_H_pieces, twos_H_pieces]
  have q1 : (z2 + 2 * (2 * (k : ℤ) + 4) - 1 - (z1 + (2 * (k : ℤ) + 4))) ^ 2 / 4 =
      (z2 + 1 - z1) ^ 2 / 4 + (z2 + 1 - z1) * ((k : ℤ) + 1) + ((k : ℤ) + 1) ^ 2 := by
    rw [show z2 + 2 * (2 * (k : ℤ) + 4) - 1 - (z1 + (2 * (k : ℤ) + 4)) = (z2 + 1 - z1) + 2 * ((k : ℤ) + 1) by ring]
    exact sq_div4_add _ _
  dsimp only
  rw [q1, show 2 * (k : ℤ) + 4 - (z2 + 1) = 2 * (k : ℤ) + 4 - (z2 + 1) from rfl,
    show 2 * (k : ℤ) + 4 - (z2 + 2 * (2 * (k : ℤ) + 4) - 1) = 1 - (2 * (k : ℤ) + 4) - z2 by ring,
    show 2 * (2 * (k : ℤ) + 4) - (z2 + 2 * (2 * (k : ℤ) + 4) - 1) = 1 - z2 by ring,
    show z2 + 2 * (2 * (k : ℤ) + 4) - 1 - (z1 + (2 * (k : ℤ) + 4)) - (2 * (k : ℤ) + 4) = z2 - z1 - 1 by ring]
  ring

/-- **The closed form of the price in class `V`.** -/
theorem twos_price_closedV (k : ℕ) {z1 z2 : ℤ} (hk : TwosKey (2 * (k : ℤ) + 4) z1 z2)
    (hV : (z1 + 1, z2 - (2 * (k : ℤ) + 4)) ∈ paperNearLadderTile (2 * (k : ℤ) + 4)) :
    (frameAt (List.replicate (k + 1) Digit.two)).price
        (standardField (List.replicate (k + 1) Digit.two)) (z1, z2) =
      ((k : ℤ) ^ 2 + 5 * (k : ℤ) + 5) + z1 +
        ((min 0 (2 * (k : ℤ) + 4 - (z2 + 1)) + min 0 (2 * (2 * (k : ℤ) + 4) - (z2 + 1)) -
          min 0 (2 * (2 * (k : ℤ) + 4) - z2) - min 0 (3 * (2 * (k : ℤ) + 4) - z2)) +
          (max (z2 + 1 - z1 - (2 * (k : ℤ) + 4)) 0 - max (z2 - z1 - 2 * (2 * (k : ℤ) + 4) - 1) 0)) +
        (twosInd (2 * (k : ℤ) + 4) (z1, z2 + 1) - twosInd (2 * (k : ℤ) + 4) (z1 + 1, z2 - (2 * (k : ℤ) + 4))) := by
  rw [twos_price_classV k hk hV, twos_H_pieces, twos_H_pieces]
  have q1V : (z2 - (2 * (k : ℤ) + 4) - (z1 + 1)) ^ 2 / 4 =
      (z2 + 1 - z1) ^ 2 / 4 - (z2 + 1 - z1) * ((k : ℤ) + 3) + ((k : ℤ) + 3) ^ 2 := by
    rw [show z2 - (2 * (k : ℤ) + 4) - (z1 + 1) = (z2 + 1 - z1) + 2 * (-((k : ℤ) + 3)) by ring]
    rw [sq_div4_add (z2 + 1 - z1) (-((k : ℤ) + 3))]
    ring
  dsimp only
  rw [q1V, show 2 * (k : ℤ) + 4 - (z2 - (2 * (k : ℤ) + 4)) = 2 * (2 * (k : ℤ) + 4) - z2 by ring,
    show 2 * (2 * (k : ℤ) + 4) - (z2 - (2 * (k : ℤ) + 4)) = 3 * (2 * (k : ℤ) + 4) - z2 by ring,
    show z2 - (2 * (k : ℤ) + 4) - (z1 + 1) - (2 * (k : ℤ) + 4) = z2 - z1 - 2 * (2 * (k : ℤ) + 4) - 1 by ring]
  ring

end FLatticePaper.Induction
