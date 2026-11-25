import FLatticePaper.Plane.Induction.TwosFlatReduce
import FLatticePaper.Plane.Induction.TwosPriceBand
import FLatticePaper.Plane.Induction.TwosSlipForm
import FLatticePaper.Plane.Induction.TwosPriceForm

/-! Task Q25 / twos flatness, step (i): the cover lemmas on the native points.

For a native point `p = (x, y)` with `TwosKey (x+1, y+1)`, one of the two closed forms of the slip (`slip_cover`) and one of the two
closed forms of the price (`price_cover`) applies. These are the region splits used by the closed form of the chain potential. -/

noncomputable section

namespace FLatticePaper.TwosEPolicy

open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey
open scoped Classical

/-- A point of `A ∪ B ∪ C` outside `D` is in the tile (the linear form of `paperNearLadderTile`). -/
theorem mem_tile_of (d u v : ℤ)
    (hC : (u = -1 ∧ v = 2 * d + 1) ∨ (u = d + 1 ∧ v = d - 1) ∨ (v - u = d ∧ 0 < u ∧ u < d) ∨
      (-1 ≤ u ∧ u ≤ d + 1 ∧ 1 ≤ v ∧ v ≤ 3 * d - 1 ∧ -1 ≤ v - u ∧ v - u ≤ 2 * d + 1))
    (hD : ¬ ((u = -1 ∧ v ≤ d + 1) ∨ (u = d + 1 ∧ 2 * d - 1 ≤ v))) :
    (u, v) ∈ paperNearLadderTile d :=
  (mem_pnTile_iff d u v).mpr ⟨hC, hD⟩

set_option maxHeartbeats 400000 in
/-- The slip has one of its two closed forms at a native point with `TwosKey (x+1, y+1)`. -/
theorem slip_cover (a x y : ℤ) (hN : NativeT a x y) (hk : TwosKey a (x + 1) (y + 1)) :
    (x + 1, y + 2) ∈ paperNearLadderTile a ∨ (x - a, y - a + 3) ∈ paperNearLadderTile a := by
  unfold NativeT at hN
  unfold TwosKey at hk
  by_cases hE : x = a + 1 ∨ y = 3 * a - 2 ∨ (x = a ∧ 2 * a - 3 ≤ y)
  · right
    apply mem_tile_of
    · right; right; right
      omega
    · omega
  · left
    apply mem_tile_of
    · right; right; right
      omega
    · omega

set_option maxHeartbeats 400000 in
/-- The price has one of its two closed forms at a native point with `TwosKey (x+1, y+1)`. -/
theorem price_cover (a x y : ℤ) (hN : NativeT a x y) (hk : TwosKey a (x + 1) (y + 1)) :
    (x, y + a + 1) ∈ paperNearLadderTile a ∨ (x + 2, y + 1 - a) ∈ paperNearLadderTile a := by
  unfold NativeT at hN
  unfold TwosKey at hk
  by_cases hR : y - x ≥ a + 1 ∨ 2 * a - 1 ≤ y
  · right
    apply mem_tile_of
    · right; right; right
      omega
    · omega
  · left
    apply mem_tile_of
    · right; right; right
      omega
    · omega

end FLatticePaper.TwosEPolicy
