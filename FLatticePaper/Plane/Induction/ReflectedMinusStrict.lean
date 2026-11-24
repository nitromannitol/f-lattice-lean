import FLatticePaper.Plane.Induction.ReflectedRankPlus
import FLatticePaper.Plane.Induction.ReflectWitness
import FLatticePaper.Plane.Induction.ReflectedStrict

/-!
# Strictness of the reflected plus rank along the policy edges with native targets, eta = -1 (task 118, W1 base)

The sign-`-1` analogue of `ReflectedStrict`. For a native centre `y` and a `-1`-policy edge `y → y + e` with native target,
`R0minus` strictly decreases: `strict_native_minus` (the plus gate `qplus_gate` at the reflected source) with the retained
direction from `edge_white_minus` / `edge_black_minus`, and the values of `R0minus` at native points from `QdeckP_native`.
-/

namespace FLatticePaper.ReflectedMinusStrict

open FLatticePaper.PureRank FLatticePaper.EPolicy FLatticePaper.ReflectedRankPlus FLatticePaper.ReflectWitness
  FLatticePaper.ReflectedStrict FLatticePaper.Construction

set_option maxHeartbeats 400000 in
theorem R0minus_strict_native (d x y e1 e2 : ℤ) (hd3 : 3 ≤ d) (hdodd : d % 2 = 1)
    (hden : BaseMask.stairEven.Valid d) (hN : NativeP d (x, y))
    (hR : RetainedP d (2 - x) (d + 1 - y) (-e1) (-e2))
    (hunit : (-e1, -e2) = (1, 0) ∨ (-e1, -e2) = (-1, 0) ∨ (-e1, -e2) = (0, 1) ∨ (-e1, -e2) = (0, -1))
    (hT : NativeP d (2 - (x + e1), d + 1 - (y + e2))) :
    R0minus d hdodd hden (x + e1, y + e2) < R0minus d hdodd hden (x, y) := by
  have hs : NativeP d (2 - x, d + 1 - y) := (nativeP_refl d x y).mpr hN
  unfold R0minus
  dsimp only
  rw [QdeckP_native d hd3 hdodd hden _ hT, QdeckP_native d hd3 hdodd hden _ hs]
  exact strict_native_minus d x y e1 e2 hd3 hdodd hN hR hunit hT

set_option maxHeartbeats 400000 in
theorem R0minus_edge_white_minus (d x y e1 e2 : ℤ) (hd3 : 3 ≤ d) (hdodd : d % 2 = 1)
    (hden : BaseMask.stairEven.Valid d) (hN : NativeP d (x, y)) (hW : WhiteN d (x, y))
    (h : RetNat d (-1) False (x, y) ((x, y) + (e1, e2)))
    (hT : NativeP d (2 - (x + e1), d + 1 - (y + e2))) :
    R0minus d hdodd hden (x + e1, y + e2) < R0minus d hdodd hden (x, y) := by
  have he := (retNat_white_pt hd3 hdodd (Or.inr rfl) hN hW (e1, e2)).mp h
  have hR := edge_white_minus d x y e1 e2 hd3 hdodd hN hW h
  have hu : (e1, e2) = (1, 0) ∨ (e1, e2) = (-1, 0) ∨ (e1, e2) = (0, 1) ∨ (e1, e2) = (0, -1) := by
    rw [he]
    rcases selDisp_unit d (-1) (Or.inr rfl) (x, y) with h' | h' | h' | h' <;> simp [h']
  exact R0minus_strict_native d x y e1 e2 hd3 hdodd hden hN hR (neg_unit e1 e2 hu) hT

set_option maxHeartbeats 400000 in
theorem R0minus_edge_black_minus (d x y e1 e2 : ℤ) (hd3 : 3 ≤ d) (hdodd : d % 2 = 1)
    (hden : BaseMask.stairEven.Valid d) (hN : NativeP d (x, y)) (hB : ¬ WhiteN d (x, y))
    (h : RetNat d (-1) True (x, y) ((x, y) + (e1, e2)))
    (hT : NativeP d (2 - (x + e1), d + 1 - (y + e2))) :
    R0minus d hdodd hden (x + e1, y + e2) < R0minus d hdodd hden (x, y) :=
  R0minus_strict_native d x y e1 e2 hd3 hdodd hden hN (edge_black_minus d x y e1 e2 hd3 hdodd hN hB h)
    (neg_unit e1 e2 (black_unit d (-1) x y e1 e2 h)) hT

end FLatticePaper.ReflectedMinusStrict
