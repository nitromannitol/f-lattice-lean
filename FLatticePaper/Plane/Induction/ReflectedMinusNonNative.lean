import FLatticePaper.Plane.Induction.QRankPlusDeck
import FLatticePaper.Plane.Induction.ReflectedRankPlus

/-!
# The four non-native triples of the sign-(-1) reflected rank (task 118, W1 base; eta = -1, part two)

For `eta = -1` a retained edge from a native centre with a non-native target is one of four cases (see
`ReflectedMinusFull.minus_white_cases`): the special even centre `(2-d, d)` with `e = (-1, 0)` (`minus_tri_A`); the even
centre `(d, 1)` with `e = (1, 0)` (`minus_tri_B`); an odd centre on the top row, `e = (0, 1)` (`minus_tri_C`); an odd
centre on the anti-diagonal `x + y = d + 2`, `e = (0, 1)` (`minus_tri_D`). In each case the reflected target is written as
`n + iU + jV` with `n` native (`R0minus_val`), and the comparison reduces to the explicit values of `qRankP` at native
points, from `qRankP_fam` and `omega`. Each triple decreases `R0minus` by a margin of at least one.
-/

namespace FLatticePaper.ReflectedMinusNonNative

open FLatticePaper.PureRank FLatticePaper.EPolicy FLatticePaper.ReflectedRankPlus FLatticePaper.QRankPlusDeck
  FLatticePaper.Construction

theorem nativeP_box_mk (d x y : ℤ) (h1 : 2 - d ≤ x) (h2 : x ≤ d) (h3 : 0 ≤ y) (h4 : y ≤ d + 1)
    (h5 : 1 ≤ x + y) (h6 : x + y ≤ d + 2) : NativeP d (x, y) :=
  Or.inl ⟨h1, h2, h3, h4, h5, h6⟩

/-- `R0minus` at `(a, b)` in the form `n + iU + jV`, with `n` native. -/
theorem R0minus_val (d : ℤ) (hd3 : 3 ≤ d) (hdodd : d % 2 = 1) (hden : BaseMask.stairEven.Valid d)
    (a b n1 n2 i j : ℤ) (hn : NativeP d (n1, n2)) (h1 : 2 - a = n1 + i * d + j * (1 - d))
    (h2 : d + 1 - b = n2 + i + j * (d + 1)) :
    R0minus d hdodd hden (a, b) = qRankP d (n1, n2) + 2 * d * i + 2 * (d + 1) * j := by
  unfold R0minus
  exact QdeckP_eq d hd3 hdodd hden _ ((n1, n2), i, j) ⟨hn, h1, h2⟩

/-- `R0minus` at a point whose reflection is native. -/
theorem R0minus_native_eq (d : ℤ) (hd3 : 3 ≤ d) (hdodd : d % 2 = 1) (hden : BaseMask.stairEven.Valid d)
    (a b : ℤ) (hz : NativeP d (2 - a, d + 1 - b)) :
    R0minus d hdodd hden (a, b) = qRankP d (2 - a, d + 1 - b) := by
  unfold R0minus
  exact QdeckP_native d hd3 hdodd hden _ hz

set_option maxHeartbeats 400000 in
theorem minus_tri_A (d : ℤ) (hd3 : 3 ≤ d) (hdodd : d % 2 = 1) (hden : BaseMask.stairEven.Valid d) :
    R0minus d hdodd hden (2 - d + -1, d + 0) < R0minus d hdodd hden (2 - d, d) := by
  have h10 : NativeP d (1, 0) :=
    nativeP_box_mk d 1 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hN2 : NativeP d (2 - (2 - d), d + 1 - d) :=
    nativeP_box_mk d _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hv1 : qRankP d (1, 0) = -1 := by
    rcases qRankP_fam d 1 0 hd3 hdodd h10 with h | h | h | h | h | h | h | h | h <;> omega
  have hv2 : qRankP d (2 - (2 - d), d + 1 - d) = 2 * d := by
    rcases qRankP_fam d (2 - (2 - d)) (d + 1 - d) hd3 hdodd hN2 with h | h | h | h | h | h | h | h | h <;> omega
  rw [R0minus_val d hd3 hdodd hden (2 - d + -1) (d + 0) 1 0 1 0 h10 (by ring) (by ring),
    R0minus_native_eq d hd3 hdodd hden (2 - d) d hN2, hv1, hv2]
  omega

set_option maxHeartbeats 400000 in
theorem minus_tri_B (d : ℤ) (hd3 : 3 ≤ d) (hdodd : d % 2 = 1) (hden : BaseMask.stairEven.Valid d) :
    R0minus d hdodd hden (d + 1, 1 + 0) < R0minus d hdodd hden (d, 1) := by
  have h1 : NativeP d (1, d + 1) :=
    nativeP_box_mk d 1 (d + 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hN2 : NativeP d (2 - d, d + 1 - 1) :=
    nativeP_box_mk d _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hv1 : qRankP d (1, d + 1) = 4 * d - 1 := by
    rcases qRankP_fam d 1 (d + 1) hd3 hdodd h1 with h | h | h | h | h | h | h | h | h <;> omega
  have hv2 : qRankP d (2 - d, d + 1 - 1) = 2 * d := by
    rcases qRankP_fam d (2 - d) (d + 1 - 1) hd3 hdodd hN2 with h | h | h | h | h | h | h | h | h <;> omega
  rw [R0minus_val d hd3 hdodd hden (d + 1) (1 + 0) 1 (d + 1) (-1) 0 h1 (by ring) (by ring),
    R0minus_native_eq d hd3 hdodd hden d 1 hN2, hv1, hv2]
  omega

set_option maxHeartbeats 400000 in
theorem minus_tri_C (d : ℤ) (hd3 : 3 ≤ d) (hdodd : d % 2 = 1) (hden : BaseMask.stairEven.Valid d)
    (y1 : ℤ) (hy1 : 2 - d ≤ y1) (hy2 : y1 ≤ 1) (hodd : (y1 + (d + 1)) % 2 = 1) :
    R0minus d hdodd hden (y1 + 0, d + 1 + 1) < R0minus d hdodd hden (y1, d + 1) := by
  have hn : NativeP d (3 - y1 - d, d) :=
    nativeP_box_mk d _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hs : NativeP d (2 - y1, d + 1 - (d + 1)) :=
    nativeP_box_mk d _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hv1 : qRankP d (3 - y1 - d, d) = 2 - 2 * y1 + 2 * d := by
    rcases qRankP_fam d (3 - y1 - d) d hd3 hdodd hn with h | h | h | h | h | h | h | h | h <;> omega
  have hv2 : qRankP d (2 - y1, d + 1 - (d + 1)) = 1 - 2 * y1 := by
    rcases qRankP_fam d (2 - y1) (d + 1 - (d + 1)) hd3 hdodd hs with h | h | h | h | h | h | h | h | h <;> omega
  rw [R0minus_val d hd3 hdodd hden (y1 + 0) (d + 1 + 1) (3 - y1 - d) d 0 (-1) hn (by ring) (by ring),
    R0minus_native_eq d hd3 hdodd hden y1 (d + 1) hs, hv1, hv2]
  omega

set_option maxHeartbeats 400000 in
theorem minus_tri_D (d : ℤ) (hd3 : 3 ≤ d) (hdodd : d % 2 = 1) (hden : BaseMask.stairEven.Valid d)
    (y1 y2 : ℤ) (hs : y1 + y2 = d + 2) (h2 : 2 ≤ y1) (h3 : y1 ≤ d) :
    R0minus d hdodd hden (y1 + 0, y2 + 1) < R0minus d hdodd hden (y1, y2) := by
  have hn : NativeP d (d + 2 - y1, y1 - 1) :=
    nativeP_box_mk d _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hsN : NativeP d (2 - y1, d + 1 - y2) :=
    nativeP_box_mk d _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hv1 : qRankP d (d + 2 - y1, y1 - 1) = 2 * d - 4 + 2 * y1 := by
    rcases qRankP_fam d (d + 2 - y1) (y1 - 1) hd3 hdodd hn with h | h | h | h | h | h | h | h | h <;> omega
  have hv2 : qRankP d (2 - y1, d + 1 - y2) = 2 * y1 - 3 := by
    rcases qRankP_fam d (2 - y1) (d + 1 - y2) hd3 hdodd hsN with h | h | h | h | h | h | h | h | h <;> omega
  rw [R0minus_val d hd3 hdodd hden (y1 + 0) (y2 + 1) (d + 2 - y1) (y1 - 1) (-1) 0 hn (by ring) (by linarith),
    R0minus_native_eq d hd3 hdodd hden y1 y2 hsN, hv1, hv2]
  omega

end FLatticePaper.ReflectedMinusNonNative
