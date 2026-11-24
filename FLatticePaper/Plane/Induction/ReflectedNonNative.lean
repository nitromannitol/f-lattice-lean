import FLatticePaper.Plane.Induction.ReflectedEdges
import FLatticePaper.Plane.Induction.QRankDeck

/-!
# Strictness of the reflected rank at the non-native targets: the five families (task 118, W1 base; bridge iv, part four)

For a native centre `y` with a policy edge `y → y + e` (`η = +1`, white centre) whose target is not native, the edge is one of
five cases (the classification `white_cases` is not yet proved). Each case has an explicit native decomposition of the reflected
target, and the strict inequality is a comparison of explicit values of `qRank` (`qRank_fam`):

* `tri_T4`: `y = (d,1)`, `e = (1,0)` (target `(d+1,1)`);
* `tri_T5`: `y = (2,d+1)`, `e = (1,0)` (target `(3,d+1)`);
* `tri_T2`: `y = (1,0)`, `e = (0,-1)` (target `(1,-1)`);
* `tri_T1`: `y` on the V-path (`y1 + y2 = 1`, `2 - d ≤ y1 ≤ 0`), `e = (0,-1)` (target on the line `x + y = 0`);
* `tri_T3`: `y` odd on the top row, `y1 ≠ 2 - d, 2`, `e = (0,1)` (target on the line `y = d+2`).
-/

namespace FLatticePaper.ReflectedNonNative

open FLatticePaper FLatticePaper.Induction FLatticePaper.PureRank FLatticePaper.EPolicy FLatticePaper.ReflectedRank FLatticePaper.QRankDeck FLatticePaper.ReflectedEdges FLatticePaper.ReflectWitness FLatticePaper.Construction

set_option maxHeartbeats 400000 in
theorem tri_T2 (d : ℤ) (hd3 : 3 ≤ d) (hdodd : d % 2 = 1) (hden : BaseMask.stairEven.Valid d) :
    R0plus d hdodd hden (1 + 0, 0 + (-1)) < R0plus d hdodd hden (1, 0) := by
  have hn : NativeP d (d, 1) := by unfold NativeP; simp only [Prod.mk.injEq]; omega
  have hn2 : NativeP d (1, d + 1) := by unfold NativeP; simp only [Prod.mk.injEq]; omega
  unfold R0plus
  dsimp only
  have hq1 := Qdeck_eq d hd3 hdodd hden (2 - (1 + 0), d + 1 - (0 + -1)) ((d, 1), 0, 1)
    ⟨hn, by simp only; ring, by simp only; ring⟩
  have hq2 := Qdeck_native d hd3 hdodd hden (2 - 1, d + 1 - 0) (by unfold NativeP; simp only [Prod.mk.injEq]; omega)
  rw [hq1, hq2]
  have f1 := qRank_fam d d 1 hd3 hdodd hn
  have f2 := qRank_fam d 1 (d + 1) hd3 hdodd hn2
  have v1 : qRank d (d, 1) = 2 * d := by
    rcases f1 with h|h|h|h|h|h|h|h|h <;> omega
  have v2 : qRank d (1, d + 1) = 2 * (1 + d - 1) + (1 + d - 1 + 0) % 2 - 2 * (d + 1) := by
    rcases f2 with h|h|h|h|h|h|h|h|h <;> omega
  have e1 : (2 : ℤ) - 1 = 1 := by norm_num
  have e2 : d + 1 - (0 : ℤ) = d + 1 := by ring
  dsimp only
  rw [e1, e2, v1, v2]
  omega

set_option maxHeartbeats 400000 in
theorem tri_T4 (d : ℤ) (hd3 : 3 ≤ d) (hdodd : d % 2 = 1) (hden : BaseMask.stairEven.Valid d) :
    R0plus d hdodd hden (d + 1, 1 + 0) < R0plus d hdodd hden (d, 1) := by
  have hn : NativeP d (1, d + 1) := by unfold NativeP; simp only [Prod.mk.injEq]; omega
  have hs : NativeP d (2 - d, d + 1 - 1) := by unfold NativeP; simp only [Prod.mk.injEq]; omega
  unfold R0plus
  dsimp only
  have hq1 := Qdeck_eq d hd3 hdodd hden (2 - (d + 1), d + 1 - (1 + 0)) ((1, d + 1), -1, 0)
    ⟨hn, by simp only; ring, by simp only; ring⟩
  have hq2 := Qdeck_native d hd3 hdodd hden (2 - d, d + 1 - 1) hs
  rw [hq1, hq2]
  have f1 := qRank_fam d 1 (d + 1) hd3 hdodd hn
  have f2 := qRank_fam d (2 - d) (d + 1 - 1) hd3 hdodd hs
  have v1 : qRank d (1, d + 1) = 2 * (1 + d - 1) + (1 + d - 1 + 0) % 2 - 2 * (d + 1) := by
    rcases f1 with h|h|h|h|h|h|h|h|h <;> omega
  have v2 : qRank d (2 - d, d + 1 - 1) = -2 * (d + 1 - 1) - (2 - d + (d + 1 - 1)) % 2 := by
    rcases f2 with h|h|h|h|h|h|h|h|h <;> omega
  rw [v1, v2]
  dsimp only
  omega

set_option maxHeartbeats 400000 in
theorem tri_T5 (d : ℤ) (hd3 : 3 ≤ d) (hdodd : d % 2 = 1) (hden : BaseMask.stairEven.Valid d) :
    R0plus d hdodd hden (2 + 1, d + 1 + 0) < R0plus d hdodd hden (2, d + 1) := by
  have hn : NativeP d (d - 1, 1) := by unfold NativeP; simp only [Prod.mk.injEq]; omega
  have hs : NativeP d (2 - 2, d + 1 - (d + 1)) := by unfold NativeP; simp only [Prod.mk.injEq]; omega
  unfold R0plus
  dsimp only
  have hq1 := Qdeck_eq d hd3 hdodd hden (2 - (2 + 1), d + 1 - (d + 1 + 0)) ((d - 1, 1), -1, 0)
    ⟨hn, by simp only; ring, by simp only; ring⟩
  have hq2 := Qdeck_native d hd3 hdodd hden (2 - 2, d + 1 - (d + 1)) hs
  rw [hq1, hq2]
  have f1 := qRank_fam d (d - 1) 1 hd3 hdodd hn
  have f2 := qRank_fam d (2 - 2) (d + 1 - (d + 1)) hd3 hdodd hs
  have v1 : qRank d (d - 1, 1) = 2 * d - 1 := by
    rcases f1 with h|h|h|h|h|h|h|h|h <;> omega
  have v2 : qRank d (2 - 2, d + 1 - (d + 1)) = 0 := by
    rcases f2 with h|h|h|h|h|h|h|h|h <;> omega
  rw [v1, v2]
  dsimp only
  omega

set_option maxHeartbeats 400000 in
theorem tri_T1 (d : ℤ) (hd3 : 3 ≤ d) (hdodd : d % 2 = 1) (hden : BaseMask.stairEven.Valid d) (y1 y2 : ℤ)
    (hyN : NativeP d (y1, y2)) (hA : (2 - y1) + (d + 1 - y2) = d + 2) (hA2 : 2 ≤ 2 - y1) (hA3 : 2 - y1 ≤ d) :
    R0plus d hdodd hden (y1 + 0, y2 + (-1)) < R0plus d hdodd hden (y1, y2) := by
  have hs : NativeP d (2 - y1, d + 1 - y2) := (nativeP_refl d y1 y2).mpr hyN
  have hn : NativeP d (2 - y1 - d, d + 1 - y2) := by unfold NativeP; dsimp only; simp only [Prod.mk.injEq]; omega
  unfold R0plus
  dsimp only
  have hq1 := Qdeck_eq d hd3 hdodd hden (2 - (y1 + 0), d + 1 - (y2 + -1)) ((2 - y1 - d, d + 1 - y2), 1, 0)
    ⟨hn, by simp only; ring, by simp only; ring⟩
  have hq2 := Qdeck_native d hd3 hdodd hden (2 - y1, d + 1 - y2) hs
  rw [hq1, hq2]
  have fn := qRank_fam d (2 - y1 - d) (d + 1 - y2) hd3 hdodd hn
  have fs := qRank_fam d (2 - y1) (d + 1 - y2) hd3 hdodd hs
  have vs : qRank d (2 - y1, d + 1 - y2) = 2 * d - 2 * (d + 1 - y2) + 1 := by
    rcases fs with h|h|h|h|h|h|h|h|h <;> omega
  rw [vs]
  dsimp only
  rcases fn with h|h|h|h|h|h|h|h|h <;> omega

set_option maxHeartbeats 400000 in
set_option maxHeartbeats 400000 in
theorem top_val (d : ℤ) (hd3 : 3 ≤ d) (hdodd : d % 2 = 1) (y1 : ℤ)
    (hyN : NativeP d (y1, d + 1)) (hodd : (y1 + (d + 1)) % 2 = 1) (_hne : y1 ≠ 2 - d) (_hne2 : y1 ≠ 2) :
    qRank d (2 - y1, d + 1 - (d + 1)) = 2 * (2 - y1) + (2 - y1 + (d + 1 - (d + 1))) % 2 := by
  have hs : NativeP d (2 - y1, d + 1 - (d + 1)) := (nativeP_refl d y1 (d + 1)).mpr hyN
  have fs := qRank_fam d (2 - y1) (d + 1 - (d + 1)) hd3 hdodd hs
  have hyB := hyN
  unfold NativeP at hyB
  dsimp only at hyB
  simp only [Prod.mk.injEq] at hyB
  clear hs hyN
  rcases fs with g|g|g|g|g|g|g|g|g <;> omega

set_option maxHeartbeats 400000 in
theorem top_nat (d : ℤ) (hd3 : 3 ≤ d) (y1 : ℤ)
    (hyN : NativeP d (y1, d + 1)) (hne2 : y1 ≠ 2) : NativeP d (3 - y1 - d, d) := by
  have hyB := hyN
  unfold NativeP at hyB
  dsimp only at hyB
  simp only [Prod.mk.injEq] at hyB
  unfold NativeP
  dsimp only
  simp only [Prod.mk.injEq]
  omega

set_option maxHeartbeats 400000 in
theorem tri_T3 (d : ℤ) (hd3 : 3 ≤ d) (hdodd : d % 2 = 1) (hden : BaseMask.stairEven.Valid d) (y1 : ℤ)
    (hyN : NativeP d (y1, d + 1)) (hodd : (y1 + (d + 1)) % 2 = 1) (hne : y1 ≠ 2 - d) (hne2 : y1 ≠ 2) :
    R0plus d hdodd hden (y1 + 0, d + 1 + 1) < R0plus d hdodd hden (y1, d + 1) := by
  have hn := top_nat d hd3 y1 hyN hne2
  have hs : NativeP d (2 - y1, d + 1 - (d + 1)) := (nativeP_refl d y1 (d + 1)).mpr hyN
  have vs := top_val d hd3 hdodd y1 hyN hodd hne hne2
  unfold R0plus
  dsimp only
  have hq1 := Qdeck_eq d hd3 hdodd hden (2 - (y1 + 0), d + 1 - (d + 1 + 1)) ((3 - y1 - d, d), 0, -1)
    ⟨hn, by simp only; ring, by simp only; ring⟩
  have hq2 := Qdeck_native d hd3 hdodd hden (2 - y1, d + 1 - (d + 1)) hs
  rw [hq1, hq2, vs]
  have fn := qRank_fam d (3 - y1 - d) d hd3 hdodd hn
  have hyB := hyN
  unfold NativeP at hyB
  dsimp only at hyB
  simp only [Prod.mk.injEq] at hyB
  dsimp only
  rcases fn with h|h|h|h|h|h|h|h|h <;> omega

end FLatticePaper.ReflectedNonNative
