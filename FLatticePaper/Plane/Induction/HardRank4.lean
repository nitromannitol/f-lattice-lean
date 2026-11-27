import FLatticePaper.Plane.Induction.OddAxialRank
import FLatticePaper.Plane.Induction.H0Core

/-! # The rank-4 black north-east site cannot occur in the hard frames (d <= 3n)

For an odd free H point `z` with `2 ≤ z.1 < d`, the north-east site `q = z + (1,1)` is odd, and its inputs `q ± (0,1)` are even. Their
t-grades are `t(z) + n − 2d` and `t(z) + n`, which lie in the even zero window `[2 − (d+n), 2(d+n) − 2]` when `d ≤ 3n` (since
`t(z) ≥ n + 2`). If the field vanishes at both inputs, the laplacian of `q` is `−2 F(q)`, which is never `−1` over the integers. -/

namespace FLatticePaper.HardRank4

open FLatticePaper FLatticePaper.Induction

theorem no_black_NE (frame : ChildFrame) (F : Field)
    (hZ : ∀ w : Site, EvenSite w → 2 - (frame.child.den + frame.child.num) ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = 0)
    (hd3 : frame.child.den ≤ 3 * frame.child.num)
    {z : Site} (hz : z ∈ frame.freeH) (hodd : ¬ EvenSite z) (hx2 : 2 ≤ z.1) (hxd : z.1 < frame.child.den) :
    laplacian F (z.1 + 1, z.2 + 1) ≠ -1 := by
  have hrange := OddAxialRank.odd_t_range frame hz hodd hx2 hxd
  have hodd' : ¬ EvenSite (z.1 + 1, z.2 + 1) := by
    unfold EvenSite at hodd ⊢
    dsimp only
    omega
  have hn1 : incomingNeg (z.1 + 1, z.2 + 1) = (z.1 + 1, z.2) := by
    rw [H0Core.incomingNeg_of_not_even _ hodd']
    ext
    · rfl
    · ring
  have hp1 : incomingPos (z.1 + 1, z.2 + 1) = (z.1 + 1, z.2 + 2) := by
    rw [H0Core.incomingPos_of_not_even _ hodd']
    ext
    · rfl
    · ring
  have hev1 : EvenSite (z.1 + 1, z.2) := by
    unfold EvenSite at hodd ⊢
    dsimp only
    omega
  have hev2 : EvenSite (z.1 + 1, z.2 + 2) := by
    unfold EvenSite at hodd ⊢
    dsimp only
    omega
  have t1 : frame.tGrade (z.1 + 1, z.2) = frame.tGrade z + frame.child.num := by
    unfold ChildFrame.tGrade
    dsimp only
    ring
  have t2 : frame.tGrade (z.1 + 1, z.2 + 2) = frame.tGrade z + frame.child.num - 2 * frame.child.den := by
    unfold ChildFrame.tGrade
    dsimp only
    ring
  have F1 : F (z.1 + 1, z.2) = 0 := by
    apply hZ _ hev1
    · rw [t1]; omega
    · rw [t1]; omega
  have F2 : F (z.1 + 1, z.2 + 2) = 0 := by
    apply hZ _ hev2
    · rw [t2]; omega
    · rw [t2]; omega
  intro hlap
  unfold laplacian at hlap
  rw [hn1, hp1, F1, F2] at hlap
  omega

end FLatticePaper.HardRank4
