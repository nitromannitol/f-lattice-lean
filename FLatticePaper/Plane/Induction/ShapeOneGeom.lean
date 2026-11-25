import FLatticePaper.Plane.Induction.AllBranchFan
import FLatticePaper.Plane.Induction.ShortRoute
import FLatticePaper.Plane.Induction.FreeTraceBox
import FLatticePaper.Plane.Induction.Binary

/-! # The geometry of shape 1: the chain points are contacts of the fan based at the odd H midpoint

For an odd free H midpoint `z` with `n + 2 ≤ t(z)` (the cone base condition) and `z ≠ hLast`, the free-root bounds give
`n + 2 ≤ t(z) ≤ d − 2` (`freeH_tGrade_add_two_le`) and `d + n ≤ s(z) ≤ T − (d − n)` (`freeH_sGrade_bounds`). Then:

* `z+N` and `z+E+N` have `t`-grades `t(z) − d` and `t(z) + n − d`, which lie in the zero strip `[1 − d, n + 2d − 1]`; so `F = 0` there
  (`HasStrips`), and both are contacts of the base `z` (the parabola is `capMin 1 = 0` at height `z.2 + 1`).
* `z+N` is open (`north_open`); `z+E+N` is open by `openE_box`, an integer lemma on the odd box `1 ≤ x ≤ d`, `0 ≤ y ≤ n − 1`.
* Both lie in the cone `ConeRoot z K` for `K ≥ 2`. -/

namespace FLatticePaper.ShapeOneGeom

open FLatticePaper FLatticePaper.Induction FLatticePaper.AllBranchFan FLatticePaper.CapRay FLatticePaper.ContactCone
open FLatticePaper.ShortRoute FLatticePaper.QuadraticCap

/-- **The open top of the odd east-north point**, on the odd box: `(d+n)x + (d−n)y + 2d < T + 2 − d + n`, given `n + 2 ≤ n x − d y ≤ d − 2`. -/
theorem openE_box (n d x y : ℤ) (hn : 1 ≤ n) (hpar : (n + d) % 2 = 0)
    (hx1 : 1 ≤ x) (hxd : x ≤ d) (hy0 : 0 ≤ y) (hyn : y ≤ n - 1) (hodd : (x + y) % 2 = 1)
    (htlo : n + 2 ≤ n * x - d * y) (hthi : n * x - d * y ≤ d - 2) :
    (d + n) * x + (d - n) * y + 2 * d < d ^ 2 + 2 * d * n - n ^ 2 + 2 - d + n := by
  by_contra hcon
  have hcon' := not_lt.mp hcon
  obtain ⟨a, rfl⟩ : ∃ a, x = d - a := ⟨d - x, by ring⟩
  obtain ⟨b, rfl⟩ : ∃ b, y = n - 1 - b := ⟨n - 1 - y, by ring⟩
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hviol : (d + n) * a + (d - n) * b ≤ 2 * d - 2 := by
    have e : (d + n) * (d - a) + (d - n) * (n - 1 - b) + 2 * d
        = (d ^ 2 + 2 * d * n - n ^ 2) - (d - n) - ((d + n) * a + (d - n) * b) + 2 * d := by ring
    linarith
  have ht1 : d * b - n * a ≤ -2 := by
    have e : n * (d - a) - d * (n - 1 - b) = d + d * b - n * a := by ring
    linarith
  have h1 : 1 ≤ a := by
    by_contra h
    have h0 : a = 0 := by omega
    subst h0
    nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ d) hb0]
  have h2 : a ≤ 1 := by
    by_contra h
    have h' := not_le.mp h
    nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ a - 2) (by linarith : (0 : ℤ) ≤ d + n),
      mul_nonneg (by linarith : (0 : ℤ) ≤ d - n) hb0]
  have ha1 : a = 1 := by omega
  subst ha1
  have h3 : b = 0 := by
    by_contra h
    have hb1 : 1 ≤ b := by omega
    nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ b - 1) (by linarith : (0 : ℤ) ≤ d - n)]
  subst h3
  omega


/-- The zero strip of `HasStrips`, on the `t`-grade. -/
theorem zero_of_tGrade {frame : ChildFrame} {F : Field} (hS : frame.HasStrips F) {w : Site}
    (h1 : 1 - frame.child.den ≤ frame.tGrade w) (h2 : frame.tGrade w ≤ frame.child.num + 2 * frame.child.den - 1) :
    F w = 0 := by
  unfold ChildFrame.HasStrips at hS
  exact hS.1 w h1 h2

/-- **The east-north point of an odd free H midpoint is open.** -/
theorem openRect_east_north (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeH) (hodd : ¬ EvenSite z)
    (hne : z ≠ frame.hLast) (hbt : frame.child.num + 2 ≤ frame.tGrade z) :
    frame.openRect (z.1 + 1, z.2 + 1) := by
  have ht := freeH_tGrade_add_two_le frame hz hodd hne
  obtain ⟨hs1, hs2⟩ := freeH_sGrade_bounds frame hz
  obtain ⟨hx1, hxd, hy0, hyn⟩ := FreeTraceBox.freeH_box frame hz
  obtain ⟨hn1, hnd, -, hd3, hP⟩ := frame.child_facts
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hwo : ¬ EvenSite (z.1 + 1, z.2 + 1) := by
    unfold EvenSite at hodd ⊢
    simp only at hodd ⊢
    omega
  have hpar : (z.1 + z.2) % 2 = 1 := by
    unfold EvenSite at hodd
    omega
  have htz : frame.tGrade z = frame.child.num * z.1 - frame.child.den * z.2 := rfl
  have hsz : frame.sGrade z = (frame.child.den + frame.child.num) * z.1 + (frame.child.den - frame.child.num) * z.2 := rfl
  have htG : frame.tGrade (z.1 + 1, z.2 + 1) = frame.tGrade z + frame.child.num - frame.child.den := by
    unfold ChildFrame.tGrade
    dsimp only
    ring
  have hsG : frame.sGrade (z.1 + 1, z.2 + 1) = frame.sGrade z + 2 * frame.child.den := by
    unfold ChildFrame.sGrade
    dsimp only
    ring
  have key := openE_box frame.child.num frame.child.den z.1 z.2 hn1 hev hx1 hxd hy0 hyn hpar
    (by rw [← htz]; omega) (by rw [← htz]; omega)
  unfold ChildFrame.openRect
  rw [if_neg hwo, htG, hsG, hP]
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith
  · linarith
  · linarith
  · rw [hsz]
    linarith [key]

/-- The chain points of the east-north shape are contacts of the fan based at the odd free H midpoint `z`:
`z+N` and `z+E+N` (heights `1`, parabola value `capMin 1 = 0`, `F = 0` in the zero strip). -/
theorem chain_contacts (frame : ChildFrame) {F : Field} (hS : frame.HasStrips F) {z : Site}
    (hz : z ∈ frame.freeH) (hodd : ¬ EvenSite z) (hne : z ≠ frame.hLast)
    (hbt : frame.child.num + 2 ≤ frame.tGrade z) {K : ℕ} (hK : 2 ≤ K) :
    (z.1, z.2 + 1) ∈ contactFan frame F z K ∧ (z.1 + 1, z.2 + 1) ∈ contactFan frame F z K := by
  have ht := freeH_tGrade_add_two_le frame hz hodd hne
  obtain ⟨hn1, hnd, hdn, hd3, -⟩ := frame.child_facts
  have hcapOne : capMin ((z.2 + 1) - z.2) = 0 := by
    have e : (z.2 + 1) - z.2 = 1 := by ring
    rw [e]
    unfold capMin
    norm_num
  have hev : EvenSite (z.1, z.2 + 1) := by
    unfold EvenSite at hodd ⊢
    simp only at hodd ⊢
    omega
  have hwo : ¬ EvenSite (z.1 + 1, z.2 + 1) := by
    unfold EvenSite at hodd ⊢
    simp only at hodd ⊢
    omega
  constructor
  · -- north: `F = 0` from the zero strip at `tGrade = t − d`
    have hF : F (z.1, z.2 + 1) = 0 := by
      apply zero_of_tGrade hS
      · have e : frame.tGrade (z.1, z.2 + 1) = frame.tGrade z - frame.child.den := by
          unfold ChildFrame.tGrade
          dsimp only
          ring
        omega
      · have e : frame.tGrade (z.1, z.2 + 1) = frame.tGrade z - frame.child.den := by
          unfold ChildFrame.tGrade
          dsimp only
          ring
        omega
    refine mem_contactFan.mpr ⟨⟨north_open frame hz hodd hne hbt, ?_⟩, ?_⟩
    · unfold ConeRoot
      refine ⟨?_, ?_, fun _ => ?_, fun h => absurd hev h⟩ <;> dsimp only <;> omega
    · show F (z.1, z.2 + 1) = parabolaField z.2 (z.1, z.2 + 1)
      unfold parabolaField
      dsimp only
      rw [hF, hcapOne]
  · have hF : F (z.1 + 1, z.2 + 1) = 0 := by
      apply zero_of_tGrade hS
      · have e : frame.tGrade (z.1 + 1, z.2 + 1) = frame.tGrade z + frame.child.num - frame.child.den := by
          unfold ChildFrame.tGrade
          dsimp only
          ring
        omega
      · have e : frame.tGrade (z.1 + 1, z.2 + 1) = frame.tGrade z + frame.child.num - frame.child.den := by
          unfold ChildFrame.tGrade
          dsimp only
          ring
        omega
    refine mem_contactFan.mpr ⟨⟨openRect_east_north frame hz hodd hne hbt, ?_⟩, ?_⟩
    · unfold ConeRoot
      refine ⟨?_, ?_, fun h => absurd h hwo, fun _ => ?_⟩ <;> dsimp only <;> omega
    · show F (z.1 + 1, z.2 + 1) = parabolaField z.2 (z.1 + 1, z.2 + 1)
      unfold parabolaField
      dsimp only
      rw [hF, hcapOne]

end FLatticePaper.ShapeOneGeom
