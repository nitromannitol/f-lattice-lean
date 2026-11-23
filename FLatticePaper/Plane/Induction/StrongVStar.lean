import FLatticePaper.Plane.Induction.BaseReflection
import FLatticePaper.Plane.Induction.ChartGrades
import FLatticePaper.Plane.Induction.Potentials
import FLatticePaper.Plane.Induction.PolygonGeometry
import FLatticePaper.Plane.Induction.Reflection
import FLatticePaper.Plane.Induction.Strips
import FLatticePaper.Plane.Induction.StrongHStrip

/-! Task 67, STRONG_PRICE §3 (the V full stars): the `t`-saturation puts every site of a V full star into `E + Z U`.

The kernel `U = (d, n)` has `t(U) = 0` and `s(U) = T`, so a kernel shift changes `s` by multiples of `T` and keeps `t` and the parity.
A site whose `t`-grade lies in the `t`-range of `E` (at its parity) is therefore moved into `E` by a kernel shift alone
(`exists_kernel_mem_of_tWindow`, from the window `exists_kernel_shift`). The sites of a V star have `t` in those ranges, by arithmetic
from the V root bounds (the named V arc geometry of the note): even roots `t ∈ [L − T, 0]`, odd roots `t ∈ [L + d − T, −d]`
(`vStar_even_root_mem`, `vStar_odd_root_mem`). -/

namespace FLatticePaper.StrongVStar

open Farey FLatticePaper FLatticePaper.Induction

/-- The kernel `U = (d, n)` has `t`-grade `0`. -/
theorem tGrade_kernel_eq_zero (frame : ChildFrame) :
    frame.tGrade frame.child.modifiedDeck.kernel = 0 := by
  rw [frame.child_modifiedDeck_kernel]
  unfold ChildFrame.tGrade
  ring

/-- **The covering by a kernel shift.** If the `t`-grade of `x` lies in the `t`-range of `E` at its parity, some kernel shift of `x` lies
in `E`. -/
theorem exists_kernel_mem_of_tWindow (frame : ChildFrame) (x : Site)
    (hw : (EvenSite x → 2 - frame.child.periodDenominator ≤ frame.tGrade x ∧
        frame.tGrade x ≤ frame.child.den + frame.child.num - 2) ∧
      (¬ EvenSite x → frame.child.num - frame.child.periodDenominator ≤ frame.tGrade x ∧
        frame.tGrade x ≤ frame.child.den)) :
    ∃ k : ℤ, x + k • frame.child.modifiedDeck.kernel ∈ frame.closedPolygon := by
  obtain ⟨hn0, hnd, hdn, hd3, hT⟩ := frame.child_facts
  have htU : ∀ k : ℤ, frame.tGrade (x + k • frame.child.modifiedDeck.kernel) = frame.tGrade x := by
    intro k
    rw [frame.tGrade_add_pt, frame.tGrade_smul, tGrade_kernel_eq_zero]
    ring
  by_cases he : EvenSite x
  · obtain ⟨k, e, he0, heT, hse⟩ := frame.exists_kernel_shift x 0
    refine ⟨k, frame.mem_closedPolygon_of_even ((frame.evenSite_add_smul_kernel x k).mpr he) ?_ ?_⟩
    · rw [htU]
      exact hw.1 he
    · rw [hse]
      constructor <;> omega
  · obtain ⟨k, e, he0, heT, hse⟩ := frame.exists_kernel_shift x (2 - frame.child.den + frame.child.num)
    refine ⟨k, frame.mem_closedPolygon_of_odd (fun h => he ((frame.evenSite_add_smul_kernel x k).mp h)) ?_ ?_⟩
    · rw [htU]
      exact hw.2 he
    · rw [hse]
      constructor <;> omega

/-- The inputs of an odd site are its vertical neighbours: `t(incomingNeg) = t + d` and `t(incomingPos) = t − d`. -/
theorem odd_inputs_tGrade (frame : ChildFrame) (z : Site) (ho : ¬ EvenSite z) :
    frame.tGrade (FLatticePaper.incomingNeg z) = frame.tGrade z + frame.child.den ∧
      frame.tGrade (FLatticePaper.incomingPos z) = frame.tGrade z - frame.child.den := by
  have hneg : FLatticePaper.incomingNeg z = (z.1, z.2 - 1) := by
    unfold FLatticePaper.incomingNeg
    rw [if_neg ho]
  have hpos : FLatticePaper.incomingPos z = (z.1, z.2 + 1) := by
    unfold FLatticePaper.incomingPos
    rw [if_neg ho]
  rw [hneg, hpos]
  unfold ChildFrame.tGrade
  constructor <;> ring

/-- **The even V star.** An even V root with `t ∈ [L − T, 0]` (`L = d + n`) and its two inputs (odd, with `t ∈ [d − T, n]`) lie in
`E + Z U`. -/
theorem vStar_even_root_mem (frame : ChildFrame) (r : Site) (he : EvenSite r)
    (hr1 : frame.child.den + frame.child.num - frame.child.periodDenominator ≤ frame.tGrade r)
    (hr2 : frame.tGrade r ≤ 0) :
    (∃ k : ℤ, r + k • frame.child.modifiedDeck.kernel ∈ frame.closedPolygon) ∧
      (∃ k : ℤ, FLatticePaper.incomingNeg r + k • frame.child.modifiedDeck.kernel ∈ frame.closedPolygon) ∧
      (∃ k : ℤ, FLatticePaper.incomingPos r + k • frame.child.modifiedDeck.kernel ∈ frame.closedPolygon) := by
  obtain ⟨hn0, hnd, hdn, hd3, hT⟩ := frame.child_facts
  obtain ⟨hN, hP⟩ := FLatticePaper.StrongHStrip.even_inputs_tGrade frame r he
  have he' : (r.1 + r.2) % 2 = 0 := he
  have hnegE : ¬ EvenSite (FLatticePaper.incomingNeg r) := by
    have e : FLatticePaper.incomingNeg r = (r.1 - 1, r.2) := by
      unfold FLatticePaper.incomingNeg
      rw [if_pos he]
    rw [e]
    show ¬ ((r.1 - 1 + r.2) % 2 = 0)
    omega
  have hposE : ¬ EvenSite (FLatticePaper.incomingPos r) := by
    have e : FLatticePaper.incomingPos r = (r.1 + 1, r.2) := by
      unfold FLatticePaper.incomingPos
      rw [if_pos he]
    rw [e]
    show ¬ ((r.1 + 1 + r.2) % 2 = 0)
    omega
  refine ⟨exists_kernel_mem_of_tWindow frame r ⟨fun _ => ?_, fun h => absurd he h⟩,
    exists_kernel_mem_of_tWindow frame _ ⟨fun h => absurd h hnegE, fun _ => ?_⟩,
    exists_kernel_mem_of_tWindow frame _ ⟨fun h => absurd h hposE, fun _ => ?_⟩⟩
  · constructor <;> omega
  · rw [hN]
    constructor <;> omega
  · rw [hP]
    constructor <;> omega

/-- **The odd V star.** An odd V root with `t ∈ [L + d − T, −d]` and its two inputs (even, with `t ∈ [L − T, 0]`) lie in `E + Z U`. -/
theorem vStar_odd_root_mem (frame : ChildFrame) (r : Site) (ho : ¬ EvenSite r)
    (hr1 : frame.child.den + frame.child.num + frame.child.den - frame.child.periodDenominator ≤ frame.tGrade r)
    (hr2 : frame.tGrade r ≤ -frame.child.den) :
    (∃ k : ℤ, r + k • frame.child.modifiedDeck.kernel ∈ frame.closedPolygon) ∧
      (∃ k : ℤ, FLatticePaper.incomingNeg r + k • frame.child.modifiedDeck.kernel ∈ frame.closedPolygon) ∧
      (∃ k : ℤ, FLatticePaper.incomingPos r + k • frame.child.modifiedDeck.kernel ∈ frame.closedPolygon) := by
  obtain ⟨hn0, hnd, hdn, hd3, hT⟩ := frame.child_facts
  obtain ⟨hN, hP⟩ := odd_inputs_tGrade frame r ho
  have ho' : ¬ ((r.1 + r.2) % 2 = 0) := ho
  have hnegE : EvenSite (FLatticePaper.incomingNeg r) := by
    have e : FLatticePaper.incomingNeg r = (r.1, r.2 - 1) := by
      unfold FLatticePaper.incomingNeg
      rw [if_neg ho]
    rw [e]
    show (r.1 + (r.2 - 1)) % 2 = 0
    omega
  have hposE : EvenSite (FLatticePaper.incomingPos r) := by
    have e : FLatticePaper.incomingPos r = (r.1, r.2 + 1) := by
      unfold FLatticePaper.incomingPos
      rw [if_neg ho]
    rw [e]
    show (r.1 + (r.2 + 1)) % 2 = 0
    omega
  refine ⟨exists_kernel_mem_of_tWindow frame r ⟨fun h => absurd h ho, fun _ => ?_⟩,
    exists_kernel_mem_of_tWindow frame _ ⟨fun _ => ?_, fun h => absurd hnegE h⟩,
    exists_kernel_mem_of_tWindow frame _ ⟨fun _ => ?_, fun h => absurd hposE h⟩⟩
  · constructor <;> omega
  · rw [hN]
    constructor <;> omega
  · rw [hP]
    constructor <;> omega

end FLatticePaper.StrongVStar
