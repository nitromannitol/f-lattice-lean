import FLatticePaper.Plane.Induction.AlignedClassSite
import FLatticePaper.Plane.Induction.FaceReflect
import FLatticePaper.Plane.Induction.CollarTop
import FLatticePaper.Plane.Induction.BoundaryPair
import FLatticePaper.Plane.Induction.StripColours
import FLatticePaper.Plane.Induction.Exceptions

/-! # The two pair classifications, by reflection (steps (5d) of the top square)

The reflection `z ↦ R − z` (`R = frame.centre`) exchanges left with right and bottom with top. So the two pairs of
adjacent boundary witnesses reduce to the classifications `classify_minus` (right and top) and `classify_plus`
(left and top) at the reflected centre:

* a strict centre with a left witness and a bottom witness is `(1, 1)` (the lower-left meeting, black);
* a strict centre with a right witness and a bottom witness is `(d − 1, n)` (the right-bottom meeting, black). -/

namespace FLatticePaper.PairClass

open FLatticePaper FLatticePaper.W1 FLatticePaper.W1OffCollar FLatticePaper.FaceWitness FLatticePaper.FaceReflect
  FLatticePaper.CollarTop FLatticePaper.BoundaryPair FLatticePaper.AlignedClassSite FLatticePaper.StripColours

/-- A bottom witness of `c` gives a top witness of the reflected centre `R − c`. -/
theorem bottomTop_witness (frame : FLatticePaper.Induction.ChildFrame) {c : Site} (hB : BottomWit frame c) :
    TopWit frame (frame.centre - c) := by
  obtain ⟨v, hvA, hvB, hv⟩ := hB
  refine ⟨frame.centre - v, ?_, ?_, ?_⟩
  · have e : (frame.centre - v).1 - (frame.centre - c).1 = c.1 - v.1 := by
      simp only [Prod.fst_sub]
      ring
    rw [e, abs_sub_comm]
    exact hvA
  · have e : (frame.centre - v).2 - (frame.centre - c).2 = c.2 - v.2 := by
      simp only [Prod.snd_sub]
      ring
    rw [e, abs_sub_comm]
    exact hvB
  · rw [sub_sub]
    exact freeH_reflect frame hv

/-- **The lower-left meeting.** A strict centre with a left witness and a bottom witness is `(1, 1)`. -/
theorem left_bottom_centre (frame : FLatticePaper.Induction.ChildFrame) {c : Site} (hS : FLatticePaper.W1.StrictInterior
      frame.child.num frame.child.den c)
    (hL : LeftWit frame c) (hB : BottomWit frame c) : c = (1, 1) := by
  obtain ⟨hnO, hdO⟩ := frame.child_odd
  obtain ⟨hn0, hnd1, hd2, -, -⟩ := frame.child_facts
  have hn1 : 1 ≤ frame.child.num := by omega
  have hnd : frame.child.num + 2 ≤ frame.child.den := by omega
  have hTL : 2 * (frame.child.den + frame.child.num) < w1T frame.child.num frame.child.den := by
    have := FLatticePaper.Exceptions.period_ge2 hn1 hnd
    omega
  have hS' : FLatticePaper.W1.StrictInterior frame.child.num frame.child.den (frame.centre - c) :=
    (strict_reflect_centre frame c).mpr hS
  obtain ⟨v, hv1, hv2, hvF⟩ := leftWit_rightWit frame hL
  obtain ⟨w, hw1, hw2, hwF⟩ := bottomTop_witness frame hB
  rw [kernel_eq] at hvF
  rw [transverse_eq] at hwF
  have hR : ∃ v : Site, |v.1 - (frame.centre - c).1| ≤ 1 ∧ |v.2 - (frame.centre - c).2| ≤ 1 ∧
      freeVn frame.child.num frame.child.den (v.1 - frame.child.den, v.2 - frame.child.num) :=
    ⟨v, hv1, hv2, (freeV_iff_freeVn frame _).mp hvF⟩
  have hT : ∃ w : Site, |w.1 - (frame.centre - c).1| ≤ 1 ∧ |w.2 - (frame.centre - c).2| ≤ 1 ∧
      freeHn frame.child.num frame.child.den (w.1 - (frame.child.num - frame.child.den),
        w.2 - (frame.child.num + frame.child.den)) :=
    ⟨w, hw1, hw2, (freeH_iff_freeHn frame _).mp hwF⟩
  have hcls := classify_minus hnO hdO hn1 hnd hTL (frame.centre - c) hS' hR hT
  rw [CollarTop.centre_eq] at hcls
  have h1 := congrArg Prod.fst hcls
  have h2 := congrArg Prod.snd hcls
  simp only [Prod.fst_sub, Prod.snd_sub] at h1 h2
  exact Prod.ext (by dsimp only; omega) (by dsimp only; omega)

/-- **The right-bottom meeting.** A strict centre with a right witness and a bottom witness is `(d − 1, n)`. -/
theorem right_bottom_centre (frame : FLatticePaper.Induction.ChildFrame) {c : Site} (hS : FLatticePaper.W1.StrictInterior
      frame.child.num frame.child.den c)
    (hR : RightWit frame c) (hB : BottomWit frame c) :
    c = (frame.child.den - 1, frame.child.num) := by
  obtain ⟨hnO, hdO⟩ := frame.child_odd
  obtain ⟨hn0, hnd1, hd2, -, -⟩ := frame.child_facts
  have hn1 : 1 ≤ frame.child.num := by omega
  have hnd : frame.child.num + 2 ≤ frame.child.den := by omega
  have hTL : 2 * (frame.child.den + frame.child.num) < w1T frame.child.num frame.child.den := by
    have := FLatticePaper.Exceptions.period_ge2 hn1 hnd
    omega
  have hS' : FLatticePaper.W1.StrictInterior frame.child.num frame.child.den (frame.centre - c) :=
    (strict_reflect_centre frame c).mpr hS
  obtain ⟨v, hv1, hv2, hvF⟩ := rightWit_leftWit frame hR
  obtain ⟨w, hw1, hw2, hwF⟩ := bottomTop_witness frame hB
  rw [transverse_eq] at hwF
  have hL : ∃ v : Site, |v.1 - (frame.centre - c).1| ≤ 1 ∧ |v.2 - (frame.centre - c).2| ≤ 1 ∧
      freeVn frame.child.num frame.child.den v :=
    ⟨v, hv1, hv2, (freeV_iff_freeVn frame _).mp hvF⟩
  have hT : ∃ w : Site, |w.1 - (frame.centre - c).1| ≤ 1 ∧ |w.2 - (frame.centre - c).2| ≤ 1 ∧
      freeHn frame.child.num frame.child.den (w.1 - (frame.child.num - frame.child.den),
        w.2 - (frame.child.num + frame.child.den)) :=
    ⟨w, hw1, hw2, (freeH_iff_freeHn frame _).mp hwF⟩
  have hcls := classify_plus hnO hdO hn1 hnd hTL (frame.centre - c) hS' hL hT
  rw [CollarTop.centre_eq] at hcls
  have h1 := congrArg Prod.fst hcls
  have h2 := congrArg Prod.snd hcls
  simp only [Prod.fst_sub, Prod.snd_sub] at h1 h2
  exact Prod.ext (by dsimp only; omega) (by dsimp only; omega)

end FLatticePaper.PairClass
