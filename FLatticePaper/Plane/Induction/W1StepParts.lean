import FLatticePaper.Plane.Induction.WiredCovered
import FLatticePaper.Plane.Induction.CapBaseN1
import FLatticePaper.Plane.Induction.ReflectedFan
import FLatticePaper.Plane.Induction.W1Strips
import FLatticePaper.Plane.Induction.NonfreeBridge

/-! # The standard inputs of the route assembly, from a packet of the standard field

For a packet `hP : frame.Packet G` with the slip sign bound `hsig`, the cap inputs `hAS` hold for every frame: for `n = 1` by
`CapBaseN1.hAS_n1`, for `n ≥ 3` and `d − n ≥ 4` by `WiredCovered.hAS_of_proper`, and for `d − n = 2` the range of `K` is empty
(`n K ≥ 3n + 1` and `2 n K ≤ 6n + 5` force `K ≤ 3` and `K ≥ 4`). The H-reflection symmetry `hsym` is the I-symmetry of `G` composed
with the kernel period. -/

namespace FLatticePaper.W1StepParts

open FLatticePaper FLatticePaper.Induction

theorem hAS_all {frame : ChildFrame} {G : Field} (hP : frame.Packet G)
    (hsig : ∀ w ∈ frame.closedPolygon, G w - G (w - frame.shortShift) ≤ 0) :
    ∀ K : ℕ, 2 ≤ K → frame.child.den + 2 * frame.child.num - 1 ≤ frame.child.num * (K : ℤ) →
      2 * frame.child.num * (K : ℤ) ≤ 3 * frame.child.den + 3 * frame.child.num - 1 →
      ∃ p q : ℤ, frame.child.num * p - frame.child.den * q = 2 - frame.child.num ∧
        ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ G (p + (k : ℤ), q + (k : ℤ)) := by
  intro K hK2 hKs hKr
  obtain ⟨hn0, hnd, hd2, -, -⟩ := frame.child_facts
  obtain ⟨hnO, hdO⟩ := frame.child_odd
  by_cases h1 : frame.child.num = 1
  · exact FLatticePaper.CapBaseN1.hAS_n1 hP hsig h1 K hKr
  by_cases h2 : 4 ≤ frame.child.den - frame.child.num
  · exact FLatticePaper.WiredCovered.hAS_of_proper hP hsig (by omega) h2 K hKr
  exfalso
  have hden : frame.child.den = frame.child.num + 2 := by omega
  have hn3 : 3 ≤ frame.child.num := by omega
  rw [hden] at hKs hKr
  rcases le_or_gt K 3 with hK | hK
  · have hK' : (K : ℤ) ≤ 3 := by exact_mod_cast hK
    nlinarith
  · have hK' : (4 : ℤ) ≤ (K : ℤ) := by exact_mod_cast (show 4 ≤ K by omega)
    nlinarith

/-- The H-reflection symmetry of the standard field: the I-symmetry and the kernel period. -/
theorem hsym_of_iRefl {frame : ChildFrame} {G : Field} (hP : frame.Packet G)
    (hIsym : ∀ z : Site, G (FLatticePaper.W1Strips.iRefl z) = G z) :
    ∀ y, G (FLatticePaper.ReflectedFan.reflH frame y) = G y := by
  have hper : HasGeneratorPeriods frame.child G 0 frame.coherentConstantV := by
    have h := hP.periods
    rw [FLatticePaper.Induction.coherentConstantU_eq_zero frame] at h
    exact h
  have hk : frame.child.modifiedDeck.kernel = (frame.child.den, frame.child.num) := by
    rw [frame.child_modifiedDeck_kernel]
  have hrefl : ∀ z : Site, G (reflectionI - z) = G z := by
    intro z
    have h := hIsym z
    rw [FLatticePaper.W1Strips.iRefl_eq_sub] at h
    exact h
  intro y
  have e : FLatticePaper.ReflectedFan.reflH frame y = (reflectionI - y) + frame.child.modifiedDeck.kernel := by
    rw [hk]
    unfold FLatticePaper.ReflectedFan.reflH reflectionI
    refine Prod.ext ?_ ?_
    all_goals simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
    all_goals omega
  have hpd := ChildFrame.periodic_kernel frame hper (reflectionI - y) 1
  rw [one_smul] at hpd
  rw [e, hpd, hrefl]

/-- The kernel period of the standard field with zero constant: `G (z + (d, n)) = G z`. -/
theorem perK_of_packet {frame : ChildFrame} {G : Field} (hP : frame.Packet G) :
    ∀ z : Site, G (z + (frame.child.den, frame.child.num)) = G z := by
  intro z
  have h := hP.periods.1 z
  rw [FLatticePaper.Induction.coherentConstantU_eq_zero frame, add_zero] at h
  rw [frame.child_modifiedDeck_kernel] at h
  exact h

/-- The periods of the standard field with zero kernel constant. -/
theorem hper_of_packet {frame : ChildFrame} {G : Field} (hP : frame.Packet G) :
    HasGeneratorPeriods frame.child G 0 frame.coherentConstantV := by
  have h := hP.periods
  rw [FLatticePaper.Induction.coherentConstantU_eq_zero frame] at h
  exact h

/-- The slip sign bound `G w − G (w − σ) ≤ 0` on the closed polygon, from the slip range. -/
theorem hsig_of_SE {frame : ChildFrame} {G : Field} (hP : frame.Packet G)
    (hslipR : ∀ z ∈ frame.closedPolygon, 0 ≤ frame.slip G 1 z ∧ frame.slip G 1 z ≤ 2) :
    ∀ w ∈ frame.closedPolygon, G w - G (w - frame.shortShift) ≤ 0 := by
  apply FLatticePaper.SheetMonoChild.hsig_of_slip frame hP
  intro w hw
  have h := hslipR w hw
  unfold ChildFrame.slip at h
  simp only [one_smul] at h
  exact h

end FLatticePaper.W1StepParts
