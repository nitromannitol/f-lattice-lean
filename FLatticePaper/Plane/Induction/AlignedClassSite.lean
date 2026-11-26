import FLatticePaper.Plane.Induction.CrossingLattice
import FLatticePaper.Plane.Induction.W1OffCollar
import FLatticePaper.Plane.Induction.AlignedClassGrade
import FLatticePaper.Plane.Induction.AlignedClassGradeMinus

/-! # The aligned classification at lattice points (both signs)

A strict integer site `c` with an aligned witness and a top witness is the target: `V + (2,-1) = (n-d+2, n+d-1)` for `eps = +1`,
and `R - (1,1) = (n, 2n+d-2)` for `eps = -1`. The site predicates are rewritten in grades (`w1t`, `w1s`), the witnesses become
the grade predicates of `AlignedClassGrade`, and the grade cores give the offset `(p, q) = (0, 0)` of `c` from the target. The
offsets are integers (site coordinates), so no integrality beyond the site itself is needed. -/

namespace FLatticePaper.AlignedClassSite

open FLatticePaper FLatticePaper.W1 FLatticePaper.W1OffCollar FLatticePaper.CrossingLattice
  FLatticePaper.AlignedClassGrade FLatticePaper.AlignedClassGradeMinus

theorem w1T_eq (n d : ℤ) : w1T n d = d * d + 2 * d * n - n * n := by
  unfold w1T; ring

theorem w1t_diff (n d : ℤ) (c v : Site) :
    w1t n d v = w1t n d c + n * (v.1 - c.1) - d * (v.2 - c.2) := by
  unfold w1t; ring

theorem w1s_diff (n d : ℤ) (c v : Site) :
    w1s n d v = w1s n d c + (d + n) * (v.1 - c.1) + (d - n) * (v.2 - c.2) := by
  unfold w1s; ring

theorem closedRect_iff_ClG {n d : ℤ} (hn : n % 2 = 1) (hd : d % 2 = 1) (z : Site) :
    closedRect n d z ↔ ClG n d (w1T n d) (w1t n d z) (w1s n d z) := by
  have hp := parity_w1t hn hd z
  unfold ClG
  by_cases h : EvenSite z
  · rw [cR_even h]
    unfold EvenSite at h
    generalize w1t n d z = t at *
    generalize w1s n d z = s at *
    generalize w1T n d = T at *
    constructor <;> intro hh <;> omega
  · rw [cR_odd h]
    unfold EvenSite at h
    generalize w1t n d z = t at *
    generalize w1s n d z = s at *
    generalize w1T n d = T at *
    constructor <;> intro hh <;> omega

theorem strict_to_SIG {n d : ℤ} (hn : n % 2 = 1) (hd : d % 2 = 1) (z : Site)
    (hS : StrictInterior n d z) : SIG n d (w1T n d) (w1t n d z) (w1s n d z) := by
  have hp := parity_w1t hn hd z
  unfold SIG
  by_cases h : EvenSite z
  · rw [sI_even h] at hS
    unfold EvenSite at h
    generalize w1t n d z = t at *
    generalize w1s n d z = s at *
    generalize w1T n d = T at *
    omega
  · rw [sI_odd h] at hS
    unfold EvenSite at h
    generalize w1t n d z = t at *
    generalize w1s n d z = s at *
    generalize w1T n d = T at *
    omega

theorem freeVn_to_FVG {n d : ℤ} (hn : n % 2 = 1) (hd : d % 2 = 1) {v : Site} (hv : freeVn n d v) :
    FVG n d (w1T n d) (w1t n d v) (w1s n d v) := by
  obtain ⟨h1, h2, h3⟩ := hv
  refine ⟨(closedRect_iff_ClG hn hd v).mp h1, ?_, h3⟩
  intro h4
  apply h2
  have e1 : w1t n d (v.1 - 1, v.2) = w1t n d v - n := by unfold w1t; ring
  have e2 : w1s n d (v.1 - 1, v.2) = w1s n d v - (d + n) := by unfold w1s; ring
  rw [closedRect_iff_ClG hn hd, e1, e2]
  exact h4

theorem freeHn_to_FHG {n d : ℤ} (hn : n % 2 = 1) (hd : d % 2 = 1) {v : Site} (hv : freeHn n d v) :
    FHG n d (w1T n d) (w1t n d v) (w1s n d v) := by
  obtain ⟨h1, h2, h3⟩ := hv
  refine ⟨(closedRect_iff_ClG hn hd v).mp h1, ?_, h3⟩
  intro h4
  apply h2
  have e1 : w1t n d (v.1, v.2 - 1) = w1t n d v + d := by unfold w1t; ring
  have e2 : w1s n d (v.1, v.2 - 1) = w1s n d v - (d - n) := by unfold w1s; ring
  rw [closedRect_iff_ClG hn hd, e1, e2]
  exact h4

/-- **The aligned classification at lattice points, eps = +1.** -/
theorem classify_plus {n d : ℤ} (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hTL : 2 * (d + n) < w1T n d) (c : Site) (hS : StrictInterior n d c)
    (hL : ∃ v : Site, |v.1 - c.1| ≤ 1 ∧ |v.2 - c.2| ≤ 1 ∧ freeVn n d v)
    (hTop : ∃ w : Site, |w.1 - c.1| ≤ 1 ∧ |w.2 - c.2| ≤ 1 ∧
      freeHn n d (w.1 - (n - d), w.2 - (n + d))) :
    c = (n - d + 2, n + d - 1) := by
  obtain ⟨v, hv1, hv2, hvF⟩ := hL
  obtain ⟨w, hw1, hw2, hwF⟩ := hTop
  have hT2 := parity_w1T hn hd
  have hS' := strict_to_SIG hn hd c hS
  have hFV := freeVn_to_FVG hn hd hvF
  rw [w1t_diff n d c v, w1s_diff n d c v] at hFV
  have hFH := freeHn_to_FHG hn hd hwF
  have eV : w1t n d (w.1 - (n - d), w.2 - (n + d)) = w1t n d w + w1T n d := by
    unfold w1t w1T; ring
  have eS : w1s n d (w.1 - (n - d), w.2 - (n + d)) = w1s n d w := by
    unfold w1s; ring
  rw [eV, eS, w1t_diff n d c w, w1s_diff n d c w] at hFH
  have hb1 := abs_le.mp hv1
  have hb2 := abs_le.mp hv2
  have hb3 := abs_le.mp hw1
  have hb4 := abs_le.mp hw2
  have hL' : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FVG n d (w1T n d) (w1t n d c + n * i - d * j) (w1s n d c + (d + n) * i + (d - n) * j) :=
    ⟨v.1 - c.1, v.2 - c.2, hb1.1, hb1.2, hb2.1, hb2.2, hFV⟩
  have hT' : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FHG n d (w1T n d) (w1t n d c + n * i - d * j + w1T n d) (w1s n d c + (d + n) * i + (d - n) * j) :=
    ⟨w.1 - c.1, w.2 - c.2, hb3.1, hb3.2, hb4.1, hb4.2, hFH⟩
  have hpt : w1t n d c = (-(w1T n d) + 2 * n + d) + n * (c.1 - (n - d + 2)) - d * (c.2 - (n + d - 1)) := by
    unfold w1t; rw [w1T_eq]; ring
  have hps : w1s n d c = (d + 3 * n) + (d + n) * (c.1 - (n - d + 2)) + (d - n) * (c.2 - (n + d - 1)) := by
    unfold w1s; ring
  obtain ⟨h1, h2⟩ := class_plus_core n d (w1T n d) (w1t n d c) (w1s n d c)
    (c.1 - (n - d + 2)) (c.2 - (n + d - 1)) hn hd hn1 hnd hTL hT2 (w1T_eq n d) hpt hps hS' hL' hT'
  exact Prod.ext (by dsimp only; omega) (by dsimp only; omega)

/-- **The aligned classification at lattice points, eps = -1.** The aligned witness is the kernel-shifted free V point. -/
theorem classify_minus {n d : ℤ} (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hTL : 2 * (d + n) < w1T n d) (c : Site) (hS : StrictInterior n d c)
    (hR : ∃ v : Site, |v.1 - c.1| ≤ 1 ∧ |v.2 - c.2| ≤ 1 ∧ freeVn n d (v.1 - d, v.2 - n))
    (hTop : ∃ w : Site, |w.1 - c.1| ≤ 1 ∧ |w.2 - c.2| ≤ 1 ∧
      freeHn n d (w.1 - (n - d), w.2 - (n + d))) :
    c = (n, 2 * n + d - 2) := by
  obtain ⟨v, hv1, hv2, hvF⟩ := hR
  obtain ⟨w, hw1, hw2, hwF⟩ := hTop
  have hT2 := parity_w1T hn hd
  have hS' := strict_to_SIG hn hd c hS
  have hFV := freeVn_to_FVG hn hd hvF
  have eK : w1t n d (v.1 - d, v.2 - n) = w1t n d v := by
    unfold w1t; ring
  have eKs : w1s n d (v.1 - d, v.2 - n) = w1s n d v - w1T n d := by
    unfold w1s w1T; ring
  rw [eK, eKs, w1t_diff n d c v, w1s_diff n d c v] at hFV
  have hFH := freeHn_to_FHG hn hd hwF
  have eV : w1t n d (w.1 - (n - d), w.2 - (n + d)) = w1t n d w + w1T n d := by
    unfold w1t w1T; ring
  have eS : w1s n d (w.1 - (n - d), w.2 - (n + d)) = w1s n d w := by
    unfold w1s; ring
  rw [eV, eS, w1t_diff n d c w, w1s_diff n d c w] at hFH
  have hb1 := abs_le.mp hv1
  have hb2 := abs_le.mp hv2
  have hb3 := abs_le.mp hw1
  have hb4 := abs_le.mp hw2
  have hL' : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FVG n d (w1T n d) (w1t n d c + n * i - d * j)
        (w1s n d c + (d + n) * i + (d - n) * j - w1T n d) :=
    ⟨v.1 - c.1, v.2 - c.2, hb1.1, hb1.2, hb2.1, hb2.2, hFV⟩
  have hT' : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FHG n d (w1T n d) (w1t n d c + n * i - d * j + w1T n d) (w1s n d c + (d + n) * i + (d - n) * j) :=
    ⟨w.1 - c.1, w.2 - c.2, hb3.1, hb3.2, hb4.1, hb4.2, hFH⟩
  have hpt : w1t n d c = (-(w1T n d) + 2 * d) + n * (c.1 - n) - d * (c.2 - (2 * n + d - 2)) := by
    unfold w1t; rw [w1T_eq]; ring
  have hps : w1s n d c = (w1T n d - 2 * d + 2 * n) + (d + n) * (c.1 - n) + (d - n) * (c.2 - (2 * n + d - 2)) := by
    unfold w1s; rw [w1T_eq]; ring
  obtain ⟨h1, h2⟩ := class_minus_core n d (w1T n d) (w1t n d c) (w1s n d c)
    (c.1 - n) (c.2 - (2 * n + d - 2)) hn hd hn1 hnd hTL hT2 (w1T_eq n d) hpt hps hS' hL' hT'
  exact Prod.ext (by dsimp only; omega) (by dsimp only; omega)

end FLatticePaper.AlignedClassSite
