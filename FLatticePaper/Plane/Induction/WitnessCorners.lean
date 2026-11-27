import FLatticePaper.Plane.Induction.TopSquare
import FLatticePaper.Plane.Induction.PairClass
import FLatticePaper.Plane.Induction.ColourPacket
import FLatticePaper.Plane.Induction.CollarOneOne
import FLatticePaper.Plane.Induction.WitnessPairs
import FLatticePaper.Plane.Induction.ChildNumerator
import FLatticePaper.Plane.Induction.CollarChain
import FLatticePaper.Plane.Induction.AlignedClassSite

/-! # The corner pairs of the witness dichotomy at strict white centres

The corner pairs of `CollarChain.WitnessDichotomy` are excluded at a strict interior centre `c` with `laplacian (MW word) c = 0`:

* top with aligned: `classify_plus` (eps = +1, aligned = left) or `classify_minus` (eps = -1, aligned = right) puts `c` at the
  black site `vLast + (1,0) = (n-d+2, n+d-1)` resp. `R - (1,1) = (n, 2n+d-2)`, whose laplacian is `-1`;
* opposite with bottom: `right_bottom_centre` (eps = +1, opposite = right) puts `c` at the black site `(d-1, n)`, and
  `left_bottom_centre` (eps = -1, opposite = left) at the black site `(1,1)`.

The pairs top with bottom and left with right are the grade pairs of `WitnessPairs`, and opposite with aligned is a pair of vertical
faces. Together these prove the full dichotomy at strict white centres (no collar hypothesis). -/

namespace FLatticePaper.WitnessCorners

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.FaceWitness FLatticePaper.W1 FLatticePaper.W1MSheet FLatticePaper.TopSquare

/-- **Top with aligned, at a strict white centre.** -/
theorem top_aligned_white (word : Word) (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) {c : Site}
    (hc : W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hM : laplacian (MW word) c = 0) (hT : TopWit (frameAt word) c) (hA : AlignedWit (frameAt word) c) : False := by
  obtain ⟨hnO, hdO⟩ := (frameAt word).child_odd
  obtain ⟨hn0, hnd1, hd2, -, -⟩ := (frameAt word).child_facts
  have hn1 : 1 ≤ (frameAt word).child.num := by omega
  have hnd : (frameAt word).child.num + 2 ≤ (frameAt word).child.den := by omega
  have hTL : 2 * ((frameAt word).child.den + (frameAt word).child.num) <
      w1T (frameAt word).child.num (frameAt word).child.den := by
    have := FLatticePaper.Exceptions.period_ge2 hn1 hnd
    omega
  rcases hA with ⟨-, hL⟩ | ⟨-, hR⟩
  · have hcC := FLatticePaper.AlignedClassSite.classify_plus hnO hdO hn1 hnd hTL c hc (leftWit_site hL) (topWit_site hT)
    have hcE : c = ((frameAt word).vLast.1 + 1, (frameAt word).vLast.2) := by
      rw [hcC]
      refine Prod.ext ?_ ?_
      · simp only [ChildFrame.vLast]; ring
      · simp only [ChildFrame.vLast]
    have hl := FLatticePaper.ColourPacket.lap_MW_vLast hw hSE
    rw [hcE, hl] at hM
    norm_num at hM
  · have hcC := FLatticePaper.AlignedClassSite.classify_minus hnO hdO hn1 hnd hTL c hc (rightWit_site hR) (topWit_site hT)
    have hl := FLatticePaper.ColourPacket.lap_MW_R hw hSE
    rw [hcC, hl] at hM
    norm_num at hM

/-- **Opposite with bottom, at a strict white centre.** -/
theorem opposite_bottom_white (word : Word) (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) {c : Site}
    (hc : W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hM : laplacian (MW word) c = 0) (hO : OppositeWit (frameAt word) c) (hB : BottomWit (frameAt word) c) : False := by
  rcases hO with ⟨-, hR⟩ | ⟨-, hL⟩
  · have hcE := FLatticePaper.PairClass.right_bottom_centre (frameAt word) hc hR hB
    have hl := FLatticePaper.ColourPacket.lap_MW_dn1 hw hSE
    rw [hcE, hl] at hM
    norm_num at hM
  · have hcE := FLatticePaper.PairClass.left_bottom_centre (frameAt word) hc hL hB
    have hl := FLatticePaper.Induction.laplacian_MW_one_one hw hSE
    rw [hcE, hl] at hM
    norm_num at hM

/-- **Opposite with aligned.** Both are vertical faces, of opposite sides (`eps` fixed). -/
theorem opposite_aligned (word : Word) (hn3 : 3 ≤ (frameAt word).child.num) {c : Site}
    (hO : OppositeWit (frameAt word) c) (hA : AlignedWit (frameAt word) c) : False := by
  rcases hO with ⟨hε, hR⟩ | ⟨hε, hL⟩
  · rcases hA with ⟨-, hL'⟩ | ⟨hε', -⟩
    · exact FLatticePaper.WitnessPairs.not_left_right (frameAt word) hn3 hL' hR
    · rw [hε] at hε'
      norm_num at hε'
  · rcases hA with ⟨hε', -⟩ | ⟨-, hR'⟩
    · rw [hε] at hε'
      norm_num at hε'
    · exact FLatticePaper.WitnessPairs.not_left_right (frameAt word) hn3 hL hR'

/-- **The witness dichotomy at strict white centres.** Every strict interior centre `c` with `laplacian (MW word) c = 0` has no pair
`(top or opposite, bottom or aligned)`. -/
theorem witnessDichotomy (word : Word) (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) : CollarChain.WitnessDichotomy word := by
  intro c hc hM hcontra
  have hn3 := FLatticePaper.Induction.child_num_ge_three hw
  obtain ⟨hTO, hBA⟩ := hcontra
  rcases hTO with hT | hO
  · rcases hBA with hB | hA
    · exact FLatticePaper.WitnessPairs.not_bottom_top (frameAt word) hB hT
    · exact top_aligned_white word hw hSE hc hM hT hA
  · rcases hBA with hB | hA
    · exact opposite_bottom_white word hw hSE hc hM hO hB
    · exact opposite_aligned word hn3 hO hA

end FLatticePaper.WitnessCorners
