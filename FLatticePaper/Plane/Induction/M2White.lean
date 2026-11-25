import FLatticePaper.Plane.Induction.HardEast
import FLatticePaper.Plane.Induction.HderivEasy

/-! # The diagonal middle is white for `d ≥ 2n`, and hderiv in both regimes

For an even free V root `z` with `2n ≤ d`, the diagonal middle `M2 = (z.1 + 1, z.2 - 1)` is even, and its two horizontal
neighbours are the odd sites `y = (z.1, z.2 - 1)` and `u = (z.1 + 2, z.2 - 1)`. The grades are `s(M2) = s(z) + 2n`,
`s(y) = s(z) - (d - n)` and `s(u) = s(z) + d + 3n`, with `0 ≤ s(z) ≤ 2n` (`root_bounds`). The field is harmonic on the
even strip at `M2` and on the odd extension at `y` and `u` (`hS`, `hO`, from `Q30Strips`), so `laplacian G M2 = 0`.

The arithmetic needs `d ≥ 2n + 1`: `d = 2n` would force `n = 1`, `d = 2` for a coprime pair, which contradicts `3 ≤ d`. -/

namespace FLatticePaper.M2White

open FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.W1 FLatticePaper.W1NonfreeOut
open FLatticePaper.CentralForced

/-- `d ≠ 2n`: a coprime pair `(n, d)` with `d = 2n` forces `n = 1`, `d = 2`, which contradicts `3 ≤ d`. -/
theorem den_ne_two_num (frame : ChildFrame) : frame.child.den ≠ 2 * frame.child.num := by
  intro h
  obtain ⟨hn0, -, -, hd3, -⟩ := frame.child_facts
  obtain ⟨u, v, huv⟩ := frame.child_reduced
  rw [h] at huv
  have hdvd : frame.child.num ∣ 1 := ⟨u + 2 * v, by linear_combination -huv⟩
  have hle := Int.le_of_dvd one_pos hdvd
  omega

/-- **`M2` is white for `d ≥ 2n`.** The field is harmonic on the stencil of `M2` (its even strip at `M2`, its odd extension at
the two horizontal neighbours), so the Laplacian at `M2` is that of the harmonic grid, which is `0`. -/
theorem lap_M2_zero {G : Field} (frame : ChildFrame)
    (hS : ∀ x : Site, 2 - 2 * frame.child.den ≤ frame.sGrade x →
      frame.sGrade x ≤ 2 * (frame.child.den + frame.child.num) - 2 → G x = harmonicGrid x)
    (hO : ∀ x : Site, ¬ EvenSite x → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade x →
      frame.sGrade x ≤ 3 * frame.child.den + frame.child.num - 2 → G x = harmonicGrid x)
    {z : Site} (hz : z ∈ frame.freeV) (hev : EvenSite z) (hreg : 2 * frame.child.num ≤ frame.child.den) :
    laplacian G (z.1 + 1, z.2 - 1) = 0 := by
  obtain ⟨hn0, hnd, hdn, hd3, -⟩ := frame.child_facts
  obtain ⟨hs0, hs2, -, -⟩ := frame.root_bounds hz hev
  have hne := den_ne_two_num frame
  have hd1 : 2 * frame.child.num + 1 ≤ frame.child.den := by omega
  have hev' : (z.1 + z.2) % 2 = 0 := hev
  have hM2ev : EvenSite (z.1 + 1, z.2 - 1) := by
    show ((z.1 + 1) + (z.2 - 1)) % 2 = 0
    omega
  have hyodd : ¬ EvenSite (z.1, z.2 - 1) := by
    show ¬ ((z.1 + (z.2 - 1)) % 2 = 0)
    omega
  have hu2odd : ¬ EvenSite (z.1 + 2, z.2 - 1) := by
    show ¬ (((z.1 + 2) + (z.2 - 1)) % 2 = 0)
    omega
  have sM2 : frame.sGrade (z.1 + 1, z.2 - 1) = frame.sGrade z + 2 * frame.child.num := by
    unfold ChildFrame.sGrade
    ring
  have sy : frame.sGrade (z.1, z.2 - 1) = frame.sGrade z - (frame.child.den - frame.child.num) := by
    unfold ChildFrame.sGrade
    ring
  have su : frame.sGrade (z.1 + 2, z.2 - 1) = frame.sGrade z + (frame.child.den + 3 * frame.child.num) := by
    unfold ChildFrame.sGrade
    ring
  have hG1 : G (z.1 + 1, z.2 - 1) = harmonicGrid (z.1 + 1, z.2 - 1) :=
    hS _ (by rw [sM2]; omega) (by rw [sM2]; omega)
  have hG2 : G (z.1, z.2 - 1) = harmonicGrid (z.1, z.2 - 1) :=
    hO _ hyodd (by rw [sy]; omega) (by rw [sy]; omega)
  have hG3 : G (z.1 + 2, z.2 - 1) = harmonicGrid (z.1 + 2, z.2 - 1) :=
    hO _ hu2odd (by rw [su]; omega) (by rw [su]; omega)
  have n1 : incomingNeg (z.1 + 1, z.2 - 1) = (z.1, z.2 - 1) := by
    unfold incomingNeg
    rw [if_pos hM2ev]
    exact Prod.ext (by show z.1 + 1 - 1 = z.1; ring) rfl
  have n2 : incomingPos (z.1 + 1, z.2 - 1) = (z.1 + 2, z.2 - 1) := by
    unfold incomingPos
    rw [if_pos hM2ev]
    exact Prod.ext (by show z.1 + 1 + 1 = z.1 + 2; ring) rfl
  have hH := harmonicGrid_harmonic (z.1 + 1, z.2 - 1)
  unfold laplacian at hH ⊢
  rw [n1, n2] at hH ⊢
  rw [hG1, hG2, hG3]
  linarith

/-- **hderiv, east.** For `d ≥ 2n` the middle `M2` is white (`lap_M2_zero`), so `hderiv_easy` applies; for `d < 2n` the reflected
fan gives `M1 → M2` (`HardEast.hderiv_regime`), which needs `z ≠ vLast`. -/
theorem hderiv_east_full {G : Field} (frame : ChildFrame) (hP : frame.Packet G)
    (hprice : ∀ z ∈ frame.closedPolygon, frame.cutPrice - 1 ≤ frame.price G z ∧ frame.price G z ≤ frame.cutPrice)
    (hdrU : ∀ z, frame.price G (z + frame.child.modifiedDeck.kernel) = frame.price G z - 1)
    (hdrV : ∀ z, frame.price G (z + frame.child.modifiedDeck.transverse) = frame.price G z)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (hper : ∀ z : Site, G (z + (frame.child.den, frame.child.num)) = G z)
    (hI : ∀ z, G (reflectionI - z) = G z)
    (hS : ∀ x : Site, 2 - 2 * frame.child.den ≤ frame.sGrade x →
      frame.sGrade x ≤ 2 * (frame.child.den + frame.child.num) - 2 → G x = harmonicGrid x)
    (hO : ∀ x : Site, ¬ EvenSite x → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade x →
      frame.sGrade x ≤ 3 * frame.child.den + frame.child.num - 2 → G x = harmonicGrid x)
    {z : Site} (hz : z ∈ frame.freeV) (hev : EvenSite z) (hzF : z ≠ FLatticePaper.Induction.vFirst)
    (hzL : z ≠ frame.vLast ∨ 2 * frame.child.num ≤ frame.child.den)
    (hlapM1 : laplacian G (z.1 + 1, z.2) = 0) :
    FLatticePaper.SquareClauses.ForcedEdge G (fun _ _ => False) (z.1 + 1, z.2) (z.1 + 1, z.2 - 1) := by
  by_cases h : frame.child.den < 2 * frame.child.num
  · rcases hzL with hzL | hzL
    · exact FLatticePaper.HardEast.hderiv_regime frame hP hprice hdrU hdrV hW1 hper h hI hz hev hzF hzL
    · omega
  · exact hderiv_easy frame hW1 hz hev hzF hlapM1 (lap_M2_zero frame hS hO hz hev (by omega))

/-- **hderiv, west.** For `d ≥ 2n` the west middle's diagonal `(z.1 - 1, z.2 + 1)` is white: it is the image under the central
reflection `A = I + tr` of the east diagonal at the reflected root `A - z`, so `lap_M2_zero` at `A - z` and
`lap_cref_centre` give it. For `d < 2n` it is `HardEast.hderiv_west_regime`. -/
theorem hderiv_west_full {G : Field} (frame : ChildFrame) (hP : frame.Packet G)
    (hprice : ∀ z ∈ frame.closedPolygon, frame.cutPrice - 1 ≤ frame.price G z ∧ frame.price G z ≤ frame.cutPrice)
    (hdrU : ∀ z, frame.price G (z + frame.child.modifiedDeck.kernel) = frame.price G z - 1)
    (hdrV : ∀ z, frame.price G (z + frame.child.modifiedDeck.transverse) = frame.price G z)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (hper : ∀ z : Site, G (z + (frame.child.den, frame.child.num)) = G z)
    (hI : ∀ z, G (reflectionI - z) = G z)
    (hS : ∀ x : Site, 2 - 2 * frame.child.den ≤ frame.sGrade x →
      frame.sGrade x ≤ 2 * (frame.child.den + frame.child.num) - 2 → G x = harmonicGrid x)
    (hO : ∀ x : Site, ¬ EvenSite x → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade x →
      frame.sGrade x ≤ 3 * frame.child.den + frame.child.num - 2 → G x = harmonicGrid x)
    {z : Site} (hz : z ∈ frame.freeV) (hev : EvenSite z) (hzF : z ≠ FLatticePaper.Induction.vFirst)
    (hzL : z ≠ frame.vLast)
    (hlapM1 : laplacian G (z.1 - 1, z.2) = 0) :
    FLatticePaper.SquareClauses.ForcedEdge G (fun _ _ => False) (z.1 - 1, z.2) (z.1 - 1, z.2 + 1) := by
  by_cases h : frame.child.den < 2 * frame.child.num
  · exact FLatticePaper.HardEast.hderiv_west_regime frame hP hprice hdrU hdrV hW1 hper h hI hz hev hzF hzL
  · obtain ⟨hw, hwev, -⟩ := cref_freeV frame hz hev hzF hzL
    have hM2w := lap_M2_zero frame hS hO hw hwev (by omega)
    have e : cref (reflectionI + frame.child.modifiedDeck.transverse)
        ((cref (reflectionI + frame.child.modifiedDeck.transverse) z).1 + 1,
          (cref (reflectionI + frame.child.modifiedDeck.transverse) z).2 - 1) = (z.1 - 1, z.2 + 1) := by
      exact Prod.ext (by simp only [cref]; try ring) (by simp only [cref]; try ring)
    have hlapM2 : laplacian G (z.1 - 1, z.2 + 1) = 0 := by
      rw [← e, lap_cref_centre frame hI hP.periods]
      exact hM2w
    exact hderiv_west frame hW1 hI hP.periods hz hev hzF hzL hlapM1 hlapM2

end FLatticePaper.M2White
