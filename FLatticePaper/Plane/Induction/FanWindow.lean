import FLatticePaper.Plane.Induction.FanStart
import FLatticePaper.Plane.Induction.RotatedMono
import FLatticePaper.Plane.Induction.CapRayGrades
import FLatticePaper.Plane.Induction.RouteStay

/-! # The cone window of the rotated fan at an even free V entry (Q41 section 3)

For an even free V entry `w` with `1 ≤ w_2 ≤ L − 2` in a hard-type frame (`n ≥ 3`, `n + 2 ≤ d < 2n`), the rotated residual field
`quarterTurnField G` (`G` a field with the frame's packet, prices and drifts) is a window on the cone of apex `(w_2 + 1, −w_1)`
over `resRegion n d` at some depth `K ≥ 2`: the ray cap (`RotatedMono.rotated_ray_cap_mono`) and the cone window (`CapConeGrades.cone_window_NL`)
are instantiated at the coprime pair `(N, D) = ((d−n)/2, (d+n)/2)`, the ray start `(p, q)` with `a = 1` (`CapRayGrades.ray_start_odd`), and
the depth `K` of `RotatedForced.K_bounds_rot`. -/

namespace FLatticePaper.FanWindow

open FLatticePaper FLatticePaper.Induction FLatticePaper.RotatedForced FLatticePaper.CapRay FLatticePaper.ContactCone
  FLatticePaper.CapConeGrades FLatticePaper.RotatedCap FLatticePaper.W1 FLatticePaper.RotatedMono FLatticePaper.CapRayGrades
  FLatticePaper.FanPropagation

theorem entry_window (frame : ChildFrame) {G : Field} (hP : frame.Packet G)
    (hprice : ∀ z ∈ frame.closedPolygon, frame.cutPrice - 1 ≤ frame.price G z ∧ frame.price G z ≤ frame.cutPrice)
    (hdrU : ∀ z, frame.price G (z + frame.child.modifiedDeck.kernel) = frame.price G z - 1)
    (hdrV : ∀ z, frame.price G (z + frame.child.modifiedDeck.transverse) = frame.price G z)
    (hd2 : frame.child.den < 2 * frame.child.num)
    {N D : ℤ} (hN2 : 2 * N = frame.child.den - frame.child.num) (hD2 : 2 * D = frame.child.den + frame.child.num)
    (hN0 : 0 < N) (hND : N < D)
    {w : Site} (hF : w ∈ frame.freeV) (he : EvenSite w) (h1 : 1 ≤ w.2)
    (h2 : w.2 ≤ frame.child.den + frame.child.num - 2) :
    ∃ K : ℕ, 2 ≤ K ∧ WindowOn (fun x => resRegion frame.child.num frame.child.den x ∧ ConeRoot (w.2 + 1, -w.1) K x)
      (quarterTurnField G) (fun i => parabolaField (-w.1) i) := by
  have H := rotated_NL hP hprice hdrU hdrV N D hN2 hD2 hN0 hND
  have hcop : IsCoprime N D := coprime_residual frame N D hN2.symm hD2.symm
  have hodd : (D + N) % 2 = 1 := by
    obtain ⟨hon, hod⟩ := frame.child_odd
    omega
  obtain ⟨p, q, hs, hpq⟩ := ray_start_odd N D 1 hcop hodd
  obtain ⟨J, hJ1, hJ2⟩ := exists_floor_window (2 * N) (N + D - 2) (by omega) (by omega)
  obtain ⟨K, hK2, hKlo, hKhi⟩ := K_bounds_rot (N := N) (D := D) (by omega) (by omega)
  have hcap := rotated_ray_cap_mono hP hprice hdrU hdrV N D 1 le_rfl (by norm_num) hN2 hD2 hN0 hND hs hpq J K
    hJ1 hJ2 hKhi
  obtain ⟨hs1, -⟩ := RouteStay.even_grade_strict frame hF he h1 h2
  rw [frame_sGrade_eq] at hs1
  have hsw : w1s frame.child.num frame.child.den w = 2 * D * w.1 + 2 * N * w.2 := by
    unfold w1s
    linear_combination (-(w.1 : ℤ)) * hD2 + (-(w.2 : ℤ)) * hN2
  have hb : N + 1 ≤ N * (w.2 + 1) - D * (-w.1) := by nlinarith [hsw, hs1, hN0]
  refine ⟨K, hK2, ?_⟩
  have hwin := cone_window_NL H (w1T frame.child.num frame.child.den) hN0 hND (by norm_num) hs hpq K hcap
    (w.2 + 1, -w.1) hb
  intro x hx i hi
  exact hwin x ⟨resRegion_sub_ropen (by omega) (by omega) hN0 hND x hx.1, hx.2⟩ i hi

/-- The ray data of the residual cap at an even free V entry: the depth, the ray start, the cap and the apex inequality. -/
theorem entry_data (frame : ChildFrame) {G : Field} (hP : frame.Packet G)
    (hprice : ∀ z ∈ frame.closedPolygon, frame.cutPrice - 1 ≤ frame.price G z ∧ frame.price G z ≤ frame.cutPrice)
    (hdrU : ∀ z, frame.price G (z + frame.child.modifiedDeck.kernel) = frame.price G z - 1)
    (hdrV : ∀ z, frame.price G (z + frame.child.modifiedDeck.transverse) = frame.price G z)
    (hd2 : frame.child.den < 2 * frame.child.num)
    {N D : ℤ} (hN2 : 2 * N = frame.child.den - frame.child.num) (hD2 : 2 * D = frame.child.den + frame.child.num)
    (hN0 : 0 < N) (hND : N < D)
    {w : Site} (hF : w ∈ frame.freeV) (he : EvenSite w) (h1 : 1 ≤ w.2)
    (h2 : w.2 ≤ frame.child.den + frame.child.num - 2) :
    ∃ K : ℕ, ∃ p q : ℤ, 2 ≤ K ∧ N * p - D * q = 1 - N ∧ (p + q) % 2 = 1 ∧
      4 * N + 2 * D - 1 ≤ 2 * N * (K : ℤ) ∧ 2 * N * (K : ℤ) ≤ 3 * D + 5 * N - 1 ∧
      (∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ quarterTurnField G (p + (k : ℤ), q + (k : ℤ))) ∧
      N + 1 ≤ N * (w.2 + 1) - D * (-w.1) := by
  have hcop : IsCoprime N D := coprime_residual frame N D hN2.symm hD2.symm
  have hodd : (D + N) % 2 = 1 := by
    obtain ⟨hon, hod⟩ := frame.child_odd
    omega
  obtain ⟨p, q, hs, hpq⟩ := ray_start_odd N D 1 hcop hodd
  obtain ⟨J, hJ1, hJ2⟩ := exists_floor_window (2 * N) (N + D - 2) (by omega) (by omega)
  obtain ⟨K, hK2, hKlo, hKhi⟩ := K_bounds_rot (N := N) (D := D) (by omega) (by omega)
  have hcap := rotated_ray_cap_mono hP hprice hdrU hdrV N D 1 le_rfl (by norm_num) hN2 hD2 hN0 hND hs hpq J K
    hJ1 hJ2 hKhi
  obtain ⟨hs1, -⟩ := RouteStay.even_grade_strict frame hF he h1 h2
  rw [frame_sGrade_eq] at hs1
  have hsw : w1s frame.child.num frame.child.den w = 2 * D * w.1 + 2 * N * w.2 := by
    unfold w1s
    linear_combination (-(w.1 : ℤ)) * hD2 + (-(w.2 : ℤ)) * hN2
  have hb : N + 1 ≤ N * (w.2 + 1) - D * (-w.1) := by nlinarith [hsw, hs1, hN0]
  exact ⟨K, p, q, hK2, hs, hpq, hKlo, by omega, hcap, hb⟩

end FLatticePaper.FanWindow
