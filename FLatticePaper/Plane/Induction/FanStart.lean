import FLatticePaper.Plane.Induction.RotatedForced
import FLatticePaper.Plane.Induction.CapConeGrades
import FLatticePaper.Plane.Induction.ConeRoot
import FLatticePaper.Plane.Induction.ContactCone
import FLatticePaper.Plane.Induction.RouteStay
import FLatticePaper.Plane.Induction.ArcRanges
import FLatticePaper.Plane.Induction.ShortPassages
import FLatticePaper.Plane.Induction.W1Constructor

/-! # The start of the rotated fan (Q41 section 3, "Verification of the apex and start")

For an even free V entry `w` with `1 ≤ w_2 ≤ L − 2`, the apex is `b = (w_2 + 1, −w_1)` and the start is `v₀ = (w_2 + 1, 1 − w_1)`
(so `Zs v₀ = w + (−1, 0)`). In a frame with `n ≥ 3` and `n + 2 ≤ d`, the start lies in the residual region `resRegion n d`,
satisfies `ConeRoot b K` for `K ≥ 2`, and is a contact of the rotated residual `quarterTurnField F` when the residual cap holds. -/

namespace FLatticePaper.FanStart

open FLatticePaper FLatticePaper.Induction FLatticePaper.RotatedForced FLatticePaper.CapRay FLatticePaper.ContactCone
  FLatticePaper.CapConeGrades FLatticePaper.RotatedCap FLatticePaper.W1

/-- The start lies in the residual region. -/
theorem start_resRegion (frame : ChildFrame) (hn3 : 3 ≤ frame.child.num)
    (hnd : frame.child.num + 2 ≤ frame.child.den)
    {w : Site} (hF : w ∈ frame.freeV) (he : EvenSite w)
    (h1 : 1 ≤ w.2) (h2 : w.2 ≤ frame.child.den + frame.child.num - 2) :
    resRegion frame.child.num frame.child.den (w.2 + 1, 1 - w.1) := by
  obtain ⟨hodd_n, hodd_d⟩ := frame.child_odd
  obtain ⟨hs1, hs2⟩ := RouteStay.even_grade_strict frame hF he h1 h2
  have ht := ArcRanges.arc_even_range frame hF he
    (by intro h; rw [h] at h1; simp [FLatticePaper.Induction.vFirst] at h1)
    (by intro h; rw [h] at h2; simp [ChildFrame.vLast] at h2; omega)
  have hT3 := ShortPassages.T_ge frame
  rw [frame_periodDenominator_eq] at hT3 ht
  rw [frame_tGrade_eq] at ht
  rw [frame_sGrade_eq] at hs1 hs2
  show FLatticePaper.W1.StrictInterior frame.child.num frame.child.den
    (-(1 - w.1) + frame.child.den, w.2 + 1 - 1 + frame.child.num)
  have e : (-(1 - w.1) + frame.child.den, w.2 + 1 - 1 + frame.child.num) =
      (w.1 - 1 + frame.child.den, w.2 + frame.child.num) :=
    Prod.ext (by ring) (by ring)
  rw [e]
  have hodd : ¬ EvenSite (w.1 - 1 + frame.child.den, w.2 + frame.child.num) := by
    unfold EvenSite at he ⊢
    simp only at he ⊢
    omega
  have ht0 : w1t frame.child.num frame.child.den (w.1 - 1 + frame.child.den, w.2 + frame.child.num) =
      w1t frame.child.num frame.child.den w - frame.child.num := by
    unfold w1t; ring
  have hs0 : w1s frame.child.num frame.child.den (w.1 - 1 + frame.child.den, w.2 + frame.child.num) =
      w1s frame.child.num frame.child.den w +
        (w1T frame.child.num frame.child.den - (frame.child.den + frame.child.num)) := by
    unfold w1s w1T; ring
  unfold FLatticePaper.W1.StrictInterior
  simp only [w1b, w1a, w1c, w1h, if_neg hodd, ht0, hs0]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [ht.1, ht.2, hs1, hs2, hT3]

/-- The start is a `ConeRoot` of the apex `b = (w_2 + 1, −w_1)` at depth `K ≥ 2`. -/
theorem start_coneRoot {w : Site} (he : EvenSite w) {K : ℕ} (hK : 2 ≤ K) :
    ConeRoot (w.2 + 1, -w.1) K (w.2 + 1, 1 - w.1) := by
  unfold EvenSite at he
  have hv : EvenSite (w.2 + 1, 1 - w.1) := by
    unfold EvenSite
    simp only
    omega
  refine ⟨?_, ?_, fun _ => ?_, fun h => absurd hv h⟩
  · simp only; omega
  · simp only; omega
  · simp only; omega

/-- The start is a contact of the rotated residual field, when the residual cap holds at its rotated grade. -/
theorem start_contact (frame : ChildFrame) {G : Field} {N D : ℤ} (H : NLCap N D (quarterTurnField G))
    (hN : 2 * N = frame.child.den - frame.child.num) (hD : 2 * D = frame.child.den + frame.child.num)
    (hN0 : 0 < N) (hn3 : 3 ≤ frame.child.num)
    {w : Site} (hF : w ∈ frame.freeV) (he : EvenSite w)
    (h1 : 1 ≤ w.2) (h2 : w.2 ≤ frame.child.den + frame.child.num - 2) :
    quarterTurnField G (w.2 + 1, 1 - w.1) = parabolaField (-w.1) (w.2 + 1, 1 - w.1) := by
  obtain ⟨hs1, hs2⟩ := RouteStay.even_grade_strict frame hF he h1 h2
  rw [frame_sGrade_eq] at hs1 hs2
  have hsw : w1s frame.child.num frame.child.den w = 2 * D * w.1 + 2 * N * w.2 := by
    unfold w1s
    linear_combination (-(w.1 : ℤ)) * hD + (-(w.2 : ℤ)) * hN
  have hn : frame.child.num < D := by omega
  have hz := H.zero (w.2 + 1, 1 - w.1)
    (by simp only; nlinarith [hsw, hs1, hN0])
    (by simp only; nlinarith [hsw, hs2, hn, hN0])
  rw [hz]
  have hv : (w.2 + 1, 1 - w.1).2 - (-w.1) = 1 := by simp only; ring
  unfold parabolaField
  rw [hv]
  norm_num [FLatticePaper.QuadraticCap.capMin]

end FLatticePaper.FanStart
