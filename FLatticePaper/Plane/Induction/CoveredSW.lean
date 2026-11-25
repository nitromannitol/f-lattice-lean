import FLatticePaper.Plane.Induction.ReflectedFan
import FLatticePaper.Plane.Induction.WestSelect
import FLatticePaper.Plane.Induction.W1Strips
import FLatticePaper.Plane.Induction.ShapeOneGeom
import FLatticePaper.Plane.Induction.ShortRoute

/-! # Coverage of the west arrow `z+S → z+SW` at every covered odd H root (Q32 he1, coverage lemma)

If `d < 3n − 2` the south neighbour `y = z+SW+(0,−1)` of `z+SW` has `t(y) ≤ 2(d+n) − 2`, so it lies in the even zero window
(`W1Strips.even_zero_full`), and `z+SW`, `z+W` lie in the ordinary zero strip: `z+SW` is white. Contrapositively, a black `z+SW`
forces `d ≥ 3n − 2`, and then the depth bounds of the reflected fan hold with `K = ⌊(3d+3n−1)/(2n)⌋`.
`G(z+S) = 0` comes from the ordinary zero strip. -/

namespace FLatticePaper.CoveredSW

open FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.W1 FLatticePaper.ShortRoute
  FLatticePaper.ShapeOneGeom FLatticePaper.ReflectedFan

/-- **Short roots have white `z+SW`.** For `d < 3n − 2` the corner `z+SW` of an odd free H root is white. -/
theorem sw_white_of_small_d {frame : ChildFrame} {F : Field}
    (hper : HasGeneratorPeriods frame.child F 0 frame.coherentConstantV)
    (hstrips : frame.HasStrips F)
    (hslip : ∀ z ∈ frame.closedPolygon, 0 ≤ frame.slip F 1 z)
    (hseed : ∀ z : Site, EvenSite z → frame.tGrade z = 2 - (frame.child.den + frame.child.num) → F z = 0)
    (hIsym : ∀ z : Site, F (FLatticePaper.W1Strips.iRefl z) = F z)
    {z : Site} (hz : z ∈ frame.freeH) (hodd : ¬ EvenSite z) (hne : z ≠ frame.hLast)
    (hbt : frame.child.num + 2 ≤ frame.tGrade z)
    (hd : frame.child.den < 3 * frame.child.num - 2) :
    laplacian F (z.1 - 1, z.2 - 1) = 0 := by
  have ht := freeH_tGrade_add_two_le frame hz hodd hne
  obtain ⟨hn1, hnd, hdn, hd3, hP⟩ := frame.child_facts
  have hodd' : (z.1 + z.2) % 2 = 1 := by
    unfold EvenSite at hodd
    omega
  have hSW : ¬ EvenSite (z.1 - 1, z.2 - 1) := by
    unfold EvenSite
    dsimp only
    omega
  have hpYe : EvenSite (z.1 - 1, z.2 - 1 - 1) := by
    unfold EvenSite
    dsimp only
    omega
  have htS : frame.tGrade (z.1 - 1, z.2 - 1) = frame.tGrade z - frame.child.num + frame.child.den := by
    unfold ChildFrame.tGrade
    dsimp only
    ring
  have htW : frame.tGrade (z.1 - 1, z.2 - 1 + 1) = frame.tGrade z - frame.child.num := by
    unfold ChildFrame.tGrade
    dsimp only
    ring
  have htY : frame.tGrade (z.1 - 1, z.2 - 1 - 1) = frame.tGrade z - frame.child.num + 2 * frame.child.den := by
    unfold ChildFrame.tGrade
    dsimp only
    ring
  have hpS0 : F (z.1 - 1, z.2 - 1) = 0 := zero_of_tGrade hstrips (by omega) (by omega)
  have hpW0 : F (z.1 - 1, z.2 - 1 + 1) = 0 := zero_of_tGrade hstrips (by omega) (by omega)
  have hpY0 : F (z.1 - 1, z.2 - 1 - 1) = 0 :=
    FLatticePaper.W1Strips.even_zero_full frame hper hstrips hslip hseed hIsym (z.1 - 1, z.2 - 1 - 1) hpYe
      (by omega) (by omega)
  unfold laplacian incomingNeg incomingPos
  simp only [if_neg hSW]
  rw [hpY0, hpS0, hpW0]
  ring

/-- **`z+S` is a zero of the field.** The ordinary zero strip contains `t(z+S) = t(z) + d`. -/
theorem start_contact_zero {frame : ChildFrame} {F : Field} (hstrips : frame.HasStrips F) {z : Site}
    (hz : z ∈ frame.freeH) (hodd : ¬ EvenSite z) (hne : z ≠ frame.hLast) (hbt : frame.child.num + 2 ≤ frame.tGrade z) :
    F (z.1, z.2 - 1) = 0 := by
  have ht := freeH_tGrade_add_two_le frame hz hodd hne
  obtain ⟨hn1, hnd, hdn, hd3, hP⟩ := frame.child_facts
  have htS : frame.tGrade (z.1, z.2 - 1) = frame.tGrade z + frame.child.den := by
    unfold ChildFrame.tGrade
    dsimp only
    ring
  exact zero_of_tGrade hstrips (by omega) (by omega)

/-- **The depth bounds of the reflected fan from `d ≥ 3n − 2`.** With `K = ⌊(3d+3n−1)/(2n)⌋`: `2 ≤ K`, `d + 2n − 1 ≤ nK`, and
`2nK ≤ 3d + 5n − 1`. -/
theorem K_bounds_of_three_n {n d : ℤ} (hn : 1 ≤ n) (hd : 3 * n - 2 ≤ d) :
    ∃ K : ℕ, 2 ≤ K ∧ d + 2 * n - 1 ≤ n * (K : ℤ) ∧ 2 * n * (K : ℤ) ≤ 3 * d + 5 * n - 1 := by
  have hmpos : 0 < 2 * n := by omega
  have hXnn : 0 ≤ 3 * d + 3 * n - 1 := by omega
  have hmod := Int.emod_def (3 * d + 3 * n - 1) (2 * n)
  have hmnn := Int.emod_nonneg (3 * d + 3 * n - 1) (ne_of_gt hmpos)
  have hmlt := Int.emod_lt_of_pos (3 * d + 3 * n - 1) hmpos
  obtain ⟨K0, hK0⟩ : ∃ K0 : ℤ, K0 = (3 * d + 3 * n - 1) / (2 * n) := ⟨_, rfl⟩
  have hK0nn : 0 ≤ K0 := by
    rw [hK0]
    exact Int.ediv_nonneg hXnn (le_of_lt hmpos)
  rw [← hK0] at hmod
  have h1 : 2 * n * K0 ≤ 3 * d + 3 * n - 1 := by linarith
  have h2 : 3 * d + 3 * n - 1 < 2 * n * K0 + 2 * n := by linarith
  have hK2i : 2 ≤ K0 := by
    by_contra hlt
    have hK1 : K0 ≤ 1 := by omega
    nlinarith
  have hcast : ((K0.toNat : ℕ) : ℤ) = K0 := Int.toNat_of_nonneg hK0nn
  refine ⟨K0.toNat, by omega, ?_, ?_⟩
  · rw [hcast]
    nlinarith
  · rw [hcast]
    linarith

/-- **The west arrow `z+S → z+SW` at a covered odd H root**, in both colours of `z+SW`: white `z+SW` is the square case
(`forcedEdge_SW`); black `z+SW` forces `d ≥ 3n − 2` (`sw_white_of_small_d`), where the reflected fan applies
(`forcedEdge_he1`, with the depth bounds of `K_bounds_of_three_n`). The named inputs are the all-slope cap ray `hAS` (for the
depth `K`), the field symmetry `hsym`, the W1 forcing `hW1`, and the packet and strip inputs `hper`, `hslip`, `hseed`, `hIsym`. -/
theorem he1_covered {frame : ChildFrame} {G : Field} (hP : frame.Packet G)
    (hsig : ∀ w ∈ frame.closedPolygon, G w - G (w - frame.shortShift) ≤ 0)
    (hAS : ∀ K : ℕ, 2 ≤ K → frame.child.den + 2 * frame.child.num - 1 ≤ frame.child.num * (K : ℤ) →
      2 * frame.child.num * (K : ℤ) ≤ 3 * frame.child.den + 5 * frame.child.num - 1 →
      ∃ p q : ℤ, frame.child.num * p - frame.child.den * q = 2 - frame.child.num ∧
        ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ G (p + (k : ℤ), q + (k : ℤ)))
    (hsym : ∀ y, G (reflH frame y) = G y)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (hper : HasGeneratorPeriods frame.child G 0 frame.coherentConstantV)
    (hstrips : frame.HasStrips G)
    (hslip : ∀ z ∈ frame.closedPolygon, 0 ≤ frame.slip G 1 z)
    (hseed : ∀ z : Site, EvenSite z → frame.tGrade z = 2 - (frame.child.den + frame.child.num) → G z = 0)
    (hIsym : ∀ z : Site, G (FLatticePaper.W1Strips.iRefl z) = G z)
    {z : Site} (hz : z ∈ frame.freeH) (hodd : ¬ EvenSite z) (hne : z ≠ frame.hLast)
    (hbt : frame.child.num + 2 ≤ frame.tGrade z)
    (hzS : laplacian G (z.1, z.2 - 1) = 0) :
    ForcedEdge G (fun _ _ => False) (z.1, z.2 - 1) (z.1 - 1, z.2 - 1) := by
  obtain ⟨hn1, -, -, -, -⟩ := frame.child_facts
  by_cases hSW : laplacian G (z.1 - 1, z.2 - 1) = 0
  · exact FLatticePaper.WestSelect.forcedEdge_SW hP hW1 hz hodd hne hbt hzS hSW
  · have hd : 3 * frame.child.num - 2 ≤ frame.child.den := by
      by_contra h
      exact hSW (sw_white_of_small_d hper hstrips hslip hseed hIsym hz hodd hne hbt (by omega))
    obtain ⟨K, hK2, hKs, hKr⟩ := K_bounds_of_three_n (by omega) hd
    obtain ⟨p, q, hs, hcap⟩ := hAS K hK2 hKs hKr
    exact forcedEdge_he1 hP hsig hs hK2 hKs hKr hcap hsym hW1 hz hodd hne hbt
      (start_contact_zero hstrips hz hodd hne hbt)

end FLatticePaper.CoveredSW
