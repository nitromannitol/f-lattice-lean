import FLatticePaper.Plane.Induction.ReflectedFan
import FLatticePaper.Plane.Induction.CoveredSW
import FLatticePaper.Plane.Induction.WestSelect
import FLatticePaper.Plane.Induction.WestForced
import FLatticePaper.Plane.Induction.ShortRoute
import FLatticePaper.Plane.Induction.ShapeOneGeom
import FLatticePaper.Plane.Induction.CapRay
import FLatticePaper.Plane.Induction.W1Exit
import FLatticePaper.Plane.Induction.AllBranchFan
import FLatticePaper.Plane.Induction.ReturnPrescribed
import FLatticePaper.Plane.Induction.NativeCases
import FLatticePaper.Plane.Induction.FanInputs

/-! # The north fan of an odd free H root: the `h3` second arrow (the H midpoint of section B)

For an odd free H root `b` (`b ≠ hFirst`, `b ≠ hLast`) with `t(b) ≥ n + 2`, the north neighbour `m = b + (0, 1)` is an even strictly interior
point with zero field value (its `t`-grade `t(b) − d` lies in the zero band). The all-branch contact fan of the cone of base `b` starts at
`m` (`ConeRoot`, the cap value `capMin 1 = 0`), so its forced edge is its east input (`fan_start_forced`), and `m → m + (1, 0)` is the
arrow `h3` asks for, when `z = b + (1, 0)` is the even free H root of the row. -/

namespace FLatticePaper.RouteFan

open FLatticePaper FLatticePaper.Induction FLatticePaper.W1 FLatticePaper.W1NonfreeOut FLatticePaper.W1Witness
  FLatticePaper.ReturnPrescribed FLatticePaper.ReflectedFan FLatticePaper.AllBranchFan FLatticePaper.CapRay
  FLatticePaper.FanPropagation FLatticePaper.WestSelect FLatticePaper.SquareClauses FLatticePaper.ContactCone

/-- **The north neighbour of an odd free H root is strictly interior** (`b ≠ hLast`, `n + 2 ≤ t(b)`): with `t = t(b)`, `s = s(b)`,
`t(b + N) = t − d` and `s(b + N) = s + (d − n)`; the box `1 ≤ x ≤ d`, `0 ≤ y ≤ n − 1` gives `s < T − d + n` off `hLast`. -/
theorem north_strict {frame : ChildFrame} {b : Site} (hz : b ∈ frame.freeH) (hodd : ¬ EvenSite b)
    (hne : b ≠ frame.hLast) (hbt : frame.child.num + 2 ≤ frame.tGrade b) :
    StrictInterior frame.child.num frame.child.den (b.1, b.2 + 1) := by
  obtain ⟨hn1, hnd, hdn, hd3, hP⟩ := frame.child_facts
  have hTd : frame.child.periodDenominator
      = frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2 := rfl
  obtain ⟨hx1, hxd, hy0, hyn⟩ := FLatticePaper.Induction.FreeTraceBox.freeH_box frame hz
  have ht2 := FLatticePaper.ShortRoute.freeH_tGrade_add_two_le frame hz hodd hne
  have hsb := FLatticePaper.WestForced.sGrade_odd_H_big hz hodd hne hbt
  have hev : EvenSite (b.1, b.2 + 1) := by
    unfold EvenSite at hodd ⊢
    omega
  have hTbig : 2 * frame.child.den < frame.child.periodDenominator := by
    rw [hTd]
    nlinarith [mul_nonneg (show (0:ℤ) ≤ frame.child.den - frame.child.num - 2 by omega)
      (show (0:ℤ) ≤ frame.child.den + frame.child.num by omega),
      mul_pos hn1 (show (0:ℤ) < frame.child.den by omega)]
  have hs_up : frame.sGrade b < frame.child.periodDenominator - frame.child.den + frame.child.num := by
    rw [hTd]
    unfold ChildFrame.sGrade
    rcases lt_or_eq_of_le hxd with hlt | heq
    · nlinarith [mul_le_mul_of_nonneg_left (show b.1 ≤ frame.child.den - 1 by omega)
        (show (0:ℤ) ≤ frame.child.den + frame.child.num by omega),
        mul_le_mul_of_nonneg_left hyn (show (0:ℤ) ≤ frame.child.den - frame.child.num by omega)]
    · have hyl : b.2 ≤ frame.child.num - 2 := by
        by_contra hc
        apply hne
        have h1 : b.2 = frame.child.num - 1 := by omega
        unfold ChildFrame.hLast
        exact Prod.ext heq h1
      nlinarith [mul_le_mul_of_nonneg_left hyl (show (0:ℤ) ≤ frame.child.den - frame.child.num by omega)]
  have htw : FLatticePaper.W1.w1t frame.child.num frame.child.den (b.1, b.2 + 1)
      = frame.tGrade b - frame.child.den := by
    unfold FLatticePaper.W1.w1t ChildFrame.tGrade
    ring
  have hsw : FLatticePaper.W1.w1s frame.child.num frame.child.den (b.1, b.2 + 1)
      = frame.sGrade b + (frame.child.den - frame.child.num) := by
    unfold FLatticePaper.W1.w1s ChildFrame.sGrade
    ring
  have hTw : FLatticePaper.W1.w1T frame.child.num frame.child.den = frame.child.periodDenominator := hTd.symm
  have ht_hi := ht2
  unfold StrictInterior
  simp only [FLatticePaper.W1.w1b, FLatticePaper.W1.w1a, FLatticePaper.W1.w1h, FLatticePaper.W1.w1c, if_pos hev]
  rw [htw, hsw, hTw]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [hTbig, hs_up, hsb, ht_hi, hbt]

/-- The zero field value at the north neighbour of an odd free H root: its `t`-grade `t(b) − d` lies in the zero band. -/
theorem north_zero {frame : ChildFrame} {G : Field} (hS : frame.HasStrips G) {b : Site}
    (hbt : frame.child.num + 2 ≤ frame.tGrade b) (hle : frame.tGrade b ≤ frame.child.den) :
    G (b.1, b.2 + 1) = 0 := by
  obtain ⟨hn1, hnd, -, -, -⟩ := frame.child_facts
  have htS : frame.tGrade (b.1, b.2 + 1) = frame.tGrade b - frame.child.den := by
    unfold ChildFrame.tGrade
    ring
  exact FLatticePaper.ShapeOneGeom.zero_of_tGrade hS (by omega) (by omega)

/-- **The north fan of an odd free H root.** The all-branch contact fan of the cone of base `b` starts at `m = b + (0, 1)`, a white
contact with zero field value; its forced edge is its east input (`fan_start_forced`). -/
theorem north_fan_forced {frame : ChildFrame} {G : Field} (hP : frame.Packet G)
    (hsig : ∀ w ∈ frame.closedPolygon, G w - G (w - frame.shortShift) ≤ 0)
    {p q : ℤ} (hs : frame.child.num * p - frame.child.den * q = 2 - frame.child.num) {K : ℕ}
    (hK2 : 2 ≤ K)
    (hKs : frame.child.den + 2 * frame.child.num - 1 ≤ frame.child.num * (K : ℤ))
    (hKr : 2 * frame.child.num * (K : ℤ) ≤ 3 * frame.child.den + 5 * frame.child.num - 1)
    (hcap : ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ G (p + (k : ℤ), q + (k : ℤ)))
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    {b : Site} (hz : b ∈ frame.freeH) (hodd : ¬ EvenSite b) (hne : b ≠ frame.hLast)
    (hbt : frame.child.num + 2 ≤ frame.tGrade b) (hGm : G (b.1, b.2 + 1) = 0) :
    ForcedEdge G (fun _ _ => False) (b.1, b.2 + 1) (incomingPos (b.1, b.2 + 1)) := by
  have hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0 := hP.binary
  have hSI := north_strict hz hodd hne hbt
  have hevS : EvenSite (b.1, b.2 + 1) := by
    unfold EvenSite at hodd ⊢
    omega
  have hconeS : ConeRoot b K (b.1, b.2 + 1) := by
    unfold ConeRoot
    refine ⟨?_, ?_, ?_, fun h => absurd hevS h⟩
    · dsimp only
      omega
    · dsimp only
      omega
    · dsimp only
      omega
  have hc1 : FLatticePaper.QuadraticCap.capMin ((b.1, b.2 + 1).2 - b.2) = 0 := by
    have e1 : (b.1, b.2 + 1).2 - b.2 = 1 := by
      dsimp only
      ring
    rw [e1]
    norm_num [FLatticePaper.QuadraticCap.capMin]
  have hmem : (b.1, b.2 + 1) ∈ contactFan frame G b K := by
    refine mem_contactFan.mpr ⟨⟨(FLatticePaper.W1Exit.openRect_iff frame _).mpr hSI, hconeS⟩, ?_⟩
    unfold parabolaField
    rw [hGm, hc1]
  have hwin := cone_window frame hP hsig hs K hcap b hbt
  have hlapS := contactFan_even_white hbin hwin hmem hevS
  obtain ⟨o, ho⟩ := hW1 (b.1, b.2 + 1) hSI hlapS
  have hO := fan_start_forced hP hsig hs hK2 hKs hKr hcap hbt hmem hevS ho
  rw [hO] at ho
  exact FLatticePaper.W1.forcedEdgeIn_forced ho

/-- **The `h3` second arrow** `m → p` (`m = (z.1 - 1, z.2 + 1)`, `p = (z.1, z.2 + 1)`) of an even free H root whose west neighbour
`b = (z.1 - 1, z.2)` is a free H root: the north fan of `b` forces `m` to its east input `p`, which the canonical policy keeps. -/
theorem h3_arrow_north {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} {η : ℤ}
    (C : CanonicalSignedPolicy frame G η) (W : FLatticePaper.W1Witness.OldPolicyWitness frame G seed η)
    (hW : W.retained = C.policy) (hP : frame.Packet G)
    (hsig : ∀ w ∈ frame.closedPolygon, G w - G (w - frame.shortShift) ≤ 0)
    (hAS : ∀ K : ℕ, 2 ≤ K → frame.child.den + 2 * frame.child.num - 1 ≤ frame.child.num * (K : ℤ) →
      2 * frame.child.num * (K : ℤ) ≤ 3 * frame.child.den + 3 * frame.child.num - 1 →
      ∃ p q : ℤ, frame.child.num * p - frame.child.den * q = 2 - frame.child.num ∧
        ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ G (p + (k : ℤ), q + (k : ℤ)))
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (hd : 3 * frame.child.num - 2 ≤ frame.child.den)
    {z : Site} (hz : z ∈ frame.freeH) (hev : EvenSite z) (hq : (z.1 - 1, z.2) ∈ frame.freeH)
    (hz2 : z ≠ (2, 0)) :
    C.policy (z.1 - 1, z.2 + 1) (z.1, z.2 + 1) := by
  obtain ⟨hn1, -, -, -, -⟩ := frame.child_facts
  obtain ⟨hx1, hxd, hy0, hyn⟩ := FLatticePaper.Induction.FreeTraceBox.freeH_box frame hz
  have hodd : ¬ EvenSite (z.1 - 1, z.2) := by
    intro h
    have h' : (z.1 - 1 + z.2) % 2 = 0 := h
    unfold EvenSite at hev
    omega
  have hne : (z.1 - 1, z.2) ≠ frame.hLast := by
    intro h
    have h1 : (z.1 - 1, z.2).1 = (frame.hLast).1 := by rw [h]
    unfold ChildFrame.hLast at h1
    dsimp only at h1
    omega
  have hfirst : (z.1 - 1, z.2) ≠ FLatticePaper.Induction.hFirst := by
    intro h
    apply hz2
    have h1 : (z.1 - 1, z.2).1 = FLatticePaper.Induction.hFirst.1 := by rw [h]
    have h2 : (z.1 - 1, z.2).2 = FLatticePaper.Induction.hFirst.2 := by rw [h]
    unfold FLatticePaper.Induction.hFirst at h1 h2
    dsimp only at h1 h2
    exact Prod.ext (by omega) (by omega)
  obtain ⟨hl, hu⟩ := FLatticePaper.NativeCases.freeH_odd_bounds frame hq hodd
  have hbt : frame.child.num + 2 ≤ frame.tGrade (z.1 - 1, z.2) := by
    have hne_t : frame.tGrade (z.1 - 1, z.2) ≠ frame.child.num := by
      intro ht
      exact hfirst (FLatticePaper.FanInputs.freeH_odd_t_num frame hq hodd ht)
    have hpar : frame.tGrade (z.1 - 1, z.2) % 2 = 1 := by
      rw [FLatticePaper.Induction.tGrade_parity frame]
      have h' : ¬ ((z.1 - 1 + z.2) % 2 = 0) := hodd
      omega
    have hnodd : frame.child.num % 2 = 1 := FLatticePaper.FanInputs.num_odd frame
    omega
  have hle : frame.tGrade (z.1 - 1, z.2) ≤ frame.child.den := hu
  obtain ⟨K, hK2, hKs, hKr⟩ := FLatticePaper.CoveredSW.K_bounds_of_three_n hn1 hd
  obtain ⟨p, q, hs, hcap⟩ := hAS K hK2 hKs hKr
  have hGm := north_zero hP.strips hbt hle
  have hF := north_fan_forced hP hsig hs hK2 hKs (by linarith) hcap hW1 hq hodd hne hbt hGm
  have hevm : EvenSite (z.1 - 1, z.2 + 1) := by
    unfold EvenSite at hev ⊢
    omega
  have hposeq : incomingPos (z.1 - 1, z.2 + 1) = (z.1, z.2 + 1) := by
    unfold incomingPos
    rw [if_pos hevm]
    ext <;> simp
  rw [hposeq] at hF
  have hpres : PrescribedAt frame G η W.retained := by
    rw [hW]
    exact C.prescribed
  have he : EdgeP frame η G seed (z.1 - 1, z.2 + 1) (z.1, z.2 + 1) :=
    Or.inl (Or.inr (forcedEdge_seed_mono hF))
  rw [← hW]
  exact edgeP_retained W.toOldPolicyData hpres he

end FLatticePaper.RouteFan
