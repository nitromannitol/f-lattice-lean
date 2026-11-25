import FLatticePaper.Plane.Induction.WestForced
import FLatticePaper.Plane.Induction.WestArrows
import FLatticePaper.Plane.Induction.RegionalCompat
import FLatticePaper.Plane.Induction.ReturnPrescribed
import FLatticePaper.Plane.Induction.StrictNonfree
import FLatticePaper.Plane.Induction.DeckForced
import FLatticePaper.Plane.Induction.ShortRoute

/-! # The west arrow `z+S → z+SW` at an odd free H root (Q32 he1, §C.1 of the source)

At an odd free H root `z` with `n + 2 ≤ t(z)`, `z ≠ hLast`, white `z+S` and white `z+SW`, the forced edge `z+S → z+SW` holds.
Proof: the strict-interior translate `x1 = z+S+V` (V = Vdeck) is forced by `W1Forced`; the regional region
`{x1, x2}` with `x2 = z+SW+V` and the free exit `w = z+W+V` (`C x1 = x2`, `C x2 = w`, rank 2 > 1 > 0) forces the forced target to
be `x2` by `RegionalCompat.regional_forced`; translating back by `−V` gives the forced edge. -/

namespace FLatticePaper.WestSelect

open FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.ShortRoute FLatticePaper.W1

/-- An empty-seed forced edge is a forced edge for any seed. -/
theorem forcedEdge_seed_mono {G : Field} {s : Site → Site → Prop} {c i : Site}
    (h : ForcedEdge G (fun _ _ => False) c i) : ForcedEdge G s c i := by
  induction h with
  | seed hs => exact (hs : False).elim
  | unit inside hc hw ho hout hin hforced ih =>
    exact ForcedEdge.unit inside hc hw ho hout hin (fun c' hc' hne hl => ih c' hc' hne hl)

/-- The strict-interior translate `z+S+V` of an odd free H root `z` (with `t(z) ≥ n+2`). -/
theorem SI_seV {frame : ChildFrame} {z : Site} (hz : z ∈ frame.freeH) (hodd : ¬ EvenSite z)
    (hne : z ≠ frame.hLast) (hbt : frame.child.num + 2 ≤ frame.tGrade z) :
    FLatticePaper.W1.StrictInterior frame.child.num frame.child.den ((z.1, z.2 - 1) + Vdeck frame) := by
  have ht := freeH_tGrade_add_two_le frame hz hodd hne
  obtain ⟨_, hs2⟩ := freeH_sGrade_bounds frame hz
  have hsbig := FLatticePaper.WestForced.sGrade_odd_H_big hz hodd hne hbt
  obtain ⟨hn1, hnd, hdn, hd3, hP⟩ := frame.child_facts
  have hev : EvenSite ((z.1, z.2 - 1) + Vdeck frame) := by
    unfold EvenSite Vdeck
    simp only [Prod.fst_add, Prod.snd_add]
    unfold EvenSite at hodd
    omega
  have hTw : FLatticePaper.W1.w1T frame.child.num frame.child.den = frame.child.periodDenominator := by
    rw [hP]
    rfl
  have hTbig : 2 * frame.child.den + 2 < frame.child.periodDenominator := by
    rw [hP]
    nlinarith
  have htw : FLatticePaper.W1.w1t frame.child.num frame.child.den ((z.1, z.2 - 1) + Vdeck frame)
      = frame.tGrade z + frame.child.den - frame.child.periodDenominator := by
    unfold FLatticePaper.W1.w1t Vdeck ChildFrame.tGrade
    simp only [Prod.fst_add, Prod.snd_add]
    rw [hP]
    ring
  have hsw : FLatticePaper.W1.w1s frame.child.num frame.child.den ((z.1, z.2 - 1) + Vdeck frame)
      = frame.sGrade z - (frame.child.den - frame.child.num) := by
    unfold FLatticePaper.W1.w1s Vdeck ChildFrame.sGrade
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  unfold FLatticePaper.W1.StrictInterior
  simp only [FLatticePaper.W1.w1b, FLatticePaper.W1.w1a, FLatticePaper.W1.w1h, FLatticePaper.W1.w1c, if_pos hev]
  rw [htw, hsw, hTw]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- The west corner `z+W+V` is not strict-interior: `z+W` is free, and strict-interior sites are nonfree. -/
theorem not_SI_west {frame : ChildFrame} {z : Site} (hz : z ∈ frame.freeH) (hodd : ¬ EvenSite z)
    (hne : z ≠ frame.hLast) (hbt : frame.child.num + 2 ≤ frame.tGrade z) :
    ¬ FLatticePaper.W1.StrictInterior frame.child.num frame.child.den ((z.1 - 1, z.2) + Vdeck frame) := by
  intro hSI
  have hN := strictInterior_nonfree frame hSI
  unfold Nonfree at hN
  apply hN (-Vdeck frame) (span_neg_mem (Vdeck_mem_span frame))
  rw [add_neg_cancel_right]
  exact Set.mem_union_left _ (FLatticePaper.WestArrows.freeH_west hz hodd hne hbt)

/-- **The forced west arrow.** At an odd free H root `z` with white `z+S` and white `z+SW`, `z+S → z+SW` is a forced edge. -/
theorem forcedEdge_SW {frame : ChildFrame} {G : Field} (hP : frame.Packet G)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G) {z : Site}
    (hz : z ∈ frame.freeH) (hodd : ¬ EvenSite z) (hne : z ≠ frame.hLast)
    (hbt : frame.child.num + 2 ≤ frame.tGrade z)
    (hzS : laplacian G (z.1, z.2 - 1) = 0) (hSW : laplacian G (z.1 - 1, z.2 - 1) = 0) :
    ForcedEdge G (fun _ _ => False) (z.1, z.2 - 1) (z.1 - 1, z.2 - 1) := by
  have hvS : Vdeck frame ∈ frame.child.modifiedDeck.span := Vdeck_mem_span frame
  have hnvS : -Vdeck frame ∈ frame.child.modifiedDeck.span := span_neg_mem hvS
  have hevnV : EvenSite (-Vdeck frame) := evenSite_of_span frame hnvS
  have hLinv : ∀ y, laplacian G (y + Vdeck frame) = laplacian G y :=
    fun y => laplacian_span_inv frame G hP hvS y
  obtain ⟨x1, hx1⟩ : ∃ p : Site, p = (z.1, z.2 - 1) + Vdeck frame := ⟨_, rfl⟩
  obtain ⟨x2, hx2⟩ : ∃ p : Site, p = (z.1 - 1, z.2 - 1) + Vdeck frame := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ p : Site, p = (z.1 - 1, z.2) + Vdeck frame := ⟨_, rfl⟩
  have hSI1 : FLatticePaper.W1.StrictInterior frame.child.num frame.child.den x1 := by
    rw [hx1]
    exact SI_seV hz hodd hne hbt
  have hlap1 : laplacian G x1 = 0 := by
    rw [hx1, hLinv]
    exact hzS
  have hlap2 : laplacian G x2 = 0 := by
    rw [hx2, hLinv]
    exact hSW
  have hodd1 : ¬ EvenSite x2 := by
    rw [hx2]
    unfold EvenSite Vdeck
    simp only [Prod.fst_add, Prod.snd_add]
    unfold EvenSite at hodd
    omega
  have hev1 : EvenSite x1 := by
    rw [hx1]
    unfold EvenSite Vdeck
    simp only [Prod.fst_add, Prod.snd_add]
    unfold EvenSite at hodd
    omega
  have hin1 : x2 = incomingNeg x1 := by
    unfold incomingNeg
    rw [if_pos hev1, hx1, hx2]
    refine Prod.ext ?_ ?_
    all_goals simp only [Prod.fst_add, Prod.snd_add]
    all_goals omega
  have hin2 : w = incomingPos x2 := by
    unfold incomingPos
    rw [if_neg hodd1, hw, hx2]
    refine Prod.ext ?_ ?_
    all_goals simp only [Prod.fst_add, Prod.snd_add]
    all_goals omega
  have hx12 : x1 ≠ x2 := by
    intro h
    have h1 := congrArg Prod.fst h
    rw [hx1, hx2] at h1
    simp only [Prod.fst_add] at h1
    omega
  have hwx1 : w ≠ x1 := by
    intro h
    have h1 := congrArg Prod.fst h
    rw [hw, hx1] at h1
    simp only [Prod.fst_add] at h1
    omega
  have hwx2 : w ≠ x2 := by
    intro h
    have h1 := congrArg Prod.snd h
    rw [hw, hx2] at h1
    simp only [Prod.snd_add] at h1
    omega
  have hW1' : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G := hW1
  obtain ⟨o, ho⟩ := hW1' x1 hSI1 hlap1
  have hreg := FLatticePaper.RegionalCompat.regional_forced (F := G)
    (R := FLatticePaper.W1.StrictInterior frame.child.num frame.child.den)
    (S := fun p => p = x1 ∨ p = x2)
    (C := fun p u => (p = x1 ∧ u = x2) ∨ (p = x2 ∧ u = w))
    (r := fun p => if p = x1 then (2 : ℤ) else if p = x2 then 1 else 0)
    (by
      rintro p u (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · simp [hx12.symm]
      · simp [hwx1, hwx2, hx12.symm])
    (by
      intro p u hp hCu hR
      rcases hp with rfl | rfl
      · rcases hCu with ⟨_, hu⟩ | ⟨h, _⟩
        · exact Or.inr hu
        · exact absurd h hx12
      · rcases hCu with ⟨h, _⟩ | ⟨_, hu⟩
        · exact absurd h.symm hx12
        · rw [hu, hw] at hR
          exact absurd hR (not_SI_west hz hodd hne hbt))
    (by
      rintro p (rfl | rfl) hl
      · rw [hlap1] at hl
        norm_num at hl
      · rw [hlap2] at hl
        norm_num at hl)
    (by
      rintro p (rfl | rfl) _
      · exact ⟨x2, Or.inl ⟨rfl, rfl⟩, Or.inl hin1⟩
      · exact ⟨w, Or.inr ⟨rfl, rfl⟩, Or.inr hin2⟩)
    ho (Or.inl rfl)
  have ho2 : o = x2 := by
    rcases hreg with ⟨_, h⟩ | ⟨h, _⟩
    · exact h
    · exact absurd h hx12
  rw [ho2] at ho
  have hF : ForcedEdge G (fun _ _ => False) x1 x2 := FLatticePaper.W1.forcedEdgeIn_forced ho
  have hback := forcedEdge_add G hevnV (fun y => laplacian_span_inv frame G hP hnvS y) hF
  have e1 : x1 + -Vdeck frame = (z.1, z.2 - 1) := by
    rw [hx1, add_neg_cancel_right]
  have e2 : x2 + -Vdeck frame = (z.1 - 1, z.2 - 1) := by
    rw [hx2, add_neg_cancel_right]
  rw [e1, e2] at hback
  exact hback

end FLatticePaper.WestSelect
