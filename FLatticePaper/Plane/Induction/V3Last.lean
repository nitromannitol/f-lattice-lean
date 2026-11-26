import FLatticePaper.Plane.Induction.VGradeBounds
import FLatticePaper.Plane.Induction.VStrict
import FLatticePaper.Plane.Induction.VLattice
import FLatticePaper.Plane.Induction.RouteRegional
import FLatticePaper.Plane.Induction.RouteRegion
import FLatticePaper.Plane.Induction.V2Minus
import FLatticePaper.Plane.Induction.V2Arrows
import FLatticePaper.Plane.Induction.FreeNonfree
import FLatticePaper.Plane.Induction.StripColours

/-! # The last arrow of the `v3` row: `(z.1 + η, z.2) → z` for an odd free V root `z`

For `η = 1` the source `q = (z.1 + 1, z.2)` is strictly interior (by the grade bounds `t(z) ≤ 1 − n` and `t(z) ≥ n + 2d − T`
of `VGradeBounds`), so `white_route_policy` keeps `z` at `q`. For `η = −1` the source `q = (z.1 − 1, z.2)` is not strictly interior,
but its translate `q + (d, n)` is, and the deck port `RouteRegion.route_port_arrow` keeps `z` at `q`. -/

namespace FLatticePaper.V3Last

open FLatticePaper FLatticePaper.Induction FLatticePaper.W1

/-- The grade data of an odd free V root. -/
theorem odd_V_grades {frame : ChildFrame} {z : Site} (hz : z ∈ frame.freeV) (hodd : ¬ EvenSite z) :
    frame.tGrade z ≤ 1 - frame.child.num ∧ frame.child.num + 2 * frame.child.den - (frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2) ≤ frame.tGrade z ∧
      2 - frame.child.den + frame.child.num ≤ frame.sGrade z ∧ frame.sGrade z ≤ frame.child.den + frame.child.num - 2 := by
  obtain ⟨h1, h2, h3, h4, hvs⟩ := VStrict.odd_free_V_facts hz hodd
  obtain ⟨hn0, hnd, hd2, hd3, hT⟩ := frame.child_facts
  obtain ⟨hnO, hdO⟩ := frame.child_odd
  have hTd : frame.child.periodDenominator
      = frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2 := rfl
  have hodd' : (z.1 + z.2) % 2 = 1 := by
    unfold EvenSite at hodd
    omega
  have hcop : IsCoprime frame.child.num frame.child.den := frame.child_reduced
  have ht : frame.tGrade z = frame.child.num * z.1 - frame.child.den * z.2 := rfl
  have hs : frame.sGrade z = (frame.child.den + frame.child.num) * z.1 + (frame.child.den - frame.child.num) * z.2 := by
    unfold ChildFrame.sGrade; ring
  obtain ⟨hs_lo, hs_hi⟩ := VLattice.s_range (by omega) hvs
  have hA := VGradeBounds.t_le_one_sub_n (by omega) (by omega) hodd' ht hs h2 h3 (by omega)
  have hB := VGradeBounds.t_ge_n_add_two_d_sub_T (by omega) (by omega) hnO hdO hcop hodd' ht hs h1 h2 h3 (by omega)
  exact ⟨hA, hB, h3, by omega⟩

/-- **The last `v3` arrow, `η = 1`**: `(z.1 + 1, z.2) → z`, from the white-middle regional argument with the strictly interior
source `(z.1 + 1, z.2)`. -/
theorem v3_last_plus {frame : ChildFrame} {G : Field} (C : CanonicalSignedPolicy frame G 1)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0)
    {z : Site} (hz : z ∈ frame.freeV) (hodd : ¬ EvenSite z) (hwz : laplacian G z = 0)
    (hnb : (z.1, z.2 + 1) ∈ frame.freeV) :
    laplacian G (z.1 + 1, z.2) = -1 ∨ C.policy (z.1 + 1, z.2) z := by
  by_cases hb : laplacian G (z.1 + 1, z.2) = -1
  · exact Or.inl hb
  · right
    have hmw : laplacian G (z.1 + 1, z.2) = 0 := (hbin _).resolve_left hb
    obtain ⟨hA, hB, hsl, hsh⟩ := odd_V_grades hz hodd
    have hbig := FLatticePaper.FreeNonfree.big_T (frame := frame)
    have hev : EvenSite (z.1 + 1, z.2) := by
      unfold EvenSite at hodd ⊢
      simp only at hodd ⊢
      omega
    have hTd : frame.child.periodDenominator
        = frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2 := rfl
    have hTw : w1T frame.child.num frame.child.den = frame.child.periodDenominator := hTd.symm
    have hstrict : StrictInterior frame.child.num frame.child.den (z.1 + 1, z.2) := by
      unfold StrictInterior
      simp only [w1b, w1a, w1h, w1c, if_pos hev]
      have e1 : w1t frame.child.num frame.child.den (z.1 + 1, z.2) = frame.tGrade z + frame.child.num := by
        unfold w1t ChildFrame.tGrade; ring
      have e2 : w1s frame.child.num frame.child.den (z.1 + 1, z.2) = frame.sGrade z + (frame.child.den + frame.child.num) := by
        unfold w1s ChildFrame.sGrade; ring
      rw [e1, e2, hTw]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
    have hin : z = incomingNeg (z.1 + 1, z.2) ∨ z = incomingPos (z.1 + 1, z.2) := by
      refine Or.inl ?_
      unfold incomingNeg
      rw [if_pos hev]
      refine Prod.ext ?_ ?_ <;> simp
    have hzin : (z.1, z.2 + 1) = incomingNeg z ∨ (z.1, z.2 + 1) = incomingPos z := by
      refine Or.inr ?_
      unfold incomingPos
      rw [if_neg hodd]
    have hzR := FLatticePaper.V2Arrows.not_strict_of_freeV hnb
    have hzm : (z.1, z.2 + 1) ≠ (z.1 + 1, z.2) := by
      intro h
      have h1 : z.1 = z.1 + 1 := congrArg Prod.fst h
      omega
    exact FLatticePaper.RouteRegional.white_route_policy C hW1 hstrict hmw hin hwz hzin hzR hzm

/-- **The last `v3` arrow, `η = −1`**: `(z.1 − 1, z.2) → z`, by the deck port with the kernel `(d, n)`: the source is not interior, but
its translate `(z.1 − 1 + d, z.2 + n)` is. -/
theorem v3_last_minus {frame : ChildFrame} {G : Field} (C : CanonicalSignedPolicy frame G (-1))
    (hP : frame.Packet G) (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0)
    (hdK : ∀ x u, C.policy x u ↔ C.policy (x + (frame.child.den, frame.child.num)) (u + (frame.child.den, frame.child.num)))
    {z : Site} (hz : z ∈ frame.freeV) (hodd : ¬ EvenSite z) :
    laplacian G (z.1 - 1, z.2) = -1 ∨ C.policy (z.1 - 1, z.2) z := by
  by_cases hb : laplacian G (z.1 - 1, z.2) = -1
  · exact Or.inl hb
  · right
    have hmw : laplacian G (z.1 - 1, z.2) = 0 := (hbin _).resolve_left hb
    obtain ⟨hA, hB, hsl, hsh⟩ := odd_V_grades hz hodd
    have hbig := FLatticePaper.FreeNonfree.big_T (frame := frame)
    have hpar : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
    have hev : EvenSite (z.1 - 1, z.2) := by
      unfold EvenSite at hodd ⊢
      simp only at hodd ⊢
      omega
    have hKev : EvenSite (frame.child.den, frame.child.num) := by
      unfold EvenSite
      simp only
      omega
    have hqKev : EvenSite ((z.1 - 1, z.2) + (frame.child.den, frame.child.num)) := by
      unfold EvenSite at hodd ⊢
      simp only [Prod.fst_add, Prod.snd_add] at hodd ⊢
      omega
    have hTd : frame.child.periodDenominator
        = frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2 := rfl
    have hTw : w1T frame.child.num frame.child.den = frame.child.periodDenominator := hTd.symm
    have hstrict : StrictInterior frame.child.num frame.child.den ((z.1 - 1, z.2) + (frame.child.den, frame.child.num)) := by
      obtain ⟨hn0, hnd0, hd2, -, -⟩ := frame.child_facts
      rw [hTd] at hbig
      unfold StrictInterior
      simp only [w1b, w1a, w1h, w1c, if_pos hqKev]
      have e1 : w1t frame.child.num frame.child.den ((z.1 - 1, z.2) + (frame.child.den, frame.child.num))
          = frame.tGrade z - frame.child.num := by
        unfold w1t ChildFrame.tGrade; simp only [Prod.fst_add, Prod.snd_add]; ring
      have e2 : w1s frame.child.num frame.child.den ((z.1 - 1, z.2) + (frame.child.den, frame.child.num))
          = frame.sGrade z - (frame.child.den + frame.child.num)
            + (frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2) := by
        unfold w1s ChildFrame.sGrade; simp only [Prod.fst_add, Prod.snd_add]; ring
      rw [e1, e2, hTw]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
    have hin : z = incomingPos (z.1 - 1, z.2) := by
      unfold incomingPos
      rw [if_pos hev]
      refine Prod.ext ?_ ?_ <;> simp
    exact FLatticePaper.RouteRegion.route_port_arrow C hW1 hKev hdK
      ((FLatticePaper.StripColours.lap_add_kernel frame hP.periods (z.1 - 1, z.2)).trans hmw)
      hstrict (Or.inr hin) (FLatticePaper.V2Minus.not_strict_shift_of_freeV hz)

end FLatticePaper.V3Last
