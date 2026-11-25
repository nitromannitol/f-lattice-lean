import FLatticePaper.Plane.Induction.WestArrows
import FLatticePaper.Plane.Induction.DeckForced
import FLatticePaper.Plane.Induction.NonfreeBridge
import FLatticePaper.Plane.Induction.StrictNonfree

/-! # The forced existence at the west corner `z+SW` (Q32 part (a), hFsw)

At an odd free H root `z` (`n + 2 ≤ t(z)`, `z ≠ hLast`), the corner `z+SW` is not strict-interior, but it is non-free: its deck translate
`z + SW + V` (with `V = (n−d, n+d)`, which fixes `s` and shifts `t` by `−T`) is strict-interior (`s(z) > 3d+n−2`, from the H box and
`t(z) ≥ n+2`). A non-free white has a forced edge (`W1Forced` at the strict-interior translate, transported back by the deck,
`nonfree_white_forced`). So `hFsw` of `WestArrows.edge_west_adjacency` is derived, not named. -/

namespace FLatticePaper.WestForced

open FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.ShortRoute FLatticePaper.ShapeOneGeom

/-- On the odd free H trace, `s(z) > 3d + n − 2` (for `t(z) ≥ n + 2`): on the box, `n·s = L·t + T·y`. -/
theorem sGrade_odd_H_big {frame : ChildFrame} {z : Site} (hz : z ∈ frame.freeH) (hodd : ¬ EvenSite z)
    (hne : z ≠ frame.hLast) (hbt : frame.child.num + 2 ≤ frame.tGrade z) :
    3 * frame.child.den + frame.child.num - 2 < frame.sGrade z := by
  obtain ⟨hx1, hxd, hy0, hyn⟩ := FreeTraceBox.freeH_box frame hz
  have ht := freeH_tGrade_add_two_le frame hz hodd hne
  obtain ⟨hn1, hnd, hdn, hd3, hP⟩ := frame.child_facts
  have hodd' : (z.1 + z.2) % 2 = 1 := by
    unfold EvenSite at hodd
    omega
  have hzt : frame.tGrade z = frame.child.num * z.1 - frame.child.den * z.2 := rfl
  have hzs : frame.sGrade z = (frame.child.den + frame.child.num) * z.1 + (frame.child.den - frame.child.num) * z.2 := rfl
  have hT : frame.child.periodDenominator = frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2 := hP
  rcases eq_or_lt_of_le (show (0:ℤ) ≤ z.2 from hy0) with h0 | hpos
  · have h0 : z.2 = 0 := h0.symm
    -- `z.2 = 0`: `z.1` is odd and `n z.1 ≥ n + 2`, so `z.1 ≥ 3`
    have hz1 : 2 ≤ z.1 := by
      rw [hzt, h0] at hbt
      nlinarith
    have hz3 : 3 ≤ z.1 := by omega
    rw [hzs, h0]
    nlinarith
  · have key : frame.child.num * frame.sGrade z
        = (frame.child.num + frame.child.den) * frame.tGrade z
          + frame.child.periodDenominator * z.2 := by
      rw [hzs, hzt, hT]
      ring
    have hlow : (frame.child.num + frame.child.den) * (frame.child.num + 2)
        + frame.child.periodDenominator ≤ frame.child.num * frame.sGrade z := by
      rw [key]
      have h1 : (frame.child.num + frame.child.den) * (frame.child.num + 2)
          ≤ (frame.child.num + frame.child.den) * frame.tGrade z := by
        apply mul_le_mul_of_nonneg_left (by omega) (by omega)
      have h2 : frame.child.periodDenominator * 1 ≤ frame.child.periodDenominator * z.2 := by
        apply mul_le_mul_of_nonneg_left (by omega) (by rw [hT]; nlinarith)
      nlinarith
    have hpos' : 0 < frame.child.num := hn1
    by_contra hcon
    have hcon' : frame.sGrade z ≤ 3 * frame.child.den + frame.child.num - 2 := not_lt.mp hcon
    have : frame.child.num * frame.sGrade z ≤ frame.child.num * (3 * frame.child.den + frame.child.num - 2) :=
      mul_le_mul_of_nonneg_left hcon' (by omega)
    rw [hT] at hlow
    nlinarith

/-- **The translate of `z+SW` is strict-interior**: `z + SW + V` (with `V = Vdeck`) lies in the strict interior of the odd H root `z`. -/
theorem SI_swV {frame : ChildFrame} {z : Site} (hz : z ∈ frame.freeH) (hodd : ¬ EvenSite z)
    (hne : z ≠ frame.hLast) (hbt : frame.child.num + 2 ≤ frame.tGrade z) :
    FLatticePaper.W1.StrictInterior frame.child.num frame.child.den ((z.1 - 1, z.2 - 1) + Vdeck frame) := by
  have ht := freeH_tGrade_add_two_le frame hz hodd hne
  obtain ⟨hs1, hs2⟩ := freeH_sGrade_bounds frame hz
  have hsbig := sGrade_odd_H_big hz hodd hne hbt
  obtain ⟨hn1, hnd, hdn, hd3, hP⟩ := frame.child_facts
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hodd' : (z.1 + z.2) % 2 = 1 := by
    unfold EvenSite at hodd
    omega
  have hw_odd : ¬ EvenSite ((z.1 - 1, z.2 - 1) + Vdeck frame) := by
    unfold EvenSite Vdeck
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  have hTw : FLatticePaper.W1.w1T frame.child.num frame.child.den = frame.child.periodDenominator := by
    rw [hP]
    rfl
  have htw : FLatticePaper.W1.w1t frame.child.num frame.child.den ((z.1 - 1, z.2 - 1) + Vdeck frame)
      = frame.tGrade z - frame.child.num + frame.child.den - frame.child.periodDenominator := by
    unfold FLatticePaper.W1.w1t Vdeck ChildFrame.tGrade
    simp only [Prod.fst_add, Prod.snd_add]
    rw [hP]
    ring
  have hsw : FLatticePaper.W1.w1s frame.child.num frame.child.den ((z.1 - 1, z.2 - 1) + Vdeck frame)
      = frame.sGrade z - 2 * frame.child.den := by
    unfold FLatticePaper.W1.w1s Vdeck ChildFrame.sGrade
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  have hTbig : 2 * frame.child.den - 2 * frame.child.num - 2 < frame.child.periodDenominator := by
    rw [hP]
    nlinarith
  unfold FLatticePaper.W1.StrictInterior
  simp only [FLatticePaper.W1.w1b, FLatticePaper.W1.w1a, FLatticePaper.W1.w1h, FLatticePaper.W1.w1c, if_neg hw_odd]
  rw [htw, hsw, hTw]
  refine ⟨?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega
  · omega

/-- **Non-freeness transfers along a strict-interior translate.** -/
theorem nonfree_of_translate_SI {frame : ChildFrame} {z v : Site} (hv : v ∈ frame.child.modifiedDeck.span)
    (hSI : FLatticePaper.W1.StrictInterior frame.child.num frame.child.den (z + v)) : Nonfree frame z := by
  unfold Nonfree
  intro u hu hmem
  have hN := strictInterior_nonfree frame hSI
  unfold Nonfree at hN
  apply hN (u + -v) (span_add_mem hu (span_neg_mem hv))
  rw [show z + v + (u + -v) = z + u by abel]
  exact hmem

/-- **A non-free white has a forced edge** (`W1Forced` at the strict-interior deck translate, transported back). -/
theorem exists_forced_of_nonfree {frame : ChildFrame} {G : Field} (hP : frame.Packet G)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G) {z : Site}
    (hnf : Nonfree frame z) (hw : laplacian G z = 0) :
    ∃ o, ForcedEdge G (fun _ _ => False) z o := by
  obtain ⟨v, hv, hSI⟩ := nonfree_bridge frame z hnf
  have hwv : laplacian G (z + v) = 0 := by
    rw [laplacian_span_inv frame G hP hv z]
    exact hw
  obtain ⟨o, ho⟩ := hW1 (z + v) hSI hwv
  have hf : ForcedEdge G (fun _ _ => False) (z + v) o := FLatticePaper.W1.forcedEdgeIn_forced ho
  have hnv : -v ∈ frame.child.modifiedDeck.span := span_neg_mem hv
  have hfz := forcedEdge_add G (evenSite_of_span frame hnv) (fun y => laplacian_span_inv frame G hP hnv y) hf
  rw [add_neg_cancel_right] at hfz
  exact ⟨o + -v, hfz⟩

/-- **`hFsw` derived**: at an odd free H root, a white `z+SW` has a forced edge. -/
theorem hFsw_of_freeH {frame : ChildFrame} {G : Field} (hP : frame.Packet G)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G) {z : Site}
    (hz : z ∈ frame.freeH) (hodd : ¬ EvenSite z) (hne : z ≠ frame.hLast)
    (hbt : frame.child.num + 2 ≤ frame.tGrade z) :
    laplacian G (z.1 - 1, z.2 - 1) = 0 → ∃ i, ForcedEdge G (fun _ _ => False) (z.1 - 1, z.2 - 1) i := by
  intro hw
  have hSI := SI_swV hz hodd hne hbt
  have hnf : Nonfree frame (z.1 - 1, z.2 - 1) := nonfree_of_translate_SI (Vdeck_mem_span frame) hSI
  exact exists_forced_of_nonfree hP hW1 hnf hw

end FLatticePaper.WestForced
