import FLatticePaper.Plane.Induction.MinusPrefixTable
import FLatticePaper.Plane.Induction.FanStart
import FLatticePaper.Plane.Induction.FanWindow
import FLatticePaper.Plane.Induction.FreeWebClaims
import FLatticePaper.Plane.Induction.RouteStay
import FLatticePaper.Plane.Induction.Q3White
import FLatticePaper.Plane.Induction.ArcRanges
import FLatticePaper.Plane.Induction.ListPrefix

/-! # The even V entries of the minus-prefix block are refuted (Q41 section 4, block 1)

For an even hard V entry `w = V_j` of the minus prefix (`1 ≤ j ≤ r`): the entry is white with its prescribed input `w + (−1, 0)`
(`permitsQ1` by `freeClosure` and `FreePresc`), and that input is the start `Zs v₀` of the rotated fan. The fan is refuted at `v₀` by
`HardVFanBlocks.minus_prefix_refuted`, with the cone window of `FanWindow`, the exits of `MinusPrefixTable.minus_prefix_hexit`, and the
start facts of `FanStart`. -/

namespace FLatticePaper.MinusPrefixEntry

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.ContactCone FLatticePaper.FanRegion FLatticePaper.RefuteTree
  FLatticePaper.AuxRankQ1 FLatticePaper.RotatedCap FLatticePaper.RotatedForced FLatticePaper.MinusRowWiring FLatticePaper.CapRay
  FLatticePaper.FanPropagation FLatticePaper.HardVFanBlocks FLatticePaper.MinusPrefixTable FLatticePaper.FanStart
  FLatticePaper.FanWindow FLatticePaper.CapConeGrades FLatticePaper.W1

/-- **The minus-prefix entry.** The even hard V entry `V_j` (`1 ≤ j ≤ r`) is refuted from the earlier entries of the minus row. -/
theorem minus_prefix_entry (frame : ChildFrame) (F : Field) (hP : frame.Packet F)
    (hprice : ∀ z ∈ frame.closedPolygon, frame.cutPrice - 1 ≤ frame.price F z ∧ frame.price F z ≤ frame.cutPrice)
    (hdrU : ∀ z, frame.price F (z + frame.child.modifiedDeck.kernel) = frame.price F z - 1)
    (hdrV : ∀ z, frame.price F (z + frame.child.modifiedDeck.transverse) = frame.price F z)
    (hn3 : 3 ≤ frame.child.num) (hd2 : frame.child.den < 2 * frame.child.num)
    (hPH : ∀ h, frame.freeH h → frame.price F h ≤ frame.cutPrice ∧
      (frame.price F h = frame.cutPrice → h = FLatticePaper.Induction.hFirst))
    (hJH : ∀ h, frame.freeH h → frame.roundedSlip F (-1) h = 0)
    {r : ℤ}
    (hJV : ∀ k : ℕ, r < (k : ℤ) → (k : ℤ) < frame.child.den + frame.child.num →
      frame.roundedSlip F (-1) (VChain.vpath frame k) = -1)
    (hrL : r + 2 ≤ frame.child.den + frame.child.num)
    (j : ℕ) (hj1 : 1 ≤ j) (hjr : (j : ℤ) ≤ r) (hev : EvenSite (RowAt.vAt frame j)) :
    Refuted frame F (-1) (earlierAt frame r (r - (j : ℤ)).toNat) (fun _ => False) (RowAt.vAt frame j) := by
  obtain ⟨hon, hod⟩ := frame.child_odd
  obtain ⟨hn0, hnlt, -, -, -⟩ := frame.child_facts
  have hnd : frame.child.num + 2 ≤ frame.child.den := by omega
  have hjL : (j : ℤ) < frame.child.den + frame.child.num := by omega
  have hwpath : RowAt.vAt frame j = VChain.vpath frame j := (RowAt.vAt_nat frame j hjL).symm ▸ rfl
  set w : Site := RowAt.vAt frame j with hwdef
  have hwF : w ∈ frame.freeV := by
    rw [hwpath]; exact ListPrefix.vpath_freeV_all frame j hjL
  have hw2 : w.2 = (j : ℤ) := by rw [hwpath, VChain.vpath_ord frame j]
  have hw1 : 1 ≤ w.2 := by omega
  have hw2le : w.2 ≤ frame.child.den + frame.child.num - 2 := by omega
  -- the parameters N = (d − n)/2 and D = (d + n)/2
  obtain ⟨N, hN2⟩ : ∃ N : ℤ, 2 * N = frame.child.den - frame.child.num := ⟨(frame.child.den - frame.child.num) / 2, by omega⟩
  obtain ⟨D, hD2⟩ : ∃ D : ℤ, 2 * D = frame.child.den + frame.child.num := ⟨(frame.child.den + frame.child.num) / 2, by omega⟩
  have hN0 : 0 < N := by omega
  have hND : N < D := by omega
  have H := rotated_NL hP hprice hdrU hdrV N D hN2 hD2 hN0 hND
  obtain ⟨K, p, q, hK2, hs, hpq, hKs, hKr, hcap, hb⟩ :=
    entry_data frame hP hprice hdrU hdrV hd2 hN2 hD2 hN0 hND hwF hev hw1 hw2le
  -- w₁ + w₂ ≥ 2: T (w₁ + w₂) = L s(w) − 2n t(w) > 0, and w is even
  have hs1 := RouteStay.even_grade_strict frame hwF hev hw1 hw2le
  have ht := ArcRanges.arc_even_range frame hwF hev
    (by intro h; rw [h] at hw1; simp [FLatticePaper.Induction.vFirst] at hw1)
    (by intro h; rw [h] at hw2le; simp [ChildFrame.vLast] at hw2le; omega)
  have hT3 := ShortPassages.T_ge frame
  have hid : w1T frame.child.num frame.child.den * (w.1 + w.2) =
      (frame.child.den + frame.child.num) * w1s frame.child.num frame.child.den w -
        2 * frame.child.num * w1t frame.child.num frame.child.den w := by
    unfold w1s w1t w1T; ring
  rw [frame_sGrade_eq] at hs1
  rw [frame_tGrade_eq] at ht
  rw [frame_periodDenominator_eq] at ht hT3
  have hw12 : 2 ≤ w.1 + w.2 := by
    have hpos : 0 < w1T frame.child.num frame.child.den * (w.1 + w.2) := by
      rw [hid]
      nlinarith
    have hT0 : 0 < w1T frame.child.num frame.child.den := by omega
    have h1 : 0 < w.1 + w.2 := by
      by_contra hc
      push Not at hc
      nlinarith
    have he2 : (w.1 + w.2) % 2 = 0 := by
      unfold EvenSite at hev
      simpa [hwdef, RowAt.vAt] using hev
    omega
  -- the cone window of the fan at the entry
  have hwin : WindowOn (fun x => resRegion frame.child.num frame.child.den x ∧ ConeRoot (w.2 + 1, -w.1) K x)
      (quarterTurnField F) (fun i => parabolaField (-w.1) i) := by
    have hcw := cone_window_NL H (w1T frame.child.num frame.child.den) hN0 hND (by norm_num) hs hpq K hcap
      (w.2 + 1, -w.1) hb
    intro x hx i hi
    exact hcw x ⟨resRegion_sub_ropen (by omega) (by omega) hN0 hND x hx.1, hx.2⟩ i hi
  -- the exit table
  have hexit := minus_prefix_hexit frame F hP hn3 (r := r) j hj1 hjr hPH hJH hJV hN2 hD2 hN0 hND H
    (w := w) hw2 hw12 hb hK2 hs hpq hKs hKr hcap
  -- the start of the fan is in the fan
  have hv0 : ((w.2 + 1, 1 - w.1) : Site) ∈ fanSet (resRegion frame.child.num frame.child.den)
      (quarterTurnField F) (w.2 + 1, -w.1) K :=
    ⟨⟨start_resRegion frame hn3 hnd hwF hev hw1 hw2le, start_coneRoot hev hK2⟩,
      start_contact frame H hN2 hD2 hN0 hn3 hwF hev hw1 hw2le⟩
  have hstart := minus_prefix_refuted frame F (η := -1) (E := earlierAt frame r (r - (j : ℤ)).toNat)
    (C := fun _ => False) hP hwin hexit _ hv0
  have hZs : Zs ((w.2 + 1, 1 - w.1) : Site) = w + (-1, 0) := by
    unfold Zs
    exact Prod.ext (by simp; ring) (by simp)
  rw [hZs] at hstart
  -- the white step at the entry
  have hlap : laplacian F w = 0 := FLatticePaper.Induction.ChildFrame.laplacian_eq_zero_of_freeV frame hP.strips hwF
  have hx1 : w ≠ FLatticePaper.Induction.vFirst := by
    intro h
    have := congrArg Prod.snd h
    simp [FLatticePaper.Induction.vFirst] at this
    omega
  have hx2 : w ≠ frame.vLast := by
    intro h
    have := congrArg Prod.snd h
    simp [ChildFrame.vLast] at this
    omega
  have hperm : permitsQ1 frame F (-1) w (w + (-1, 0)) :=
    Or.inr ⟨hlap, Or.inl ⟨⟨0, FreeWebClaims.zero_mem_span frame, Or.inr (by simpa using hwF)⟩,
      ⟨0, FreeWebClaims.zero_mem_span frame, Or.inr ⟨by simpa using hwF, by
        simp only [add_zero]; rw [RouteStay.prescribedV_even frame hx1 hx2 hev]⟩⟩⟩⟩
  exact RefuteTree.Refuted.white hlap hperm hstart

end FLatticePaper.MinusPrefixEntry
