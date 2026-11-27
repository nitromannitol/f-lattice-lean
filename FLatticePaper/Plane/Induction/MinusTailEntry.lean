import FLatticePaper.Plane.Induction.MinusTail
import FLatticePaper.Plane.Induction.MinusRowH
import FLatticePaper.Plane.Induction.MinusPrefixTable
import FLatticePaper.Plane.Induction.FanStart
import FLatticePaper.Plane.Induction.FanWindow
import FLatticePaper.Plane.Induction.FanExitCases
import FLatticePaper.Plane.Induction.FanExitBounds
import FLatticePaper.Plane.Induction.FreeWebClaims
import FLatticePaper.Plane.Induction.RouteStay
import FLatticePaper.Plane.Induction.Q3White
import FLatticePaper.Plane.Induction.ArcRanges
import FLatticePaper.Plane.Induction.ListPrefix
import FLatticePaper.Plane.Induction.RowVEasy
import FLatticePaper.Plane.Induction.HChain
import FLatticePaper.Plane.Induction.EasyHRank

/-! # The minus tail of the hard V block (Q41 section 4, block 2): the fan, the exit table and the entries

The entry `V_j` (`r + 1 − L ≤ j ≤ −2`) of the minus tail has the rotated apex `vAt (j + L) = V_j + V`. Its fan is taken in the physical map
`Y q = Zs q − V`. Its exits are earlier entries only: a V-exit `V_{k−L}` (with `j < k − L ≤ −1`) and an H-exit `H_{i−d}` (in the H block). -/

namespace FLatticePaper.MinusTailEntry

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.ContactCone FLatticePaper.FanRegion FLatticePaper.RefuteTree
  FLatticePaper.AuxRankQ1 FLatticePaper.RotatedCap FLatticePaper.RotatedForced FLatticePaper.MinusRowWiring FLatticePaper.CapRay
  FLatticePaper.FanPropagation FLatticePaper.HardVFanBlocks FLatticePaper.MinusPrefixTable FLatticePaper.FanStart
  FLatticePaper.FanWindow FLatticePaper.CapConeGrades FLatticePaper.W1 FLatticePaper.MinusTail FLatticePaper.MinusRowH
  FLatticePaper.FanAcyclic FLatticePaper.HardVFanRefute

/-- The tail fan refutation: every node of the fan at a tail entry is refuted at the translated physical site `Zs q − V`. -/
theorem minus_tail_refuted (frame : ChildFrame) (F : Field) {η : ℤ} (hP : frame.Packet F) {b : Site} {K : ℕ}
    {E C : Site → Prop}
    (hwin : WindowOn (fun x => resRegion frame.child.num frame.child.den x ∧ ConeRoot b K x)
      (quarterTurnField F) (fun i => parabolaField b.2 i))
    (hexit : ∀ q, q ∈ fanSet (resRegion frame.child.num frame.child.den) (quarterTurnField F) b K →
      ∀ u, ((EvenSite q ∧ u = incomingPos q) ∨ (¬ EvenSite q ∧ Edge u q)) →
        quarterTurnField F u = parabolaField b.2 u →
        u ∉ fanSet (resRegion frame.child.num frame.child.den) (quarterTurnField F) b K →
        Refuted frame F η E C (Zs u - RowAt.Vvec frame)) :
    ∀ q, q ∈ fanSet (resRegion frame.child.num frame.child.den) (quarterTurnField F) b K →
      Refuted frame F η E C (Zs q - RowAt.Vvec frame) := by
  have hVd : RowAt.Vvec frame = Vdeck frame := rfl
  have hbin : ∀ c, laplacian (quarterTurnField F) c = -1 ∨ laplacian (quarterTurnField F) c = 0 := by
    intro c
    rw [laplacian_quarterTurnField]
    exact hP.binary _
  have hlapY : ∀ q, laplacian F (Zs q - RowAt.Vvec frame) = laplacian (quarterTurnField F) q := by
    intro q
    have e := RowVEasy.lap_add_Vdeck frame hP (Zs q - RowAt.Vvec frame)
    rw [hVd, sub_add_cancel] at e
    rw [laplacian_quarterTurnField, hVd]
    exact e.symm
  have hnf : ∀ q, q ∈ fanSet (resRegion frame.child.num frame.child.den) (quarterTurnField F) b K →
      Nonfree frame (Zs q - RowAt.Vvec frame) := by
    intro q hq
    apply RowVEasy.nonfree_of_add_Vdeck frame
    rw [hVd, sub_add_cancel]
    exact nonfree_Zs hq.1.1
  have hlo : ∃ lo : ℤ, ∀ q, q ∈ fanSet (resRegion frame.child.num frame.child.den) (quarterTurnField F) b K →
      lo ≤ fanRank q :=
    fanRank_lower_of_finite (R := resRegion frame.child.num frame.child.den) (resRegion_finite frame)
      |> fun h => by
        obtain ⟨lo, hlo⟩ := h
        exact ⟨lo, fun q hq => hlo q hq.1.1⟩
  exact fan_refuted (η := η) (E := E) (C := C) (Y := fun q => Zs q - RowAt.Vvec frame) hbin hlapY hwin hnf
    (tail_inputs frame) hexit hlo

/-- **The exit table of the minus tail.** Every exit of the fan at a tail entry is an earlier minus-row entry. -/
theorem minus_tail_hexit (frame : ChildFrame) (F : Field)
    (hn3 : 3 ≤ frame.child.num)
    {r : ℤ} (hr0 : 0 ≤ r) {j : ℤ} (hjlo : r + 1 - (frame.child.den + frame.child.num) ≤ j) (hj2 : j ≤ -2)
    {N D : ℤ} (hN2 : 2 * N = frame.child.den - frame.child.num) (hD2 : 2 * D = frame.child.den + frame.child.num)
    (hN0 : 0 < N) (hND : N < D)
    (H : CapConeGrades.NLCap N D (quarterTurnField F))
    {w : Site} (hwj : w.2 = j + (frame.child.den + frame.child.num)) (hw12 : 2 ≤ w.1 + w.2)
    (hb : N + 1 ≤ N * (w.2 + 1) - D * (-w.1))
    {K : ℕ} {p q : ℤ} (hK2 : 2 ≤ K) (hs : N * p - D * q = 1 - N) (hpq : (p + q) % 2 = 1)
    (hKs : 4 * N + 2 * D - 1 ≤ 2 * N * (K : ℤ)) (hKr : 2 * N * (K : ℤ) ≤ 3 * D + 5 * N - 1)
    (hcap : ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ quarterTurnField F (p + (k : ℤ), q + (k : ℤ))) :
    ∀ q' : Site, q' ∈ fanSet (resRegion frame.child.num frame.child.den) (quarterTurnField F) (w.2 + 1, -w.1) K →
      ∀ u : Site, ((EvenSite q' ∧ u = incomingPos q') ∨ (¬ EvenSite q' ∧ Edge u q')) →
        quarterTurnField F u = parabolaField (-w.1) u →
        u ∉ fanSet (resRegion frame.child.num frame.child.den) (quarterTurnField F) (w.2 + 1, -w.1) K →
        Refuted frame F (-1) (earlierAt frame r (r + frame.child.den - j).toNat) (fun _ => False)
          (Zs u - RowAt.Vvec frame) := by
  intro q' hq u hu hc hnot
  have hqR : resRegion frame.child.num frame.child.den q' := hq.1.1
  have hqC : ConeRoot (w.2 + 1, -w.1) K q' := hq.1.2
  obtain ⟨hn0, hnlt, -, -, -⟩ := frame.child_facts
  obtain ⟨hon, hod⟩ := frame.child_odd
  have hn_eq : frame.child.num = D - N := by omega
  have hd_eq : frame.child.den = D + N := by omega
  have hnotR : ¬ resRegion frame.child.num frame.child.den u := by
    intro hR
    have hopenU := resRegion_sub_ropen hn_eq hd_eq hN0 hND u hR
    have hopenQ := resRegion_sub_ropen hn_eq hd_eq hN0 hND q' hqR
    have hwu : u = incomingNeg q' ∨ u = incomingPos q' := by
      rcases hu with ⟨-, h⟩ | ⟨-, h⟩
      · exact Or.inr h
      · exact h
    have hev' : EvenSite q' → u = incomingPos q' := by
      intro he
      rcases hu with ⟨-, h⟩ | ⟨hne, -⟩
      · exact h
      · exact absurd he hne
    have hcont : quarterTurnField F u = FLatticePaper.QuadraticCap.capMin (u.2 - (w.2 + 1, -w.1).2) := hc
    obtain ⟨-, hcone⟩ := CapConeGrades.fan_next_NL H hN0 hND le_rfl (by norm_num) hs hpq K hK2 hKs hKr hcap
      (w.2 + 1, -w.1) hb q' u ⟨hopenQ, hqC⟩ hwu hev' hopenU hcont
    exact hnot ⟨⟨hR, hcone⟩, hc⟩
  obtain ⟨hz2, hsum⟩ := FanExitBounds.exit_bounds hw12 hqC hu
  have hUe : EvenSite (RowAt.Uvec frame) := by
    unfold EvenSite RowAt.Uvec
    simp only
    omega
  have hEdgeU : Edge (Zs u + RowAt.Uvec frame) (Zs q' + RowAt.Uvec frame) :=
    (AuxRankQ1.edge_shift hUe (Zs q') (Zs u)).mpr (zs_edge_of_input hu)
  have hopenZq : frame.openRect (Zs q' + RowAt.Uvec frame) :=
    (resRegion_eq_openRect frame q').mp hqR
  have hclosedU : Zs u + RowAt.Uvec frame ∈ frame.closedPolygon :=
    W1Exit.rectInputs frame _ hopenZq _ hEdgeU
  have hnotU : ¬ frame.openRect (Zs u + RowAt.Uvec frame) := fun h =>
    hnotR ((resRegion_eq_openRect frame u).mpr h)
  have hx0 : 0 ≤ (Zs u).2 := by omega
  rcases FanExitCases.fan_exit_class frame hn3 hx0 hsum hclosedU hnotU with ⟨hV, hVle⟩ | ⟨hH, hHne⟩
  · -- V-exit: Zs u = V_k with j + L < k ≤ L − 1, and Zs u − V = V_{k − L} (an earlier tail entry)
    obtain ⟨k, hk, hkz⟩ := VChain.freeV_eq_vpath_of_mem frame hV
    have hk2 : (Zs u).2 = (k : ℤ) := by rw [hkz, VChain.vpath_ord frame k]
    have hy := RowAt.vAt_add_len frame ((k : ℤ) - (frame.child.den + frame.child.num))
    rw [sub_add_cancel, RowAt.vAt_nat frame k hk] at hy
    have hY : Zs u - RowAt.Vvec frame = RowAt.vAt frame ((k : ℤ) - (frame.child.den + frame.child.num)) := by
      rw [hkz, hy, add_sub_cancel_right]
    rw [hY]
    apply RefuteTree.Refuted.earlier
    refine ⟨(r + frame.child.den - ((k : ℤ) - (frame.child.den + frame.child.num))).toNat, by omega, ?_⟩
    exact minusSites_Vtail frame r _ hr0 (by omega) (by omega)
  · -- H-exit: Zs u − V = H_{k − d} with 1 ≤ k ≤ d − 1 (an H-block entry, earlier)
    set h : Site := ((Zs u).1 + frame.child.den - (frame.child.num - frame.child.den),
      (Zs u).2 + frame.child.num - (frame.child.num + frame.child.den)) with hh
    obtain ⟨k, hk, hkh⟩ := HChain.freeH_eq_hpath_of_mem frame hH
    have hk1 : 1 ≤ k := by
      by_contra hc0
      have hk0 : k = 0 := by omega
      apply hHne
      exact hkh.trans (by rw [hk0]; rfl)
    have hY : Zs u - RowAt.Vvec frame = RowAt.hAt frame ((k : ℤ) - frame.child.den) := by
      rw [EasyHRank.hAt_sub_den frame hk, ← hkh]
      have hZ : Zs u = h + RowAt.Vvec frame - RowAt.Uvec frame := by
        rw [hh]
        unfold RowAt.Vvec RowAt.Uvec
        ext <;> simp
      rw [hZ]
      abel
    rw [hY]
    apply RefuteTree.Refuted.earlier
    refine ⟨r.toNat + 2 + (-1 - ((k : ℤ) - frame.child.den)).toNat, by omega, ?_⟩
    exact minusSites_H frame r _ (by omega) (by omega)

/-- **The minus-tail entry.** The even tail entry `V_j` (`r + 1 − L ≤ j ≤ −2`) is refuted from the earlier minus-row entries. -/
theorem minus_tail_entry (frame : ChildFrame) (F : Field) (hP : frame.Packet F)
    (hprice : ∀ z ∈ frame.closedPolygon, frame.cutPrice - 1 ≤ frame.price F z ∧ frame.price F z ≤ frame.cutPrice)
    (hdrU : ∀ z, frame.price F (z + frame.child.modifiedDeck.kernel) = frame.price F z - 1)
    (hdrV : ∀ z, frame.price F (z + frame.child.modifiedDeck.transverse) = frame.price F z)
    (hn3 : 3 ≤ frame.child.num) (hd2 : frame.child.den < 2 * frame.child.num)
    {r : ℤ} (hr0 : 0 ≤ r) {j : ℤ} (hjlo : r + 1 - (frame.child.den + frame.child.num) ≤ j) (hj2 : j ≤ -2)
    (hev : EvenSite (RowAt.vAt frame j)) :
    Refuted frame F (-1) (earlierAt frame r (r + frame.child.den - j).toNat) (fun _ => False)
      (RowAt.vAt frame j) := by
  obtain ⟨hon, hod⟩ := frame.child_odd
  obtain ⟨hn0, hnlt, -, -, -⟩ := frame.child_facts
  have hnd : frame.child.num + 2 ≤ frame.child.den := by omega
  obtain ⟨k, hkZ⟩ : ∃ k : ℕ, (k : ℤ) = j + (frame.child.den + frame.child.num) := ⟨(j + (frame.child.den + frame.child.num)).toNat, by omega⟩
  have hkL : (k : ℤ) < frame.child.den + frame.child.num := by omega
  have hk1 : 1 ≤ k := by omega
  have hk2 : k ≤ frame.child.den + frame.child.num - 2 := by omega
  have hwF : RowAt.vAt frame ((k : ℤ)) ∈ frame.freeV := by
    rw [RowAt.vAt_nat frame k hkL]
    exact ListPrefix.vpath_freeV_all frame k hkL
  have hw2 : (RowAt.vAt frame ((k : ℤ))).2 = (k : ℤ) := by
    rw [RowAt.vAt_nat frame k hkL, VChain.vpath_ord frame k]
  have hwx : RowAt.vAt frame ((k : ℤ)) = RowAt.vAt frame j + RowAt.Vvec frame := by
    have h := RowAt.vAt_add_len frame j
    rw [← hkZ] at h
    exact h
  set w : Site := RowAt.vAt frame ((k : ℤ)) with hwdef
  set x : Site := RowAt.vAt frame j with hxdef
  have hw1 : 1 ≤ w.2 := by omega
  have hw2le : w.2 ≤ frame.child.den + frame.child.num - 2 := by omega
  have hevw : EvenSite w := by
    rw [hwx]
    unfold EvenSite at hev ⊢
    unfold RowAt.Vvec
    simp only [Prod.fst_add, Prod.snd_add]
    omega
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
  -- the parameters N = (d − n)/2 and D = (d + n)/2
  obtain ⟨N, hN2⟩ : ∃ N : ℤ, 2 * N = frame.child.den - frame.child.num :=
    ⟨(frame.child.den - frame.child.num) / 2, by omega⟩
  obtain ⟨D, hD2⟩ : ∃ D : ℤ, 2 * D = frame.child.den + frame.child.num :=
    ⟨(frame.child.den + frame.child.num) / 2, by omega⟩
  have hN0 : 0 < N := by omega
  have hND : N < D := by omega
  have H := rotated_NL hP hprice hdrU hdrV N D hN2 hD2 hN0 hND
  obtain ⟨K, p, q, hK2, hs, hpq, hKs, hKr, hcap, hb⟩ :=
    entry_data frame hP hprice hdrU hdrV hd2 hN2 hD2 hN0 hND hwF hevw hw1 hw2le
  -- w₁ + w₂ ≥ 2
  have hs1 := RouteStay.even_grade_strict frame hwF hevw hw1 hw2le
  have ht := ArcRanges.arc_even_range frame hwF hevw hx1 hx2
  have hT3 := ShortPassages.T_ge frame
  have hid : w1T frame.child.num frame.child.den * (w.1 + w.2) =
      (frame.child.den + frame.child.num) * w1s frame.child.num frame.child.den w -
        2 * frame.child.num * w1t frame.child.num frame.child.den w := by
    unfold w1s w1t w1T; ring
  rw [frame_sGrade_eq] at hs1
  rw [frame_tGrade_eq] at ht
  rw [frame_periodDenominator_eq] at ht hT3
  have hw12 : 2 ≤ w.1 + w.2 := by
    have hT0 : 0 < w1T frame.child.num frame.child.den := by omega
    have hpos : 0 < w1T frame.child.num frame.child.den * (w.1 + w.2) := by
      rw [hid]
      nlinarith
    have h1 : 0 < w.1 + w.2 := by
      by_contra hc
      push Not at hc
      nlinarith
    have he2 : (w.1 + w.2) % 2 = 0 := by
      unfold EvenSite at hevw
      exact hevw
    omega
  -- the cone window at the entry
  have hwin : WindowOn (fun x => resRegion frame.child.num frame.child.den x ∧ ConeRoot (w.2 + 1, -w.1) K x)
      (quarterTurnField F) (fun i => parabolaField (-w.1) i) := by
    have hcw := cone_window_NL H (w1T frame.child.num frame.child.den) hN0 hND (by norm_num) hs hpq K hcap
      (w.2 + 1, -w.1) hb
    intro x' hx' i hi
    exact hcw x' ⟨resRegion_sub_ropen (by omega) (by omega) hN0 hND x' hx'.1, hx'.2⟩ i hi
  -- the exit table
  have hexit := minus_tail_hexit frame F hn3 hr0 hjlo hj2 hN2 hD2 hN0 hND H (w := w) (hw2.trans hkZ)
    hw12 hb hK2 hs hpq hKs hKr hcap
  -- the start of the fan
  have hv0 : ((w.2 + 1, 1 - w.1) : Site) ∈ fanSet (resRegion frame.child.num frame.child.den)
      (quarterTurnField F) (w.2 + 1, -w.1) K :=
    ⟨⟨start_resRegion frame hn3 (by omega) hwF hevw hw1 hw2le, start_coneRoot hevw hK2⟩,
      start_contact frame H hN2 hD2 hN0 hn3 hwF hevw hw1 hw2le⟩
  have hstart := minus_tail_refuted frame F (η := -1) (E := earlierAt frame r (r + frame.child.den - j).toNat)
    (C := fun _ => False) hP hwin hexit _ hv0
  have hZs : Zs ((w.2 + 1, 1 - w.1) : Site) = w + (-1, 0) := by
    unfold Zs
    exact Prod.ext (by simp; ring) (by simp)
  rw [hZs, hwx] at hstart
  have hxe : x + (-1, 0) = x + (-1, 0) := rfl
  have hstart' : Refuted frame F (-1) (earlierAt frame r (r + frame.child.den - j).toNat) (fun _ => False)
      (x + (-1, 0)) := by
    have e : x + RowAt.Vvec frame + (-1, 0) - RowAt.Vvec frame = x + (-1, 0) := by abel
    rw [e] at hstart
    exact hstart
  -- the white step at the entry: its prescribed input is x + (−1, 0)
  have hlap0 : laplacian F x = 0 := by
    have e : laplacian F (x + RowAt.Vvec frame) = laplacian F x := RowVEasy.lap_add_Vdeck frame hP x
    rw [← hwx] at e
    rw [← e]
    exact FLatticePaper.Induction.ChildFrame.laplacian_eq_zero_of_freeV frame hP.strips hwF
  have hxV : x + RowAt.Vvec frame ∈ frame.freeV := by
    rw [← hwx]
    exact hwF
  have hperm : permitsQ1 frame F (-1) x (x + (-1, 0)) :=
    Or.inr ⟨hlap0, Or.inl ⟨⟨RowAt.Vvec frame, FLatticePaper.Induction.Vdeck_mem_span frame, Or.inr hxV⟩,
      ⟨RowAt.Vvec frame, FLatticePaper.Induction.Vdeck_mem_span frame, Or.inr ⟨hxV, by
        rw [← hwx, RouteStay.prescribedV_even frame hx1 hx2 hevw]⟩⟩⟩⟩
  exact RefuteTree.Refuted.white hlap0 hperm hstart'

end FLatticePaper.MinusTailEntry
