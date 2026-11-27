import FLatticePaper.Plane.Induction.RowVEasy
import FLatticePaper.Plane.Induction.RowVRefute
import FLatticePaper.Plane.Induction.RouteStay

/-! # The V tail of the minus row: the four certificates at the tail entry `x` itself (`2n ≤ d`)

A tail entry `x = vAt j` (`j < 0`) is a deck translate of a free V root: `w = x + Vdeck` is free V. The certificates of `RowVRefute`
and `RowVEasy` were proved at free roots; here they are restated at `x`. The witness of `freeClosure` and of `FreePresc` is the span
element `Vdeck` (so the prescribed direction is read at `w`), and the nonfree middles transfer by `nonfree_of_add_Vdeck`.

Classes (`w = x + Vdeck`, `η = −1`): `refuted_tail_west` (even `x`, earlier west input: `V_{-1}`, `w = vLast`), `refuted_tail_north`
(odd `x`, north step), `refuted_tail_NW` (odd `x`, NW step), `refuted_tail_north_even` (even `x`, north step). -/

namespace FLatticePaper.RowVTail

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.RefuteTree FLatticePaper.RouteStay FLatticePaper.RowVEasy

theorem evenSite_add_Vdeck {frame : ChildFrame} {x : Site} (he : EvenSite x) : EvenSite (x + Vdeck frame) := by
  unfold EvenSite at he ⊢
  unfold Vdeck
  simp only [Prod.fst_add, Prod.snd_add]
  omega

theorem oddSite_add_Vdeck {frame : ChildFrame} {x : Site} (ho : ¬ EvenSite x) : ¬ EvenSite (x + Vdeck frame) := by
  unfold EvenSite at ho ⊢
  unfold Vdeck
  simp only [Prod.fst_add, Prod.snd_add]
  omega

/-- The laplacian at a tail entry is the laplacian at its free translate. -/
theorem lap_of_witness {frame : ChildFrame} {F : Field} (hP : frame.Packet F) {x : Site}
    (hw : x + Vdeck frame ∈ frame.freeV) : laplacian F x = 0 := by
  have h := frame.laplacian_eq_zero_of_freeV hP.strips hw
  rwa [lap_add_Vdeck frame hP] at h

/-- A permitted input at a tail entry, with the witness `Vdeck` (the free translate is the representative). -/
theorem permits_of_witness {frame : ChildFrame} {F : Field} {η : ℤ} {x i : Site} (hl : laplacian F x = 0)
    (hw : x + Vdeck frame ∈ frame.freeV) (hi : i = x + frame.prescribedV η (x + Vdeck frame)) :
    AuxRankQ1.permitsQ1 frame F η x i :=
  Or.inr ⟨hl, Or.inl ⟨⟨Vdeck frame, Vdeck_mem_span frame, Or.inr hw⟩, ⟨Vdeck frame, Vdeck_mem_span frame, Or.inr ⟨hw, hi⟩⟩⟩⟩

/-- The prescribed direction of an even root (`η = −1`), also at `vLast` (where the prescription is `(η, 0)` as well). -/
theorem prescribedV_even_ne {frame : ChildFrame} {η : ℤ} (hη : η = -1) {w : Site} (hev : EvenSite w)
    (h1 : w ≠ FLatticePaper.Induction.vFirst) : frame.prescribedV η w = (-1, 0) := by
  unfold ChildFrame.prescribedV
  rw [if_neg h1]
  by_cases h2 : w = frame.vLast
  · rw [if_pos h2, hη]
  · rw [if_neg h2, if_pos hev, hη]

/-- **Tail class W (`V_{-1}`).** An even tail entry whose west input is earlier is refuted by the white rule. -/
theorem refuted_tail_west {frame : ChildFrame} {F : Field} (hP : frame.Packet F) {E C : Site → Prop} {x : Site}
    (hw : x + Vdeck frame ∈ frame.freeV) (hev : EvenSite x)
    (h1 : x + Vdeck frame ≠ FLatticePaper.Induction.vFirst) (hE : E (x + (-1, 0))) :
    Refuted frame F (-1) E C x := by
  have hl := lap_of_witness hP hw
  have hpr := prescribedV_even_ne (frame := frame) (η := -1) rfl (evenSite_add_Vdeck hev) h1
  exact Refuted.white hl (permits_of_witness hl hw (by rw [hpr])) (Refuted.earlier hE)

/-- **Tail class N (odd).** An odd tail entry whose north input is earlier is refuted by the white rule. -/
theorem refuted_tail_north {frame : ChildFrame} {F : Field} (hP : frame.Packet F) {E C : Site → Prop} {x : Site}
    (hw : x + Vdeck frame ∈ frame.freeV) (hodd : ¬ EvenSite x)
    (hw1 : 1 ≤ (x + Vdeck frame).2) (hw2 : (x + Vdeck frame).2 ≤ frame.child.den + frame.child.num - 2)
    (hE : E (x + (0, 1))) : Refuted frame F (-1) E C x := by
  have hl := lap_of_witness hP hw
  have hpr := RowVRefute.prescribedV_odd (frame := frame) (η := -1) rfl (oddSite_add_Vdeck hodd)
    (RouteStay.ne_vFirst_of hw1) (RouteStay.ne_vLast_of frame hw2)
  exact Refuted.white hl (permits_of_witness hl hw (by rw [hpr])) (Refuted.earlier hE)

/-- **Tail class NW (odd).** An odd tail entry whose NW input is earlier, through its nonfree north middle. -/
theorem refuted_tail_NW {frame : ChildFrame} {F : Field} (hP : frame.Packet F)
    (hS : ∀ z : Site, 2 - 2 * frame.child.den ≤ frame.sGrade z →
      frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 2 → F z = harmonicGrid z)
    (hO : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 3 * frame.child.den + frame.child.num - 2 → F z = harmonicGrid z)
    {E C : Site → Prop} {x : Site}
    (hw : x + Vdeck frame ∈ frame.freeV) (hodd : ¬ EvenSite x)
    (hw1 : 1 ≤ (x + Vdeck frame).2) (hw2 : (x + Vdeck frame).2 ≤ frame.child.den + frame.child.num - 2)
    (hdiag : ((x + Vdeck frame).1 - 1, (x + Vdeck frame).2 + 1) ∈ frame.freeV) (hE : E (x + (-1, 1))) :
    Refuted frame F (-1) E C x := by
  have hl := lap_of_witness hP hw
  have hpr := RowVRefute.prescribedV_odd (frame := frame) (η := -1) rfl (oddSite_add_Vdeck hodd)
    (RouteStay.ne_vFirst_of hw1) (RouteStay.ne_vLast_of frame hw2)
  obtain ⟨hnf, hwm⟩ := c3_middles hP hS hO hw (oddSite_add_Vdeck hodd) hdiag
  have e : x + (0, 1) + Vdeck frame = x + Vdeck frame + (0, 1) := by abel
  have hnfx : Nonfree frame (x + (0, 1)) := by
    apply nonfree_of_add_Vdeck frame
    rw [e]
    exact hnf
  have hlm : laplacian F (x + (0, 1)) = 0 := by
    rw [← lap_add_Vdeck frame hP (x + (0, 1)), e]
    exact hwm
  have hev : EvenSite (x + (0, 1)) := by
    unfold EvenSite at hodd ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  have hedge : Edge (x + (-1, 1)) (x + (0, 1)) := by
    unfold Edge
    left
    rw [incNeg_even_eq hev]
    ext <;> simp
  have hm : Refuted frame F (-1) E C (x + (0, 1)) :=
    Refuted.white hlm (permits_nonfree_white hlm hnfx hedge) (Refuted.earlier hE)
  exact Refuted.white hl (permits_of_witness hl hw (by rw [hpr])) hm

/-- **Tail class north (even).** An even tail entry whose north input is earlier, through the two nonfree middles (the west odd
middle and the north-west even middle): the depth-3 certificate of `RowVEasy.refuted_C4`, at the tail. -/
theorem refuted_tail_north_even {frame : ChildFrame} {F : Field} (hP : frame.Packet F)
    (hS : ∀ z : Site, 2 - 2 * frame.child.den ≤ frame.sGrade z →
      frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 2 → F z = harmonicGrid z)
    (hO : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 3 * frame.child.den + frame.child.num - 2 → F z = harmonicGrid z)
    (hd2 : 2 * frame.child.num ≤ frame.child.den) {E C : Site → Prop} {x : Site}
    (hw : x + Vdeck frame ∈ frame.freeV) (he : EvenSite x)
    (h1 : 1 ≤ (x + Vdeck frame).2) (h2 : (x + Vdeck frame).2 ≤ frame.child.den + frame.child.num - 2)
    (hE : E (x + (0, 1))) : Refuted frame F (-1) E C x := by
  obtain ⟨hw1, hw2, hl1, hl2⟩ := c4_middles hP hS hO hd2 hw he h1 h2
  have hl := lap_of_witness hP hw
  have hpr := prescribedV_even_ne (frame := frame) (η := -1) rfl (evenSite_add_Vdeck he) (RouteStay.ne_vFirst_of h1)
  have hodd1 : ¬ EvenSite (x + (-1, 0)) := by
    rw [← incNeg_even_eq he]
    exact not_even_incNeg he
  have hev2 : EvenSite (x + (-1, 1)) := by
    unfold EvenSite at he ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  have hy2 : Refuted frame F (-1) E C (x + (-1, 1)) := by
    refine Refuted.white hl2 (permits_nonfree_white hl2 hw2 ?_) (Refuted.earlier hE)
    unfold Edge
    right
    rw [incPos_even_eq' hev2]
    ext <;> simp
  have hz1 : Refuted frame F (-1) E C (x + (-1, 0)) := by
    refine Refuted.white hl1 (permits_nonfree_white hl1 hw1 ?_) hy2
    unfold Edge
    right
    rw [incPos_odd_eq hodd1]
    ext <;> simp
  exact Refuted.white hl (permits_of_witness hl hw (i := x + (-1, 0)) (by rw [hpr])) hz1

/-- **Tail class NW (even).** An even tail entry whose NW input is earlier: the west neighbour is a nonfree white middle, whose
permitted input (its incoming positive neighbour) is the earlier NW entry. -/
theorem refuted_tail_NW_even {frame : ChildFrame} {F : Field} (hP : frame.Packet F)
    (hS : ∀ z : Site, 2 - 2 * frame.child.den ≤ frame.sGrade z →
      frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 2 → F z = harmonicGrid z)
    (hO : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 3 * frame.child.den + frame.child.num - 2 → F z = harmonicGrid z)
    (hd2 : 2 * frame.child.num ≤ frame.child.den) {E C : Site → Prop} {x : Site}
    (hw : x + Vdeck frame ∈ frame.freeV) (he : EvenSite x)
    (h1 : 1 ≤ (x + Vdeck frame).2) (h2 : (x + Vdeck frame).2 ≤ frame.child.den + frame.child.num - 2)
    (hE : E (x + (-1, 1))) : Refuted frame F (-1) E C x := by
  obtain ⟨hw1, -, hl1, -⟩ := c4_middles hP hS hO hd2 hw he h1 h2
  have hl := lap_of_witness hP hw
  have hpr := prescribedV_even_ne (frame := frame) (η := -1) rfl (evenSite_add_Vdeck he) (RouteStay.ne_vFirst_of h1)
  have hodd1 : ¬ EvenSite (x + (-1, 0)) := by
    rw [← incNeg_even_eq he]
    exact not_even_incNeg he
  have hedge : Edge (x + (-1, 1)) (x + (-1, 0)) := by
    unfold Edge
    right
    rw [incPos_odd_eq hodd1]
    ext <;> simp
  have hz1 : Refuted frame F (-1) E C (x + (-1, 0)) :=
    Refuted.white hl1 (permits_nonfree_white hl1 hw1 hedge) (Refuted.earlier hE)
  exact Refuted.white hl (permits_of_witness hl hw (i := x + (-1, 0)) (by rw [hpr])) hz1

/-- **The chain identity on the tail.** For `-L ≤ j ≤ -2`, the tail entry `vAt j` has free translate `vpath (j+L)`, and the next tail
entry is the chain successor of that translate, shifted back. -/
theorem vAt_tail_chain (frame : ChildFrame) {j : ℤ} (hj1 : -(frame.child.den + frame.child.num) ≤ j) (hj2 : j ≤ -2) :
    RowAt.vAt frame j + Vdeck frame = VChain.vpath frame (j + (frame.child.den + frame.child.num)).toNat ∧
      RowAt.vAt frame (j + 1) = VChain.vsucc frame (RowAt.vAt frame j + Vdeck frame) - Vdeck frame := by
  have hw : RowAt.vAt frame j + Vdeck frame = VChain.vpath frame (j + (frame.child.den + frame.child.num)).toNat := by
    rw [RoutePlus.vAt_neg_eq frame j hj1 (by omega)]
    exact sub_add_cancel _ _
  refine ⟨hw, ?_⟩
  rw [RoutePlus.vAt_neg_eq frame (j + 1) (by omega) (by omega), hw]
  rw [show (j + 1 + (frame.child.den + frame.child.num)).toNat = (j + (frame.child.den + frame.child.num)).toNat + 1 by omega,
    VChain.vpath_succ]
  rfl

/-- **The tail certificate for `-L < j ≤ -2`.** The entry `vAt j` is refuted from its chain successor `vAt (j+1)`, which is its
north or north-west neighbour shifted by `Vdeck` (the case of the odd or even parity, and the north or NW step of the chain). -/
theorem refuted_tail {frame : ChildFrame} {F : Field} (hP : frame.Packet F)
    (hS : ∀ z : Site, 2 - 2 * frame.child.den ≤ frame.sGrade z →
      frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 2 → F z = harmonicGrid z)
    (hO : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 3 * frame.child.den + frame.child.num - 2 → F z = harmonicGrid z)
    (hd2 : 2 * frame.child.num ≤ frame.child.den) {E C : Site → Prop} {j : ℤ}
    (hj1 : -(frame.child.den + frame.child.num) + 1 ≤ j) (hj2 : j ≤ -2)
    (hE : E (RowAt.vAt frame (j + 1))) : Refuted frame F (-1) E C (RowAt.vAt frame j) := by
  have hL : (0 : ℤ) < frame.child.den + frame.child.num := by
    obtain ⟨hn0, hnd, -, -, -⟩ := frame.child_facts
    omega
  obtain ⟨hw_eq, hsucc⟩ := vAt_tail_chain frame (j := j) (by omega) hj2
  have hk : ((j + (frame.child.den + frame.child.num)).toNat : ℤ) = j + (frame.child.den + frame.child.num) :=
    Int.toNat_of_nonneg (by omega)
  have hfree : RowAt.vAt frame j + Vdeck frame ∈ frame.freeV := by
    rw [hw_eq]
    apply VChain.vpath_free frame
    rw [hk]
    omega
  have hord : (RowAt.vAt frame j + Vdeck frame).2 = j + (frame.child.den + frame.child.num) := by
    rw [hw_eq, VChain.vpath_ord, hk]
  have hw1 : 1 ≤ (RowAt.vAt frame j + Vdeck frame).2 := by
    rw [hord]
    omega
  have hw2 : (RowAt.vAt frame j + Vdeck frame).2 ≤ frame.child.den + frame.child.num - 2 := by
    rw [hord]
    omega
  have hne : RowAt.vAt frame j + Vdeck frame ≠ frame.vLast := RouteStay.ne_vLast_of frame hw2
  by_cases hev : EvenSite (RowAt.vAt frame j)
  · by_cases hN : ((RowAt.vAt frame j + Vdeck frame).1, (RowAt.vAt frame j + Vdeck frame).2 + 1) ∈ frame.freeV
    · have e : RowAt.vAt frame (j + 1) = RowAt.vAt frame j + (0, 1) := by
        rw [hsucc]
        unfold VChain.vsucc
        rw [if_pos hN]
        ext <;> simp
        ring
      rw [e] at hE
      exact refuted_tail_north_even hP hS hO hd2 hfree hev hw1 hw2 hE
    · have e : RowAt.vAt frame (j + 1) = RowAt.vAt frame j + (-1, 1) := by
        rw [hsucc]
        unfold VChain.vsucc
        rw [if_neg hN]
        ext <;> simp <;> ring
      rw [e] at hE
      exact refuted_tail_NW_even hP hS hO hd2 hfree hev hw1 hw2 hE
  · by_cases hN : ((RowAt.vAt frame j + Vdeck frame).1, (RowAt.vAt frame j + Vdeck frame).2 + 1) ∈ frame.freeV
    · have e : RowAt.vAt frame (j + 1) = RowAt.vAt frame j + (0, 1) := by
        rw [hsucc]
        unfold VChain.vsucc
        rw [if_pos hN]
        ext <;> simp
        ring
      rw [e] at hE
      exact refuted_tail_north hP hfree hev hw1 hw2 hE
    · have e : RowAt.vAt frame (j + 1) = RowAt.vAt frame j + (-1, 1) := by
        rw [hsucc]
        unfold VChain.vsucc
        rw [if_neg hN]
        ext <;> simp <;> ring
      have hdiag : ((RowAt.vAt frame j + Vdeck frame).1 - 1, (RowAt.vAt frame j + Vdeck frame).2 + 1) ∈ frame.freeV := by
        have hv := VChain.vsucc_mem frame hfree hne
        unfold VChain.vsucc at hv
        rwa [if_neg hN] at hv
      rw [e] at hE
      exact refuted_tail_NW hP hS hO hfree hev hw1 hw2 hdiag hE

/-- **The tail entry `V_{-1}`.** It is the translate `vLast − Vdeck`, an even root whose west neighbour `H_{-1}` is earlier. -/
theorem refuted_tail_last {frame : ChildFrame} {F : Field} (hP : frame.Packet F) {E C : Site → Prop}
    (hE : E (RowAt.vAt frame (-1) + (-1, 0))) : Refuted frame F (-1) E C (RowAt.vAt frame (-1)) := by
  obtain ⟨hn0, hnd, -, -, -⟩ := frame.child_facts
  have hk : ((-1 + (frame.child.den + frame.child.num)).toNat) = (frame.child.num + frame.child.den - 1).toNat := by
    congr 1
    ring
  have hw : RowAt.vAt frame (-1) + Vdeck frame = frame.vLast := by
    rw [RoutePlus.vAt_neg_eq frame (-1) (by omega) (by omega), hk, ← VChain.vLast_eq_vpath]
    exact sub_add_cancel _ _
  have hw' : RowAt.vAt frame (-1) + Vdeck frame ∈ frame.freeV := by
    rw [hw]
    exact FLatticePaper.FreeVOrdinate.vLast_mem_freeV frame
  have hevL : EvenSite frame.vLast := by
    unfold EvenSite ChildFrame.vLast
    simp only
    omega
  have hev : EvenSite (RowAt.vAt frame (-1)) := by
    have h : EvenSite (RowAt.vAt frame (-1) + Vdeck frame) := by
      rw [hw]
      exact hevL
    unfold EvenSite at h ⊢
    unfold Vdeck at h
    simp only [Prod.fst_add, Prod.snd_add] at h
    omega
  have h1 : RowAt.vAt frame (-1) + Vdeck frame ≠ FLatticePaper.Induction.vFirst := by
    apply RouteStay.ne_vFirst_of
    rw [hw]
    show 1 ≤ frame.child.num + frame.child.den - 1
    omega
  exact refuted_tail_west hP hw' hev h1 hE

end FLatticePaper.RowVTail

