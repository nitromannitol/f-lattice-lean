import FLatticePaper.Plane.Induction.RowVTail
import FLatticePaper.Plane.Induction.CollarTop
import FLatticePaper.Plane.Induction.FreeCutPred
import FLatticePaper.Plane.Induction.EasyHRank
import FLatticePaper.Plane.Induction.Coherence

/-! # The plus row's V family (η = +1), by the reflection `σ z = vLast − z`

`σ` is the involution `z ↦ vLast − z = (1,−1) + Vdeck − z`. It preserves the free V cut (`FreeCutPred.freeV_reflect`), the free H cut
(`CollarTop.freeH_reflect`, with `centre = U + V + (1,−1)`), hence `Nonfree` (the span is symmetric and contains `U − V`), and it swaps the
two incoming inputs of a site of each parity. This module gives the reflection of `freeV` and `Nonfree`; the plus certificates use these
for the nonfree middles, and the minus certificates of `RowVEasy` / `RowVTail` at the reflected sites. -/

namespace FLatticePaper.RowVPlus

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.RefuteTree FLatticePaper.RouteStay FLatticePaper.RowVEasy

theorem Uvec_mem_span_plus (frame : ChildFrame) : RowAt.Uvec frame ∈ frame.child.modifiedDeck.span :=
  ⟨1, 0, (EasyHRank.combine_one_zero_eq_Uvec frame).symm⟩

theorem freeV_sigma_fwd (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV) : frame.vLast - z ∈ frame.freeV := by
  have h := FreeCutPred.freeV_reflect frame (x := z.1) (y := z.2) hz
  have e : frame.vLast - z = (frame.child.num - frame.child.den + 1 - z.1, frame.child.num + frame.child.den - 1 - z.2) := by
    ext <;> simp [ChildFrame.vLast]
  rw [e]
  exact h

/-- **The free V cut is invariant under `σ z = vLast − z`.** -/
theorem freeV_sigma (frame : ChildFrame) {z : Site} : z ∈ frame.freeV ↔ frame.vLast - z ∈ frame.freeV := by
  refine ⟨freeV_sigma_fwd frame, fun h => ?_⟩
  have h2 := freeV_sigma_fwd frame h
  rwa [sub_sub_cancel] at h2

/-- **`Nonfree` is invariant under `σ`.** The free H cut is reflected by `centre − (w + V) = U + (1,−1) − w`, which is `σ`
up to the span element `U − V`. -/
theorem nonfree_sigma {frame : ChildFrame} {z : Site} (h : Nonfree frame z) : Nonfree frame (frame.vLast - z) := by
  intro v hv hmem
  rcases hmem with hH | hV
  · have hr := CollarTop.freeH_reflect frame hH
    have key : frame.centre - (frame.vLast - z + v + frame.child.modifiedDeck.transverse) =
        z + ((RowAt.Uvec frame - frame.child.modifiedDeck.transverse) - v) := by
      rw [CollarTop.centre_eq]
      ext <;> simp [ChildFrame.vLast, RowAt.Uvec, ChildFrame.child_modifiedDeck_transverse] <;> ring
    have hs : (RowAt.Uvec frame - frame.child.modifiedDeck.transverse) - v ∈ frame.child.modifiedDeck.span :=
      FreeClosure.span_sub (FreeClosure.span_sub (Uvec_mem_span_plus frame) (by
        rw [ChildFrame.child_modifiedDeck_transverse]
        exact Vdeck_mem_span frame)) hv
    exact h _ hs (Or.inl (by rw [← key]; exact hr))
  · have hr := freeV_sigma_fwd frame hV
    have key : frame.vLast - (frame.vLast - z + v) = z + -v := by abel
    have hs : -v ∈ frame.child.modifiedDeck.span := span_neg_mem hv
    exact h (-v) hs (Or.inr (by rw [← key]; exact hr))

theorem evenSite_sigma (frame : ChildFrame) (p : Site) : EvenSite (frame.vLast - p) ↔ EvenSite p := by
  unfold EvenSite ChildFrame.vLast
  simp only [Prod.fst_sub, Prod.snd_sub]
  omega

theorem prescribedV_odd_plus {frame : ChildFrame} {x : Site} (hodd : ¬ EvenSite x)
    (h1 : x ≠ FLatticePaper.Induction.vFirst) (h2 : x ≠ frame.vLast) : frame.prescribedV 1 x = (0, -1) := by
  unfold ChildFrame.prescribedV
  rw [if_neg h1, if_neg h2, if_neg hodd]

theorem prescribedV_even_plus {frame : ChildFrame} {x : Site} (hev : EvenSite x)
    (h1 : x ≠ FLatticePaper.Induction.vFirst) : frame.prescribedV 1 x = (1, 0) := by
  unfold ChildFrame.prescribedV
  rw [if_neg h1]
  by_cases h2 : x = frame.vLast
  · rw [if_pos h2]
  · rw [if_neg h2, if_pos hev]

/-- A permitted input at a free root (witness `0`), for either sign. -/
theorem permits_free_zero {frame : ChildFrame} {F : Field} {η : ℤ} {x i : Site} (hl : laplacian F x = 0)
    (hx : x ∈ frame.freeV) (hi : i = x + frame.prescribedV η x) : AuxRankQ1.permitsQ1 frame F η x i :=
  Or.inr ⟨hl, Or.inl ⟨FreeWebClaims.fc_of_freeV frame hx, 0, zero_mem_span frame,
    Or.inr ⟨by rw [add_zero]; exact hx, by rw [add_zero]; exact hi⟩⟩⟩

/-- The even plus middles: `m1 = x+(1,0)` (odd) and `m2 = x+(1,-1)` (even) are nonfree (the minus `wne_nonfree` at `σ x`, reflected),
with laplacian zero (the route lemmas at the plus sites). -/
theorem plus_even_middles {frame : ChildFrame} {F : Field} (_hP : frame.Packet F)
    (hS : ∀ z : Site, 2 - 2 * frame.child.den ≤ frame.sGrade z →
      frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 2 → F z = harmonicGrid z)
    (hO : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 3 * frame.child.den + frame.child.num - 2 → F z = harmonicGrid z)
    (hd2 : 2 * frame.child.num ≤ frame.child.den) {x : Site} (hx : x ∈ frame.freeV) (he : EvenSite x)
    (h1 : 1 ≤ x.2) (h2 : x.2 ≤ frame.child.den + frame.child.num - 2) :
    Nonfree frame (x + (1, 0)) ∧ Nonfree frame (x + (1, -1)) ∧
      laplacian F (x + (1, 0)) = 0 ∧ laplacian F (x + (1, -1)) = 0 := by
  obtain ⟨hn0, hlt, hnd2, -, -⟩ := frame.child_facts
  obtain ⟨hs1, hs2⟩ := even_grade_strict frame hx he h1 h2
  have hsx : frame.vLast - x ∈ frame.freeV := freeV_sigma_fwd frame hx
  have hse : EvenSite (frame.vLast - x) := (evenSite_sigma frame x).2 he
  have hσ2 : (frame.vLast - x).2 = frame.child.num + frame.child.den - 1 - x.2 := by
    simp [ChildFrame.vLast]
  obtain ⟨hw1, hw2⟩ := wne_nonfree frame hsx hse (by omega) (by omega)
  have e1 : frame.vLast - (frame.vLast - x + (-1, 0)) = x + (1, 0) := by
    ext <;> simp [ChildFrame.vLast]
    ring
  have e2 : frame.vLast - (frame.vLast - x + (-1, 1)) = x + (1, -1) := by
    ext <;> simp [ChildFrame.vLast] <;> ring
  have hn1 : Nonfree frame (x + (1, 0)) := by
    have h := nonfree_sigma hw1
    rwa [e1] at h
  have hn2 : Nonfree frame (x + (1, -1)) := by
    have h := nonfree_sigma hw2
    rwa [e2] at h
  have hodd1 : ¬ EvenSite (x + (1, 0)) := by
    unfold EvenSite at he ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  have hev2 : EvenSite (x + (1, -1)) := by
    unfold EvenSite at he ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  have hc1 : ¬ EvenSite (x + (1, 0)) := hodd1
  refine ⟨hn1, hn2, ?_, ?_⟩
  · refine route_lap_odd frame hS hO hc1 ?_ ?_ ?_ ?_ ?_ ?_ <;> (rw [sGrade_add_pair]; omega)
  · refine route_lap_even frame hS hO hev2 ?_ ?_ ?_ ?_ ?_ ?_ <;> (rw [sGrade_add_pair]; omega)

/-- The south middle of an odd plus root is nonfree and white: the reflection of `c3_middles` at `σ x`, and the route lemma at the
plus middle, with the grade window `s(x) = 2n − s(σ x)`. -/
theorem plus_odd_middle {frame : ChildFrame} {F : Field} (hP : frame.Packet F)
    (hS : ∀ z : Site, 2 - 2 * frame.child.den ≤ frame.sGrade z →
      frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 2 → F z = harmonicGrid z)
    (hO : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 3 * frame.child.den + frame.child.num - 2 → F z = harmonicGrid z)
    (_hd2 : 2 * frame.child.num ≤ frame.child.den)
    {x : Site} (hx : x ∈ frame.freeV) (hodd : ¬ EvenSite x) (hdiag : (x.1 + 1, x.2 - 1) ∈ frame.freeV) :
    Nonfree frame (x + (0, -1)) ∧ laplacian F (x + (0, -1)) = 0 := by
  obtain ⟨hn0, hlt, hnd2, -, hT⟩ := frame.child_facts
  have hsx : frame.vLast - x ∈ frame.freeV := freeV_sigma_fwd frame hx
  have hodd' : ¬ EvenSite (frame.vLast - x) := fun h => hodd ((evenSite_sigma frame x).1 h)
  have hdiag' : ((frame.vLast - x).1 - 1, (frame.vLast - x).2 + 1) ∈ frame.freeV := by
    rw [show ((frame.vLast - x).1 - 1, (frame.vLast - x).2 + 1) = frame.vLast - (x + (1, -1)) from
      Prod.ext (by simp [ChildFrame.vLast]; ring) (by simp [ChildFrame.vLast]; ring)]
    exact freeV_sigma_fwd frame hdiag
  have hc := c3_middles hP hS hO hsx hodd' hdiag'
  have hn : Nonfree frame (x + (0, -1)) := by
    have h := nonfree_sigma hc.1
    have e : frame.vLast - (frame.vLast - x + (0, 1)) = x + (0, -1) := by
      ext <;> simp [ChildFrame.vLast]
      ring
    rwa [e] at h
  obtain ⟨-, hsle, -, hslo⟩ := V2Arrows.freeV_odd_facts frame hsx hodd' hdiag'
  have hsig : frame.sGrade (frame.vLast - x) = 2 * frame.child.num - frame.sGrade x := by
    have h2 := FreeVWindow.sGrade_vLast frame
    have h3 : frame.sGrade (frame.vLast - x) = frame.sGrade frame.vLast - frame.sGrade x := by
      unfold ChildFrame.sGrade
      simp only [Prod.fst_sub, Prod.snd_sub]
      ring
    omega
  have hev : EvenSite (x + (0, -1)) := by
    unfold EvenSite at hodd ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  refine ⟨hn, ?_⟩
  refine route_lap_even frame hS hO hev ?_ ?_ ?_ ?_ ?_ ?_ <;> (rw [sGrade_add_pair]; omega)

/-- **Plus class (odd, south predecessor).** An odd free root whose prescribed south input is earlier. -/
theorem refuted_plus_odd_S {frame : ChildFrame} {F : Field} (hP : frame.Packet F) {E C : Site → Prop} {x : Site}
    (hx : x ∈ frame.freeV) (hodd : ¬ EvenSite x) (h1 : x ≠ FLatticePaper.Induction.vFirst) (h2 : x ≠ frame.vLast)
    (hE : E (x + (0, -1))) : Refuted frame F 1 E C x := by
  have hl : laplacian F x = 0 := frame.laplacian_eq_zero_of_freeV hP.strips hx
  have hpr := prescribedV_odd_plus (frame := frame) hodd h1 h2
  exact Refuted.white hl (permits_free_zero hl hx (i := x + (0, -1)) (by rw [hpr])) (Refuted.earlier hE)

/-- **Plus class (odd, south-east predecessor).** The prescribed south input is a nonfree white middle, whose east-input
`x + (1,-1)` is the earlier entry. -/
theorem refuted_plus_odd_SE {frame : ChildFrame} {F : Field} (hP : frame.Packet F)
    (hS : ∀ z : Site, 2 - 2 * frame.child.den ≤ frame.sGrade z →
      frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 2 → F z = harmonicGrid z)
    (hO : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 3 * frame.child.den + frame.child.num - 2 → F z = harmonicGrid z)
    (hd2 : 2 * frame.child.num ≤ frame.child.den) {E C : Site → Prop} {x : Site}
    (hx : x ∈ frame.freeV) (hodd : ¬ EvenSite x) (h1 : x ≠ FLatticePaper.Induction.vFirst) (h2 : x ≠ frame.vLast)
    (hdiag : (x.1 + 1, x.2 - 1) ∈ frame.freeV) (hE : E (x + (1, -1))) : Refuted frame F 1 E C x := by
  have hl : laplacian F x = 0 := frame.laplacian_eq_zero_of_freeV hP.strips hx
  have hpr := prescribedV_odd_plus (frame := frame) hodd h1 h2
  obtain ⟨hnf, hlm⟩ := plus_odd_middle hP hS hO hd2 hx hodd hdiag
  have hev : EvenSite (x + (0, -1)) := by
    unfold EvenSite at hodd ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  have hedge : Edge (x + (1, -1)) (x + (0, -1)) := by
    unfold Edge
    right
    rw [incPos_even_eq' hev]
    ext <;> simp
  have hm : Refuted frame F 1 E C (x + (0, -1)) :=
    Refuted.white hlm (permits_nonfree_white hlm hnf hedge) (Refuted.earlier hE)
  exact Refuted.white hl (permits_free_zero hl hx (i := x + (0, -1)) (by rw [hpr])) hm

/-- **Plus class (even, south predecessor).** The chain `x → x+(1,0) → x+(1,-1) → x+(0,-1)` through two nonfree middles. -/
theorem refuted_plus_even_S {frame : ChildFrame} {F : Field} (hP : frame.Packet F)
    (hS : ∀ z : Site, 2 - 2 * frame.child.den ≤ frame.sGrade z →
      frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 2 → F z = harmonicGrid z)
    (hO : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 3 * frame.child.den + frame.child.num - 2 → F z = harmonicGrid z)
    (hd2 : 2 * frame.child.num ≤ frame.child.den) {E C : Site → Prop} {x : Site}
    (hx : x ∈ frame.freeV) (he : EvenSite x) (h1 : 1 ≤ x.2) (h2 : x.2 ≤ frame.child.den + frame.child.num - 2)
    (h0 : x ≠ FLatticePaper.Induction.vFirst) (hE : E (x + (0, -1))) : Refuted frame F 1 E C x := by
  obtain ⟨hn1, hn2, hl1, hl2⟩ := plus_even_middles hP hS hO hd2 hx he h1 h2
  have hl : laplacian F x = 0 := frame.laplacian_eq_zero_of_freeV hP.strips hx
  have hpr := prescribedV_even_plus (frame := frame) he h0
  have hodd1 : ¬ EvenSite (x + (1, 0)) := by
    unfold EvenSite at he ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  have hev2 : EvenSite (x + (1, -1)) := by
    unfold EvenSite at he ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  have edge2 : Edge (x + (0, -1)) (x + (1, -1)) := by
    unfold Edge
    left
    rw [incNeg_even_eq hev2]
    ext <;> simp
  have edge1 : Edge (x + (1, -1)) (x + (1, 0)) := by
    unfold Edge
    left
    rw [H0Core.incomingNeg_of_not_even _ hodd1]
    ext <;> simp
    ring
  have hm2 : Refuted frame F 1 E C (x + (1, -1)) :=
    Refuted.white hl2 (permits_nonfree_white hl2 hn2 edge2) (Refuted.earlier hE)
  have hm1 : Refuted frame F 1 E C (x + (1, 0)) :=
    Refuted.white hl1 (permits_nonfree_white hl1 hn1 edge1) hm2
  exact Refuted.white hl (permits_free_zero hl hx (i := x + (1, 0)) (by rw [hpr])) hm1

/-- **Plus class (even, south-east predecessor).** The chain `x → x+(1,0) → x+(1,-1)` (the earlier entry). -/
theorem refuted_plus_even_SE {frame : ChildFrame} {F : Field} (hP : frame.Packet F)
    (hS : ∀ z : Site, 2 - 2 * frame.child.den ≤ frame.sGrade z →
      frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 2 → F z = harmonicGrid z)
    (hO : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 3 * frame.child.den + frame.child.num - 2 → F z = harmonicGrid z)
    (hd2 : 2 * frame.child.num ≤ frame.child.den) {E C : Site → Prop} {x : Site}
    (hx : x ∈ frame.freeV) (he : EvenSite x) (h1 : 1 ≤ x.2) (h2 : x.2 ≤ frame.child.den + frame.child.num - 2)
    (h0 : x ≠ FLatticePaper.Induction.vFirst) (hE : E (x + (1, -1))) : Refuted frame F 1 E C x := by
  obtain ⟨hn1, -, hl1, -⟩ := plus_even_middles hP hS hO hd2 hx he h1 h2
  have hl : laplacian F x = 0 := frame.laplacian_eq_zero_of_freeV hP.strips hx
  have hpr := prescribedV_even_plus (frame := frame) he h0
  have hodd1 : ¬ EvenSite (x + (1, 0)) := by
    unfold EvenSite at he ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  have edge1 : Edge (x + (1, -1)) (x + (1, 0)) := by
    unfold Edge
    left
    rw [H0Core.incomingNeg_of_not_even _ hodd1]
    ext <;> simp
    ring
  have hm1 : Refuted frame F 1 E C (x + (1, 0)) :=
    Refuted.white hl1 (permits_nonfree_white hl1 hn1 edge1) (Refuted.earlier hE)
  exact Refuted.white hl (permits_free_zero hl hx (i := x + (1, 0)) (by rw [hpr])) hm1

/-- The plus row's V block: `V_i` sits at position `(r+1) + 1 + i`, for `0 ≤ i ≤ L − r − 2` (`V_0` in the `H_0, V_0` pair). -/
theorem getV_plus (r L d : ℤ) {i : ℕ} (hi : (i : ℤ) ≤ L - r - 2) :
    (FreeRows.plusRow r L d)[(r + 1).toNat + 1 + i]? = some (FreeRows.FreeLabel.V (i : ℤ)) := by
  unfold FreeRows.plusRow
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · rw [List.getElem?_append_left (by simp), List.getElem?_append_left (by simp),
      List.getElem?_append_right (by simp)]
    simp
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by simp; omega)]
    simp only [List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil]
    rw [show (r + 1).toNat + 1 + i - ((r + 1).toNat + 1 + 1) = i - 1 by omega, List.getElem?_map,
      List.getElem?_range (by omega)]
    have hi1 : (i - 1 : ℕ) + 1 = i := by omega
    simp only [Option.map_some]
    congr 2
    omega

/-- The plus row of the frame, as sites. -/
noncomputable def plusRowSites (frame : ChildFrame) (r : ℤ) : List Site :=
  FreeRows.rowSites (RowAt.vAt frame) (RowAt.hAt frame) (FreeRows.plusRow r (frame.child.den + frame.child.num) frame.child.den)

theorem plusRowSites_getElem? (frame : ChildFrame) (r : ℤ) {k : ℕ} {ℓ : FreeRows.FreeLabel}
    (h : (FreeRows.plusRow r (frame.child.den + frame.child.num) frame.child.den)[k]? = some ℓ) :
    (plusRowSites frame r)[k]? = some (FreeRows.labelSite (RowAt.vAt frame) (RowAt.hAt frame) ℓ) := by
  unfold plusRowSites FreeRows.rowSites
  rw [List.getElem?_map, h]
  rfl

/-- **The plus V class.** The entry `vAt (k+1)` is refuted from its predecessor `vAt k`, by the chain step between them: the
north step `vAt (k+1) = vAt k + (0,1)` makes the predecessor the south neighbour, the NW step makes it the south-east neighbour. -/
theorem plus_V_refuted {frame : ChildFrame} {F : Field} (hP : frame.Packet F)
    (hS : ∀ z : Site, 2 - 2 * frame.child.den ≤ frame.sGrade z →
      frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 2 → F z = harmonicGrid z)
    (hO : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 3 * frame.child.den + frame.child.num - 2 → F z = harmonicGrid z)
    (hd2 : 2 * frame.child.num ≤ frame.child.den) {r : ℤ} (hr : 0 ≤ r) {E C : Site → Prop} (k : ℕ)
    (hk : (k : ℤ) + r + 3 ≤ frame.child.den + frame.child.num)
    (hE : E (RowAt.vAt frame (k : ℤ))) : Refuted frame F 1 E C (RowAt.vAt frame ((k + 1 : ℕ) : ℤ)) := by
  obtain ⟨hn0, hnd, -, -, -⟩ := frame.child_facts
  have hk1 : ((k : ℕ) : ℤ) < frame.child.den + frame.child.num := by omega
  have hk2 : ((k + 1 : ℕ) : ℤ) < frame.child.den + frame.child.num := by push_cast; omega
  rw [RowAt.vAt_nat frame (k + 1) hk2]
  rw [RowAt.vAt_nat frame k hk1] at hE
  have hdef : VChain.vpath frame (k + 1) = VChain.vsucc frame (VChain.vpath frame k) := VChain.vpath_succ frame k
  have hq : VChain.vpath frame k ∈ frame.freeV := VChain.vpath_free frame k (by omega)
  have hp : VChain.vpath frame (k + 1) ∈ frame.freeV := VChain.vpath_free frame (k + 1) (by push_cast; omega)
  have hpord : (VChain.vpath frame (k + 1)).2 = ((k + 1 : ℕ) : ℤ) := VChain.vpath_ord frame (k + 1)
  have h1 : 1 ≤ (VChain.vpath frame (k + 1)).2 := by rw [hpord]; push_cast; omega
  have h2 : (VChain.vpath frame (k + 1)).2 ≤ frame.child.den + frame.child.num - 2 := by
    rw [hpord]; push_cast; omega
  have h0 : VChain.vpath frame (k + 1) ≠ FLatticePaper.Induction.vFirst := RouteStay.ne_vFirst_of h1
  have hl2 : VChain.vpath frame (k + 1) ≠ frame.vLast := RouteStay.ne_vLast_of frame h2
  by_cases hN : ((VChain.vpath frame k).1, (VChain.vpath frame k).2 + 1) ∈ frame.freeV
  · have hpq : VChain.vpath frame (k + 1) = VChain.vpath frame k + (0, 1) := by
      rw [hdef]
      unfold VChain.vsucc
      rw [if_pos hN]
      ext <;> simp
    have e : VChain.vpath frame k = VChain.vpath frame (k + 1) + (0, -1) := by
      rw [hpq]
      ext <;> simp
    rw [e] at hE
    by_cases hev : EvenSite (VChain.vpath frame (k + 1))
    · exact refuted_plus_even_S hP hS hO hd2 hp hev h1 h2 h0 hE
    · exact refuted_plus_odd_S hP hp hev h0 hl2 hE
  · have hpq : VChain.vpath frame (k + 1) = VChain.vpath frame k + (-1, 1) := by
      rw [hdef]
      unfold VChain.vsucc
      rw [if_neg hN]
      ext <;> simp
      ring
    have e : VChain.vpath frame k = VChain.vpath frame (k + 1) + (1, -1) := by
      rw [hpq]
      ext <;> simp
    rw [e] at hE
    by_cases hev : EvenSite (VChain.vpath frame (k + 1))
    · exact refuted_plus_even_SE hP hS hO hd2 hp hev h1 h2 h0 hE
    · have hdiag : ((VChain.vpath frame (k + 1)).1 + 1, (VChain.vpath frame (k + 1)).2 - 1) ∈ frame.freeV := by
        have hc : ((VChain.vpath frame (k + 1)).1 + 1, (VChain.vpath frame (k + 1)).2 - 1) = VChain.vpath frame k := by
          rw [hpq]
          ext <;> simp
        rw [hc]
        exact hq
      exact refuted_plus_odd_SE hP hS hO hd2 hp hev h0 hl2 hdiag hE

/-- **The `href` of the plus V block (easy regime).** The entry at a V position `k` of the plus row (`(r+1)+2 ≤ k`, up to the end of
the block) is refuted from the earlier entries of the row, with the empty core `C = False`. -/
theorem plus_href_row {frame : ChildFrame} {F : Field} (hP : frame.Packet F)
    (hS : ∀ z : Site, 2 - 2 * frame.child.den ≤ frame.sGrade z →
      frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 2 → F z = harmonicGrid z)
    (hO : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 3 * frame.child.den + frame.child.num - 2 → F z = harmonicGrid z)
    (hd2 : 2 * frame.child.num ≤ frame.child.den) {r : ℤ} (hr : 0 ≤ r)
    (k : ℕ) (e : Site) (hk : (plusRowSites frame r)[k]? = some e)
    (hlo : (r + 1).toNat + 2 ≤ k)
    (hhi : k ≤ (r + 1).toNat + 1 + (frame.child.den + frame.child.num - r - 2).toNat) :
    Refuted frame F 1 (fun x => ∃ k' : ℕ, k' < k ∧ (plusRowSites frame r)[k']? = some x) (fun _ => False) e := by
  obtain ⟨m, rfl⟩ : ∃ m, k = (r + 1).toNat + 2 + m := ⟨k - ((r + 1).toNat + 2), by omega⟩
  have hi : ((m + 1 : ℕ) : ℤ) ≤ frame.child.den + frame.child.num - r - 2 := by
    push_cast
    omega
  have hrow : (FreeRows.plusRow r (frame.child.den + frame.child.num) frame.child.den)[(r + 1).toNat + 2 + m]? =
      some (FreeRows.FreeLabel.V ((m + 1 : ℕ) : ℤ)) := by
    have h := getV_plus r (frame.child.den + frame.child.num) frame.child.den (i := m + 1) hi
    rw [show (r + 1).toNat + 1 + (m + 1) = (r + 1).toNat + 2 + m by omega] at h
    exact h
  have he : e = RowAt.vAt frame ((m + 1 : ℕ) : ℤ) := by
    rw [plusRowSites_getElem? frame r hrow] at hk
    exact (Option.some.inj hk).symm
  subst he
  have hi' : ((m : ℕ) : ℤ) ≤ frame.child.den + frame.child.num - r - 2 := by
    push_cast at hi ⊢
    omega
  have hE : ∃ k' : ℕ, k' < (r + 1).toNat + 2 + m ∧ (plusRowSites frame r)[k']? = some (RowAt.vAt frame (m : ℤ)) := by
    refine ⟨(r + 1).toNat + 1 + m, by omega, ?_⟩
    rw [plusRowSites_getElem? frame r (getV_plus r (frame.child.den + frame.child.num) frame.child.den (i := m) hi')]
    rfl
  have hk3 : (m : ℤ) + r + 3 ≤ frame.child.den + frame.child.num := by
    push_cast at hi
    omega
  exact plus_V_refuted hP hS hO hd2 hr m hk3 hE

end FLatticePaper.RowVPlus

