import FLatticePaper.Plane.Induction.RouteStay
import FLatticePaper.Plane.Induction.ShortPassages
import FLatticePaper.Plane.Induction.VGradeBounds
import FLatticePaper.Plane.Induction.V2Arrows
import FLatticePaper.Plane.Induction.VStrict
import FLatticePaper.Plane.Induction.RowVRefute
import FLatticePaper.Plane.Induction.PassageRank
import FLatticePaper.Plane.Induction.NonfreeBridge
import FLatticePaper.Plane.Induction.Q3White

/-! # The easy classes C3 and C4 of the minus row's V entries (`2n ≤ d`), by the route lemmas

The entry `x` is a free V site with negative ordinate (so `x + V` has positive ordinate, `V = Vdeck`, `s(V) = 0`).
* C4 (`x` even, north step): `x → x + (−1,0)` (odd, nonfree white) `→ x + (−1,1)` (even, nonfree white) `→ x + (0,1)` (earlier).
* C3 (`x` odd, NW step): `x → x + (0,1)` (even, nonfree white) `→ x + (−1,1)` (earlier).
The grade facts are read at the translate `x + V` (positive ordinate, same `s`-grade); nonfreeness and laplacians are carried back by the
span. The middles are white by `RouteStay.route_lap_even` / `route_lap_odd`, whose band hypotheses are the word's strips. -/

namespace FLatticePaper.RowVEasy

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.RefuteTree FLatticePaper.RouteStay

/-- A nonfree white site keeps any of its incoming edges (the permitted pair of `permitsQ1` for a nonfree white). -/
theorem permits_nonfree_white {frame : ChildFrame} {F : Field} {η : ℤ} {m i : Site} (hw : laplacian F m = 0)
    (hnf : Nonfree frame m) (hi : Edge i m) : AuxRankQ1.permitsQ1 frame F η m i := by
  have hncl : ¬ FreeClosure.freeClosure frame m := by
    rintro ⟨s, hs, h⟩
    refine hnf s hs ?_
    rcases h with h | h
    · exact Set.mem_union_left _ h
    · exact Set.mem_union_right _ h
  exact Or.inr ⟨hw, Or.inr ⟨hncl, hi⟩⟩

/-- Nonfreeness descends along a span translate. -/
theorem nonfree_of_add_Vdeck (frame : ChildFrame) {z : Site} (h : Nonfree frame (z + Vdeck frame)) : Nonfree frame z := by
  have hv := span_neg_mem (Vdeck_mem_span frame)
  have h2 := PassageRank.nonfree_add_span frame h hv
  have e : z + Vdeck frame + -Vdeck frame = z := by abel
  rwa [e] at h2

/-- The s-grade is unchanged by the transverse translate. -/
theorem sGrade_add_Vdeck (frame : ChildFrame) (z : Site) : frame.sGrade (z + Vdeck frame) = frame.sGrade z := by
  unfold ChildFrame.sGrade Vdeck
  simp only [Prod.fst_add, Prod.snd_add]
  ring

/-- The s-grade of a unit step. -/
theorem sGrade_add_pair (frame : ChildFrame) (z : Site) (a b : ℤ) :
    frame.sGrade (z + (a, b)) = frame.sGrade z + (frame.child.den + frame.child.num) * a + (frame.child.den - frame.child.num) * b := by
  unfold ChildFrame.sGrade
  simp only [Prod.fst_add, Prod.snd_add]
  ring

/-- The laplacian is invariant under the transverse translate. -/
theorem lap_add_Vdeck {F : Field} (frame : ChildFrame) (hP : frame.Packet F) (z : Site) :
    laplacian F (z + Vdeck frame) = laplacian F z :=
  laplacian_span_inv frame F hP (Vdeck_mem_span frame) z

/-- The incoming positive neighbour of an even site. -/
theorem incPos_even_eq' {c : Site} (hc : EvenSite c) : incomingPos c = (c.1 + 1, c.2) := by
  unfold incomingPos
  rw [if_pos hc]

/-- **C4 middles.** For an even free V site `x` whose translate `x + V` lies in the window of `RouteStay.wne_nonfree`, the two middles
`x + (−1,0)` and `x + (−1,1)` are nonfree, and both are white. -/
theorem c4_middles {frame : ChildFrame} {F : Field} (hP : frame.Packet F)
    (hS : ∀ z : Site, 2 - 2 * frame.child.den ≤ frame.sGrade z →
      frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 2 → F z = harmonicGrid z)
    (hO : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 3 * frame.child.den + frame.child.num - 2 → F z = harmonicGrid z)
    (hd2 : 2 * frame.child.num ≤ frame.child.den) {x : Site} (hV : x + Vdeck frame ∈ frame.freeV) (he : EvenSite x)
    (h1 : 1 ≤ (x + Vdeck frame).2) (h2 : (x + Vdeck frame).2 ≤ frame.child.den + frame.child.num - 2) :
    Nonfree frame (x + (-1, 0)) ∧ Nonfree frame (x + (-1, 1)) ∧
      laplacian F (x + (-1, 0)) = 0 ∧ laplacian F (x + (-1, 1)) = 0 := by
  obtain ⟨hn0, hnd, -, -, -⟩ := frame.child_facts
  have hx'e : EvenSite (x + Vdeck frame) := by
    unfold EvenSite at he ⊢
    unfold Vdeck
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  obtain ⟨hs1, hs2⟩ := even_grade_strict frame hV hx'e h1 h2
  obtain ⟨hw1, hw2⟩ := wne_nonfree frame hV hx'e h1 h2
  have e1 : x + (-1, 0) + Vdeck frame = x + Vdeck frame + (-1, 0) := by abel
  have e2 : x + (-1, 1) + Vdeck frame = x + Vdeck frame + (-1, 1) := by abel
  have hc1 : ¬ EvenSite (x + Vdeck frame + (-1, 0)) := by
    unfold EvenSite at hx'e ⊢
    simp only [Prod.fst_add, Prod.snd_add] at hx'e ⊢
    omega
  have hc2 : EvenSite (x + Vdeck frame + (-1, 1)) := by
    unfold EvenSite at hx'e ⊢
    simp only [Prod.fst_add, Prod.snd_add] at hx'e ⊢
    omega
  refine ⟨nonfree_of_add_Vdeck frame (by rw [e1]; exact hw1), nonfree_of_add_Vdeck frame (by rw [e2]; exact hw2), ?_, ?_⟩
  · rw [← lap_add_Vdeck frame hP (x + (-1, 0)), e1]
    refine route_lap_odd frame hS hO hc1 ?_ ?_ ?_ ?_ ?_ ?_ <;> (rw [sGrade_add_pair]; omega)
  · rw [← lap_add_Vdeck frame hP (x + (-1, 1)), e2]
    refine route_lap_even frame hS hO hc2 ?_ ?_ ?_ ?_ ?_ ?_ <;> (rw [sGrade_add_pair]; omega)

/-- **Class C4 certificate.** An even free V entry `x` (translate in the window), whose north neighbour is an earlier entry, is refuted
through `x + (−1,0)` and `x + (−1,1)`. -/
theorem refuted_C4 {frame : ChildFrame} {F : Field} (hP : frame.Packet F)
    (hS : ∀ z : Site, 2 - 2 * frame.child.den ≤ frame.sGrade z →
      frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 2 → F z = harmonicGrid z)
    (hO : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 3 * frame.child.den + frame.child.num - 2 → F z = harmonicGrid z)
    (hd2 : 2 * frame.child.num ≤ frame.child.den) {E C : Site → Prop} {x : Site}
    (hx : x ∈ frame.freeV) (hV : x + Vdeck frame ∈ frame.freeV) (he : EvenSite x)
    (h1 : 1 ≤ (x + Vdeck frame).2) (h2 : (x + Vdeck frame).2 ≤ frame.child.den + frame.child.num - 2)
    (hne1 : x ≠ FLatticePaper.Induction.vFirst) (hne2 : x ≠ frame.vLast) (hE : E (x + (0, 1))) :
    Refuted frame F (-1) E C x := by
  obtain ⟨hw1, hw2, hl1, hl2⟩ := c4_middles hP hS hO hd2 hV he h1 h2
  have hlx : laplacian F x = 0 := frame.laplacian_eq_zero_of_freeV hP.strips hx
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
  have perm : AuxRankQ1.permitsQ1 frame F (-1) x (x + (-1, 0)) := by
    have hp := route_permit_even frame (F := F) hx hlx hne1 hne2 he
    rwa [incNeg_even_eq he] at hp
  exact Refuted.white hlx perm hz1

/-- **C3 middles.** For an odd free V entry `x` whose NW neighbour `x + (−1,1)` is free, the north middle `x + (0,1)` is nonfree and white. -/
theorem c3_middles {frame : ChildFrame} {F : Field} (_hP : frame.Packet F)
    (hS : ∀ z : Site, 2 - 2 * frame.child.den ≤ frame.sGrade z →
      frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 2 → F z = harmonicGrid z)
    (hO : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 3 * frame.child.den + frame.child.num - 2 → F z = harmonicGrid z)
    {x : Site} (hx : x ∈ frame.freeV) (hodd : ¬ EvenSite x) (hdiag : (x.1 - 1, x.2 + 1) ∈ frame.freeV) :
    Nonfree frame (x + (0, 1)) ∧ laplacian F (x + (0, 1)) = 0 := by
  obtain ⟨hn0, hlt, hnd2, -, hT⟩ := frame.child_facts
  have hnd : frame.child.num + 2 ≤ frame.child.den := by omega
  obtain ⟨hnO, hdO⟩ := frame.child_odd
  obtain ⟨hTle, hsle, -, hslo⟩ := V2Arrows.freeV_odd_facts frame hx hodd hdiag
  have htlo0 := (VStrict.odd_free_V_facts hx hodd).1
  have hodd' : (x.1 + x.2) % 2 = 1 := by
    unfold EvenSite at hodd
    omega
  have hcop : IsCoprime frame.child.num frame.child.den := frame.child_reduced
  have htlow := VGradeBounds.t_ge_n_add_two_d_sub_T (n := frame.child.num) (d := frame.child.den)
    (z1 := x.1) (z2 := x.2) (t := frame.tGrade x) (s := frame.sGrade x) (by omega) hnd hnO hdO hcop hodd'
    rfl rfl (by linarith [htlo0, hT]) hTle (by omega) hsle
  have ht2 : frame.tGrade x < frame.child.den := by
    have h := VGradeBounds.t_le_one_sub_n (n := frame.child.num) (d := frame.child.den)
      (z1 := x.1) (z2 := x.2) (t := frame.tGrade x) (s := frame.sGrade x) (by omega) hnd hodd'
      rfl rfl hTle (by omega) hsle
    omega
  have ht1 : frame.child.num + frame.child.den - 1 - frame.child.periodDenominator + frame.child.den
      < frame.tGrade x := by
    linarith [htlow, hT]
  have hnf : Nonfree frame (x + (0, 1)) :=
    ShortPassages.V_NW_middle_nonfree frame x hodd (by omega) hsle ht1 ht2
  have hc : EvenSite (x + (0, 1)) := by
    unfold EvenSite at hodd ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  refine ⟨hnf, ?_⟩
  refine route_lap_even frame hS hO hc ?_ ?_ ?_ ?_ ?_ ?_ <;> (rw [sGrade_add_pair]; omega)

/-- **Class C3 certificate.** An odd free V entry `x` whose NW neighbour is an earlier entry (`x + (−1,1)`) is refuted through its north
middle `x + (0,1)`. -/
theorem refuted_C3 {frame : ChildFrame} {F : Field} (hP : frame.Packet F)
    (hS : ∀ z : Site, 2 - 2 * frame.child.den ≤ frame.sGrade z →
      frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 2 → F z = harmonicGrid z)
    (hO : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 3 * frame.child.den + frame.child.num - 2 → F z = harmonicGrid z)
    {E C : Site → Prop} {x : Site} (hx : x ∈ frame.freeV) (hodd : ¬ EvenSite x)
    (hdiag : (x.1 - 1, x.2 + 1) ∈ frame.freeV) (hE : E (x + (-1, 1)))
    (hne1 : x ≠ FLatticePaper.Induction.vFirst) (hne2 : x ≠ frame.vLast) :
    Refuted frame F (-1) E C x := by
  obtain ⟨hnf, hw⟩ := c3_middles hP hS hO hx hodd hdiag
  have hlx : laplacian F x = 0 := frame.laplacian_eq_zero_of_freeV hP.strips hx
  have hev : EvenSite (x + (0, 1)) := by
    unfold EvenSite at hodd ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  have hi : incomingNeg (x + (0, 1)) = x + (-1, 1) := by
    rw [incNeg_even_eq hev]
    ext <;> simp
  have hedge : Edge (x + (-1, 1)) (x + (0, 1)) := by
    unfold Edge
    exact Or.inl hi.symm
  have hm : Refuted frame F (-1) E C (x + (0, 1)) :=
    Refuted.white hw (permits_nonfree_white hw hnf hedge) (Refuted.earlier hE)
  have perm : AuxRankQ1.permitsQ1 frame F (-1) x (x + (0, 1)) := by
    have hp := route_permit_odd frame (F := F) hx hlx hne1 hne2 hodd
    rwa [incPos_odd_eq hodd] at hp
  exact Refuted.white hlx perm hm

end FLatticePaper.RowVEasy

