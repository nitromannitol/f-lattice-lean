import FLatticePaper.Plane.Induction.RouteStay
import FLatticePaper.Plane.Induction.RouteReflect

/-! # The plus route stays in the fort (easy frames), by the reflection `z ↦ vLast − z`

The plus entries are the translates `vpath k − V` of the free V cut; `V` has grade `s = 0`. The reflection maps the chain to
itself reversed, `vLast − vpath k = vpath (L−1−k)`, and preserves `Nonfree` (`RouteReflect`). -/

namespace FLatticePaper.RoutePlus

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.RouteStay FLatticePaper.RouteReflect

/-- The transverse translation `V = (n − d, n + d)`. -/
def Vt (frame : ChildFrame) : Site := (frame.child.num - frame.child.den, frame.child.num + frame.child.den)

theorem sG_Vt (frame : ChildFrame) : frame.sGrade (Vt frame) = 0 := by
  unfold ChildFrame.sGrade Vt
  ring

theorem sG_sub_Vt (frame : ChildFrame) (z : Site) : frame.sGrade (z - Vt frame) = frame.sGrade z := by
  unfold ChildFrame.sGrade Vt
  simp only [Prod.fst_sub, Prod.snd_sub]
  ring

theorem even_sub_Vt (frame : ChildFrame) (z : Site) : EvenSite (z - Vt frame) ↔ EvenSite z := by
  unfold EvenSite Vt
  simp only [Prod.fst_sub, Prod.snd_sub]
  omega

theorem Vt_mem_span (frame : ChildFrame) : Vt frame ∈ frame.child.modifiedDeck.span := by
  refine ⟨0, 1, ?_⟩
  have hV := transverse_eq frame
  unfold Vt PeriodDeck.combine
  rw [hV]
  ext <;> simp

theorem span_add_Vt (frame : ChildFrame) {v : Site} (hv : v ∈ frame.child.modifiedDeck.span) :
    v + Vt frame ∈ frame.child.modifiedDeck.span := by
  obtain ⟨i, j, rfl⟩ := hv
  refine ⟨i, j + 1, ?_⟩
  have hV := transverse_eq frame
  unfold Vt PeriodDeck.combine at *
  rw [hV]
  ext <;> simp <;> ring

theorem span_sub_Vt (frame : ChildFrame) {v : Site} (hv : v ∈ frame.child.modifiedDeck.span) :
    v - Vt frame ∈ frame.child.modifiedDeck.span := by
  obtain ⟨i, j, rfl⟩ := hv
  refine ⟨i, j - 1, ?_⟩
  have hV := transverse_eq frame
  unfold Vt PeriodDeck.combine at *
  rw [hV]
  ext <;> simp <;> ring

/-- `Nonfree` is invariant under the translation `V`. -/
theorem nonfree_add_Vt (frame : ChildFrame) (w : Site) :
    Induction.Nonfree frame (w + Vt frame) ↔ Induction.Nonfree frame w := by
  constructor
  · intro h v hv hm
    apply h (v - Vt frame) (span_sub_Vt frame hv)
    have e : w + Vt frame + (v - Vt frame) = w + v := by abel
    rw [e]
    exact hm
  · intro h v hv hm
    apply h (v + Vt frame) (span_add_Vt frame hv)
    have e : w + (v + Vt frame) = w + Vt frame + v := by abel
    rw [e]
    exact hm

/-- The reflection of the chain: `vLast − vpath k = vpath i` for `i = L − 1 − k`. -/
theorem vLast_sub_vpath (frame : ChildFrame) (k : ℕ) (hk : (k : ℤ) < frame.child.den + frame.child.num)
    (i : ℕ) (hi : (i : ℤ) = frame.child.num + frame.child.den - 1 - k) :
    frame.vLast - VChain.vpath frame k = VChain.vpath frame i := by
  have hz := ListPrefix.vpath_freeV_all frame k hk
  have hr := FLatticePaper.RouteReflect.freeV_vLast_sub frame hz
  apply VChain.freeV_eq_vpath frame i _ hr
  have hv : frame.vLast.2 = frame.child.num + frame.child.den - 1 := rfl
  show frame.vLast.2 - (VChain.vpath frame k).2 = (i : ℤ)
  rw [VChain.vpath_ord frame k, hv]
  omega

theorem prescribedV_odd_plus (frame : ChildFrame) {x : Site} (hx1 : x ≠ vFirst) (hx2 : x ≠ frame.vLast)
    (ho : ¬ EvenSite x) : frame.prescribedV 1 x = (0, -1) := by
  simp [ChildFrame.prescribedV, hx1, hx2, ho]

theorem prescribedV_even_plus (frame : ChildFrame) {x : Site} (hx1 : x ≠ vFirst) (hx2 : x ≠ frame.vLast)
    (he : EvenSite x) : frame.prescribedV 1 x = (1, 0) := by
  simp [ChildFrame.prescribedV, hx1, hx2, he]

theorem even_vLast_sub (frame : ChildFrame) (z : Site) : EvenSite (frame.vLast - z) ↔ EvenSite z := by
  unfold EvenSite ChildFrame.vLast
  simp only [Prod.fst_sub, Prod.snd_sub]
  omega

/-- **The plus permit at an odd site**: the south input of `z − Vt` is permitted (η = +1, translate `Vt`). -/
theorem plus_permit_odd {F : Field} (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV)
    (hw : laplacian F (z - Vt frame) = 0) (h1 : z ≠ vFirst) (h2 : z ≠ frame.vLast) (ho : ¬ EvenSite z) :
    AuxRankQ1.permitsQ1 frame F 1 (z - Vt frame) (incomingNeg (z - Vt frame)) := by
  have hoX : ¬ EvenSite (z - Vt frame) := fun h => ho ((even_sub_Vt frame z).mp h)
  have hpv : (z - Vt frame) + frame.prescribedV 1 ((z - Vt frame) + Vt frame) = incomingNeg (z - Vt frame) := by
    rw [sub_add_cancel, prescribedV_odd_plus frame h1 h2 ho, FLatticePaper.CapRecursion.incomingNeg_of_odd' _ hoX]
    ext <;> (simp; try ring)
  have hfc : FreeClosure.freeClosure frame (z - Vt frame) :=
    ⟨Vt frame, Vt_mem_span frame, Or.inr (by rw [sub_add_cancel]; exact hz)⟩
  have hfp : FreePolicy.FreePresc frame 1 (z - Vt frame) (incomingNeg (z - Vt frame)) :=
    ⟨Vt frame, Vt_mem_span frame, Or.inr ⟨by rw [sub_add_cancel]; exact hz, hpv.symm⟩⟩
  exact Or.inr ⟨hw, Or.inl ⟨hfc, hfp⟩⟩

/-- **The plus permit at an even site**: the east input of `z − Vt` is permitted. -/
theorem plus_permit_even {F : Field} (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV)
    (hw : laplacian F (z - Vt frame) = 0) (h1 : z ≠ vFirst) (h2 : z ≠ frame.vLast) (he : EvenSite z) :
    AuxRankQ1.permitsQ1 frame F 1 (z - Vt frame) (incomingPos (z - Vt frame)) := by
  have heX : EvenSite (z - Vt frame) := (even_sub_Vt frame z).mpr he
  have hpv : (z - Vt frame) + frame.prescribedV 1 ((z - Vt frame) + Vt frame) = incomingPos (z - Vt frame) := by
    rw [sub_add_cancel, prescribedV_even_plus frame h1 h2 he, FLatticePaper.CapRecursion.incomingPos_of_even' _ heX]
    ext <;> simp
  have hfc : FreeClosure.freeClosure frame (z - Vt frame) :=
    ⟨Vt frame, Vt_mem_span frame, Or.inr (by rw [sub_add_cancel]; exact hz)⟩
  have hfp : FreePolicy.FreePresc frame 1 (z - Vt frame) (incomingPos (z - Vt frame)) :=
    ⟨Vt frame, Vt_mem_span frame, Or.inr ⟨by rw [sub_add_cancel]; exact hz, hpv.symm⟩⟩
  exact Or.inr ⟨hw, Or.inl ⟨hfc, hfp⟩⟩

/-- A site whose reflection is a translate `w + Vt` is nonfree exactly when `w` is. -/
theorem nonfree_via_reflect (frame : ChildFrame) {m w : Site} (h : frame.vLast - m = w + Vt frame) :
    Induction.Nonfree frame m ↔ Induction.Nonfree frame w := by
  rw [← nonfree_vLast_iff frame m, h, nonfree_add_Vt]

/-- A nonfree white site of `S` keeps both inputs (η = +1). -/
theorem plus_inputs_of_nonfree {F : Field} {frame : ChildFrame} {S : Set Site}
    (hR : IsRestrictedFort F (AuxRankQ1.permitsQ1 frame F 1) S) {m : Site} (hmS : m ∈ S)
    (hw : laplacian F m = 0) (hnf : Induction.Nonfree frame m) :
    incomingNeg m ∈ S ∧ incomingPos m ∈ S := by
  have hncl : ¬ FreeClosure.freeClosure frame m := by
    rintro ⟨s, hs, h⟩
    refine hnf s hs ?_
    rcases h with h | h
    · exact Set.mem_union_left _ h
    · exact Set.mem_union_right _ h
  constructor
  · refine route_mem_of_white hR hmS hw (Or.inl rfl) ?_
    exact Or.inr ⟨hw, Or.inr ⟨hncl, by unfold Edge; exact Or.inl rfl⟩⟩
  · refine route_mem_of_white hR hmS hw (Or.inr rfl) ?_
    exact Or.inr ⟨hw, Or.inr ⟨hncl, by unfold Edge; exact Or.inr rfl⟩⟩

/-- **Plus odd step.** The odd chain site `x₀ = vpath (j+1)` with `x₀ − Vt ∈ S` puts `vpath j − Vt` in `S`. -/
theorem plus_odd_step {F : Field} (frame : ChildFrame) {S : Set Site}
    (hS : ∀ z : Site, 2 - 2 * frame.child.den ≤ frame.sGrade z →
      frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 2 → F z = harmonicGrid z)
    (hO : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 3 * frame.child.den + frame.child.num - 2 → F z = harmonicGrid z)
    (hd : 2 * frame.child.num ≤ frame.child.den)
    (hR : IsRestrictedFort F (AuxRankQ1.permitsQ1 frame F 1) S)
    (j : ℕ) (hj : (j : ℤ) + 3 ≤ frame.child.den + frame.child.num)
    (hin : VChain.vpath frame (j + 1) - Vt frame ∈ S)
    (ho : ¬ EvenSite (VChain.vpath frame (j + 1))) :
    VChain.vpath frame j - Vt frame ∈ S := by
  obtain ⟨hn0, hnd, hd2, hd3, -⟩ := frame.child_facts
  have hjL : ((j + 1 : ℕ) : ℤ) < frame.child.den + frame.child.num := by
    push_cast
    omega
  have hx0F : VChain.vpath frame (j + 1) ∈ frame.freeV := ListPrefix.vpath_freeV_all frame (j + 1) hjL
  have hx0o : (VChain.vpath frame (j + 1)).2 = (j : ℤ) + 1 := by
    rw [VChain.vpath_ord]
    omega
  have hx1 : VChain.vpath frame (j + 1) ≠ vFirst := ne_vFirst_of (by rw [hx0o]; omega)
  have hx2 : VChain.vpath frame (j + 1) ≠ frame.vLast := ne_vLast_of frame (by rw [hx0o]; omega)
  obtain ⟨hs1, hs2⟩ := FreeVWindow.freeV_odd_window frame hx0F ho
  have hxo : ¬ EvenSite (VChain.vpath frame (j + 1) - Vt frame) := fun h => ho ((even_sub_Vt frame _).mp h)
  have hw : laplacian F (VChain.vpath frame (j + 1) - Vt frame) = 0 :=
    route_lap_odd frame hS hO hxo (by rw [sG_sub_Vt]; omega) (by rw [sG_sub_Vt]; omega)
      (by rw [sG_sub_Vt]; omega) (by rw [sG_sub_Vt]; omega) (by rw [sG_sub_Vt]; omega)
      (by rw [sG_sub_Vt]; omega)
  have hmS : incomingNeg (VChain.vpath frame (j + 1) - Vt frame) ∈ S :=
    route_mem_of_white hR hin hw (Or.inl rfl) (plus_permit_odd frame hx0F hw hx1 hx2 ho)
  by_cases hN : ((VChain.vpath frame j).1, (VChain.vpath frame j).2 + 1) ∈ frame.freeV
  · have hx0eq : VChain.vpath frame (j + 1) = ((VChain.vpath frame j).1, (VChain.vpath frame j).2 + 1) := by
      rw [VChain.vpath_succ frame j, VChain.vsucc, if_pos hN]
    have e : incomingNeg (VChain.vpath frame (j + 1) - Vt frame) = VChain.vpath frame j - Vt frame := by
      rw [FLatticePaper.CapRecursion.incomingNeg_of_odd' _ hxo, hx0eq]
      ext <;> (simp; try ring)
    rw [e] at hmS
    exact hmS
  · have hx0eq : VChain.vpath frame (j + 1) = ((VChain.vpath frame j).1 - 1, (VChain.vpath frame j).2 + 1) := by
      rw [VChain.vpath_succ frame j, VChain.vsucc, if_neg hN]
    obtain ⟨i, hi⟩ : ∃ i : ℕ, (i : ℤ) = frame.child.num + frame.child.den - 1 - ((j + 1 : ℕ) : ℤ) :=
      ⟨(frame.child.num + frame.child.den - 1 - ((j + 1 : ℕ) : ℤ)).toNat, by omega⟩
    have hvi : frame.vLast - VChain.vpath frame (j + 1) = VChain.vpath frame i :=
      vLast_sub_vpath frame (j + 1) hjL i hi
    have hi_lt : (i : ℤ) < frame.child.den + frame.child.num := by
      push_cast at hi
      omega
    have hiF : VChain.vpath frame i ∈ frame.freeV := ListPrefix.vpath_freeV_all frame i hi_lt
    have hiO : ¬ EvenSite (VChain.vpath frame i) := by
      rw [← hvi]
      intro h
      exact ho ((even_vLast_sub frame _).mp h)
    have hstep : VChain.vpath frame i + (0, 1) ∉ frame.freeV := by
      intro hN2
      have hN2' : ((VChain.vpath frame i).1, (VChain.vpath frame i).2 + 1) ∈ frame.freeV := by
        convert hN2 using 1
        ext <;> simp
      have hi1 : frame.vLast - VChain.vpath frame j = VChain.vpath frame (i + 1) :=
        vLast_sub_vpath frame j (by omega) (i + 1) (by push_cast at hi ⊢; omega)
      have hs := VChain.vpath_succ frame i
      rw [VChain.vsucc, if_pos hN2'] at hs
      have key : (VChain.vpath frame (i + 1)).1 = (VChain.vpath frame i).1 - 1 := by
        rw [← hi1, ← hvi, hx0eq]
        simp [ChildFrame.vLast]
        ring
      have h3 := congrArg Prod.fst hs
      simp only at h3
      rw [h3] at key
      omega
    have hnf : Induction.Nonfree frame (VChain.vpath frame i + (0, 1)) :=
      RouteSteps.V_NW_of_step frame hiF hiO hstep
    have hmE : EvenSite (incomingNeg (VChain.vpath frame (j + 1) - Vt frame)) := even_incNeg_of_odd hxo
    have href : frame.vLast - incomingNeg (VChain.vpath frame (j + 1) - Vt frame)
        = (VChain.vpath frame i + (0, 1)) + Vt frame := by
      rw [FLatticePaper.CapRecursion.incomingNeg_of_odd' _ hxo, ← hvi]
      ext <;> simp [ChildFrame.vLast, Vt] <;> ring
    have hnf_m : Induction.Nonfree frame (incomingNeg (VChain.vpath frame (j + 1) - Vt frame)) :=
      (nonfree_via_reflect frame href).mpr hnf
    have hwm : laplacian F (incomingNeg (VChain.vpath frame (j + 1) - Vt frame)) = 0 :=
      route_lap_even frame hS hO hmE
        (by rw [sG_incNeg_odd frame hxo, sG_sub_Vt]; omega)
        (by rw [sG_incNeg_odd frame hxo, sG_sub_Vt]; omega)
        (by rw [sG_incNeg_odd frame hxo, sG_sub_Vt]; omega)
        (by rw [sG_incNeg_odd frame hxo, sG_sub_Vt]; omega)
        (by rw [sG_incNeg_odd frame hxo, sG_sub_Vt]; omega)
        (by rw [sG_incNeg_odd frame hxo, sG_sub_Vt]; omega)
    obtain ⟨-, hB⟩ := plus_inputs_of_nonfree hR hmS hwm hnf_m
    have e2 : incomingPos (incomingNeg (VChain.vpath frame (j + 1) - Vt frame)) = VChain.vpath frame j - Vt frame := by
      rw [FLatticePaper.CapRecursion.incomingPos_of_even' _ hmE, FLatticePaper.CapRecursion.incomingNeg_of_odd' _ hxo, hx0eq]
      ext <;> simp <;> ring
    rw [e2] at hB
    exact hB

/-- **Plus even step.** The even chain site `x₀ = vpath (j+1)` with `x₀ − Vt ∈ S` puts `vpath j − Vt` in `S`. -/
theorem plus_even_step {F : Field} (frame : ChildFrame) {S : Set Site}
    (hS : ∀ z : Site, 2 - 2 * frame.child.den ≤ frame.sGrade z →
      frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 2 → F z = harmonicGrid z)
    (hO : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 3 * frame.child.den + frame.child.num - 2 → F z = harmonicGrid z)
    (hd : 2 * frame.child.num ≤ frame.child.den)
    (hR : IsRestrictedFort F (AuxRankQ1.permitsQ1 frame F 1) S)
    (j : ℕ) (hj : (j : ℤ) + 3 ≤ frame.child.den + frame.child.num)
    (hin : VChain.vpath frame (j + 1) - Vt frame ∈ S)
    (he : EvenSite (VChain.vpath frame (j + 1))) :
    VChain.vpath frame j - Vt frame ∈ S := by
  obtain ⟨hn0, hnd, hd2, hd3, -⟩ := frame.child_facts
  have hjL : ((j + 1 : ℕ) : ℤ) < frame.child.den + frame.child.num := by
    push_cast
    omega
  have hx0F : VChain.vpath frame (j + 1) ∈ frame.freeV := ListPrefix.vpath_freeV_all frame (j + 1) hjL
  have hx0o : (VChain.vpath frame (j + 1)).2 = (j : ℤ) + 1 := by
    rw [VChain.vpath_ord]
    omega
  have hx1 : VChain.vpath frame (j + 1) ≠ vFirst := ne_vFirst_of (by rw [hx0o]; omega)
  have hx2 : VChain.vpath frame (j + 1) ≠ frame.vLast := ne_vLast_of frame (by rw [hx0o]; omega)
  obtain ⟨hs1, hs2⟩ := even_grade_strict frame hx0F he (by rw [hx0o]; omega) (by rw [hx0o]; omega)
  have heX : EvenSite (VChain.vpath frame (j + 1) - Vt frame) := (even_sub_Vt frame _).mpr he
  have hw : laplacian F (VChain.vpath frame (j + 1) - Vt frame) = 0 :=
    route_lap_even frame hS hO heX (by rw [sG_sub_Vt]; omega) (by rw [sG_sub_Vt]; omega)
      (by rw [sG_sub_Vt]; omega) (by rw [sG_sub_Vt]; omega) (by rw [sG_sub_Vt]; omega)
      (by rw [sG_sub_Vt]; omega)
  have hw1S : incomingPos (VChain.vpath frame (j + 1) - Vt frame) ∈ S :=
    route_mem_of_white hR hin hw (Or.inr rfl) (plus_permit_even frame hx0F hw hx1 hx2 he)
  have hw1o : ¬ EvenSite (incomingPos (VChain.vpath frame (j + 1) - Vt frame)) := not_even_incPos heX
  have hw1 : laplacian F (incomingPos (VChain.vpath frame (j + 1) - Vt frame)) = 0 :=
    route_lap_odd frame hS hO hw1o (by rw [sG_incPos_even frame heX, sG_sub_Vt]; omega)
      (by rw [sG_incPos_even frame heX, sG_sub_Vt]; omega)
      (by rw [sG_incPos_even frame heX, sG_sub_Vt]; omega)
      (by rw [sG_incPos_even frame heX, sG_sub_Vt]; omega)
      (by rw [sG_incPos_even frame heX, sG_sub_Vt]; omega)
      (by rw [sG_incPos_even frame heX, sG_sub_Vt]; omega)
  obtain ⟨i, hi⟩ : ∃ i : ℕ, (i : ℤ) = frame.child.num + frame.child.den - 1 - ((j + 1 : ℕ) : ℤ) :=
    ⟨(frame.child.num + frame.child.den - 1 - ((j + 1 : ℕ) : ℤ)).toNat, by omega⟩
  have hvi : frame.vLast - VChain.vpath frame (j + 1) = VChain.vpath frame i :=
    vLast_sub_vpath frame (j + 1) hjL i hi
  have hi_lt : (i : ℤ) < frame.child.den + frame.child.num := by
    push_cast at hi
    omega
  have hiF : VChain.vpath frame i ∈ frame.freeV := ListPrefix.vpath_freeV_all frame i hi_lt
  have hiE : EvenSite (VChain.vpath frame i) := by
    rw [← hvi]
    exact (even_vLast_sub frame _).mpr he
  have hi1 : 1 ≤ (VChain.vpath frame i).2 := by
    rw [VChain.vpath_ord]
    push_cast at hi
    omega
  have hi2 : (VChain.vpath frame i).2 ≤ frame.child.den + frame.child.num - 2 := by
    rw [VChain.vpath_ord]
    push_cast at hi
    omega
  obtain ⟨hnfA, hnfB⟩ := wne_nonfree frame hiF hiE hi1 hi2
  have href1 : frame.vLast - incomingPos (VChain.vpath frame (j + 1) - Vt frame)
      = (VChain.vpath frame i + (-1, 0)) + Vt frame := by
    rw [FLatticePaper.CapRecursion.incomingPos_of_even' _ heX, ← hvi]
    ext <;> simp [ChildFrame.vLast, Vt] <;> ring
  have hnf1 : Induction.Nonfree frame (incomingPos (VChain.vpath frame (j + 1) - Vt frame)) :=
    (nonfree_via_reflect frame href1).mpr hnfA
  obtain ⟨hw2S, -⟩ := plus_inputs_of_nonfree hR hw1S hw1 hnf1
  have hw2e : EvenSite (incomingNeg (incomingPos (VChain.vpath frame (j + 1) - Vt frame))) :=
    even_incNeg_of_odd hw1o
  have hw2 : laplacian F (incomingNeg (incomingPos (VChain.vpath frame (j + 1) - Vt frame))) = 0 :=
    route_lap_even frame hS hO hw2e
      (by rw [sG_incNeg_odd frame hw1o, sG_incPos_even frame heX, sG_sub_Vt]; omega)
      (by rw [sG_incNeg_odd frame hw1o, sG_incPos_even frame heX, sG_sub_Vt]; omega)
      (by rw [sG_incNeg_odd frame hw1o, sG_incPos_even frame heX, sG_sub_Vt]; omega)
      (by rw [sG_incNeg_odd frame hw1o, sG_incPos_even frame heX, sG_sub_Vt]; omega)
      (by rw [sG_incNeg_odd frame hw1o, sG_incPos_even frame heX, sG_sub_Vt]; omega)
      (by rw [sG_incNeg_odd frame hw1o, sG_incPos_even frame heX, sG_sub_Vt]; omega)
  have href2 : frame.vLast - incomingNeg (incomingPos (VChain.vpath frame (j + 1) - Vt frame))
      = (VChain.vpath frame i + (-1, 1)) + Vt frame := by
    rw [FLatticePaper.CapRecursion.incomingNeg_of_odd' _ hw1o, FLatticePaper.CapRecursion.incomingPos_of_even' _ heX,
      ← hvi]
    ext <;> simp [ChildFrame.vLast, Vt] <;> ring
  have hnf2 : Induction.Nonfree frame (incomingNeg (incomingPos (VChain.vpath frame (j + 1) - Vt frame))) :=
    (nonfree_via_reflect frame href2).mpr hnfB
  obtain ⟨hA, -⟩ := plus_inputs_of_nonfree hR hw2S hw2 hnf2
  by_cases hN : ((VChain.vpath frame j).1, (VChain.vpath frame j).2 + 1) ∈ frame.freeV
  · have hx0eq : VChain.vpath frame (j + 1) = ((VChain.vpath frame j).1, (VChain.vpath frame j).2 + 1) := by
      rw [VChain.vpath_succ frame j, VChain.vsucc, if_pos hN]
    have e : incomingNeg (incomingNeg (incomingPos (VChain.vpath frame (j + 1) - Vt frame)))
        = VChain.vpath frame j - Vt frame := by
      rw [FLatticePaper.CapRecursion.incomingNeg_of_even' _ hw2e, FLatticePaper.CapRecursion.incomingNeg_of_odd' _ hw1o,
        FLatticePaper.CapRecursion.incomingPos_of_even' _ heX, hx0eq]
      ext <;> (simp; try ring)
    rw [e] at hA
    exact hA
  · have hx0eq : VChain.vpath frame (j + 1) = ((VChain.vpath frame j).1 - 1, (VChain.vpath frame j).2 + 1) := by
      rw [VChain.vpath_succ frame j, VChain.vsucc, if_neg hN]
    have e : incomingNeg (incomingPos (VChain.vpath frame (j + 1) - Vt frame)) = VChain.vpath frame j - Vt frame := by
      rw [FLatticePaper.CapRecursion.incomingNeg_of_odd' _ hw1o, FLatticePaper.CapRecursion.incomingPos_of_even' _ heX,
        hx0eq]
      ext <;> simp <;> ring
    rw [e] at hw2S
    exact hw2S

/-- A negative chain index: `vAt J = vpath (J + L) − Vt` for `−L ≤ J < 0`. -/
theorem vAt_neg_eq (frame : ChildFrame) (J : ℤ) (h1 : -(frame.child.den + frame.child.num) ≤ J) (h2 : J < 0) :
    RowAt.vAt frame J = VChain.vpath frame (J + (frame.child.den + frame.child.num)).toNat - Vt frame := by
  obtain ⟨hn0, hnd, -, -, -⟩ := frame.child_facts
  have hL : (0 : ℤ) < frame.child.den + frame.child.num := by omega
  have hu : J / (frame.child.den + frame.child.num) = -1 ∧ J % (frame.child.den + frame.child.num) = J + (frame.child.den + frame.child.num) :=
    (Int.ediv_emod_unique hL).mpr ⟨by ring, by omega, by omega⟩
  obtain ⟨q1, q2⟩ := hu
  unfold RowAt.vAt
  rw [q1, q2]
  unfold RowAt.Vvec Vt
  simp [sub_eq_add_neg]

/-- **One plus step.** -/
theorem plus_step {F : Field} (frame : ChildFrame) {S : Set Site}
    (hS : ∀ z : Site, 2 - 2 * frame.child.den ≤ frame.sGrade z →
      frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 2 → F z = harmonicGrid z)
    (hO : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 3 * frame.child.den + frame.child.num - 2 → F z = harmonicGrid z)
    (hd : 2 * frame.child.num ≤ frame.child.den)
    (hR : IsRestrictedFort F (AuxRankQ1.permitsQ1 frame F 1) S)
    (j : ℕ) (hj : (j : ℤ) + 3 ≤ frame.child.den + frame.child.num)
    (hin : VChain.vpath frame (j + 1) - Vt frame ∈ S) :
    VChain.vpath frame j - Vt frame ∈ S := by
  by_cases ho : EvenSite (VChain.vpath frame (j + 1))
  · exact plus_even_step frame hS hO hd hR j hj hin ho
  · exact plus_odd_step frame hS hO hd hR j hj hin ho

/-- **The plus route stays in the fort** (the `hroute` hypothesis of `ListForce.plus_hforce_route`, easy frames `2n ≤ d`). -/
theorem plus_route_stays {F : Field} (frame : ChildFrame) {S : Set Site}
    (hS : ∀ z : Site, 2 - 2 * frame.child.den ≤ frame.sGrade z →
      frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 2 → F z = harmonicGrid z)
    (hO : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 3 * frame.child.den + frame.child.num - 2 → F z = harmonicGrid z)
    (hd : 2 * frame.child.num ≤ frame.child.den)
    (hR : IsRestrictedFort F (AuxRankQ1.permitsQ1 frame F 1) S)
    (r : ℤ) (hrL2 : r ≤ frame.child.den + frame.child.num - 2) :
    ∀ k : ℕ, (k : ℤ) < r → RowAt.vAt frame (-r - 1 + (k : ℤ)) ∈ S →
      RowAt.vAt frame (-r - 2 + (k : ℤ)) ∈ S := by
  intro k hk hin
  obtain ⟨hn0, hnd, -, -, -⟩ := frame.child_facts
  obtain ⟨q, hq⟩ : ∃ q : ℕ, (q : ℤ) = -r - 1 + (k : ℤ) + (frame.child.den + frame.child.num) :=
    ⟨(-r - 1 + (k : ℤ) + (frame.child.den + frame.child.num)).toNat, by omega⟩
  have hqe : (-r - 1 + (k : ℤ) + (frame.child.den + frame.child.num)).toNat = q := by omega
  have h1 : RowAt.vAt frame (-r - 1 + (k : ℤ)) = VChain.vpath frame q - Vt frame := by
    rw [vAt_neg_eq frame _ (by omega) (by omega), hqe]
  have h2 : RowAt.vAt frame (-r - 2 + (k : ℤ)) = VChain.vpath frame (q - 1) - Vt frame := by
    rw [vAt_neg_eq frame _ (by omega) (by omega)]
    have : (-r - 2 + (k : ℤ) + (frame.child.den + frame.child.num)).toNat = q - 1 := by omega
    rw [this]
  rw [h1] at hin
  rw [h2]
  have hq1 : q - 1 + 1 = q := by omega
  have hin' : VChain.vpath frame (q - 1 + 1) - Vt frame ∈ S := by
    rw [hq1]
    exact hin
  exact plus_step frame hS hO hd hR (q - 1) (by omega) hin'

end FLatticePaper.RoutePlus


