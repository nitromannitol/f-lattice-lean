import FLatticePaper.Plane.Induction.WhiteRoute
import FLatticePaper.Plane.Induction.RouteSteps
import FLatticePaper.Plane.Induction.ShortPassages
import FLatticePaper.Plane.Induction.ArcRanges
import FLatticePaper.Plane.Induction.FreeVWindow
import FLatticePaper.Plane.Induction.RankFromForts
import FLatticePaper.Plane.Induction.AuxRankQ1
import FLatticePaper.Plane.Induction.FreePolicy
import FLatticePaper.Plane.Induction.VChain
import FLatticePaper.Plane.Induction.RowAt
import FLatticePaper.Plane.Induction.ListPrefix

/-! # The route from an entry of a restricted fort stays in the fort (easy frames, `2n ≤ d`)

Helpers: grades and parities of the inputs, and the prescribed inputs of free V sites. -/

namespace FLatticePaper.RouteStay

open Farey FLatticePaper FLatticePaper.Induction

theorem sG_incNeg_even (frame : ChildFrame) {c : Site} (hc : EvenSite c) :
    frame.sGrade (incomingNeg c) = frame.sGrade c - (frame.child.den + frame.child.num) := by
  rw [FLatticePaper.CapRecursion.incomingNeg_of_even' c hc]
  unfold ChildFrame.sGrade
  ring

theorem sG_incPos_even (frame : ChildFrame) {c : Site} (hc : EvenSite c) :
    frame.sGrade (incomingPos c) = frame.sGrade c + (frame.child.den + frame.child.num) := by
  rw [FLatticePaper.CapRecursion.incomingPos_of_even' c hc]
  unfold ChildFrame.sGrade
  ring

theorem sG_incNeg_odd (frame : ChildFrame) {c : Site} (hc : ¬ EvenSite c) :
    frame.sGrade (incomingNeg c) = frame.sGrade c - (frame.child.den - frame.child.num) := by
  rw [FLatticePaper.CapRecursion.incomingNeg_of_odd' c hc]
  unfold ChildFrame.sGrade
  ring

theorem sG_incPos_odd (frame : ChildFrame) {c : Site} (hc : ¬ EvenSite c) :
    frame.sGrade (incomingPos c) = frame.sGrade c + (frame.child.den - frame.child.num) := by
  rw [FLatticePaper.CapRecursion.incomingPos_of_odd' c hc]
  unfold ChildFrame.sGrade
  ring

theorem not_even_incNeg {c : Site} (hc : EvenSite c) : ¬ EvenSite (incomingNeg c) := by
  rw [FLatticePaper.CapRecursion.incomingNeg_of_even' c hc]
  unfold EvenSite at hc ⊢
  simp only at hc ⊢
  omega

theorem even_incNeg_of_odd {c : Site} (hc : ¬ EvenSite c) : EvenSite (incomingNeg c) := by
  rw [FLatticePaper.CapRecursion.incomingNeg_of_odd' c hc]
  unfold EvenSite at hc ⊢
  simp only at hc ⊢
  omega

theorem not_even_incPos {c : Site} (hc : EvenSite c) : ¬ EvenSite (incomingPos c) := by
  rw [FLatticePaper.CapRecursion.incomingPos_of_even' c hc]
  unfold EvenSite at hc ⊢
  simp only at hc ⊢
  omega

theorem even_incPos_of_odd {c : Site} (hc : ¬ EvenSite c) : EvenSite (incomingPos c) := by
  rw [FLatticePaper.CapRecursion.incomingPos_of_odd' c hc]
  unfold EvenSite at hc ⊢
  simp only at hc ⊢
  omega

theorem incNeg_even_eq {c : Site} (hc : EvenSite c) : incomingNeg c = c + (-1, 0) := by
  rw [FLatticePaper.CapRecursion.incomingNeg_of_even' c hc]
  ext <;> simp
  ring

theorem incPos_odd_eq {c : Site} (hc : ¬ EvenSite c) : incomingPos c = c + (0, 1) := by
  rw [FLatticePaper.CapRecursion.incomingPos_of_odd' c hc]
  ext <;> simp

theorem zero_mem_span (frame : ChildFrame) : (0 : Site) ∈ frame.child.modifiedDeck.span :=
  ⟨0, 0, by ext <;> simp [PeriodDeck.combine]⟩

theorem ne_vFirst_of {x : Site} (h : 1 ≤ x.2) : x ≠ vFirst := by
  intro e
  have h2 := congrArg Prod.snd e
  simp [vFirst] at h2
  omega

theorem ne_vLast_of (frame : ChildFrame) {x : Site} (h : x.2 ≤ frame.child.den + frame.child.num - 2) :
    x ≠ frame.vLast := by
  intro e
  have h2 := congrArg Prod.snd e
  have hv : frame.vLast.2 = frame.child.num + frame.child.den - 1 := rfl
  omega

theorem prescribedV_even (frame : ChildFrame) {x : Site} (hx1 : x ≠ vFirst) (hx2 : x ≠ frame.vLast)
    (he : EvenSite x) : frame.prescribedV (-1) x = (-1, 0) := by
  simp [ChildFrame.prescribedV, hx1, hx2, he]

theorem prescribedV_odd (frame : ChildFrame) {x : Site} (hx1 : x ≠ vFirst) (hx2 : x ≠ frame.vLast)
    (ho : ¬ EvenSite x) : frame.prescribedV (-1) x = (0, 1) := by
  simp [ChildFrame.prescribedV, hx1, hx2, ho]

/-- An even site with ordinate `1 … L − 2` has grade `s ≠ 0` and `s ≠ 2n`: with `L = 2a`, `d − n = 2b`, both cases force
`a ∣ z₂` (resp. `a ∣ z₂ + 1`), then `z₁ + z₂ = n m` with `n` odd, so `m` is even and the ordinate is a multiple of `L`. -/
theorem no_zero_or_top (frame : ChildFrame) {z : Site} (he : EvenSite z)
    (h1 : 1 ≤ z.2) (h2 : z.2 ≤ frame.child.den + frame.child.num - 2)
    (hs : frame.sGrade z = 0 ∨ frame.sGrade z = 2 * frame.child.num) : False := by
  obtain ⟨hn2, hd2⟩ := frame.child_odd
  obtain ⟨hn0, hnd, -, -, -⟩ := frame.child_facts
  have hcop : IsCoprime frame.child.num frame.child.den := frame.child_reduced
  obtain ⟨a, ha⟩ : ∃ a, frame.child.den + frame.child.num = 2 * a :=
    ⟨(frame.child.den + frame.child.num) / 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, frame.child.den - frame.child.num = 2 * b :=
    ⟨(frame.child.den - frame.child.num) / 2, by omega⟩
  have hna : frame.child.num = a - b := by omega
  have hda : frame.child.den = a + b := by omega
  have ha0 : 0 < a := by omega
  have hcab : IsCoprime a b := by
    obtain ⟨u, v, huv⟩ := hcop
    refine ⟨u + v, v - u, ?_⟩
    rw [hna, hda] at huv
    linear_combination huv
  have hsG : frame.sGrade z = 2 * (a * z.1 + b * z.2) := by
    unfold ChildFrame.sGrade
    linear_combination z.1 * ha + z.2 * hb
  have hpar : (z.1 + z.2) % 2 = 0 := he
  rcases hs with hs | hs
  · have e1 : a * z.1 + b * z.2 = 0 := by linarith
    have hdiv : a ∣ b * z.2 := ⟨-z.1, by linear_combination e1⟩
    obtain ⟨m, hm⟩ := hcab.dvd_of_dvd_mul_left hdiv
    have e2 : a * (z.1 + b * m) = 0 := by
      rw [hm] at e1
      linear_combination e1
    have e3 : z.1 + b * m = 0 := (mul_eq_zero.mp e2).resolve_left (ne_of_gt ha0)
    have hsum : z.1 + z.2 = frame.child.num * m := by
      rw [hna]
      linear_combination e3 + hm
    have hm2 : m % 2 = 0 := by
      have h' : (frame.child.num * m) % 2 = 0 := by
        rw [← hsum]
        exact hpar
      rcases Int.emod_two_eq_zero_or_one m with h | h
      · exact h
      · rw [Int.mul_emod, hn2, h] at h'
        norm_num at h'
    obtain ⟨p, hp⟩ : ∃ p, m = 2 * p := ⟨m / 2, by omega⟩
    have hk : z.2 = (frame.child.den + frame.child.num) * p := by
      rw [hm, hp, ha]
      ring
    have hL : 0 < frame.child.den + frame.child.num := by omega
    rcases (show p ≤ 0 ∨ 1 ≤ p by omega) with hp0 | hp1
    · nlinarith
    · nlinarith
  · have e1 : a * z.1 + b * z.2 = frame.child.num := by linarith
    have hdiv : a ∣ b * (z.2 + 1) := ⟨-(z.1 - 1), by linear_combination e1 + hna⟩
    obtain ⟨m, hm⟩ := hcab.dvd_of_dvd_mul_left hdiv
    have eG : a * z.1 + b * z.2 - a + b = 0 := by linarith
    have e2 : a * (z.1 - 1 + b * m) = 0 := by
      linear_combination eG - b * hm
    have e3 : z.1 - 1 + b * m = 0 := (mul_eq_zero.mp e2).resolve_left (ne_of_gt ha0)
    have hsum : z.1 + z.2 = frame.child.num * m := by
      rw [hna]
      linear_combination e3 + hm
    have hm2 : m % 2 = 0 := by
      have h' : (frame.child.num * m) % 2 = 0 := by
        rw [← hsum]
        exact hpar
      rcases Int.emod_two_eq_zero_or_one m with h | h
      · exact h
      · rw [Int.mul_emod, hn2, h] at h'
        norm_num at h'
    obtain ⟨p, hp⟩ : ∃ p, m = 2 * p := ⟨m / 2, by omega⟩
    have hk : z.2 + 1 = (frame.child.den + frame.child.num) * p := by
      rw [hm, hp, ha]
      ring
    have hL : 0 < frame.child.den + frame.child.num := by omega
    rcases (show p ≤ 0 ∨ 1 ≤ p by omega) with hp0 | hp1
    · nlinarith
    · nlinarith

/-- **Even grades on the V cut.** An even free V site with ordinate `1 … L − 2` has `2 ≤ s ≤ 2n − 2`. -/
theorem even_grade_strict (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV) (he : EvenSite z)
    (h1 : 1 ≤ z.2) (h2 : z.2 ≤ frame.child.den + frame.child.num - 2) :
    2 ≤ frame.sGrade z ∧ frame.sGrade z ≤ 2 * frame.child.num - 2 := by
  obtain ⟨hs0, hs1⟩ := FreeVWindow.freeV_even_window frame hz he
  have hmod := frame.sGrade_mod_two z
  have hne0 : frame.sGrade z ≠ 0 := fun h => no_zero_or_top frame he h1 h2 (Or.inl h)
  have hne1 : frame.sGrade z ≠ 2 * frame.child.num := fun h => no_zero_or_top frame he h1 h2 (Or.inr h)
  omega

/-- **The W-N-E middles of an even entry are nonfree** (ShortPassages, with the grades from `even_grade_strict` and the
`t`-window from `ArcRanges.arc_even_range`). -/
theorem wne_nonfree (frame : ChildFrame) {x : Site} (hx : x ∈ frame.freeV) (he : EvenSite x)
    (h1 : 1 ≤ x.2) (h2 : x.2 ≤ frame.child.den + frame.child.num - 2) :
    Induction.Nonfree frame (x + (-1, 0)) ∧ Induction.Nonfree frame (x + (-1, 1)) := by
  obtain ⟨hn0, hnd, -, -, -⟩ := frame.child_facts
  obtain ⟨hs1, hs2⟩ := even_grade_strict frame hx he h1 h2
  obtain ⟨ht1, ht2⟩ := ArcRanges.arc_even_range frame hx he (ne_vFirst_of h1) (ne_vLast_of frame h2)
  exact ⟨ShortPassages.V_WNE_middle0_nonfree frame x he hs1 hs2 (by omega) (by omega),
    ShortPassages.V_WNE_middle1_nonfree frame x he hs1 hs2 (by omega) (by omega)⟩

/-- Even stencil: a white even site from the harmonic strips (`WhiteRoute.lap_zero_even_centre`, inputs in the odd extension). -/
theorem route_lap_even {F : Field} (frame : ChildFrame)
    (hS : ∀ z : Site, 2 - 2 * frame.child.den ≤ frame.sGrade z →
      frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 2 → F z = harmonicGrid z)
    (hO : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 3 * frame.child.den + frame.child.num - 2 → F z = harmonicGrid z)
    {c : Site} (hc : EvenSite c)
    (h1 : 2 - 2 * frame.child.den ≤ frame.sGrade c)
    (h2 : frame.sGrade c ≤ 2 * (frame.child.den + frame.child.num) - 2)
    (h3 : 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade c - (frame.child.den + frame.child.num))
    (h4 : frame.sGrade c - (frame.child.den + frame.child.num) ≤ 3 * frame.child.den + frame.child.num - 2)
    (h5 : 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade c + (frame.child.den + frame.child.num))
    (h6 : frame.sGrade c + (frame.child.den + frame.child.num) ≤ 3 * frame.child.den + frame.child.num - 2) :
    laplacian F c = 0 := by
  refine WhiteRoute.lap_zero_even_centre frame hS hO hc h1 h2 ?_ ?_ ?_ ?_
  · rw [sG_incNeg_even frame hc]; exact h3
  · rw [sG_incNeg_even frame hc]; exact h4
  · rw [sG_incPos_even frame hc]; exact h5
  · rw [sG_incPos_even frame hc]; exact h6

/-- Odd stencil: a white odd site from the harmonic strips (`WhiteRoute.lap_zero_odd_centre`, inputs in the even strip). -/
theorem route_lap_odd {F : Field} (frame : ChildFrame)
    (hS : ∀ z : Site, 2 - 2 * frame.child.den ≤ frame.sGrade z →
      frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 2 → F z = harmonicGrid z)
    (hO : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 3 * frame.child.den + frame.child.num - 2 → F z = harmonicGrid z)
    {c : Site} (hc : ¬ EvenSite c)
    (h1 : 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade c)
    (h2 : frame.sGrade c ≤ 3 * frame.child.den + frame.child.num - 2)
    (h3 : 2 - 2 * frame.child.den ≤ frame.sGrade c - (frame.child.den - frame.child.num))
    (h4 : frame.sGrade c - (frame.child.den - frame.child.num) ≤ 2 * (frame.child.den + frame.child.num) - 2)
    (h5 : 2 - 2 * frame.child.den ≤ frame.sGrade c + (frame.child.den - frame.child.num))
    (h6 : frame.sGrade c + (frame.child.den - frame.child.num) ≤ 2 * (frame.child.den + frame.child.num) - 2) :
    laplacian F c = 0 := by
  refine WhiteRoute.lap_zero_odd_centre frame hS hO hc h1 h2 ?_ ?_ ?_ ?_
  · rw [sG_incNeg_odd frame hc]; exact h3
  · rw [sG_incNeg_odd frame hc]; exact h4
  · rw [sG_incPos_odd frame hc]; exact h5
  · rw [sG_incPos_odd frame hc]; exact h6

/-- **A restricted fort keeps a white site's permitted input.** A white site of `S` has each input in `S` or not permitted. -/
theorem route_mem_of_white {F : Field} {P : Site → Site → Prop} {S : Set Site}
    (hR : IsRestrictedFort F P S) {x i : Site} (hxS : x ∈ S) (hw : laplacian F x = 0)
    (hi : i = incomingNeg x ∨ i = incomingPos x) (hP : P x i) : i ∈ S := by
  rcases hR x hxS with ⟨h, -⟩ | ⟨-, h1, h2⟩
  · have h0 : (-1 : ℤ) = 0 := h.symm.trans hw
    norm_num at h0
  · rcases hi with rfl | rfl
    · rcases h1 with h1 | h1
      · exact h1
      · exact absurd hP h1
    · rcases h2 with h2 | h2
      · exact h2
      · exact absurd hP h2

/-- The permitted input of an even free white site is its west neighbour (the prescribed input at `η = −1`). -/
theorem route_permit_even {F : Field} (frame : ChildFrame) {x : Site} (hx : x ∈ frame.freeV)
    (hw : laplacian F x = 0) (h1 : x ≠ vFirst) (h2 : x ≠ frame.vLast) (he : EvenSite x) :
    AuxRankQ1.permitsQ1 frame F (-1) x (incomingNeg x) := by
  have hpv : x + frame.prescribedV (-1) x = incomingNeg x := by
    rw [prescribedV_even frame h1 h2 he, FLatticePaper.CapRecursion.incomingNeg_of_even' x he]
    ext <;> simp
    ring
  have hfc : FreeClosure.freeClosure frame x := ⟨0, zero_mem_span frame, Or.inr (by simpa using hx)⟩
  have hfp : FreePolicy.FreePresc frame (-1) x (incomingNeg x) :=
    ⟨0, zero_mem_span frame, Or.inr ⟨by simpa using hx, by simp only [add_zero]; exact hpv.symm⟩⟩
  exact Or.inr ⟨hw, Or.inl ⟨hfc, hfp⟩⟩

/-- The permitted input of an odd free white site is its north neighbour. -/
theorem route_permit_odd {F : Field} (frame : ChildFrame) {x : Site} (hx : x ∈ frame.freeV)
    (hw : laplacian F x = 0) (h1 : x ≠ vFirst) (h2 : x ≠ frame.vLast) (ho : ¬ EvenSite x) :
    AuxRankQ1.permitsQ1 frame F (-1) x (incomingPos x) := by
  have hpv : x + frame.prescribedV (-1) x = incomingPos x := by
    rw [prescribedV_odd frame h1 h2 ho, incPos_odd_eq ho]
  have hfc : FreeClosure.freeClosure frame x := ⟨0, zero_mem_span frame, Or.inr (by simpa using hx)⟩
  have hfp : FreePolicy.FreePresc frame (-1) x (incomingPos x) :=
    ⟨0, zero_mem_span frame, Or.inr ⟨by simpa using hx, by simp only [add_zero]; exact hpv.symm⟩⟩
  exact Or.inr ⟨hw, Or.inl ⟨hfc, hfp⟩⟩

/-- **A nonfree white site keeps both inputs.** If `m ∈ S` is white and nonfree, both `incomingNeg m` and
`incomingPos m` lie in `S`. -/
theorem route_inputs_of_nonfree {F : Field} {frame : ChildFrame} {S : Set Site}
    (hR : IsRestrictedFort F (AuxRankQ1.permitsQ1 frame F (-1)) S) {m : Site} (hmS : m ∈ S)
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

/-- **Odd route step.** An odd entry `x ∈ S` (free, `1 ≤ x₂ ≤ L − 2`) puts its north neighbour `x + N` in `S`; if `x + N` is not free,
the NW target `x + (−1,1)` is in `S` too (through the nonfree white middle `x + N`). -/
theorem route_odd_step {F : Field} (frame : ChildFrame)
    {S : Set Site}
    (hS : ∀ z : Site, 2 - 2 * frame.child.den ≤ frame.sGrade z →
      frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 2 → F z = harmonicGrid z)
    (hO : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 3 * frame.child.den + frame.child.num - 2 → F z = harmonicGrid z)
    (hd : 2 * frame.child.num ≤ frame.child.den)
    (hR : IsRestrictedFort F (AuxRankQ1.permitsQ1 frame F (-1)) S)
    {x : Site} (hx : x ∈ frame.freeV) (ho : ¬ EvenSite x) (h1 : 1 ≤ x.2)
    (h2 : x.2 ≤ frame.child.den + frame.child.num - 2) (hxS : x ∈ S) :
    (x.1, x.2 + 1) ∈ S ∧ ((x.1, x.2 + 1) ∉ frame.freeV → (x.1 - 1, x.2 + 1) ∈ S) := by
  obtain ⟨hn0, hnd, hd2, hd3, -⟩ := frame.child_facts
  obtain ⟨hs1, hs2⟩ := FreeVWindow.freeV_odd_window frame hx ho
  have hw : laplacian F x = 0 :=
    route_lap_odd frame hS hO ho (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hmS : incomingPos x ∈ S :=
    route_mem_of_white hR hxS hw (Or.inr rfl)
      (route_permit_odd frame hx hw (ne_vFirst_of h1) (ne_vLast_of frame h2) ho)
  have hmeq : incomingPos x = (x.1, x.2 + 1) := by
    rw [FLatticePaper.CapRecursion.incomingPos_of_odd' x ho]
  refine ⟨by rw [← hmeq]; exact hmS, fun hN => ?_⟩
  have hstep : x + (0, 1) ∉ frame.freeV := by
    have e : x + (0, 1) = (x.1, x.2 + 1) := by ext <;> simp
    rw [e]
    exact hN
  have hme : EvenSite (incomingPos x) := even_incPos_of_odd ho
  have hnf : Induction.Nonfree frame (incomingPos x) := by
    rw [incPos_odd_eq ho]
    exact RouteSteps.V_NW_of_step frame hx ho hstep
  have hwm : laplacian F (incomingPos x) = 0 :=
    route_lap_even frame hS hO hme (by rw [sG_incPos_odd frame ho]; omega)
      (by rw [sG_incPos_odd frame ho]; omega) (by rw [sG_incPos_odd frame ho]; omega)
      (by rw [sG_incPos_odd frame ho]; omega) (by rw [sG_incPos_odd frame ho]; omega)
      (by rw [sG_incPos_odd frame ho]; omega)
  obtain ⟨hA, -⟩ := route_inputs_of_nonfree hR hmS hwm hnf
  have hw2 : incomingNeg (incomingPos x) = (x.1 - 1, x.2 + 1) := by
    rw [FLatticePaper.CapRecursion.incomingNeg_of_even' _ hme,
      FLatticePaper.CapRecursion.incomingPos_of_odd' x ho]
  rw [hw2] at hA
  exact hA

/-- **Even route step.** An even entry `x ∈ S` (free, `1 ≤ x₂ ≤ L − 2`) keeps its west input `w₁ = x + W` (nonfree white); `w₁`
keeps `w₂ = x + (−1,1)`, which is nonfree white and keeps `x + N`. So both candidate targets lie in `S`. -/
theorem route_even_step {F : Field} (frame : ChildFrame)
    {S : Set Site}
    (hS : ∀ z : Site, 2 - 2 * frame.child.den ≤ frame.sGrade z →
      frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 2 → F z = harmonicGrid z)
    (hO : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 3 * frame.child.den + frame.child.num - 2 → F z = harmonicGrid z)
    (hd : 2 * frame.child.num ≤ frame.child.den)
    (hR : IsRestrictedFort F (AuxRankQ1.permitsQ1 frame F (-1)) S)
    {x : Site} (hx : x ∈ frame.freeV) (hev : EvenSite x) (h1 : 1 ≤ x.2)
    (h2 : x.2 ≤ frame.child.den + frame.child.num - 2) (hxS : x ∈ S) :
    (x.1 - 1, x.2 + 1) ∈ S ∧ (x.1, x.2 + 1) ∈ S := by
  obtain ⟨hn0, hnd, hd2, hd3, -⟩ := frame.child_facts
  obtain ⟨hs1, hs2⟩ := even_grade_strict frame hx hev h1 h2
  obtain ⟨hnf1, hnf2⟩ := wne_nonfree frame hx hev h1 h2
  have hw : laplacian F x = 0 :=
    route_lap_even frame hS hO hev (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hw1S : incomingNeg x ∈ S :=
    route_mem_of_white hR hxS hw (Or.inl rfl)
      (route_permit_even frame hx hw (ne_vFirst_of h1) (ne_vLast_of frame h2) hev)
  have hw1odd : ¬ EvenSite (incomingNeg x) := not_even_incNeg hev
  have hnf1' : Induction.Nonfree frame (incomingNeg x) := by
    rw [incNeg_even_eq hev]
    exact hnf1
  have hw1 : laplacian F (incomingNeg x) = 0 :=
    route_lap_odd frame hS hO hw1odd (by rw [sG_incNeg_even frame hev]; omega)
      (by rw [sG_incNeg_even frame hev]; omega) (by rw [sG_incNeg_even frame hev]; omega)
      (by rw [sG_incNeg_even frame hev]; omega) (by rw [sG_incNeg_even frame hev]; omega)
      (by rw [sG_incNeg_even frame hev]; omega)
  obtain ⟨-, hw1B⟩ := route_inputs_of_nonfree hR hw1S hw1 hnf1'
  have hw2e : EvenSite (incomingPos (incomingNeg x)) := even_incPos_of_odd hw1odd
  have hw2 : laplacian F (incomingPos (incomingNeg x)) = 0 :=
    route_lap_even frame hS hO hw2e
      (by rw [sG_incPos_odd frame hw1odd, sG_incNeg_even frame hev]; omega)
      (by rw [sG_incPos_odd frame hw1odd, sG_incNeg_even frame hev]; omega)
      (by rw [sG_incPos_odd frame hw1odd, sG_incNeg_even frame hev]; omega)
      (by rw [sG_incPos_odd frame hw1odd, sG_incNeg_even frame hev]; omega)
      (by rw [sG_incPos_odd frame hw1odd, sG_incNeg_even frame hev]; omega)
      (by rw [sG_incPos_odd frame hw1odd, sG_incNeg_even frame hev]; omega)
  have hnf2' : Induction.Nonfree frame (incomingPos (incomingNeg x)) := by
    rw [incPos_odd_eq hw1odd, incNeg_even_eq hev]
    have e : x + (-1, 0) + (0, 1) = x + (-1, 1) := by ext <;> simp
    rw [e]
    exact hnf2
  obtain ⟨-, hw2B⟩ := route_inputs_of_nonfree hR hw1B hw2 hnf2'
  have hw2N : incomingPos (incomingPos (incomingNeg x)) = (x.1, x.2 + 1) := by
    rw [FLatticePaper.CapRecursion.incomingPos_of_even' _ hw2e,
      FLatticePaper.CapRecursion.incomingPos_of_odd' _ hw1odd,
      FLatticePaper.CapRecursion.incomingNeg_of_even' x hev]
    ext <;> simp
  have hw2eq : incomingPos (incomingNeg x) = (x.1 - 1, x.2 + 1) := by
    rw [FLatticePaper.CapRecursion.incomingPos_of_odd' _ hw1odd,
      FLatticePaper.CapRecursion.incomingNeg_of_even' x hev]
  rw [hw2N] at hw2B
  rw [hw2eq] at hw1B
  exact ⟨hw1B, hw2B⟩

/-- **One chain step stays in the fort.** For `1 ≤ j` and `j + 2 ≤ L`, if the chain site `vAt j` lies in `S`, so does `vAt (j+1)`. -/
theorem route_stay_at {F : Field} (frame : ChildFrame)
    {S : Set Site}
    (hS : ∀ z : Site, 2 - 2 * frame.child.den ≤ frame.sGrade z →
      frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 2 → F z = harmonicGrid z)
    (hO : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 3 * frame.child.den + frame.child.num - 2 → F z = harmonicGrid z)
    (hd : 2 * frame.child.num ≤ frame.child.den)
    (hR : IsRestrictedFort F (AuxRankQ1.permitsQ1 frame F (-1)) S)
    (j : ℕ) (hj1 : 1 ≤ j) (hj2 : (j : ℤ) + 2 ≤ frame.child.den + frame.child.num)
    (hin : RowAt.vAt frame (j : ℤ) ∈ S) : RowAt.vAt frame ((j : ℤ) + 1) ∈ S := by
  have hjL : (j : ℤ) < frame.child.den + frame.child.num := by omega
  have hvj : RowAt.vAt frame (j : ℤ) = VChain.vpath frame j := RowAt.vAt_nat frame j hjL
  have hvj1 : RowAt.vAt frame ((j : ℤ) + 1) = VChain.vpath frame (j + 1) := by
    have h := RowAt.vAt_nat frame (j + 1) (by push_cast; omega)
    push_cast at h
    exact h
  rw [hvj] at hin
  rw [hvj1, VChain.vpath_succ]
  have hord : (VChain.vpath frame j).2 = (j : ℤ) := VChain.vpath_ord frame j
  have hfree : VChain.vpath frame j ∈ frame.freeV := ListPrefix.vpath_freeV_all frame j hjL
  have h1 : 1 ≤ (VChain.vpath frame j).2 := by omega
  have h2 : (VChain.vpath frame j).2 ≤ frame.child.den + frame.child.num - 2 := by omega
  by_cases hev : EvenSite (VChain.vpath frame j)
  · obtain ⟨hA, hB⟩ := route_even_step frame hS hO hd hR hfree hev h1 h2 hin
    by_cases hN : ((VChain.vpath frame j).1, (VChain.vpath frame j).2 + 1) ∈ frame.freeV
    · rw [VChain.vsucc, if_pos hN]
      exact hB
    · rw [VChain.vsucc, if_neg hN]
      exact hA
  · obtain ⟨hA, hB⟩ := route_odd_step frame hS hO hd hR hfree hev h1 h2 hin
    by_cases hN : ((VChain.vpath frame j).1, (VChain.vpath frame j).2 + 1) ∈ frame.freeV
    · rw [VChain.vsucc, if_pos hN]
      exact hA
    · rw [VChain.vsucc, if_neg hN]
      exact hB hN

/-- **The minus route stays in the fort** (the `hroute` hypothesis of `ListForce.minus_hforce_route`, easy frames `2n ≤ d`). -/
theorem minus_route_stays {F : Field} (frame : ChildFrame)
    {S : Set Site}
    (hS : ∀ z : Site, 2 - 2 * frame.child.den ≤ frame.sGrade z →
      frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 2 → F z = harmonicGrid z)
    (hO : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 3 * frame.child.den + frame.child.num - 2 → F z = harmonicGrid z)
    (hd : 2 * frame.child.num ≤ frame.child.den)
    (hR : IsRestrictedFort F (AuxRankQ1.permitsQ1 frame F (-1)) S)
    (r : ℤ) (hrL2 : r ≤ frame.child.den + frame.child.num - 2) :
    ∀ k : ℕ, (k : ℤ) < r → RowAt.vAt frame (r - (k : ℤ)) ∈ S →
      RowAt.vAt frame (r - (k : ℤ) + 1) ∈ S := by
  intro k hk hin
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = r - (k : ℤ) := ⟨(r - (k : ℤ)).toNat, by omega⟩
  rw [← hj] at hin ⊢
  exact route_stay_at frame hS hO hd hR j (by omega) (by omega) hin

end FLatticePaper.RouteStay
