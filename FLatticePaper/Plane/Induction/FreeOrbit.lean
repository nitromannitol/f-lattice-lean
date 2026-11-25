import FLatticePaper.Plane.Induction.FreeClosure
import FLatticePaper.Plane.Induction.FreeVOrdinate
import FLatticePaper.Plane.Induction.CutRowsAll
import FLatticePaper.Plane.Induction.FreeTraceBox
import FLatticePaper.Plane.Induction.ShortRoute

/-! hgames, the orbit uniqueness of the free set (the representative of the prescription is well defined on the closure).

A span shift `s = iU + jV` (`U = kernel = (d, n)`, `V = transverse = (n − d, n + d)`, `T = d² + 2dn − n²`) changes the grades by
`t ↦ t − jT` and `s ↦ s + iT`, and the coordinates by `x ↦ x + id + j(n−d)`, `y ↦ y + in + j(n+d)`. The free windows are:

* `freeH`: `t ∈ [1, L−1]`, `x ∈ [1, d]`, and `s ∈ [L, T − (d−n)]`;
* `freeV`: `s ∈ [2−d+n, L−2]`, `y ∈ [0, L−1]`.

Two free H sites in one orbit are equal (the `t` window has width `< T`, then the `x` window has width `< d`), and likewise for V (the
`s` window has width `< T`, then the `y` window has width `< L`). A free H site and a free V site are never in one orbit (their `s`
windows are separated by less than `T`). -/

namespace FLatticePaper.FreeOrbit

open Farey FLatticePaper FLatticePaper.Induction

theorem T_gt (frame : ChildFrame) :
    frame.child.num + frame.child.den < frame.child.periodDenominator ∧
      2 * frame.child.den - 4 < frame.child.periodDenominator := by
  obtain ⟨hn0, hnd, hdn, hd3, hT⟩ := frame.child_facts
  rw [hT]
  constructor
  · nlinarith [mul_nonneg (show (0 : ℤ) ≤ frame.child.num by omega) (show (0 : ℤ) ≤ frame.child.den - frame.child.num - 2 by omega),
      mul_nonneg (show (0 : ℤ) ≤ frame.child.num - 1 by omega) (show (0 : ℤ) ≤ frame.child.den - frame.child.num - 2 by omega)]
  · nlinarith [mul_nonneg (show (0 : ℤ) ≤ frame.child.num - 1 by omega) (show (0 : ℤ) ≤ frame.child.den - frame.child.num - 2 by omega),
      mul_nonneg (show (0 : ℤ) ≤ frame.child.den by omega) (show (0 : ℤ) ≤ frame.child.den - frame.child.num - 2 by omega)]

theorem freeH_t_range (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeH) :
    1 ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den + frame.child.num - 1 := by
  obtain ⟨hn0, hnd, hdn, hd3, hT⟩ := frame.child_facts
  obtain ⟨-, -, hS⟩ := hz
  unfold ChildFrame.hSpectrum at hS
  generalize frame.tGrade z = t at hS ⊢
  rcases hS with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> constructor <;> omega

theorem freeV_s_range (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV) :
    2 - frame.child.den + frame.child.num ≤ frame.sGrade z ∧
      frame.sGrade z ≤ frame.child.den + frame.child.num - 2 := by
  obtain ⟨hn0, hnd, hdn, hd3, hT⟩ := frame.child_facts
  obtain ⟨-, -, hS⟩ := hz
  unfold ChildFrame.vSpectrum at hS
  generalize frame.sGrade z = s at hS ⊢
  obtain ⟨-, h⟩ := hS
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> omega

theorem freeV_y_range (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV) :
    0 ≤ z.2 ∧ z.2 ≤ frame.child.den + frame.child.num - 1 := by
  by_cases he : EvenSite z
  · obtain ⟨h1, h2, -⟩ := FLatticePaper.FreeVOrdinate.freeV_even_ordinate frame hz he
    exact ⟨h1, h2⟩
  · obtain ⟨h1, h2⟩ := FLatticePaper.FreeVOrdinate.freeV_odd_ordinate frame
      (FLatticePaper.CutRowsAll.cut_one_per_ordinate_all frame) hz he
    exact ⟨h1, by omega⟩

theorem fst_shift (frame : ChildFrame) (a : Site) (i j : ℤ) :
    (a + frame.child.modifiedDeck.combine i j).1 =
      a.1 + (i * frame.child.den + j * (frame.child.num - frame.child.den)) := by
  rw [Prod.fst_add, frame.combine_coords]

theorem snd_shift (frame : ChildFrame) (a : Site) (i j : ℤ) :
    (a + frame.child.modifiedDeck.combine i j).2 =
      a.2 + (i * frame.child.num + j * (frame.child.num + frame.child.den)) := by
  rw [Prod.snd_add, frame.combine_coords]

/-- Two free H sites in one orbit: the shift is zero. -/
theorem orbit_HH (frame : ChildFrame) {a : Site} (ha : a ∈ frame.freeH) {i j : ℤ}
    (hb : a + frame.child.modifiedDeck.combine i j ∈ frame.freeH) : i = 0 ∧ j = 0 := by
  obtain ⟨hn0, hnd, hdn, hd3, hT⟩ := frame.child_facts
  obtain ⟨hTL, -⟩ := T_gt frame
  obtain ⟨ha1, ha2⟩ := freeH_t_range frame ha
  obtain ⟨hb1, hb2⟩ := freeH_t_range frame hb
  have hts := frame.tGrade_add_deck a i j
  obtain ⟨hx1, hxd, -, -⟩ := FLatticePaper.Induction.FreeTraceBox.freeH_box frame ha
  obtain ⟨hx1', hxd', -, -⟩ := FLatticePaper.Induction.FreeTraceBox.freeH_box frame hb
  have hxs := fst_shift frame a i j
  have hTpos : 0 < frame.child.periodDenominator := by omega
  have hj : j = 0 := by
    rcases lt_trichotomy j 0 with h | h | h
    · have h1 : (1 : ℤ) ≤ -j := by omega
      nlinarith
    · exact h
    · have h1 : (1 : ℤ) ≤ j := by omega
      nlinarith
  subst hj
  have hi : i = 0 := by
    rcases lt_trichotomy i 0 with h | h | h
    · have h1 : (1 : ℤ) ≤ -i := by omega
      nlinarith
    · exact h
    · have h1 : (1 : ℤ) ≤ i := by omega
      nlinarith
  exact ⟨hi, rfl⟩

/-- Two free V sites in one orbit: the shift is zero. -/
theorem orbit_VV (frame : ChildFrame) {a : Site} (ha : a ∈ frame.freeV) {i j : ℤ}
    (hb : a + frame.child.modifiedDeck.combine i j ∈ frame.freeV) : i = 0 ∧ j = 0 := by
  obtain ⟨hn0, hnd, hdn, hd3, hT⟩ := frame.child_facts
  obtain ⟨-, hTw⟩ := T_gt frame
  obtain ⟨ha1, ha2⟩ := freeV_s_range frame ha
  obtain ⟨hb1, hb2⟩ := freeV_s_range frame hb
  have hss := frame.sGrade_add_deck a i j
  obtain ⟨hy1, hy2⟩ := freeV_y_range frame ha
  obtain ⟨hy1', hy2'⟩ := freeV_y_range frame hb
  have hys := snd_shift frame a i j
  have hTpos : 0 < frame.child.periodDenominator := by omega
  have hi : i = 0 := by
    rcases lt_trichotomy i 0 with h | h | h
    · have h1 : (1 : ℤ) ≤ -i := by omega
      nlinarith
    · exact h
    · have h1 : (1 : ℤ) ≤ i := by omega
      nlinarith
  subst hi
  have hL : 0 < frame.child.den + frame.child.num := by omega
  have hj : j = 0 := by
    rcases lt_trichotomy j 0 with h | h | h
    · have h1 : (1 : ℤ) ≤ -j := by omega
      nlinarith
    · exact h
    · have h1 : (1 : ℤ) ≤ j := by omega
      nlinarith
  exact ⟨rfl, hj⟩

/-- A free H site and a free V site are never in one orbit (the `s` windows are separated by less than `T`). -/
theorem not_HV (frame : ChildFrame) {a : Site} (ha : a ∈ frame.freeH) {i j : ℤ} :
    a + frame.child.modifiedDeck.combine i j ∉ frame.freeV := by
  intro hb
  obtain ⟨hn0, hnd, hdn, hd3, hT⟩ := frame.child_facts
  obtain ⟨hTL, -⟩ := T_gt frame
  obtain ⟨hb1, hb2⟩ := freeV_s_range frame hb
  obtain ⟨ha1, ha2⟩ := FLatticePaper.ShortRoute.freeH_sGrade_bounds frame ha
  have hss := frame.sGrade_add_deck a i j
  have hTpos : 0 < frame.child.periodDenominator := by omega
  rcases lt_trichotomy i 0 with h | h | h
  · have h1 : (1 : ℤ) ≤ -i := by omega
    nlinarith
  · subst h
    simp only [zero_mul, add_zero] at hss
    omega
  · have h1 : (1 : ℤ) ≤ i := by omega
    nlinarith

/-- A free V site and a free H site are never in one orbit. -/
theorem not_VH (frame : ChildFrame) {a : Site} (ha : a ∈ frame.freeV) {i j : ℤ} :
    a + frame.child.modifiedDeck.combine i j ∉ frame.freeH := by
  intro hb
  obtain ⟨hn0, hnd, hdn, hd3, hT⟩ := frame.child_facts
  obtain ⟨-, hTw⟩ := T_gt frame
  obtain ⟨ha1, ha2⟩ := freeV_s_range frame ha
  obtain ⟨hb1, hb2⟩ := FLatticePaper.ShortRoute.freeH_sGrade_bounds frame hb
  have hss := frame.sGrade_add_deck a i j
  have hTpos : 0 < frame.child.periodDenominator := by omega
  rcases lt_trichotomy i 0 with h | h | h
  · have h1 : (1 : ℤ) ≤ -i := by omega
    nlinarith
  · subst h
    simp only [zero_mul, add_zero] at hss
    omega
  · have h1 : (1 : ℤ) ≤ i := by omega
    nlinarith

/-! The representative statements used by the policy. -/

/-- A free H site has no other free H site in its span orbit: a span translate landing in `freeH` is the site itself. -/
theorem freeH_rep_zero (frame : ChildFrame) {a t : Site} (ht : t ∈ frame.child.modifiedDeck.span)
    (ha : a ∈ frame.freeH) (hb : a + t ∈ frame.freeH) : t = 0 := by
  obtain ⟨i, j, rfl⟩ := ht
  obtain ⟨hi, hj⟩ := orbit_HH frame ha hb
  subst hi
  subst hj
  ext <;> simp [PeriodDeck.combine]

/-- A free V site has no other free V site in its span orbit. -/
theorem freeV_rep_zero (frame : ChildFrame) {a t : Site} (ht : t ∈ frame.child.modifiedDeck.span)
    (ha : a ∈ frame.freeV) (hb : a + t ∈ frame.freeV) : t = 0 := by
  obtain ⟨i, j, rfl⟩ := ht
  obtain ⟨hi, hj⟩ := orbit_VV frame ha hb
  subst hi
  subst hj
  ext <;> simp [PeriodDeck.combine]

/-- A free H site has no free V site in its span orbit (in particular `freeH ∩ freeV = ∅`). -/
theorem freeH_not_freeV_shift (frame : ChildFrame) {a t : Site} (ht : t ∈ frame.child.modifiedDeck.span)
    (ha : a ∈ frame.freeH) : a + t ∉ frame.freeV := by
  obtain ⟨i, j, rfl⟩ := ht
  exact not_HV frame ha

/-- A free V site has no free H site in its span orbit. -/
theorem freeV_not_freeH_shift (frame : ChildFrame) {a t : Site} (ht : t ∈ frame.child.modifiedDeck.span)
    (ha : a ∈ frame.freeV) : a + t ∉ frame.freeH := by
  obtain ⟨i, j, rfl⟩ := ht
  exact not_VH frame ha

theorem freeH_disjoint_freeV (frame : ChildFrame) {a : Site} (ha : a ∈ frame.freeH) : a ∉ frame.freeV := by
  have h := freeH_not_freeV_shift frame (t := 0) (show (0 : Site) ∈ frame.child.modifiedDeck.span from ⟨0, 0, by ext <;> simp [PeriodDeck.combine]⟩) ha
  simpa using h

end FLatticePaper.FreeOrbit
