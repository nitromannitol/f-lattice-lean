import FLatticePaper.Plane.Induction.FreeEnum
import FLatticePaper.Plane.Induction.FreeVWindow
import FLatticePaper.Plane.Induction.NonfreeBridge
import FLatticePaper.Plane.Induction.TipVertex
import FLatticePaper.Plane.Induction.Q3Hlat
import FLatticePaper.Plane.Induction.NativeGrade
import FLatticePaper.Plane.Induction.HWeb

/-! Task w3, step 2 (E3): the extended V cut is the unique point of each ordinate in the V windows.

For any child frame: `s(V) = 0` and `s(v) = 2` (`v = parentShift`), `V` and `v` have even coordinate sums, and `s` is additive.
(1) `vAt base j` has the window of its parity (the deck `V` keeps `s` and parity; `freeV` gives the windows on `0 ≤ j < L`).
(2) Uniqueness in a row: two sites of one ordinate and one parity, both in their window, are equal (`s` differs by `2 L k`, and
the windows are narrower than `2L`).
(3) `E3`: unless `s(vAt base j)` is the lower end of its window, `vAt base j − v = vAt base (j − ε r)`, where `r = N + D`. -/

namespace FLatticePaper.VWindow

open Farey FLatticePaper FLatticePaper.Induction

theorem sGrade_add (frame : ChildFrame) (a b : Site) : frame.sGrade (a + b) = frame.sGrade a + frame.sGrade b := by
  unfold ChildFrame.sGrade
  simp only [Prod.fst_add, Prod.snd_add]
  ring

theorem sGrade_smul (frame : ChildFrame) (m : ℤ) (a : Site) : frame.sGrade (m • a) = m * frame.sGrade a := by
  unfold ChildFrame.sGrade
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- `s(V) = 0`. -/
theorem sGrade_Vdeck (frame : ChildFrame) : frame.sGrade (Vdeck frame) = 0 := by
  unfold ChildFrame.sGrade Vdeck
  ring

/-- `s(v) = 2` for the parent shift `v = ε(N − D, N + D)`. -/
theorem sGrade_parentShift (frame : ChildFrame) : frame.sGrade frame.parentShift = 2 := by
  have hdet := frame.odd_det_child
  have hsq := frame.eps_sq_one
  unfold ChildFrame.sGrade ChildFrame.parentShift
  simp only
  linear_combination (2 * frame.eps) * hdet + 2 * hsq

/-- `V` has even coordinate sum, so it preserves parity. -/
theorem evenSite_add_Vdeck (frame : ChildFrame) (a : Site) (m : ℤ) :
    EvenSite (a + m • Vdeck frame) ↔ EvenSite a := by
  unfold EvenSite Vdeck
  simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
  have e : a.1 + m * (frame.child.num - frame.child.den) + (a.2 + m * (frame.child.num + frame.child.den)) =
      (a.1 + a.2) + 2 * (m * frame.child.num) := by ring
  rw [e]
  generalize m * frame.child.num = q
  omega

/-- `v` has even coordinate sum. -/
theorem evenSite_add_parentShift (frame : ChildFrame) (a : Site) : EvenSite (a + frame.parentShift) ↔ EvenSite a := by
  have hev : (frame.parents.odd.num + frame.parents.odd.den) % 2 = 1 := frame.valid.odd_parity
  unfold EvenSite ChildFrame.parentShift
  simp only [Prod.fst_add, Prod.snd_add]
  have e : a.1 + frame.eps * (frame.parents.odd.num - frame.parents.odd.den) + (a.2 + frame.eps * (frame.parents.odd.num + frame.parents.odd.den)) =
      (a.1 + a.2) + 2 * (frame.eps * frame.parents.odd.num) := by ring
  rw [e]
  generalize frame.eps * frame.parents.odd.num = q
  omega

/-- **The window of `vAt`:** the V cut, extended by `V`, has in each ordinate the window of its parity. -/
theorem vAt_window (frame : ChildFrame) (base : ℤ → Site)
    (hbase : ∀ r : ℤ, 0 ≤ r → r < FreeEnum.period frame → base r ∈ frame.freeV ∧ (base r).2 = r) (j : ℤ) :
    (EvenSite (FreeEnum.vAt frame base j) → 0 ≤ frame.sGrade (FreeEnum.vAt frame base j) ∧
        frame.sGrade (FreeEnum.vAt frame base j) ≤ 2 * frame.child.num) ∧
      (¬ EvenSite (FreeEnum.vAt frame base j) →
        2 - frame.child.den + frame.child.num ≤ frame.sGrade (FreeEnum.vAt frame base j) ∧
          frame.sGrade (FreeEnum.vAt frame base j) ≤ frame.child.den + frame.child.num - 2) := by
  have hp := FreeEnum.period_pos frame
  have hvA : FreeEnum.vAt frame base j = base (j % FreeEnum.period frame) + (j / FreeEnum.period frame) • Vdeck frame := by
    unfold FreeEnum.vAt
    ext <;> simp
  have hmem := hbase (j % FreeEnum.period frame) (Int.emod_nonneg _ hp.ne') (Int.emod_lt_of_pos _ hp)
  rw [hvA]
  have hs : frame.sGrade (base (j % FreeEnum.period frame) + (j / FreeEnum.period frame) • Vdeck frame) =
      frame.sGrade (base (j % FreeEnum.period frame)) := by
    rw [sGrade_add, sGrade_smul, sGrade_Vdeck]
    ring
  rw [hs, evenSite_add_Vdeck]
  constructor
  · intro he
    exact FreeVWindow.freeV_even_window frame hmem.1 he
  · intro ho
    obtain ⟨h1, h2⟩ := FreeVWindow.freeV_odd_window frame hmem.1 ho
    exact ⟨by omega, by omega⟩

/-- **Uniqueness in a row.** Two sites of one ordinate, each in the window of its own parity, are equal. Same parity: `s` differs
by `2 L k`, narrower than `2L`. Different parity: `s` differs by an odd multiple of `L` inside a range of width `L − 2`, impossible. -/
theorem row_unique (frame : ChildFrame) {p q : Site} (hord : p.2 = q.2)
    (hp : (EvenSite p → 0 ≤ frame.sGrade p ∧ frame.sGrade p ≤ 2 * frame.child.num) ∧
      (¬ EvenSite p → 2 - frame.child.den + frame.child.num ≤ frame.sGrade p ∧
        frame.sGrade p ≤ frame.child.den + frame.child.num - 2))
    (hq : (EvenSite q → 0 ≤ frame.sGrade q ∧ frame.sGrade q ≤ 2 * frame.child.num) ∧
      (¬ EvenSite q → 2 - frame.child.den + frame.child.num ≤ frame.sGrade q ∧
        frame.sGrade q ≤ frame.child.den + frame.child.num - 2)) : p = q := by
  obtain ⟨hn0, hnd, hdn, hd3, -⟩ := frame.child_facts
  obtain ⟨hnodd, hdodd⟩ := frame.child_odd
  have hdiff : frame.sGrade p - frame.sGrade q = (frame.child.den + frame.child.num) * (p.1 - q.1) := by
    unfold ChildFrame.sGrade
    rw [hord]
    ring
  have hL : 0 < frame.child.den + frame.child.num := by omega
  have hpar : (p.1 - q.1) % 2 = 0 ∨ (p.1 - q.1) % 2 = 1 := by omega
  have hxeq : p.1 = q.1 := by
    by_cases hpe : EvenSite p <;> by_cases hqe : EvenSite q
    · -- both even: the difference is an even multiple of L
      obtain ⟨k, hk⟩ : ∃ k, p.1 - q.1 = 2 * k := by
        unfold EvenSite at hpe hqe
        exact ⟨(p.1 - q.1) / 2, by omega⟩
      have hb1 := hp.1 hpe
      have hb2 := hq.1 hqe
      rw [hk] at hdiff
      have hn : frame.child.num < frame.child.den + frame.child.num := by omega
      rcases lt_trichotomy k 0 with h | h | h
      · nlinarith
      · rw [h] at hk; omega
      · nlinarith
    · -- p even, q odd: impossible
      exfalso
      obtain ⟨k, hk⟩ : ∃ k, p.1 - q.1 = 2 * k + 1 := by
        unfold EvenSite at hpe hqe
        exact ⟨(p.1 - q.1 - 1) / 2, by omega⟩
      have hb1 := hp.1 hpe
      have hb2 := hq.2 hqe
      rw [hk] at hdiff
      rcases le_or_gt 0 k with h | h
      · nlinarith
      · nlinarith
    · -- p odd, q even: impossible
      exfalso
      obtain ⟨k, hk⟩ : ∃ k, p.1 - q.1 = 2 * k + 1 := by
        unfold EvenSite at hpe hqe
        exact ⟨(p.1 - q.1 - 1) / 2, by omega⟩
      have hb1 := hp.2 hpe
      have hb2 := hq.1 hqe
      rw [hk] at hdiff
      rcases le_or_gt 0 k with h | h
      · nlinarith
      · nlinarith
    · -- both odd: the difference is an even multiple of L
      obtain ⟨k, hk⟩ : ∃ k, p.1 - q.1 = 2 * k := by
        unfold EvenSite at hpe hqe
        exact ⟨(p.1 - q.1) / 2, by omega⟩
      have hb1 := hp.2 hpe
      have hb2 := hq.2 hqe
      rw [hk] at hdiff
      rcases lt_trichotomy k 0 with h | h | h
      · nlinarith
      · rw [h] at hk; omega
      · nlinarith
  exact Prod.ext hxeq hord

/-- **E3, the shift by `−v`.** Unless `s(vAt base j)` is the lower end of its window, `vAt base j − v` is the extended V point of
ordinate `j − ε r` (`r = N + D`). -/
theorem shift_vAt (frame : ChildFrame) (base : ℤ → Site)
    (hbase : ∀ r : ℤ, 0 ≤ r → r < FreeEnum.period frame → base r ∈ frame.freeV ∧ (base r).2 = r) (j : ℤ)
    (hns : (EvenSite (FreeEnum.vAt frame base j) → frame.sGrade (FreeEnum.vAt frame base j) ≠ 0) ∧
      (¬ EvenSite (FreeEnum.vAt frame base j) → frame.sGrade (FreeEnum.vAt frame base j) ≠ 2 - frame.child.den + frame.child.num)) :
    FreeEnum.vAt frame base j - frame.parentShift =
      FreeEnum.vAt frame base (j - frame.eps * (frame.parents.odd.den + frame.parents.odd.num)) := by
  obtain ⟨hn0, hnd, hdn, hd3, -⟩ := frame.child_facts
  obtain ⟨hnodd, hdodd⟩ := frame.child_odd
  set x := FreeEnum.vAt frame base j with hx
  have hwx := vAt_window frame base hbase j
  rw [← hx] at hwx
  have hxord : x.2 = j := FreeEnum.vAt_snd frame base (fun r h0 h1 => (hbase r h0 h1).2) j
  have hsv := sGrade_parentShift frame
  have hsx : frame.sGrade (x - frame.parentShift) = frame.sGrade x - 2 := by
    have := sGrade_add frame (x - frame.parentShift) frame.parentShift
    rw [sub_add_cancel, hsv] at this
    linarith
  have hpar : EvenSite (x - frame.parentShift) ↔ EvenSite x := by
    have := evenSite_add_parentShift frame (x - frame.parentShift)
    rw [sub_add_cancel] at this
    exact this.symm
  have hsev := sGrade_even frame x
  -- the window of x − v
  have hwin : (EvenSite (x - frame.parentShift) → 0 ≤ frame.sGrade (x - frame.parentShift) ∧
        frame.sGrade (x - frame.parentShift) ≤ 2 * frame.child.num) ∧
      (¬ EvenSite (x - frame.parentShift) → 2 - frame.child.den + frame.child.num ≤ frame.sGrade (x - frame.parentShift) ∧
        frame.sGrade (x - frame.parentShift) ≤ frame.child.den + frame.child.num - 2) := by
    constructor
    · intro he
      have hxe := hpar.mp he
      have hw := hwx.1 hxe
      have hne := hns.1 hxe
      rw [hsx]
      constructor
      · have : frame.sGrade x ≥ 2 := by
          have : frame.sGrade x ≥ 0 := hw.1
          have : frame.sGrade x ≠ 0 := hne
          omega
        omega
      · omega
    · intro ho
      have hxo : ¬ EvenSite x := fun h => ho (hpar.mpr h)
      have hw := hwx.2 hxo
      have hne := hns.2 hxo
      rw [hsx]
      constructor
      · have : frame.sGrade x ≠ 2 - frame.child.den + frame.child.num := hne
        omega
      · omega
  -- the target point is in its window
  have hy := vAt_window frame base hbase (j - frame.eps * (frame.parents.odd.den + frame.parents.odd.num))
  have hyord := FreeEnum.vAt_snd frame base (fun r h0 h1 => (hbase r h0 h1).2)
    (j - frame.eps * (frame.parents.odd.den + frame.parents.odd.num))
  have hxo_ord : (x - frame.parentShift).2 = j - frame.eps * (frame.parents.odd.den + frame.parents.odd.num) := by
    unfold ChildFrame.parentShift
    simp only [Prod.snd_sub]
    rw [hxord]
    ring
  -- both points have the same ordinate; uniqueness of the row point gives the equality
  have hyw : (EvenSite (FreeEnum.vAt frame base (j - frame.eps * (frame.parents.odd.den + frame.parents.odd.num))) →
        0 ≤ frame.sGrade (FreeEnum.vAt frame base (j - frame.eps * (frame.parents.odd.den + frame.parents.odd.num))) ∧
        frame.sGrade (FreeEnum.vAt frame base (j - frame.eps * (frame.parents.odd.den + frame.parents.odd.num))) ≤ 2 * frame.child.num) ∧
      (¬ EvenSite (FreeEnum.vAt frame base (j - frame.eps * (frame.parents.odd.den + frame.parents.odd.num))) →
        2 - frame.child.den + frame.child.num ≤ frame.sGrade (FreeEnum.vAt frame base (j - frame.eps * (frame.parents.odd.den + frame.parents.odd.num))) ∧
        frame.sGrade (FreeEnum.vAt frame base (j - frame.eps * (frame.parents.odd.den + frame.parents.odd.num))) ≤ frame.child.den + frame.child.num - 2) := hy
  exact row_unique frame (by rw [hxo_ord, hyord]) hwin hyw

end FLatticePaper.VWindow
