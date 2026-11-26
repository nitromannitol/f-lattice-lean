import FLatticePaper.Plane.Induction.Sec3Shift
import FLatticePaper.Plane.Induction.FreeVH0
import FLatticePaper.Plane.Induction.PriceInputs
import FLatticePaper.Plane.Induction.FreePolicy
import FLatticePaper.Plane.Induction.FreeVWindow
import FLatticePaper.Plane.Induction.FreeVOrdinate
import FLatticePaper.Plane.Induction.ArcRanges
import FLatticePaper.Plane.Induction.ParentStrip
import FLatticePaper.Plane.Induction.RootClassify
import FLatticePaper.Plane.Induction.CutRowsAll
import FLatticePaper.Plane.Induction.StrongCoreDef

namespace FLatticePaper.SheetStars

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.Sec3Shift FLatticePaper.W1MSheet

/-- The parent sums `N + D` and `D − N` are odd (`ε` odd, the even parent is odd on both entries). -/
theorem parent_sums_odd {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) :
    ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) % 2 = 1 ∧
      ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) % 2 = 1 := by
  obtain ⟨hN1, hND, hD2, hn0, hd0, hn, hd, heps, hε⟩ := PriceInputs.pdata h
  obtain ⟨hco1, hco2⟩ := (frameAt word).child_odd
  obtain ⟨a, ha⟩ : ∃ a, (frameAt word).parents.even.den = 2 * a + 1 :=
    ⟨(frameAt word).parents.even.den / 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, (frameAt word).parents.even.num = 2 * b + 1 :=
    ⟨(frameAt word).parents.even.num / 2, by omega⟩
  obtain ⟨k, hk⟩ : ∃ k, (frameAt word).eps =
      (frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 2 * k :=
    ⟨(frameAt word).parents.odd.num * a - b * (frameAt word).parents.odd.den, by rw [heps, ha, hb]; ring⟩
  rcases hε with h1 | h1 <;> constructor <;> omega

theorem sGrade_sec3X_bounds {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) :
    0 ≤ (frameAt word).sGrade (sec3X word) ∧
    (frameAt word).sGrade (sec3X word) ≤ (frameAt word).child.periodDenominator - 2 * (frameAt word).child.num - 2 ∧
    2 * ((frameAt word).child.den - (frameAt word).child.num) - 2 ≤ (frameAt word).sGrade (sec3X word) := by
  obtain ⟨hN1, hND, hD2, hn0, hd0, hn, hd, heps, hε⟩ := PriceInputs.pdata h
  obtain ⟨hco1, hco2⟩ := (frameAt word).child_odd
  obtain ⟨-, -, -, -, hT⟩ := (frameAt word).child_facts
  have hp1 : 1 ≤ (frameAt word).parents.even.num := by omega
  have hq1 : 1 ≤ (frameAt word).parents.even.den := by omega
  have hDN : 1 ≤ (frameAt word).parents.odd.den - (frameAt word).parents.odd.num := by omega
  unfold sec3X
  rcases hε with h1 | h1
  · rw [if_pos h1]
    unfold Upar ChildFrame.sGrade
    dsimp only
    rw [hT, hn, hd]
    rw [h1] at heps
    have hr : (frameAt word).parents.odd.num * (frameAt word).parents.even.den -
        (frameAt word).parents.even.num * (frameAt word).parents.odd.den = 1 := heps.symm
    generalize (frameAt word).parents.odd.num = N at *
    generalize (frameAt word).parents.odd.den = D at *
    generalize (frameAt word).parents.even.num = p at *
    generalize (frameAt word).parents.even.den = q at *
    refine ⟨?_, ?_, ?_⟩
    · nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ D) (by omega : (0:ℤ) ≤ q), mul_nonneg (by omega : (0:ℤ) ≤ N) (by omega : (0:ℤ) ≤ D - N)]
    · nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ D - N - 1) (by omega : (0:ℤ) ≤ q),
        mul_nonneg (by omega : (0:ℤ) ≤ N) (by omega : (0:ℤ) ≤ q - 1),
        mul_nonneg (by omega : (0:ℤ) ≤ p - 1) (by omega : (0:ℤ) ≤ q - 1),
        mul_nonneg (by omega : (0:ℤ) ≤ p - 1) (by omega : (0:ℤ) ≤ D - N - 1)]
    · nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ N - 1) (by omega : (0:ℤ) ≤ D - N),
        mul_nonneg (by omega : (0:ℤ) ≤ D) (by omega : (0:ℤ) ≤ N)]
  · rw [if_neg (by rw [h1]; norm_num)]
    unfold Fraction.unmodifiedDeck ChildFrame.sGrade
    dsimp only
    rw [hT, hn, hd]
    rw [h1] at heps
    have hr : (frameAt word).parents.odd.num * (frameAt word).parents.even.den -
        (frameAt word).parents.even.num * (frameAt word).parents.odd.den = -1 := heps.symm
    generalize (frameAt word).parents.odd.num = N at *
    generalize (frameAt word).parents.odd.den = D at *
    generalize (frameAt word).parents.even.num = p at *
    generalize (frameAt word).parents.even.den = q at *
    refine ⟨?_, ?_, ?_⟩
    · nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ p) (by omega : (0:ℤ) ≤ D - N), mul_nonneg (by omega : (0:ℤ) ≤ q) (by omega : (0:ℤ) ≤ D + N)]
    · nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ D - N - 1) (by omega : (0:ℤ) ≤ q),
        mul_nonneg (by omega : (0:ℤ) ≤ N) (by omega : (0:ℤ) ≤ p - 1),
        mul_nonneg (by omega : (0:ℤ) ≤ p - 1) (by omega : (0:ℤ) ≤ q - 1),
        mul_nonneg (by omega : (0:ℤ) ≤ D - N - 1) (by omega : (0:ℤ) ≤ p)]
    · nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ q - 1) (by omega : (0:ℤ) ≤ D + N),
        mul_nonneg (by omega : (0:ℤ) ≤ p - 1) (by omega : (0:ℤ) ≤ D - N)]

/-- The shift `X` has even coordinate sum: `U_p = 2(D, N)` and the even parent's kernel `(d_q, n_q)` (both odd). -/
theorem sec3X_parity {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) :
    ((sec3X word).1 + (sec3X word).2) % 2 = 0 := by
  obtain ⟨hN1, hND, hD2, hn0, hd0, hn, hd, heps, hε⟩ := PriceInputs.pdata h
  obtain ⟨hco1, hco2⟩ := (frameAt word).child_odd
  unfold sec3X
  split_ifs with h1
  · unfold Upar
    dsimp only
    omega
  · unfold Fraction.unmodifiedDeck
    dsimp only
    omega

theorem sGrade_add' (frame : ChildFrame) (z w : Site) :
    frame.sGrade (z + w) = frame.sGrade z + frame.sGrade w := by
  unfold ChildFrame.sGrade; simp only [Prod.fst_add, Prod.snd_add]; ring

theorem tGrade_add' (frame : ChildFrame) (z w : Site) :
    frame.tGrade (z + w) = frame.tGrade z + frame.tGrade w := by
  unfold ChildFrame.tGrade; simp only [Prod.fst_add, Prod.snd_add]; ring

/-- A closed-polygon site of even parity from its even bounds. -/
theorem even_closed_of_bounds (frame : ChildFrame) {y : Site} (hy : EvenSite y)
    (ht : 2 - frame.child.periodDenominator ≤ frame.tGrade y ∧ frame.tGrade y ≤ frame.child.den + frame.child.num - 2)
    (hs : 0 ≤ frame.sGrade y ∧ frame.sGrade y ≤ frame.child.periodDenominator + 2 * frame.child.num) :
    y ∈ frame.closedPolygon := by
  rw [ChildFrame.mem_closedPolygon_iff]
  left
  exact ⟨hy, ht.1, ht.2, hs.1, hs.2⟩

/-- A closed-polygon site of odd parity from its odd bounds. -/
theorem odd_closed_of_bounds (frame : ChildFrame) {y : Site} (hy : ¬ EvenSite y)
    (ht : frame.child.num - frame.child.periodDenominator ≤ frame.tGrade y ∧ frame.tGrade y ≤ frame.child.den)
    (hs : 2 - frame.child.den + frame.child.num ≤ frame.sGrade y ∧
      frame.sGrade y ≤ frame.child.periodDenominator + frame.child.den + frame.child.num - 2) :
    y ∈ frame.closedPolygon := by
  rw [ChildFrame.mem_closedPolygon_iff]
  right
  exact ⟨hy, ht.1, ht.2, hs.1, hs.2⟩

/-- `T ≥ 4` for a child with `1 ≤ n`, `n + 2 ≤ d`. -/
theorem periodDenominator_ge_four (frame : ChildFrame) : 4 ≤ frame.child.periodDenominator := by
  obtain ⟨hn0, hnd, hd2, -, hT⟩ := frame.child_facts
  rw [hT]
  nlinarith

/-- The t-range of a free even V site other than the final vertex, `4 − T ≤ t ≤ 0`. -/
theorem tGrade_even_free_range (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV) (he : EvenSite z)
    (hne : z ≠ frame.vLast) : 4 - frame.child.periodDenominator ≤ frame.tGrade z ∧ frame.tGrade z ≤ 0 := by
  obtain ⟨hn0, hnd, hd2, hd3, hT⟩ := frame.child_facts
  have hT4 := periodDenominator_ge_four frame
  by_cases hv : z = FLatticePaper.Induction.vFirst
  · subst hv
    have : frame.tGrade FLatticePaper.Induction.vFirst = 0 := by
      unfold FLatticePaper.Induction.vFirst ChildFrame.tGrade; ring
    rw [this]; constructor <;> linarith
  · obtain ⟨a1, a2⟩ := FLatticePaper.ArcRanges.arc_even_range frame hz he hv hne
    constructor <;> nlinarith

/-- The shifted even star: `x + X` lies in the closed polygon for an even free V site `x ≠ V_end`. -/
theorem even_shift_mem_of_freeV {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) {w : Site}
    (hw : w ∈ (frameAt word).freeV) (he : EvenSite w) (hne : w ≠ (frameAt word).vLast) :
    w + sec3X word ∈ (frameAt word).closedPolygon := by
  have hX := sGrade_sec3X_bounds h
  have hXt := tGrade_sec3X word
  have hXpar := sec3X_parity h
  have ht := tGrade_even_free_range (frameAt word) hw he hne
  have hs := FreeVWindow.freeV_even_window (frameAt word) hw he
  have hpar : EvenSite (w + sec3X word) := by
    unfold EvenSite at he ⊢; simp only [Prod.fst_add, Prod.snd_add]; omega
  obtain ⟨hn0, hnd, -, -, hT⟩ := (frameAt word).child_facts
  apply even_closed_of_bounds (frameAt word) hpar
  · rw [tGrade_add', hXt]; constructor <;> linarith [ht.1, ht.2]
  · rw [sGrade_add']; constructor <;> linarith [hs.1, hs.2, hX.1, hX.2.1]

/-- The shifted odd star: `x + X` lies in the closed polygon for an odd free V site. -/
theorem odd_shift_mem_of_freeV {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) {w : Site}
    (hw : w ∈ (frameAt word).freeV) (ho : ¬ EvenSite w) :
    w + sec3X word ∈ (frameAt word).closedPolygon := by
  have hX := sGrade_sec3X_bounds h
  have hXt := tGrade_sec3X word
  have hXpar := sec3X_parity h
  have ht := FLatticePaper.ArcRanges.arc_odd_range (frameAt word) hw ho
  have hs := FreeVWindow.freeV_odd_window (frameAt word) hw ho
  have hpar : ¬ EvenSite (w + sec3X word) := by
    unfold EvenSite at ho ⊢; simp only [Prod.fst_add, Prod.snd_add]; omega
  obtain ⟨hn0, hnd, hd2, -, hT⟩ := (frameAt word).child_facts
  apply odd_closed_of_bounds (frameAt word) hpar
  · rw [tGrade_add', hXt]; constructor <;> linarith [ht.1, ht.2]
  · rw [sGrade_add']; constructor <;> linarith [hs.1, hs.2, hX.1, hX.2.1, hX.2.2]

theorem prescribedV_even_one (frame : ChildFrame) {w : Site} (he : EvenSite w) :
    frame.prescribedV 1 w = (1, 0) := by
  rw [FLatticePaper.FreePolicy.pV_even frame 1 he]
  split_ifs <;> rfl

theorem prescribedV_odd_one (frame : ChildFrame) {w : Site} (ho : ¬ EvenSite w) :
    frame.prescribedV 1 w = (0, -1) := by
  rw [FLatticePaper.FreePolicy.pV_odd frame 1 ho]

theorem tGrade_one_zero (frame : ChildFrame) : frame.tGrade (1, 0) = frame.child.num := by
  unfold ChildFrame.tGrade; ring

theorem sGrade_one_zero (frame : ChildFrame) : frame.sGrade (1, 0) = frame.child.den + frame.child.num := by
  unfold ChildFrame.sGrade; ring

theorem tGrade_zero_neg (frame : ChildFrame) : frame.tGrade (0, -1) = frame.child.den := by
  unfold ChildFrame.tGrade; ring

theorem sGrade_zero_neg (frame : ChildFrame) : frame.sGrade (0, -1) = frame.child.num - frame.child.den := by
  unfold ChildFrame.sGrade; ring

/-- The even free V site `w ≠ V_end` and its east step `u = w + (1,0)`: `u + X` lies in the closed polygon. -/
theorem u_even_shift_mem (word : Word) (h : ∃ x ∈ word, x ≠ Digit.three) {w : Site}
    (hw : w ∈ (frameAt word).freeV) (he : EvenSite w) (hne : w ≠ (frameAt word).vLast) :
    (w + (1, 0)) + sec3X word ∈ (frameAt word).closedPolygon := by
  have hX := sGrade_sec3X_bounds h
  have hXt := tGrade_sec3X word
  have hXpar := sec3X_parity h
  have ht := tGrade_even_free_range (frameAt word) hw he hne
  have hs := FreeVWindow.freeV_even_window (frameAt word) hw he
  obtain ⟨hn0, hnd, hd2, -, hT⟩ := (frameAt word).child_facts
  have hodd : ¬ EvenSite ((w + (1, 0)) + sec3X word) := by
    unfold EvenSite at he ⊢; simp only [Prod.fst_add, Prod.snd_add]; omega
  apply odd_closed_of_bounds (frameAt word) hodd
  · rw [tGrade_add', tGrade_add', hXt, tGrade_one_zero]
    constructor <;> linarith [ht.1, ht.2]
  · rw [sGrade_add', sGrade_add', sGrade_one_zero]
    constructor <;> linarith [hs.1, hs.2, hX.1, hX.2.1, hX.2.2]

/-- The odd free V site `w` and its south step `u = w + (0,−1)`: `u + X` lies in the closed polygon. -/
theorem u_odd_shift_mem (word : Word) (h : ∃ x ∈ word, x ≠ Digit.three) {w : Site}
    (hw : w ∈ (frameAt word).freeV) (ho : ¬ EvenSite w) :
    (w + (0, -1)) + sec3X word ∈ (frameAt word).closedPolygon := by
  have hX := sGrade_sec3X_bounds h
  have hXt := tGrade_sec3X word
  have hXpar := sec3X_parity h
  have ht := FLatticePaper.ArcRanges.arc_odd_range (frameAt word) hw ho
  have hs := FreeVWindow.freeV_odd_window (frameAt word) hw ho
  obtain ⟨hn0, hnd, hd2, hd3, hT⟩ := (frameAt word).child_facts
  have heven : EvenSite ((w + (0, -1)) + sec3X word) := by
    unfold EvenSite at ho ⊢; simp only [Prod.fst_add, Prod.snd_add]; omega
  apply even_closed_of_bounds (frameAt word) heven
  · rw [tGrade_add', tGrade_add', hXt, tGrade_zero_neg]
    constructor <;> linarith [ht.1, ht.2]
  · rw [sGrade_add', sGrade_add', sGrade_zero_neg]
    constructor <;> linarith [hs.1, hs.2, hX.1, hX.2.1, hX.2.2]

/-- The h0 equality at the prescribed input `u = w + prescribedV 1 w` of a free V white `w ≠ V_end`. -/
theorem h0_u_of_freeV {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hW : StrongCore word)
    (hSE : StrongEstimates (conjWord word)) {w : Site}
    (hw : w ∈ (frameAt word).freeV) (hne : w ≠ (frameAt word).vLast) :
    standardField word (w + (frameAt word).prescribedV 1 w) = FqW word (w + (frameAt word).prescribedV 1 w) := by
  obtain ⟨hN1, hND, hD2, hn0, hd0, hn, hd, heps, hε⟩ := PriceInputs.pdata h
  obtain ⟨hco1, hco2⟩ := (frameAt word).child_odd
  obtain ⟨hpn, hpd⟩ := parent_sums_odd h
  obtain ⟨hcn0, hcnd, hcd2, hcd3, hT⟩ := (frameAt word).child_facts
  have hε' : (frameAt word).eps = (frameAt word).parents.odd.num * (frameAt word).child.den -
      (frameAt word).parents.odd.den * (frameAt word).child.num := by
    rw [heps, hn, hd]; ring
  have hLpos : 0 < (frameAt word).child.den + (frameAt word).child.num := by omega
  by_cases he : EvenSite w
  · rw [prescribedV_even_one (frameAt word) he]
    obtain ⟨hwin1, hwin2⟩ := FreeVWindow.freeV_even_window (frameAt word) hw he
    have hord := FreeVOrdinate.freeV_even_ordinate (frameAt word) hw he
    have hs0 : 0 ≤ ((frameAt word).child.den + (frameAt word).child.num) * w.1 +
        ((frameAt word).child.den - (frameAt word).child.num) * w.2 := by
      have := hwin1; unfold ChildFrame.sGrade at this; linarith
    have hs1 : ((frameAt word).child.den + (frameAt word).child.num) * w.1 +
        ((frameAt word).child.den - (frameAt word).child.num) * w.2 ≤ 2 * (frameAt word).child.num := by
      have := hwin2; unfold ChildFrame.sGrade at this; linarith
    have hpar : (w.1 + w.2) % 2 = 0 := by unfold EvenSite at he; exact he
    obtain ⟨sp0, sp1⟩ := RootClassify.even_sp_range (frameAt word).parents.odd.num (frameAt word).parents.odd.den
      (frameAt word).child.num (frameAt word).child.den (frameAt word).eps w.1 w.2 hε' (by rcases hε with h1 | h1 <;> simp [h1])
      (by omega) (by omega) hpn hpd hLpos (hord.1) (hord.2.2 hne) hs0 hs1 hpar
    have hsp : ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * (w + (1, 0)).1 +
        ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) * (w + (1, 0)).2 =
        (((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * w.1 +
          ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) * w.2) +
            ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) := by
      simp only [Prod.fst_add, Prod.snd_add]; ring
    have hlo : 1 - 2 * (frameAt word).parents.odd.den ≤
        ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * (w + (1, 0)).1 +
          ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) * (w + (1, 0)).2 := by
      rw [hsp]; split_ifs at sp1 <;> linarith
    have hhi : ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * (w + (1, 0)).1 +
          ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) * (w + (1, 0)).2 ≤
        2 * ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) - 1 := by
      rw [hsp]; split_ifs at sp1 <;> linarith
    have hFq := ParentStrip.FqW_eq_h0 h hSE hlo hhi
    have hsG : (frameAt word).sGrade (w + (1, 0)) = (frameAt word).sGrade w + ((frameAt word).child.den + (frameAt word).child.num) := by
      rw [sGrade_add', sGrade_one_zero]
    have hF := hW.packet.strips.2 (w + (1, 0)) (by rw [hsG]; omega) (by rw [hsG]; omega)
    rw [hF, hFq]
  · rw [prescribedV_odd_one (frameAt word) he]
    obtain ⟨hwin1, hwin2⟩ := FreeVWindow.freeV_odd_window (frameAt word) hw he
    have hord := FreeVOrdinate.freeV_odd_ordinate (frameAt word) (CutRowsAll.cut_one_per_ordinate_all (frameAt word)) hw he
    have hs0 : 2 - ((frameAt word).child.den - (frameAt word).child.num) ≤ ((frameAt word).child.den + (frameAt word).child.num) * w.1 +
        ((frameAt word).child.den - (frameAt word).child.num) * w.2 := by
      have := hwin1; unfold ChildFrame.sGrade at this; linarith
    have hs1 : ((frameAt word).child.den + (frameAt word).child.num) * w.1 +
        ((frameAt word).child.den - (frameAt word).child.num) * w.2 ≤ (frameAt word).child.den + (frameAt word).child.num - 2 := by
      have := hwin2; unfold ChildFrame.sGrade at this; linarith
    have hpar : (w.1 + w.2) % 2 = 1 := by unfold EvenSite at he; omega
    obtain ⟨sp0, sp1⟩ := RootClassify.odd_sp_range (frameAt word).parents.odd.num (frameAt word).parents.odd.den
      (frameAt word).child.num (frameAt word).child.den (frameAt word).eps w.1 w.2 hε' (by rcases hε with h1 | h1 <;> simp [h1])
      (by omega) (by omega) hpn hpd hLpos hord.1 hord.2 hs0 hs1 hpar
    have hsp : ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * (w + (0, -1)).1 +
        ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) * (w + (0, -1)).2 =
        ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * w.1 +
          ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) * w.2 - ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) := by
      simp only [Prod.fst_add, Prod.snd_add]; ring
    have hlo : 1 - 2 * (frameAt word).parents.odd.den ≤
        ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * (w + (0, -1)).1 +
          ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) * (w + (0, -1)).2 := by
      rw [hsp]; linarith
    have hhi : ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * (w + (0, -1)).1 +
          ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) * (w + (0, -1)).2 ≤
        2 * ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) - 1 := by
      rw [hsp]; linarith
    have hFq := ParentStrip.FqW_eq_h0 h hSE hlo hhi
    have hsG : (frameAt word).sGrade (w + (0, -1)) = (frameAt word).sGrade w + ((frameAt word).child.num - (frameAt word).child.den) := by
      rw [sGrade_add', sGrade_zero_neg]
    have hF := hW.packet.strips.2 (w + (0, -1)) (by rw [hsG]; omega) (by rw [hsG]; omega)
    rw [hF, hFq]

end FLatticePaper.SheetStars
