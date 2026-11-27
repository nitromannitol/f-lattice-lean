import FLatticePaper.Plane.Induction.FreeGrades
import FLatticePaper.Plane.Induction.ParentWindow
import FLatticePaper.Plane.Induction.FaceWitness
import FLatticePaper.Plane.Induction.ConjFreeRoot
import FLatticePaper.Plane.Induction.VArcOffers
import FLatticePaper.Plane.Induction.Packet
import FLatticePaper.Plane.Induction.ChildNumerator
import FLatticePaper.Plane.Induction.MatchedPolicy

/-! # The root class of a bottom centre (`hClassB`)

For a strict interior centre `c` of a proper word with a bottom witness, and the conjugate root `z = zTurn (c − sheetShift)` free
(not `Nonfree`), the root lies in one of the two classes: `z − (0,−1) ∈ span` (even centre) or `z − (0,0) ∈ span` (odd centre).

The proof chains: the child window (`RootWindow.bottom_window`), the parent window (`ParentWindow`, with the shift
`sheetShift = (1 − W) U_q` of parent `u`-grade `(1 − W) ε`), the conjugate grades of `zTurn` (`ConjFreeRoot`), the free closure in
grades (`FreeGrades.nonfree_to_grades`), the integrality core (`RootFree.free_closure_B`), and the span test by divisibility
(`PeriodDeck.mem_span_iff_dvd`). The word hypothesis `hw` (not a pure word) is an explicit input. -/

namespace FLatticePaper.HClassB

open FLatticePaper FLatticePaper.Induction FLatticePaper.Farey FLatticePaper.FreeGrades FLatticePaper.RootFree

/-- The span test: a site with `sGrade = 0` and `tGrade = −2Tk` (for the conjugate child with `num = D − N`, `den = D + N`) lies in
the span. The numerators of the deck are `sGrade` and `−tGrade`, and the determinant is `2T`. -/
theorem span_of_grades (G : ChildFrame) (N D T : ℤ) (hnum : G.child.num = D - N) (hden : G.child.den = D + N)
    (hT : T = D * D + 2 * D * N - N * N) (hTpos : 0 < T) (site : Site) (k : ℤ)
    (hs : G.sGrade site = 0) (ht : G.tGrade site = -(2 * T * k)) :
    site ∈ G.child.modifiedDeck.span := by
  have hk := G.child_modifiedDeck_kernel
  have htr := G.child_modifiedDeck_transverse
  have hdet : G.child.modifiedDeck.det = 2 * T := by
    unfold PeriodDeck.det
    rw [hk, htr, hnum, hden, hT]
    ring
  have hkn : PeriodDeck.kernelNumerator G.child.modifiedDeck site = G.sGrade site := by
    unfold PeriodDeck.kernelNumerator ChildFrame.sGrade
    rw [htr, hnum, hden]
    simp only
    ring
  have htn : PeriodDeck.transverseNumerator G.child.modifiedDeck site = 2 * T * k := by
    unfold PeriodDeck.transverseNumerator
    rw [hk]
    have : ChildFrame.tGrade G site = G.child.num * site.1 - G.child.den * site.2 := rfl
    rw [ChildFrame.tGrade] at ht
    simp only
    rw [hnum, hden] at ht ⊢
    linarith [ht]
  rw [PeriodDeck.mem_span_iff_dvd G.child.modifiedDeck (by rw [hdet]; positivity) site]
  constructor
  · rw [hkn, hs]
    exact dvd_zero _
  · rw [htn, hdet]
    exact ⟨k, rfl⟩

theorem tGrade_sub' (G : ChildFrame) (p q : Site) : G.tGrade (p - q) = G.tGrade p - G.tGrade q := by
  unfold ChildFrame.tGrade; simp only [Prod.fst_sub, Prod.snd_sub]; ring

theorem sGrade_sub' (G : ChildFrame) (p q : Site) : G.sGrade (p - q) = G.sGrade p - G.sGrade q := by
  unfold ChildFrame.sGrade; simp only [Prod.fst_sub, Prod.snd_sub]; ring

/-- **The root class of a bottom centre.** -/
theorem classB (word : Word) (hw : ∃ x ∈ word, x ≠ Digit.three) (c : Site)
    (hS : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hB : FLatticePaper.FaceWitness.BottomWit (frameAt word) c)
    (hnf : ¬ Nonfree (frameAt (conjWord word)) (zTurn (c - (frameAt word).sheetShift))) :
    zTurn (c - (frameAt word).sheetShift) - (0, -1) ∈ (frameAt (conjWord word)).child.modifiedDeck.span ∨
      zTurn (c - (frameAt word).sheetShift) - (0, 0) ∈ (frameAt (conjWord word)).child.modifiedDeck.span := by
  -- the conjugate child and its grades
  have hc : (frameAt (conjWord word)).child = (frameAt word).parents.odd.rotate := frameAt_conj_child hw
  obtain ⟨hcn, hcd⟩ := conj_child_num_den hc
  obtain ⟨T, hTdef⟩ : ∃ T, T = (frameAt word).parents.odd.den * (frameAt word).parents.odd.den
      + 2 * (frameAt word).parents.odd.den * (frameAt word).parents.odd.num
      - (frameAt word).parents.odd.num * (frameAt word).parents.odd.num := ⟨_, rfl⟩
  have hper : (frameAt (conjWord word)).child.periodDenominator = 2 * T := by
    rw [conj_periodDenominator hw, hTdef]
    unfold oddParentPeriod
    ring
  -- the parent: N = odd.num, D = odd.den
  obtain ⟨N, hNdef⟩ : ∃ N, N = (frameAt word).parents.odd.num := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D, D = (frameAt word).parents.odd.den := ⟨_, rfl⟩
  rw [← hNdef, ← hDdef] at hcn hcd
  rw [← hDdef] at hTdef
  rw [← hNdef] at hTdef
  have hodd : (N + D) % 2 = 1 := by
    rw [hNdef, hDdef]; exact (parentsAt_valid word).odd_parity
  have hcop : IsCoprime N D := by
    rw [hNdef, hDdef]; exact (parentsAt_valid word).odd_reduced
  have hbd : 0 < D ∧ 0 ≤ N ∧ N ≤ D := by
    rw [hNdef, hDdef]; exact (parentsAt_valid word).odd_bounds
  have hND : N < D := by omega
  -- the child: odd, n ≥ 3, n < d
  have hn3 : 3 ≤ (frameAt word).child.num := child_num_ge_three hw
  have hcf := (frameAt word).child_facts
  have hco := (frameAt word).child_odd
  -- the parity of the eps relation
  have hε : N * (frameAt word).child.den - D * (frameAt word).child.num = (frameAt word).eps := by
    rw [hNdef, hDdef]; exact ((frameAt word).eps_eq).symm
  have hεu := (frameAt word).eps_unit
  have hev : ((frameAt word).parents.even.num + (frameAt word).parents.even.den) % 2 = 0 :=
    (parentsAt_valid word).even_parity
  have hTpos : 0 < T := by
    rw [hTdef]; nlinarith
  have hN0 : 0 < N := by
    by_contra hN'
    have hN00 : N = 0 := by omega
    rw [hN00] at hε
    rcases hεu with h | h
    · rw [h] at hε; nlinarith
    · rw [h] at hε; nlinarith
  -- the child window of the centre, in the parent window form
  obtain ⟨v0, hv1, hv2, hv0⟩ := hB
  obtain ⟨-, -, hspv⟩ := hv0
  have hsp : (FLatticePaper.W1.w1t (frameAt word).child.num (frameAt word).child.den v0 % 2 = 0 ∧
        2 ≤ FLatticePaper.W1.w1t (frameAt word).child.num (frameAt word).child.den v0) ∨
      (FLatticePaper.W1.w1t (frameAt word).child.num (frameAt word).child.den v0 % 2 = 1 ∧
        (frameAt word).child.num ≤ FLatticePaper.W1.w1t (frameAt word).child.num (frameAt word).child.den v0) := by
    unfold ChildFrame.hSpectrum at hspv
    rcases hspv with ⟨a, b, -⟩ | ⟨a, b, -⟩
    · exact Or.inl ⟨a, b⟩
    · exact Or.inr ⟨a, b⟩
  have hwc := FLatticePaper.RootWindow.bottom_window (frameAt word).child.num (frameAt word).child.den
    hco.1 hco.2 hn3 hcf.2.1 c v0 hS hv1 hv2 hsp
  -- the parent window of the centre, for both signs of eps
  have hεN : N * (frameAt word).child.den - D * (frameAt word).child.num = (frameAt word).eps := hε
  have hwin_c : ((c.1 + c.2) % 2 = 0 → (frameAt word).eps = 1 → 1 - (D + N) ≤ N * c.1 - D * c.2 ∧ N * c.1 - D * c.2 ≤ 0) ∧
      ((c.1 + c.2) % 2 = 0 → (frameAt word).eps = -1 → -(D + N) ≤ N * c.1 - D * c.2 ∧ N * c.1 - D * c.2 ≤ -1) ∧
      ((c.1 + c.2) % 2 = 1 → (frameAt word).eps = 1 → 1 - D ≤ N * c.1 - D * c.2 ∧ N * c.1 - D * c.2 ≤ N) ∧
      ((c.1 + c.2) % 2 = 1 → (frameAt word).eps = -1 → -D ≤ N * c.1 - D * c.2 ∧ N * c.1 - D * c.2 ≤ N - 1) := by
    have hwE := hwc.1
    have hwO := hwc.2
    have hT' : FLatticePaper.W1.w1T (frameAt word).child.num (frameAt word).child.den
        = (frameAt word).child.den * (frameAt word).child.den + 2 * (frameAt word).child.den * (frameAt word).child.num
          - (frameAt word).child.num * (frameAt word).child.num := by
      unfold FLatticePaper.W1.w1T; ring
    refine ⟨fun he h1 => ?_, fun he h1 => ?_, fun he h1 => ?_, fun he h1 => ?_⟩
    · obtain ⟨a1, a2, a3, a4⟩ := hwE he
      have hsw := (ParentWindow.parent_window_even (frameAt word).child.num (frameAt word).child.den N D c.1 c.2
        (frameAt word).eps hεN (Or.inl h1) hn3 hcf.2.1 hN0 hND a1 a2 a3 (by rw [hT'] at a4; unfold FLatticePaper.W1.w1s at a4; linarith))
      exact hsw.1 h1
    · obtain ⟨a1, a2, a3, a4⟩ := hwE he
      have hsw := (ParentWindow.parent_window_even (frameAt word).child.num (frameAt word).child.den N D c.1 c.2
        (frameAt word).eps hεN (Or.inr h1) hn3 hcf.2.1 hN0 hND a1 a2 a3 (by rw [hT'] at a4; unfold FLatticePaper.W1.w1s at a4; linarith))
      exact hsw.2 h1
    · obtain ⟨a1, a2, a3, a4⟩ := hwO he
      have hsw := (ParentWindow.parent_window_odd (frameAt word).child.num (frameAt word).child.den N D c.1 c.2
        (frameAt word).eps hεN (Or.inl h1) hn3 hcf.2.1 hN0 hND a1 a2 a3
        (by rw [hT'] at a4; unfold FLatticePaper.W1.w1s at a4; linarith))
      exact hsw.1 h1
    · obtain ⟨a1, a2, a3, a4⟩ := hwO he
      have hsw := (ParentWindow.parent_window_odd (frameAt word).child.num (frameAt word).child.den N D c.1 c.2
        (frameAt word).eps hεN (Or.inr h1) hn3 hcf.2.1 hN0 hND a1 a2 a3
        (by rw [hT'] at a4; unfold FLatticePaper.W1.w1s at a4; linarith))
      exact hsw.2 h1
  -- the final assembly, given a parent point x = c − sheetShift with its window and parity
  have final_assembly : ∀ (x' : Site), x' = c - (frameAt word).sheetShift →
      ((x'.1 + x'.2) % 2 = 0 → 1 - (D + N) ≤ N * x'.1 - D * x'.2 ∧ N * x'.1 - D * x'.2 ≤ 0) ∧
        ((x'.1 + x'.2) % 2 = 1 → 1 - D ≤ N * x'.1 - D * x'.2 ∧ N * x'.1 - D * x'.2 ≤ N) →
      (x'.1 + x'.2) % 2 = (c.1 + c.2) % 2 →
      zTurn (c - (frameAt word).sheetShift) - (0, -1) ∈ (frameAt (conjWord word)).child.modifiedDeck.span ∨
        zTurn (c - (frameAt word).sheetShift) - (0, 0) ∈ (frameAt (conjWord word)).child.modifiedDeck.span := by
    intro x' hx' hwin_x hxpar
    rw [← hx']
    have hzt : (frameAt (conjWord word)).tGrade (zTurn x') = D + N - ((D + N) * x'.1 + (D - N) * x'.2) := by
      rw [conj_tGrade_zTurn hw x']
      unfold ChildFrame.parentSGrade
      rw [← hDdef, ← hNdef]
    have hzs : (frameAt (conjWord word)).sGrade (zTurn x') = 2 * (N * x'.1 - D * x'.2 - N) := by
      rw [conj_sGrade_zTurn hw x']
      unfold ChildFrame.parentTGrade
      rw [← hNdef, ← hDdef]
    have hn' : (frameAt (conjWord word)).child.num % 2 = 1 := by rw [hcn]; omega
    have hd' : (frameAt (conjWord word)).child.den % 2 = 1 := by rw [hcd]; omega
    obtain ⟨i, j, hfree⟩ := nonfree_to_grades (frameAt (conjWord word)) N D T hcn hcd hper hTdef hn' hd'
      (zTurn x') (by rw [hx']; exact hnf)
    rw [hzt, hzs] at hfree
    have hres := free_closure_B N D T x'.1 x'.2 hN0 hND hodd hcop hTdef hwin_x ⟨i, j, hfree⟩
    have e1 : (frameAt (conjWord word)).sGrade (0, -1) =
        -((frameAt (conjWord word)).child.den - (frameAt (conjWord word)).child.num) := by
      unfold ChildFrame.sGrade; ring
    have e2 : (frameAt (conjWord word)).tGrade (0, -1) = (frameAt (conjWord word)).child.den := by
      unfold ChildFrame.tGrade; ring
    have e0s : (frameAt (conjWord word)).sGrade (0, 0) = 0 := by unfold ChildFrame.sGrade; ring
    have e0t : (frameAt (conjWord word)).tGrade (0, 0) = 0 := by unfold ChildFrame.tGrade; ring
    by_cases hcp : (c.1 + c.2) % 2 = 0
    · left
      have hxp : (x'.1 + x'.2) % 2 = 0 := by rw [hxpar]; exact hcp
      obtain ⟨hu0, k, hk⟩ := hres.1 hxp
      apply span_of_grades (frameAt (conjWord word)) N D T hcn hcd hTdef hTpos _ k
      · rw [sGrade_sub', hzs, e1, hcn, hcd]; linarith
      · rw [tGrade_sub', hzt, e2, hcd]; linarith
    · right
      have hxp : (x'.1 + x'.2) % 2 = 1 := by rw [hxpar]; omega
      obtain ⟨hu, k, hk⟩ := hres.2 hxp
      apply span_of_grades (frameAt (conjWord word)) N D T hcn hcd hTdef hTpos _ k
      · rw [sGrade_sub', hzs, e0s]; linarith
      · rw [tGrade_sub', hzt, e0t]; linarith
  -- the sheet shift and the parent point x = c − sheetShift
  rcases hεu with heu | heu
  · -- ε = 1: the sheet shift is zero, x = c
    have hsh1 : (frameAt word).sheetShift.1 = 0 := by
      unfold ChildFrame.sheetShift ChildFrame.phaseW
      rw [heu]
      norm_num
    have hsh2 : (frameAt word).sheetShift.2 = 0 := by
      unfold ChildFrame.sheetShift ChildFrame.phaseW
      rw [heu]
      norm_num
    have hsh : (frameAt word).sheetShift = (0, 0) := Prod.ext hsh1 hsh2
    have hx : c - (frameAt word).sheetShift = c := by rw [hsh]; simp
    exact final_assembly c hx.symm (by
      refine ⟨fun he => ?_, fun he => ?_⟩
      · exact hwin_c.1 he heu
      · exact hwin_c.2.2.1 he heu) (by simp)
  · -- ε = −1: the sheet shift is the even kernel (den, num), with N · den − D · num = −1
    have hsh1 : (frameAt word).sheetShift.1 = (frameAt word).parents.even.den := by
      unfold ChildFrame.sheetShift ChildFrame.phaseW
      rw [heu]
      simp [Fraction.unmodifiedDeck]
    have hsh2 : (frameAt word).sheetShift.2 = (frameAt word).parents.even.num := by
      unfold ChildFrame.sheetShift ChildFrame.phaseW
      rw [heu]
      simp [Fraction.unmodifiedDeck]
    have hdet : (frameAt word).eps = N * (frameAt word).parents.even.den - (frameAt word).parents.even.num * D := by
      unfold ChildFrame.eps Fraction.det
      rw [← hNdef, ← hDdef]
    have hkey : N * (frameAt word).sheetShift.1 - D * (frameAt word).sheetShift.2 = -1 := by
      rw [hsh1, hsh2]
      linarith [hdet, heu]
    set x := c - (frameAt word).sheetShift with hxdef
    have hx1 : x.1 = c.1 - (frameAt word).sheetShift.1 := by rw [hxdef]; simp
    have hx2 : x.2 = c.2 - (frameAt word).sheetShift.2 := by rw [hxdef]; simp
    have hxpar : (x.1 + x.2) % 2 = (c.1 + c.2) % 2 := by
      rw [hx1, hx2, hsh1, hsh2]
      omega
    have hu_eq : N * x.1 - D * x.2 = N * c.1 - D * c.2 + 1 := by
      rw [hx1, hx2]
      linarith [hkey]
    have hwin_x : ((x.1 + x.2) % 2 = 0 → 1 - (D + N) ≤ N * x.1 - D * x.2 ∧ N * x.1 - D * x.2 ≤ 0) ∧
        ((x.1 + x.2) % 2 = 1 → 1 - D ≤ N * x.1 - D * x.2 ∧ N * x.1 - D * x.2 ≤ N) := by
      refine ⟨fun he => ?_, fun he => ?_⟩
      · have he' : (c.1 + c.2) % 2 = 0 := by rw [← hxpar]; exact he
        obtain ⟨a1, a2⟩ := hwin_c.2.1 he' heu
        rw [hu_eq]
        constructor <;> linarith
      · have he' : (c.1 + c.2) % 2 = 1 := by rw [← hxpar]; exact he
        obtain ⟨a1, a2⟩ := hwin_c.2.2.2 he' heu
        rw [hu_eq]
        constructor <;> linarith
    exact final_assembly x hxdef hwin_x hxpar

end FLatticePaper.HClassB
