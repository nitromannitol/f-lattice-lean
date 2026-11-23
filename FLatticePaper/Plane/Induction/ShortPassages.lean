import FLatticePaper.Plane.Induction.DeckForced

/-! Task 72 (FIXED_FREE_GAME_AUDIT §3 and §4): the interior sites of the short H and V passages are nonfree, for all parameters.

Grades: `t = n x − d y`, `s = L x + c y` (`L = d + n`, `c = d − n`), `T = d² + 2dn − n²`; the deck vectors `K = (d, n)` and
`V = (n − d, L)` (kernel and transverse) act by `s ↦ s + T` and `t ↦ t − T` respectively.

* `nonfree_of_avoid`: a site is nonfree if the H spectrum avoids all `t − jT` and the V spectrum all `s + iT`.
* window lemmas: the windows of the middles give that avoidance (`avoid_*`).
* `nonfree_V_even_left`, `nonfree_V_even_neg`: the two even V middles, whose `i = 0` translates fail the bottom/left or `E` tests.
* the four route theorems: the middles of the H-E-N, H-N-E-S, V-N-W and V-W-N-E routes, from the root hypotheses
  (`FIXED_FREE` §3, §4; checked on the actual routes by `scripts/passage_root_hypotheses.py`). -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

namespace ShortPassages

theorem period_facts (frame : ChildFrame) :
    frame.child.periodDenominator = frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2 ∧
      0 < frame.child.num ∧ frame.child.num + 2 ≤ frame.child.den ∧ 3 ≤ frame.child.den := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := frame.child_facts
  exact ⟨h5, h1, by omega, h4⟩

theorem T_mod_two (frame : ChildFrame) : frame.child.periodDenominator % 2 = 0 := by
  obtain ⟨hn, hd⟩ := FLatticePaper.W1Exit.child_parity frame
  rw [(period_facts frame).1]
  exact FLatticePaper.W1Exit.parity_T _ _ hn hd

theorem T_ge (frame : ChildFrame) :
    3 * (frame.child.den + frame.child.num) ≤ frame.child.periodDenominator := by
  obtain ⟨hT, hn, hnd, hd3⟩ := period_facts frame
  rw [hT]
  nlinarith

theorem tGrade_add_combine (frame : ChildFrame) (u : Site) (i j : ℤ) :
    frame.tGrade (u + frame.child.modifiedDeck.combine i j) =
      frame.tGrade u - j * frame.child.periodDenominator := by
  rw [(period_facts frame).1]
  unfold ChildFrame.tGrade PeriodDeck.combine
  simp only [ChildFrame.child_modifiedDeck_kernel, ChildFrame.child_modifiedDeck_transverse, Prod.fst_add,
    Prod.snd_add]
  ring

theorem sGrade_add_combine (frame : ChildFrame) (u : Site) (i j : ℤ) :
    frame.sGrade (u + frame.child.modifiedDeck.combine i j) =
      frame.sGrade u + i * frame.child.periodDenominator := by
  rw [(period_facts frame).1]
  unfold ChildFrame.sGrade PeriodDeck.combine
  simp only [ChildFrame.child_modifiedDeck_kernel, ChildFrame.child_modifiedDeck_transverse, Prod.fst_add,
    Prod.snd_add]
  ring

/-- **Spectral avoidance implies nonfree.** -/
theorem nonfree_of_avoid (frame : ChildFrame) (u : Site)
    (hH : ∀ j : ℤ, ¬ frame.hSpectrum (frame.tGrade u - j * frame.child.periodDenominator))
    (hV : ∀ i : ℤ, ¬ frame.vSpectrum (frame.sGrade u + i * frame.child.periodDenominator)) :
    Nonfree frame u := by
  intro v hv hmem
  obtain ⟨i, j, rfl⟩ := hv
  rcases hmem with h | h
  · obtain ⟨-, -, hs⟩ := h
    rw [tGrade_add_combine] at hs
    exact hH j hs
  · obtain ⟨-, -, hs⟩ := h
    rw [sGrade_add_combine] at hs
    exact hV i hs

theorem tGrade_parity' (frame : ChildFrame) (z : Site) (hz : ¬ EvenSite z) : frame.tGrade z % 2 = 1 := by
  rw [tGrade_parity]
  unfold EvenSite at hz
  omega

/-! ### H windows: the translates `t − jT` avoid the H spectrum. -/

theorem avoid_H_odd_high (frame : ChildFrame) (u : Site) (hu : ¬ EvenSite u)
    (h1 : frame.child.den < frame.tGrade u) (h2 : frame.tGrade u < frame.child.periodDenominator + frame.child.num) :
    ∀ j : ℤ, ¬ frame.hSpectrum (frame.tGrade u - j * frame.child.periodDenominator) := by
  intro j hsp
  have hpar := tGrade_parity' frame u hu
  have hjT : (j * frame.child.periodDenominator) % 2 = 0 := by
    rw [Int.mul_emod, T_mod_two]
    simp
  have hx : (frame.tGrade u - j * frame.child.periodDenominator) % 2 = 1 := by
    rw [Int.sub_emod, hpar, hjT]
    norm_num
  obtain ⟨hT, hn, hnd, hd3⟩ := period_facts frame
  unfold ChildFrame.hSpectrum at hsp
  rcases hsp with ⟨he, -, -⟩ | ⟨-, hl, hu'⟩
  · rw [hx] at he
    norm_num at he
  · rcases lt_trichotomy j 0 with hj | hj | hj
    · have : j * frame.child.periodDenominator ≤ -frame.child.periodDenominator := by nlinarith
      nlinarith
    · subst hj
      simp at hu'
      linarith
    · have : frame.child.periodDenominator ≤ j * frame.child.periodDenominator := by nlinarith
      nlinarith

theorem avoid_H_odd_low (frame : ChildFrame) (u : Site) (hu : ¬ EvenSite u)
    (h1 : frame.child.den - frame.child.periodDenominator < frame.tGrade u) (h2 : frame.tGrade u < frame.child.num) :
    ∀ j : ℤ, ¬ frame.hSpectrum (frame.tGrade u - j * frame.child.periodDenominator) := by
  intro j hsp
  have hpar := tGrade_parity' frame u hu
  have hjT : (j * frame.child.periodDenominator) % 2 = 0 := by
    rw [Int.mul_emod, T_mod_two]
    simp
  have hx : (frame.tGrade u - j * frame.child.periodDenominator) % 2 = 1 := by
    rw [Int.sub_emod, hpar, hjT]
    norm_num
  obtain ⟨hT, hn, hnd, hd3⟩ := period_facts frame
  unfold ChildFrame.hSpectrum at hsp
  rcases hsp with ⟨he, -, -⟩ | ⟨-, hl, hu'⟩
  · rw [hx] at he
    norm_num at he
  · rcases lt_trichotomy j 0 with hj | hj | hj
    · have : j * frame.child.periodDenominator ≤ -frame.child.periodDenominator := by nlinarith
      nlinarith
    · subst hj
      simp at hl
      linarith
    · have : frame.child.periodDenominator ≤ j * frame.child.periodDenominator := by nlinarith
      nlinarith

theorem avoid_H_even_high (frame : ChildFrame) (u : Site) (hu : EvenSite u)
    (h1 : frame.child.num + frame.child.den - 2 < frame.tGrade u)
    (h2 : frame.tGrade u < frame.child.periodDenominator + 2) :
    ∀ j : ℤ, ¬ frame.hSpectrum (frame.tGrade u - j * frame.child.periodDenominator) := by
  intro j hsp
  have hpar : frame.tGrade u % 2 = 0 := by
    rw [tGrade_parity]
    exact hu
  have hjT : (j * frame.child.periodDenominator) % 2 = 0 := by
    rw [Int.mul_emod, T_mod_two]
    simp
  have hx : (frame.tGrade u - j * frame.child.periodDenominator) % 2 = 0 := by
    rw [Int.sub_emod, hpar, hjT]
    norm_num
  obtain ⟨hT, hn, hnd, hd3⟩ := period_facts frame
  unfold ChildFrame.hSpectrum at hsp
  rcases hsp with ⟨-, hl, hu'⟩ | ⟨he, -, -⟩
  · rcases lt_trichotomy j 0 with hj | hj | hj
    · have : j * frame.child.periodDenominator ≤ -frame.child.periodDenominator := by nlinarith
      nlinarith
    · subst hj
      simp at hu'
      linarith
    · have : frame.child.periodDenominator ≤ j * frame.child.periodDenominator := by nlinarith
      nlinarith
  · rw [hx] at he
    norm_num at he

theorem avoid_H_even_low (frame : ChildFrame) (u : Site) (hu : EvenSite u)
    (h1 : frame.child.num + frame.child.den - 2 - frame.child.periodDenominator < frame.tGrade u)
    (h2 : frame.tGrade u < 2) :
    ∀ j : ℤ, ¬ frame.hSpectrum (frame.tGrade u - j * frame.child.periodDenominator) := by
  intro j hsp
  have hpar : frame.tGrade u % 2 = 0 := by
    rw [tGrade_parity]
    exact hu
  have hjT : (j * frame.child.periodDenominator) % 2 = 0 := by
    rw [Int.mul_emod, T_mod_two]
    simp
  have hx : (frame.tGrade u - j * frame.child.periodDenominator) % 2 = 0 := by
    rw [Int.sub_emod, hpar, hjT]
    norm_num
  obtain ⟨hT, hn, hnd, hd3⟩ := period_facts frame
  unfold ChildFrame.hSpectrum at hsp
  rcases hsp with ⟨-, hl, hu'⟩ | ⟨he, -, -⟩
  · rcases lt_trichotomy j 0 with hj | hj | hj
    · have : j * frame.child.periodDenominator ≤ -frame.child.periodDenominator := by nlinarith
      nlinarith
    · subst hj
      simp at hl
      linarith
    · have : frame.child.periodDenominator ≤ j * frame.child.periodDenominator := by nlinarith
      nlinarith
  · rw [hx] at he
    norm_num at he

/-! ### V windows: the translates `s + iT` avoid the V spectrum. -/

theorem avoid_V_high (frame : ChildFrame) (u : Site)
    (h1 : frame.child.num + frame.child.den - 2 < frame.sGrade u)
    (h2 : frame.sGrade u < frame.child.periodDenominator + 2 - (frame.child.den - frame.child.num)) :
    ∀ i : ℤ, ¬ frame.vSpectrum (frame.sGrade u + i * frame.child.periodDenominator) := by
  intro i hsp
  obtain ⟨hT, hn, hnd, hd3⟩ := period_facts frame
  have hTL := T_ge frame
  unfold ChildFrame.vSpectrum at hsp
  obtain ⟨-, hA | hB⟩ := hsp
  · rcases lt_trichotomy i 0 with hi | hi | hi
    · have : i * frame.child.periodDenominator ≤ -frame.child.periodDenominator := by nlinarith
      nlinarith
    · subst hi
      simp at hA
      nlinarith
    · have : frame.child.periodDenominator ≤ i * frame.child.periodDenominator := by nlinarith
      nlinarith
  · rcases lt_trichotomy i 0 with hi | hi | hi
    · have : i * frame.child.periodDenominator ≤ -frame.child.periodDenominator := by nlinarith
      nlinarith
    · subst hi
      simp at hB
      nlinarith
    · have : frame.child.periodDenominator ≤ i * frame.child.periodDenominator := by nlinarith
      nlinarith

theorem avoid_V_low (frame : ChildFrame) (u : Site)
    (h1 : frame.child.num + frame.child.den - 2 - frame.child.periodDenominator < frame.sGrade u)
    (h2 : frame.sGrade u < 2 - (frame.child.den - frame.child.num)) :
    ∀ i : ℤ, ¬ frame.vSpectrum (frame.sGrade u + i * frame.child.periodDenominator) := by
  intro i hsp
  obtain ⟨hT, hn, hnd, hd3⟩ := period_facts frame
  have hTL := T_ge frame
  unfold ChildFrame.vSpectrum at hsp
  obtain ⟨-, hA | hB⟩ := hsp
  · rcases lt_trichotomy i 0 with hi | hi | hi
    · have : i * frame.child.periodDenominator ≤ -frame.child.periodDenominator := by nlinarith
      nlinarith
    · subst hi
      simp at hA
      nlinarith
    · have : frame.child.periodDenominator ≤ i * frame.child.periodDenominator := by nlinarith
      nlinarith
  · rcases lt_trichotomy i 0 with hi | hi | hi
    · have : i * frame.child.periodDenominator ≤ -frame.child.periodDenominator := by nlinarith
      nlinarith
    · subst hi
      simp at hB
      nlinarith
    · have : frame.child.periodDenominator ≤ i * frame.child.periodDenominator := by nlinarith
      nlinarith

/-! ### Translates of a site by a unit step (for the route middles). -/

theorem tGrade_left (frame : ChildFrame) (z : Site) :
    frame.tGrade (z.1 - 1, z.2) = frame.tGrade z - frame.child.num := by
  unfold ChildFrame.tGrade
  ring

theorem sGrade_left (frame : ChildFrame) (z : Site) :
    frame.sGrade (z.1 - 1, z.2) = frame.sGrade z - (frame.child.den + frame.child.num) := by
  unfold ChildFrame.sGrade
  ring

theorem tGrade_add_pair (frame : ChildFrame) (z : Site) (a b : ℤ) :
    frame.tGrade (z + (a, b)) = frame.tGrade z + frame.child.num * a - frame.child.den * b := by
  unfold ChildFrame.tGrade
  simp only [Prod.fst_add, Prod.snd_add]
  ring

theorem sGrade_add_pair (frame : ChildFrame) (z : Site) (a b : ℤ) :
    frame.sGrade (z + (a, b)) =
      frame.sGrade z + (frame.child.den + frame.child.num) * a + (frame.child.den - frame.child.num) * b := by
  unfold ChildFrame.sGrade
  simp only [Prod.fst_add, Prod.snd_add]
  ring

theorem evenSite_add_pair_iff (z : Site) (a b : ℤ) (h : (a + b) % 2 = 0) :
    EvenSite (z + (a, b)) ↔ EvenSite z := by
  unfold EvenSite
  simp only [Prod.fst_add, Prod.snd_add]
  omega

theorem evenSite_add_span_iff (frame : ChildFrame) (u : Site) {v : Site}
    (hv : v ∈ frame.child.modifiedDeck.span) : EvenSite (u + v) ↔ EvenSite u := by
  have hv' := evenSite_of_span frame hv
  unfold EvenSite at hv' ⊢
  simp only [Prod.fst_add, Prod.snd_add]
  omega

/-! ### The two even V middles. -/

/-- The even V middle with `s ∈ [2n + 2, 2d − 2]`: its left neighbour is in `E`, so its `i = 0` translates are not free. -/
theorem nonfree_V_even_left (frame : ChildFrame) (u : Site) (hu : EvenSite u)
    (ht1 : frame.child.num + frame.child.den - 1 - frame.child.periodDenominator < frame.tGrade u)
    (ht2 : frame.tGrade u < 0)
    (hs1 : 2 * frame.child.num + 2 ≤ frame.sGrade u) (hs2 : frame.sGrade u ≤ 2 * frame.child.den - 2) :
    Nonfree frame u := by
  obtain ⟨hT, hn, hnd, hd3⟩ := period_facts frame
  have hTL := T_ge frame
  have hH := avoid_H_even_low frame u hu (by linarith) (by linarith)
  have hleft : (u.1 - 1, u.2) ∈ frame.closedPolygon := by
    rw [mem_closedPolygon_iff]
    have hodd : ¬ EvenSite (u.1 - 1, u.2) := by
      unfold EvenSite at hu ⊢
      simp only
      omega
    rw [if_neg hodd, tGrade_left, sGrade_left]
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  intro v hv hmem
  obtain ⟨i, j, rfl⟩ := hv
  rcases hmem with h | h
  · obtain ⟨-, -, hs⟩ := h
    rw [tGrade_add_combine] at hs
    exact hH j hs
  · obtain ⟨hE, hnl, hs⟩ := h
    by_cases hi : i = 0
    · subst hi
      have hpar : EvenSite (u + frame.child.modifiedDeck.combine 0 j) :=
        ((evenSite_add_span_iff frame u ⟨0, j, rfl⟩).mpr hu)
      rw [mem_closedPolygon_iff, if_pos hpar, tGrade_add_combine, sGrade_add_combine] at hE
      obtain ⟨e1, e2, -, -⟩ := hE
      have hj0 : j = 0 := by
        rcases lt_trichotomy j 0 with hj | hj | hj
        · have : j * frame.child.periodDenominator ≤ -frame.child.periodDenominator := by nlinarith
          nlinarith
        · exact hj
        · have : frame.child.periodDenominator ≤ j * frame.child.periodDenominator := by nlinarith
          nlinarith
      subst hj0
      have e : u + frame.child.modifiedDeck.combine 0 0 = u := by
        simp [PeriodDeck.combine]
      rw [e] at hnl
      exact hnl hleft
    · rw [sGrade_add_combine] at hs
      unfold ChildFrame.vSpectrum at hs
      obtain ⟨-, hA | hB⟩ := hs
      · rcases lt_trichotomy i 0 with hi' | hi' | hi'
        · have : i * frame.child.periodDenominator ≤ -frame.child.periodDenominator := by nlinarith
          nlinarith
        · exact absurd hi' hi
        · have : frame.child.periodDenominator ≤ i * frame.child.periodDenominator := by nlinarith
          nlinarith
      · rcases lt_trichotomy i 0 with hi' | hi' | hi'
        · have : i * frame.child.periodDenominator ≤ -frame.child.periodDenominator := by nlinarith
          nlinarith
        · exact absurd hi' hi
        · have : frame.child.periodDenominator ≤ i * frame.child.periodDenominator := by nlinarith
          nlinarith

/-- The even V middle with `L − 2 − T < s < 0`: its `i = 0` translates lie outside `E` (their `s` is negative). -/
theorem nonfree_V_even_neg (frame : ChildFrame) (u : Site) (hu : EvenSite u)
    (ht1 : frame.child.num + frame.child.den - 2 - frame.child.periodDenominator < frame.tGrade u)
    (ht2 : frame.tGrade u < 2)
    (hs1 : frame.child.num + frame.child.den - 2 - frame.child.periodDenominator < frame.sGrade u)
    (hs2 : frame.sGrade u < 0) :
    Nonfree frame u := by
  obtain ⟨hT, hn, hnd, hd3⟩ := period_facts frame
  have hTL := T_ge frame
  have hH := avoid_H_even_low frame u hu ht1 ht2
  intro v hv hmem
  obtain ⟨i, j, rfl⟩ := hv
  rcases hmem with h | h
  · obtain ⟨-, -, hs⟩ := h
    rw [tGrade_add_combine] at hs
    exact hH j hs
  · obtain ⟨hE, -, hs⟩ := h
    by_cases hi : i = 0
    · subst hi
      have hpar : EvenSite (u + frame.child.modifiedDeck.combine 0 j) :=
        (evenSite_add_span_iff frame u ⟨0, j, rfl⟩).mpr hu
      rw [mem_closedPolygon_iff, if_pos hpar, sGrade_add_combine] at hE
      obtain ⟨-, -, e3, -⟩ := hE
      simp at e3
      linarith
    · rw [sGrade_add_combine] at hs
      unfold ChildFrame.vSpectrum at hs
      obtain ⟨-, hA | hB⟩ := hs
      · rcases lt_trichotomy i 0 with hi' | hi' | hi'
        · have : i * frame.child.periodDenominator ≤ -frame.child.periodDenominator := by nlinarith
          nlinarith
        · exact absurd hi' hi
        · have : frame.child.periodDenominator ≤ i * frame.child.periodDenominator := by nlinarith
          nlinarith
      · rcases lt_trichotomy i 0 with hi' | hi' | hi'
        · have : i * frame.child.periodDenominator ≤ -frame.child.periodDenominator := by nlinarith
          nlinarith
        · exact absurd hi' hi
        · have : frame.child.periodDenominator ≤ i * frame.child.periodDenominator := by nlinarith
          nlinarith

/-! ### The four route theorems (the middles of the short passages). -/

/-- **H E-N (FIXED_FREE §3).** The odd middle `z + (1, 0)` of the E-N route from an even H root `z`, with the next endpoint
`z + (1, 1)` in the even H spectrum (`c + 2 ≤ t(z)`) and the root box `s(z) < T + 2 − 2d`, is nonfree. -/
theorem H_EN_middle_nonfree (frame : ChildFrame) (z : Site) (hz : EvenSite z)
    (hzE : z ∈ frame.closedPolygon) (hT : frame.child.den - frame.child.num + 2 ≤ frame.tGrade z)
    (hS : frame.sGrade z < frame.child.periodDenominator + 2 - 2 * frame.child.den) :
    Nonfree frame (z + (1, 0)) := by
  obtain ⟨hT0, hn, hnd, hd3⟩ := period_facts frame
  have hTL := T_ge frame
  rw [mem_closedPolygon_iff, if_pos hz] at hzE
  obtain ⟨z1, z2, z3, z4⟩ := hzE
  have hodd : ¬ EvenSite (z + (1, 0)) := by
    unfold EvenSite at hz ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  apply nonfree_of_avoid
  · apply avoid_H_odd_high frame _ hodd
    · rw [tGrade_add_pair]
      linarith
    · rw [tGrade_add_pair]
      linarith
  · apply avoid_V_high frame
    · rw [sGrade_add_pair]
      linarith
    · rw [sGrade_add_pair]
      linarith

/-- **H N-E-S, first middle (FIXED_FREE §3).** The even middle `z + (0, 1)` of the N-E-S route from an odd H root `z` with
`n + 2 ≤ t(z) ≤ d − 2` and `2n − 2 < s(z) < T + 2 − 3d + n` is nonfree. -/
theorem H_NES_middle1_nonfree (frame : ChildFrame) (z : Site) (hz : ¬ EvenSite z)
    (hT1 : frame.child.num + 2 ≤ frame.tGrade z) (hT2 : frame.tGrade z ≤ frame.child.den - 2)
    (hS1 : 2 * frame.child.num - 2 < frame.sGrade z)
    (hS2 : frame.sGrade z < frame.child.periodDenominator + 2 - 3 * frame.child.den + frame.child.num) :
    Nonfree frame (z + (0, 1)) := by
  obtain ⟨hT0, hn, hnd, hd3⟩ := period_facts frame
  have hTL := T_ge frame
  have hev : EvenSite (z + (0, 1)) := by
    unfold EvenSite at hz ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  apply nonfree_of_avoid
  · apply avoid_H_even_low frame _ hev
    · rw [tGrade_add_pair]
      linarith
    · rw [tGrade_add_pair]
      linarith
  · apply avoid_V_high frame
    · rw [sGrade_add_pair]
      linarith
    · rw [sGrade_add_pair]
      linarith

/-- **H N-E-S, second middle (FIXED_FREE §3).** The odd middle `z + (1, 1)` of the N-E-S route from the same odd H root. -/
theorem H_NES_middle2_nonfree (frame : ChildFrame) (z : Site) (hz : ¬ EvenSite z)
    (hT1 : frame.child.num + 2 ≤ frame.tGrade z) (hT2 : frame.tGrade z ≤ frame.child.den - 2)
    (hS1 : 2 * frame.child.num - 2 < frame.sGrade z)
    (hS2 : frame.sGrade z < frame.child.periodDenominator + 2 - 3 * frame.child.den + frame.child.num) :
    Nonfree frame (z + (1, 1)) := by
  obtain ⟨hT0, hn, hnd, hd3⟩ := period_facts frame
  have hTL := T_ge frame
  have hodd : ¬ EvenSite (z + (1, 1)) := by
    unfold EvenSite at hz ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  apply nonfree_of_avoid
  · apply avoid_H_odd_low frame _ hodd
    · rw [tGrade_add_pair]
      linarith
    · rw [tGrade_add_pair]
      linarith
  · apply avoid_V_high frame
    · rw [sGrade_add_pair]
      linarith
    · rw [sGrade_add_pair]
      linarith

/-- **V N-W (FIXED_FREE §4).** The even middle `z + (0, 1)` of the N-W route from an odd V root `z` with
`2n + 2 − c ≤ s(z) ≤ L − 2` and `L − 1 − T + d < t(z) < d` is nonfree. -/
theorem V_NW_middle_nonfree (frame : ChildFrame) (z : Site) (hz : ¬ EvenSite z)
    (hS1 : 2 * frame.child.num + 2 - (frame.child.den - frame.child.num) ≤ frame.sGrade z)
    (hS2 : frame.sGrade z ≤ frame.child.den + frame.child.num - 2)
    (ht1 : frame.child.num + frame.child.den - 1 - frame.child.periodDenominator + frame.child.den < frame.tGrade z)
    (ht2 : frame.tGrade z < frame.child.den) :
    Nonfree frame (z + (0, 1)) := by
  obtain ⟨hT0, hn, hnd, hd3⟩ := period_facts frame
  have hev : EvenSite (z + (0, 1)) := by
    unfold EvenSite at hz ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  apply nonfree_V_even_left frame _ hev
  · rw [tGrade_add_pair]
    linarith
  · rw [tGrade_add_pair]
    linarith
  · rw [sGrade_add_pair]
    linarith
  · rw [sGrade_add_pair]
    linarith

/-- **V W-N-E, first middle (FIXED_FREE §4).** The odd middle `z + (−1, 0)` of the W-N-E route from an even V root `z` with
`2 ≤ s(z) ≤ 2n − 2` and `2L − 1 − T < t(z) < n` is nonfree. -/
theorem V_WNE_middle0_nonfree (frame : ChildFrame) (z : Site) (hz : EvenSite z)
    (hS1 : 2 ≤ frame.sGrade z) (hS2 : frame.sGrade z ≤ 2 * frame.child.num - 2)
    (ht1 : 2 * (frame.child.num + frame.child.den) - 1 - frame.child.periodDenominator < frame.tGrade z)
    (ht2 : frame.tGrade z < frame.child.num) :
    Nonfree frame (z + (-1, 0)) := by
  obtain ⟨hT0, hn, hnd, hd3⟩ := period_facts frame
  have hTL := T_ge frame
  have hodd : ¬ EvenSite (z + (-1, 0)) := by
    unfold EvenSite at hz ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  apply nonfree_of_avoid
  · apply avoid_H_odd_low frame _ hodd
    · rw [tGrade_add_pair]
      linarith
    · rw [tGrade_add_pair]
      linarith
  · apply avoid_V_low frame
    · rw [sGrade_add_pair]
      linarith
    · rw [sGrade_add_pair]
      linarith

/-- **V W-N-E, second middle (FIXED_FREE §4).** The even middle `z + (−1, 1)` of the W-N-E route from the same even V root. -/
theorem V_WNE_middle1_nonfree (frame : ChildFrame) (z : Site) (hz : EvenSite z)
    (hS1 : 2 ≤ frame.sGrade z) (hS2 : frame.sGrade z ≤ 2 * frame.child.num - 2)
    (ht1 : 2 * (frame.child.num + frame.child.den) - 1 - frame.child.periodDenominator < frame.tGrade z)
    (ht2 : frame.tGrade z < frame.child.num) :
    Nonfree frame (z + (-1, 1)) := by
  obtain ⟨hT0, hn, hnd, hd3⟩ := period_facts frame
  have hTL := T_ge frame
  have hev : EvenSite (z + (-1, 1)) := by
    unfold EvenSite at hz ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  apply nonfree_V_even_neg frame _ hev
  · rw [tGrade_add_pair]
    linarith
  · rw [tGrade_add_pair]
    linarith
  · rw [sGrade_add_pair]
    linarith
  · rw [sGrade_add_pair]
    linarith

end ShortPassages


end FLatticePaper.Induction
