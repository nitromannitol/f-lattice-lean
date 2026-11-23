import FLatticePaper.Tiles.SiteBase

/-! Task 53, item 2 (scope): the parent pairs of the non-base words are proper and oriented by the phase.

The source (Part III §3(B), the ordinary propagation note) states the six-source inclusions and the cover conclusion for proper
parity-compatible determinant-one parents `P, Q` (`0 < num < den` for both). The induction only uses them at the parents of
non-base words. This module proves that those parents are proper and that their determinant is `2 · phase − 1`, so the word-indexed
hypotheses of `SiteInduction.SourceHyps` are instances of the source's statement with the phase as the orientation.

* `det_parentsAt`: `(parentsAt w).odd.det (parentsAt w).even = 2 · phase w − 1` (a letter `1` flips both, `2` and `3` keep both).
* `parents_bounds`: for every word, `0 ≤ odd.num`, `1 ≤ odd.den − odd.num`, `1 ≤ even.num`, `0 ≤ even.den − even.num`.
* `odd_num_pos`, `even_den_gap_pos`: a letter other than `3` (resp. `2`) makes the odd (resp. even) parent non-degenerate.
* `proper_of_not_base`: for a non-base word both parents are proper. -/

namespace FLatticePaper.Tiles.SiteScope

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.Standard
open FLatticePaper.Tiles.SiteInduction

theorem phase_snoc (v : Word) (d : Digit) :
    phase (v ++ [d]) = if d = Digit.one then (phase v + 1) % 2 else phase v := by
  cases d <;> simp [phase, List.count_append]

theorem det_step_one (P : Parents) :
    (P.step .one).odd.det (P.step .one).even = -(P.odd.det P.even) := by
  simp only [Parents.step, Parents.current, Parents.combine, Fraction.det]
  ring

theorem det_step_two (P : Parents) :
    (P.step .two).odd.det (P.step .two).even = P.odd.det P.even := by
  simp only [Parents.step, Parents.current, Parents.combine, Fraction.det]
  ring

theorem det_step_three (P : Parents) :
    (P.step .three).odd.det (P.step .three).even = P.odd.det P.even := by
  simp only [Parents.step, Parents.current, Parents.combine, Fraction.det]
  ring

/-- The determinant of the parent pair of a word is `2 · phase − 1`: it is `−1` at the empty word and flips with each letter `1`. -/
theorem det_parentsAt (w : Word) : (parentsAt w).odd.det (parentsAt w).even = 2 * (phase w : ℤ) - 1 := by
  induction w using List.reverseRecOn with
  | nil => decide
  | append_singleton v d ih =>
    rw [parentsAt_append_singleton]
    cases d with
    | one =>
      have hlt : phase v < 2 := by unfold phase; omega
      rw [det_step_one, ih, phase_snoc]
      simp only [if_true]
      omega
    | two =>
      rw [det_step_two, ih, phase_snoc]
      simp
    | three =>
      rw [det_step_three, ih, phase_snoc]
      simp

/-- The invariant of the parent recursion: the odd parent has `0 ≤ num` and `1 ≤ den − num`; the even parent has `1 ≤ num` and
`0 ≤ den − num`. -/
theorem parents_bounds (w : Word) :
    1 ≤ (parentsAt w).odd.den - (parentsAt w).odd.num ∧ 0 ≤ (parentsAt w).odd.num ∧
      1 ≤ (parentsAt w).even.num ∧ 0 ≤ (parentsAt w).even.den - (parentsAt w).even.num := by
  induction w using List.reverseRecOn with
  | nil => decide
  | append_singleton v d ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    rw [parentsAt_append_singleton]
    cases d with
    | one =>
      simp only [Parents.step, Parents.current, Parents.combine]
      exact ⟨by omega, by omega, by omega, by omega⟩
    | two =>
      simp only [Parents.step, Parents.current, Parents.combine]
      exact ⟨by omega, by omega, by omega, by omega⟩
    | three =>
      simp only [Parents.step, Parents.current, Parents.combine]
      exact ⟨by omega, by omega, by omega, by omega⟩

/-- A letter other than `3` makes the odd parent's numerator positive. -/
theorem odd_num_pos (w : Word) (h : ∃ x ∈ w, x ≠ Digit.three) : 1 ≤ (parentsAt w).odd.num := by
  induction w using List.reverseRecOn with
  | nil => obtain ⟨x, hx, -⟩ := h; simp at hx
  | append_singleton v d ih =>
    rw [parentsAt_append_singleton]
    cases d with
    | one =>
      obtain ⟨b1, b2, b3, b4⟩ := parents_bounds v
      simp only [Parents.step, Parents.current, Parents.combine]
      omega
    | two =>
      obtain ⟨b1, b2, b3, b4⟩ := parents_bounds v
      simp only [Parents.step, Parents.current, Parents.combine]
      omega
    | three =>
      have hv : ∃ x ∈ v, x ≠ Digit.three := by
        obtain ⟨x, hx, hne⟩ := h
        rcases List.mem_append.mp hx with hx | hx
        · exact ⟨x, hx, hne⟩
        · rw [List.mem_singleton] at hx
          exact absurd hx hne
      have := ih hv
      simp only [Parents.step]
      exact this

/-- A letter other than `2` makes the even parent's gap `den − num` positive. -/
theorem even_gap_pos (w : Word) (h : ∃ x ∈ w, x ≠ Digit.two) : 1 ≤ (parentsAt w).even.den - (parentsAt w).even.num := by
  induction w using List.reverseRecOn with
  | nil => obtain ⟨x, hx, -⟩ := h; simp at hx
  | append_singleton v d ih =>
    rw [parentsAt_append_singleton]
    cases d with
    | one =>
      obtain ⟨b1, b2, b3, b4⟩ := parents_bounds v
      simp only [Parents.step, Parents.current, Parents.combine]
      omega
    | three =>
      obtain ⟨b1, b2, b3, b4⟩ := parents_bounds v
      simp only [Parents.step, Parents.current, Parents.combine]
      omega
    | two =>
      have hv : ∃ x ∈ v, x ≠ Digit.two := by
        obtain ⟨x, hx, hne⟩ := h
        rcases List.mem_append.mp hx with hx | hx
        · exact ⟨x, hx, hne⟩
        · rw [List.mem_singleton] at hx
          exact absurd hx hne
      have := ih hv
      simp only [Parents.step]
      exact this

/-- For a non-base word, both parent fractions are proper: `0 < num < den`. -/
theorem proper_of_not_base (w : Word) (hw : ¬ IsBase w) :
    0 < (parentsAt w).odd.num ∧ (parentsAt w).odd.num < (parentsAt w).odd.den ∧
      0 < (parentsAt w).even.num ∧ (parentsAt w).even.num < (parentsAt w).even.den := by
  obtain ⟨hx3, hx2⟩ : (∃ x ∈ w, x ≠ Digit.three) ∧ (∃ x ∈ w, x ≠ Digit.two) := by
    refine ⟨?_, ?_⟩
    · by_contra hc
      apply hw
      right; left
      intro d hd
      by_contra hne
      exact hc ⟨d, hd, hne⟩
    · by_contra hc
      apply hw
      right; right
      intro d hd
      by_contra hne
      exact hc ⟨d, hd, hne⟩
  have hb := parents_bounds w
  have h1 := odd_num_pos w hx3
  have h2 := even_gap_pos w hx2
  exact ⟨by omega, by omega, by omega, by omega⟩

end FLatticePaper.Tiles.SiteScope
