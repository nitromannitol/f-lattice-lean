import FLatticePaper.Farey.Recursion

/-! The numerators along the Farey recursion (task 38, item 1).

With `O` and `E` the numerators of the odd and even parent, the digit `one` sets `(O, E) ↦ (O + E, 2O + E)`, the digit
`two` sets `(O, E) ↦ (O + E, E)`, and the digit `three` sets `(O, E) ↦ (O, 2O + E)`. The walk from the root `(0, 1)`
keeps `E ≥ 1` and `O ≥ 0`, never decreases `O`, and a digit `one` or `two` makes `O ≥ 1`. The current even register,
which is the child, has numerator `2O + E`, so a word with a digit `one` or `two` has child numerator at least `3`. -/

namespace FLatticePaper.Farey

/-- Along a walk the odd numerator stays nonnegative and never decreases, the even numerator stays at least `1`, and a
walk that uses a digit other than `three` ends with odd numerator at least `1`. -/
theorem walk_numerators (w : Word) (p : Parents) (h0 : 0 ≤ p.odd.num) (h1 : 1 ≤ p.even.num) :
    0 ≤ (p.walk w).odd.num ∧ 1 ≤ (p.walk w).even.num ∧ p.odd.num ≤ (p.walk w).odd.num ∧
      ((∃ x ∈ w, x ≠ Digit.three) → 1 ≤ (p.walk w).odd.num) := by
  induction w generalizing p with
  | nil =>
    refine ⟨h0, h1, le_refl _, fun h => ?_⟩
    obtain ⟨x, hx, _⟩ := h
    simp at hx
  | cons digit tail ih =>
    rw [Parents.walk_cons]
    have hstep : 0 ≤ (p.step digit).odd.num ∧ 1 ≤ (p.step digit).even.num ∧
        p.odd.num ≤ (p.step digit).odd.num ∧ (digit ≠ Digit.three → 1 ≤ (p.step digit).odd.num) := by
      cases digit
      · simp only [Parents.step, Parents.current, Parents.combine]
        refine ⟨by omega, by omega, by omega, fun _ => by omega⟩
      · simp only [Parents.step, Parents.current, Parents.combine]
        refine ⟨by omega, by omega, by omega, fun _ => by omega⟩
      · simp only [Parents.step, Parents.current, Parents.combine]
        refine ⟨by omega, by omega, by omega, fun h => absurd rfl h⟩
    obtain ⟨a, b, c, d⟩ := ih (p.step digit) hstep.1 hstep.2.1
    refine ⟨a, b, le_trans hstep.2.2.1 c, ?_⟩
    rintro ⟨x, hx, hne⟩
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact le_trans (hstep.2.2.2 hne) c
    · exact d ⟨x, hx', hne⟩

/-- A word with a digit other than `three` has, at its current even register, numerator `2O + E ≥ 3`. -/
theorem current_even_num_ge_three (w : Word) (h : ∃ x ∈ w, x ≠ Digit.three) :
    3 ≤ ((parentsAt w).current .even).num := by
  have hroot0 : (0 : ℤ) ≤ (root : Parents).odd.num := by
    show (0 : ℤ) ≤ 0
    exact le_refl _
  have hroot1 : (1 : ℤ) ≤ (root : Parents).even.num := by
    show (1 : ℤ) ≤ 1
    exact le_refl _
  obtain ⟨-, hE, -, hO⟩ := walk_numerators w root hroot0 hroot1
  have hO' := hO h
  show 3 ≤ 2 * (parentsAt w).odd.num + 1 * (parentsAt w).even.num
  unfold parentsAt
  omega

/-- The registers `den − num` of the parents: once `2a + b ≥ 4` (with `a, b ≥ 0`), every digit keeps it, since each digit maps
`(a, b)` to `(a + b, 2a + b)`, `(a + b, b)` or `(a, 2a + b)`. -/
theorem diff_preserved (w : Word) (p : Parents) (ha : 0 ≤ p.odd.den - p.odd.num) (hb : 0 ≤ p.even.den - p.even.num)
    (h4 : 4 ≤ 2 * (p.odd.den - p.odd.num) + (p.even.den - p.even.num)) :
    4 ≤ 2 * ((p.walk w).odd.den - (p.walk w).odd.num) + ((p.walk w).even.den - (p.walk w).even.num) := by
  induction w generalizing p with
  | nil => simpa [Parents.walk] using h4
  | cons digit tail ih =>
    rw [Parents.walk_cons]
    have hstep : 0 ≤ (p.step digit).odd.den - (p.step digit).odd.num ∧
        0 ≤ (p.step digit).even.den - (p.step digit).even.num ∧
        4 ≤ 2 * ((p.step digit).odd.den - (p.step digit).odd.num) +
          ((p.step digit).even.den - (p.step digit).even.num) := by
      cases digit
      · simp only [Parents.step, Parents.current, Parents.combine]
        refine ⟨by omega, by omega, by omega⟩
      · simp only [Parents.step, Parents.current, Parents.combine]
        refine ⟨by omega, by omega, by omega⟩
      · simp only [Parents.step, Parents.current, Parents.combine]
        refine ⟨by omega, by omega, by omega⟩
    exact ih _ hstep.1 hstep.2.1 hstep.2.2

/-- A word with a digit other than `two` has, at its current even register, `den − num ≥ 4` (with `2a + b` the registers' sum). -/
theorem walk_diff_ge (w : Word) (p : Parents) (ha : 1 ≤ p.odd.den - p.odd.num) (hb : 0 ≤ p.even.den - p.even.num)
    (h : ∃ x ∈ w, x ≠ Digit.two) :
    4 ≤ 2 * ((p.walk w).odd.den - (p.walk w).odd.num) + ((p.walk w).even.den - (p.walk w).even.num) := by
  induction w generalizing p with
  | nil =>
    obtain ⟨x, hx, -⟩ := h
    simp at hx
  | cons digit tail ih =>
    rw [Parents.walk_cons]
    cases digit
    · -- digit one: the register after one already has 2a + b ≥ 4
      have hstep : 4 ≤ 2 * ((p.step Digit.one).odd.den - (p.step Digit.one).odd.num) +
          ((p.step Digit.one).even.den - (p.step Digit.one).even.num) := by
        simp only [Parents.step, Parents.current, Parents.combine]
        omega
      exact diff_preserved tail _ (by simp only [Parents.step, Parents.current, Parents.combine]; omega)
        (by simp only [Parents.step, Parents.current, Parents.combine]; omega) hstep
    · -- digit two: the head is not used; the tail carries the witness
      have hw : ∃ x ∈ tail, x ≠ Digit.two := by
        obtain ⟨x, hx, hne⟩ := h
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact absurd rfl hne
        · exact ⟨x, hx', hne⟩
      exact ih _ (by simp only [Parents.step, Parents.current, Parents.combine]; omega)
        (by simp only [Parents.step, Parents.current, Parents.combine]; omega) hw
    · -- digit three
      have hstep : 4 ≤ 2 * ((p.step Digit.three).odd.den - (p.step Digit.three).odd.num) +
          ((p.step Digit.three).even.den - (p.step Digit.three).even.num) := by
        simp only [Parents.step, Parents.current, Parents.combine]
        omega
      exact diff_preserved tail _ (by simp only [Parents.step, Parents.current, Parents.combine]; omega)
        (by simp only [Parents.step, Parents.current, Parents.combine]; omega) hstep

/-- The child of a word with a digit other than `two` has `den − num ≥ 4`. -/
theorem current_even_diff_ge_four (w : Word) (h : ∃ x ∈ w, x ≠ Digit.two) :
    4 ≤ ((parentsAt w).current .even).den - ((parentsAt w).current .even).num := by
  have hroot0 : (1 : ℤ) ≤ (root : Parents).odd.den - (root : Parents).odd.num := by
    show (1 : ℤ) ≤ 1 - 0
    omega
  have hroot1 : (0 : ℤ) ≤ (root : Parents).even.den - (root : Parents).even.num := by
    show (0 : ℤ) ≤ 1 - 1
    omega
  have hw := walk_diff_ge w root hroot0 hroot1 h
  unfold parentsAt
  simp only [Parents.current, Parents.combine]
  omega

end FLatticePaper.Farey
