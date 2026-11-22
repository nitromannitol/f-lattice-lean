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

end FLatticePaper.Farey
