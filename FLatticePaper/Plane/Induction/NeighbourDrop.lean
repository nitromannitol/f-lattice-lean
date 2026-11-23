import FLatticePaper.Plane.Induction.EvenWindow

/-! Task 72 (case (b), the neighbour zero and the regular H drop).

With `u = t_p x + iT_p` the H-web value of the root, the neighbour `y` has `t_p y + iT_p = u + step`, where the step is `±N` for an
odd neighbour and `±D` for an even neighbour (the incoming edge). Away from the exceptional value `u = N + D`, both arguments of
the neighbour jump lie in the zero window of their parity, so `a(y + V-translate) = 0`. Translating the star by `−iV_p` shifts
`a` by `−i` at both endpoints, so the root and neighbour zeros give `1 − i = 0 = −i`, a contradiction.

The exceptional value `u = N + D` is the residual for link 3. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper FLatticePaper.W1Seeds

/-- The parity of a site is unchanged by the vertical translate `−i V_p` (its coordinate sum changes by `−2 i n`). -/
theorem evenSite_add_vec_iff (y : Site) (d n i : ℤ) :
    EvenSite (y + (0 * (2 * d) + -i * (n - d), 0 * (2 * n) + -i * (n + d))) ↔ EvenSite y := by
  unfold EvenSite
  simp only [Prod.fst_add, Prod.snd_add]
  have e : (y.1 + (0 * (2 * d) + -i * (n - d))) + (y.2 + (0 * (2 * n) + -i * (n + d))) =
      (y.1 + y.2) + 2 * (-i * n) := by
    ring
  rw [e, Int.add_mul_emod_self_left]

/-- **Odd neighbour, regular.** For `u ≠ N + D` and an odd neighbour (step `±N`), both the neighbour and its partner lie in the
ordinary zero strip. -/
theorem odd_neighbour_strip {N D u step : ℤ} (hN : 1 ≤ N) (hND : N + 1 ≤ D)
    (hw : HRootWeb N D u) (hu : u ≠ N + D) (hs : step = N ∨ step = -N) :
    1 - D ≤ u + step ∧ u + step + 1 ≤ N + 2 * D - 1 := by
  unfold HRootWeb at hw
  omega

/-- **Even neighbour, regular.** For `u ≠ N + D` and an even neighbour (step `±D`), both the neighbour and its partner lie in the
extended window. -/
theorem even_neighbour_window {N D u step : ℤ} (hN : 1 ≤ N) (hND : N + 1 ≤ D)
    (hw : HRootWeb N D u) (hu : u ≠ N + D) (hs : step = D ∨ step = -D) :
    1 - (N + D) ≤ u + step ∧ u + step + 1 ≤ 2 * (N + D) - 1 ∧
      1 - (N + D) ≤ u + step + 1 ∧ u + step + 1 ≤ 2 * (N + D) - 1 := by
  unfold HRootWeb at hw
  omega

/-- **The regular H drop is impossible.** A root in the H web with `u ≠ N + D`, a jump `1` at `x` and `0` at `y` with the neighbour
step of the parity of `y`, cannot occur. -/
theorem H_drop_regular {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpar : SeedFields (conjWord word)) {x y : Site} {i : ℤ}
    (hx : jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x = 1)
    (hy : jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) y = 0)
    (hwx : HRootWeb (frameAt word).parents.odd.num (frameAt word).parents.odd.den
      ((frameAt word).parentTGrade x + i * oddParentPeriod (frameAt word)))
    (hstep : (EvenSite y ∧ ((frameAt word).parentTGrade y - (frameAt word).parentTGrade x = (frameAt word).parents.odd.den ∨
        (frameAt word).parentTGrade y - (frameAt word).parentTGrade x = -(frameAt word).parents.odd.den)) ∨
      (¬ EvenSite y ∧ ((frameAt word).parentTGrade y - (frameAt word).parentTGrade x = (frameAt word).parents.odd.num ∨
        (frameAt word).parentTGrade y - (frameAt word).parentTGrade x = -(frameAt word).parents.odd.num)))
    (hu : (frameAt word).parentTGrade x + i * oddParentPeriod (frameAt word) ≠
      (frameAt word).parents.odd.num + (frameAt word).parents.odd.den) : False := by
  have hN := frameAt_odd_num_pos h
  obtain ⟨-, -, hNle⟩ := (frameAt word).valid.odd_bounds
  have hodd : ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den) % 2 = 1 :=
    (frameAt word).valid.odd_parity
  have hND : (frameAt word).parents.odd.num + 1 ≤ (frameAt word).parents.odd.den := by omega
  have hA : jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) (x +
      (0 * (2 * (frameAt word).parents.odd.den) + -i * ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den),
        0 * (2 * (frameAt word).parents.odd.num) + -i * ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den))) =
      jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x + -i :=
    aVal_translate_UV h hSE 0 (-i) x
  have hB : jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) (y +
      (0 * (2 * (frameAt word).parents.odd.den) + -i * ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den),
        0 * (2 * (frameAt word).parents.odd.num) + -i * ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den))) =
      jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) y + -i :=
    aVal_translate_UV h hSE 0 (-i) y
  -- the root: the H web gives the ordinary zero strip at its translate
  have zA := jumpA_zero_of_strip h hSE _
    (by rw [parentTGrade_translate_V]; exact (web_args_in_strip hN hND hwx).1)
    (by rw [parentTGrade_translate_V]; exact (web_args_in_strip hN hND hwx).2)
  -- the neighbour: its zero from the parity window
  have zB : jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) (y +
      (0 * (2 * (frameAt word).parents.odd.den) + -i * ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den),
        0 * (2 * (frameAt word).parents.odd.num) + -i * ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den))) = 0 := by
    rcases hstep with ⟨hyE, hs⟩ | ⟨hyO, hs⟩
    · have hyE' := (evenSite_add_vec_iff y (frameAt word).parents.odd.den (frameAt word).parents.odd.num i).2 hyE
      have hb := even_neighbour_window hN hND hwx hu hs
      exact jumpA_zero_of_even_window h hSE hpar _ hyE'
        (by rw [parentTGrade_translate_V]; linarith [hb.1])
        (by rw [parentTGrade_translate_V]; linarith [hb.2.1])
        (by rw [parentTGrade_translate_V]; linarith [hb.2.2.1])
        (by rw [parentTGrade_translate_V]; linarith [hb.2.2.2])
    · have hb := odd_neighbour_strip hN hND hwx hu hs
      exact jumpA_zero_of_strip h hSE _
        (by rw [parentTGrade_translate_V]; linarith [hb.1])
        (by rw [parentTGrade_translate_V]; linarith [hb.2])
  rw [hA, hx] at zA
  rw [hB, hy] at zB
  omega

end FLatticePaper.Induction
