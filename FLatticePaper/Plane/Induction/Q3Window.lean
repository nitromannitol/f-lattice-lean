import Mathlib.Tactic.Linarith

/-! Task 59, step 2 (paragraph 4): the window bounds of the shifted edge, as integer statements.

PROVISIONAL readings (from the notation of Q2.md, paragraph 3; checked numerically before stating):
* transverse grade = `t` (tGrade), longitudinal grade = `s`;
* supported interval at parity `χ`: `[a_χ − T, b_χ]` with `(a_e, b_e) = (2, L−2)`, `(a_o, b_o) = (n, d)`;
* the two ends: the centre `z` and its input `u`; the shifted edge `(z + ησ, u + ησ)` with `t(· + ησ) = t(·) − 2η`;
* an upper exit at parity `χ`: the shifted `t` exceeds `b_χ` (η = −1 for an even end, and for an odd end);
* a lower exit: the shifted `t` is below `a_χ − T` (η = +1).

Numerically (words ≤ 4, `scripts/q3_window_check_inE.py`), with both ends in `E`: all 464 upper exits and all 464 lower
exits satisfy the bounds below; the shifted grades lie in the ordinary zero strip `[1−d, n+2d−1]` (upper) and its transverse
translate (lower). With `u` outside `E` the bounds fail, so `u ∈ E` is a hypothesis (the paper's "membership in E").

Each lemma takes the exiting end's grade `tz` and the other end's grade `tu`, with `tu = tz ± (input change)`. -/

namespace FLatticePaper.Induction.Q3Window

/-- Upper exit of an even end (η = −1): both original grades in `[−1, L−2]`, and both shifted grades in the zero strip. -/
theorem upper_exit_even_end (tz tu n d T : ℤ) (hn : 3 ≤ n) (hnd : n + 2 ≤ d)
    (hz : 2 - T ≤ tz ∧ tz ≤ d + n - 2) (hu : n - T ≤ tu ∧ tu ≤ d)
    (hin : tu = tz + n ∨ tu = tz - n) (hexit : d + n - 2 < tz + 2) :
    (-1 ≤ tz ∧ tz ≤ d + n - 2 ∧ -1 ≤ tu ∧ tu ≤ d + n - 2) ∧
      (1 - d ≤ tz + 2 ∧ tz + 2 ≤ n + 2 * d - 1 ∧ 1 - d ≤ tu + 2 ∧ tu + 2 ≤ n + 2 * d - 1) := by
  omega

/-- Upper exit of an odd end (η = −1): the same conclusions with the odd end as the exiting site. -/
theorem upper_exit_odd_end (tz tu n d T : ℤ) (hn : 3 ≤ n) (hnd : n + 2 ≤ d)
    (hz : n - T ≤ tz ∧ tz ≤ d) (hu : 2 - T ≤ tu ∧ tu ≤ d + n - 2)
    (hin : tu = tz + d ∨ tu = tz - d) (hexit : d < tz + 2) :
    (-1 ≤ tz ∧ tz ≤ d + n - 2 ∧ -1 ≤ tu ∧ tu ≤ d + n - 2) ∧
      (1 - d ≤ tz + 2 ∧ tz + 2 ≤ n + 2 * d - 1 ∧ 1 - d ≤ tu + 2 ∧ tu + 2 ≤ n + 2 * d - 1) := by
  omega

/-- Lower exit of an even end (η = +1): both `t + T` in `[2, n+1+d]`; the shifted `t + T` in the zero strip. -/
theorem lower_exit_even_end (tz tu n d T : ℤ) (hn : 3 ≤ n) (hnd : n + 2 ≤ d)
    (hz : 2 - T ≤ tz ∧ tz ≤ d + n - 2) (hu : n - T ≤ tu ∧ tu ≤ d)
    (hin : tu = tz + n ∨ tu = tz - n) (hexit : tz - 2 < 2 - T) :
    (2 ≤ tz + T ∧ tz + T ≤ n + 1 + d ∧ 2 ≤ tu + T ∧ tu + T ≤ n + 1 + d) ∧
      (1 - d ≤ tz - 2 + T ∧ tz - 2 + T ≤ n + 2 * d - 1 ∧ 1 - d ≤ tu - 2 + T ∧ tu - 2 + T ≤ n + 2 * d - 1) := by
  omega

/-- Lower exit of an odd end (η = +1): the same conclusions with the odd end as the exiting site. -/
theorem lower_exit_odd_end (tz tu n d T : ℤ) (hn : 3 ≤ n) (hnd : n + 2 ≤ d)
    (hz : n - T ≤ tz ∧ tz ≤ d) (hu : 2 - T ≤ tu ∧ tu ≤ d + n - 2)
    (hin : tu = tz + d ∨ tu = tz - d) (hexit : tz - 2 < n - T) :
    (2 ≤ tz + T ∧ tz + T ≤ n + 1 + d ∧ 2 ≤ tu + T ∧ tu + T ≤ n + 1 + d) ∧
      (1 - d ≤ tz - 2 + T ∧ tz - 2 + T ≤ n + 2 * d - 1 ∧ 1 - d ≤ tu - 2 + T ∧ tu - 2 + T ≤ n + 2 * d - 1) := by
  omega

end FLatticePaper.Induction.Q3Window
