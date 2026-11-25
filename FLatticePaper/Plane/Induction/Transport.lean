import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Task w3, step 1(a): the transport index. For the free H point `w = H_idx` of abscissa `idx + 1` (`HEnum.freeH_enumeration`),
the earlier-cut query `Z x` with `x = w − (1 − W)(d_q, n_q)` and `Z(x, y) = (−y, x − 1)` has ordinate
`(Z x).2 = idx − (1 − W) d_q`. In phase `W = 0` this is `j − d_q` (`idx = j`); in phase `W = 1` the reversed index
`idx = d − 1 − j` gives `d − 1 − j` (`(1 − W) = 0`). -/

namespace FLatticePaper.Transport

/-- The transport query `Z x` for `x = w − (1 − W)(d_q, n_q)`. -/
def zQuery (w : ℤ × ℤ) (W dq nq : ℤ) : ℤ × ℤ :=
  let x : ℤ × ℤ := (w.1 - (1 - W) * dq, w.2 - (1 - W) * nq)
  (-x.2, x.1 - 1)

/-- **Step 1(a), the index.** If `w` has abscissa `idx + 1`, the query has ordinate `idx − (1 − W) d_q`. -/
theorem zQuery_snd (w : ℤ × ℤ) (W dq nq idx : ℤ) (hw : w.1 = idx + 1) :
    (zQuery w W dq nq).2 = idx - (1 - W) * dq := by
  unfold zQuery
  simp only
  linarith

/-- The phase-zero index: `w = H_j`, `(Z x).2 = j − d_q`. -/
theorem zQuery_snd_W0 (w : ℤ × ℤ) (dq nq j : ℤ) (hw : w.1 = j + 1) :
    (zQuery w 0 dq nq).2 = j - dq := by
  rw [zQuery_snd w 0 dq nq j hw]
  ring

/-- The phase-one index: `w = H_{d−1−j}` (abscissa `d − j`), `(Z x).2 = d − 1 − j`. -/
theorem zQuery_snd_W1 (w : ℤ × ℤ) (dq nq d j : ℤ) (hw : w.1 = (d - 1 - j) + 1) :
    (zQuery w 1 dq nq).2 = d - 1 - j := by
  rw [zQuery_snd w 1 dq nq (d - 1 - j) hw]
  ring

end FLatticePaper.Transport
