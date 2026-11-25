import FLatticePaper.Plane.Induction.SheetDownJump
import FLatticePaper.Plane.Induction.W0Sheets
import FLatticePaper.Plane.Induction.VArcOffers
import FLatticePaper.Plane.Induction.Q3VStar
import FLatticePaper.Plane.Induction.SheetFacts
import FLatticePaper.Plane.Induction.SheetCharts
import FLatticePaper.Plane.Induction.ParentStepDischarge
import FLatticePaper.Plane.Induction.RawB

/-! Task Q27 (short route): the exceptional corner `V_p + I` at `ε = +1` has `Ψ ≥ 1`.

With `ε = +1` the sheet shift is `0`, the sheet offset is `e = V_q + U_q = (n, 2n + d)` and the sheet difference is
`Ψ z = F (z − e) − F z + a_q·z + c_e`, where `F = quarterTurnField G`, `a_q·z = n z₁ − d z₂` and
`c_e = (d² + 2dn − n² − d − n)/2 + 2`. For the odd parent `(N, D)` and the even sibling `(n, d)` (`N d − n D = 1`):

* the transverse deck law `F (w + V_p) = F w + h₀(w + V_p) − h₀ w` (`W0Sheets.quarterTurnField_add_tipVertex`);
* the harmonic strip at `I = (1, −1)` and `y = I − V_q = (1 + (d − n), −1 − (d + n))` (`quarterTurnField_eq_harmonic_of_sp`);
* the paragraph-5 identity at `y`: `F (y − U_q) − F y = c₀ − P'(Z y)` (`sheetA_sub_uq_eq_cutPrice`);
* the price floor `P'(Z y) − c₀ ≤ −parentFloor y ≤ 0` (`price_floor_bound_of_strong`, `parentFloor_nonneg`).

The harmonic bookkeeping of the corner is the integer identity `K = 1` (`corner_harmonic_identity`), so
`Ψ(V_p + I) = K + (c₀ − P'(Z y)) ≥ 1`. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- `4 h₀(a, b) = a² + 2ab − b² − 2b` on sites of even parity. -/
theorem four_harmonicGrid_pair (a b : ℤ) (hab : (a + b) % 2 = 0) :
    4 * harmonicGrid (a, b) = a ^ 2 + 2 * a * b - b ^ 2 - 2 * b := by
  obtain ⟨t, ht⟩ : ∃ t, a + b = 2 * t := ⟨(a + b) / 2, by omega⟩
  obtain ⟨r, hr⟩ := Int.even_mul_succ_self b
  have hP : a ^ 2 + 2 * a * b - b ^ 2 - 2 * b = 4 * (t ^ 2 - r) := by
    linear_combination (a + b + 2 * t) * ht - 2 * hr
  have hH : harmonicGrid (a, b) = t ^ 2 - r := by
    unfold harmonicGrid
    dsimp only
    rw [hab, sub_zero, hP]
    exact Int.mul_ediv_cancel_left _ (by norm_num)
  rw [hH, hP]

/-- `2 ((T − d − n)/2) = T − d − n` for `T = d² + 2dn − n²`: the numerator is even. -/
theorem two_mul_quad_ediv (d n : ℤ) :
    2 * ((d ^ 2 + 2 * d * n - n ^ 2 - d - n) / 2) = d ^ 2 + 2 * d * n - n ^ 2 - d - n := by
  obtain ⟨a, ha⟩ := Int.even_mul_succ_self (d - 1)
  obtain ⟨b, hb⟩ := Int.even_mul_succ_self n
  have hk : d ^ 2 + 2 * d * n - n ^ 2 - d - n = 2 * (d * n + a - b) := by
    linear_combination ha - hb
  rw [hk, Int.mul_ediv_cancel_left _ (by norm_num)]

/-- The harmonic corner identity: `K = 1` from the determinant `N d − n D = 1` and `d + n` even. -/
theorem corner_harmonic_identity (N D n d ce : ℤ) (hdet : N * d - n * D = 1) (hpar : (n + d) % 2 = 0)
    (hce : 2 * ce = d ^ 2 + 2 * d * n - n ^ 2 - d - n) :
    harmonicGrid (1 + (d - n), -1 - (d + n))
      + harmonicGrid (1 + (d - n) - d + (N - D), -1 - (d + n) - n + (N + D))
      - harmonicGrid (1 + (d - n) - d, -1 - (d + n) - n)
      - harmonicGrid (N - D + 1, N + D - 1)
      + (n * (N - D + 1) - d * (N + D - 1)) + (ce + 2) = 1 := by
  have e1 := four_harmonicGrid_pair (1 + (d - n)) (-1 - (d + n)) (by clear hdet hce; omega)
  have e2 := four_harmonicGrid_pair (1 + (d - n) - d + (N - D)) (-1 - (d + n) - n + (N + D))
    (by clear hdet hce; omega)
  have e3 := four_harmonicGrid_pair (1 + (d - n) - d) (-1 - (d + n) - n) (by clear hdet hce; omega)
  have e4 := four_harmonicGrid_pair (N - D + 1) (N + D - 1) (by clear hdet hce; omega)
  apply mul_left_cancel₀ (show (4 : ℤ) ≠ 0 by norm_num)
  linear_combination e1 + e2 - e3 - e4 + 2 * hce - 4 * hdet

/-- The corner inequality from the named data of the sheet: `Ψ(corner) ≥ 1`. -/
theorem corner_ge_one_of_data (N D n d ce c0 Pp : ℤ) (Fq : Site → ℤ)
    (hdet : N * d - n * D = 1) (hpar : (n + d) % 2 = 0)
    (hce : 2 * ce = d ^ 2 + 2 * d * n - n ^ 2 - d - n)
    (hFI : Fq (1, -1) = harmonicGrid (1, -1))
    (hFy : Fq (1 + (d - n), -1 - (d + n)) = harmonicGrid (1 + (d - n), -1 - (d + n)))
    (hTr : ∀ a b : ℤ, Fq (a + (N - D), b + (N + D)) = Fq (a, b) +
      (harmonicGrid (a + (N - D), b + (N + D)) - harmonicGrid (a, b)))
    (hPI : Fq (1 + (d - n) - d, -1 - (d + n) - n) - Fq (1 + (d - n), -1 - (d + n)) = c0 - Pp)
    (hΔ : 0 ≤ c0 - Pp) :
    1 ≤ Fq ((N - D + 1, N + D - 1) - (n, 2 * n + d)) - Fq (N - D + 1, N + D - 1)
      + (n * (N - D + 1) - d * (N + D - 1)) + (ce + 2) := by
  have hK := corner_harmonic_identity N D n d ce hdet hpar hce
  have hc1 : ((N - D + 1, N + D - 1) - (n, 2 * n + d)) =
      (1 + (d - n) - d + (N - D), -1 - (d + n) - n + (N + D)) := by
    ext <;> simp <;> ring
  have E1 : Fq ((N - D + 1, N + D - 1) - (n, 2 * n + d)) =
      Fq (1 + (d - n) - d, -1 - (d + n) - n) +
        (harmonicGrid (1 + (d - n) - d + (N - D), -1 - (d + n) - n + (N + D)) -
          harmonicGrid (1 + (d - n) - d, -1 - (d + n) - n)) := by
    rw [hc1]
    exact hTr (1 + (d - n) - d) (-1 - (d + n) - n)
  have E2 : Fq (N - D + 1, N + D - 1) = harmonicGrid (N - D + 1, N + D - 1) := by
    have hc2 : (N - D + 1, N + D - 1) = (1 + (N - D), -1 + (N + D)) := by
      ext <;> simp <;> ring
    have hT1 := hTr 1 (-1)
    rw [hc2, hT1, hFI]
    ring
  linarith [E1, E2, hPI, hFy, hK, hΔ]

/-- **The corner of the exceptional V-block (Q27, short route).** At `ε = +1` the sheet difference at `V_p + I` is at
least `1`, hence nonzero: this discharges the named corner input of the H-cut case. -/
theorem sheetDiffW_corner_ge_one {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (heps : (frameAt word).eps = 1) :
    1 ≤ sheetDiffW word ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1,
      (frameAt word).parents.odd.num + (frameAt word).parents.odd.den - 1) := by
  obtain ⟨hcn, hcd⟩ := frameAt_conj_num_den h
  have hStrips := hSE.packet.strips
  have hN1 := frameAt_odd_num_pos h
  obtain ⟨hDpos, hN0, hNle⟩ := (frameAt word).valid.odd_bounds
  obtain ⟨hdPos, hn0, hnle⟩ := (frameAt word).valid.even_bounds
  have hOp : ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den) % 2 = 1 :=
    (frameAt word).valid.odd_parity
  have hpar : ((frameAt word).parents.even.num + (frameAt word).parents.even.den) % 2 = 0 :=
    (frameAt word).valid.even_parity
  have hND : (frameAt word).parents.odd.num + 1 ≤ (frameAt word).parents.odd.den := by omega
  have hdet : (frameAt word).parents.odd.num * (frameAt word).parents.even.den
      - (frameAt word).parents.even.num * (frameAt word).parents.odd.den = 1 := heps
  have hB : 0 < (frameAt word).parents.odd.den ^ 2
      + 2 * (frameAt word).parents.odd.den * (frameAt word).parents.odd.num
      - (frameAt word).parents.odd.num ^ 2 := by
    nlinarith
  -- the sheet difference at `ε = +1`: zero shift, offset `(n, 2n + d)`, constant `c_e`
  have hsh : (frameAt word).sheetShift = 0 := by
    unfold ChildFrame.sheetShift ChildFrame.phaseW
    rw [heps]
    norm_num
  have huq : (frameAt word).uq = ((frameAt word).parents.even.den, (frameAt word).parents.even.num) := by
    unfold ChildFrame.uq
    rw [heps]
    simp
  have hoff : (frameAt word).sheetOffset = ((frameAt word).parents.even.num,
      2 * (frameAt word).parents.even.num + (frameAt word).parents.even.den) := by
    unfold ChildFrame.sheetOffset Fraction.unmodifiedDeck
    rw [heps]
    ext
    · simp
    · simp; ring
  have hconst : (frameAt word).sheetConstant = ((frameAt word).parents.even.den ^ 2
      + 2 * (frameAt word).parents.even.den * (frameAt word).parents.even.num
      - (frameAt word).parents.even.num ^ 2 - (frameAt word).parents.even.den
      - (frameAt word).parents.even.num) / 2 + 2 := by
    unfold ChildFrame.sheetConstant ChildFrame.phaseW Fraction.periodDenominator
    rw [heps]
    norm_num
  unfold sheetDiffW ChildFrame.sheetC ChildFrame.sheetA
  rw [hsh, sub_zero, hoff, hconst]
  unfold ChildFrame.siblingSlope
  dsimp only
  -- the price identity at `y = I − V_q` and the price floor there
  have hyk : (frameAt word).parents.odd.num ≤ (frameAt word).parents.odd.num
      * (1 + ((frameAt word).parents.even.den - (frameAt word).parents.even.num))
      - (frameAt word).parents.odd.den
      * (-1 - ((frameAt word).parents.even.den + (frameAt word).parents.even.num)) := by
    nlinarith [mul_nonneg hN0 (sub_nonneg.2 hnle), mul_nonneg hDpos.le (add_nonneg hdPos.le hn0)]
  have hpf := parentFloor_nonneg (frame := frameAt word)
    (x := (1 + ((frameAt word).parents.even.den - (frameAt word).parents.even.num),
      -1 - ((frameAt word).parents.even.den + (frameAt word).parents.even.num))) hB hyk
  have hpfu := (price_floor_bound_of_strong h hSE (1 + ((frameAt word).parents.even.den
      - (frameAt word).parents.even.num), -1 - ((frameAt word).parents.even.den
      + (frameAt word).parents.even.num))).2
  have key := corner_ge_one_of_data (frameAt word).parents.odd.num (frameAt word).parents.odd.den
    (frameAt word).parents.even.num (frameAt word).parents.even.den
    (((frameAt word).parents.even.den ^ 2 + 2 * (frameAt word).parents.even.den
      * (frameAt word).parents.even.num - (frameAt word).parents.even.num ^ 2
      - (frameAt word).parents.even.den - (frameAt word).parents.even.num) / 2)
    (frameAt (conjWord word)).cutPrice
    ((frameAt (conjWord word)).price (standardField (conjWord word))
      (zTurn (1 + ((frameAt word).parents.even.den - (frameAt word).parents.even.num),
        -1 - ((frameAt word).parents.even.den + (frameAt word).parents.even.num))))
    (quarterTurnField (standardField (conjWord word)))
    hdet hpar (two_mul_quad_ediv _ _)
    (quarterTurnField_eq_harmonic_of_sp hStrips hcn hcd (by dsimp only; linarith) (by dsimp only; linarith))
    (quarterTurnField_eq_harmonic_of_sp hStrips hcn hcd (by dsimp only; linarith) (by dsimp only; linarith))
    (fun a b => W0Sheets.quarterTurnField_add_tipVertex h hSE (a, b))
    (by
      have e := sheetA_sub_uq_eq_cutPrice h hSE (1 + ((frameAt word).parents.even.den
        - (frameAt word).parents.even.num), -1 - ((frameAt word).parents.even.den
        + (frameAt word).parents.even.num))
      unfold ChildFrame.sheetA at e
      simp only [hsh, sub_zero, huq] at e
      exact e)
    (by
      have hpfu' : (frameAt (conjWord word)).price (standardField (conjWord word))
          (zTurn (1 + ((frameAt word).parents.even.den - (frameAt word).parents.even.num),
            -1 - ((frameAt word).parents.even.den + (frameAt word).parents.even.num)))
          - (frameAt (conjWord word)).cutPrice
          ≤ -parentFloor (frameAt word) (1 + ((frameAt word).parents.even.den
              - (frameAt word).parents.even.num), -1 - ((frameAt word).parents.even.den
              + (frameAt word).parents.even.num)) := hpfu
      linarith)
  linarith [key]

end FLatticePaper.Induction
