import FLatticePaper.Plane.Induction.SheetCharts
import FLatticePaper.Plane.Induction.W1Step
import FLatticePaper.Plane.Induction.I3Permits
import FLatticePaper.Plane.Induction.Q3VStar
import FLatticePaper.Plane.Induction.W1MSheet

/-! # The calibration of `Ψ` on the child H arc (task 114, step (b)): `Ψ(H₀) = 0` and `Ψ(H₁) = 1` in phase W0

The H-source note (`H_SOURCE_ANCESTRAL_CLOSURE.md` §3) calibrates `Ψ = C − A` directly. In Lean, `sheetPsi word = sheetC (FqW word) − sheetA (FqW word)`
with `FqW word = quarterTurnField G`, `G = standardField (conjWord word)`, and the sheet pieces of the child frame are the note's `lv`, `e`, `c_e`
(`sheetShift`, `sheetOffset`, `sheetConstant`; `siblingSlope = a_q·x`). In phase W0 (`eps = −1`): `lv = U_q = (d_q, n_q)`,
`e = V_q − U_q`, `c_e = (T_q − L_q)/2`.

Everything reduces to three facts: `quarterTurnField G w = G(Z w) + h₀(w)` with `Z(x,y) = (−y, x−1)`; `h₀(Z w) = −h₀(w)`
(`harmonicGrid_Z`); and the conjugate's strips, `G = 0` on its zero band and `G = h₀` on its harmonic band, evaluated at the `Z`-images of
`z − V_q` and `z − U_q`, using the conjugate's child `(D−N, D+N)` and `D n_q − N d_q = 1` (from `eps = −1`). So `A(H₀) = 0`,
`C(H₀) = h₀(z − V_q) + n_q + c_e = 0`, hence `Ψ(H₀) = 0`; with `z = H₁ = (2,0)`, `Ψ(H₁) = 1`. -/

namespace FLatticePaper.PsiCalibration

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1Step FLatticePaper.W1MSheet

/-- `h₀(Z w) = −h₀(w)` for the quarter-turn offset `Z(x, y) = (−y, x − 1)`. -/
theorem harmonicGrid_Z (w : Site) : harmonicGrid (i3Z w) = -harmonicGrid w := by
  have h1 := harmonicGrid_exact (i3Z w)
  have h2 := harmonicGrid_exact w
  have e : (i3Z w).1 ^ 2 + 2 * (i3Z w).1 * (i3Z w).2 - (i3Z w).2 ^ 2 - 2 * (i3Z w).2 - ((i3Z w).1 + (i3Z w).2) % 2
      + (w.1 ^ 2 + 2 * w.1 * w.2 - w.2 ^ 2 - 2 * w.2 - (w.1 + w.2) % 2) = 1 - ((i3Z w).1 + (i3Z w).2) % 2
        - (w.1 + w.2) % 2 := by
    unfold i3Z
    ring
  have hp : ((i3Z w).1 + (i3Z w).2) % 2 + (w.1 + w.2) % 2 = 1 := by
    unfold i3Z
    omega
  linarith

/-- The quarter turn of a field: `quarterTurnField G w = G(Z w) + h₀(w)`. -/
theorem quarterTurnField_apply (G : Field) (w : Site) :
    quarterTurnField G w = G (i3Z w) + harmonicGrid w := by
  unfold quarterTurnField
  rw [i3_mapSite_eq]

/-- The W0 relation `D·n_q − N·d_q = 1` from `eps = −1`. -/
theorem w0_relation (word : Word) (hW0 : (frameAt word).eps = -1) :
    (frameAt word).parents.odd.den * (frameAt word).parents.even.num -
        (frameAt word).parents.odd.num * (frameAt word).parents.even.den = 1 := by
  unfold ChildFrame.eps Fraction.det at hW0
  linarith

/-- The W0 sheet shift is `U_q = (d_q, n_q)`. -/
theorem sheetShift_W0 (word : Word) (hW0 : (frameAt word).eps = -1) :
    (frameAt word).sheetShift = ((frameAt word).parents.even.den, (frameAt word).parents.even.num) := by
  unfold ChildFrame.sheetShift ChildFrame.phaseW
  rw [hW0]
  simp [Fraction.unmodifiedDeck]

/-- The W0 sheet offset is `V_q + eps·U_q = (n_q − 2d_q, d_q)`. -/
theorem sheetOffset_W0 (word : Word) (hW0 : (frameAt word).eps = -1) :
    (frameAt word).sheetOffset = ((frameAt word).parents.even.num - 2 * (frameAt word).parents.even.den,
      (frameAt word).parents.even.den) := by
  unfold ChildFrame.sheetOffset
  rw [hW0]
  ext <;> simp [Fraction.unmodifiedDeck]
  · ring

/-- The W0 sheet constant is `c_e = (T_q − d_q − n_q)/2`. -/
theorem sheetConstant_W0 (word : Word) (hW0 : (frameAt word).eps = -1) :
    (frameAt word).sheetConstant =
      ((frameAt word).parents.even.periodDenominator - (frameAt word).parents.even.den -
        (frameAt word).parents.even.num) / 2 := by
  unfold ChildFrame.sheetConstant ChildFrame.phaseW
  rw [hW0]
  norm_num

/-- The conjugate's `t`-grade in the parent's coordinates. -/
theorem tGrade_conj (word : Word) (h : ∃ x ∈ word, x ≠ Digit.three) (z : Site) :
    (frameAt (conjWord word)).tGrade z =
      ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) * z.1 -
        ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * z.2 := by
  obtain ⟨hcn, hcd⟩ := frameAt_conj_num_den h
  unfold ChildFrame.tGrade
  rw [hcn, hcd]

/-- The conjugate's `s`-grade in the parent's coordinates: `2D z₁ + 2N z₂`. -/
theorem sGrade_conj (word : Word) (h : ∃ x ∈ word, x ≠ Digit.three) (z : Site) :
    (frameAt (conjWord word)).sGrade z = 2 * (frameAt word).parents.odd.den * z.1 +
      2 * (frameAt word).parents.odd.num * z.2 := by
  obtain ⟨hcn, hcd⟩ := frameAt_conj_num_den h
  unfold ChildFrame.sGrade
  rw [hcn, hcd]
  ring

/-- **The point identity for `C(H₀)`.** With `a = n_q` and `d_q = 2b − a`: `h₀(1 − a + d_q, −a − d_q) + a + (T_q − L_q)/2 = 0`. -/
theorem h0_point_zero (a b : ℤ) :
    harmonicGrid (1 - a + (2 * b - a), -a - (2 * b - a)) + a +
      ((2 * b - a) ^ 2 + 2 * (2 * b - a) * a - a ^ 2 - (a + (2 * b - a))) / 2 = 0 := by
  have hN := harmonicGrid_exact (1 - a + (2 * b - a), -a - (2 * b - a))
  have hpar : ((1 - a + (2 * b - a)) + (-a - (2 * b - a))) % 2 = 1 := by omega
  have hq : ((2 * b - a) ^ 2 + 2 * (2 * b - a) * a - a ^ 2 - (a + (2 * b - a))) / 2 = 2 * b ^ 2 - a ^ 2 - b := by
    have e : (2 * b - a) ^ 2 + 2 * (2 * b - a) * a - a ^ 2 - (a + (2 * b - a)) = 2 * (2 * b ^ 2 - a ^ 2 - b) := by
      ring
    rw [e, Int.mul_ediv_cancel_left _ (by norm_num)]
  rw [hq]
  dsimp only at hN
  linarith

/-- **The point identity for `C(H₁)`.** `h₀(2 − a + d_q, −a − d_q) + 2a + (T_q − L_q)/2 = 1` with `d_q = 2b − a`. -/
theorem h0_point_one (a b : ℤ) :
    harmonicGrid (2 - a + (2 * b - a), -a - (2 * b - a)) + 2 * a +
      ((2 * b - a) ^ 2 + 2 * (2 * b - a) * a - a ^ 2 - (a + (2 * b - a))) / 2 = 1 := by
  have hN := harmonicGrid_exact (2 - a + (2 * b - a), -a - (2 * b - a))
  have hpar : ((2 - a + (2 * b - a)) + (-a - (2 * b - a))) % 2 = 0 := by omega
  have hq : ((2 * b - a) ^ 2 + 2 * (2 * b - a) * a - a ^ 2 - (a + (2 * b - a))) / 2 = 2 * b ^ 2 - a ^ 2 - b := by
    have e : (2 * b - a) ^ 2 + 2 * (2 * b - a) * a - a ^ 2 - (a + (2 * b - a)) = 2 * (2 * b ^ 2 - a ^ 2 - b) := by
      ring
    rw [e, Int.mul_ediv_cancel_left _ (by norm_num)]
  rw [hq]
  dsimp only at hN
  linarith

/-- **`Ψ(H₀) = 0` in phase W0**: `A(H₀) = 0` by the harmonic band, `C(H₀) = h₀(z − V_q) + n_q + c_e = 0` by the zero band and
`h0_point_zero`. -/
theorem sheetPsi_H0_W0 (word : Word) (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hW0 : (frameAt word).eps = -1) :
    sheetPsi word (1, 0) = 0 := by
  have hrel := w0_relation word hW0
  obtain ⟨b, hb⟩ : ∃ b : ℤ, (frameAt word).parents.even.num + (frameAt word).parents.even.den = 2 * b := by
    have hev : ((frameAt word).parents.even.num + (frameAt word).parents.even.den) % 2 = 0 :=
      (frameAt word).valid.even_parity
    exact ⟨((frameAt word).parents.even.num + (frameAt word).parents.even.den) / 2, by omega⟩
  have hdq : (frameAt word).parents.even.den = 2 * b - (frameAt word).parents.even.num := by omega
  obtain ⟨hcn, hcd⟩ := frameAt_conj_num_den h
  obtain ⟨c1, c2, c3, c4, -⟩ := (frameAt (conjWord word)).child_facts
  have hS := hSE.packet.strips
  -- the three points
  have e1 : ((1 : ℤ), (0 : ℤ)) - ((frameAt word).parents.even.den, (frameAt word).parents.even.num) =
      (1 - (frameAt word).parents.even.den, -(frameAt word).parents.even.num) := by
    ext <;> simp
  have e2 : (1 - (frameAt word).parents.even.den, -(frameAt word).parents.even.num) -
      ((frameAt word).parents.even.num - 2 * (frameAt word).parents.even.den, (frameAt word).parents.even.den) =
      (1 - (frameAt word).parents.even.num + (frameAt word).parents.even.den,
        -(frameAt word).parents.even.num - (frameAt word).parents.even.den) := by
    ext <;> simp
    ring
  -- the strips of the conjugate at the `Z`-images
  have hzero : standardField (conjWord word)
      (i3Z (1 - (frameAt word).parents.even.num + (frameAt word).parents.even.den,
        -(frameAt word).parents.even.num - (frameAt word).parents.even.den)) = 0 := by
    apply hS.1
    · simp only [tGrade_conj word h, hcd]
      unfold i3Z
      simp only
      nlinarith [hrel, c1, c2, c3, c4]
    · simp only [tGrade_conj word h, hcd, hcn]
      unfold i3Z
      simp only
      nlinarith [hrel, c1, c2, c3, c4]
  have hharm : standardField (conjWord word)
      (i3Z (1 - (frameAt word).parents.even.den, -(frameAt word).parents.even.num)) =
      harmonicGrid (i3Z (1 - (frameAt word).parents.even.den, -(frameAt word).parents.even.num)) := by
    apply hS.2
    · simp only [sGrade_conj word h, hcd]
      unfold i3Z
      simp only
      nlinarith [hrel, c1, c2, c3, c4]
    · simp only [sGrade_conj word h, hcd, hcn]
      unfold i3Z
      simp only
      nlinarith [hrel, c1, c2, c3, c4]
  have key := h0_point_zero (frameAt word).parents.even.num b
  rw [← hdq] at key
  have hce : ((frameAt word).parents.even.periodDenominator - (frameAt word).parents.even.den -
      (frameAt word).parents.even.num) / 2 =
      ((frameAt word).parents.even.den ^ 2 + 2 * (frameAt word).parents.even.den * (frameAt word).parents.even.num -
        (frameAt word).parents.even.num ^ 2 - ((frameAt word).parents.even.num + (frameAt word).parents.even.den)) / 2 := by
    congr 1
    unfold Fraction.periodDenominator
    ring
  unfold sheetPsi ChildFrame.sheetC ChildFrame.sheetA
  rw [sheetShift_W0 word hW0, sheetOffset_W0 word hW0, sheetConstant_W0 word hW0, e1, e2]
  unfold FqW
  rw [quarterTurnField_apply, quarterTurnField_apply, hzero, hharm, harmonicGrid_Z]
  unfold ChildFrame.siblingSlope
  rw [hce]
  dsimp only
  linarith [key]

/-- **`Ψ(H₁) = 1` in phase W0**: `A(H₁) = 0` by the harmonic band, and `C(H₁) = h₀(2 − n_q + d_q, −n_q − d_q) + 2n_q + c_e = 1`. -/
theorem sheetPsi_H1_W0 (word : Word) (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hW0 : (frameAt word).eps = -1) :
    sheetPsi word (2, 0) = 1 := by
  have hrel := w0_relation word hW0
  obtain ⟨b, hb⟩ : ∃ b : ℤ, (frameAt word).parents.even.num + (frameAt word).parents.even.den = 2 * b := by
    have hev : ((frameAt word).parents.even.num + (frameAt word).parents.even.den) % 2 = 0 :=
      (frameAt word).valid.even_parity
    exact ⟨((frameAt word).parents.even.num + (frameAt word).parents.even.den) / 2, by omega⟩
  have hdq : (frameAt word).parents.even.den = 2 * b - (frameAt word).parents.even.num := by omega
  obtain ⟨hcn, hcd⟩ := frameAt_conj_num_den h
  obtain ⟨c1, c2, c3, c4, -⟩ := (frameAt (conjWord word)).child_facts
  have hS := hSE.packet.strips
  have e1 : ((2 : ℤ), (0 : ℤ)) - ((frameAt word).parents.even.den, (frameAt word).parents.even.num) =
      (2 - (frameAt word).parents.even.den, -(frameAt word).parents.even.num) := by
    ext <;> simp
  have e2 : (2 - (frameAt word).parents.even.den, -(frameAt word).parents.even.num) -
      ((frameAt word).parents.even.num - 2 * (frameAt word).parents.even.den, (frameAt word).parents.even.den) =
      (2 - (frameAt word).parents.even.num + (frameAt word).parents.even.den,
        -(frameAt word).parents.even.num - (frameAt word).parents.even.den) := by
    ext <;> simp
    ring
  -- the zero band at `Z(z − V_q)` for `z = (2, 0)`
  have hzero : standardField (conjWord word)
      (i3Z (2 - (frameAt word).parents.even.num + (frameAt word).parents.even.den,
        -(frameAt word).parents.even.num - (frameAt word).parents.even.den)) = 0 := by
    apply hS.1
    · simp only [tGrade_conj word h, hcd]
      unfold i3Z
      simp only
      nlinarith [hrel, c1, c2, c3, c4]
    · simp only [tGrade_conj word h, hcd, hcn]
      unfold i3Z
      simp only
      nlinarith [hrel, c1, c2, c3, c4]
  -- the harmonic band at `Z(z − U_q)` for `z = (2, 0)`
  have hharm : standardField (conjWord word)
      (i3Z (2 - (frameAt word).parents.even.den, -(frameAt word).parents.even.num)) =
      harmonicGrid (i3Z (2 - (frameAt word).parents.even.den, -(frameAt word).parents.even.num)) := by
    apply hS.2
    · simp only [sGrade_conj word h, hcd]
      unfold i3Z
      simp only
      nlinarith [hrel, c1, c2, c3, c4]
    · simp only [sGrade_conj word h, hcd, hcn]
      unfold i3Z
      simp only
      nlinarith [hrel, c1, c2, c3, c4]
  have key := h0_point_one (frameAt word).parents.even.num b
  rw [← hdq] at key
  have hce : ((frameAt word).parents.even.periodDenominator - (frameAt word).parents.even.den -
      (frameAt word).parents.even.num) / 2 =
      ((frameAt word).parents.even.den ^ 2 + 2 * (frameAt word).parents.even.den * (frameAt word).parents.even.num -
        (frameAt word).parents.even.num ^ 2 - ((frameAt word).parents.even.num + (frameAt word).parents.even.den)) / 2 := by
    congr 1
    unfold Fraction.periodDenominator
    ring
  unfold sheetPsi ChildFrame.sheetC ChildFrame.sheetA
  rw [sheetShift_W0 word hW0, sheetOffset_W0 word hW0, sheetConstant_W0 word hW0, e1, e2]
  unfold FqW
  rw [quarterTurnField_apply, quarterTurnField_apply, hzero, hharm, harmonicGrid_Z]
  unfold ChildFrame.siblingSlope
  rw [hce]
  dsimp only
  linarith [key]

/-! ## Phase W1 (`eps = +1`): the calibration at `H_last = (d, n−1)` and `H_{d−2} = (d−1, n−1)` -/

/-- The child's denominator and numerator in the parents: `d = 2D + d_q`, `n = 2N + n_q`. -/
theorem child_den_eq (word : Word) : (frameAt word).child.den = 2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den := by
  unfold ChildFrame.child Parents.current Parents.combine
  simp

theorem child_num_eq (word : Word) : (frameAt word).child.num = 2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num := by
  unfold ChildFrame.child Parents.current Parents.combine
  simp

/-- The W1 relation `D·n_q − N·d_q = −1` from `eps = +1`. -/
theorem w1_relation (word : Word) (hW1 : (frameAt word).eps = 1) :
    (frameAt word).parents.odd.den * (frameAt word).parents.even.num -
        (frameAt word).parents.odd.num * (frameAt word).parents.even.den = -1 := by
  unfold ChildFrame.eps Fraction.det at hW1
  linarith

/-- The W1 sheet shift vanishes (`phaseW = 1`). -/
theorem sheetShift_W1 (word : Word) (hW1 : (frameAt word).eps = 1) : (frameAt word).sheetShift = 0 := by
  unfold ChildFrame.sheetShift ChildFrame.phaseW
  rw [hW1]
  simp

/-- The W1 sheet offset is `V_q + U_q = (n_q, 2n_q + d_q)`. -/
theorem sheetOffset_W1 (word : Word) (hW1 : (frameAt word).eps = 1) :
    (frameAt word).sheetOffset = ((frameAt word).parents.even.num, 2 * (frameAt word).parents.even.num + (frameAt word).parents.even.den) := by
  unfold ChildFrame.sheetOffset
  rw [hW1]
  ext <;> simp [Fraction.unmodifiedDeck]
  ring

/-- The W1 sheet constant is `(T_q − d_q − n_q)/2 + 2`. -/
theorem sheetConstant_W1 (word : Word) (hW1 : (frameAt word).eps = 1) :
    (frameAt word).sheetConstant =
      ((frameAt word).parents.even.periodDenominator - (frameAt word).parents.even.den -
        (frameAt word).parents.even.num) / 2 + 2 := by
  unfold ChildFrame.sheetConstant ChildFrame.phaseW
  rw [hW1]
  norm_num

/-- **The identity at `H_last` (W1)**, with `d_q = 2m − n_q`: `h₀(2m − 2u, −1 − 2m) + (2m − u) + (2m² − u² − m) = 0`. -/
theorem h0_w1_last (u m : ℤ) :
    harmonicGrid (2 * m - 2 * u, -1 - 2 * m) + (2 * m - u) + (2 * m ^ 2 - u ^ 2 - m) = 0 := by
  have hN := harmonicGrid_exact (2 * m - 2 * u, -1 - 2 * m)
  have hpar : ((2 * m - 2 * u) + (-1 - 2 * m)) % 2 = 1 := by omega
  dsimp only at hN
  linarith

/-- **The identity at `H_{d−2}` (W1)**: `h₀(−1 − 2u + 2m, −1 − 2m) − 2u + m + (2m² − u² − m)... = 1`, i.e. the value `1` at `H_{d−2}`. -/
theorem h0_w1_minus2 (u m : ℤ) :
    harmonicGrid (-1 - 2 * u + 2 * m, -1 - 2 * m) - u + (2 * m - u) + (2 * m ^ 2 - u ^ 2 - m) = 1 := by
  have hN := harmonicGrid_exact (-1 - 2 * u + 2 * m, -1 - 2 * m)
  have hpar : ((-1 - 2 * u + 2 * m) + (-1 - 2 * m)) % 2 = 0 := by omega
  dsimp only at hN
  linarith

/-- **`Ψ(H_last) = 0` in phase W1.** `A(H_last) = 0` by the harmonic band; `C(H_last) = h₀(x) + (−2 + d_q) + c_e = 0` with
`x = (0,−1) − V_q`, the `C`-argument being `x` modulo the parent's `U_p` (`quarterTurnField_Upar_period`), and `x` in the zero band. -/
theorem sheetPsi_hLast_W1 (word : Word) (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hW1 : (frameAt word).eps = 1) :
    sheetPsi word ((frameAt word).child.den, (frameAt word).child.num - 1) = 0 := by
  have hrel := w1_relation word hW1
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (frameAt word).parents.even.num + (frameAt word).parents.even.den = 2 * m := by
    have hev : ((frameAt word).parents.even.num + (frameAt word).parents.even.den) % 2 = 0 :=
      (frameAt word).valid.even_parity
    exact ⟨((frameAt word).parents.even.num + (frameAt word).parents.even.den) / 2, by omega⟩
  have hdq : (frameAt word).parents.even.den = 2 * m - (frameAt word).parents.even.num := by omega
  obtain ⟨hcn, hcd⟩ := frameAt_conj_num_den h
  obtain ⟨c1, c2, c3, c4, -⟩ := (frameAt (conjWord word)).child_facts
  rw [hcn] at c1 c2 c3
  rw [hcd] at c2 c3 c4
  have hS := hSE.packet.strips
  have hd := child_den_eq word
  have hn := child_num_eq word
  have hzero : standardField (conjWord word)
      (i3Z (((0 : ℤ), (-1 : ℤ)) - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
        (frameAt word).parents.even.num + (frameAt word).parents.even.den))) = 0 := by
    apply hS.1
    · simp only [tGrade_conj word h, hcd]
      unfold i3Z
      simp only [Prod.fst_sub, Prod.snd_sub]
      nlinarith [hrel, c1, c2, c3, c4]
    · simp only [tGrade_conj word h, hcn, hcd]
      unfold i3Z
      simp only [Prod.fst_sub, Prod.snd_sub]
      nlinarith [hrel, c1, c2, c3, c4]
  have hharm : standardField (conjWord word)
      (i3Z ((frameAt word).child.den, (frameAt word).child.num - 1)) =
      harmonicGrid (i3Z ((frameAt word).child.den, (frameAt word).child.num - 1)) := by
    apply hS.2
    · simp only [sGrade_conj word h, hcd, hd, hn]
      unfold i3Z
      simp only
      nlinarith [hrel, c1, c2, c3, c4]
    · simp only [sGrade_conj word h, hcd, hd, hn]
      unfold i3Z
      simp only
      nlinarith [hrel, c1, c2, c3, c4]
  have hx : ((0 : ℤ), (-1 : ℤ)) - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
        (frameAt word).parents.even.num + (frameAt word).parents.even.den) =
      (2 * m - 2 * (frameAt word).parents.even.num, -1 - 2 * m) := by
    ext <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> rw [hdq] <;> ring
  have hval : harmonicGrid (((0 : ℤ), (-1 : ℤ)) - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
        (frameAt word).parents.even.num + (frameAt word).parents.even.den)) =
      -(2 * m - (frameAt word).parents.even.num) - (2 * m ^ 2 - (frameAt word).parents.even.num ^ 2 - m) := by
    rw [hx]
    have := h0_w1_last (frameAt word).parents.even.num m
    linarith
  have hce : ((frameAt word).parents.even.periodDenominator - (frameAt word).parents.even.den -
      (frameAt word).parents.even.num) / 2 = 2 * m ^ 2 - (frameAt word).parents.even.num ^ 2 - m := by
    have e : (frameAt word).parents.even.periodDenominator - (frameAt word).parents.even.den -
        (frameAt word).parents.even.num = 2 * (2 * m ^ 2 - (frameAt word).parents.even.num ^ 2 - m) := by
      unfold Fraction.periodDenominator
      rw [hdq]
      ring
    rw [e, Int.mul_ediv_cancel_left _ (by norm_num)]
  have hsh : ((frameAt word).child.den, (frameAt word).child.num - 1) -
      ((frameAt word).parents.even.num, 2 * (frameAt word).parents.even.num + (frameAt word).parents.even.den) =
      (((0 : ℤ), (-1 : ℤ)) - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
        (frameAt word).parents.even.num + (frameAt word).parents.even.den)) + Upar word := by
    unfold Upar
    ext <;> simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, hd, hn] <;> ring
  have hsib : (frameAt word).parents.even.num * ((frameAt word).child.den) -
      (frameAt word).parents.even.den * ((frameAt word).child.num - 1) = -2 + (2 * m - (frameAt word).parents.even.num) := by
    rw [hd, hn]
    have hrel' := hrel
    rw [hdq] at hrel'
    linarith
  unfold sheetPsi ChildFrame.sheetC ChildFrame.sheetA
  rw [sheetShift_W1 word hW1, sheetOffset_W1 word hW1, sheetConstant_W1 word hW1]
  simp only [sub_zero]
  unfold FqW
  rw [hsh, quarterTurnField_Upar_period h hSE, quarterTurnField_apply, quarterTurnField_apply, hzero, hharm, harmonicGrid_Z]
  unfold ChildFrame.siblingSlope
  rw [hce]
  linarith [hval, hsib]

/-- **`Ψ(H_{d−2}) = 1` in phase W1.** `A = 0` by the harmonic band at `Z(H_{d−2})`; `C = h₀(x₂) + (−2 − n_q + d_q) + c_e = 1` with
`x₂ = (−1,−1) − V_q` (the `C`-argument is `x₂` modulo `U_p`), and `x₂` in the zero band. -/
theorem sheetPsi_hMinus2_W1 (word : Word) (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hW1 : (frameAt word).eps = 1) :
    sheetPsi word ((frameAt word).child.den - 1, (frameAt word).child.num - 1) = 1 := by
  have hrel := w1_relation word hW1
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (frameAt word).parents.even.num + (frameAt word).parents.even.den = 2 * m := by
    have hev : ((frameAt word).parents.even.num + (frameAt word).parents.even.den) % 2 = 0 :=
      (frameAt word).valid.even_parity
    exact ⟨((frameAt word).parents.even.num + (frameAt word).parents.even.den) / 2, by omega⟩
  have hdq : (frameAt word).parents.even.den = 2 * m - (frameAt word).parents.even.num := by omega
  obtain ⟨hcn, hcd⟩ := frameAt_conj_num_den h
  obtain ⟨c1, c2, c3, c4, -⟩ := (frameAt (conjWord word)).child_facts
  rw [hcn] at c1 c2 c3
  rw [hcd] at c2 c3 c4
  have hS := hSE.packet.strips
  have hd := child_den_eq word
  have hn := child_num_eq word
  have hzero : standardField (conjWord word)
      (i3Z (((-1 : ℤ), (-1 : ℤ)) - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
        (frameAt word).parents.even.num + (frameAt word).parents.even.den))) = 0 := by
    apply hS.1
    · simp only [tGrade_conj word h, hcd]
      unfold i3Z
      simp only [Prod.fst_sub, Prod.snd_sub]
      nlinarith [hrel, c1, c2, c3, c4]
    · simp only [tGrade_conj word h, hcn, hcd]
      unfold i3Z
      simp only [Prod.fst_sub, Prod.snd_sub]
      nlinarith [hrel, c1, c2, c3, c4]
  have hharm : standardField (conjWord word)
      (i3Z ((frameAt word).child.den - 1, (frameAt word).child.num - 1)) =
      harmonicGrid (i3Z ((frameAt word).child.den - 1, (frameAt word).child.num - 1)) := by
    apply hS.2
    · simp only [sGrade_conj word h, hcd, hd, hn]
      unfold i3Z
      simp only
      nlinarith [hrel, c1, c2, c3, c4]
    · simp only [sGrade_conj word h, hcd, hd, hn]
      unfold i3Z
      simp only
      nlinarith [hrel, c1, c2, c3, c4]
  have hx : ((-1 : ℤ), (-1 : ℤ)) - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
        (frameAt word).parents.even.num + (frameAt word).parents.even.den) =
      (-1 - 2 * (frameAt word).parents.even.num + 2 * m, -1 - 2 * m) := by
    ext <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> rw [hdq] <;> ring
  have hval : harmonicGrid (((-1 : ℤ), (-1 : ℤ)) - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
        (frameAt word).parents.even.num + (frameAt word).parents.even.den)) =
      1 + (frameAt word).parents.even.num - (2 * m - (frameAt word).parents.even.num) -
        (2 * m ^ 2 - (frameAt word).parents.even.num ^ 2 - m) := by
    rw [hx]
    have := h0_w1_minus2 (frameAt word).parents.even.num m
    linarith
  have hce : ((frameAt word).parents.even.periodDenominator - (frameAt word).parents.even.den -
      (frameAt word).parents.even.num) / 2 = 2 * m ^ 2 - (frameAt word).parents.even.num ^ 2 - m := by
    have e : (frameAt word).parents.even.periodDenominator - (frameAt word).parents.even.den -
        (frameAt word).parents.even.num = 2 * (2 * m ^ 2 - (frameAt word).parents.even.num ^ 2 - m) := by
      unfold Fraction.periodDenominator
      rw [hdq]
      ring
    rw [e, Int.mul_ediv_cancel_left _ (by norm_num)]
  have hsh : ((frameAt word).child.den - 1, (frameAt word).child.num - 1) -
      ((frameAt word).parents.even.num, 2 * (frameAt word).parents.even.num + (frameAt word).parents.even.den) =
      (((-1 : ℤ), (-1 : ℤ)) - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
        (frameAt word).parents.even.num + (frameAt word).parents.even.den)) + Upar word := by
    unfold Upar
    ext <;> simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, hd, hn] <;> ring
  have hsib : (frameAt word).parents.even.num * ((frameAt word).child.den - 1) -
      (frameAt word).parents.even.den * ((frameAt word).child.num - 1) = -2 - (frameAt word).parents.even.num +
        (frameAt word).parents.even.den := by
    rw [hd, hn]
    have hrel' := hrel
    rw [hdq] at hrel'
    rw [hdq]
    linarith
  unfold sheetPsi ChildFrame.sheetC ChildFrame.sheetA
  rw [sheetShift_W1 word hW1, sheetOffset_W1 word hW1, sheetConstant_W1 word hW1]
  simp only [sub_zero]
  unfold FqW
  rw [hsh, quarterTurnField_Upar_period h hSE, quarterTurnField_apply, quarterTurnField_apply, hzero, hharm, harmonicGrid_Z]
  unfold ChildFrame.siblingSlope
  rw [hce]
  linarith [hval, hsib]

end FLatticePaper.PsiCalibration



