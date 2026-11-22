import FLatticePaper.Plane.Induction.Sheets

/-! Task 25: the written steps behind (I1) and (I2).

* (I1) root values, H_SOURCE_ANCESTRAL_CLOSURE §2-3. For eps = -1 (archive W0; `W = (1 + eps)/2 = 0`), the calibration
  at H_0 = (1, 0) and H_1 = (2, y), y in {0, 1, 2}, gives `C = h0` and `A = 0`, so `Psi = h0` there:
  `Psi(H_0) = 0` and `Psi(H_1) = 1`. Along the child index, `Psi` is nondecreasing (the V-trace monotonicity of §1,
  an input), so `Psi(H_j) >= 1` for `1 <= j < d`.
  Named inputs: the parent strips `Fp = h0` at `H_0 - V_q` and `H_1 - V_q`; the zero strips `Fp = 0` at `H_0 - U_q` and
  `H_1 - U_q` (the sheet A is zero on the root); the monotone order; the height y in {0, 1, 2} of H_1 (from n < d).
* (I2) nontied roots, V_SOURCE_MONOTONICITY_AUDIT (eps = +1). If the sheet A agrees with h0 on the star of a root with
  `Psi >= 1` and unit input gaps, then `min(A, C) = h0` on the complete star. The agreement of A with h0 is the parent
  harmonic strip under the sp-guard of the audit (named input). -/

namespace FLatticePaper.Induction
open Farey FLatticePaper

/-- A harmonic value from its numerator: the numerator of `harmonicGrid` is four times the value. -/
theorem harmonicGrid_eq_of_numerator (x1 x2 k : ℤ)
    (h : x1 ^ 2 + 2 * x1 * x2 - x2 ^ 2 - 2 * x2 - (x1 + x2) % 2 = 4 * k) :
    harmonicGrid (x1, x2) = k := by
  show (x1 ^ 2 + 2 * x1 * x2 - x2 ^ 2 - 2 * x2 - (x1 + x2) % 2) / 4 = k
  rw [h]
  omega

/-- `h0` on the row `x = 2` is one at the heights `y = 0, 1, 2` (the endpoint H_1 of the calibration). -/
theorem harmonicGrid_two_row (y : ℤ) (hy : y = 0 ∨ y = 1 ∨ y = 2) : harmonicGrid (2, y) = 1 :=
  harmonicGrid_eq_of_numerator 2 y 1 (by rcases hy with rfl | rfl | rfl <;> norm_num)

/-- The quadratic part of the H_0 numerator, halved, is an integer (a(a-1) and b(b-1) are even). -/
theorem even_quadratic_H0 (a b : ℤ) : ∃ k : ℤ, a ^ 2 - 2 * a * b - a - b ^ 2 + b = 2 * k := by
  obtain ⟨r1, hr1⟩ := Int.even_mul_pred_self a
  obtain ⟨r2, hr2⟩ := Int.even_mul_pred_self b
  exact ⟨r1 - a * b - r2, by linear_combination hr1 - hr2⟩

/-- The quadratic part of the H_1 numerator for the height `y`, halved, is an integer. -/
theorem even_quadratic_H1 (a b y : ℤ) :
    ∃ k : ℤ, a ^ 2 - 2 * a * b - 3 * a - b ^ 2 + (2 * y + 1) * b + 2 = 2 * k := by
  obtain ⟨r1, hr1⟩ := Int.even_mul_pred_self a
  obtain ⟨r2, hr2⟩ := Int.even_mul_pred_self b
  exact ⟨r1 - a - r2 + y * b - a * b + 1, by linear_combination hr1 - hr2⟩

/-- Arithmetic of the calibration at `H_0 = (1, 0)` for `eps = -1`: with `a = n_q`, `b = d_q`, the value of `h0` at
`H_0 - V_q` plus the slope `a` plus the constant `(T_q - b - a)/2` is `h0(H_0) = 0`. -/
theorem harmonic_calibration_zero (a b : ℤ) :
    harmonicGrid (1 - (a - b), 0 - (a + b)) + a + ((b ^ 2 + 2 * b * a - a ^ 2) - b - a) / 2 =
      harmonicGrid (1, 0) := by
  obtain ⟨k, hk⟩ := even_quadratic_H0 a b
  have hp : (1 - (a - b) + (0 - (a + b))) % 2 = 1 := by omega
  have hH : harmonicGrid (1 - (a - b), 0 - (a + b)) = k := by
    apply harmonicGrid_eq_of_numerator
    rw [hp]
    linear_combination 2 * hk
  have hT : (b ^ 2 + 2 * b * a - a ^ 2) - b - a = 2 * (-k - a) := by
    linear_combination (-1 : ℤ) * hk
  have h10 : harmonicGrid (1, 0) = 0 := harmonicGrid_eq_of_numerator 1 0 0 (by norm_num)
  rw [hH, hT, h10, Int.mul_ediv_cancel_left _ two_ne_zero]
  ring

/-- Arithmetic of the calibration at `H_1 = (2, y)`, `y in {0, 1, 2}`, for `eps = -1`: `h0(H_1 - V_q) + (2a - b y) +
(T_q - b - a)/2 = h0(2, y) = 1`. -/
theorem harmonic_calibration_one (a b y : ℤ) (hy : y = 0 ∨ y = 1 ∨ y = 2) :
    harmonicGrid (2 - (a - b), y - (a + b)) + (2 * a - b * y) + ((b ^ 2 + 2 * b * a - a ^ 2) - b - a) / 2 =
      harmonicGrid (2, y) := by
  obtain ⟨k, hk⟩ := even_quadratic_H1 a b y
  have hp : (2 - (a - b) + (y - (a + b))) % 2 = y % 2 := by omega
  have hN : (2 - (a - b)) ^ 2 + 2 * (2 - (a - b)) * (y - (a + b)) - (y - (a + b)) ^ 2 - 2 * (y - (a + b))
      = 2 * (a ^ 2 - 2 * a * b - 3 * a - b ^ 2 + (2 * y + 1) * b + 2) + y % 2 := by
    rcases hy with rfl | rfl | rfl <;> norm_num <;> ring
  have hH : harmonicGrid (2 - (a - b), y - (a + b)) = k := by
    apply harmonicGrid_eq_of_numerator
    rw [hp]
    linear_combination hN + 2 * hk
  have hT : ((b ^ 2 + 2 * b * a - a ^ 2) - b - a) = 2 * (-k - 2 * a + y * b + 1) := by
    linear_combination (-1 : ℤ) * hk
  rw [hH, hT, harmonicGrid_two_row y hy, Int.mul_ediv_cancel_left _ two_ne_zero]
  ring

/-- For `eps = -1` the shift is the even kernel, the offset is `V_q - U_q`, and the constant is `(T_q - d_q - n_q)/2`. -/
theorem eps_neg_shift (frame : ChildFrame) (hε : frame.eps = -1) :
    frame.sheetShift = frame.parents.even.unmodifiedDeck.kernel := by
  have hW : frame.phaseW = 0 := by unfold ChildFrame.phaseW; rw [hε]; norm_num
  unfold ChildFrame.sheetShift; rw [hW]; simp

theorem eps_neg_offset (frame : ChildFrame) (hε : frame.eps = -1) :
    frame.sheetOffset =
      frame.parents.even.unmodifiedDeck.transverse - frame.parents.even.unmodifiedDeck.kernel := by
  unfold ChildFrame.sheetOffset; rw [hε]; simp [sub_eq_add_neg]

theorem eps_neg_constant (frame : ChildFrame) (hε : frame.eps = -1) :
    frame.sheetConstant =
      ((frame.parents.even.den ^ 2 + 2 * frame.parents.even.den * frame.parents.even.num -
        frame.parents.even.num ^ 2) - frame.parents.even.den - frame.parents.even.num) / 2 := by
  have hW : frame.phaseW = 0 := by unfold ChildFrame.phaseW; rw [hε]; norm_num
  unfold ChildFrame.sheetConstant Fraction.periodDenominator; rw [hW]; ring_nf

/-- Calibration at `H_0 = (1, 0)` for the frame with `eps = -1`: `C = h0` there, under the parent harmonic strip
`Fp = h0` at `H_0 - V_q` (named input). -/
theorem sheetC_H0_of_eps_neg (frame : ChildFrame) (Fp : Field) (hε : frame.eps = -1)
    (hstrip : Fp ((1, 0) - frame.parents.even.unmodifiedDeck.transverse) =
      harmonicGrid ((1, 0) - frame.parents.even.unmodifiedDeck.transverse)) :
    frame.sheetC Fp (1, 0) = harmonicGrid (1, 0) := by
  have harg : (1, 0) - frame.sheetShift - frame.sheetOffset =
      (1, 0) - frame.parents.even.unmodifiedDeck.transverse := by
    rw [eps_neg_shift frame hε, eps_neg_offset frame hε]; abel
  have hslope : frame.siblingSlope ((1, 0) - frame.sheetShift) = frame.parents.even.num := by
    rw [eps_neg_shift frame hε]; unfold ChildFrame.siblingSlope
    simp only [Fraction.unmodifiedDeck, Prod.fst_sub, Prod.snd_sub]; ring
  have hc := harmonic_calibration_zero frame.parents.even.num frame.parents.even.den
  unfold ChildFrame.sheetC
  rw [harg, hstrip, hslope, eps_neg_constant frame hε]
  simp only [Fraction.unmodifiedDeck, Prod.mk_sub_mk] at hc ⊢
  linarith [hc]

/-- Calibration at `H_1 = (2, y)` for the frame with `eps = -1`, `y in {0, 1, 2}`: `C = h0` there, under the parent
harmonic strip `Fp = h0` at `H_1 - V_q` (named input). -/
theorem sheetC_H1_of_eps_neg (frame : ChildFrame) (Fp : Field) (hε : frame.eps = -1) (y : ℤ)
    (hy : y = 0 ∨ y = 1 ∨ y = 2)
    (hstrip : Fp ((2, y) - frame.parents.even.unmodifiedDeck.transverse) =
      harmonicGrid ((2, y) - frame.parents.even.unmodifiedDeck.transverse)) :
    frame.sheetC Fp (2, y) = harmonicGrid (2, y) := by
  have harg : (2, y) - frame.sheetShift - frame.sheetOffset =
      (2, y) - frame.parents.even.unmodifiedDeck.transverse := by
    rw [eps_neg_shift frame hε, eps_neg_offset frame hε]; abel
  have hslope : frame.siblingSlope ((2, y) - frame.sheetShift) =
      2 * frame.parents.even.num - frame.parents.even.den * y := by
    rw [eps_neg_shift frame hε]; unfold ChildFrame.siblingSlope
    simp only [Fraction.unmodifiedDeck, Prod.fst_sub, Prod.snd_sub]; ring
  have hc := harmonic_calibration_one frame.parents.even.num frame.parents.even.den y hy
  unfold ChildFrame.sheetC
  rw [harg, hstrip, hslope, eps_neg_constant frame hε]
  simp only [Fraction.unmodifiedDeck, Prod.mk_sub_mk] at hc ⊢
  linarith [hc]

/-- The monotone root gaps: a nondecreasing sequence with value one at index one has value at least one at every index
`1 <= j < d`. -/
theorem rootGap_ge_one_of_monotone (f : ℕ → ℤ) (d : ℕ)
    (hmono : ∀ j, j + 1 < d → f j ≤ f (j + 1)) (h1 : f 1 = 1) :
    ∀ j, 1 ≤ j → j < d → 1 ≤ f j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => intro _; rw [h1]
  | succ m hm ih =>
    intro hmd
    exact le_trans (ih (by omega)) (hmono m hmd)

/-- (I1), eps = -1: the root gaps `Psi(w_j) = C - A` at the child H points, with `w_0 = H_0` and `w_1 = H_1`, are at
least one for `1 <= j < d`, from the calibration, the zero strips, and the monotone order (V-trace, an input). -/
theorem psi_H0_eps_neg (frame : ChildFrame) (Fp : Field) (hε : frame.eps = -1)
    (hstrip0 : Fp ((1, 0) - frame.parents.even.unmodifiedDeck.transverse) =
      harmonicGrid ((1, 0) - frame.parents.even.unmodifiedDeck.transverse))
    (hzero0 : Fp ((1, 0) - frame.sheetShift) = 0) :
    frame.sheetC Fp (1, 0) - frame.sheetA Fp (1, 0) = 0 := by
  have hA0 : frame.sheetA Fp (1, 0) = 0 := by unfold ChildFrame.sheetA; exact hzero0
  rw [hA0, sheetC_H0_of_eps_neg frame Fp hε hstrip0, sub_zero, harmonicGrid_eq_of_numerator 1 0 0 (by norm_num)]

/-- (I1), eps = -1: the root gaps `Psi(w_j) = C - A` at the child H points, with `w_1 = H_1`, are at least one for
`1 <= j < d`, from the calibration at H_1, the zero strip at H_1, and the monotone order (V-trace, an input). -/
theorem rootGap_ge_one_eps_neg (frame : ChildFrame) (Fp : Field) (hε : frame.eps = -1) (w : ℕ → Site) (d : ℕ)
    (y : ℤ) (hy : y = 0 ∨ y = 1 ∨ y = 2) (hw1 : w 1 = (2, y))
    (hstrip1 : Fp ((2, y) - frame.parents.even.unmodifiedDeck.transverse) =
      harmonicGrid ((2, y) - frame.parents.even.unmodifiedDeck.transverse))
    (hzero1 : Fp ((2, y) - frame.sheetShift) = 0)
    (hmono : ∀ j, j + 1 < d →
      frame.sheetC Fp (w j) - frame.sheetA Fp (w j) ≤ frame.sheetC Fp (w (j + 1)) - frame.sheetA Fp (w (j + 1))) :
    ∀ j, 1 ≤ j → j < d → 1 ≤ frame.sheetC Fp (w j) - frame.sheetA Fp (w j) := by
  have hA1 : frame.sheetA Fp (2, y) = 0 := by unfold ChildFrame.sheetA; exact hzero1
  have h1 : frame.sheetC Fp (w 1) - frame.sheetA Fp (w 1) = 1 := by
    rw [hw1, sheetC_H1_of_eps_neg frame Fp hε y hy hstrip1, hA1, harmonicGrid_two_row y hy]
    ring
  exact rootGap_ge_one_of_monotone (fun j => frame.sheetC Fp (w j) - frame.sheetA Fp (w j)) d hmono h1

/-- The nontied root step, sheet level: if the sheet A agrees with `h` on the star of a root `w` whose gap is at least
one, and the input gaps are unit, then `min(A, C) = h` on the complete star. -/
theorem min_eq_of_root_gap (A C h : Site → ℤ) (w : Site)
    (hgap : 1 ≤ C w - A w)
    (hunit : ∀ u, FLatticePaper.Edge u w → -1 ≤ (C u - A u) - (C w - A w) ∧ (C u - A u) - (C w - A w) ≤ 1)
    (hA : ∀ u, u = w ∨ FLatticePaper.Edge u w → A u = h u) :
    ∀ u, u = w ∨ FLatticePaper.Edge u w → min (A u) (C u) = h u := by
  intro u hu
  rcases hu with h' | hE
  · have hle : A w ≤ C w := by linarith
    rw [h', min_eq_left hle, hA w (Or.inl rfl)]
  · have hu' := hunit u hE
    have hle : A u ≤ C u := by linarith [hu'.1]
    rw [min_eq_left hle, hA u (Or.inr hE)]

/-- On the branch `eps = +1` the shift vanishes, so the sheet `A` is the field itself. -/
theorem sheetA_eq_of_eps_pos (frame : ChildFrame) (Fp : Field) (hε : frame.eps = 1) (z : Site) :
    frame.sheetA Fp z = Fp z := by
  have hW : frame.phaseW = 1 := by unfold ChildFrame.phaseW; rw [hε]; norm_num
  have hshift : frame.sheetShift = 0 := by unfold ChildFrame.sheetShift; rw [hW]; simp
  unfold ChildFrame.sheetA; rw [hshift, sub_zero]

/-- The sp-guard of the audit for a site: `-2 D + 1 <= sp(u) <= 2 D + 2 N - 1` with `sp = (D + N) u_1 + (D - N) u_2`,
for the odd parent `N/D`. -/
def ChildFrame.spGuard (frame : ChildFrame) (u : Site) : Prop :=
  -2 * frame.parents.odd.den + 1 ≤
      (frame.parents.odd.den + frame.parents.odd.num) * u.1 + (frame.parents.odd.den - frame.parents.odd.num) * u.2 ∧
    (frame.parents.odd.den + frame.parents.odd.num) * u.1 + (frame.parents.odd.den - frame.parents.odd.num) * u.2 ≤
      2 * frame.parents.odd.den + 2 * frame.parents.odd.num - 1

/-- (I2), eps = +1, nontied roots. Named inputs: the parent harmonic strip `Fp = h0` on the sp-guarded sites, and the
sp-guard on the star. Then `min(A, C) = h0` on the complete star of a root with `Psi >= 1` and unit input gaps. -/
theorem i2_nontied_min_eq_harmonic (frame : ChildFrame) (Fp : Field) (hε : frame.eps = 1)
    (hstrip : ∀ x : Site, frame.spGuard x → Fp x = harmonicGrid x)
    (w : Site) (hgap : 1 ≤ frame.sheetC Fp w - frame.sheetA Fp w)
    (hunit : ∀ u, FLatticePaper.Edge u w →
      -1 ≤ (frame.sheetC Fp u - frame.sheetA Fp u) - (frame.sheetC Fp w - frame.sheetA Fp w) ∧
        (frame.sheetC Fp u - frame.sheetA Fp u) - (frame.sheetC Fp w - frame.sheetA Fp w) ≤ 1)
    (hguard : ∀ u, u = w ∨ FLatticePaper.Edge u w → frame.spGuard u) :
    ∀ u, u = w ∨ FLatticePaper.Edge u w →
      min (frame.sheetA Fp u) (frame.sheetC Fp u) = harmonicGrid u :=
  min_eq_of_root_gap (frame.sheetA Fp) (frame.sheetC Fp) harmonicGrid w hgap hunit
    (fun u hu => by rw [sheetA_eq_of_eps_pos frame Fp hε u]; exact hstrip u (hguard u hu))

end FLatticePaper.Induction
