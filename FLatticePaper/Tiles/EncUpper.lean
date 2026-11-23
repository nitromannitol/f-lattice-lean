import FLatticePaper.Tiles.SitePairScope

/-! Task 53, item 2 (encOdd / encEven): the six natural standard sources of an ordinary child lie in `H` of the child.

Proof structure (ALL_ORDINARY_A3_NATIVE_H_ENCLOSURES_BY_FOUR_MARGINS §§3-8): the formal reflection
`z ↦ R_X − z` of `H_X` removes the upper facets, so only the two lower facets of each source remain. Each lower facet
follows from a linear identity in the parent's `(t, s)` coordinates, the minimising corner of the parent's rectangle, and
a real margin that is `> −1` (odd child, `t`) or `> −2` with parity (all `s`, and even child `t`). -/

namespace FLatticePaper.Tiles.EncUpper

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.SiteInduction

/-- The lower facets of `H_X` at a site `z` (the two inequalities of (H) that bound from below). -/
def LowerOK (X : Fraction) (z : ℤ × ℤ) : Prop :=
  aOf X (decide ((z.1 + z.2) % 2 = 0)) - tOf X ≤ tCo X z ∧
    lOf X (decide ((z.1 + z.2) % 2 = 0)) ≤ sCo X z

/-- The formal reflection `z ↦ R_X − z` with `R_X = μ X + V_X + I`, on sites. -/
def refl (f : Fraction) (z : ℤ × ℤ) : ℤ × ℤ :=
  (muOf f * f.den + f.num - f.den + 1 - z.1, muOf f * f.num + f.den + f.num - 1 - z.2)

theorem tCo_refl (f : Fraction) (z : ℤ × ℤ) :
    tCo f (refl f z) = f.den + f.num - tOf f - tCo f z := by
  unfold refl tCo tOf; ring

theorem sCo_refl (f : Fraction) (z : ℤ × ℤ) :
    sCo f (refl f z) = muOf f * tOf f + 2 * f.num - sCo f z := by
  unfold refl sCo tOf; ring

theorem refl_sum (f : Fraction) (z : ℤ × ℤ) :
    ((refl f z).1 + (refl f z).2) % 2 = (z.1 + z.2) % 2 := by
  have hA : (muOf f * (f.den + f.num)) % 2 = 0 := by
    unfold muOf; split_ifs with h <;> omega
  have key : (refl f z).1 + (refl f z).2 = muOf f * (f.den + f.num) + 2 * f.num - (z.1 + z.2) := by
    unfold refl; ring
  rw [key]
  generalize muOf f * (f.den + f.num) = A at hA ⊢
  omega

theorem refl_refl (f : Fraction) (w : ℤ × ℤ) : refl f (refl f w) = w := by
  unfold refl; ext <;> simp

theorem inH_iff_lower (X : Fraction) (z : ℤ × ℤ) :
    InH X z ↔ LowerOK X z ∧ LowerOK X (refl X z) := by
  have hp : decide (((refl X z).1 + (refl X z).2) % 2 = 0) = decide ((z.1 + z.2) % 2 = 0) := by
    rw [refl_sum]
  unfold LowerOK
  rw [hp, tCo_refl, sCo_refl]
  unfold InH
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h1, h3⟩, by constructor <;> linarith⟩
  · rintro ⟨⟨h1, h3⟩, h5, h6⟩
    exact ⟨h1, by linarith, h3, by linarith⟩

theorem inH_refl (f : Fraction) (w : ℤ × ℤ) (hw : InH f w) : InH f (refl f w) := by
  rw [inH_iff_lower] at hw ⊢
  rw [refl_refl]
  exact ⟨hw.2, hw.1⟩

/-- A containment of a translated source from its lower facets at the origin `v` and at the reflected origin `v'`. -/
theorem piece_sub (X f : Fraction) (v v' : ℤ × ℤ) (hv' : ∀ w, refl X (v + w) = v' + refl f w)
    (hlow : ∀ w, InH f w → LowerOK X (v + w)) (hlow' : ∀ w, InH f w → LowerOK X (v' + w)) :
    ∀ w, InH f w → InH X (v + w) := by
  intro w hw
  rw [inH_iff_lower]
  refine ⟨hlow w hw, ?_⟩
  have h2 := hlow' (refl f w) (inH_refl f w hw)
  rw [← hv'] at h2
  exact h2

theorem round1 {Y : ℤ} (h : -1 < Y) : 0 ≤ Y := by omega

theorem round2 {Y : ℤ} (hY : Y % 2 = 0) (h : -2 < Y) : 0 ≤ Y := by omega

/-! ### The linear identities of `t_C`, `s_C` on the parent sources (exact, with `δ = dr − ne`). -/

theorem ident_tP (n d e r m : ℤ) (w : ℤ × ℤ) :
    (d ^ 2 + 2 * d * n - n ^ 2) * tCo ⟨m * n + r, m * d + e⟩ w
      = (m * (d ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r)) * tCo ⟨n, d⟩ w
        + (d * r - n * e) * sCo ⟨n, d⟩ w := by
  unfold tCo sCo; ring

theorem ident_sP (n d e r m : ℤ) (w : ℤ × ℤ) :
    (d ^ 2 + 2 * d * n - n ^ 2) * sCo ⟨m * n + r, m * d + e⟩ w
      = (m * (d ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r)) * sCo ⟨n, d⟩ w
        + 2 * (d * r - n * e) * tCo ⟨n, d⟩ w := by
  unfold tCo sCo; ring

theorem ident_tQ (n d e r m : ℤ) (w : ℤ × ℤ) :
    (e ^ 2 + 2 * e * r - r ^ 2) * tCo ⟨m * n + r, m * d + e⟩ w
      = (e ^ 2 + 2 * e * r - r ^ 2 + m * ((d + n) * e + (d - n) * r)) * tCo ⟨r, e⟩ w
        - m * (d * r - n * e) * sCo ⟨r, e⟩ w := by
  unfold tCo sCo; ring

theorem ident_sQ (n d e r m : ℤ) (w : ℤ × ℤ) :
    (e ^ 2 + 2 * e * r - r ^ 2) * sCo ⟨m * n + r, m * d + e⟩ w
      = (e ^ 2 + 2 * e * r - r ^ 2 + m * ((d + n) * e + (d - n) * r)) * sCo ⟨r, e⟩ w
        - 2 * m * (d * r - n * e) * tCo ⟨r, e⟩ w := by
  unfold tCo sCo; ring

/-! ### Base lower-facet lemmas: the margin condition `0 < M` gives `−k < Y`, with `Y` the lower-facet slack. -/

theorem base_tP_pos {X tP sP Dn K m aP lP aC TC g0 k : ℤ} (hD : 0 < Dn) (hK : 0 ≤ K) (hm : 0 ≤ m)
    (hX : Dn * X = (m * Dn + K) * tP + sP) (ht : aP - Dn ≤ tP) (hs : lP ≤ sP)
    (hM : 0 < Dn * (g0 - aC + TC) + (m * Dn + K) * (aP - Dn) + lP + k * Dn) :
    -k < X + g0 - aC + TC := by
  have hc : 0 ≤ m * Dn + K := by nlinarith
  have h1 : (m * Dn + K) * (aP - Dn) ≤ (m * Dn + K) * tP := mul_le_mul_of_nonneg_left ht hc
  have h2 : Dn * (-k) < Dn * (X + g0 - aC + TC) := by nlinarith
  exact lt_of_mul_lt_mul_left h2 hD.le

theorem base_tP_neg {X tP sP Dn K m aP hi aC TC g0 k : ℤ} (hD : 0 < Dn) (hK : 0 ≤ K) (hm : 0 ≤ m)
    (hX : Dn * X = (m * Dn + K) * tP - sP) (ht : aP - Dn ≤ tP) (hs : sP ≤ hi)
    (hM : 0 < Dn * (g0 - aC + TC) + (m * Dn + K) * (aP - Dn) - hi + k * Dn) :
    -k < X + g0 - aC + TC := by
  have hc : 0 ≤ m * Dn + K := by nlinarith
  have h1 : (m * Dn + K) * (aP - Dn) ≤ (m * Dn + K) * tP := mul_le_mul_of_nonneg_left ht hc
  have h2 : Dn * (-k) < Dn * (X + g0 - aC + TC) := by nlinarith
  exact lt_of_mul_lt_mul_left h2 hD.le

theorem base_sP_pos {X tP sP Dn K m lP aP lC g0 k : ℤ} (hD : 0 < Dn) (hK : 0 ≤ K) (hm : 0 ≤ m)
    (hX : Dn * X = (m * Dn + K) * sP + 2 * tP) (ht : aP - Dn ≤ tP) (hs : lP ≤ sP)
    (hM : 0 < Dn * (g0 - lC) + (m * Dn + K) * lP + 2 * (aP - Dn) + k * Dn) :
    -k < X + g0 - lC := by
  have hc : 0 ≤ m * Dn + K := by nlinarith
  have h1 : (m * Dn + K) * lP ≤ (m * Dn + K) * sP := mul_le_mul_of_nonneg_left hs hc
  have h2 : Dn * (-k) < Dn * (X + g0 - lC) := by nlinarith
  exact lt_of_mul_lt_mul_left h2 hD.le

theorem base_sP_neg {X tP sP Dn K m lP hi lC g0 k : ℤ} (hD : 0 < Dn) (hK : 0 ≤ K) (hm : 0 ≤ m)
    (hX : Dn * X = (m * Dn + K) * sP - 2 * tP) (ht : tP ≤ hi) (hs : lP ≤ sP)
    (hM : 0 < Dn * (g0 - lC) + (m * Dn + K) * lP - 2 * hi + k * Dn) :
    -k < X + g0 - lC := by
  have hc : 0 ≤ m * Dn + K := by nlinarith
  have h1 : (m * Dn + K) * lP ≤ (m * Dn + K) * sP := mul_le_mul_of_nonneg_left hs hc
  have h2 : Dn * (-k) < Dn * (X + g0 - lC) := by nlinarith
  exact lt_of_mul_lt_mul_left h2 hD.le

/-- `Q`-source, `t`-facet, flag true (`δ = −1`): `T X = (T + mK) tQ + m sQ`, `sQ ≥ lQ`. -/
theorem base_tQ_neg {X tQ sQ Dn K m aQ lQ aC TC g0 k : ℤ} (hD : 0 < Dn) (hK : 0 ≤ K) (hm : 0 ≤ m)
    (hX : Dn * X = (Dn + m * K) * tQ + m * sQ) (ht : aQ - Dn ≤ tQ) (hs : lQ ≤ sQ)
    (hM : 0 < Dn * (g0 - aC + TC) + (Dn + m * K) * (aQ - Dn) + m * lQ + k * Dn) :
    -k < X + g0 - aC + TC := by
  have hc : 0 ≤ Dn + m * K := by nlinarith
  have h1 : (Dn + m * K) * (aQ - Dn) ≤ (Dn + m * K) * tQ := mul_le_mul_of_nonneg_left ht hc
  have h2 : Dn * (-k) < Dn * (X + g0 - aC + TC) := by nlinarith
  exact lt_of_mul_lt_mul_left h2 hD.le

/-- `Q`-source, `t`-facet, flag false (`δ = +1`): `T X = (T + mK) tQ − m sQ`, `sQ ≤ hi`. -/
theorem base_tQ_pos {X tQ sQ Dn K m aQ hi aC TC g0 k : ℤ} (hD : 0 < Dn) (hK : 0 ≤ K) (hm : 0 ≤ m)
    (hX : Dn * X = (Dn + m * K) * tQ - m * sQ) (ht : aQ - Dn ≤ tQ) (hs : sQ ≤ hi)
    (hM : 0 < Dn * (g0 - aC + TC) + (Dn + m * K) * (aQ - Dn) - m * hi + k * Dn) :
    -k < X + g0 - aC + TC := by
  have hc : 0 ≤ Dn + m * K := by nlinarith
  have h1 : (Dn + m * K) * (aQ - Dn) ≤ (Dn + m * K) * tQ := mul_le_mul_of_nonneg_left ht hc
  have h2 : Dn * (-k) < Dn * (X + g0 - aC + TC) := by nlinarith
  exact lt_of_mul_lt_mul_left h2 hD.le

/-- `Q`-source, `s`-facet, flag false: `T s_C = (T + mK) sQ − 2m tQ`, `tQ ≤ hi`. -/
theorem base_sQ_pos {X tQ sQ Dn K m lQ hi lC g0 k : ℤ} (hD : 0 < Dn) (hK : 0 ≤ K) (hm : 0 ≤ m)
    (hX : Dn * X = (Dn + m * K) * sQ - 2 * m * tQ) (ht : tQ ≤ hi) (hs : lQ ≤ sQ)
    (hM : 0 < Dn * (g0 - lC) + (Dn + m * K) * lQ - 2 * m * hi + k * Dn) :
    -k < X + g0 - lC := by
  have hc : 0 ≤ Dn + m * K := by nlinarith
  have h1 : (Dn + m * K) * lQ ≤ (Dn + m * K) * sQ := mul_le_mul_of_nonneg_left hs hc
  have h2 : Dn * (-k) < Dn * (X + g0 - lC) := by nlinarith
  exact lt_of_mul_lt_mul_left h2 hD.le

/-- `Q`-source, `s`-facet, flag true: `T s_C = (T + mK) sQ + 2m tQ`, `tQ ≥ aQ − T`. -/
theorem base_sQ_neg {X tQ sQ Dn K m lQ aQ lC g0 k : ℤ} (hD : 0 < Dn) (hK : 0 ≤ K) (hm : 0 ≤ m)
    (hX : Dn * X = (Dn + m * K) * sQ + 2 * m * tQ) (ht : aQ - Dn ≤ tQ) (hs : lQ ≤ sQ)
    (hM : 0 < Dn * (g0 - lC) + (Dn + m * K) * lQ + 2 * m * (aQ - Dn) + k * Dn) :
    -k < X + g0 - lC := by
  have hc : 0 ≤ Dn + m * K := by nlinarith
  have h1 : (Dn + m * K) * lQ ≤ (Dn + m * K) * sQ := mul_le_mul_of_nonneg_left hs hc
  have h2 : Dn * (-k) < Dn * (X + g0 - lC) := by nlinarith
  exact lt_of_mul_lt_mul_left h2 hD.le

/-! ### Evaluations of `a`, `l`, `μ` on the parents and children -/

theorem aOf_true_le (f : Fraction) (h : 2 * f.num ≤ f.den - f.num) : aOf f true = 2 * f.num := by
  simp [aOf, min_eq_left h]

theorem aOf_true_ge (f : Fraction) (h : f.den - f.num ≤ 2 * f.num) : aOf f true = f.den - f.num := by
  simp [aOf, min_eq_right h]

theorem aOf_false' (f : Fraction) : aOf f false = f.num := by simp [aOf]

theorem lOf_true' (f : Fraction) : lOf f true = 0 := by simp [lOf]

theorem lOf_false_le (f : Fraction) (h : 2 * f.num ≤ f.den) : lOf f false = 3 * f.num - f.den := by
  simp [lOf, min_eq_right (show 3 * f.num - f.den ≤ f.den - f.num by omega)]

theorem lOf_false_ge (f : Fraction) (h : f.den ≤ 2 * f.num) : lOf f false = f.den - f.num := by
  simp [lOf, min_eq_left (show f.den - f.num ≤ 3 * f.num - f.den by omega)]

theorem muOf_two (f : Fraction) (h : (f.num + f.den) % 2 = 1) : muOf f = 2 := by
  simp [muOf, h]

theorem muOf_one (f : Fraction) (h : (f.num + f.den) % 2 = 0) : muOf f = 1 := by
  simp [muOf, h]

theorem inH_even {f : Fraction} {w : ℤ × ℤ} (h : (w.1 + w.2) % 2 = 0) :
    InH f w ↔ (aOf f true - tOf f ≤ tCo f w ∧ tCo f w ≤ f.den + f.num - aOf f true ∧
      lOf f true ≤ sCo f w ∧ sCo f w ≤ muOf f * tOf f + 2 * f.num - lOf f true) := by
  unfold InH; rw [decide_eq_true h]

theorem inH_odd {f : Fraction} {w : ℤ × ℤ} (h : ¬ (w.1 + w.2) % 2 = 0) :
    InH f w ↔ (aOf f false - tOf f ≤ tCo f w ∧ tCo f w ≤ f.den + f.num - aOf f false ∧
      lOf f false ≤ sCo f w ∧ sCo f w ≤ muOf f * tOf f + 2 * f.num - lOf f false) := by
  unfold InH; rw [decide_eq_false h]

/-! ### The side of a pair: no proper pair straddles `1/3` or `1/2` strictly. -/

theorem mixed3a (n d r e δ : ℤ) (hn : 1 ≤ n) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = δ) (hδ : δ = 1 ∨ δ = -1) (h1 : 3 * n < d) (h2 : e < 3 * r) : False := by
  have hid : (3 * r - e) * d + (d - 3 * n) * e = 3 * δ := by linear_combination 3 * hdet
  rcases hδ with h | h <;> subst h <;>
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ 3 * r - e - 1 by omega) (show (0 : ℤ) ≤ d by omega),
      mul_nonneg (show (0 : ℤ) ≤ d - 3 * n - 1 by omega) (show (0 : ℤ) ≤ e by omega)]

theorem mixed3b (n d r e δ : ℤ) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = δ) (hδ : δ = 1 ∨ δ = -1) (h1 : d < 3 * n) (h2 : 3 * r < e) : False := by
  have hid : (3 * r - e) * d + (d - 3 * n) * e = 3 * δ := by linear_combination 3 * hdet
  rcases hδ with h | h <;> subst h <;>
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ e - 3 * r - 1 by omega) (show (0 : ℤ) ≤ d by omega),
      mul_nonneg (show (0 : ℤ) ≤ 3 * n - d - 1 by omega) (show (0 : ℤ) ≤ e by omega)]

theorem mixed2a (n d r e δ : ℤ) (hn : 1 ≤ n) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = δ) (hδ : δ = 1 ∨ δ = -1) (h1 : 2 * n < d) (h2 : e < 2 * r) : False := by
  have hid : (2 * r - e) * d + (d - 2 * n) * e = 2 * δ := by linear_combination 2 * hdet
  rcases hδ with h | h <;> subst h <;>
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 * r - e - 1 by omega) (show (0 : ℤ) ≤ d by omega),
      mul_nonneg (show (0 : ℤ) ≤ d - 2 * n - 1 by omega) (show (0 : ℤ) ≤ e by omega)]

theorem mixed2b (n d r e δ : ℤ) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = δ) (hδ : δ = 1 ∨ δ = -1) (h1 : d < 2 * n) (h2 : 2 * r < e) : False := by
  have hid : (2 * r - e) * d + (d - 2 * n) * e = 2 * δ := by linear_combination 2 * hdet
  rcases hδ with h | h <;> subst h <;>
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ e - 2 * r - 1 by omega) (show (0 : ℤ) ≤ d by omega),
      mul_nonneg (show (0 : ℤ) ≤ 2 * n - d - 1 by omega) (show (0 : ℤ) ≤ e by omega)]

theorem side3 (n d r e δ : ℤ) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = δ) (hδ : δ = 1 ∨ δ = -1) :
    (3 * n ≤ d ∧ 3 * r ≤ e) ∨ (d ≤ 3 * n ∧ e ≤ 3 * r) := by
  rcases le_or_gt (3 * n) d with h1 | h1 <;> rcases le_or_gt (3 * r) e with h2 | h2
  · exact Or.inl ⟨h1, h2⟩
  · rcases eq_or_lt_of_le h1 with h3 | h3
    · exact Or.inr ⟨h3.symm.le, h2.le⟩
    · exact (mixed3a n d r e δ hn hr hre hdet hδ h3 h2).elim
  · rcases eq_or_lt_of_le h2 with h3 | h3
    · exact Or.inr ⟨h1.le, h3.symm.le⟩
    · exact (mixed3b n d r e δ hn hnd hr hre hdet hδ h1 h3).elim
  · exact Or.inr ⟨h1.le, h2.le⟩

theorem side2 (n d r e δ : ℤ) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = δ) (hδ : δ = 1 ∨ δ = -1) :
    (2 * n ≤ d ∧ 2 * r ≤ e) ∨ (d ≤ 2 * n ∧ e ≤ 2 * r) := by
  rcases le_or_gt (2 * n) d with h1 | h1 <;> rcases le_or_gt (2 * r) e with h2 | h2
  · exact Or.inl ⟨h1, h2⟩
  · rcases eq_or_lt_of_le h1 with h3 | h3
    · exact Or.inr ⟨h3.symm.le, h2.le⟩
    · exact (mixed2a n d r e δ hn hr hre hdet hδ h3 h2).elim
  · rcases eq_or_lt_of_le h2 with h3 | h3
    · exact Or.inr ⟨h1.le, h3.symm.le⟩
    · exact (mixed2b n d r e δ hnd hr hre hdet hδ h1 h3).elim
  · exact Or.inr ⟨h1.le, h2.le⟩

/-! ### The child's `a`, `l` on either branch (`C = ⟨m n + r, m d + e⟩`, `m = 1, 2`). -/

theorem childA_true_below (n d r e m : ℤ) (hm : m = 1 ∨ m = 2) (h3 : 3 * n ≤ d ∧ 3 * r ≤ e) :
    aOf ⟨m * n + r, m * d + e⟩ true = m * (2 * n) + 2 * r := by
  have hle : 2 * (m * n + r) ≤ (m * d + e) - (m * n + r) := by
    rcases hm with rfl | rfl <;> omega
  rw [aOf_true_le _ hle]; ring

theorem childA_true_above (n d r e m : ℤ) (hm : m = 1 ∨ m = 2) (h3 : d ≤ 3 * n ∧ e ≤ 3 * r) :
    aOf ⟨m * n + r, m * d + e⟩ true = m * (d - n) + (e - r) := by
  have hge : (m * d + e) - (m * n + r) ≤ 2 * (m * n + r) := by
    rcases hm with rfl | rfl <;> omega
  rw [aOf_true_ge _ hge]; ring

theorem childL_false_below (n d r e m : ℤ) (hm : m = 1 ∨ m = 2) (h2 : 2 * n ≤ d ∧ 2 * r ≤ e) :
    lOf ⟨m * n + r, m * d + e⟩ false = m * (3 * n - d) + (3 * r - e) := by
  have hle : 2 * (m * n + r) ≤ m * d + e := by
    rcases hm with rfl | rfl <;> omega
  rw [lOf_false_le _ hle]; ring

theorem childL_false_above (n d r e m : ℤ) (hm : m = 1 ∨ m = 2) (h2 : d ≤ 2 * n ∧ e ≤ 2 * r) :
    lOf ⟨m * n + r, m * d + e⟩ false = m * (d - n) + (e - r) := by
  have hge : m * d + e ≤ 2 * (m * n + r) := by
    rcases hm with rfl | rfl <;> omega
  rw [lOf_false_ge _ hge]; ring

/-! ### Parity of the rounded slacks (the integer rounding of the `k = 2` margins). -/

theorem par_tA (X : Fraction) (hn : X.num % 2 = 1) (hd : X.den % 2 = 1) (z : ℤ × ℤ) :
    (tCo X z - aOf X (decide ((z.1 + z.2) % 2 = 0)) + tOf X) % 2 = 0 := by
  have hT : tOf X = X.den * X.den + 2 * (X.den * X.num) - X.num * X.num := by unfold tOf; ring
  have h1 : (X.num * z.1) % 2 = z.1 % 2 := by rw [Int.mul_emod, hn]; simp
  have h2 : (X.den * z.2) % 2 = z.2 % 2 := by rw [Int.mul_emod, hd]; simp
  have h3 : (X.den * X.den) % 2 = 1 := by rw [Int.mul_emod, hd]; simp
  have h4 : (X.num * X.num) % 2 = 1 := by rw [Int.mul_emod, hn]; simp
  have hA : aOf X true % 2 = 0 := by unfold aOf; simp only [if_true]; omega
  unfold tCo; rw [hT]
  by_cases h : (z.1 + z.2) % 2 = 0
  · rw [decide_eq_true h]; omega
  · rw [decide_eq_false h, aOf_false']; omega

theorem par_sA (X : Fraction) (hn : X.num % 2 = 1) (hd : X.den % 2 = 1) (z : ℤ × ℤ) :
    (sCo X z - lOf X (decide ((z.1 + z.2) % 2 = 0))) % 2 = 0 := by
  have h1 : ((X.den + X.num) * z.1) % 2 = 0 := by
    rw [Int.mul_emod]; have : (X.den + X.num) % 2 = 0 := by omega
    rw [this]; simp
  have h2 : ((X.den - X.num) * z.2) % 2 = 0 := by
    rw [Int.mul_emod]; have : (X.den - X.num) % 2 = 0 := by omega
    rw [this]; simp
  have hL : lOf X false % 2 = 0 := by unfold lOf; simp only [Bool.false_eq_true, if_false]; omega
  unfold sCo
  by_cases h : (z.1 + z.2) % 2 = 0
  · rw [decide_eq_true h, lOf_true']; omega
  · rw [decide_eq_false h]; omega

theorem par_sB (X : Fraction) (hs : (X.num + X.den) % 2 = 1) (z : ℤ × ℤ) :
    (sCo X z - lOf X (decide ((z.1 + z.2) % 2 = 0))) % 2 = 0 := by
  have h1 : ((X.den + X.num) * z.1) % 2 = z.1 % 2 := by
    rw [Int.mul_emod]; have : (X.den + X.num) % 2 = 1 := by omega
    rw [this]; simp
  have h2 : ((X.den - X.num) * z.2) % 2 = z.2 % 2 := by
    rw [Int.mul_emod]; have : (X.den - X.num) % 2 = 1 := by omega
    rw [this]; simp
  have hL : lOf X false % 2 = 1 := by unfold lOf; simp only [Bool.false_eq_true, if_false]; omega
  unfold sCo
  by_cases h : (z.1 + z.2) % 2 = 0
  · rw [decide_eq_true h, lOf_true']; omega
  · rw [decide_eq_false h]; omega

/-! ### Origins: a source with origin `v` (even coordinate sum) has its lower facets from the two minimising origins. -/

theorem lowOK_origin (X f : Fraction) (v vt vs : ℤ × ℤ) (hv : (v.1 + v.2) % 2 = 0)
    (ht : tCo X vt ≤ tCo X v) (hs : sCo X vs ≤ sCo X v)
    (hfam : ∀ w, InH f w →
      (aOf X (decide ((w.1 + w.2) % 2 = 0)) - tOf X ≤ tCo X (vt + w)) ∧
        (lOf X (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo X (vs + w))) :
    ∀ w, InH f w → LowerOK X (v + w) := by
  intro w hw
  obtain ⟨h1, h2⟩ := hfam w hw
  have hp : decide (((v + w).1 + (v + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have ht' : tCo X (v + w) = tCo X v + tCo X w := by unfold tCo; simp only [Prod.fst_add, Prod.snd_add]; ring
  have ht'' : tCo X (vt + w) = tCo X vt + tCo X w := by unfold tCo; simp only [Prod.fst_add, Prod.snd_add]; ring
  have hs' : sCo X (v + w) = sCo X v + sCo X w := by unfold sCo; simp only [Prod.fst_add, Prod.snd_add]; ring
  have hs'' : sCo X (vs + w) = sCo X vs + sCo X w := by unfold sCo; simp only [Prod.fst_add, Prod.snd_add]; ring
  unfold LowerOK
  rw [hp]
  constructor
  · rw [ht']; rw [ht''] at h1; linarith
  · rw [hs']; rw [hs''] at h2; linarith

/-! ### Parent-level evaluations at explicit fractions, and the parity of the determinant pairs. -/

theorem tCo_pair (f : Fraction) (x y : ℤ) : tCo f (x, y) = f.num * x - f.den * y := rfl

theorem sCo_pair (f : Fraction) (x y : ℤ) : sCo f (x, y) = (f.den + f.num) * x + (f.den - f.num) * y := rfl

theorem tOf_mk (n d : ℤ) : tOf ⟨n, d⟩ = d ^ 2 + 2 * d * n - n ^ 2 := by
  unfold tOf; ring

theorem aOf_mk_true_le (n d : ℤ) (h : 2 * n ≤ d - n) : aOf ⟨n, d⟩ true = 2 * n := by
  simp [aOf, min_eq_left h]

theorem aOf_mk_true_ge (n d : ℤ) (h : d - n ≤ 2 * n) : aOf ⟨n, d⟩ true = d - n := by
  simp [aOf, min_eq_right h]

theorem aOf_mk_false (n d : ℤ) : aOf ⟨n, d⟩ false = n := by simp [aOf]

theorem lOf_mk_true (n d : ℤ) : lOf ⟨n, d⟩ true = 0 := by simp [lOf]

theorem lOf_mk_false_le (n d : ℤ) (h : 2 * n ≤ d) : lOf ⟨n, d⟩ false = 3 * n - d := by
  simp [lOf, min_eq_right (show 3 * n - d ≤ d - n by omega)]

theorem lOf_mk_false_ge (n d : ℤ) (h : d ≤ 2 * n) : lOf ⟨n, d⟩ false = d - n := by
  simp [lOf, min_eq_left (show d - n ≤ 3 * n - d by omega)]

theorem muOf_mk_two (n d : ℤ) (h : (n + d) % 2 = 1) : muOf ⟨n, d⟩ = 2 := by
  simp [muOf, h]

theorem muOf_mk_one (n d : ℤ) (h : (n + d) % 2 = 0) : muOf ⟨n, d⟩ = 1 := by
  simp [muOf, h]

/-- The determinant `dr − ne = ±1` with `d + n` odd and `e + r` even forces `r`, `e` odd. -/
theorem re_odd (n d r e δ : ℤ) (hdet : d * r - n * e = δ) (hδ : δ = 1 ∨ δ = -1)
    (heven : (e + r) % 2 = 0) : r % 2 = 1 ∧ e % 2 = 1 := by
  by_contra hc
  have hr0 : r % 2 = 0 ∨ e % 2 = 0 := by omega
  have he : e % 2 = r % 2 := by omega
  have hdr : (d * r) % 2 = 0 := by
    rcases hr0 with h | h
    · rw [Int.mul_emod, h]; simp
    · have : r % 2 = 0 := by omega
      rw [Int.mul_emod, this]; simp
  have hne : (n * e) % 2 = 0 := by
    have : e % 2 = 0 := by omega
    rw [Int.mul_emod, this]; simp
  have hz : (d * r - n * e) % 2 = 0 := by omega
  rw [hdet] at hz
  rcases hδ with h | h <;> rw [h] at hz <;> norm_num at hz

/-! ### Rounding to the lower facets (the `a`, `l` values are supplied at the site's parity). -/

theorem lowT1 (X : Fraction) (z : ℤ × ℤ) (a : ℤ) (hA : aOf X (decide ((z.1 + z.2) % 2 = 0)) = a)
    (h : -1 < tCo X z - a + tOf X) : aOf X (decide ((z.1 + z.2) % 2 = 0)) - tOf X ≤ tCo X z := by
  rw [hA]; have := round1 h; linarith

theorem lowT2 (X : Fraction) (z : ℤ × ℤ) (a : ℤ) (hA : aOf X (decide ((z.1 + z.2) % 2 = 0)) = a)
    (hpar : (tCo X z - a + tOf X) % 2 = 0) (h : -2 < tCo X z - a + tOf X) :
    aOf X (decide ((z.1 + z.2) % 2 = 0)) - tOf X ≤ tCo X z := by
  rw [hA]; have := round2 hpar h; linarith

theorem lowS1 (X : Fraction) (z : ℤ × ℤ) (l : ℤ) (hL : lOf X (decide ((z.1 + z.2) % 2 = 0)) = l)
    (h : -1 < sCo X z - l) : lOf X (decide ((z.1 + z.2) % 2 = 0)) ≤ sCo X z := by
  rw [hL]; have := round1 h; linarith

theorem lowS2 (X : Fraction) (z : ℤ × ℤ) (l : ℤ) (hL : lOf X (decide ((z.1 + z.2) % 2 = 0)) = l)
    (hpar : (sCo X z - l) % 2 = 0) (h : -2 < sCo X z - l) :
    lOf X (decide ((z.1 + z.2) % 2 = 0)) ≤ sCo X z := by
  rw [hL]; have := round2 hpar h; linarith

theorem aOf_child_false (m n r d e : ℤ) : aOf ⟨m * n + r, m * d + e⟩ false = m * n + r := by
  simp [aOf]

end FLatticePaper.Tiles.EncUpper
