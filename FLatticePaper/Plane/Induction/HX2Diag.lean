import FLatticePaper.Plane.Induction.HX1Residue

/-! # The diagonal neighbours hX2 of an even free V root are nonfree

For an even free V root `z` (not the origin), the east diagonal `(z.1 + 1, z.2 - 1)` is nonfree, and for `z ≠ vLast` the west
diagonal `(z.1 - 1, z.2 + 1)` is nonfree. Every deck translate is checked on its grades, using the polygon and the lower input
`(z.1, z.2 - 1)` (which lies in the V band, `ChildFrame.lower_in_vBand`), and two lattice facts on the even V roots:
`t ≤ -L` (`t ∉ (-L, 0)`) and `t ∉ [L - P + 2, 2L - P - 2]`. -/

namespace FLatticePaper.Induction

open LowerBandCore
open FLatticePaper.Induction.ShortPassages
open Farey

/-- The grade `t` of an even free V root avoids `(-L, 0)`: the argument `P a = (d-n) t + d s` forces `a = 0`, then `d ∣ t`. -/
theorem core_neg_mid {n d P a s t : ℤ} (hn0 : 0 < n) (hnd : n < d) (hdn : 2 ≤ d - n)
    (hP : P = d ^ 2 + 2 * d * n - n ^ 2) (hcop : IsCoprime d (d - n)) (hdodd : d % 2 = 1)
    (hA : P * a = (d - n) * t + d * s) (hs1 : 0 ≤ s) (hs2 : s ≤ 2 * n)
    (hlo : 1 - (d + n) ≤ t) (hhi : t ≤ -1) (hpar : t % 2 = 0) : False := by
  have hPpos : 0 < P := by rw [hP]; nlinarith
  have hV1 : -P < (d - n) * t + d * s := by
    nlinarith [mul_le_mul_of_nonneg_left hlo (show (0:ℤ) ≤ d - n by omega),
      mul_nonneg (show (0:ℤ) ≤ d by omega) hs1]
  have hV2 : (d - n) * t + d * s < P := by
    nlinarith [mul_le_mul_of_nonneg_left hhi (show (0:ℤ) ≤ d - n by omega),
      mul_le_mul_of_nonneg_left hs2 (show (0:ℤ) ≤ d by omega)]
  have ha : a = 0 := by
    by_contra h
    rcases lt_or_gt_of_ne h with h' | h'
    · nlinarith [mul_le_mul_of_nonneg_left (show a ≤ -1 by omega) hPpos.le]
    · nlinarith [mul_le_mul_of_nonneg_left (show 1 ≤ a by omega) hPpos.le]
  subst ha
  have hV0 : (d - n) * t + d * s = 0 := by linear_combination -hA
  have hdvd : d ∣ (d - n) * t := ⟨-s, by linear_combination hV0⟩
  obtain ⟨k, hk⟩ := hcop.dvd_of_dvd_mul_left hdvd
  have hk1 : k ≤ -1 := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg (show (0:ℤ) ≤ d by omega) (show (0:ℤ) ≤ k by omega)]
  have hk2 : -1 ≤ k := by
    by_contra h
    push Not at h
    nlinarith [mul_le_mul_of_nonneg_left (show k ≤ -2 by omega) (show (0:ℤ) ≤ d by omega)]
  have hk' : k = -1 := by omega
  subst hk'
  omega

/-- The grade `t` of an even free V root avoids `[L - P + 2, 2L - P - 2]`: `a = n - d + 1`, then `τ = d`, `s = 3n - d`, and the
even point would be `(n - d + 1, L - 2)` with odd sum. -/
theorem core_mid {n d P a b s t : ℤ} (hn0 : 0 < n) (hnd : n < d) (hdn : 2 ≤ d - n)
    (hP : P = d ^ 2 + 2 * d * n - n ^ 2) (hcop : IsCoprime d (d - n))
    (hA : P * a = (d - n) * t + d * s) (hB : P * b = n * s - (d + n) * t)
    (hs1 : 0 ≤ s) (hs2 : s ≤ 2 * n) (hEv : (a + b) % 2 = 0)
    (hlo : d + n - P + 2 ≤ t) (hhi : t ≤ 2 * (d + n) - P - 2) : False := by
  have hPpos : 0 < P := by rw [hP]; nlinarith
  have hW : P * (a + (d - n)) = (d - n) * (t + P) + d * s := by linear_combination hA
  have hW0 : 0 < (d - n) * (t + P) + d * s := by
    nlinarith [mul_le_mul_of_nonneg_left (show (2:ℤ) ≤ t + P by omega) (show (0:ℤ) ≤ d - n by omega),
      mul_nonneg (show (0:ℤ) ≤ d by omega) hs1]
  have hW1 : (d - n) * (t + P) + d * s < 2 * P := by
    nlinarith [mul_le_mul_of_nonneg_left (show t + P ≤ 2 * (d + n) - 2 by omega) (show (0:ℤ) ≤ d - n by omega),
      mul_le_mul_of_nonneg_left hs2 (show (0:ℤ) ≤ d by omega)]
  have hk1 : a + (d - n) = 1 := by
    have hk0 : 0 < a + (d - n) := by
      by_contra h
      push Not at h
      nlinarith [mul_nonneg hPpos.le (show (0:ℤ) ≤ -(a + (d - n)) by omega)]
    have hk2 : a + (d - n) < 2 := by
      by_contra h
      push Not at h
      nlinarith [mul_le_mul_of_nonneg_left h hPpos.le]
    omega
  have ha : a = n - d + 1 := by omega
  subst ha
  have hsub : (d - n) * (t - (d + n - P)) + d * (s - 2 * n) = 0 := by
    linear_combination (-1 : ℤ) * hA + hP
  have hdvd : d ∣ (d - n) * (t - (d + n - P)) := ⟨-(s - 2 * n), by linear_combination hsub⟩
  obtain ⟨k, hk⟩ := hcop.dvd_of_dvd_mul_left hdvd
  have hk1' : 1 ≤ k := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg (show (0:ℤ) ≤ d by omega) (show (0:ℤ) ≤ -k by omega)]
  have hk2' : k ≤ 1 := by
    by_contra h
    push Not at h
    nlinarith [mul_le_mul_of_nonneg_left (show (2:ℤ) ≤ k by omega) (show (0:ℤ) ≤ d by omega)]
  have hk3 : k = 1 := by omega
  subst hk3
  have ht : t = 2 * d + n - P := by linarith
  subst ht
  have hs' : s = 3 * n - d := by
    have h : d * (s - (3 * n - d)) = 0 := by linear_combination hsub
    rcases mul_eq_zero.mp h with h' | h'
    · omega
    · linarith
  subst hs'
  have hPb : P * (b - (d + n - 2)) = 0 := by
    linear_combination hB + 2 * hP
  have hb : b = d + n - 2 := by
    have := (mul_eq_zero.mp hPb).resolve_left hPpos.ne'
    linarith
  subst hb
  omega

namespace ChildFrame
variable (frame : ChildFrame)

/-- The grade `t` of an even free V root (not the origin) is at most `-L`. -/
theorem t_le_neg_L {z : Site} (hz : z ∈ frame.freeV) (hev : EvenSite z)
    (hzF : z ≠ FLatticePaper.Induction.vFirst) :
    frame.tGrade z ≤ -(frame.child.num + frame.child.den) := by
  obtain ⟨hn0, hnd, hdn, hd3, hP⟩ := frame.child_facts
  have hodd := frame.child_num_odd
  have hpar : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hdodd : frame.child.den % 2 = 1 := by omega
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * frame.child.num + v * frame.child.den = 1 := frame.child_reduced
  have hcop : IsCoprime frame.child.den (frame.child.den - frame.child.num) :=
    ⟨u + v, -u, by linear_combination huv⟩
  obtain ⟨hs1, hs2, ht1, ht2⟩ := frame.root_bounds hz hev
  have hpar_t := frame.tGrade_even hev
  have hA := frame.ident_a z
  have hB := frame.ident_b z
  have hev' : (z.1 + z.2) % 2 = 0 := hev
  have ht0 : frame.tGrade z ≠ 0 := by
    intro h0
    rw [h0] at hA hB
    obtain ⟨ha, hb⟩ := core_t0 hn0 hnd hdn hP hA hB hs1 hs2
    exact hzF (Prod.ext ha hb)
  by_contra hc
  push Not at hc
  have hlo : 1 - (frame.child.den + frame.child.num) ≤ frame.tGrade z := by omega
  have hhi : frame.tGrade z ≤ -1 := by omega
  exact core_neg_mid hn0 hnd hdn hP hcop hdodd hA hs1 hs2 hlo hhi hpar_t

/-- The grade `t` of an even free V root avoids `[L - P + 2, 2L - P - 2]`. -/
theorem t_not_mid {z : Site} (hz : z ∈ frame.freeV) (hev : EvenSite z)
    (hlo : frame.child.den + frame.child.num - frame.child.periodDenominator + 2 ≤ frame.tGrade z)
    (hhi : frame.tGrade z ≤ 2 * (frame.child.den + frame.child.num) - frame.child.periodDenominator - 2) :
    False := by
  obtain ⟨hn0, hnd, hdn, hd3, hP⟩ := frame.child_facts
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * frame.child.num + v * frame.child.den = 1 := frame.child_reduced
  have hcop : IsCoprime frame.child.den (frame.child.den - frame.child.num) :=
    ⟨u + v, -u, by linear_combination huv⟩
  obtain ⟨hs1, hs2, -, -⟩ := frame.root_bounds hz hev
  have hA := frame.ident_a z
  have hB := frame.ident_b z
  have hev' : (z.1 + z.2) % 2 = 0 := hev
  exact core_mid hn0 hnd hdn hP hcop hA hB hs1 hs2 hev' hlo hhi

/-- The point `z` has `s ≠ 2n` unless it is `vLast`. -/
theorem s_ne_two_n {z : Site} (hz : z ∈ frame.freeV) (hev : EvenSite z)
    (hzL : z ≠ frame.vLast) : frame.sGrade z ≠ 2 * frame.child.num := by
  obtain ⟨hn0, hnd, hdn, hd3, hP⟩ := frame.child_facts
  have hodd := frame.child_num_odd
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * frame.child.num + v * frame.child.den = 1 := frame.child_reduced
  obtain ⟨-, -, ht1, ht2⟩ := frame.root_bounds hz hev
  have hev' : (z.1 + z.2) % 2 = 0 := hev
  intro h2
  have hA := frame.ident_a z
  have hB := frame.ident_b z
  rw [h2] at hA hB
  obtain ⟨ha, hb⟩ := core_s2n hn0 hdn hP ⟨u, v, huv⟩ hodd hA hB hev' ht1 ht2
  exact hzL (by unfold ChildFrame.vLast; exact Prod.ext ha hb)

/-- The bounds of an even translate lying in the closed polygon. -/
theorem cp_bounds_even {p : Site} (hp : p ∈ frame.closedPolygon) (hev : EvenSite p) :
    2 - frame.child.periodDenominator ≤ frame.tGrade p ∧
      frame.tGrade p ≤ frame.child.den + frame.child.num - 2 ∧ 0 ≤ frame.sGrade p ∧
      frame.sGrade p ≤ frame.child.periodDenominator + 2 * frame.child.num := by
  rcases (frame.mem_closedPolygon_iff p).mp hp with h | h
  · exact h.2
  · exact absurd hev h.1

/-- The east diagonal `(z.1 + 1, z.2 - 1)` of an even free V root (not the origin) is nonfree. -/
theorem nonfree_east_diag {z : Site} (hz : z ∈ frame.freeV) (hev : EvenSite z)
    (hzF : z ≠ FLatticePaper.Induction.vFirst) : Nonfree frame (z.1 + 1, z.2 - 1) := by
  obtain ⟨hn0, hnd, hdn, hd3, hP⟩ := frame.child_facts
  have hodd := frame.child_num_odd
  have hpar : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hPpar := frame.T_even
  have hev' : (z.1 + z.2) % 2 = 0 := hev
  obtain ⟨hs1, hs2, ht1, ht2⟩ := frame.root_bounds hz hev
  have htlo := frame.t_le_neg_L hz hev hzF
  have hvs : frame.vSpectrum (frame.sGrade z) := hz.2.2
  have hsE : frame.sGrade z % 2 = 0 := by
    unfold ChildFrame.vSpectrum at hvs
    exact hvs.1
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * frame.child.num + v * frame.child.den = 1 := frame.child_reduced
  have hA := frame.ident_a z
  have hB := frame.ident_b z
  have hPgt := P_gt_L _ _ _ hn0 hdn hP
  have ht0 : frame.tGrade z ≠ 0 := by
    intro h0
    rw [h0] at hA hB
    obtain ⟨ha, hb⟩ := core_t0 hn0 hnd hdn hP hA hB hs1 hs2
    exact hzF (Prod.ext ha hb)
  have hs2' : 2 ≤ frame.sGrade z := by
    have hs0 : frame.sGrade z ≠ 0 := by
      intro h0
      rw [h0] at hA hB
      obtain ⟨ha, hb⟩ := core_s0 hn0 hdn hP ⟨u, v, huv⟩ hodd hA hB hev' ht1 ht2
      exact hzF (Prod.ext ha hb)
    omega
  have hlow := frame.lower_in_vBand hz hev hzF (δ := 1) (Or.inl rfl) (Or.inl rfl)
  have hlowcp : (z.1, z.2 - 1) ∈ frame.closedPolygon := ((frame.mem_vBand_iff _).mp hlow).1
  have tu : frame.tGrade (z.1 + 1, z.2 - 1) = frame.tGrade z + frame.child.num + frame.child.den := by
    unfold ChildFrame.tGrade; ring
  have su : frame.sGrade (z.1 + 1, z.2 - 1) = frame.sGrade z + 2 * frame.child.num := by
    unfold ChildFrame.sGrade; ring
  intro w hw hmem
  obtain ⟨i, j, rfl⟩ := hw
  have hspan : frame.child.modifiedDeck.combine i j ∈ frame.child.modifiedDeck.span := ⟨i, j, rfl⟩
  have hpE : EvenSite ((z.1 + 1, z.2 - 1) + frame.child.modifiedDeck.combine i j) :=
    (evenSite_add_span_iff frame _ hspan).mpr (by show (z.1 + 1 + (z.2 - 1)) % 2 = 0; omega)
  rcases hmem with ⟨hcp, hnot, hs⟩ | ⟨hcp, hnot, hs⟩
  · -- the H case: t-grades of the translate are `t + L - j P`, which avoid the H spectrum
    rw [tGrade_add_combine, tu] at hs
    unfold ChildFrame.hSpectrum at hs
    rcases lt_trichotomy j 0 with hj | hj | hj
    · have hjP : j * frame.child.periodDenominator ≤ -frame.child.periodDenominator := by
        nlinarith [mul_le_mul_of_nonneg_right (show j ≤ -1 by omega) (show (0:ℤ) ≤ frame.child.periodDenominator by omega)]
      rcases hs with ⟨-, -, h3⟩ | ⟨-, -, h3⟩ <;> linarith
    · subst hj
      simp only [zero_mul, sub_zero] at hs
      rcases hs with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩ <;> linarith
    · have hjP : frame.child.periodDenominator ≤ j * frame.child.periodDenominator := by
        nlinarith [mul_le_mul_of_nonneg_right (show (1:ℤ) ≤ j by omega) (show (0:ℤ) ≤ frame.child.periodDenominator by omega)]
      rcases hs with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩ <;> linarith
  · -- the V case: the translate has s-grade `s + 2n + i P` and lies in the polygon
    have hb := frame.cp_bounds_even hcp hpE
    rw [tGrade_add_combine, sGrade_add_combine, tu, su] at hb
    rw [sGrade_add_combine, su] at hs
    unfold ChildFrame.vSpectrum at hs
    obtain ⟨-, hs'⟩ := hs
    obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
    rcases lt_trichotomy i 0 with hi | hi | hi
    · have hiP : i * frame.child.periodDenominator ≤ -frame.child.periodDenominator := by
        nlinarith [mul_le_mul_of_nonneg_right (show i ≤ -1 by omega) (show (0:ℤ) ≤ frame.child.periodDenominator by omega)]
      linarith
    · subst hi
      simp only [zero_mul, add_zero] at hb1 hb2 hb3 hb4 hs'
      rcases lt_trichotomy j 0 with hj | hj | hj
      · have hjP : j * frame.child.periodDenominator ≤ -frame.child.periodDenominator := by
          nlinarith [mul_le_mul_of_nonneg_right (show j ≤ -1 by omega) (show (0:ℤ) ≤ frame.child.periodDenominator by omega)]
        linarith
      · subst hj
        have hc0 : frame.child.modifiedDeck.combine 0 0 = (0, 0) := by
          simp [PeriodDeck.combine]
        rw [hc0] at hnot
        simp only [Prod.mk_add_mk, add_zero] at hnot
        apply hnot
        convert hlowcp using 2
        all_goals simp
      · have hjP : frame.child.periodDenominator ≤ j * frame.child.periodDenominator := by
          nlinarith [mul_le_mul_of_nonneg_right (show (1:ℤ) ≤ j by omega) (show (0:ℤ) ≤ frame.child.periodDenominator by omega)]
        linarith
    · have hiP : frame.child.periodDenominator ≤ i * frame.child.periodDenominator := by
        nlinarith [mul_le_mul_of_nonneg_right (show (1:ℤ) ≤ i by omega) (show (0:ℤ) ≤ frame.child.periodDenominator by omega)]
      linarith

/-- The west diagonal `(z.1 - 1, z.2 + 1)` of an even free V root (not the origin, not `vLast`) is nonfree. -/
theorem nonfree_west_diag {z : Site} (hz : z ∈ frame.freeV) (hev : EvenSite z)
    (hzF : z ≠ FLatticePaper.Induction.vFirst) (hzL : z ≠ frame.vLast) :
    Nonfree frame (z.1 - 1, z.2 + 1) := by
  obtain ⟨hn0, hnd, hdn, hd3, hP⟩ := frame.child_facts
  have hodd := frame.child_num_odd
  have hpar : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hPpar := frame.T_even
  have hev' : (z.1 + z.2) % 2 = 0 := hev
  obtain ⟨hs1, hs2, ht1, ht2⟩ := frame.root_bounds hz hev
  have hpar_t := frame.tGrade_even hev
  have htlo := frame.t_le_neg_L hz hev hzF
  have hs2ne := frame.s_ne_two_n hz hev hzL
  have hPgt := P_gt_L _ _ _ hn0 hdn hP
  have hP0 : (0:ℤ) ≤ frame.child.periodDenominator := by omega
  have tu : frame.tGrade (z.1 - 1, z.2 + 1) = frame.tGrade z - (frame.child.num + frame.child.den) := by
    unfold ChildFrame.tGrade; ring
  have su : frame.sGrade (z.1 - 1, z.2 + 1) = frame.sGrade z - 2 * frame.child.num := by
    unfold ChildFrame.sGrade; ring
  intro w hw hmem
  obtain ⟨i, j, rfl⟩ := hw
  have hspan : frame.child.modifiedDeck.combine i j ∈ frame.child.modifiedDeck.span := ⟨i, j, rfl⟩
  have hpE : EvenSite ((z.1 - 1, z.2 + 1) + frame.child.modifiedDeck.combine i j) :=
    (evenSite_add_span_iff frame _ hspan).mpr (by show (z.1 - 1 + (z.2 + 1)) % 2 = 0; omega)
  have hcpall : (z.1 - 1, z.2 + 1) + frame.child.modifiedDeck.combine i j ∈ frame.closedPolygon := by
    rcases hmem with h | h
    · exact h.1
    · exact h.1
  have hb := frame.cp_bounds_even hcpall hpE
  rw [tGrade_add_combine, sGrade_add_combine, tu, su] at hb
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
  have hi1 : i = 1 := by
    rcases lt_trichotomy i 0 with hi | hi | hi
    · have hiP : i * frame.child.periodDenominator ≤ -frame.child.periodDenominator := by
        nlinarith [mul_le_mul_of_nonneg_right (show i ≤ -1 by omega) hP0]
      linarith
    · subst hi
      simp only [zero_mul, add_zero] at hb3
      exfalso
      apply hs2ne
      omega
    · by_contra hne
      have hi2 : 2 ≤ i := by omega
      have hiP : 2 * frame.child.periodDenominator ≤ i * frame.child.periodDenominator := by
        nlinarith [mul_le_mul_of_nonneg_right (show (2:ℤ) ≤ i by omega) hP0]
      linarith
  subst hi1
  rcases hmem with ⟨hcp, hnot, hs⟩ | ⟨hcp, hnot, hs⟩
  · -- the H case: only the translate with `j = -1` is in the polygon, and that needs `t ∉ [L-P+2, 2L-P-2]`
    rw [tGrade_add_combine, tu] at hs
    unfold ChildFrame.hSpectrum at hs
    rcases lt_trichotomy j (-1) with hj | hj | hj
    · have hjP : 2 * frame.child.periodDenominator ≤ -(j * frame.child.periodDenominator) := by
        nlinarith [mul_le_mul_of_nonneg_right (show j ≤ -2 by omega) hP0]
      linarith
    · subst hj
      rcases hs with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · exact frame.t_not_mid hz hev (by linarith) (by linarith)
      · exfalso
        omega
    · have hjP : 0 ≤ j * frame.child.periodDenominator := by
        nlinarith [mul_le_mul_of_nonneg_right (show (0:ℤ) ≤ j by omega) hP0]
      rcases hs with ⟨-, h2, -⟩ | ⟨-, h2, -⟩ <;> linarith
  · -- the V case: the translate's s-grade `s - 2n + P` lies in neither branch of the V spectrum
    rw [sGrade_add_combine, su, one_mul] at hs
    unfold ChildFrame.vSpectrum at hs
    obtain ⟨-, hs'⟩ := hs
    rcases hs' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith

/-- The `hX2` dichotomy at the diagonal, from the binary field. -/
theorem hX2_dichotomy {G : Field} (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0)
    {z : Site} (hz : z ∈ frame.freeV) (hev : EvenSite z) (hzF : z ≠ FLatticePaper.Induction.vFirst)
    {δ : ℤ} (hδ : δ = 1 ∨ δ = -1) (hδz : δ = 1 ∨ z ≠ frame.vLast) :
    laplacian G (z.1 + δ, z.2 - δ) = -1 ∨
      (laplacian G (z.1 + δ, z.2 - δ) = 0 ∧ Nonfree frame (z.1 + δ, z.2 - δ)) := by
  rcases hδ with rfl | rfl
  · have hnf := frame.nonfree_east_diag hz hev hzF
    exact (hbin _).imp id (fun h => ⟨h, hnf⟩)
  · have hzL : z ≠ frame.vLast := hδz.resolve_left (by norm_num)
    have hnf := frame.nonfree_west_diag hz hev hzF hzL
    have e1 : z.1 + -1 = z.1 - 1 := by ring
    have e2 : z.2 - -1 = z.2 + 1 := by ring
    rw [e1, e2]
    exact (hbin _).imp id (fun h => ⟨h, hnf⟩)

end ChildFrame

end FLatticePaper.Induction
