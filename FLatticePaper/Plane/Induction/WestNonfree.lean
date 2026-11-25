import FLatticePaper.Plane.Induction.WestException
import FLatticePaper.Plane.Induction.PriceInputs

/-! The exceptional vertex `v = V_p + I` is not free (`hNF` of `WestException`), and it is strictly interior (`hSI`).

With `n = 2N + p`, `d = 2D + q` (the parents `N/D`, `p/q` with `N q − D p = 1`), `T = d² + 2dn − n²`, and `v = (N−D+1, N+D−1)`:
the grades of `v` are `t v = n(N−D+1) − d(N+D−1)` and `s v = 2n + 2`; on the span `aU + bV` (`U = (d,n)`, `V = (n−d, n+d)`) the grades shift
by `t ↦ t − bT`, `s ↦ s + aT`. The strict-interior band of `t` is `(L−2−T, 2)` (`L = d + n`), so every free candidate is excluded by
the closed polygon bounds of `t` and `s`. -/

namespace FLatticePaper.WestNonfree

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.FreeClosure
open FLatticePaper.SquareClauses FLatticePaper.AndOrRank FLatticePaper.W1
open FLatticePaper.W1Phase FLatticePaper.W1MSheet FLatticePaper.W1Step FLatticePaper.W1ForcedPhase FLatticePaper.FreePolicy

/-- The `t`-grade of the exceptional vertex is below `2`. -/
theorem t_exc_lt (N D p q : ℤ) (hN : 1 ≤ N) (hND : N + 1 ≤ D) (hp : 0 ≤ p) (hq : 0 ≤ q) (hrel : N * q - D * p = 1) :
    (2 * N + p) * (N - D + 1) - (2 * D + q) * (N + D - 1) < 2 := by
  nlinarith [mul_nonneg hp hq, mul_nonneg (sub_nonneg.mpr hN) hp, mul_nonneg (sub_nonneg.mpr hND) hp,
    mul_nonneg (sub_nonneg.mpr hND) hq, mul_nonneg (sub_nonneg.mpr hN) hq]

/-- The `t`-grade of the exceptional vertex is above the lower strict-interior band `L − 2 − T`. -/
theorem t_exc_gt (N D p q : ℤ) (hN : 1 ≤ N) (hND : N + 1 ≤ D) (hp : 0 ≤ p) (hq : 0 ≤ q) (hrel : N * q - D * p = 1) :
    (2 * D + q) + (2 * N + p) - 2 - ((2 * D + q) ^ 2 + 2 * (2 * D + q) * (2 * N + p) - (2 * N + p) ^ 2)
      < (2 * N + p) * (N - D + 1) - (2 * D + q) * (N + D - 1) := by
  nlinarith [mul_nonneg hp hq, mul_nonneg (sub_nonneg.mpr hN) hp, mul_nonneg (sub_nonneg.mpr hND) hp,
    mul_nonneg (sub_nonneg.mpr hND) hq, mul_nonneg (sub_nonneg.mpr hN) hq]

/-- The `s`-grade of the exceptional vertex is `2n + 2`. -/
theorem s_exc (N D p q : ℤ) (hrel : N * q - D * p = 1) :
    (2 * D + q + (2 * N + p)) * (N - D + 1) + (2 * D + q - (2 * N + p)) * (N + D - 1) = 2 * (2 * N + p) + 2 := by
  linear_combination 2 * hrel

/-- `2n + 2 < T`, with `d ≥ n + 3` (from `N q − D p = 1`, `D ≥ N + 1`, `p, q ≥ 0`) and `n ≥ 2`. -/
theorem two_n_add_two_lt_T (N D p q : ℤ) (hN : 1 ≤ N) (hND : N + 1 ≤ D) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hrel : N * q - D * p = 1) :
    2 * (2 * N + p) + 2 < (2 * D + q) ^ 2 + 2 * (2 * D + q) * (2 * N + p) - (2 * N + p) ^ 2 := by
  have hqp : p + 1 ≤ q := by
    by_contra hc
    have hle : q ≤ p := by omega
    nlinarith [mul_le_mul_of_nonneg_left hle (by omega : (0:ℤ) ≤ N), mul_le_mul_of_nonneg_left (by omega : N + 1 ≤ D) hp]
  nlinarith [mul_nonneg hp hq, mul_nonneg (sub_nonneg.mpr hN) hp, mul_nonneg (sub_nonneg.mpr hND) hp,
    mul_nonneg (sub_nonneg.mpr hND) hq, mul_nonneg (sub_nonneg.mpr hN) hq]

/-- The `T` of the period denominator, in product form. -/
theorem periodDen_eq_prod (frame : ChildFrame) :
    frame.child.periodDenominator = frame.child.den * frame.child.den + 2 * frame.child.den * frame.child.num
      - frame.child.num * frame.child.num := by
  rw [ChildFrame.periodDenominator_eq_expr]
  ring

/-- A freeH candidate in the closed band is impossible: `t` is below `2` for `b ≥ 0`, and above `Lm` for `b < 0`. -/
theorem exc_H_false (t0 T Lm tz b : ℤ) (hT : 0 < T) (h1 : t0 < 2) (h2 : Lm - T < t0) (h2le : 2 ≤ tz)
    (hc2 : tz ≤ Lm) (hsh : tz = t0 - b * T) : False := by
  rcases le_or_gt 0 b with hb | hb
  · have : 0 ≤ b * T := mul_nonneg hb hT.le
    linarith
  · have : b * T ≤ -T := by nlinarith
    linarith

/-- The span coefficients of a free V candidate at the exceptional vertex are zero. -/
theorem exc_V_coeffs (t0 s0 T Lm n a b sz tz : ℤ) (hT : 0 < T) (hs0 : s0 = 2 * n + 2) (hsT : s0 < T)
    (h1 : t0 < 2) (h2 : Lm - T < t0) (hsz : sz = s0 + a * T) (htz : tz = t0 - b * T)
    (hs_lo : 0 ≤ sz) (hs_hi : sz ≤ T + 2 * n) (ht_lo : 2 - T ≤ tz) (ht_hi : tz ≤ Lm) : a = 0 ∧ b = 0 := by
  have ha : a = 0 := by
    rcases lt_trichotomy a 0 with ha | ha | ha
    · have : a * T ≤ -T := by nlinarith
      linarith
    · exact ha
    · have : T ≤ a * T := by nlinarith
      linarith
  subst ha
  have hb : b = 0 := by
    rcases lt_trichotomy b 0 with hb | hb | hb
    · have : b * T ≤ -T := by nlinarith
      linarith
    · exact hb
    · have : T ≤ b * T := by nlinarith
      linarith
  exact ⟨rfl, hb⟩

/-- The odd left neighbour of the exceptional vertex is in the closed band (its four bounds). -/
theorem exc_neighbour (t0 n d T s0 : ℤ) (hn : 2 ≤ n) (hnd : n + 2 ≤ d) (hs0 : s0 = 2 * n + 2)
    (h1 : t0 < 2) (h2 : d + n - 2 - T < t0) :
    n - T ≤ t0 - n ∧ t0 - n ≤ d ∧ 2 - d + n ≤ s0 - (d + n) ∧ s0 - (d + n) ≤ T + d + n - 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · linarith

/-- The exceptional vertex `v = (N − D + 1, N + D − 1)` of the odd parent, in the frame of the word. -/
abbrev excVertex (word : Word) : Site :=
  ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1,
    (frameAt word).parents.odd.num + (frameAt word).parents.odd.den - 1)

/-- **`hSI`**: under `ε = 1`, the exceptional vertex is strictly interior. -/
theorem strictInterior_exc {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (heps : (frameAt word).eps = 1) :
    FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den (excVertex word) := by
  obtain ⟨hN1, hND, hD2, hnq, hdq, hn_eq, hd_eq, heps', -⟩ := FLatticePaper.PriceInputs.pdata h
  have hrel : (frameAt word).parents.odd.num * (frameAt word).parents.even.den
      - (frameAt word).parents.odd.den * (frameAt word).parents.even.num = 1 := by
    have := heps'.symm.trans heps
    linarith [mul_comm (frameAt word).parents.even.num (frameAt word).parents.odd.den]
  have hev : EvenSite (excVertex word) := by
    unfold EvenSite excVertex
    have e : ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1 +
        ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den - 1)) = 2 * (frameAt word).parents.odd.num := by ring
    simp only [e]
    omega
  unfold FLatticePaper.W1.StrictInterior FLatticePaper.W1.w1b FLatticePaper.W1.w1a FLatticePaper.W1.w1h
    FLatticePaper.W1.w1c FLatticePaper.W1.w1t FLatticePaper.W1.w1s FLatticePaper.W1.w1T
  rw [if_pos hev, if_pos hev, if_pos hev, if_pos hev, hn_eq, hd_eq]
  have h1 := t_exc_gt _ _ _ _ hN1 hND (by omega) (by omega) hrel
  have h2 := t_exc_lt _ _ _ _ hN1 hND (by omega) (by omega) hrel
  have h3 := s_exc _ _ _ _ hrel
  have h4 := two_n_add_two_lt_T _ _ _ _ hN1 hND (by omega) (by omega) hrel
  unfold excVertex at *
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem evenSite_add' {x y : Site} (hx : EvenSite x) (hy : EvenSite y) : EvenSite (x + y) := by
  unfold EvenSite at *
  simp only [Prod.fst_add, Prod.snd_add]
  omega

/-- The `t`-grade along a span element: `t(x + aU + bV) = t(x) − b T`. -/
theorem tGrade_add_combine (frame : ChildFrame) (x : Site) (a b : ℤ) :
    frame.tGrade (x + frame.child.modifiedDeck.combine a b) =
      frame.tGrade x - b * (frame.child.den * frame.child.den + 2 * frame.child.den * frame.child.num
        - frame.child.num * frame.child.num) := by
  rw [ChildFrame.combine_coords]
  unfold ChildFrame.tGrade
  simp only [Prod.fst_add, Prod.snd_add]
  ring

/-- The `s`-grade along a span element: `s(x + aU + bV) = s(x) + a T`. -/
theorem sGrade_add_combine (frame : ChildFrame) (x : Site) (a b : ℤ) :
    frame.sGrade (x + frame.child.modifiedDeck.combine a b) =
      frame.sGrade x + a * (frame.child.den * frame.child.den + 2 * frame.child.den * frame.child.num
        - frame.child.num * frame.child.num) := by
  rw [ChildFrame.combine_coords]
  unfold ChildFrame.sGrade
  simp only [Prod.fst_add, Prod.snd_add]
  ring

/-- The `t`-grade of the left neighbour `(x.1 − 1, x.2)` is `t(x) − n`. -/
theorem tGrade_sub_one (frame : ChildFrame) (x : Site) :
    frame.tGrade (x.1 - 1, x.2) = frame.tGrade x - frame.child.num := by
  unfold ChildFrame.tGrade
  ring

/-- The `s`-grade of the left neighbour `(x.1 − 1, x.2)` is `s(x) − (d + n)`. -/
theorem sGrade_sub_one (frame : ChildFrame) (x : Site) :
    frame.sGrade (x.1 - 1, x.2) = frame.sGrade x - (frame.child.den + frame.child.num) := by
  unfold ChildFrame.sGrade
  ring

/-- **`hNF`**: under `ε = 1`, no span translate of the exceptional vertex is free (H or V). -/
theorem not_freeClosure_exceptional {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (heps : (frameAt word).eps = 1) :
    ¬ freeClosure (frameAt word) (excVertex word) := by
  obtain ⟨hN1, hND, hD2, hnq, hdq, hn_eq, hd_eq, heps', -⟩ := FLatticePaper.PriceInputs.pdata h
  have hrel : (frameAt word).parents.odd.num * (frameAt word).parents.even.den
      - (frameAt word).parents.odd.den * (frameAt word).parents.even.num = 1 := by
    have := heps'.symm.trans heps
    linarith [mul_comm (frameAt word).parents.even.num (frameAt word).parents.odd.den]
  have hn2 : 2 ≤ (frameAt word).child.num := by omega
  have hnd : (frameAt word).child.num + 2 ≤ (frameAt word).child.den := by
    have := (frameAt word).child_facts.2.2.1
    omega
  have hvE : EvenSite (excVertex word) := by
    unfold EvenSite excVertex
    have e : ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1 +
        ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den - 1)) = 2 * (frameAt word).parents.odd.num := by ring
    simp only [e]
    omega
  -- the grade facts of the exceptional vertex
  have F1 : (frameAt word).tGrade (excVertex word) < 2 := by
    simp only [ChildFrame.tGrade]
    rw [hn_eq, hd_eq]
    exact t_exc_lt _ _ _ _ hN1 hND (by omega) (by omega) hrel
  have F2 : (frameAt word).child.den + (frameAt word).child.num - 2 -
      ((frameAt word).child.den * (frameAt word).child.den + 2 * (frameAt word).child.den * (frameAt word).child.num
        - (frameAt word).child.num * (frameAt word).child.num) < (frameAt word).tGrade (excVertex word) := by
    have := t_exc_gt _ _ _ _ hN1 hND (by omega) (by omega) hrel
    simp only [ChildFrame.tGrade]
    rw [hn_eq, hd_eq]
    nlinarith [this]
  have F3 : (frameAt word).sGrade (excVertex word) = 2 * (frameAt word).child.num + 2 := by
    have := s_exc _ _ _ _ hrel
    simp only [ChildFrame.sGrade]
    rw [hn_eq, hd_eq]
    linarith [this]
  have F4 : 2 * (frameAt word).child.num + 2 <
      (frameAt word).child.den * (frameAt word).child.den + 2 * (frameAt word).child.den * (frameAt word).child.num
        - (frameAt word).child.num * (frameAt word).child.num := by
    have := two_n_add_two_lt_T _ _ _ _ hN1 hND (by omega) (by omega) hrel
    rw [hn_eq, hd_eq]
    nlinarith [this]
  intro hfc
  obtain ⟨sp, hsp, hmem⟩ := hfc
  obtain ⟨a, b, rfl⟩ := hsp
  have hzE : EvenSite (excVertex word + (frameAt word).child.modifiedDeck.combine a b) :=
    evenSite_add' hvE ((frameAt word).evenSite_combine a b)
  have Ht := tGrade_add_combine (frameAt word) (excVertex word) a b
  have Hs := sGrade_add_combine (frameAt word) (excVertex word) a b
  rcases hmem with hH | hV
  · -- freeH
    obtain ⟨hcp, -, hspc⟩ := hH
    simp only [ChildFrame.closedPolygon, Set.mem_setOf_eq] at hcp
    rw [if_pos hzE, periodDen_eq_prod] at hcp
    obtain ⟨-, c2, -, -⟩ := hcp
    unfold ChildFrame.hSpectrum at hspc
    rw [Ht] at c2 hspc
    have hT0 : 0 < (frameAt word).child.den * (frameAt word).child.den + 2 * (frameAt word).child.den * (frameAt word).child.num
        - (frameAt word).child.num * (frameAt word).child.num := by linarith
    rcases hspc with ⟨-, h1', -⟩ | ⟨-, h1', -⟩
    · exact exc_H_false _ _ _ _ _ hT0 F1 F2 h1' c2 rfl
    · exact exc_H_false _ _ _ _ _ hT0 F1 F2 (le_trans hn2 h1') c2 rfl
  · -- freeV
    obtain ⟨hcp, hnb, -⟩ := hV
    simp only [ChildFrame.closedPolygon, Set.mem_setOf_eq] at hcp
    rw [if_pos hzE, periodDen_eq_prod] at hcp
    obtain ⟨c1, c2, c3, c4⟩ := hcp
    have hT0 : 0 < (frameAt word).child.den * (frameAt word).child.den + 2 * (frameAt word).child.den * (frameAt word).child.num
        - (frameAt word).child.num * (frameAt word).child.num := by linarith
    have hsT : (frameAt word).sGrade (excVertex word) < (frameAt word).child.den * (frameAt word).child.den
        + 2 * (frameAt word).child.den * (frameAt word).child.num - (frameAt word).child.num * (frameAt word).child.num := by
      rw [F3]; linarith
    obtain ⟨ha, hb⟩ := exc_V_coeffs _ _ _ _ _ _ _ _ _ hT0 F3 hsT F1 F2 Hs Ht c3 c4 c1 c2
    subst ha
    subst hb
    apply hnb
    have hodd : ¬ EvenSite ((excVertex word + (frameAt word).child.modifiedDeck.combine 0 0).1 - 1,
        (excVertex word + (frameAt word).child.modifiedDeck.combine 0 0).2) := by
      unfold EvenSite at hzE ⊢
      simp only [Prod.fst_add, Prod.snd_add] at hzE ⊢
      omega
    simp only [ChildFrame.closedPolygon, Set.mem_setOf_eq]
    rw [if_neg hodd, periodDen_eq_prod, tGrade_sub_one, sGrade_sub_one, Ht, Hs]
    obtain ⟨k1, k2, k3, k4⟩ := exc_neighbour _ _ _ _ _ hn2 hnd F3 F1 F2
    simp only [zero_mul, sub_zero, add_zero]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **`hwest`, with the geometric leaves discharged**: under `ε = 1`, the free policy of the word retains the west input at the
exceptional vertex, given the parent's retained south image (`hSouth`), the W1 square data and a satisfying selection. -/
theorem hwest_of_south {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hWord : StrongEstimates word)
    {seed : Site → Site → Prop}
    (P : OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hsq : ∀ c : Site, FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      laplacian (MW word) c = 0 → ∃ a b : ℤ,
        c ∈ squareCorners a b ∧ (∀ c' ∈ squareCorners a b, FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c') ∧
        sheetOut P (frameAt word).sheetShift (frameAt word).centre (sheetPsi word) c ∉ squareCorners a b ∧
        (∀ c' ∈ squareCorners a b, c' ≠ c → laplacian (MW word) c' = -1 ∨
          (laplacian (MW word) c' = 0 ∧
            sheetOut P (frameAt word).sheetShift (frameAt word).centre (sheetPsi word) c' ∈ squareCorners a b)) ∧
        (∀ c' ∈ squareCorners a b, c' ≠ c → laplacian (MW word) c' = 0 →
          PhaseOK (sheetPsi word) c c' ∧
            Relation.TransGen (phasePolicy (sheetPsi word)
              (sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift)
              (sheetPolicyC P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift (frameAt word).centre) c) c' c))
    (heps : (frameAt word).eps = 1)
    (hSouth : sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift (excVertex word)
      (incomingNeg (excVertex word)))
    (hsat : HasSatSelection (standardField word)) (η : ℤ) :
    freePolicy (frameAt word) (standardField word) η (excVertex word) (incomingNeg (excVertex word)) :=
  WestException.hwest_freePolicy h hSE hWord P hsq heps (strictInterior_exc h heps) hSouth
    (not_freeClosure_exceptional h heps) hsat η

end FLatticePaper.WestNonfree
