import FLatticePaper.Tiles.BaseTwoOdd
import FLatticePaper.Tiles.BaseVertVp
import FLatticePaper.Tiles.BaseVertOdoFamily
import FLatticePaper.Tiles.RegisterLink
import FLatticePaper.Tiles.AltRotStep
import FLatticePaper.Tiles.BaseTileProps
import FLatticePaper.Tiles.TexVPositions
import FLatticePaper.Tiles.StandardClauseA
import FLatticePaper.Construction.NearOneBaseCases

/-! # The vertical base pieces of the even `2^k` word (`k ≥ 1`): the closed forms

The vertical word of the even child of `2^k` is `p q^k p q^(k+1)`, its anchor is `(2k+2, 2k)`. The forward family has affine
factors `(j-1, -j)` for `1 ≤ j ≤ k`, `(j-2, -j)` for `k+2 ≤ j ≤ 2k+2`, and positions `(0,2j)` for `j ≤ k` and `(-1, 2j-1)` for
`k+1 ≤ j ≤ 2k+2`; the reversed family has affine factors `(j, -j)` for `j ≤ k+1` and `(j-1, -j)` for `k+2 ≤ j ≤ 2k+2`. -/

namespace FLatticePaper.Tiles.BaseTwoEven

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Tiles.BaseVertOdo FLatticePaper.Tiles.BaseVertOdoFamily FLatticePaper.Tiles.BaseVertVp
open FLatticePaper.Tiles.StandardClause

/-- The word `p q^k p q^(k+1)`, the vertical word of the even child of `2^k`. -/
abbrev W4 (k : ℕ) : BinaryWord :=
  Letter.p :: (List.replicate k Letter.q ++ Letter.p :: List.replicate (k + 1) Letter.q)

theorem wv_even2 (k : ℕ) : vWordOf (List.replicate k Digit.two) true = W4 k := by
  unfold vWordOf
  rw [FLatticePaper.Tiles.AltRotStep.swapW_replicate_two, if_pos rfl,
    (FLatticePaper.Tiles.RegisterLink.quad_threes k).1]
  simp [W4, List.map_append, swapLetter, List.map_replicate]

theorem anchor_even2 (k : ℕ) :
    lastPosOf (hStringAt (hWordOf (List.replicate k Digit.two) true) (0, 0)) = (2 * (k : ℤ) + 2, 2 * (k : ℤ)) := by
  rw [TexVPositions.lastPos_hWordOf_true_tex]
  unfold fracEven
  rw [BaseTileProps.parents_two]
  unfold texV1Even
  simp only [Parents.current, Parents.combine]
  ext
  all_goals simp
  all_goals ring

theorem hz0 : letterZTile Letter.p = ZTile.zero := rfl

theorem hz1 : letterZTile Letter.q = ZTile.one := rfl

/-! ### The letters of `W4 k` -/

theorem getD_app_cons (n : ℕ) (L : List Letter) (i : ℕ) :
    (List.replicate n Letter.q ++ Letter.p :: L).getD i Letter.p =
      if i < n then Letter.q else if i = n then Letter.p else L.getD (i - n - 1) Letter.p := by
  induction n generalizing i with
  | zero =>
    cases i with
    | zero => simp
    | succ j => simp
  | succ n ih =>
    cases i with
    | zero => simp
    | succ j =>
      rw [List.replicate_succ, List.cons_append, List.getD_cons_succ, ih j]
      have e : j + 1 - (n + 1) - 1 = j - n - 1 := by omega
      rw [e]
      split_ifs <;> first | rfl | (exfalso; omega)

theorem lf4 (k j : ℕ) :
    lettersOf (W4 k) false j = if j = 0 ∨ j = k + 1 ∨ 2 * k + 3 ≤ j then Letter.p else Letter.q := by
  unfold lettersOf
  cases j with
  | zero => simp [W4]
  | succ i =>
    simp only [W4, Bool.false_eq_true, if_false]
    rw [List.getD_cons_succ, getD_app_cons, FLatticePaper.Tiles.BaseTwoOdd.getD_rep_q]
    by_cases h1 : i < k
    · rw [if_pos h1, if_neg (show ¬(i + 1 = 0 ∨ i + 1 = k + 1 ∨ 2 * k + 3 ≤ i + 1) by omega)]
    · by_cases h2 : i = k
      · rw [if_neg h1, if_pos h2, if_pos (show i + 1 = 0 ∨ i + 1 = k + 1 ∨ 2 * k + 3 ≤ i + 1 by omega)]
      · rw [if_neg h1, if_neg h2]
        by_cases h3 : i - k - 1 < k + 1
        · rw [if_pos h3, if_neg (show ¬(i + 1 = 0 ∨ i + 1 = k + 1 ∨ 2 * k + 3 ≤ i + 1) by omega)]
        · rw [if_neg h3, if_pos (show i + 1 = 0 ∨ i + 1 = k + 1 ∨ 2 * k + 3 ≤ i + 1 by omega)]

theorem lr4 (k j : ℕ) :
    lettersOf (W4 k) true j = if j ≤ k ∨ (k + 2 ≤ j ∧ j ≤ 2 * k + 1) then Letter.q else Letter.p := by
  have hr : (W4 k).reverse = List.replicate (k + 1) Letter.q ++ Letter.p :: (List.replicate k Letter.q ++ [Letter.p]) := by
    simp [W4, List.reverse_cons, List.reverse_append, List.reverse_replicate]
  unfold lettersOf
  simp only [if_true]
  rw [hr, getD_app_cons, getD_app_cons]
  simp only [List.getD_nil]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hfq4 (k n : ℕ) (h1 : 1 ≤ n) (hk : n ≤ k) : lettersOf (W4 k) false n = Letter.q := by
  rw [lf4, if_neg (show ¬(n = 0 ∨ n = k + 1 ∨ 2 * k + 3 ≤ n) by omega)]

theorem hfq4' (k n : ℕ) (h1 : k + 2 ≤ n) (hk : n ≤ 2 * k + 2) : lettersOf (W4 k) false n = Letter.q := by
  rw [lf4, if_neg (show ¬(n = 0 ∨ n = k + 1 ∨ 2 * k + 3 ≤ n) by omega)]

theorem hfp4 (k : ℕ) : lettersOf (W4 k) false (k + 1) = Letter.p := by
  rw [lf4, if_pos (show (k + 1 = 0 ∨ k + 1 = k + 1 ∨ 2 * k + 3 ≤ k + 1) from Or.inr (Or.inl rfl))]

theorem hfp40 (k : ℕ) : lettersOf (W4 k) false 0 = Letter.p := by
  rw [lf4, if_pos (show (0 = 0 ∨ 0 = k + 1 ∨ 2 * k + 3 ≤ 0) from Or.inl rfl)]

theorem hrq4 (k n : ℕ) (h : n ≤ k) : lettersOf (W4 k) true n = Letter.q := by
  rw [lr4, if_pos (show n ≤ k ∨ (k + 2 ≤ n ∧ n ≤ 2 * k + 1) from Or.inl h)]

theorem hrq4' (k n : ℕ) (h1 : k + 2 ≤ n) (h2 : n ≤ 2 * k + 1) : lettersOf (W4 k) true n = Letter.q := by
  rw [lr4, if_pos (show n ≤ k ∨ (k + 2 ≤ n ∧ n ≤ 2 * k + 1) from Or.inr ⟨h1, h2⟩)]

theorem hrp4 (k n : ℕ) (h : n = k + 1 ∨ n = 2 * k + 2) : lettersOf (W4 k) true n = Letter.p := by
  rw [lr4, if_neg (show ¬(n ≤ k ∨ (k + 2 ≤ n ∧ n ≤ 2 * k + 1)) by omega)]

/-! ### The forward positions -/

theorem posF4_low (k : ℕ) : ∀ j : ℕ, j ≤ k →
    posF .vertical false (lettersOf (W4 k) false) j = (0, 2 * (j : ℤ)) := by
  intro j
  induction j with
  | zero => intro _; simp [posF]; rfl
  | succ n ih =>
    intro hn
    rw [show posF .vertical false (lettersOf (W4 k) false) (n + 1)
        = posF .vertical false (lettersOf (W4 k) false) n
          + stepOf .vertical false (lettersOf (W4 k) false n) (lettersOf (W4 k) false (n + 1)) from rfl,
      ih (by omega), hfq4 k (n + 1) (by omega) hn]
    simp only [stepOf, zeroOneVerticalStep]
    ext
    all_goals simp
    all_goals ring

theorem posF4_mid (k : ℕ) : ∀ j : ℕ, k + 1 ≤ j → j ≤ 2 * k + 2 →
    posF .vertical false (lettersOf (W4 k) false) j = (-1, 2 * (j : ℤ) - 1) := by
  intro j
  induction j with
  | zero => intro h1 _; omega
  | succ n ih =>
    intro h1 h2
    by_cases hn : n + 1 = k + 1
    · rw [hn]
      rw [show posF .vertical false (lettersOf (W4 k) false) (k + 1)
          = posF .vertical false (lettersOf (W4 k) false) k
            + stepOf .vertical false (lettersOf (W4 k) false k) (lettersOf (W4 k) false (k + 1)) from rfl,
        posF4_low k k le_rfl, hfp4 k]
      simp only [stepOf, zeroOneVerticalStep]
      ext
      all_goals simp
      all_goals ring
    · have ih' := ih (by omega) (by omega)
      rw [show posF .vertical false (lettersOf (W4 k) false) (n + 1)
          = posF .vertical false (lettersOf (W4 k) false) n
            + stepOf .vertical false (lettersOf (W4 k) false n) (lettersOf (W4 k) false (n + 1)) from rfl,
        ih', hfq4' k (n + 1) (by omega) h2]
      simp only [stepOf, zeroOneVerticalStep]
      ext
      all_goals simp
      all_goals ring

/-! ### The forward affine factors -/

theorem vtCnt4f (k : ℕ) : ∀ j : ℕ, j ≤ 2 * k + 1 →
    vtCnt (lettersOf (W4 k) false) (j + 1) = if j ≤ k then (j : ℤ) else (j : ℤ) - 1 := by
  intro j
  induction j with
  | zero => intro _; simp [vtCnt, hfp40]
  | succ n ih =>
    intro hn
    rw [show vtCnt (lettersOf (W4 k) false) (n + 1 + 1)
        = vtCnt (lettersOf (W4 k) false) (n + 1)
          + (if lettersOf (W4 k) false (n + 1) = Letter.q then 1 else 0) from rfl, ih (by omega)]
    by_cases h1 : n + 1 ≤ k
    · rw [hfq4 k (n + 1) (by omega) h1, if_pos (show n ≤ k by omega), if_pos h1]
      simp
    · by_cases h2 : n = k
      · rw [h2, hfp4 k, if_pos (le_refl k), if_neg (show ¬(k + 1 ≤ k) by omega)]
        simp
      · rw [hfq4' k (n + 1) (by omega) (by omega), if_neg (show ¬(n ≤ k) by omega), if_neg h1]
        norm_num

theorem vtAff4f_low (k j : ℕ) (hj1 : 1 ≤ j) (hjk : j ≤ k + 1) :
    vtAff (lettersOf (W4 k) false) j = ((j : ℤ) - 1, -(j : ℤ)) := by
  obtain ⟨p, rfl⟩ : ∃ p, j = p + 1 := ⟨j - 1, by omega⟩
  have hc := vtCnt4f k p (by omega)
  simp only [vtAff]
  rw [hc, if_pos (show p ≤ k by omega)]
  exact Prod.ext (by push_cast; ring) rfl

theorem vtAff4f_high (k j : ℕ) (hj1 : k + 2 ≤ j) (hjk : j ≤ 2 * k + 2) :
    vtAff (lettersOf (W4 k) false) j = ((j : ℤ) - 2, -(j : ℤ)) := by
  obtain ⟨p, rfl⟩ : ∃ p, j = p + 1 := ⟨j - 1, by omega⟩
  have hc := vtCnt4f k p (by omega)
  simp only [vtAff]
  rw [hc, if_neg (show ¬(p ≤ k) by omega)]
  exact Prod.ext (by push_cast; ring) rfl

/-! ### The forward constants -/

theorem vtCP4f_low (k : ℕ) : ∀ n : ℕ, n + 1 ≤ k →
    vtCP (lettersOf (W4 k) false) (n + 1) = 1 - ((n : ℤ) + 1) - ((n : ℤ) + 1) * ((n : ℤ) + 1) := by
  intro n
  induction n with
  | zero =>
    intro _
    rw [show vtCP (lettersOf (W4 k) false) (0 + 1)
        = vtCP (lettersOf (W4 k) false) 0 + vtBetaP (lettersOf (W4 k) false 0) (lettersOf (W4 k) false 1)
          + ptDot (vtAff (lettersOf (W4 k) false) 0) (zeroOneVerticalStep (lettersOf (W4 k) false 1)) from rfl,
      hfp40, hfq4 k 1 le_rfl (by omega)]
    simp [vtCP, vtAff, vtCnt, vtBetaP, zeroOneVerticalStep, ptDot]
  | succ n ih =>
    intro hn
    rw [show vtCP (lettersOf (W4 k) false) (n + 1 + 1)
        = vtCP (lettersOf (W4 k) false) (n + 1)
          + vtBetaP (lettersOf (W4 k) false (n + 1)) (lettersOf (W4 k) false (n + 1 + 1))
          + ptDot (vtAff (lettersOf (W4 k) false) (n + 1))
            (zeroOneVerticalStep (lettersOf (W4 k) false (n + 1 + 1))) from rfl,
      hfq4 k (n + 1) (by omega) (by omega), hfq4 k (n + 1 + 1) (by omega) (by omega), ih (by omega)]
    have hA : vtAff (lettersOf (W4 k) false) (n + 1) = ((n : ℤ), -((n : ℤ) + 1)) := by
      rw [vtAff4f_low k (n + 1) (by omega) (by omega)]
      push_cast
      exact Prod.ext (by ring) rfl
    rw [hA]
    simp only [vtBetaP, zeroOneVerticalStep, ptDot]
    push_cast
    ring

theorem vtCP4f_k1 (k : ℕ) (hk : 1 ≤ k) :
    vtCP (lettersOf (W4 k) false) (k + 1) = -((k : ℤ) * (k : ℤ)) - 3 * (k : ℤ) := by
  obtain ⟨p, rfl⟩ : ∃ p, k = p + 1 := ⟨k - 1, by omega⟩
  rw [show vtCP (lettersOf (W4 (p + 1)) false) (p + 1 + 1)
      = vtCP (lettersOf (W4 (p + 1)) false) (p + 1)
        + vtBetaP (lettersOf (W4 (p + 1)) false (p + 1)) (lettersOf (W4 (p + 1)) false (p + 1 + 1))
        + ptDot (vtAff (lettersOf (W4 (p + 1)) false) (p + 1))
          (zeroOneVerticalStep (lettersOf (W4 (p + 1)) false (p + 1 + 1))) from rfl]
  rw [hfq4 (p + 1) (p + 1) (by omega) le_rfl, hfp4 (p + 1), vtCP4f_low (p + 1) p (by omega),
    vtAff4f_low (p + 1) (p + 1) (by omega) (by omega)]
  simp only [vtBetaP, zeroOneVerticalStep, ptDot]
  push_cast
  ring

theorem vtCP4f_high (k : ℕ) (hk : 1 ≤ k) : ∀ j : ℕ, k + 2 ≤ j → j ≤ 2 * k + 2 →
    vtCP (lettersOf (W4 k) false) j = 3 - (j : ℤ) - (j : ℤ) * (j : ℤ) := by
  intro j
  induction j with
  | zero => intro h _; omega
  | succ n ih =>
    intro h1 h2
    by_cases hn : n + 1 = k + 2
    · rw [hn]
      rw [show vtCP (lettersOf (W4 k) false) (k + 2)
          = vtCP (lettersOf (W4 k) false) (k + 1)
            + vtBetaP (lettersOf (W4 k) false (k + 1)) (lettersOf (W4 k) false (k + 2))
            + ptDot (vtAff (lettersOf (W4 k) false) (k + 1))
              (zeroOneVerticalStep (lettersOf (W4 k) false (k + 2))) from rfl,
        hfp4 k, hfq4' k (k + 2) le_rfl (by omega), vtCP4f_k1 k hk, vtAff4f_low k (k + 1) (by omega) le_rfl]
      simp only [vtBetaP, zeroOneVerticalStep, ptDot]
      push_cast
      ring
    · have ih' := ih (by omega) (by omega)
      rw [show vtCP (lettersOf (W4 k) false) (n + 1)
          = vtCP (lettersOf (W4 k) false) n
            + vtBetaP (lettersOf (W4 k) false n) (lettersOf (W4 k) false (n + 1))
            + ptDot (vtAff (lettersOf (W4 k) false) n)
              (zeroOneVerticalStep (lettersOf (W4 k) false (n + 1))) from rfl,
        ih', hfq4' k n (by omega) (by omega), hfq4' k (n + 1) (by omega) h2,
        vtAff4f_high k n (by omega) (by omega)]
      simp only [vtBetaP, zeroOneVerticalStep, ptDot]
      push_cast
      ring

/-! ### The reversed affine factors and constants -/

theorem vtCnt4r (k : ℕ) : ∀ j : ℕ, j ≤ k + 1 →
    vtCnt (lettersOf (W4 k) true) j = (j : ℤ) := by
  intro j
  induction j with
  | zero => intro _; simp [vtCnt]
  | succ n ih =>
    intro hn
    rw [show vtCnt (lettersOf (W4 k) true) (n + 1)
        = vtCnt (lettersOf (W4 k) true) n + (if lettersOf (W4 k) true n = Letter.q then 1 else 0) from rfl,
      ih (by omega), hrq4 k n (by omega)]
    simp

theorem vtCnt4r_high (k : ℕ) : ∀ j : ℕ, k + 2 ≤ j → j ≤ 2 * k + 2 →
    vtCnt (lettersOf (W4 k) true) j = (j : ℤ) - 1 := by
  intro j
  induction j with
  | zero => intro h _; omega
  | succ n ih =>
    intro h1 h2
    by_cases hn : n + 1 = k + 2
    · rw [hn]
      rw [show vtCnt (lettersOf (W4 k) true) (k + 2)
          = vtCnt (lettersOf (W4 k) true) (k + 1) + (if lettersOf (W4 k) true (k + 1) = Letter.q then 1 else 0)
          from rfl, vtCnt4r k (k + 1) le_rfl, hrp4 k (k + 1) (Or.inl rfl)]
      simp
      ring
    · have ih' := ih (by omega) (by omega)
      rw [show vtCnt (lettersOf (W4 k) true) (n + 1)
          = vtCnt (lettersOf (W4 k) true) n + (if lettersOf (W4 k) true n = Letter.q then 1 else 0) from rfl,
        ih', hrq4' k n (by omega) (by omega)]
      simp

theorem vtAff4r_low (k j : ℕ) (hj : j ≤ k + 1) :
    vtAff (lettersOf (W4 k) true) j = ((j : ℤ), -(j : ℤ)) := by
  simp only [vtAff, vtCnt4r k j hj]

theorem vtAff4r_high (k j : ℕ) (h1 : k + 2 ≤ j) (h2 : j ≤ 2 * k + 2) :
    vtAff (lettersOf (W4 k) true) j = ((j : ℤ) - 1, -(j : ℤ)) := by
  simp only [vtAff, vtCnt4r_high k j h1 h2]

theorem vtCM4r_low (k : ℕ) : ∀ j : ℕ, j ≤ k →
    vtCM (lettersOf (W4 k) true) j = -((j : ℤ) * ((j : ℤ) + 1)) := by
  intro j
  induction j with
  | zero => intro _; simp [vtCM]
  | succ n ih =>
    intro hn
    rw [show vtCM (lettersOf (W4 k) true) (n + 1)
        = vtCM (lettersOf (W4 k) true) n
          + vtBetaM (lettersOf (W4 k) true n) (lettersOf (W4 k) true (n + 1))
          + ptDot (vtAff (lettersOf (W4 k) true) n)
            (zeroOneVerticalReversedStep (lettersOf (W4 k) true n) (lettersOf (W4 k) true (n + 1))) from rfl,
      ih (by omega), hrq4 k n (by omega), hrq4 k (n + 1) hn, vtAff4r_low k n (by omega)]
    simp only [vtBetaM, zeroOneVerticalReversedStep, ptDot]
    push_cast
    ring

theorem vtCM4r_mid (k : ℕ) : vtCM (lettersOf (W4 k) true) (k + 1) = -(((k : ℤ) + 1) * ((k : ℤ) + 1)) := by
  rw [show vtCM (lettersOf (W4 k) true) (k + 1)
      = vtCM (lettersOf (W4 k) true) k
        + vtBetaM (lettersOf (W4 k) true k) (lettersOf (W4 k) true (k + 1))
        + ptDot (vtAff (lettersOf (W4 k) true) k)
          (zeroOneVerticalReversedStep (lettersOf (W4 k) true k) (lettersOf (W4 k) true (k + 1))) from rfl,
    vtCM4r_low k k le_rfl, hrq4 k k le_rfl, hrp4 k (k + 1) (Or.inl rfl), vtAff4r_low k k (by omega)]
  simp only [vtBetaM, zeroOneVerticalReversedStep, ptDot]
  ring

theorem vtCM4r_high (k : ℕ) (hk : 1 ≤ k) : ∀ j : ℕ, k + 2 ≤ j → j ≤ 2 * k + 1 →
    vtCM (lettersOf (W4 k) true) j = 1 - (j : ℤ) * ((j : ℤ) + 1) := by
  intro j
  induction j with
  | zero => intro h _; omega
  | succ n ih =>
    intro h1 h2
    by_cases hn : n + 1 = k + 2
    · rw [hn]
      rw [show vtCM (lettersOf (W4 k) true) (k + 2)
          = vtCM (lettersOf (W4 k) true) (k + 1)
            + vtBetaM (lettersOf (W4 k) true (k + 1)) (lettersOf (W4 k) true (k + 2))
            + ptDot (vtAff (lettersOf (W4 k) true) (k + 1))
              (zeroOneVerticalReversedStep (lettersOf (W4 k) true (k + 1)) (lettersOf (W4 k) true (k + 2))) from rfl,
        vtCM4r_mid k, hrp4 k (k + 1) (Or.inl rfl), hrq4' k (k + 2) le_rfl (by omega),
        vtAff4r_low k (k + 1) le_rfl]
      simp only [vtBetaM, zeroOneVerticalReversedStep, ptDot]
      push_cast
      ring
    · have ih' := ih (by omega) (by omega)
      rw [show vtCM (lettersOf (W4 k) true) (n + 1)
          = vtCM (lettersOf (W4 k) true) n
            + vtBetaM (lettersOf (W4 k) true n) (lettersOf (W4 k) true (n + 1))
            + ptDot (vtAff (lettersOf (W4 k) true) n)
              (zeroOneVerticalReversedStep (lettersOf (W4 k) true n) (lettersOf (W4 k) true (n + 1))) from rfl,
        ih', hrq4' k n (by omega) (by omega), hrq4' k (n + 1) (by omega) (by omega),
        vtAff4r_high k n (by omega) (by omega)]
      simp only [vtBetaM, zeroOneVerticalReversedStep, ptDot]
      push_cast
      ring

theorem vtCM4r_last (k : ℕ) (hk : 1 ≤ k) :
    vtCM (lettersOf (W4 k) true) (2 * k + 2) = 1 - (2 * (k : ℤ) + 2) * (2 * (k : ℤ) + 2) := by
  rw [show vtCM (lettersOf (W4 k) true) (2 * k + 2)
      = vtCM (lettersOf (W4 k) true) (2 * k + 1)
        + vtBetaM (lettersOf (W4 k) true (2 * k + 1)) (lettersOf (W4 k) true (2 * k + 2))
        + ptDot (vtAff (lettersOf (W4 k) true) (2 * k + 1))
          (zeroOneVerticalReversedStep (lettersOf (W4 k) true (2 * k + 1)) (lettersOf (W4 k) true (2 * k + 2))) from rfl,
    vtCM4r_high k hk (2 * k + 1) (by omega) le_rfl, hrq4' k (2 * k + 1) (by omega) le_rfl,
    hrp4 k (2 * k + 2) (Or.inr rfl), vtAff4r_high k (2 * k + 1) (by omega) (by omega)]
  simp only [vtBetaM, zeroOneVerticalReversedStep, ptDot]
  push_cast
  ring

/-! ### The reversed positions -/

theorem posF4r_low (k : ℕ) : ∀ j : ℕ, j ≤ k →
    posF .vertical true (lettersOf (W4 k) true) j = (0, 2 * (j : ℤ)) := by
  intro j
  induction j with
  | zero => intro _; simp [posF]; rfl
  | succ n ih =>
    intro hn
    rw [show posF .vertical true (lettersOf (W4 k) true) (n + 1)
        = posF .vertical true (lettersOf (W4 k) true) n
          + stepOf .vertical true (lettersOf (W4 k) true n) (lettersOf (W4 k) true (n + 1)) from rfl,
      ih (by omega), hrq4 k n (by omega), hrq4 k (n + 1) hn]
    simp only [stepOf, zeroOneVerticalReversedStep]
    ext
    all_goals simp
    all_goals ring

theorem posF4r_k1 (k : ℕ) :
    posF .vertical true (lettersOf (W4 k) true) (k + 1) = (0, 2 * (k : ℤ) + 1) := by
  rw [show posF .vertical true (lettersOf (W4 k) true) (k + 1)
      = posF .vertical true (lettersOf (W4 k) true) k
        + stepOf .vertical true (lettersOf (W4 k) true k) (lettersOf (W4 k) true (k + 1)) from rfl,
    posF4r_low k k le_rfl, hrq4 k k le_rfl, hrp4 k (k + 1) (Or.inl rfl)]
  simp only [stepOf, zeroOneVerticalReversedStep]
  ext
  all_goals simp

theorem posF4r_high (k : ℕ) (hk : 1 ≤ k) : ∀ j : ℕ, k + 2 ≤ j → j ≤ 2 * k + 1 →
    posF .vertical true (lettersOf (W4 k) true) j = (-1, 2 * (j : ℤ) - 1) := by
  intro j
  induction j with
  | zero => intro h _; omega
  | succ n ih =>
    intro h1 h2
    by_cases hn : n + 1 = k + 2
    · rw [hn]
      rw [show posF .vertical true (lettersOf (W4 k) true) (k + 2)
          = posF .vertical true (lettersOf (W4 k) true) (k + 1)
            + stepOf .vertical true (lettersOf (W4 k) true (k + 1)) (lettersOf (W4 k) true (k + 2)) from rfl,
        posF4r_k1 k, hrp4 k (k + 1) (Or.inl rfl), hrq4' k (k + 2) le_rfl (by omega)]
      simp only [stepOf, zeroOneVerticalReversedStep]
      ext
      all_goals simp
      all_goals ring
    · have ih' := ih (by omega) (by omega)
      rw [show posF .vertical true (lettersOf (W4 k) true) (n + 1)
          = posF .vertical true (lettersOf (W4 k) true) n
            + stepOf .vertical true (lettersOf (W4 k) true n) (lettersOf (W4 k) true (n + 1)) from rfl,
        ih', hrq4' k n (by omega) (by omega), hrq4' k (n + 1) (by omega) (by omega)]
      simp only [stepOf, zeroOneVerticalReversedStep]
      ext
      all_goals simp
      all_goals ring

theorem posF4r_last (k : ℕ) (hk : 1 ≤ k) :
    posF .vertical true (lettersOf (W4 k) true) (2 * k + 2) = (-1, 4 * (k : ℤ) + 2) := by
  rw [show posF .vertical true (lettersOf (W4 k) true) (2 * k + 2)
      = posF .vertical true (lettersOf (W4 k) true) (2 * k + 1)
        + stepOf .vertical true (lettersOf (W4 k) true (2 * k + 1)) (lettersOf (W4 k) true (2 * k + 2)) from rfl,
    posF4r_high k hk (2 * k + 1) (by omega) le_rfl, hrq4' k (2 * k + 1) (by omega) le_rfl,
    hrp4 k (2 * k + 2) (Or.inr rfl)]
  simp only [stepOf, zeroOneVerticalReversedStep]
  ext
  all_goals simp
  all_goals ring

/-! ### The paper value on the tiles -/

theorem sq4_even (n q : ℤ) (h : n = 2 * q) : n ^ 2 / 4 = q * q := by
  subst h
  rw [show (2 * q) ^ 2 = 4 * (q * q) by ring, Int.mul_ediv_cancel_left (q * q) (by norm_num : (4 : ℤ) ≠ 0)]

theorem sq4_odd (n q : ℤ) (h : n = 2 * q + 1) : n ^ 2 / 4 = q * (q + 1) := by
  subst h
  rw [show (2 * q + 1) ^ 2 = 1 + q * (q + 1) * 4 by ring,
    Int.add_mul_ediv_right 1 (q * (q + 1)) (by norm_num : (4 : ℤ) ≠ 0)]
  norm_num


theorem zo_00 : zeroOdometer (0, 0) = 0 := by simp [zeroOdometer]
theorem zo_01 : zeroOdometer (0, 1) = 0 := by simp [zeroOdometer]
theorem zo_02 : zeroOdometer (0, 2) = -1 := by simp [zeroOdometer]
theorem zo_10 : zeroOdometer (1, 0) = 0 := by simp [zeroOdometer]
theorem zo_11 : zeroOdometer (1, 1) = 0 := by simp [zeroOdometer]
theorem zo_12 : zeroOdometer (1, 2) = -1 := by simp [zeroOdometer]
theorem oo_00 : oneOdometer (0, 0) = 0 := by simp [oneOdometer]
theorem oo_01 : oneOdometer (0, 1) = -1 := by simp [oneOdometer]
theorem oo_10 : oneOdometer (1, 0) = 0 := by simp [oneOdometer]
theorem oo_11 : oneOdometer (1, 1) = 0 := by simp [oneOdometer]

theorem ind_ge (d x1 x2 : ℤ) :
    (paperNearLadderA d ∪ paperNearLadderB d).indicator (fun _ => (1 : ℤ)) (x1, x2) =
      if ((x1 = -1 ∧ x2 = 2 * d + 1) ∨ (x1 = d + 1 ∧ x2 = d - 1)) ∨ (x2 - x1 = d ∧ 0 < x1 ∧ x1 < d) then 1 else 0 := by
  by_cases hm : ((x1 = -1 ∧ x2 = 2 * d + 1) ∨ (x1 = d + 1 ∧ x2 = d - 1)) ∨ (x2 - x1 = d ∧ 0 < x1 ∧ x1 < d)
  · have hmem : (x1, x2) ∈ paperNearLadderA d ∪ paperNearLadderB d := by
      simp only [paperNearLadderA, paperNearLadderB, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
        Set.mem_setOf_eq, Prod.mk.injEq]
      exact hm
    rw [Set.indicator_of_mem hmem, if_pos hm]
  · have hnm : (x1, x2) ∉ paperNearLadderA d ∪ paperNearLadderB d := by
      intro h
      apply hm
      simp only [paperNearLadderA, paperNearLadderB, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
        Set.mem_setOf_eq, Prod.mk.injEq] at h
      exact h
    rw [Set.indicator_of_notMem hnm, if_neg hm]

theorem vp2e_zero0 (k a b x1 x2 : ℤ) (hk : 0 ≤ k) (hab : (a, b) = (0, 0) ∨ (a, b) = (0, 1) ∨ (a, b) = (0, 2) ∨ (a, b) = (1, 0) ∨ (a, b) = (1, 1) ∨ (a, b) = (1, 2))
    (hx1 : x1 = 2 * k + 2 + a) (hx2 : x2 = 2 * k + b + 1) :
    paperNearLadderValue (2 * k + 2) (x1, x2) = zeroOdometer (a, b) := by
  unfold paperNearLadderValue
  dsimp only
  rcases hab with h | h | h | h | h | h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨rfl, rfl⟩ := h
  · rw [sq4_odd (x2 - x1) (-1) (by omega), ind_ge]
    simp only [min_def, max_def]
    split_ifs
    all_goals subst hx1 hx2
    all_goals rw [zo_00]
    all_goals (try omega)
  · rw [sq4_even (x2 - x1) (0) (by omega), ind_ge]
    simp only [min_def, max_def]
    split_ifs
    all_goals subst hx1 hx2
    all_goals rw [zo_01]
    all_goals (try omega)
  · rw [sq4_odd (x2 - x1) (0) (by omega), ind_ge]
    simp only [min_def, max_def]
    split_ifs
    all_goals subst hx1 hx2
    all_goals rw [zo_02]
    all_goals (try omega)
  · rw [sq4_even (x2 - x1) (-1) (by omega), ind_ge]
    simp only [min_def, max_def]
    split_ifs
    all_goals subst hx1 hx2
    all_goals rw [zo_10]
    all_goals (try omega)
  · rw [sq4_odd (x2 - x1) (-1) (by omega), ind_ge]
    simp only [min_def, max_def]
    split_ifs
    all_goals subst hx1 hx2
    all_goals rw [zo_11]
    all_goals (try omega)
  · rw [sq4_even (x2 - x1) (0) (by omega), ind_ge]
    simp only [min_def, max_def]
    split_ifs
    all_goals subst hx1 hx2
    all_goals rw [zo_12]
    all_goals (try omega)

theorem vp2e_one (k j a b x1 x2 : ℤ) (hj1 : 1 ≤ j) (hjk : j ≤ k) (hab : (a, b) = (0, 0) ∨ (a, b) = (0, 1) ∨ (a, b) = (1, 0) ∨ (a, b) = (1, 1))
    (hx1 : x1 = 2 * k + 2 + a) (hx2 : x2 = 2 * k + 2 * j + b + 1) :
    paperNearLadderValue (2 * k + 2) (x1, x2) = oneOdometer (a, b) + (j - 1) * (2 * k + 2 + a) + (-j) * (2 * k + 2 * j + b) + (j * j - 3 * j + 2 * k + 3) := by
  unfold paperNearLadderValue
  dsimp only
  rcases hab with h | h | h | h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨rfl, rfl⟩ := h
  · rw [sq4_odd (x2 - x1) (j - 1) (by omega), ind_ge]
    simp only [min_def, max_def]
    split_ifs
    all_goals subst hx1 hx2
    all_goals rw [oo_00]
    all_goals (try omega)
    all_goals ring_nf
  · rw [sq4_even (x2 - x1) (j) (by omega), ind_ge]
    simp only [min_def, max_def]
    split_ifs
    all_goals subst hx1 hx2
    all_goals rw [oo_01]
    all_goals (try omega)
    all_goals ring_nf
  · rw [sq4_even (x2 - x1) (j - 1) (by omega), ind_ge]
    simp only [min_def, max_def]
    split_ifs
    all_goals subst hx1 hx2
    all_goals rw [oo_10]
    all_goals (try omega)
    all_goals ring_nf
  · rw [sq4_odd (x2 - x1) (j - 1) (by omega), ind_ge]
    simp only [min_def, max_def]
    split_ifs
    all_goals subst hx1 hx2
    all_goals rw [oo_11]
    all_goals (try omega)
    all_goals ring_nf

theorem vp2e_zero_mid (k a b x1 x2 : ℤ) (hk : 1 ≤ k) (hab : (a, b) = (0, 0) ∨ (a, b) = (0, 1) ∨ (a, b) = (0, 2) ∨ (a, b) = (1, 0) ∨ (a, b) = (1, 1) ∨ (a, b) = (1, 2))
    (hx1 : x1 = 2 * k + 1 + a) (hx2 : x2 = 4 * k + 2 + b) :
    paperNearLadderValue (2 * k + 2) (x1, x2) = zeroOdometer (a, b) + k * (2 * k + 1 + a) + (-(k + 1)) * (4 * k + 1 + b) + (k * k + k + 1) := by
  unfold paperNearLadderValue
  dsimp only
  rcases hab with h | h | h | h | h | h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨rfl, rfl⟩ := h
  · rw [sq4_odd (x2 - x1) (k) (by omega), ind_ge]
    simp only [min_def, max_def]
    split_ifs
    all_goals subst hx1 hx2
    all_goals rw [zo_00]
    all_goals (try omega)
    all_goals ring_nf
  · rw [sq4_even (x2 - x1) (k + 1) (by omega), ind_ge]
    simp only [min_def, max_def]
    split_ifs
    all_goals subst hx1 hx2
    all_goals rw [zo_01]
    all_goals (try omega)
    all_goals ring_nf
  · rw [sq4_odd (x2 - x1) (k + 1) (by omega), ind_ge]
    simp only [min_def, max_def]
    split_ifs
    all_goals subst hx1 hx2
    all_goals rw [zo_02]
    all_goals (try omega)
    all_goals ring_nf
  · rw [sq4_even (x2 - x1) (k) (by omega), ind_ge]
    simp only [min_def, max_def]
    split_ifs
    all_goals subst hx1 hx2
    all_goals rw [zo_10]
    all_goals (try omega)
    all_goals ring_nf
  · rw [sq4_odd (x2 - x1) (k) (by omega), ind_ge]
    simp only [min_def, max_def]
    split_ifs
    all_goals subst hx1 hx2
    all_goals rw [zo_11]
    all_goals (try omega)
    all_goals ring_nf
  · rw [sq4_even (x2 - x1) (k + 1) (by omega), ind_ge]
    simp only [min_def, max_def]
    split_ifs
    all_goals subst hx1 hx2
    all_goals rw [zo_12]
    all_goals (try omega)
    all_goals ring_nf

theorem vp2e_top (k m a b x1 x2 : ℤ) (hm1 : k + 2 ≤ m) (hm2 : m ≤ 2 * k + 2) (hab : (a, b) = (0, 0) ∨ (a, b) = (0, 1) ∨ (a, b) = (1, 0) ∨ (a, b) = (1, 1))
    (hx1 : x1 = 2 * k + 1 + a) (hx2 : x2 = 2 * k + 2 * m + b) :
    paperNearLadderValue (2 * k + 2) (x1, x2) = oneOdometer (a, b) + (m - 2) * (2 * k + 1 + a) + (-m) * (2 * k + 2 * m - 1 + b) + (m * m - 3 * m + 4 * k + 5) := by
  unfold paperNearLadderValue
  dsimp only
  rcases hab with h | h | h | h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨rfl, rfl⟩ := h
  · rw [sq4_odd (x2 - x1) (m - 1) (by omega), ind_ge]
    simp only [min_def, max_def]
    split_ifs
    all_goals subst hx1 hx2
    all_goals rw [oo_00]
    all_goals (try omega)
    all_goals (try (have hmk : m = k + 2 := (by omega); subst hmk))
    all_goals ring_nf
  · rw [sq4_even (x2 - x1) (m) (by omega), ind_ge]
    simp only [min_def, max_def]
    split_ifs
    all_goals subst hx1 hx2
    all_goals rw [oo_01]
    all_goals (try omega)
    all_goals ring_nf
  · rw [sq4_even (x2 - x1) (m - 1) (by omega), ind_ge]
    simp only [min_def, max_def]
    split_ifs
    all_goals subst hx1 hx2
    all_goals rw [oo_10]
    all_goals (try omega)
    all_goals (try (have hmk : m = k + 2 := (by omega); subst hmk))
    all_goals ring_nf
  · rw [sq4_odd (x2 - x1) (m - 1) (by omega), ind_ge]
    simp only [min_def, max_def]
    split_ifs
    all_goals subst hx1 hx2
    all_goals rw [oo_11]
    all_goals (try omega)
    all_goals ring_nf

theorem vm2e_one (k i a b x1 x2 : ℤ) (hi0 : 0 ≤ i) (hik : i ≤ k) (hab : (a, b) = (0, 0) ∨ (a, b) = (0, 1) ∨ (a, b) = (1, 0) ∨ (a, b) = (1, 1))
    (hx1 : x1 = a) (hx2 : x2 = 2 * i + b + 1) :
    paperNearLadderValue (2 * k + 2) (x1, x2) = oneOdometer (a, b) + i * a + (-i) * (2 * i + b) + i * (i - 1) := by
  unfold paperNearLadderValue
  dsimp only
  rcases hab with h | h | h | h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨rfl, rfl⟩ := h
  · rw [sq4_odd (x2 - x1) (i) (by omega), ind_ge]
    simp only [min_def, max_def]
    split_ifs
    all_goals subst hx1 hx2
    all_goals rw [oo_00]
    all_goals (try omega)
    all_goals ring_nf
  · rw [sq4_even (x2 - x1) (i + 1) (by omega), ind_ge]
    simp only [min_def, max_def]
    split_ifs
    all_goals subst hx1 hx2
    all_goals rw [oo_01]
    all_goals (try omega)
    all_goals ring_nf
  · rw [sq4_even (x2 - x1) (i) (by omega), ind_ge]
    simp only [min_def, max_def]
    split_ifs
    all_goals subst hx1 hx2
    all_goals rw [oo_10]
    all_goals (try omega)
    all_goals ring_nf
  · rw [sq4_odd (x2 - x1) (i) (by omega), ind_ge]
    simp only [min_def, max_def]
    split_ifs
    all_goals subst hx1 hx2
    all_goals rw [oo_11]
    all_goals (try omega)
    all_goals ring_nf

theorem vm2e_zero (k a b x1 x2 : ℤ) (hk : 0 ≤ k) (hab : (a, b) = (0, 0) ∨ (a, b) = (0, 1) ∨ (a, b) = (0, 2) ∨ (a, b) = (1, 0) ∨ (a, b) = (1, 1) ∨ (a, b) = (1, 2))
    (hx1 : x1 = a) (hx2 : x2 = 2 * k + 2 + b) :
    paperNearLadderValue (2 * k + 2) (x1, x2) = zeroOdometer (a, b) + (k + 1) * a + (-(k + 1)) * (2 * k + 1 + b) + k * (k + 1) := by
  unfold paperNearLadderValue
  dsimp only
  rcases hab with h | h | h | h | h | h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨rfl, rfl⟩ := h
  · rw [sq4_even (x2 - x1) (k + 1) (by omega), ind_ge]
    simp only [min_def, max_def]
    split_ifs
    all_goals subst hx1 hx2
    all_goals rw [zo_00]
    all_goals (try omega)
    all_goals ring_nf
  · rw [sq4_odd (x2 - x1) (k + 1) (by omega), ind_ge]
    simp only [min_def, max_def]
    split_ifs
    all_goals subst hx1 hx2
    all_goals rw [zo_01]
    all_goals (try omega)
    all_goals ring_nf
  · rw [sq4_even (x2 - x1) (k + 2) (by omega), ind_ge]
    simp only [min_def, max_def]
    split_ifs
    all_goals subst hx1 hx2
    all_goals rw [zo_02]
    all_goals (try omega)
    all_goals ring_nf
  · rw [sq4_odd (x2 - x1) (k) (by omega), ind_ge]
    simp only [min_def, max_def]
    split_ifs
    all_goals subst hx1 hx2
    all_goals rw [zo_10]
    all_goals (try omega)
    all_goals ring_nf
  · rw [sq4_even (x2 - x1) (k + 1) (by omega), ind_ge]
    simp only [min_def, max_def]
    split_ifs
    all_goals subst hx1 hx2
    all_goals rw [zo_11]
    all_goals (try omega)
    all_goals ring_nf
  · rw [sq4_odd (x2 - x1) (k + 1) (by omega), ind_ge]
    simp only [min_def, max_def]
    split_ifs
    all_goals subst hx1 hx2
    all_goals rw [zo_12]
    all_goals (try omega)
    all_goals ring_nf

theorem vm2e_second (k m a b x1 x2 : ℤ) (hm1 : k + 2 ≤ m) (hm2 : m ≤ 2 * k + 1) (hab : (a, b) = (0, 0) ∨ (a, b) = (0, 1) ∨ (a, b) = (1, 0) ∨ (a, b) = (1, 1))
    (hx1 : x1 = a - 1) (hx2 : x2 = 2 * m + b) :
    paperNearLadderValue (2 * k + 2) (x1, x2) = oneOdometer (a, b) + (m - 1) * (a - 1) + (-m) * (2 * m - 1 + b) + m * (m - 1) := by
  unfold paperNearLadderValue
  dsimp only
  rcases hab with h | h | h | h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨rfl, rfl⟩ := h
  · rw [sq4_odd (x2 - x1) (m) (by omega), ind_ge]
    simp only [min_def, max_def]
    split_ifs
    all_goals subst hx1 hx2
    all_goals rw [oo_00]
    all_goals (try omega)
    all_goals ring_nf
  · rw [sq4_even (x2 - x1) (m + 1) (by omega), ind_ge]
    simp only [min_def, max_def]
    split_ifs
    all_goals subst hx1 hx2
    all_goals rw [oo_01]
    all_goals (try omega)
    all_goals ring_nf
  · rw [sq4_even (x2 - x1) (m) (by omega), ind_ge]
    simp only [min_def, max_def]
    split_ifs
    all_goals subst hx1 hx2
    all_goals rw [oo_10]
    all_goals (try omega)
    all_goals ring_nf
  · rw [sq4_odd (x2 - x1) (m) (by omega), ind_ge]
    simp only [min_def, max_def]
    split_ifs
    all_goals subst hx1 hx2
    all_goals rw [oo_11]
    all_goals (try omega)
    all_goals ring_nf

theorem vm2e_last (k a b x1 x2 : ℤ) (hk : 1 ≤ k) (hab : (a, b) = (0, 0) ∨ (a, b) = (0, 1) ∨ (a, b) = (0, 2) ∨ (a, b) = (1, 0) ∨ (a, b) = (1, 1) ∨ (a, b) = (1, 2))
    (hx1 : x1 = a - 1) (hx2 : x2 = 4 * k + 3 + b) :
    paperNearLadderValue (2 * k + 2) (x1, x2) = zeroOdometer (a, b) + (2 * k + 1) * (a - 1) + (-(2 * k + 2)) * (4 * k + 2 + b) + (2 * k + 1) * (2 * k + 2) := by
  unfold paperNearLadderValue
  dsimp only
  rcases hab with h | h | h | h | h | h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨rfl, rfl⟩ := h
  · rw [sq4_even (x2 - x1) (2 * k + 2) (by omega), ind_ge]
    simp only [min_def, max_def]
    split_ifs
    all_goals subst hx1 hx2
    all_goals rw [zo_00]
    all_goals (try omega)
    all_goals ring_nf
  · rw [sq4_odd (x2 - x1) (2 * k + 2) (by omega), ind_ge]
    simp only [min_def, max_def]
    split_ifs
    all_goals subst hx1 hx2
    all_goals rw [zo_01]
    all_goals (try omega)
    all_goals ring_nf
  · rw [sq4_even (x2 - x1) (2 * k + 3) (by omega), ind_ge]
    simp only [min_def, max_def]
    split_ifs
    all_goals subst hx1 hx2
    all_goals rw [zo_02]
    all_goals (try omega)
    all_goals ring_nf
  · rw [sq4_odd (x2 - x1) (2 * k + 1) (by omega), ind_ge]
    simp only [min_def, max_def]
    split_ifs
    all_goals subst hx1 hx2
    all_goals rw [zo_10]
    all_goals (try omega)
    all_goals ring_nf
  · rw [sq4_even (x2 - x1) (2 * k + 2) (by omega), ind_ge]
    simp only [min_def, max_def]
    split_ifs
    all_goals subst hx1 hx2
    all_goals rw [zo_11]
    all_goals (try omega)
    all_goals ring_nf
  · rw [sq4_odd (x2 - x1) (2 * k + 2) (by omega), ind_ge]
    simp only [min_def, max_def]
    split_ifs
    all_goals subst hx1 hx2
    all_goals rw [zo_12]
    all_goals (try omega)
    all_goals ring_nf

/-! ### The odometers of the forward piece, tile by tile -/

theorem vtCP4f_J (k J : ℕ) (h1 : 1 ≤ J) (h2 : J ≤ k) :
    vtCP (lettersOf (W4 k) false) J = 1 - (J : ℤ) - (J : ℤ) * (J : ℤ) := by
  obtain ⟨n, rfl⟩ : ∃ n, J = n + 1 := ⟨J - 1, by omega⟩
  have h := vtCP4f_low k n (by omega)
  push_cast at h ⊢
  exact h

theorem wlen4 (k : ℕ) : (W4 k).length = 2 * k + 3 := by
  simp only [W4, List.length_cons, List.length_append, List.length_replicate]
  omega

theorem vtAff_two_zero_even (k : ℕ) : vtAff (lettersOf (W4 k) false) 0 = (0, 0) := by
  simp [vtAff, vtCnt]

theorem vtCP_zero_even (k : ℕ) : vtCP (lettersOf (W4 k) false) 0 = 0 := rfl

theorem vp2e_zero0_pt (k : ℕ) (hk : 0 ≤ (k : ℤ)) (y : GInt) (hy : y ∈ tileShape ZTile.zero) :
    paperNearLadderValue (2 * (k : ℤ) + 2) (y + ((0, 2 * ((0 : ℕ) : ℤ)) + (2 * (k : ℤ) + 2, 2 * (k : ℤ))) + (0, 1)) =
      (vpPiece (W4 k) (2 * (k : ℤ) + 2, 2 * (k : ℤ))).odo 0
        (y + ((0, 2 * ((0 : ℕ) : ℤ)) + (2 * (k : ℤ) + 2, 2 * (k : ℤ)))) := by
  obtain ⟨a, b⟩ := y
  have hab : (a, b) = (0, 0) ∨ (a, b) = (0, 1) ∨ (a, b) = (0, 2) ∨ (a, b) = (1, 0) ∨ (a, b) = (1, 1) ∨
      (a, b) = (1, 2) := by
    simpa [tileShape] using hy
  rw [vpPiece_odo _ _ 0 (by rw [wlen4]; omega), posF4_low k 0 (Nat.zero_le _), hfp40 k, hz0,
    vtAff_two_zero_even k, vtCP_zero_even k, add_sub_cancel_right]
  rw [show (a, b) + ((0, 2 * ((0 : ℕ) : ℤ)) + (2 * (k : ℤ) + 2, 2 * (k : ℤ))) + (0, 1)
      = (2 * (k : ℤ) + 2 + a, 2 * (k : ℤ) + b + 1)
      from Prod.ext (by push_cast; simp only [Prod.fst_add]; ring) (by push_cast; simp only [Prod.snd_add]; ring),
    vp2e_zero0 (k : ℤ) a b (2 * (k : ℤ) + 2 + a) (2 * (k : ℤ) + b + 1) hk hab rfl rfl]
  simp only [zTileOdo, Nat.cast_zero, mul_zero, zero_add, add_zero, sub_zero, zero_sub, ptDot, Prod.fst_add,
    Prod.snd_add]
  ring

theorem vp2e_one_pt (k J : ℕ) (hJ1 : 1 ≤ J) (hJk : J ≤ k) (y : GInt) (hy : y ∈ tileShape ZTile.one) :
    paperNearLadderValue (2 * (k : ℤ) + 2) (y + ((0, 2 * (J : ℤ)) + (2 * (k : ℤ) + 2, 2 * (k : ℤ))) + (0, 1)) =
      (vpPiece (W4 k) (2 * (k : ℤ) + 2, 2 * (k : ℤ))).odo J (y + ((0, 2 * (J : ℤ)) + (2 * (k : ℤ) + 2, 2 * (k : ℤ)))) := by
  obtain ⟨a, b⟩ := y
  have hab : (a, b) = (0, 0) ∨ (a, b) = (0, 1) ∨ (a, b) = (1, 0) ∨ (a, b) = (1, 1) := by
    simpa [tileShape] using hy
  rw [vpPiece_odo _ _ J (by rw [wlen4]; omega), posF4_low k J (by omega), hfq4 k J hJ1 hJk, hz1,
    vtAff4f_low k J hJ1 (by omega), vtCP4f_J k J hJ1 hJk, add_sub_cancel_right]
  rw [show (a, b) + ((0, 2 * (J : ℤ)) + (2 * (k : ℤ) + 2, 2 * (k : ℤ))) + (0, 1)
      = (2 * (k : ℤ) + 2 + a, 2 * (k : ℤ) + 2 * (J : ℤ) + b + 1)
      from Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring),
    vp2e_one (k : ℤ) (J : ℤ) a b (2 * (k : ℤ) + 2 + a) (2 * (k : ℤ) + 2 * (J : ℤ) + b + 1)
      (by exact_mod_cast hJ1) (by exact_mod_cast hJk) hab rfl rfl]
  simp only [zTileOdo, ptDot, Prod.fst_add, Prod.snd_add]
  ring

theorem vp2e_zero_mid_pt (k : ℕ) (hk : 1 ≤ k) (y : GInt) (hy : y ∈ tileShape ZTile.zero) :
    paperNearLadderValue (2 * (k : ℤ) + 2) (y + ((-1, 2 * ((k + 1 : ℕ) : ℤ) - 1) + (2 * (k : ℤ) + 2, 2 * (k : ℤ))) + (0, 1)) =
      (vpPiece (W4 k) (2 * (k : ℤ) + 2, 2 * (k : ℤ))).odo (k + 1)
        (y + ((-1, 2 * ((k + 1 : ℕ) : ℤ) - 1) + (2 * (k : ℤ) + 2, 2 * (k : ℤ)))) := by
  obtain ⟨a, b⟩ := y
  have hab : (a, b) = (0, 0) ∨ (a, b) = (0, 1) ∨ (a, b) = (0, 2) ∨ (a, b) = (1, 0) ∨ (a, b) = (1, 1) ∨
      (a, b) = (1, 2) := by
    simpa [tileShape] using hy
  rw [vpPiece_odo _ _ (k + 1) (by rw [wlen4]; omega), posF4_mid k (k + 1) le_rfl (by omega), hfp4 k, hz0,
    vtAff4f_low k (k + 1) (by omega) le_rfl, vtCP4f_k1 k hk, add_sub_cancel_right]
  rw [show (a, b) + ((-1, 2 * ((k + 1 : ℕ) : ℤ) - 1) + (2 * (k : ℤ) + 2, 2 * (k : ℤ))) + (0, 1)
      = (2 * (k : ℤ) + 1 + a, 4 * (k : ℤ) + 2 + b)
      from Prod.ext (by push_cast; simp only [Prod.fst_add]; ring) (by push_cast; simp only [Prod.snd_add]; ring),
    vp2e_zero_mid (k : ℤ) a b (2 * (k : ℤ) + 1 + a) (4 * (k : ℤ) + 2 + b) (by exact_mod_cast hk) hab rfl rfl]
  simp only [zTileOdo, ptDot, Prod.fst_add, Prod.snd_add]
  push_cast
  ring

theorem vp2e_top_pt (k J : ℕ) (hk : 1 ≤ k) (hJ1 : k + 2 ≤ J) (hJ2 : J ≤ 2 * k + 2) (y : GInt) (hy : y ∈ tileShape ZTile.one) :
    paperNearLadderValue (2 * (k : ℤ) + 2) (y + ((-1, 2 * (J : ℤ) - 1) + (2 * (k : ℤ) + 2, 2 * (k : ℤ))) + (0, 1)) =
      (vpPiece (W4 k) (2 * (k : ℤ) + 2, 2 * (k : ℤ))).odo J
        (y + ((-1, 2 * (J : ℤ) - 1) + (2 * (k : ℤ) + 2, 2 * (k : ℤ)))) := by
  obtain ⟨a, b⟩ := y
  have hab : (a, b) = (0, 0) ∨ (a, b) = (0, 1) ∨ (a, b) = (1, 0) ∨ (a, b) = (1, 1) := by
    simpa [tileShape] using hy
  rw [vpPiece_odo _ _ J (by rw [wlen4]; omega), posF4_mid k J (by omega) hJ2, hfq4' k J hJ1 hJ2, hz1,
    vtAff4f_high k J hJ1 hJ2, vtCP4f_high k hk J hJ1 hJ2, add_sub_cancel_right]
  rw [show (a, b) + ((-1, 2 * (J : ℤ) - 1) + (2 * (k : ℤ) + 2, 2 * (k : ℤ))) + (0, 1)
      = (2 * (k : ℤ) + 1 + a, 2 * (k : ℤ) + 2 * (J : ℤ) + b)
      from Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring),
    vp2e_top (k : ℤ) (J : ℤ) a b (2 * (k : ℤ) + 1 + a) (2 * (k : ℤ) + 2 * (J : ℤ) + b)
      (by exact_mod_cast hJ1) (by exact_mod_cast hJ2) hab rfl rfl]
  simp only [zTileOdo, ptDot, Prod.fst_add, Prod.snd_add]
  ring

/-- The forward vertical base piece of the even `2^k` word (`k ≥ 1`) respects its string, with the near-ladder value
as odometer. -/
theorem vp2e_respects (k : ℕ) (hk : 1 ≤ k) :
    RespectsTiles .vertical false
      (vStringAt (vWordOf (List.replicate k Digit.two) true)
        (lastPosOf (hStringAt (hWordOf (List.replicate k Digit.two) true) (0, 0))))
      (fun x => paperNearLadderValue (2 * (k : ℤ) + 2) (x + (0, 1))) := by
  rw [anchor_even2 k, wv_even2 k]
  have hR : (vpPiece (W4 k) (2 * (k : ℤ) + 2, 2 * (k : ℤ))).Respects .vertical false :=
    PTFamily.translate_respects _ _ _ _ (vtP_respects _)
  refine ⟨vpPiece (W4 k) (2 * (k : ℤ) + 2, 2 * (k : ℤ)), vpPiece_ts _ _, ?_, hR⟩
  intro J hJ x hx
  rw [vpPiece_n, wlen4] at hJ
  rcases (show J = 0 ∨ (1 ≤ J ∧ J ≤ k) ∨ J = k + 1 ∨ (k + 2 ≤ J ∧ J ≤ 2 * k + 2) by omega) with rfl | ⟨h1, h2⟩ | rfl | ⟨h1, h2⟩
  · unfold PTFamily.dom at hx
    rw [vpPiece_tile _ _ 0 (by rw [wlen4]; omega), hfp40 k, hz0, posF4_low k 0 (Nat.zero_le _)] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact vp2e_zero0_pt k (by positivity) y hy
  · unfold PTFamily.dom at hx
    rw [vpPiece_tile _ _ J (by rw [wlen4]; omega), hfq4 k J h1 h2, hz1, posF4_low k J h2] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact vp2e_one_pt k J h1 h2 y hy
  · unfold PTFamily.dom at hx
    rw [vpPiece_tile _ _ (k + 1) (by rw [wlen4]; omega), hfp4 k, hz0,
      posF4_mid k (k + 1) le_rfl (by omega)] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact vp2e_zero_mid_pt k hk y hy
  · unfold PTFamily.dom at hx
    rw [vpPiece_tile _ _ J (by rw [wlen4]; omega), hfq4' k J h1 h2, hz1,
      posF4_mid k J (by omega) h2] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact vp2e_top_pt k J hk h1 h2 y hy

/-! ### The odometers of the reversed piece, tile by tile -/

theorem vm2e_one_pt (k J : ℕ) (hJk : J ≤ k) (y : GInt) (hy : y ∈ tileShape ZTile.one) :
    paperNearLadderValue (2 * (k : ℤ) + 2) (y + (0, 2 * (J : ℤ)) + (0, 1)) =
      (piece (W4 k)).odo J (y + (0, 2 * (J : ℤ))) := by
  obtain ⟨a, b⟩ := y
  have hab : (a, b) = (0, 0) ∨ (a, b) = (0, 1) ∨ (a, b) = (1, 0) ∨ (a, b) = (1, 1) := by
    simpa [tileShape] using hy
  rw [piece_odo _ J (by rw [wlen4]; omega), posF4r_low k J hJk, hrq4 k J hJk, hz1,
    vtAff4r_low k J (by omega), vtCM4r_low k J hJk, add_sub_cancel_right]
  rw [show (a, b) + (0, 2 * (J : ℤ)) + (0, 1) = (a, 2 * (J : ℤ) + b + 1)
      from Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring),
    vm2e_one (k : ℤ) (J : ℤ) a b a (2 * (J : ℤ) + b + 1) (by positivity) (by exact_mod_cast hJk) hab rfl rfl]
  simp only [zTileOdo, ptDot, Prod.fst_add, Prod.snd_add]
  ring

theorem vm2e_zero_pt (k : ℕ) (y : GInt) (hy : y ∈ tileShape ZTile.zero) :
    paperNearLadderValue (2 * (k : ℤ) + 2) (y + (0, 2 * (k : ℤ) + 1) + (0, 1)) =
      (piece (W4 k)).odo (k + 1) (y + (0, 2 * (k : ℤ) + 1)) := by
  obtain ⟨a, b⟩ := y
  have hab : (a, b) = (0, 0) ∨ (a, b) = (0, 1) ∨ (a, b) = (0, 2) ∨ (a, b) = (1, 0) ∨ (a, b) = (1, 1) ∨
      (a, b) = (1, 2) := by
    simpa [tileShape] using hy
  have hk : (0 : ℤ) ≤ (k : ℤ) := by positivity
  rw [piece_odo _ (k + 1) (by rw [wlen4]; omega), posF4r_k1 k, hrp4 k (k + 1) (Or.inl rfl), hz0,
    vtAff4r_low k (k + 1) le_rfl, vtCM4r_mid k, add_sub_cancel_right]
  rw [show (a, b) + (0, 2 * (k : ℤ) + 1) + (0, 1) = (a, 2 * (k : ℤ) + 2 + b)
      from Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring),
    vm2e_zero (k : ℤ) a b a (2 * (k : ℤ) + 2 + b) hk hab rfl rfl]
  simp only [zTileOdo, ptDot, Prod.fst_add, Prod.snd_add]
  push_cast
  ring

theorem vm2e_second_pt (k : ℕ) (hk : 1 ≤ k) (J : ℕ) (h1 : k + 2 ≤ J) (h2 : J ≤ 2 * k + 1) (y : GInt)
    (hy : y ∈ tileShape ZTile.one) :
    paperNearLadderValue (2 * (k : ℤ) + 2) (y + (-1, 2 * (J : ℤ) - 1) + (0, 1)) =
      (piece (W4 k)).odo J (y + (-1, 2 * (J : ℤ) - 1)) := by
  obtain ⟨a, b⟩ := y
  have hab : (a, b) = (0, 0) ∨ (a, b) = (0, 1) ∨ (a, b) = (1, 0) ∨ (a, b) = (1, 1) := by
    simpa [tileShape] using hy
  rw [piece_odo _ J (by rw [wlen4]; omega), posF4r_high k hk J h1 h2, hrq4' k J h1 (by omega), hz1,
    vtAff4r_high k J h1 (by omega), vtCM4r_high k hk J h1 h2, add_sub_cancel_right]
  rw [show (a, b) + (-1, 2 * (J : ℤ) - 1) + (0, 1) = (a - 1, 2 * (J : ℤ) + b)
      from Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring),
    vm2e_second (k : ℤ) (J : ℤ) a b (a - 1) (2 * (J : ℤ) + b) (by exact_mod_cast h1) (by exact_mod_cast h2) hab rfl rfl]
  simp only [zTileOdo, ptDot, Prod.fst_add, Prod.snd_add]
  ring

theorem vm2e_last_pt (k : ℕ) (hk : 1 ≤ k) (y : GInt) (hy : y ∈ tileShape ZTile.zero) :
    paperNearLadderValue (2 * (k : ℤ) + 2) (y + (-1, 4 * (k : ℤ) + 2) + (0, 1)) =
      (piece (W4 k)).odo (2 * k + 2) (y + (-1, 4 * (k : ℤ) + 2)) := by
  obtain ⟨a, b⟩ := y
  have hab : (a, b) = (0, 0) ∨ (a, b) = (0, 1) ∨ (a, b) = (0, 2) ∨ (a, b) = (1, 0) ∨ (a, b) = (1, 1) ∨
      (a, b) = (1, 2) := by
    simpa [tileShape] using hy
  rw [piece_odo _ (2 * k + 2) (by rw [wlen4]; omega), posF4r_last k hk, hrp4 k (2 * k + 2) (Or.inr rfl), hz0,
    vtAff4r_high k (2 * k + 2) (by omega) le_rfl, vtCM4r_last k hk, add_sub_cancel_right]
  rw [show (a, b) + (-1, 4 * (k : ℤ) + 2) + (0, 1) = (a - 1, 4 * (k : ℤ) + 3 + b)
      from Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring),
    vm2e_last (k : ℤ) a b (a - 1) (4 * (k : ℤ) + 3 + b) (by exact_mod_cast hk) hab rfl rfl]
  simp only [zTileOdo, ptDot, Prod.fst_add, Prod.snd_add]
  push_cast
  ring

/-- The reversed vertical base piece of the even `2^k` word (`k ≥ 1`) respects its string, anchored at `(0,0)`, with the
near-ladder value as odometer. -/
theorem vm2e_respects (k : ℕ) (hk : 1 ≤ k) :
    RespectsTiles .vertical true
      (vRevStringAt (vWordOf (List.replicate k Digit.two) true).reverse (0, 0))
      (fun x => paperNearLadderValue (2 * (k : ℤ) + 2) (x + (0, 1))) := by
  rw [wv_even2 k]
  have hR : (piece (W4 k)).Respects .vertical true := PTFamily.translate_respects _ _ _ _ (vtM_respects _)
  refine ⟨piece (W4 k), piece_ts _, ?_, hR⟩
  intro J hJ x hx
  rw [piece_n, wlen4] at hJ
  rcases (show J ≤ k ∨ J = k + 1 ∨ (k + 2 ≤ J ∧ J ≤ 2 * k + 1) ∨ J = 2 * k + 2 by omega) with h | rfl | ⟨h1, h2⟩ | rfl
  · unfold PTFamily.dom at hx
    rw [piece_tile _ J (by rw [wlen4]; omega), hrq4 k J h, posF4r_low k J h, hz1] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact vm2e_one_pt k J h y hy
  · unfold PTFamily.dom at hx
    rw [piece_tile _ (k + 1) (by rw [wlen4]; omega), hrp4 k (k + 1) (Or.inl rfl), posF4r_k1 k, hz0] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact vm2e_zero_pt k y hy
  · unfold PTFamily.dom at hx
    rw [piece_tile _ J (by rw [wlen4]; omega), hrq4' k J h1 (by omega), posF4r_high k hk J h1 h2, hz1] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact vm2e_second_pt k hk J h1 h2 y hy
  · unfold PTFamily.dom at hx
    rw [piece_tile _ (2 * k + 2) (by rw [wlen4]; omega), hrp4 k (2 * k + 2) (Or.inr rfl),
      posF4r_last k hk, hz0] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact vm2e_last_pt k hk y hy

end FLatticePaper.Tiles.BaseTwoEven
