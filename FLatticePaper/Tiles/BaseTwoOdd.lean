import FLatticePaper.Tiles.BaseVertVp
import FLatticePaper.Tiles.BaseVertOdoFamily
import FLatticePaper.Tiles.RegisterLink
import FLatticePaper.Tiles.AltRotStep
import FLatticePaper.Tiles.BaseTileProps
import FLatticePaper.Tiles.TexVPositions
import FLatticePaper.Tiles.StandardClauseA
import FLatticePaper.Construction.NearOneBaseCases

/-! # The vertical base pieces of the odd `2^k` word (`k ≥ 0`, so also the empty word's odd child)

The vertical word of the odd child of `2^k` is `p q^(k+1)`, its anchor is `(2k+3, 2k+1)`, and the odometer of both pieces is
the near-stair value `paperNearStairValue (2k+3) (x + (0,1))`. The forward piece `Vp` has a `zero` tile at the anchor and `one`
tiles at `c + (0, 2j)`, `1 ≤ j ≤ k+1`; the reversed piece `Vm` (anchor `(0,0)`) has `one` tiles at `(0, 2j)`, `j ≤ k`, and a
`zero` tile at `(0, 2k+1)`. -/

namespace FLatticePaper.Tiles.BaseTwoOdd

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Tiles.BaseVertOdo FLatticePaper.Tiles.BaseVertOdoFamily FLatticePaper.Tiles.BaseVertVp
open FLatticePaper.Tiles.StandardClause

/-- The word `p q^(k+1)`, the vertical word of the odd child of `2^k`. -/
abbrev W2 (k : ℕ) : BinaryWord := Letter.p :: List.replicate (k + 1) Letter.q

theorem wv_two (k : ℕ) : vWordOf (List.replicate k Digit.two) false = W2 k := by
  unfold vWordOf
  rw [FLatticePaper.Tiles.AltRotStep.swapW_replicate_two, if_neg Bool.false_ne_true,
    (FLatticePaper.Tiles.RegisterLink.quad_threes k).2.1]
  simp [W2, swapLetter, List.map_replicate]

theorem anchor_two (k : ℕ) :
    lastPosOf (hStringAt (hWordOf (List.replicate k Digit.two) false) (0, 0)) = (2 * (k : ℤ) + 3, 2 * (k : ℤ) + 1) := by
  rw [TexVPositions.lastPos_hWordOf_false_tex]
  unfold fracOdd
  rw [BaseTileProps.parents_two]
  unfold texV1Odd
  simp only [Parents.current, Parents.combine]
  ext
  all_goals simp
  all_goals ring

/-! ### The letters of `W2 k` -/

theorem getD_rep_q (n i : ℕ) :
    (List.replicate n Letter.q).getD i Letter.p = if i < n then Letter.q else Letter.p := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split_ifs <;> simp

theorem lf_get (k n : ℕ) :
    lettersOf (W2 k) false n = if n = 0 ∨ k + 1 < n then Letter.p else Letter.q := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [lettersOf, W2]
  · obtain ⟨i, rfl⟩ : ∃ i, n = i + 1 := ⟨n - 1, by omega⟩
    have hL : lettersOf (W2 k) false (i + 1) = (List.replicate (k + 1) Letter.q).getD i Letter.p := by
      simp [lettersOf, W2]
    rw [hL, getD_rep_q]
    by_cases hi : i < k + 1
    · rw [if_pos hi, if_neg (show ¬(i + 1 = 0 ∨ k + 1 < i + 1) by omega)]
    · rw [if_neg hi, if_pos (show i + 1 = 0 ∨ k + 1 < i + 1 by omega)]

theorem lr_get (k n : ℕ) :
    lettersOf (W2 k) true n = if k + 1 ≤ n then Letter.p else Letter.q := by
  have hr : (W2 k).reverse = List.replicate (k + 1) Letter.q ++ [Letter.p] := by
    simp [W2, List.reverse_cons, List.reverse_replicate]
  have hL : lettersOf (W2 k) true n = (List.replicate (k + 1) Letter.q ++ [Letter.p]).getD n Letter.p := by
    simp only [lettersOf, if_true, hr]
  rw [hL]
  by_cases hi : n < k + 1
  · rw [List.getD_append _ _ _ _ (by simp; omega), getD_rep_q, if_pos hi,
      if_neg (show ¬(k + 1 ≤ n) by omega)]
  · rw [if_pos (show k + 1 ≤ n by omega)]
    by_cases hn : n = k + 1
    · subst hn
      simp [List.getD_eq_getElem?_getD]
    · rw [List.getD_eq_default _ _ (by simp; omega)]

theorem hfq (k n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ k + 1) : lettersOf (W2 k) false n = Letter.q := by
  rw [lf_get, if_neg (show ¬(n = 0 ∨ k + 1 < n) by omega)]

theorem hfp0 (k : ℕ) : lettersOf (W2 k) false 0 = Letter.p := by
  rw [lf_get, if_pos (show (0 = 0 ∨ k + 1 < 0) from Or.inl rfl)]

theorem hrq (k n : ℕ) (h : n < k + 1) : lettersOf (W2 k) true n = Letter.q := by
  rw [lr_get, if_neg (show ¬(k + 1 ≤ n) by omega)]

theorem hrp (k n : ℕ) (h : k + 1 ≤ n) : lettersOf (W2 k) true n = Letter.p := by
  rw [lr_get, if_pos h]

/-! ### The forward piece `Vp` -/

theorem vtCnt_two_fwd (k : ℕ) : ∀ m : ℕ, m ≤ k + 1 →
    vtCnt (lettersOf (W2 k) false) (m + 1) = (m : ℤ) := by
  intro m
  induction m with
  | zero => intro _; simp [vtCnt, hfp0]
  | succ n ih =>
    intro hn
    rw [show vtCnt (lettersOf (W2 k) false) (n + 1 + 1)
        = vtCnt (lettersOf (W2 k) false) (n + 1)
          + (if lettersOf (W2 k) false (n + 1) = Letter.q then 1 else 0) from rfl,
      ih (by omega), hfq k (n + 1) (by omega) (by omega)]
    simp

theorem posF_two_fwd (k : ℕ) : ∀ m : ℕ, m ≤ k + 1 →
    posF .vertical false (lettersOf (W2 k) false) m = (0, 2 * (m : ℤ)) := by
  intro m
  induction m with
  | zero => intro _; simp [posF]; rfl
  | succ n ih =>
    intro hn
    rw [show posF .vertical false (lettersOf (W2 k) false) (n + 1)
        = posF .vertical false (lettersOf (W2 k) false) n
          + stepOf .vertical false (lettersOf (W2 k) false n) (lettersOf (W2 k) false (n + 1)) from rfl,
      ih (by omega), hfq k (n + 1) (by omega) (by omega)]
    simp only [stepOf, zeroOneVerticalStep]
    ext
    all_goals simp
    all_goals ring

theorem vtCP_two_fwd (k : ℕ) : ∀ m : ℕ, 1 ≤ m → m ≤ k + 1 →
    vtCP (lettersOf (W2 k) false) m = 1 - (m : ℤ) - (m : ℤ) * (m : ℤ) := by
  intro m hm1
  induction m, hm1 using Nat.le_induction with
  | base =>
    intro _
    rw [show vtCP (lettersOf (W2 k) false) (1 : ℕ)
        = vtCP (lettersOf (W2 k) false) 0 + vtBetaP (lettersOf (W2 k) false 0) (lettersOf (W2 k) false 1)
          + ptDot (vtAff (lettersOf (W2 k) false) 0) (zeroOneVerticalStep (lettersOf (W2 k) false 1)) from rfl,
      hfp0, hfq k 1 le_rfl (by omega)]
    simp [vtCP, vtAff, vtCnt, vtBetaP, zeroOneVerticalStep, ptDot]
  | succ n hn ih =>
    intro hn1
    obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
    have hc := vtCnt_two_fwd k p (by omega)
    have ih' := ih (by omega)
    rw [show vtCP (lettersOf (W2 k) false) (p + 1 + 1)
        = vtCP (lettersOf (W2 k) false) (p + 1)
          + vtBetaP (lettersOf (W2 k) false (p + 1)) (lettersOf (W2 k) false (p + 1 + 1))
          + ptDot (vtAff (lettersOf (W2 k) false) (p + 1))
            (zeroOneVerticalStep (lettersOf (W2 k) false (p + 1 + 1))) from rfl,
      hfq k (p + 1) (by omega) (by omega), hfq k (p + 1 + 1) (by omega) (by omega), ih']
    have hA : vtAff (lettersOf (W2 k) false) (p + 1) = ((p : ℤ), -((p : ℤ) + 1)) := by
      simp [vtAff, hc]
    rw [hA]
    simp only [vtBetaP, zeroOneVerticalStep, ptDot]
    push_cast
    ring

/-! ### The reversed piece `Vm` -/

theorem vtCnt_two_rev (k : ℕ) : ∀ m : ℕ, m ≤ k + 1 →
    vtCnt (lettersOf (W2 k) true) m = (m : ℤ) := by
  intro m
  induction m with
  | zero => intro _; simp [vtCnt]
  | succ n ih =>
    intro hn
    rw [show vtCnt (lettersOf (W2 k) true) (n + 1)
        = vtCnt (lettersOf (W2 k) true) n + (if lettersOf (W2 k) true n = Letter.q then 1 else 0) from rfl,
      ih (by omega), hrq k n (by omega)]
    push_cast
    simp

theorem posF_two_rev (k : ℕ) : ∀ m : ℕ, m ≤ k →
    posF .vertical true (lettersOf (W2 k) true) m = (0, 2 * (m : ℤ)) := by
  intro m
  induction m with
  | zero => intro _; simp [posF]; rfl
  | succ n ih =>
    intro hn
    rw [show posF .vertical true (lettersOf (W2 k) true) (n + 1)
        = posF .vertical true (lettersOf (W2 k) true) n
          + stepOf .vertical true (lettersOf (W2 k) true n) (lettersOf (W2 k) true (n + 1)) from rfl,
      ih (by omega), hrq k n (by omega), hrq k (n + 1) (by omega)]
    simp only [stepOf, zeroOneVerticalReversedStep]
    ext
    all_goals simp
    all_goals ring

theorem posF_two_rev_last (k : ℕ) :
    posF .vertical true (lettersOf (W2 k) true) (k + 1) = (0, 2 * (k : ℤ) + 1) := by
  rw [show posF .vertical true (lettersOf (W2 k) true) (k + 1)
      = posF .vertical true (lettersOf (W2 k) true) k
        + stepOf .vertical true (lettersOf (W2 k) true k) (lettersOf (W2 k) true (k + 1)) from rfl,
    posF_two_rev k k le_rfl, hrq k k (by omega), hrp k (k + 1) (by omega)]
  simp only [stepOf, zeroOneVerticalReversedStep]
  ext
  all_goals simp

theorem vtCM_two_rev (k : ℕ) : ∀ m : ℕ, m ≤ k →
    vtCM (lettersOf (W2 k) true) m = -((m : ℤ) * ((m : ℤ) + 1)) := by
  intro m
  induction m with
  | zero => intro _; simp [vtCM]
  | succ n ih =>
    intro hn
    rw [show vtCM (lettersOf (W2 k) true) (n + 1)
        = vtCM (lettersOf (W2 k) true) n
          + vtBetaM (lettersOf (W2 k) true n) (lettersOf (W2 k) true (n + 1))
          + ptDot (vtAff (lettersOf (W2 k) true) n)
            (zeroOneVerticalReversedStep (lettersOf (W2 k) true n) (lettersOf (W2 k) true (n + 1))) from rfl,
      ih (by omega), hrq k n (by omega), hrq k (n + 1) (by omega)]
    have hA : vtAff (lettersOf (W2 k) true) n = ((n : ℤ), -(n : ℤ)) := by
      simp [vtAff, vtCnt_two_rev k n (by omega)]
    rw [hA]
    simp only [vtBetaM, zeroOneVerticalReversedStep, ptDot]
    push_cast
    ring

theorem vtCM_two_rev_last (k : ℕ) :
    vtCM (lettersOf (W2 k) true) (k + 1) = -(((k : ℤ) + 1) * ((k : ℤ) + 1)) := by
  rw [show vtCM (lettersOf (W2 k) true) (k + 1)
      = vtCM (lettersOf (W2 k) true) k
        + vtBetaM (lettersOf (W2 k) true k) (lettersOf (W2 k) true (k + 1))
        + ptDot (vtAff (lettersOf (W2 k) true) k)
          (zeroOneVerticalReversedStep (lettersOf (W2 k) true k) (lettersOf (W2 k) true (k + 1))) from rfl,
    vtCM_two_rev k k le_rfl, hrq k k (by omega), hrp k (k + 1) (by omega)]
  have hA : vtAff (lettersOf (W2 k) true) k = ((k : ℤ), -(k : ℤ)) := by
    simp [vtAff, vtCnt_two_rev k k (by omega)]
  rw [hA]
  simp only [vtBetaM, zeroOneVerticalReversedStep, ptDot]
  ring

/-! ### The paper value and the half-square identity -/

theorem paper_eval (d x1 x2 : ℤ) :
    paperNearStairValue d (x1, x2) = -((x2 - x1) ^ 2 / 4) + min (d - x2) 0
      + (if (x1, x2) = (0, d + 1) ∨ (x1, x2) = (d + 1, d - 1) then 1 else 0) := rfl

theorem sq_half (n : ℤ) : n ^ 2 / 4 = (n / 2) * ((n + 1) / 2) := by
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' n
  · subst hm
    have h1 : (2 * m) ^ 2 = 4 * (m * m) := by ring
    have e1 : 2 * m / 2 = m := by omega
    have e2 : (2 * m + 1) / 2 = m := by omega
    rw [h1, Int.mul_ediv_cancel_left _ (by norm_num), e1, e2]
  · subst hm
    have h1 : (2 * m + 1) ^ 2 = 4 * (m * m + m) + 1 := by ring
    have e1 : (4 * (m * m + m) + 1) / 4 = m * m + m := by omega
    have e2 : (2 * m + 1) / 2 = m := by omega
    have e3 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    rw [h1, e1, e2, e3]
    ring

/-! ### Half squares at the concrete values -/

theorem sqd_odd (m : ℤ) : (2 * m + 1) ^ 2 / 4 = m * (m + 1) := by
  have e1 : (2 * m + 1) / 2 = m := by omega
  have e2 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
  rw [sq_half, e1, e2]

theorem sqd_even (m : ℤ) : (2 * m) ^ 2 / 4 = m * m := by
  have e1 : 2 * m / 2 = m := by omega
  have e2 : (2 * m + 1) / 2 = m := by omega
  rw [sq_half, e1, e2]

/-! ### The paper value on the tiles of `Vp` -/

/-- The zero tile at the anchor `(2k+3, 2k+1)`. -/
theorem paper_zero_vp (k a b : ℤ) (hk : 0 ≤ k) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb2 : b ≤ 2)
    (hab : (a, b) = (0, 0) ∨ (a, b) = (0, 1) ∨ (a, b) = (0, 2) ∨ (a, b) = (1, 0) ∨ (a, b) = (1, 1) ∨ (a, b) = (1, 2)) :
    paperNearStairValue (2 * k + 3) ((a, b) + (2 * k + 3, 2 * k + 1) + (0, 1)) = zeroOdometer (a, b) := by
  rw [show (a, b) + (2 * k + 3, 2 * k + 1) + (0, 1) = (2 * k + 3 + a, 2 * k + 2 + b)
      from Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring)]
  have hite : (if (2 * k + 3 + a, 2 * k + 2 + b) = (0, 2 * k + 3 + 1)
      ∨ (2 * k + 3 + a, 2 * k + 2 + b) = (2 * k + 3 + 1, 2 * k + 3 - 1) then (1 : ℤ) else 0)
      = if a = 1 ∧ b = 0 then 1 else 0 := by
    by_cases h10 : a = 1 ∧ b = 0
    · rw [if_pos h10, if_pos (show (2 * k + 3 + a, 2 * k + 2 + b) = (0, 2 * k + 3 + 1)
        ∨ (2 * k + 3 + a, 2 * k + 2 + b) = (2 * k + 3 + 1, 2 * k + 3 - 1) from
          Or.inr (Prod.ext (by omega) (by omega)))]
    · rw [if_neg h10, if_neg (show ¬((2 * k + 3 + a, 2 * k + 2 + b) = (0, 2 * k + 3 + 1)
        ∨ (2 * k + 3 + a, 2 * k + 2 + b) = (2 * k + 3 + 1, 2 * k + 3 - 1)) from by
          rintro (h | h) <;> simp only [Prod.mk.injEq] at h <;> omega)]
  rw [paper_eval, hite, show 2 * k + 2 + b - (2 * k + 3 + a) = b - a - 1 by ring,
    show 2 * k + 3 - (2 * k + 2 + b) = 1 - b by ring]
  rcases hab with h | h | h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
    norm_num [zeroOdometer]

/-- The one tile at `(2k+3, 2k+1) + (0, 2j)`, `1 ≤ j ≤ k+1`. -/
theorem paper_one_vp (k j a b : ℤ) (hk : 0 ≤ k) (hj : 1 ≤ j) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hab : (a, b) = (0, 0) ∨ (a, b) = (0, 1) ∨ (a, b) = (1, 0) ∨ (a, b) = (1, 1)) :
    paperNearStairValue (2 * k + 3) ((a, b) + ((0, 2 * j) + (2 * k + 3, 2 * k + 1)) + (0, 1)) =
      oneOdometer (a, b) + (j - 1) * (2 * k + 3 + a) + (-j) * (2 * k + 1 + 2 * j + b)
        + (1 - j + j * j - (j - 1) * (2 * k + 3) + j * (2 * k + 1)) := by
  rw [show (a, b) + ((0, 2 * j) + (2 * k + 3, 2 * k + 1)) + (0, 1) = (2 * k + 3 + a, 2 * k + 2 + 2 * j + b)
      from Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring)]
  rw [paper_eval, show 2 * k + 2 + 2 * j + b - (2 * k + 3 + a) = 2 * j - 1 + b - a by ring,
    show 2 * k + 3 - (2 * k + 2 + 2 * j + b) = 1 - 2 * j - b by ring,
    min_eq_left (show 1 - 2 * j - b ≤ 0 by omega),
    if_neg (show ¬((2 * k + 3 + a, 2 * k + 2 + 2 * j + b) = (0, 2 * k + 3 + 1)
      ∨ (2 * k + 3 + a, 2 * k + 2 + 2 * j + b) = (2 * k + 3 + 1, 2 * k + 3 - 1)) from by
        rintro (h | h) <;> simp only [Prod.mk.injEq] at h <;> omega)]
  rcases hab with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
  · rw [show 2 * j - 1 + 0 - 0 = 2 * (j - 1) + 1 by ring, sqd_odd]
    norm_num [oneOdometer]
    ring
  · rw [show 2 * j - 1 + 1 - 0 = 2 * j by ring, sqd_even]
    norm_num [oneOdometer]
    ring
  · rw [show 2 * j - 1 + 0 - 1 = 2 * (j - 1) by ring, sqd_even]
    norm_num [oneOdometer]
    ring
  · rw [show 2 * j - 1 + 1 - 1 = 2 * (j - 1) + 1 by ring, sqd_odd]
    norm_num [oneOdometer]
    ring

/-- The one tile of the reversed piece at `(0, 2j)`, `0 ≤ j ≤ k`. -/
theorem paper_one_vm (k j a b : ℤ) (hj0 : 0 ≤ j) (hjk : j ≤ k)
    (hab : (a, b) = (0, 0) ∨ (a, b) = (0, 1) ∨ (a, b) = (1, 0) ∨ (a, b) = (1, 1)) :
    paperNearStairValue (2 * k + 3) ((a, b) + (0, 2 * j) + (0, 1)) =
      oneOdometer (a, b) + j * a + (-j) * (2 * j + b) + j * (j - 1) := by
  rw [show (a, b) + (0, 2 * j) + (0, 1) = (a, 2 * j + b + 1)
      from Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring)]
  rw [paper_eval, min_eq_right (show (0 : ℤ) ≤ 2 * k + 3 - (2 * j + b + 1) by
      rcases hab with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> omega),
    if_neg (show ¬((a, 2 * j + b + 1) = (0, 2 * k + 3 + 1) ∨ (a, 2 * j + b + 1) = (2 * k + 3 + 1, 2 * k + 3 - 1))
      from by rintro (h | h) <;> simp only [Prod.mk.injEq] at h <;>
        rcases hab with h' | h' | h' | h' <;> simp only [Prod.mk.injEq] at h' <;> omega)]
  rcases hab with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
  · rw [show 2 * j + 0 + 1 - 0 = 2 * j + 1 by ring, sqd_odd]
    norm_num [oneOdometer]
    ring
  · rw [show 2 * j + 1 + 1 - 0 = 2 * (j + 1) by ring, sqd_even]
    norm_num [oneOdometer]
    ring
  · rw [show 2 * j + 0 + 1 - 1 = 2 * j by ring, sqd_even]
    norm_num [oneOdometer]
    ring
  · rw [show 2 * j + 1 + 1 - 1 = 2 * j + 1 by ring, sqd_odd]
    norm_num [oneOdometer]
    ring

/-- The zero tile of the reversed piece at `(0, 2k+1)`. -/
theorem paper_zero_vm (k a b : ℤ) (hk : 0 ≤ k) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb2 : b ≤ 2)
    (hab : (a, b) = (0, 0) ∨ (a, b) = (0, 1) ∨ (a, b) = (0, 2) ∨ (a, b) = (1, 0) ∨ (a, b) = (1, 1) ∨ (a, b) = (1, 2)) :
    paperNearStairValue (2 * k + 3) ((a, b) + (0, 2 * k + 1) + (0, 1)) =
      zeroOdometer (a, b) + (k + 1) * a + (-(k + 1)) * (2 * k + 1 + b) + k * (k + 1) := by
  rw [show (a, b) + (0, 2 * k + 1) + (0, 1) = (a, 2 * k + 2 + b)
      from Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring)]
  have hite : (if (a, 2 * k + 2 + b) = (0, 2 * k + 3 + 1)
      ∨ (a, 2 * k + 2 + b) = (2 * k + 3 + 1, 2 * k + 3 - 1) then (1 : ℤ) else 0)
      = if a = 0 ∧ b = 2 then 1 else 0 := by
    by_cases h02 : a = 0 ∧ b = 2
    · rw [if_pos h02, if_pos (show (a, 2 * k + 2 + b) = (0, 2 * k + 3 + 1)
        ∨ (a, 2 * k + 2 + b) = (2 * k + 3 + 1, 2 * k + 3 - 1) from
          Or.inl (Prod.ext (by omega) (by omega)))]
    · rw [if_neg h02, if_neg (show ¬((a, 2 * k + 2 + b) = (0, 2 * k + 3 + 1)
        ∨ (a, 2 * k + 2 + b) = (2 * k + 3 + 1, 2 * k + 3 - 1)) from by
          rintro (h | h) <;> simp only [Prod.mk.injEq] at h <;> omega)]
  rw [paper_eval, hite, show 2 * k + 3 - (2 * k + 2 + b) = 1 - b by ring]
  rcases hab with h | h | h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
  · rw [show 2 * k + 2 + 0 - 0 = 2 * (k + 1) by ring, sqd_even]
    norm_num [zeroOdometer]
    ring
  · rw [show 2 * k + 2 + 1 - 0 = 2 * (k + 1) + 1 by ring, sqd_odd]
    norm_num [zeroOdometer]
    ring
  · rw [show 2 * k + 2 + 2 - 0 = 2 * (k + 2) by ring, sqd_even]
    norm_num [zeroOdometer]
    ring
  · rw [show 2 * k + 2 + 0 - 1 = 2 * k + 1 by ring, sqd_odd]
    norm_num [zeroOdometer]
    ring
  · rw [show 2 * k + 2 + 1 - 1 = 2 * (k + 1) by ring, sqd_even]
    norm_num [zeroOdometer]
    ring
  · rw [show 2 * k + 2 + 2 - 1 = 2 * (k + 1) + 1 by ring, sqd_odd]
    norm_num [zeroOdometer]
    ring

/-! ### The odometer identities of the pieces, tile by tile -/

theorem vtAff_two_fwd (k j : ℕ) (hj1 : 1 ≤ j) (hjk : j ≤ k + 1) :
    vtAff (lettersOf (W2 k) false) j = ((j : ℤ) - 1, -(j : ℤ)) := by
  obtain ⟨p, rfl⟩ : ∃ p, j = p + 1 := ⟨j - 1, by omega⟩
  simp only [vtAff, vtCnt_two_fwd k p (by omega)]
  exact Prod.ext (by push_cast; ring) rfl

theorem vtAff_two_rev (k j : ℕ) (hjk : j ≤ k + 1) :
    vtAff (lettersOf (W2 k) true) j = ((j : ℤ), -(j : ℤ)) := by
  simp only [vtAff, vtCnt_two_rev k j hjk]

theorem vtAff_two_zero (k : ℕ) : vtAff (lettersOf (W2 k) false) 0 = (0, 0) := by
  simp [vtAff, vtCnt]

theorem hz0 : letterZTile Letter.p = ZTile.zero := rfl

theorem hz1 : letterZTile Letter.q = ZTile.one := rfl

/-- The zero tile of the forward piece at the anchor. -/
theorem zero_tile_vp (k : ℕ) (y : GInt) (hy : y ∈ tileShape ZTile.zero) :
    paperNearStairValue (2 * (k : ℤ) + 3) (y + ((0, 0) + (2 * (k : ℤ) + 3, 2 * (k : ℤ) + 1)) + (0, 1)) =
      (vpPiece (W2 k) (2 * (k : ℤ) + 3, 2 * (k : ℤ) + 1)).odo 0
        (y + ((0, 0) + (2 * (k : ℤ) + 3, 2 * (k : ℤ) + 1))) := by
  obtain ⟨a, b⟩ := y
  have hab : (a, b) = (0, 0) ∨ (a, b) = (0, 1) ∨ (a, b) = (0, 2) ∨ (a, b) = (1, 0) ∨ (a, b) = (1, 1)
      ∨ (a, b) = (1, 2) := by
    simpa [tileShape] using hy
  have ha : 0 ≤ a ∧ a ≤ 1 := by
    rcases hab with h | h | h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> omega
  have hb : 0 ≤ b ∧ b ≤ 2 := by
    rcases hab with h | h | h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> omega
  have hk : (0 : ℤ) ≤ (k : ℤ) := by positivity
  have hp0 : posF .vertical false (lettersOf (W2 k) false) 0 = (0, 0) := by simp [posF]; rfl
  rw [vpPiece_odo _ _ 0 (by simp [W2]), hfp0 k, hz0, hp0, vtAff_two_zero k]
  have hV0 : vtCP (lettersOf (W2 k) false) 0 = 0 := rfl
  rw [hV0]
  simp only [Prod.mk_zero_zero, zero_add]
  rw [paper_zero_vp (k : ℤ) a b hk ha.1 ha.2 hb.1 hb.2 hab, add_sub_cancel_right]
  simp [zTileOdo, zeroOdometer, ptDot]

/-- The one tile `j` of the forward piece, `1 ≤ j ≤ k+1`. -/
theorem one_tile_vp (k j : ℕ) (hj1 : 1 ≤ j) (hjk : j ≤ k + 1) (y : GInt) (hy : y ∈ tileShape ZTile.one) :
    paperNearStairValue (2 * (k : ℤ) + 3) (y + ((0, 2 * (j : ℤ)) + (2 * (k : ℤ) + 3, 2 * (k : ℤ) + 1)) + (0, 1)) =
      (vpPiece (W2 k) (2 * (k : ℤ) + 3, 2 * (k : ℤ) + 1)).odo j
        (y + ((0, 2 * (j : ℤ)) + (2 * (k : ℤ) + 3, 2 * (k : ℤ) + 1))) := by
  obtain ⟨a, b⟩ := y
  have hab : (a, b) = (0, 0) ∨ (a, b) = (0, 1) ∨ (a, b) = (1, 0) ∨ (a, b) = (1, 1) := by
    simpa [tileShape] using hy
  have ha : 0 ≤ a ∧ a ≤ 1 := by
    rcases hab with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> omega
  have hb : 0 ≤ b ∧ b ≤ 1 := by
    rcases hab with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> omega
  have hk : (0 : ℤ) ≤ (k : ℤ) := by positivity
  rw [vpPiece_odo _ _ j (by simp [W2]; omega), posF_two_fwd k j hjk, hfq k j hj1 hjk, hz1,
    vtAff_two_fwd k j hj1 hjk, vtCP_two_fwd k j hj1 hjk]
  rw [paper_one_vp (k : ℤ) (j : ℤ) a b hk (by exact_mod_cast hj1) ha.1 ha.2 hb.1 hb.2 hab]
  simp [zTileOdo, oneOdometer, ptDot]
  ring

/-- The one tile `j` of the reversed piece, `0 ≤ j ≤ k`. -/
theorem vm_one_tile (k j : ℕ) (hjk : j ≤ k) (y : GInt) (hy : y ∈ tileShape ZTile.one) :
    paperNearStairValue (2 * (k : ℤ) + 3) (y + (0, 2 * (j : ℤ)) + (0, 1)) =
      (piece (W2 k)).odo j (y + (0, 2 * (j : ℤ))) := by
  obtain ⟨a, b⟩ := y
  have hab : (a, b) = (0, 0) ∨ (a, b) = (0, 1) ∨ (a, b) = (1, 0) ∨ (a, b) = (1, 1) := by
    simpa [tileShape] using hy
  have hk : (0 : ℤ) ≤ (k : ℤ) := by positivity
  rw [piece_odo _ j (by simp [W2]; omega), posF_two_rev k j hjk, hrq k j (by omega), hz1,
    vtAff_two_rev k j (by omega), vtCM_two_rev k j hjk]
  rw [paper_one_vm (k : ℤ) (j : ℤ) a b (by positivity) (by exact_mod_cast hjk) hab]
  simp [zTileOdo, oneOdometer, ptDot]
  ring

/-- The zero tile of the reversed piece at `(0, 2k+1)`. -/
theorem vm_zero_tile (k : ℕ) (y : GInt) (hy : y ∈ tileShape ZTile.zero) :
    paperNearStairValue (2 * (k : ℤ) + 3) (y + (0, 2 * (k : ℤ) + 1) + (0, 1)) =
      (piece (W2 k)).odo (k + 1) (y + (0, 2 * (k : ℤ) + 1)) := by
  obtain ⟨a, b⟩ := y
  have hab : (a, b) = (0, 0) ∨ (a, b) = (0, 1) ∨ (a, b) = (0, 2) ∨ (a, b) = (1, 0) ∨ (a, b) = (1, 1)
      ∨ (a, b) = (1, 2) := by
    simpa [tileShape] using hy
  have ha : 0 ≤ a ∧ a ≤ 1 := by
    rcases hab with h | h | h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> omega
  have hb : 0 ≤ b ∧ b ≤ 2 := by
    rcases hab with h | h | h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> omega
  have hk : (0 : ℤ) ≤ (k : ℤ) := by positivity
  rw [piece_odo _ (k + 1) (by simp [W2]), posF_two_rev_last k, hrp k (k + 1) (by omega), hz0,
    vtAff_two_rev k (k + 1) le_rfl, vtCM_two_rev_last k]
  rw [paper_zero_vm (k : ℤ) a b hk ha.1 ha.2 hb.1 hb.2 hab]
  simp [zTileOdo, zeroOdometer, ptDot]
  ring

/-! ### The two pieces of the odd `2^k` word respect their strings -/

/-- The forward vertical base piece of the odd `2^k` word (`k ≥ 0`, so also the empty word's odd child) respects its string,
with the near-stair value as odometer. -/
theorem vp2_odd_respects (k : ℕ) :
    RespectsTiles .vertical false
      (vStringAt (vWordOf (List.replicate k Digit.two) false)
        (lastPosOf (hStringAt (hWordOf (List.replicate k Digit.two) false) (0, 0))))
      (fun x => paperNearStairValue (2 * (k : ℤ) + 3) (x + (0, 1))) := by
  rw [anchor_two k, wv_two k]
  have hR : (vpPiece (W2 k) (2 * (k : ℤ) + 3, 2 * (k : ℤ) + 1)).Respects .vertical false :=
    PTFamily.translate_respects _ _ _ _ (vtP_respects _)
  refine ⟨vpPiece (W2 k) (2 * (k : ℤ) + 3, 2 * (k : ℤ) + 1), vpPiece_ts _ _, ?_, hR⟩
  intro J hJ x hx
  rw [vpPiece_n] at hJ
  have hlen : (W2 k).length = k + 2 := by simp [W2]
  rw [hlen] at hJ
  rcases (show J = 0 ∨ 1 ≤ J by omega) with rfl | hJ1
  · unfold PTFamily.dom at hx
    rw [vpPiece_tile _ _ 0 (by simp [W2]), hfp0 k, hz0, posF_two_fwd k 0 (by omega)] at hx
    simp only [Nat.cast_zero, mul_zero] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact zero_tile_vp k y hy
  · unfold PTFamily.dom at hx
    rw [vpPiece_tile _ _ J (by simp [W2]; omega), hfq k J hJ1 (by omega), hz1,
      posF_two_fwd k J (by omega)] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact one_tile_vp k J hJ1 (by omega) y hy

/-- The reversed vertical base piece of the odd `2^k` word respects its string, anchored at `(0,0)`. -/
theorem vm2_odd_respects (k : ℕ) :
    RespectsTiles .vertical true
      (vRevStringAt (vWordOf (List.replicate k Digit.two) false).reverse (0, 0))
      (fun x => paperNearStairValue (2 * (k : ℤ) + 3) (x + (0, 1))) := by
  rw [wv_two k]
  have hR : (piece (W2 k)).Respects .vertical true := PTFamily.translate_respects _ _ _ _ (vtM_respects _)
  refine ⟨piece (W2 k), piece_ts _, ?_, hR⟩
  intro J hJ x hx
  rw [piece_n] at hJ
  have hlen : (W2 k).length = k + 2 := by simp [W2]
  rw [hlen] at hJ
  rcases (show J ≤ k ∨ J = k + 1 by omega) with hJk | rfl
  · unfold PTFamily.dom at hx
    rw [piece_tile _ J (by simp [W2]; omega), hrq k J (by omega), posF_two_rev k J hJk, hz1] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact vm_one_tile k J hJk y hy
  · unfold PTFamily.dom at hx
    rw [piece_tile _ (k + 1) (by simp [W2]), hrp k (k + 1) (by omega), posF_two_rev_last k, hz0] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact vm_zero_tile k y hy

end FLatticePaper.Tiles.BaseTwoOdd
