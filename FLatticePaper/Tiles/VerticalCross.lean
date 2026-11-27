import FLatticePaper.Tiles.VerticalWithin

/-! # The cross part of the vertical Moreover: letter facts and the constant identity

For an almost palindrome `w = p · mid · q` (`mid` a palindrome) the reversed word agrees with `w` on the middle positions:
`w[i] = w[n-1-i]` for `1 ≤ i ≤ n-2`. The first letters are `p` (forward) and `q` (reversed), the last ones `q` and `p`.
The reversed prefix counts of `q` exceed the forward ones by one for `1 ≤ j ≤ n-1`, and the constant of the reversed family is
the constant of the forward family minus `vtDelta j` (`vtCM_eq`, by a finite case analysis per step). -/

namespace FLatticePaper.Tiles

theorem vt_mid_getD (w : BinaryWord) (hw : IsAlmostPalindrome w) (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 2 ≤ w.length) :
    w.getD i .p = w.getD (w.length - 1 - i) .p := by
  obtain ⟨f, l, mid, hmid, rfl⟩ := hw
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  have hlen : (f :: (mid ++ [l])).length = mid.length + 2 := by simp
  have hi' : i' < mid.length := by omega
  have hj : mid.length - 1 - i' < mid.length := by omega
  have e1 : (f :: (mid ++ [l])).getD (i' + 1) .p = mid.getD i' .p := by
    rw [List.getD_cons_succ, List.getD_append _ _ _ _ hi']
  have e2 : (f :: (mid ++ [l])).getD ((f :: (mid ++ [l])).length - 1 - (i' + 1)) .p
      = mid.getD (mid.length - 1 - i') .p := by
    have hidx : (f :: (mid ++ [l])).length - 1 - (i' + 1) = (mid.length - 1 - i') + 1 := by
      omega
    rw [hidx, List.getD_cons_succ, List.getD_append _ _ _ _ hj]
  have key : ∀ j, j < mid.length → mid.reverse.getD j .p = mid.getD (mid.length - 1 - j) .p := by
    intro j hj'
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_reverse (by simpa using hj')]
  have hpal : mid.getD i' .p = mid.getD (mid.length - 1 - i') .p := by
    have h := key (mid.length - 1 - i') hj
    rw [hmid] at h
    have h2' : mid.length - 1 - (mid.length - 1 - i') = i' := by omega
    rw [h2'] at h
    exact h.symm
  rw [e1, e2]
  exact hpal

theorem lettersTrue_eq (w : BinaryWord) (i : ℕ) (hi : i < w.length) :
    lettersOf w true i = w.getD (w.length - 1 - i) .p := by
  simp only [lettersOf, ↓reduceIte, List.getD_eq_getElem?_getD]
  rw [List.getElem?_reverse hi]

theorem lettersFalse_eq (w : BinaryWord) (i : ℕ) : lettersOf w false i = w.getD i .p := by
  simp [lettersOf]

theorem vt_fwd_zero (w : BinaryWord) (hf : w.head? = some .p) : lettersOf w false 0 = .p := by
  rw [lettersFalse_eq]
  exact getD_zero_of_head? hf

theorem vt_fwd_last (w : BinaryWord) (hl : w.getLast? = some .q) :
    lettersOf w false (w.length - 1) = .q := by
  rw [lettersFalse_eq]
  exact getD_last_of_getLast? hl

theorem vt_rev_zero (w : BinaryWord) (hn : 0 < w.length) (hl : w.getLast? = some .q) :
    lettersOf w true 0 = .q := by
  rw [lettersTrue_eq w 0 hn]
  simpa using getD_last_of_getLast? hl

theorem vt_rev_last (w : BinaryWord) (hn : 0 < w.length) (hf : w.head? = some .p) :
    lettersOf w true (w.length - 1) = .p := by
  rw [lettersTrue_eq w (w.length - 1) (by omega)]
  have h0 : w.length - 1 - (w.length - 1) = 0 := by omega
  rw [h0]
  exact getD_zero_of_head? hf

/-- The middle letters of the reversed word are those of the forward word. -/
theorem vt_mid_letters (w : BinaryWord) (hw : IsAlmostPalindrome w) (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 2 ≤ w.length) :
    lettersOf w true i = lettersOf w false i := by
  rw [lettersTrue_eq w i (by omega), lettersFalse_eq, vt_mid_getD w hw i h1 h2]

/-- The reversed prefix counts of `q` exceed the forward ones by one, for `1 ≤ j < n`. -/
theorem vt_cnt_rev (w : BinaryWord) (hw : IsAlmostPalindrome w) (hf : w.head? = some .p)
    (hl : w.getLast? = some .q) (hn : 2 ≤ w.length) (j : ℕ) (h1 : 1 ≤ j) (hj : j < w.length) :
    vtCnt (lettersOf w true) j = vtCnt (lettersOf w false) j + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  clear h1
  induction m with
  | zero =>
    simp only [vtCnt, vt_rev_zero w (by omega) hl, vt_fwd_zero w hf]
    simp
  | succ m ih =>
    have ih' := ih (by omega)
    have hm := vt_mid_letters w hw (m + 1) (by omega) (by omega)
    show vtCnt (lettersOf w true) (m + 1) + (if lettersOf w true (m + 1) = Letter.q then 1 else 0)
      = vtCnt (lettersOf w false) (m + 1) + (if lettersOf w false (m + 1) = Letter.q then 1 else 0) + 1
    rw [ih', hm]
    ring

/-- The closed form of the constant difference: the per-letter increments of the centred constants. -/
def vtDeltaF (Z : Letter) (c j : ℤ) : ℤ := if Z = Letter.q then -c + j else -2 * c + j

/-- The constant difference `vtCP j - vtCM j` for the forward and reversed families. -/
def vtDelta (w : BinaryWord) (j : ℕ) : ℤ :=
  if j = 0 then 0
  else if j + 1 = w.length then -vtCnt (lettersOf w false) j
  else vtDeltaF (lettersOf w false j) (vtCnt (lettersOf w false) j) (j : ℤ)

theorem vtDelta_zero (w : BinaryWord) : vtDelta w 0 = 0 := by
  simp [vtDelta]

theorem vtDelta_last (w : BinaryWord) (j : ℕ) (hj : 1 ≤ j) (hjn : j + 1 = w.length) :
    vtDelta w j = -vtCnt (lettersOf w false) j := by
  unfold vtDelta
  rw [if_neg (by omega), if_pos hjn]

theorem vtDelta_mid (w : BinaryWord) (j : ℕ) (hj : 1 ≤ j) (hjn : j + 1 < w.length) :
    vtDelta w j = vtDeltaF (lettersOf w false j) (vtCnt (lettersOf w false) j) (j : ℤ) := by
  unfold vtDelta
  rw [if_neg (by omega), if_neg (by omega)]

/-- The first step: the constant difference at index one (letter identity). -/
theorem vt_identA (Y : Letter) :
    vtDeltaF Y 0 1 = vtBetaP Letter.p Y - vtBetaM Letter.q Y := by
  cases Y <;> norm_num [vtDeltaF, vtBetaP, vtBetaM]

/-- The middle step of the constant difference (letter identity). -/
theorem vt_identB (X Y : Letter) (c j : ℤ) :
    vtDeltaF Y (c + (if X = Letter.q then 1 else 0)) (j + 1) - vtDeltaF X c j
      = vtBetaP X Y - vtBetaM X Y
        + (c * (zeroOneVerticalStep Y).1 + (-j) * (zeroOneVerticalStep Y).2)
        - ((c + 1) * (zeroOneVerticalReversedStep X Y).1 + (-j) * (zeroOneVerticalReversedStep X Y).2) := by
  cases X <;> cases Y <;> simp [vtDeltaF, vtBetaP, vtBetaM, zeroOneVerticalStep, zeroOneVerticalReversedStep] <;> ring

/-- The last step of the constant difference (letter identity). -/
theorem vt_identC (X : Letter) (c j : ℤ) :
    -(c + (if X = Letter.q then 1 else 0)) - vtDeltaF X c j
      = vtBetaP X Letter.q - vtBetaM X Letter.p
        + (c * (zeroOneVerticalStep Letter.q).1 + (-j) * (zeroOneVerticalStep Letter.q).2)
        - ((c + 1) * (zeroOneVerticalReversedStep X Letter.p).1 + (-j) * (zeroOneVerticalReversedStep X Letter.p).2) := by
  cases X <;> simp [vtDeltaF, vtBetaP, vtBetaM, zeroOneVerticalStep, zeroOneVerticalReversedStep] <;> ring

/-- The reversed constants are the forward constants minus `vtDelta`. -/
theorem vtCM_eq (w : BinaryWord) (hw : IsAlmostPalindrome w) (hf : w.head? = some .p)
    (hl : w.getLast? = some .q) (hn : 2 ≤ w.length) (j : ℕ) (hj : j < w.length) :
    vtCM (lettersOf w true) j = vtCP (lettersOf w false) j - vtDelta w j := by
  induction j with
  | zero => simp [vtCM, vtCP, vtDelta_zero]
  | succ j ih =>
    have ih' := ih (by omega)
    simp only [vtCM, vtCP]
    rw [ih']
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · -- the first step
      have hA0 : vtAff (lettersOf w true) 0 = 0 := by simp [vtAff, vtCnt]
      have hB0 : vtAff (lettersOf w false) 0 = 0 := by simp [vtAff, vtCnt]
      rw [hA0, hB0, vtDelta_zero, vt_rev_zero w (by omega) hl, vt_fwd_zero w hf]
      simp only [vtCP, ptDot, Prod.fst_zero, Prod.snd_zero, zero_mul, add_zero, sub_zero, zero_add]
      by_cases hn2 : 1 + 1 = w.length
      · have e1 : lettersOf w false 1 = .q := by
          rw [show (1 : ℕ) = w.length - 1 by omega]
          exact vt_fwd_last w hl
        have e2 : lettersOf w true 1 = .p := by
          rw [show (1 : ℕ) = w.length - 1 by omega]
          exact vt_rev_last w (by omega) hf
        rw [e1, e2, vtDelta_last w 1 le_rfl hn2]
        have hc1 : vtCnt (lettersOf w false) 1 = 0 := by simp [vtCnt, vt_fwd_zero w hf]
        rw [hc1]
        norm_num [vtBetaP, vtBetaM]
      · have hm := vt_mid_letters w hw 1 le_rfl (by omega)
        rw [hm, vtDelta_mid w 1 le_rfl (by omega)]
        have hc1 : vtCnt (lettersOf w false) 1 = 0 := by simp [vtCnt, vt_fwd_zero w hf]
        rw [hc1]
        have := vt_identA (lettersOf w false 1)
        simp only [Nat.cast_one] at this ⊢
        linarith
    · -- the middle steps and the last step
      have hc := vt_cnt_rev w hw hf hl hn j hj1 (by omega)
      have hdj := vtDelta_mid w j hj1 (by omega)
      by_cases hB : j + 2 < w.length
      · have m1 := vt_mid_letters w hw j hj1 (by omega)
        have m2 := vt_mid_letters w hw (j + 1) (by omega) (by omega)
        rw [hdj, vtDelta_mid w (j + 1) (by omega) (by omega)]
        simp only [vtAff, ptDot]
        rw [m1, m2, hc]
        have hcn : vtCnt (lettersOf w false) (j + 1)
            = vtCnt (lettersOf w false) j + (if lettersOf w false j = Letter.q then 1 else 0) := rfl
        rw [hcn]
        push_cast
        have hid := vt_identB (lettersOf w false j) (lettersOf w false (j + 1))
          (vtCnt (lettersOf w false) j) (j : ℤ)
        linarith [hid]
      · have hjn : j + 2 = w.length := by omega
        have e1 : lettersOf w false (j + 1) = .q := by
          rw [show j + 1 = w.length - 1 by omega]
          exact vt_fwd_last w hl
        have e2 : lettersOf w true (j + 1) = .p := by
          rw [show j + 1 = w.length - 1 by omega]
          exact vt_rev_last w (by omega) hf
        have m1 := vt_mid_letters w hw j hj1 (by omega)
        rw [hdj, vtDelta_last w (j + 1) (by omega) (by omega)]
        simp only [vtAff, ptDot]
        rw [m1, e1, e2, hc]
        have hcn : vtCnt (lettersOf w false) (j + 1)
            = vtCnt (lettersOf w false) j + (if lettersOf w false j = Letter.q then 1 else 0) := rfl
        rw [hcn]
        have hid := vt_identC (lettersOf w false j) (vtCnt (lettersOf w false) j) (j : ℤ)
        linarith [hid]

end FLatticePaper.Tiles
