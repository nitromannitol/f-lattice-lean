import FLatticePaper.Tiles.StackedMoreover

/-! # Locality of the horizontal cross overlaps (the local check of the horizontal half of the Moreover)

For an almost palindrome `w` starting with `q` and ending with `p`, the plus tile `k` (on the forward string) meets a minus tile
`j` (on the reversed stacked string) only when `j = k` or `j + 1 = k` (`CrossLocal`). The proof uses three facts:

* the `x`-coordinates of the placed tiles increase by at least one per tile (every zero-one step has `x`-component `1` or `2`);
* the offset `plus k − minus k` of the fixed-offset lemma has `x`-component in `{-2, -1}`, and it is `offH` (exact for `0 < k`);
* for `k − j ∈ {2, 3}` the overlap is excluded by a finite check over the letters (`window2`, `window3`, by `decide`).

The statements here are proved; the horizontal half of the Moreover (the existence of the parameters) is not yet. -/

namespace FLatticePaper.Tiles

/-- The offset `plus k − minus k` of the horizontal stacked string at an index `k > 0` with plus letter `x`; `last` says that
`k` is the last index (lines 1361-1364 and the fixed-offset lemma). -/
def offH (x : Letter) (last : Bool) : GInt :=
  if last then ((-1 : ℤ), (1 : ℤ)) else if x = Letter.q then ((-2 : ℤ), (2 : ℤ)) else ((-1 : ℤ), (2 : ℤ))

/-- The reversed horizontal zero-one step (the minus string). -/
def rsH (a b : Letter) : GInt := stepOf .horizontal true a b

/-- Two tiles at a difference `E` overlap when some site of the first, shifted, is a site of the second. -/
def OverlapAt (A B : ZTile) (E : GInt) : Prop :=
  ∃ s ∈ tileShape A, ∃ t ∈ tileShape B, s - t = E

/-- The window check with two reversed steps (minus tiles `j, j+1, j+2 = k`). -/
theorem window2 : ∀ (x a b c : Letter) (last : Bool),
    ¬ OverlapAt (letterZTile x) (letterZTile a) (-(offH x last + rsH a b + rsH b c)) := by
  intro x a b c last
  unfold OverlapAt
  cases x <;> cases a <;> cases b <;> cases c <;> cases last <;> decide

/-- The window check with three reversed steps (minus tiles `j, …, j+3 = k`). -/
theorem window3 : ∀ (x a b c d : Letter) (last : Bool),
    ¬ OverlapAt (letterZTile x) (letterZTile a) (-(offH x last + rsH a b + rsH b c + rsH c d)) := by
  intro x a b c d last
  unfold OverlapAt
  cases x <;> cases a <;> cases b <;> cases c <;> cases d <;> cases last <;> decide

/-- A horizontal zero-one step has `x`-component at least one (forward and reversed). -/
theorem stepH_x_pos (a b : Letter) : 1 ≤ (stepOf .horizontal true a b).1 := by
  cases a <;> cases b <;> decide

/-- The `x`-coordinates of the reversed positions increase by at least one per tile. -/
theorem posRev_x_ge (ℓ : ℕ → Letter) (j m : ℕ) :
    (posF .horizontal true ℓ j).1 + (m : ℤ) ≤ (posF .horizontal true ℓ (j + m)).1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : posF .horizontal true ℓ (j + (m + 1)) =
        posF .horizontal true ℓ (j + m) + stepOf .horizontal true (ℓ (j + m)) (ℓ (j + m + 1)) := by
      rw [← Nat.add_assoc]; rfl
    rw [h1]
    have := stepH_x_pos (ℓ (j + m)) (ℓ (j + m + 1))
    simp only [Prod.fst_add]
    push_cast
    linarith

/-- The `x`-coordinates of the placed tiles of a zero-one string are at most two steps apart from the first. -/
theorem tileShape_x_bounds (x : Letter) (s : GInt) (hs : s ∈ tileShape (letterZTile x)) : 0 ≤ s.1 ∧ s.1 ≤ 1 := by
  cases x
  · simp only [letterZTile, tileShape, List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [letterZTile, tileShape, List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl <;> decide

/-- The reversed step of two consecutive minus letters, as the position difference. -/
theorem posRev_two (ℓ : ℕ → Letter) (j : ℕ) :
    posF .horizontal true ℓ (j + 2) = posF .horizontal true ℓ j + rsH (ℓ j) (ℓ (j + 1)) + rsH (ℓ (j + 1)) (ℓ (j + 2)) :=
  rfl

theorem posRev_three (ℓ : ℕ → Letter) (j : ℕ) :
    posF .horizontal true ℓ (j + 3) = posF .horizontal true ℓ j + rsH (ℓ j) (ℓ (j + 1)) + rsH (ℓ (j + 1)) (ℓ (j + 2))
      + rsH (ℓ (j + 2)) (ℓ (j + 3)) :=
  rfl

/-- The letters of the forward string are the letters of the word. -/
theorem lettersOf_false (w : BinaryWord) (k : ℕ) (hk : k < w.length) : lettersOf w false k = w[k] := by
  simp [lettersOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

/-- The letters of the reversed string are the letters of the reversed word. -/
theorem lettersOf_true (w : BinaryWord) (k : ℕ) (hk : k < w.length) :
    lettersOf w true k = w.reverse[k]'(by simp; omega) := by
  simp [lettersOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < w.reverse.length by simp; omega)]

theorem fixed_hplus (w : BinaryWord) (i : ℕ) (h : i + 1 < w.length) :
    posF .horizontal false (lettersOf w false) (i + 1) - posF .horizontal false (lettersOf w false) i =
      zeroOneHorizontalStep w[i + 1] := by
  have e : posF .horizontal false (lettersOf w false) (i + 1) =
      posF .horizontal false (lettersOf w false) i + zeroOneHorizontalStep (lettersOf w false (i + 1)) := rfl
  rw [e, add_sub_cancel_left, lettersOf_false w (i + 1) h]

theorem fixed_hminus (w : BinaryWord) (i : ℕ) (h : i + 1 < w.length) :
    (posF .horizontal true (lettersOf w true) (i + 1) - horizontalStackShift) -
        (posF .horizontal true (lettersOf w true) i - horizontalStackShift) =
      zeroOneHorizontalReversedStep (w.reverse[i]'(by simp; omega)) (w.reverse[i + 1]'(by simp; omega)) := by
  have e : posF .horizontal true (lettersOf w true) (i + 1) =
      posF .horizontal true (lettersOf w true) i +
        zeroOneHorizontalReversedStep (lettersOf w true i) (lettersOf w true (i + 1)) := rfl
  rw [sub_sub_sub_cancel_right, e, add_sub_cancel_left, lettersOf_true w i (by omega),
    lettersOf_true w (i + 1) h]

/-- The offset at the first index. -/
theorem fixed_hstack (w : BinaryWord) :
    posF .horizontal false (lettersOf w false) 0 -
        (posF .horizontal true (lettersOf w true) 0 - horizontalStackShift) = ((-1 : ℤ), (2 : ℤ)) := by
  simp [posF, horizontalStackShift]

/-- The offset `plus k − minus k` at `0 < k` is `offH` of the letter at `k` (fixed-offset lemma of the horizontal strings). -/
theorem fixed_off (w : BinaryWord) (hw : IsAlmostPalindrome w) (hf : w.head? = some Letter.q)
    (hl : w.getLast? = some Letter.p) (k : ℕ) (hk : k < w.length) (hk0 : 0 < k) :
    posF .horizontal false (lettersOf w false) k - (posF .horizontal true (lettersOf w true) k - horizontalStackShift) =
      offH (lettersOf w false k) (decide (k + 1 = w.length)) := by
  obtain ⟨h1, h2, h3⟩ := zeroOne_fixed_offsets_horizontal w hw hf hl
    (fun i => posF .horizontal false (lettersOf w false) i)
    (fun i => posF .horizontal true (lettersOf w true) i - horizontalStackShift)
    (fun i h => fixed_hplus w i h) (fun i h => fixed_hminus w i h) (fixed_hstack w)
  have hwk : w[k] = lettersOf w false k := (lettersOf_false w k hk).symm
  by_cases hlast : k + 1 = w.length
  · have hk' : k = w.length - 1 := by omega
    subst hk'
    have hd : decide (w.length - 1 + 1 = w.length) = true := by
      rw [decide_eq_true_iff]; omega
    rw [hd]
    simp only [offH, if_true]
    exact h3
  · have hlt : k + 1 < w.length := by omega
    have hd : decide (k + 1 = w.length) = false := by
      rw [decide_eq_false_iff_not]; exact hlast
    rw [hd]
    simp only [offH]
    cases hx : lettersOf w false k
    · simp only [Bool.false_eq_true, if_false]
      exact h2 k hlt hk0 (hwk.trans hx)
    · simp only [if_true]
      exact h1 k hlt hk0 (hwk.trans hx)

/-- The `k`-th placed tile of the forward string. -/
theorem zoF_tile (ℓ : ℕ → Letter) (n k : ℕ) (hk : k < n) :
    (zoForward ℓ n).getD k (ZTile.zero, (0 : GInt)) = (letterZTile (ℓ k), posF .horizontal false ℓ k) := by
  unfold zoForward
  rw [List.getD_eq_getElem _ _ (by simp [hk])]
  simp

/-- The `k`-th placed tile of the reversed stacked string. -/
theorem zoR_tile (ℓ : ℕ → Letter) (n k : ℕ) (hk : k < n) :
    (zoReversedStacked ℓ n).getD k (ZTile.zero, (0 : GInt)) =
      (letterZTile (ℓ k), posF .horizontal true ℓ k - horizontalStackShift) := by
  unfold zoReversedStacked
  rw [List.getD_eq_getElem _ _ (by simp [hk])]
  simp

theorem ptile_of_ts (P : PTFamily) (ts : List (ZTile × GInt)) (h : P.ts = ts) (k : ℕ) :
    P.tile k = ts.getD k (ZTile.zero, (0 : GInt)) := by
  unfold PTFamily.tile; rw [h]

/-- The `x`-component of the offset `plus k − minus k` is at most `-1` and at least `-2`, for every index. -/
theorem off_x_bounds (w : BinaryWord) (hw : IsAlmostPalindrome w) (hf : w.head? = some Letter.q)
    (hl : w.getLast? = some Letter.p) (k : ℕ) (hk : k < w.length) :
    -2 ≤ (posF .horizontal false (lettersOf w false) k -
        (posF .horizontal true (lettersOf w true) k - horizontalStackShift)).1 ∧
      (posF .horizontal false (lettersOf w false) k -
        (posF .horizontal true (lettersOf w true) k - horizontalStackShift)).1 ≤ -1 := by
  by_cases hk0 : k = 0
  · subst hk0
    rw [fixed_hstack w]
    simp
  · rw [fixed_off w hw hf hl k hk (Nat.pos_of_ne_zero hk0)]
    unfold offH
    split_ifs <;> simp

theorem crossLocal_horizontal (w : BinaryWord) (hw : IsAlmostPalindrome w) (hf : w.head? = some Letter.q)
    (hl : w.getLast? = some Letter.p) (P M : PTFamily)
    (hP : P.ts = zoForward (lettersOf w false) w.length)
    (hM : M.ts = zoReversedStacked (lettersOf w true) w.length) : CrossLocal P M := by
  intro k hk j hj hov
  obtain ⟨x, hxP, hxM⟩ := hov
  have hPn : P.n = w.length := by simp [PTFamily.n, hP, zoForward]
  have hMn : M.n = w.length := by simp [PTFamily.n, hM, zoReversedStacked]
  rw [hPn] at hk
  rw [hMn] at hj
  have hPt : P.tile k = (letterZTile (lettersOf w false k),
      posF .horizontal false (lettersOf w false) k) := by
    rw [ptile_of_ts P _ hP k, zoF_tile _ _ k hk]
  have hMt : M.tile j = (letterZTile (lettersOf w true j),
      posF .horizontal true (lettersOf w true) j - horizontalStackShift) := by
    rw [ptile_of_ts M _ hM j, zoR_tile _ _ j hj]
  unfold PTFamily.dom at hxP hxM
  rw [hPt, List.mem_map] at hxP
  rw [hMt, List.mem_map] at hxM
  obtain ⟨s, hs, hsx⟩ := hxP
  obtain ⟨t, ht, htx⟩ := hxM
  simp only at hsx htx
  have hsx' := congrArg Prod.fst (hsx.trans htx.symm)
  have hsy' := congrArg Prod.snd (hsx.trans htx.symm)
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hsx' hsy'
  have hs01 := tileShape_x_bounds _ s hs
  have ht01 := tileShape_x_bounds _ t ht
  have hob := off_x_bounds w hw hf hl k hk
  have hobj := off_x_bounds w hw hf hl k hk
  -- the component facts about the minus positions
  have hσ1 : horizontalStackShift.1 = -1 := rfl
  by_cases hA : k < j
  · -- j ≥ k + 1: the x-coordinates of the minus tiles grow by one per step
    have hmono := posRev_x_ge (lettersOf w true) k (j - k)
    rw [show k + (j - k) = j by omega] at hmono
    simp only [Prod.fst_sub] at hmono hob hobj
    omega
  by_cases hB : j + 4 ≤ k
  · have hmono := posRev_x_ge (lettersOf w true) j (k - j)
    rw [show j + (k - j) = k by omega] at hmono
    simp only [Prod.fst_sub] at hmono hob hobj
    omega
  have hc : k = j ∨ k = j + 1 ∨ k = j + 2 ∨ k = j + 3 := by omega
  rcases hc with hc | hc | hc | hc
  · exact Or.inl hc.symm
  · exact Or.inr hc.symm
  · exfalso
    subst hc
    have hoff := fixed_off w hw hf hl (j + 2) hk (by omega)
    have hpos := posRev_two (lettersOf w true) j
    have hfst : (posF .horizontal false (lettersOf w false) (j + 2) -
        (posF .horizontal true (lettersOf w true) (j + 2) - horizontalStackShift)) =
        offH (lettersOf w false (j + 2)) (decide (j + 2 + 1 = w.length)) := hoff
    apply window2 (lettersOf w false (j + 2)) (lettersOf w true j) (lettersOf w true (j + 1))
      (lettersOf w true (j + 2)) (decide (j + 2 + 1 = w.length))
    refine ⟨s, hs, t, ht, ?_⟩
    have hx1 := congrArg Prod.fst hfst
    have hx2 := congrArg Prod.snd hfst
    have hp1 := congrArg Prod.fst hpos
    have hp2 := congrArg Prod.snd hpos
    simp only [Prod.fst_sub, Prod.fst_add] at hx1 hp1 hsx'
    simp only [Prod.snd_sub, Prod.snd_add] at hx2 hp2 hsy'
    apply Prod.ext
    · simp only [Prod.fst_sub, Prod.fst_neg, Prod.fst_add]
      omega
    · simp only [Prod.snd_sub, Prod.snd_neg, Prod.snd_add]
      omega
  · exfalso
    subst hc
    have hoff := fixed_off w hw hf hl (j + 3) hk (by omega)
    have hpos := posRev_three (lettersOf w true) j
    have hfst : (posF .horizontal false (lettersOf w false) (j + 3) -
        (posF .horizontal true (lettersOf w true) (j + 3) - horizontalStackShift)) =
        offH (lettersOf w false (j + 3)) (decide (j + 3 + 1 = w.length)) := hoff
    apply window3 (lettersOf w false (j + 3)) (lettersOf w true j) (lettersOf w true (j + 1))
      (lettersOf w true (j + 2)) (lettersOf w true (j + 3)) (decide (j + 3 + 1 = w.length))
    refine ⟨s, hs, t, ht, ?_⟩
    have hx1 := congrArg Prod.fst hfst
    have hx2 := congrArg Prod.snd hfst
    have hp1 := congrArg Prod.fst hpos
    have hp2 := congrArg Prod.snd hpos
    simp only [Prod.fst_sub, Prod.fst_add] at hx1 hp1 hsx'
    simp only [Prod.snd_sub, Prod.snd_add] at hx2 hp2 hsy'
    apply Prod.ext
    · simp only [Prod.fst_sub, Prod.fst_neg, Prod.fst_add]
      omega
    · simp only [Prod.snd_sub, Prod.snd_neg, Prod.snd_add]
      omega

end FLatticePaper.Tiles
