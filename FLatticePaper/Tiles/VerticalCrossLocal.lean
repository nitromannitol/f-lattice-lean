import FLatticePaper.Tiles.VerticalCross

/-! # Locality of the cross overlaps of the vertical families

The fixed offset `P_j - M_j` of the forward and reversed tile positions is `vtG (ℓ'_j)` for `j ≤ n-2` (the vertical
fixed-offset lemma `zeroOne_fixed_offsets_vertical`). An overlap `x` of the tiles `k` and `j` gives `v - u = P_k - M_j`, with
`u` a tile point of the letter `ℓ_k` and `v` one of `ℓ'_j`. Tiles at distance two or three never overlap (finite checks over
the letters), and at distance at least four the `y`-coordinates of the positions separate the tiles. -/

namespace FLatticePaper.Tiles

/-- The fixed offset of the vertical families by the letter of the reversed family. -/
def vtG (m : Letter) : GInt :=
  if m = Letter.q then ((-1 : ℤ), (-1 : ℤ)) else ((-2 : ℤ), (-1 : ℤ))

theorem vtG_snd (m : Letter) : (vtG m).2 = -1 := by
  unfold vtG
  split_ifs <;> rfl

theorem vtNoOv2 : ∀ a m b c : Letter, ∀ u ∈ tileShape (letterZTile a), ∀ v ∈ tileShape (letterZTile m),
    v - u ≠ zeroOneVerticalStep b + zeroOneVerticalStep c + vtG m := by
  intro a m b c; cases a <;> cases m <;> cases b <;> cases c <;> decide

theorem vtNoOv3 : ∀ a m b c d : Letter, ∀ u ∈ tileShape (letterZTile a), ∀ v ∈ tileShape (letterZTile m),
    v - u ≠ zeroOneVerticalStep b + zeroOneVerticalStep c + zeroOneVerticalStep d + vtG m := by
  intro a m b c d; cases a <;> cases m <;> cases b <;> cases c <;> cases d <;> decide

theorem vtNoOvR2 : ∀ a m0 m1 m2 : Letter, ∀ u ∈ tileShape (letterZTile a), ∀ v ∈ tileShape (letterZTile m2),
    v - u ≠ vtG m0 - zeroOneVerticalReversedStep m0 m1 - zeroOneVerticalReversedStep m1 m2 := by
  intro a m0 m1 m2; cases a <;> cases m0 <;> cases m1 <;> cases m2 <;> decide

theorem vtNoOvR3 : ∀ a m0 m1 m2 m3 : Letter, ∀ u ∈ tileShape (letterZTile a), ∀ v ∈ tileShape (letterZTile m3),
    v - u ≠ vtG m0 - zeroOneVerticalReversedStep m0 m1 - zeroOneVerticalReversedStep m1 m2
      - zeroOneVerticalReversedStep m2 m3 := by
  intro a m0 m1 m2 m3; cases a <;> cases m0 <;> cases m1 <;> cases m2 <;> cases m3 <;> decide

theorem lettersFalse_getElem (w : BinaryWord) (i : ℕ) (h : i < w.length) :
    lettersOf w false i = w[i] := by
  rw [lettersFalse_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem lettersTrue_getElem (w : BinaryWord) (i : ℕ) (h' : i < w.reverse.length) :
    lettersOf w true i = w.reverse[i]'h' := by
  simp only [lettersOf, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h', Option.getD_some]

/-- The fixed offset of the vertical families, for `j + 2 ≤ n` (from the vertical fixed-offset lemma). -/
theorem vt_fixed_le (w : BinaryWord) (hw : IsAlmostPalindrome w) (hf : w.head? = some .p)
    (hl : w.getLast? = some .q) (hn : 2 ≤ w.length) (j : ℕ) (hj : j + 2 ≤ w.length) :
    posF .vertical false (lettersOf w false) j
      - (posF .vertical true (lettersOf w true) j - verticalStackShift) = vtG (lettersOf w true j) := by
  have hplus : ∀ i (h : i + 1 < w.length),
      posF .vertical false (lettersOf w false) (i + 1) - posF .vertical false (lettersOf w false) i
        = zeroOneVerticalStep w[i + 1] := by
    intro i h
    rw [show posF .vertical false (lettersOf w false) (i + 1)
        = posF .vertical false (lettersOf w false) i + zeroOneVerticalStep (lettersOf w false (i + 1)) from rfl,
      add_sub_cancel_left, lettersFalse_getElem w (i + 1) h]
  have hminus : ∀ i (h : i + 1 < w.length),
      (posF .vertical true (lettersOf w true) (i + 1) - verticalStackShift)
        - (posF .vertical true (lettersOf w true) i - verticalStackShift)
        = zeroOneVerticalReversedStep (w.reverse[i]'(by simp; omega)) (w.reverse[i + 1]'(by simp; omega)) := by
    intro i h
    rw [show posF .vertical true (lettersOf w true) (i + 1)
        = posF .vertical true (lettersOf w true) i
          + zeroOneVerticalReversedStep (lettersOf w true i) (lettersOf w true (i + 1)) from rfl,
      lettersTrue_getElem w i (by rw [List.length_reverse]; omega),
      lettersTrue_getElem w (i + 1) (by rw [List.length_reverse]; omega)]
    abel
  have hstack : posF .vertical false (lettersOf w false) 0
      - (posF .vertical true (lettersOf w true) 0 - verticalStackShift) = ((-1 : ℤ), (-1 : ℤ)) := by
    simp [posF, verticalStackShift]
  obtain ⟨hA, hB, hC⟩ := zeroOne_fixed_offsets_vertical w hw hf hl
    (fun i => posF .vertical false (lettersOf w false) i)
    (fun i => posF .vertical true (lettersOf w true) i - verticalStackShift) hplus hminus hstack
  rcases Nat.eq_zero_or_pos j with rfl | hj1
  · rw [vt_rev_zero w (by omega) hl]
    simp only [vtG, if_true]
    exact hstack
  · have hmid := vt_mid_letters w hw j hj1 (by omega)
    rw [hmid]
    by_cases hq : lettersOf w false j = Letter.q
    · have hwq : w[j]'(by omega) = Letter.q := by
        rw [← lettersFalse_getElem w j (by omega)]
        exact hq
      have := hA j (by omega) hj1 hwq
      simp only [vtG, hq, if_true] at this ⊢
      exact this
    · have hp : lettersOf w false j = Letter.p := by
        revert hq
        cases lettersOf w false j <;> simp
      have hwp : w[j]'(by omega) = Letter.p := by
        rw [← lettersFalse_getElem w j (by omega)]
        exact hp
      have := hB j (by omega) hj1 hwp
      simp only [vtG, hp] at this ⊢
      simp only [if_neg (show Letter.p ≠ Letter.q by decide)]
      exact this

/-- Locality of the cross overlaps: the tiles `k` of the forward family and `j` of the reversed one meet only if
`j ∈ {k-1, k, k+1}`. -/
theorem vt_cross_local (w : BinaryWord) (hw : IsAlmostPalindrome w) (hf : w.head? = some .p)
    (hl : w.getLast? = some .q) (hn : 2 ≤ w.length) (k j : ℕ) (hk : k < w.length) (hj : j < w.length)
    (x : GInt) (hxP : x ∈ (vtP w).dom k) (hxM : x ∈ (vtM w).dom j) :
    j = k ∨ j + 1 = k ∨ k + 1 = j := by
  rw [vtP_mem w k hk] at hxP
  rw [vtM_mem w j hj] at hxM
  obtain ⟨u, hu, hux⟩ := hxP
  obtain ⟨v, hv, hvx⟩ := hxM
  have hdiff : v - u = posF .vertical false (lettersOf w false) k
      - (posF .vertical true (lettersOf w true) j - verticalStackShift) := by
    rw [← hux] at hvx
    calc v - u = (v + (posF .vertical true (lettersOf w true) j - verticalStackShift))
          - (posF .vertical true (lettersOf w true) j - verticalStackShift) - u := by abel
      _ = (u + posF .vertical false (lettersOf w false) k) - (posF .vertical true (lettersOf w true) j - verticalStackShift) - u := by rw [hvx]
      _ = _ := by abel
  have hr1 := vtRows _ u hu
  have hr2 := vtRows _ v hv
  rcases lt_trichotomy k j with hkj | rfl | hkj
  · -- k < j: the tiles of the reversed family lie ahead
    by_cases h1 : j = k + 1
    · exact Or.inr (Or.inr (by omega))
    · exfalso
      obtain ⟨d, rfl⟩ : ∃ d, j = k + d := ⟨j - k, by omega⟩
      rcases (show d = 2 ∨ d = 3 ∨ 4 ≤ d by omega) with rfl | rfl | hd4
      · have e1 : posF .vertical true (lettersOf w true) (k + 1)
            = posF .vertical true (lettersOf w true) k
              + zeroOneVerticalReversedStep (lettersOf w true k) (lettersOf w true (k + 1)) := rfl
        have e2 : posF .vertical true (lettersOf w true) (k + 2)
            = posF .vertical true (lettersOf w true) (k + 1)
              + zeroOneVerticalReversedStep (lettersOf w true (k + 1)) (lettersOf w true (k + 2)) := rfl
        have hf2 := vt_fixed_le w hw hf hl hn k (by omega)
        have hdiff2 : v - u = vtG (lettersOf w true k)
            - zeroOneVerticalReversedStep (lettersOf w true k) (lettersOf w true (k + 1))
            - zeroOneVerticalReversedStep (lettersOf w true (k + 1)) (lettersOf w true (k + 2)) := by
          rw [hdiff, e2, e1, ← hf2]
          abel
        exact vtNoOvR2 _ _ _ _ u hu v hv hdiff2
      · have e1 : posF .vertical true (lettersOf w true) (k + 1)
            = posF .vertical true (lettersOf w true) k
              + zeroOneVerticalReversedStep (lettersOf w true k) (lettersOf w true (k + 1)) := rfl
        have e2 : posF .vertical true (lettersOf w true) (k + 2)
            = posF .vertical true (lettersOf w true) (k + 1)
              + zeroOneVerticalReversedStep (lettersOf w true (k + 1)) (lettersOf w true (k + 2)) := rfl
        have e3 : posF .vertical true (lettersOf w true) (k + 3)
            = posF .vertical true (lettersOf w true) (k + 2)
              + zeroOneVerticalReversedStep (lettersOf w true (k + 2)) (lettersOf w true (k + 3)) := rfl
        have hf2 := vt_fixed_le w hw hf hl hn k (by omega)
        have hdiff3 : v - u = vtG (lettersOf w true k)
            - zeroOneVerticalReversedStep (lettersOf w true k) (lettersOf w true (k + 1))
            - zeroOneVerticalReversedStep (lettersOf w true (k + 1)) (lettersOf w true (k + 2))
            - zeroOneVerticalReversedStep (lettersOf w true (k + 2)) (lettersOf w true (k + 3)) := by
          rw [hdiff, e3, e2, e1, ← hf2]
          abel
        exact vtNoOvR3 _ _ _ _ _ u hu v hv hdiff3
      · have hk4 : k + 2 ≤ w.length := by omega
        have hf2 := vt_fixed_le w hw hf hl hn k hk4
        have hy := vtPos_y_ge_M (lettersOf w true) k d
        have hGk := vtG_snd (lettersOf w true k)
        have h2 := congrArg Prod.snd hdiff
        have h3 := congrArg Prod.snd hf2
        simp only [Prod.snd_sub, verticalStackShift] at h2 h3
        rw [hGk] at h3
        omega
  · exact Or.inl rfl
  · -- j < k: the tiles of the forward family lie ahead
    by_cases h1 : k = j + 1
    · exact Or.inr (Or.inl (by omega))
    · exfalso
      obtain ⟨d, rfl⟩ : ∃ d, k = j + d := ⟨k - j, by omega⟩
      rcases (show d = 2 ∨ d = 3 ∨ 4 ≤ d by omega) with rfl | rfl | hd4
      · have e1 : posF .vertical false (lettersOf w false) (j + 1)
            = posF .vertical false (lettersOf w false) j
              + zeroOneVerticalStep (lettersOf w false (j + 1)) := rfl
        have e2 : posF .vertical false (lettersOf w false) (j + 2)
            = posF .vertical false (lettersOf w false) (j + 1)
              + zeroOneVerticalStep (lettersOf w false (j + 2)) := rfl
        have hf2 := vt_fixed_le w hw hf hl hn j (by omega)
        have hdiff2 : v - u = zeroOneVerticalStep (lettersOf w false (j + 1))
            + zeroOneVerticalStep (lettersOf w false (j + 2)) + vtG (lettersOf w true j) := by
          rw [hdiff, e2, e1, ← hf2]
          abel
        exact vtNoOv2 _ _ _ _ u hu v hv hdiff2
      · have e1 : posF .vertical false (lettersOf w false) (j + 1)
            = posF .vertical false (lettersOf w false) j
              + zeroOneVerticalStep (lettersOf w false (j + 1)) := rfl
        have e2 : posF .vertical false (lettersOf w false) (j + 2)
            = posF .vertical false (lettersOf w false) (j + 1)
              + zeroOneVerticalStep (lettersOf w false (j + 2)) := rfl
        have e3 : posF .vertical false (lettersOf w false) (j + 3)
            = posF .vertical false (lettersOf w false) (j + 2)
              + zeroOneVerticalStep (lettersOf w false (j + 3)) := rfl
        have hf2 := vt_fixed_le w hw hf hl hn j (by omega)
        have hdiff3 : v - u = zeroOneVerticalStep (lettersOf w false (j + 1))
            + zeroOneVerticalStep (lettersOf w false (j + 2))
            + zeroOneVerticalStep (lettersOf w false (j + 3)) + vtG (lettersOf w true j) := by
          rw [hdiff, e3, e2, e1, ← hf2]
          abel
        exact vtNoOv3 _ _ _ _ _ u hu v hv hdiff3
      · have hj2 : j + 2 ≤ w.length := by omega
        have hf2 := vt_fixed_le w hw hf hl hn j hj2
        have hy := vtPos_y_ge_P (lettersOf w false) j d
        have hGj := vtG_snd (lettersOf w true j)
        have h2 := congrArg Prod.snd hdiff
        have h3 := congrArg Prod.snd hf2
        simp only [Prod.snd_sub, verticalStackShift] at h2 h3
        rw [hGj] at h3
        omega

end FLatticePaper.Tiles
