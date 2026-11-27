import FLatticePaper.Tiles.HorizontalEnlarged
import FLatticePaper.Tiles.VerticalCross

/-! # The cross part of the horizontal Moreover with the enlarged tiles

The overlap of a forward tile `k` (tile type `hTt (ℓ (k-1)) (ℓ k)`) and a reversed tile `j` (type `hTt (ℓ' (j-1)) (ℓ' j)`) is
`v - u = P_k - M_j`. The offset `P_k - M_k` is the fixed offset (`offH`, or `(-1,2)` at the first index), and `M_k - M_j` is a sum of
reversed steps. Distances two to four never overlap (finite checks on letters, with no relation between the forward and reversed
letters); distances five and beyond by the `x`-coordinate; the adjacent index `j = k+1` by the relation `ℓ'_k = ℓ_k` (middle) and
the first index. The identities at equal index and at `j = k-1` are finite checks on the tile types and the constants `alphaH`,
`cstH` of the reversed letter. -/

namespace FLatticePaper.Tiles

/-! ## Letter-level decides -/

theorem hcL2 : ∀ pp x pm m0 m1 m2 : Letter, ∀ last : Bool, ∀ u ∈ tileShape (hTt pp x), ∀ v ∈ tileShape (hTt pm m0),
    v - u ≠ offH x last + (zeroOneHorizontalReversedStep m0 m1 + zeroOneHorizontalReversedStep m1 m2) := by
  intro pp x pm m0 m1 m2 last
  cases pp <;> cases x <;> cases pm <;> cases m0 <;> cases m1 <;> cases m2 <;> cases last <;> decide

theorem hcL3 : ∀ pp x pm m0 m1 m2 m3 : Letter, ∀ last : Bool, ∀ u ∈ tileShape (hTt pp x), ∀ v ∈ tileShape (hTt pm m0),
    v - u ≠ offH x last + (zeroOneHorizontalReversedStep m0 m1 + zeroOneHorizontalReversedStep m1 m2
      + zeroOneHorizontalReversedStep m2 m3) := by
  intro pp x pm m0 m1 m2 m3 last
  cases pp <;> cases x <;> cases pm <;> cases m0 <;> cases m1 <;> cases m2 <;> cases m3 <;> cases last <;> decide

theorem hcL4 : ∀ pp x pm m0 m1 m2 m3 m4 : Letter, ∀ last : Bool, ∀ u ∈ tileShape (hTt pp x), ∀ v ∈ tileShape (hTt pm m0),
    v - u ≠ offH x last + (zeroOneHorizontalReversedStep m0 m1 + zeroOneHorizontalReversedStep m1 m2
      + zeroOneHorizontalReversedStep m2 m3 + zeroOneHorizontalReversedStep m3 m4) := by
  intro pp x pm m0 m1 m2 m3 m4 last
  cases pp <;> cases x <;> cases pm <;> cases m0 <;> cases m1 <;> cases m2 <;> cases m3 <;> cases m4 <;> cases last <;>
    decide

/-- The adjacent overlap for a middle index: the forward tile `k` and the reversed tile `k+1` with `ℓ'_k = ℓ_k`. -/
theorem hcL1 : ∀ pp m0 m1 : Letter, ∀ u ∈ tileShape (hTt pp m0), ∀ v ∈ tileShape (hTt m0 m1),
    v - u ≠ offH m0 false - zeroOneHorizontalReversedStep m0 m1 := by
  intro pp m0 m1; cases pp <;> cases m0 <;> cases m1 <;> decide

/-- The adjacent overlap at the first index: the forward tile `0` (`q`, previous `p`) and the reversed tile `1`. -/
theorem hcL1k0 : ∀ m1 : Letter, ∀ u ∈ tileShape (hTt Letter.p Letter.q), ∀ v ∈ tileShape (hTt Letter.p m1),
    v - u ≠ ((-1 : ℤ), (2 : ℤ)) - zeroOneHorizontalReversedStep Letter.p m1 := by
  intro m1; cases m1 <;> decide

/-- The identity at equal index, middle: forward and reversed tiles of the same letter. -/
theorem hcI_mid : ∀ a b x : Letter, ∀ u ∈ tileShape (hTt a x), ∀ v ∈ tileShape (hTt b x),
    v - u = offH x false →
      zTileOdo (hTt a x) u = zTileOdo (hTt b x) v + ptDot (alphaH x) v + cstH x := by
  intro a b x; cases a <;> cases b <;> cases x <;> decide

/-- The identity at equal index, first tile (forward `q` after `p`, reversed `p`). -/
theorem hcI_first : ∀ u ∈ tileShape (hTt Letter.p Letter.q), ∀ v ∈ tileShape (hTt Letter.p Letter.p),
    v - u = ((-1 : ℤ), (2 : ℤ)) →
      zTileOdo (hTt Letter.p Letter.q) u = zTileOdo (hTt Letter.p Letter.p) v + ptDot (alphaH Letter.p) v + cstH Letter.p := by
  decide

/-- The identity at equal index, last tile (forward `p`, reversed `q`). -/
theorem hcI_last : ∀ a b : Letter, ∀ u ∈ tileShape (hTt a Letter.p), ∀ v ∈ tileShape (hTt b Letter.q),
    v - u = offH Letter.p true →
      zTileOdo (hTt a Letter.p) u = zTileOdo (hTt b Letter.q) v + ptDot (alphaH Letter.q) v + cstH Letter.q := by
  intro a b; cases a <;> cases b <;> decide

/-- The identity at `j = k-1`, middle: the reversed tile `k-1` with letter `m`, and `ℓ'_k = x`. -/
theorem hcK_mid : ∀ a b x m : Letter, ∀ u ∈ tileShape (hTt a x), ∀ v ∈ tileShape (hTt b m),
    v - u = offH x false + zeroOneHorizontalReversedStep m x →
      zTileOdo (hTt a x) u = zTileOdo (hTt b m) v + ptDot (alphaH m) v + cstH m := by
  intro a b x m; cases a <;> cases b <;> cases x <;> cases m <;> decide

/-- The identity at `j = k-1` for `k = 1`: the forward tile `1` (previous `q`) and the reversed tile `0` (`p`). -/
theorem hcK_first : ∀ x : Letter, ∀ u ∈ tileShape (hTt Letter.q x), ∀ v ∈ tileShape (hTt Letter.p Letter.p),
    v - u = offH x false + zeroOneHorizontalReversedStep Letter.p x →
      zTileOdo (hTt Letter.q x) u = zTileOdo (hTt Letter.p Letter.p) v + ptDot (alphaH Letter.p) v + cstH Letter.p := by
  intro x; cases x <;> decide

/-- The identity at `j = k-1` for `k = n-1`: the last forward tile `p` and the reversed tile `n-2`. -/
theorem hcK_last : ∀ a b m : Letter, ∀ u ∈ tileShape (hTt a Letter.p), ∀ v ∈ tileShape (hTt b m),
    v - u = offH Letter.p true + zeroOneHorizontalReversedStep m Letter.q →
      zTileOdo (hTt a Letter.p) u = zTileOdo (hTt b m) v + ptDot (alphaH m) v + cstH m := by
  intro a b m; cases a <;> cases b <;> cases m <;> decide

/-! ## Letters at the ends and the tile types -/

theorem hL0 (w : BinaryWord) (hf : w.head? = some .q) : lettersOf w false 0 = Letter.q := by
  rw [lettersFalse_eq]
  exact getD_zero_of_head? hf

theorem hLlast (w : BinaryWord) (hl : w.getLast? = some .p) : lettersOf w false (w.length - 1) = Letter.p := by
  rw [lettersFalse_eq]
  exact getD_last_of_getLast? hl

theorem hR0 (w : BinaryWord) (hn : 0 < w.length) (hl : w.getLast? = some .p) :
    lettersOf w true 0 = Letter.p := by
  rw [lettersTrue_eq w 0 hn]
  simpa using getD_last_of_getLast? hl

theorem hRlast (w : BinaryWord) (hn : 0 < w.length) (hf : w.head? = some .q) :
    lettersOf w true (w.length - 1) = Letter.q := by
  rw [lettersTrue_eq w (w.length - 1) (by omega)]
  have h0 : w.length - 1 - (w.length - 1) = 0 := by omega
  rw [h0]
  exact getD_zero_of_head? hf

theorem hTileAt_succ (ℓ : ℕ → Letter) (k : ℕ) : hTileAt ℓ (k + 1) = hTt (ℓ k) (ℓ (k + 1)) := by
  unfold hTileAt
  rw [hPrev_succ]

theorem hTileAt_pos (ℓ : ℕ → Letter) (k : ℕ) (hk : k ≠ 0) : hTileAt ℓ k = hTt (ℓ (k - 1)) (ℓ k) := by
  unfold hTileAt hPrev
  rw [if_neg hk]

theorem hTileAt_zero (ℓ : ℕ → Letter) : hTileAt ℓ 0 = hTt Letter.p (ℓ 0) := by
  unfold hTileAt hPrev
  simp

theorem HPE_odo (w : BinaryWord) (k : ℕ) (hk : k < w.length) (x : GInt) :
    (HPE w).odo k x = zTileOdo (hTileAt (lettersOf w false) k) (x - posF .horizontal false (lettersOf w false) k) := by
  unfold PTFamily.odo
  rw [HPE_tile w k hk]
  simp [HPE]

theorem HME_odo_rel' (w : BinaryWord) (j : ℕ) (hj : j < w.length) (x : GInt) :
    (HME w).odo j x = zTileOdo (hTileAt (lettersOf w true) j) (x - posMH w j)
      + ptDot (alphaH (lettersOf w true j)) (x - posMH w j) + cstH (lettersOf w true j) := by
  unfold PTFamily.odo
  rw [HME_tile w j hj]
  simp only [HME, ptDot, Prod.fst_sub, Prod.snd_sub]
  ring

theorem posMH_succ' (w : BinaryWord) (j : ℕ) :
    posMH w (j + 1) = posMH w j + zeroOneHorizontalReversedStep (lettersOf w true j) (lettersOf w true (j + 1)) :=
  posMH_succ w j

theorem posF_fwd_step (ℓ : ℕ → Letter) (k : ℕ) :
    posF .horizontal false ℓ (k + 1) = posF .horizontal false ℓ k + zeroOneHorizontalStep (ℓ (k + 1)) := rfl

/-- The offset of the forward tile `k` against the reversed tile `k` is the fixed offset `offH` (`k ≥ 1`) or `(-1,2)` (`k = 0`). -/
theorem hdiff_of_pos (w : BinaryWord) (hw : IsAlmostPalindrome w) (hf : w.head? = some .q)
    (hl : w.getLast? = some .p) (k : ℕ) (hk : k < w.length) (hk0 : 0 < k) :
    posF .horizontal false (lettersOf w false) k - posMH w k
      = offH (lettersOf w false k) (decide (k + 1 = w.length)) :=
  fixed_off w hw hf hl k hk hk0

/-- The `x`-coordinate of the offset of the forward tile `k` against the reversed tile `k`. -/
theorem hx_bounds (w : BinaryWord) (hw : IsAlmostPalindrome w) (hf : w.head? = some .q)
    (hl : w.getLast? = some .p) (k : ℕ) (hk : k < w.length) :
    -2 ≤ (posF .horizontal false (lettersOf w false) k - posMH w k).1 ∧
      (posF .horizontal false (lettersOf w false) k - posMH w k).1 ≤ -1 :=
  off_x_bounds w hw hf hl k hk

/-- Locality of the cross overlaps of the enlarged horizontal families: the forward tile `k` and the reversed tile `j` meet only
if `j = k` or `j + 1 = k`. -/
theorem horiz_cross_local (w : BinaryWord) (hw : IsAlmostPalindrome w) (hf : w.head? = some .q)
    (hl : w.getLast? = some .p) (k j : ℕ) (hk : k < w.length) (hj : j < w.length)
    (x : GInt) (hxP : x ∈ (HPE w).dom k) (hxM : x ∈ (HME w).dom j) : j = k ∨ j + 1 = k := by
  rw [HPE_mem w k hk] at hxP
  rw [HME_mem w j hj] at hxM
  obtain ⟨u, hu, hux⟩ := hxP
  obtain ⟨v, hv, hvx⟩ := hxM
  have hd : v - u = posF .horizontal false (lettersOf w false) k - posMH w j := by
    have h := hux.trans hvx.symm
    calc v - u = (v + posMH w j) - posMH w j - u := by abel
      _ = (u + posF .horizontal false (lettersOf w false) k) - posMH w j - u := by rw [← h]
      _ = _ := by abel
  have hxk := hx_bounds w hw hf hl k hk
  have hu1 := hTt_xbounds _ _ u hu
  have hv1 := hTt_xbounds _ _ v hv
  by_cases hA : j = k
  · exact Or.inl hA
  by_cases hB : j + 1 = k
  · exact Or.inr hB
  exfalso
  rcases Nat.lt_or_gt_of_ne hA with hlt | hgt
  · -- j < k, k ≥ j + 2
    obtain ⟨d, rfl⟩ : ∃ d, k = j + d := ⟨k - j, by omega⟩
    rcases (show d ≤ 4 ∨ 5 ≤ d by omega) with hd4 | hd5
    · rcases (show d = 2 ∨ d = 3 ∨ d = 4 by omega) with rfl | rfl | rfl
      · have hg := hdiff_of_pos w hw hf hl (j + 2) hk (by omega)
        have hs : posMH w (j + 2) = posMH w j + zeroOneHorizontalReversedStep (lettersOf w true j) (lettersOf w true (j + 1))
            + zeroOneHorizontalReversedStep (lettersOf w true (j + 1)) (lettersOf w true (j + 2)) := by
          rw [posMH_succ', posMH_succ']
        have hdiff : v - u = offH (lettersOf w false (j + 2)) (decide (j + 2 + 1 = w.length))
            + (zeroOneHorizontalReversedStep (lettersOf w true j) (lettersOf w true (j + 1))
              + zeroOneHorizontalReversedStep (lettersOf w true (j + 1)) (lettersOf w true (j + 2))) := by
          rw [hd, ← hg, hs]
          abel
        exact hcL2 _ _ _ _ _ _ _ u hu v hv hdiff
      · have hg := hdiff_of_pos w hw hf hl (j + 3) hk (by omega)
        have hs : posMH w (j + 3) = posMH w j + zeroOneHorizontalReversedStep (lettersOf w true j) (lettersOf w true (j + 1))
            + zeroOneHorizontalReversedStep (lettersOf w true (j + 1)) (lettersOf w true (j + 2))
            + zeroOneHorizontalReversedStep (lettersOf w true (j + 2)) (lettersOf w true (j + 3)) := by
          rw [posMH_succ', posMH_succ', posMH_succ']
        have hdiff : v - u = offH (lettersOf w false (j + 3)) (decide (j + 3 + 1 = w.length))
            + (zeroOneHorizontalReversedStep (lettersOf w true j) (lettersOf w true (j + 1))
              + zeroOneHorizontalReversedStep (lettersOf w true (j + 1)) (lettersOf w true (j + 2))
              + zeroOneHorizontalReversedStep (lettersOf w true (j + 2)) (lettersOf w true (j + 3))) := by
          rw [hd, ← hg, hs]
          abel
        exact hcL3 _ _ _ _ _ _ _ _ u hu v hv hdiff
      · have hg := hdiff_of_pos w hw hf hl (j + 4) hk (by omega)
        have hs : posMH w (j + 4) = posMH w j + zeroOneHorizontalReversedStep (lettersOf w true j) (lettersOf w true (j + 1))
            + zeroOneHorizontalReversedStep (lettersOf w true (j + 1)) (lettersOf w true (j + 2))
            + zeroOneHorizontalReversedStep (lettersOf w true (j + 2)) (lettersOf w true (j + 3))
            + zeroOneHorizontalReversedStep (lettersOf w true (j + 3)) (lettersOf w true (j + 4)) := by
          rw [posMH_succ', posMH_succ', posMH_succ', posMH_succ']
        have hdiff : v - u = offH (lettersOf w false (j + 4)) (decide (j + 4 + 1 = w.length))
            + (zeroOneHorizontalReversedStep (lettersOf w true j) (lettersOf w true (j + 1))
              + zeroOneHorizontalReversedStep (lettersOf w true (j + 1)) (lettersOf w true (j + 2))
              + zeroOneHorizontalReversedStep (lettersOf w true (j + 2)) (lettersOf w true (j + 3))
              + zeroOneHorizontalReversedStep (lettersOf w true (j + 3)) (lettersOf w true (j + 4))) := by
          rw [hd, ← hg, hs]
          abel
        exact hcL4 _ _ _ _ _ _ _ _ _ u hu v hv hdiff
    · -- distance at least five: the x-coordinates separate
      have hmono := posRev_x_ge (lettersOf w true) j (j + d - j)
      rw [show j + (j + d - j) = j + d by omega] at hmono
      have e := congrArg Prod.fst hd
      simp only [Prod.fst_sub, posMH, horizontalStackShift] at e hxk
      have hm : ((j + d - j : ℕ) : ℤ) ≥ 5 := by omega
      omega
  · -- j > k
    by_cases hjk : j = k + 1
    · -- the reversed tile k+1 meets the forward tile k: only the first index and the middle with `ℓ'_k = ℓ_k`
      subst hjk
      by_cases hk0 : k = 0
      · subst hk0
        have hfix := fixed_hstack w
        have hTu : u ∈ tileShape (hTt Letter.p (lettersOf w false 0)) := by
          rw [hTileAt_zero] at hu
          exact hu
        rw [hL0 w hf] at hTu
        have hTv : v ∈ tileShape (hTt Letter.p (lettersOf w true 1)) := by
          rw [hTileAt_succ] at hv
          rw [hR0 w (by omega) hl] at hv
          exact hv
        have hM1 : posMH w 1 = posMH w 0 + zeroOneHorizontalReversedStep (lettersOf w true 0) (lettersOf w true 1) :=
          posMH_succ' w 0
        have hdiff : v - u = ((-1 : ℤ), (2 : ℤ)) - zeroOneHorizontalReversedStep Letter.p (lettersOf w true 1) := by
          rw [hd, hM1, hR0 w (by omega) hl]
          have hg : posF .horizontal false (lettersOf w false) 0 - posMH w 0 = ((-1 : ℤ), (2 : ℤ)) := hfix
          rw [← hg]
          abel
        exact hcL1k0 _ u hTu v hTv hdiff
      · have hmid := vt_mid_letters w hw k (by omega) (by omega)
        have hg := hdiff_of_pos w hw hf hl k hk (by omega)
        have hdk : decide (k + 1 = w.length) = false := decide_eq_false (by omega)
        rw [hdk] at hg
        have hPu : u ∈ tileShape (hTt (lettersOf w false (k - 1)) (lettersOf w false k)) := by
          rw [hTileAt_pos _ k hk0] at hu
          exact hu
        have hPv : v ∈ tileShape (hTt (lettersOf w true k) (lettersOf w true (k + 1))) := by
          rw [hTileAt_succ] at hv
          exact hv
        rw [hmid] at hPv
        have hdiff : v - u = offH (lettersOf w false k) false
            - zeroOneHorizontalReversedStep (lettersOf w false k) (lettersOf w true (k + 1)) := by
          rw [hd, posMH_succ' w k, ← hg, hmid]
          abel
        exact hcL1 _ _ _ u hPu v hPv hdiff
    · -- the reversed tile j ≥ k + 2: the x-coordinates separate
      obtain ⟨d, rfl⟩ : ∃ d, j = k + d := ⟨j - k, by omega⟩
      have hmono := posRev_x_ge (lettersOf w true) k d
      have e := congrArg Prod.fst hd
      simp only [Prod.fst_sub, posMH, horizontalStackShift] at e hxk
      have hm : (d : ℤ) ≥ 2 := by omega
      omega

/-- The cross identity of equal indices for the enlarged horizontal families. -/
theorem horiz_same (w : BinaryWord) (hw : IsAlmostPalindrome w) (hf : w.head? = some .q)
    (hl : w.getLast? = some .p) (hn : 2 ≤ w.length) (k : ℕ) (hk : k < w.length) (x : GInt)
    (hxP : x ∈ (HPE w).dom k) (hxM : x ∈ (HME w).dom k) : (HPE w).odo k x = (HME w).odo k x := by
  rw [HPE_mem w k hk] at hxP
  rw [HME_mem w k hk] at hxM
  obtain ⟨u, hu, hux⟩ := hxP
  obtain ⟨v, hv, hvx⟩ := hxM
  have hd : v - u = posF .horizontal false (lettersOf w false) k - posMH w k := by
    have h := hux.trans hvx.symm
    calc v - u = (v + posMH w k) - posMH w k - u := by abel
      _ = (u + posF .horizontal false (lettersOf w false) k) - posMH w k - u := by rw [← h]
      _ = _ := by abel
  have ex : x - posF .horizontal false (lettersOf w false) k = u := by rw [← hux]; abel
  have ey : x - posMH w k = v := by rw [← hvx]; abel
  rw [HPE_odo w k hk x, HME_odo_rel' w k hk x, ex, ey]
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · -- the first tile: `q` against `p`
    have hfix := fixed_hstack w
    have hg : posF .horizontal false (lettersOf w false) 0 - posMH w 0 = ((-1 : ℤ), (2 : ℤ)) := hfix
    have hdiff : v - u = ((-1 : ℤ), (2 : ℤ)) := by rw [hd, hg]
    have hu' : u ∈ tileShape (hTt Letter.p Letter.q) := by
      rw [hTileAt_zero, hL0 w hf] at hu
      exact hu
    have hv' : v ∈ tileShape (hTt Letter.p Letter.p) := by
      rw [hTileAt_zero, hR0 w (by omega) hl] at hv
      exact hv
    rw [hTileAt_zero, hL0 w hf, hTileAt_zero, hR0 w (by omega) hl]
    exact hcI_first u hu' v hv' hdiff
  · by_cases hkn : k + 1 = w.length
    · -- the last tile: `p` against `q`
      have hg := hdiff_of_pos w hw hf hl k hk hk0
      have hdk : decide (k + 1 = w.length) = true := decide_eq_true hkn
      rw [hdk] at hg
      have hLk : lettersOf w false k = Letter.p := by
        rw [show k = w.length - 1 by omega]
        exact hLlast w hl
      have hRk : lettersOf w true k = Letter.q := by
        rw [show k = w.length - 1 by omega]
        exact hRlast w (by omega) hf
      have hdiff : v - u = offH Letter.p true := by
        rw [hd, ← hLk, hg, hLk]
      have eF := hTileAt_pos (lettersOf w false) k (by omega)
      have eR := hTileAt_pos (lettersOf w true) k (by omega)
      have hu'' : u ∈ tileShape (hTt (lettersOf w false (k - 1)) (lettersOf w false k)) := by
        rw [← eF]
        exact hu
      have hv'' : v ∈ tileShape (hTt (lettersOf w true (k - 1)) (lettersOf w true k)) := by
        rw [← eR]
        exact hv
      rw [hLk] at hu''
      rw [hRk] at hv''
      rw [eF, eR, hLk, hRk]
      exact hcI_last _ _ u hu'' v hv'' hdiff
    · -- a middle tile: the letters agree
      have hmid := vt_mid_letters w hw k hk0 (by omega)
      have hg := hdiff_of_pos w hw hf hl k hk hk0
      have hdk : decide (k + 1 = w.length) = false := decide_eq_false hkn
      rw [hdk] at hg
      have hdiff : v - u = offH (lettersOf w false k) false := by
        rw [hd, hg]
      have eF := hTileAt_pos (lettersOf w false) k (by omega)
      have eR := hTileAt_pos (lettersOf w true) k (by omega)
      have hu' : u ∈ tileShape (hTt (lettersOf w false (k - 1)) (lettersOf w false k)) := by
        rw [← eF]
        exact hu
      have hv' : v ∈ tileShape (hTt (lettersOf w true (k - 1)) (lettersOf w false k)) := by
        rw [← hmid, ← eR]
        exact hv
      rw [eF, eR, hmid]
      exact hcI_mid _ _ _ u hu' v hv' hdiff

/-- The cross identity of the forward tile `j+1` with the reversed tile `j`. -/
theorem horiz_pred (w : BinaryWord) (hw : IsAlmostPalindrome w) (hf : w.head? = some .q)
    (hl : w.getLast? = some .p) (hn : 2 ≤ w.length) (j : ℕ) (hj : j + 1 < w.length) (x : GInt)
    (hxP : x ∈ (HPE w).dom (j + 1)) (hxM : x ∈ (HME w).dom j) :
    (HPE w).odo (j + 1) x = (HME w).odo j x := by
  rw [HPE_mem w (j + 1) hj] at hxP
  rw [HME_mem w j (by omega)] at hxM
  obtain ⟨u, hu, hux⟩ := hxP
  obtain ⟨v, hv, hvx⟩ := hxM
  have hd : v - u = posF .horizontal false (lettersOf w false) (j + 1) - posMH w j := by
    have h := hux.trans hvx.symm
    calc v - u = (v + posMH w j) - posMH w j - u := by abel
      _ = (u + posF .horizontal false (lettersOf w false) (j + 1)) - posMH w j - u := by rw [← h]
      _ = _ := by abel
  have ex : x - posF .horizontal false (lettersOf w false) (j + 1) = u := by rw [← hux]; abel
  have ey : x - posMH w j = v := by rw [← hvx]; abel
  rw [HPE_odo w (j + 1) hj x, HME_odo_rel' w j (by omega) x, ex, ey]
  have hg := hdiff_of_pos w hw hf hl (j + 1) hj (by omega)
  have hM := posMH_succ' w j
  have hd2 : v - u = offH (lettersOf w false (j + 1)) (decide (j + 1 + 1 = w.length))
      + zeroOneHorizontalReversedStep (lettersOf w true j) (lettersOf w true (j + 1)) := by
    rw [hd, ← hg, hM]
    abel
  have hsucc : hTileAt (lettersOf w false) (j + 1) = hTt (lettersOf w false j) (lettersOf w false (j + 1)) :=
    hTileAt_succ (lettersOf w false) j
  rw [hsucc]
  by_cases hkn : j + 1 + 1 = w.length
  · -- the last forward tile
    have hdk : decide (j + 1 + 1 = w.length) = true := decide_eq_true hkn
    rw [hdk] at hd2
    have hLk : lettersOf w false (j + 1) = Letter.p := by
      rw [show j + 1 = w.length - 1 by omega]
      exact hLlast w hl
    have hRk : lettersOf w true (j + 1) = Letter.q := by
      rw [show j + 1 = w.length - 1 by omega]
      exact hRlast w (by omega) hf
    have hdiff : v - u = offH Letter.p true + zeroOneHorizontalReversedStep (lettersOf w true j) Letter.q := by
      rw [hd2, hLk, hRk]
    have hu' : u ∈ tileShape (hTt (lettersOf w false j) Letter.p) := by
      have h := hu
      rw [hsucc, hLk] at h
      exact h
    have hv' : v ∈ tileShape (hTt (hPrev (lettersOf w true) j) (lettersOf w true j)) := by
      have h := hv
      unfold hTileAt at h
      exact h
    rw [hLk]
    exact hcK_last _ _ _ u hu' v hv' hdiff
  · by_cases hk1 : j = 0
    · -- the first forward tile against the first reversed tile
      obtain rfl := hk1
      have hmid : lettersOf w true (0 + 1) = lettersOf w false (0 + 1) :=
        vt_mid_letters w hw (0 + 1) (by norm_num) (by omega)
      have hdk : decide (0 + 1 + 1 = w.length) = false := decide_eq_false (by omega)
      rw [hdk, hmid, hR0 w (by omega) hl] at hd2
      have hu' : u ∈ tileShape (hTt Letter.q (lettersOf w false (0 + 1))) := by
        have h := hu
        rw [hsucc, hL0 w hf] at h
        exact h
      have hv' : v ∈ tileShape (hTt Letter.p Letter.p) := by
        have h := hv
        rw [hTileAt_zero, hR0 w (by omega) hl] at h
        exact h
      rw [hL0 w hf, hTileAt_zero, hR0 w (by omega) hl]
      exact hcK_first _ u hu' v hv' hd2
    · -- a middle forward tile: the letters agree at `j+1`
      have hmid := vt_mid_letters w hw (j + 1) (by omega) (by omega)
      have hdk : decide (j + 1 + 1 = w.length) = false := decide_eq_false hkn
      rw [hdk, hmid] at hd2
      have eM := hTileAt_pos (lettersOf w true) j hk1
      have hu' : u ∈ tileShape (hTt (lettersOf w false j) (lettersOf w false (j + 1))) := by
        have h := hu
        rw [hsucc] at h
        exact h
      have hv' : v ∈ tileShape (hTt (lettersOf w true (j - 1)) (lettersOf w true j)) := by
        have h := hv
        rw [eM] at h
        exact h
      rw [eM]
      exact hcK_mid _ _ _ _ u hu' v hv' hd2

/-- The cross overlaps of the enlarged horizontal families agree. -/
theorem horiz_cross_common (w : BinaryWord) (hw : IsAlmostPalindrome w) (hf : w.head? = some .q)
    (hl : w.getLast? = some .p) (hn : 2 ≤ w.length) : CrossCommon (HPE w) (HME w) := by
  intro k hk j hj x hxP hxM
  have hk' : k < w.length := by simpa only [HPE_n] using hk
  have hj' : j < w.length := by simpa only [HME_n] using hj
  rcases horiz_cross_local w hw hf hl k j hk' hj' x hxP hxM with rfl | h
  · exact horiz_same w hw hf hl hn _ hk' x hxP hxM
  · obtain rfl : k = j + 1 := h.symm
    exact horiz_pred w hw hf hl hn j hk' x hxP hxM

/-- The horizontal half of the Moreover of `lemma:stacked_zero_one_string`, with the enlarged tiles, for every word. -/
theorem horizontalMoreover_proof (w : BinaryWord) : HorizontalMoreover w := by
  unfold HorizontalMoreover
  intro hw hf hl
  have hn : 2 ≤ w.length := by
    rcases w with _ | ⟨a, _ | ⟨b, t⟩⟩
    · simp at hf
    · simp_all
    · simp
  refine ⟨HPE w, HME w, rfl, rfl, HPE_respects w, HME_respects w, HPE_within w, HME_within w,
    horiz_cross_common w hw hf hl hn, ?_⟩
  show (0 : GInt) - alphaH (lettersOf w true 0) = ((0 : ℤ), (-1 : ℤ))
  rw [hR0 w (by omega) hl]
  rfl

end FLatticePaper.Tiles
