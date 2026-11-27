import FLatticePaper.Tiles.VerticalCrossLocal

/-! # The cross identities of the vertical Moreover

For a tile `k` of the forward family and `j` of the reversed family with a common point `x = u + P_k = v + M_j`, the odometers
are `zTileOdo (ℓ_k) u + (cnt_k, -k) · u + vtCP_k` and `zTileOdo (ℓ'_j) v + (cnt'_j, -j) · v + vtCP_j - vtDelta_j`. The equal-index
pairs are handled here; the offsets are the fixed offsets `vtG` (middle), `(-1,-1)` (first) and `(-1,0)` (last). -/

namespace FLatticePaper.Tiles

theorem vtP_odo (w : BinaryWord) (k : ℕ) (hk : k < w.length) (x : GInt) :
    (vtP w).odo k x = zTileOdo (letterZTile (lettersOf w false k))
        (x - posF .vertical false (lettersOf w false) k)
      + ptDot (vtAff (lettersOf w false) k) (x - posF .vertical false (lettersOf w false) k)
      + vtCP (lettersOf w false) k := by
  unfold PTFamily.odo
  rw [vtP_tile w k hk]
  simp only [vtP, ptDot, Prod.fst_sub, Prod.snd_sub]
  ring

theorem vtM_odo (w : BinaryWord) (j : ℕ) (hj : j < w.length) (x : GInt) :
    (vtM w).odo j x = zTileOdo (letterZTile (lettersOf w true j))
        (x - (posF .vertical true (lettersOf w true) j - verticalStackShift))
      + ptDot (vtAff (lettersOf w true) j) (x - (posF .vertical true (lettersOf w true) j - verticalStackShift))
      + vtCM (lettersOf w true) j := by
  unfold PTFamily.odo
  rw [vtM_tile w j hj]
  simp only [vtM, ptDot, Prod.fst_sub, Prod.snd_sub]
  ring

theorem vt_fixed_last (w : BinaryWord) (hw : IsAlmostPalindrome w) (hf : w.head? = some .p)
    (hl : w.getLast? = some .q) (_hn : 2 ≤ w.length) :
    posF .vertical false (lettersOf w false) (w.length - 1)
      - (posF .vertical true (lettersOf w true) (w.length - 1) - verticalStackShift) = ((-1 : ℤ), (0 : ℤ)) := by
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
  obtain ⟨_, _, hC⟩ := zeroOne_fixed_offsets_vertical w hw hf hl
    (fun i => posF .vertical false (lettersOf w false) i)
    (fun i => posF .vertical true (lettersOf w true) i - verticalStackShift) hplus hminus hstack
  exact hC

/-- The equal-index overlap of the first tiles: `p` against `q` with offset `(-1,-1)`. -/
theorem vtAuxA0 : ∀ u ∈ tileShape (letterZTile Letter.p), ∀ v ∈ tileShape (letterZTile Letter.q),
    v = u + ((-1 : ℤ), (-1 : ℤ)) → zTileOdo (letterZTile Letter.p) u = zTileOdo (letterZTile Letter.q) v := by
  decide

/-- The equal-index overlap of a middle `q` tile: the odometers differ by `u.1 - 1`. -/
theorem vtAuxQ : ∀ u ∈ tileShape (letterZTile Letter.q), ∀ v ∈ tileShape (letterZTile Letter.q),
    v = u + ((-1 : ℤ), (-1 : ℤ)) → zTileOdo (letterZTile Letter.q) u = zTileOdo (letterZTile Letter.q) v + (u.1 - 1) := by
  decide

/-- The equal-index overlap of the last tile: `q` against `p` with offset `(-1,0)`. -/
theorem vtAuxLast : ∀ u ∈ tileShape (letterZTile Letter.q), ∀ v ∈ tileShape (letterZTile Letter.p),
    v = u + ((-1 : ℤ), (0 : ℤ)) → zTileOdo (letterZTile Letter.q) u = zTileOdo (letterZTile Letter.p) v + (u.1 - 1) := by
  decide

/-- The cross identity of equal indices. -/
theorem vt_cross_same (w : BinaryWord) (hw : IsAlmostPalindrome w) (hf : w.head? = some .p)
    (hl : w.getLast? = some .q) (hn : 2 ≤ w.length) (k : ℕ) (hk : k < w.length) (x : GInt)
    (hxP : x ∈ (vtP w).dom k) (hxM : x ∈ (vtM w).dom k) : (vtP w).odo k x = (vtM w).odo k x := by
  rw [vtP_mem w k hk] at hxP
  rw [vtM_mem w k hk] at hxM
  obtain ⟨u, hu, hux⟩ := hxP
  obtain ⟨v, hv, hvx⟩ := hxM
  have hd : v - u = posF .vertical false (lettersOf w false) k
      - (posF .vertical true (lettersOf w true) k - verticalStackShift) := by
    have h := hux.trans hvx.symm
    calc v - u = (v + (posF .vertical true (lettersOf w true) k - verticalStackShift))
          - (posF .vertical true (lettersOf w true) k - verticalStackShift) - u := by abel
      _ = (u + posF .vertical false (lettersOf w false) k) - (posF .vertical true (lettersOf w true) k
          - verticalStackShift) - u := by rw [← h]
      _ = _ := by abel
  rw [vtP_odo w k hk x, vtM_odo w k hk x, vtCM_eq w hw hf hl hn k hk]
  have ex : x - posF .vertical false (lettersOf w false) k = u := by rw [← hux]; abel
  have ey : x - (posF .vertical true (lettersOf w true) k - verticalStackShift) = v := by rw [← hvx]; abel
  rw [ex, ey]
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · -- the first tiles: `p` of the forward family and `q` of the reversed one
    have hfix := vt_fixed_le w hw hf hl hn 0 (by omega)
    rw [vt_rev_zero w (by omega) hl] at hfix
    have hG : vtG Letter.q = ((-1 : ℤ), (-1 : ℤ)) := by decide
    have hvu : v - u = ((-1 : ℤ), (-1 : ℤ)) := by rw [hd, hfix, hG]
    have hv' : v = u + ((-1 : ℤ), (-1 : ℤ)) := by rw [← hvu]; abel
    rw [vt_fwd_zero w hf] at hu ⊢
    rw [vt_rev_zero w (by omega) hl] at hv ⊢
    have := vtAuxA0 u hu v hv hv'
    simp only [vtAff, vtCnt, ptDot, vtDelta_zero, vtCP, Nat.cast_zero, neg_zero, zero_mul,
      add_zero, sub_zero]
    linarith [this]
  · by_cases hkn : k + 1 = w.length
    · -- the last tiles: `q` of the forward family and `p` of the reversed one
      have eF : lettersOf w false k = .q := by
        rw [show k = w.length - 1 by omega]
        exact vt_fwd_last w hl
      have eR : lettersOf w true k = .p := by
        rw [show k = w.length - 1 by omega]
        exact vt_rev_last w (by omega) hf
      have hfix := vt_fixed_last w hw hf hl hn
      rw [show w.length - 1 = k by omega] at hfix
      have hvu : v - u = ((-1 : ℤ), (0 : ℤ)) := by rw [hd, hfix]
      have hv' : v = u + ((-1 : ℤ), (0 : ℤ)) := by rw [← hvu]; abel
      rw [eF] at hu
      rw [eR] at hv
      have hcnt := vt_cnt_rev w hw hf hl hn k hk0 hk
      have hdl := vtDelta_last w k hk0 hkn
      have := vtAuxLast u hu v hv hv'
      rw [hdl]
      simp only [vtAff, ptDot]
      rw [hcnt, eF, eR]
      subst hv'
      simp only [Prod.fst_add, Prod.snd_add]
      linarith [this]
    · -- the middle tiles: the letters of the two families agree
      have hmid := vt_mid_letters w hw k hk0 (by omega)
      have hfix := vt_fixed_le w hw hf hl hn k (by omega)
      rw [hmid] at hfix
      have hcnt := vt_cnt_rev w hw hf hl hn k hk0 hk
      have hdm := vtDelta_mid w k hk0 (by omega)
      have hvu : v - u = vtG (lettersOf w false k) := hd.trans hfix
      by_cases hqk : lettersOf w false k = .q
      · have hG : vtG (lettersOf w false k) = ((-1 : ℤ), (-1 : ℤ)) := by rw [hqk]; decide
        rw [hG] at hvu
        have hv' : v = u + ((-1 : ℤ), (-1 : ℤ)) := by rw [← hvu]; abel
        rw [hqk] at hu
        rw [hmid, hqk] at hv
        have := vtAuxQ u hu v hv hv'
        simp only [vtAff, ptDot]
        rw [hcnt, hmid, hdm, hqk]
        simp only [vtDeltaF, ↓reduceIte]
        subst hv'
        simp only [Prod.fst_add, Prod.snd_add]
        linarith [this]
      · have hp : lettersOf w false k = .p := by
          revert hqk
          cases lettersOf w false k <;> simp
        have hG : vtG (lettersOf w false k) = ((-2 : ℤ), (-1 : ℤ)) := by rw [hp]; decide
        rw [hG] at hvu
        exfalso
        have hb1 := tileShape_x_bounds (lettersOf w false k) u hu
        have hb2 := tileShape_x_bounds (lettersOf w true k) v hv
        have h1 := congrArg Prod.fst hvu
        simp only [Prod.fst_sub] at h1
        omega

theorem vtCP_succ (ℓ : ℕ → Letter) (k : ℕ) : vtCP ℓ (k + 1)
    = vtCP ℓ k + vtBetaP (ℓ k) (ℓ (k + 1)) + ptDot (vtAff ℓ k) (zeroOneVerticalStep (ℓ (k + 1))) := rfl

/-- The only common points of the forward tile `k` and the reversed tile `k+1` (the offset is `vtG m0 - R m0 m1`). -/
theorem vtOvB : ∀ a m0 m1 : Letter, ∀ u ∈ tileShape (letterZTile a), ∀ v ∈ tileShape (letterZTile m1),
    v - u = vtG m0 - zeroOneVerticalReversedStep m0 m1 →
      a = Letter.p ∧ m1 = Letter.p ∧ u = ((1 : ℤ), (2 : ℤ)) ∧ v = ((0 : ℤ), (0 : ℤ)) := by
  intro a m0 m1; cases a <;> cases m0 <;> cases m1 <;> decide

/-- The cross identity of the forward tile `k` with the reversed tile `k+1`. -/
theorem vt_cross_succ (w : BinaryWord) (hw : IsAlmostPalindrome w) (hf : w.head? = some .p)
    (hl : w.getLast? = some .q) (hn : 2 ≤ w.length) (k : ℕ) (hk : k + 1 < w.length) (x : GInt)
    (hxP : x ∈ (vtP w).dom k) (hxM : x ∈ (vtM w).dom (k + 1)) :
    (vtP w).odo k x = (vtM w).odo (k + 1) x := by
  have hk0 : k < w.length := by omega
  rw [vtP_mem w k hk0] at hxP
  rw [vtM_mem w (k + 1) hk] at hxM
  obtain ⟨u, hu, hux⟩ := hxP
  obtain ⟨v, hv, hvx⟩ := hxM
  have hd : v - u = posF .vertical false (lettersOf w false) k
      - (posF .vertical true (lettersOf w true) (k + 1) - verticalStackShift) := by
    have h' : v + (posF .vertical true (lettersOf w true) (k + 1) - verticalStackShift)
        = u + posF .vertical false (lettersOf w false) k := hvx.trans hux.symm
    calc v - u = (v + (posF .vertical true (lettersOf w true) (k + 1) - verticalStackShift))
          - (posF .vertical true (lettersOf w true) (k + 1) - verticalStackShift) - u := by abel
      _ = (u + posF .vertical false (lettersOf w false) k) - (posF .vertical true (lettersOf w true) (k + 1)
          - verticalStackShift) - u := by rw [h']
      _ = _ := by abel
  have e : posF .vertical true (lettersOf w true) (k + 1) - verticalStackShift
      = (posF .vertical true (lettersOf w true) k - verticalStackShift)
        + zeroOneVerticalReversedStep (lettersOf w true k) (lettersOf w true (k + 1)) := by
    have e1 : posF .vertical true (lettersOf w true) (k + 1)
        = posF .vertical true (lettersOf w true) k
          + zeroOneVerticalReversedStep (lettersOf w true k) (lettersOf w true (k + 1)) := rfl
    rw [e1]
    abel
  have hfix := vt_fixed_le w hw hf hl hn k (by omega)
  have hd2 : v - u = vtG (lettersOf w true k)
      - zeroOneVerticalReversedStep (lettersOf w true k) (lettersOf w true (k + 1)) := by
    rw [hd, e, ← hfix]
    abel
  rw [vtP_odo w k hk0 x, vtM_odo w (k + 1) hk x, vtCM_eq w hw hf hl hn (k + 1) hk]
  have ex : x - posF .vertical false (lettersOf w false) k = u := by rw [← hux]; abel
  have ey : x - (posF .vertical true (lettersOf w true) (k + 1) - verticalStackShift) = v := by
    rw [← hvx]; abel
  rw [ex, ey]
  obtain ⟨ha, hm1, rfl, rfl⟩ := vtOvB _ _ _ u hu v hv hd2
  rw [vtCP_succ, ha, hm1]
  have hz1 : zTileOdo (letterZTile Letter.p) ((1 : ℤ), (2 : ℤ)) = -1 := by decide
  have hz0 : zTileOdo (letterZTile Letter.p) ((0 : ℤ), (0 : ℤ)) = 0 := by decide
  rw [hz1, hz0]
  have hc : vtCnt (lettersOf w false) (k + 1) = vtCnt (lettersOf w false) k := by
    show vtCnt (lettersOf w false) k + (if lettersOf w false k = Letter.q then 1 else 0)
      = vtCnt (lettersOf w false) k
    rw [ha]
    simp
  by_cases hkn : k + 2 = w.length
  · have hY : lettersOf w false (k + 1) = .q := by
      rw [show k + 1 = w.length - 1 by omega]
      exact vt_fwd_last w hl
    rw [vtDelta_last w (k + 1) (by omega) (by omega), hY, hc]
    simp only [vtAff, ptDot, vtBetaP, zeroOneVerticalStep, mul_zero, add_zero, zero_add]
    linarith
  · have hm := vt_mid_letters w hw (k + 1) (by omega) (by omega)
    have hY : lettersOf w false (k + 1) = .p := by
      rw [← hm]
      exact hm1
    rw [vtDelta_mid w (k + 1) (by omega) (by omega), hY, hc]
    simp only [vtAff, ptDot, vtBetaP, zeroOneVerticalStep, vtDeltaF, mul_zero, add_zero, zero_add]
    push_cast
    linarith

/-- The common points of the forward tile `i+1` and the reversed tile `i`, for a middle `i+1` (`q` against `q`). -/
theorem vtOvCmid : ∀ a m1 : Letter, ∀ u ∈ tileShape (letterZTile a), ∀ v ∈ tileShape (letterZTile m1),
    v - u = vtG a + zeroOneVerticalReversedStep m1 a →
      m1 = Letter.q ∧ a = Letter.q ∧ u = ((1 : ℤ), (0 : ℤ)) ∧ v = ((0 : ℤ), (1 : ℤ)) := by
  intro a m1; cases a <;> cases m1 <;> decide

/-- The common points of the forward tile `i+1` (the last tile, letter `q`) and the reversed tile `i`. -/
theorem vtOvClast : ∀ m1 : Letter, ∀ u ∈ tileShape (letterZTile Letter.q), ∀ v ∈ tileShape (letterZTile m1),
    v - u = ((-1 : ℤ), (0 : ℤ)) + zeroOneVerticalReversedStep m1 Letter.p →
      m1 = Letter.q ∧ u = ((1 : ℤ), (0 : ℤ)) ∧ v = ((0 : ℤ), (1 : ℤ)) := by
  intro m1; cases m1 <;> decide

/-- The cross identity of the forward tile `i+1` with the reversed tile `i`. -/
theorem vt_cross_pred (w : BinaryWord) (hw : IsAlmostPalindrome w) (hf : w.head? = some .p)
    (hl : w.getLast? = some .q) (hn : 2 ≤ w.length) (i : ℕ) (hi : i + 1 < w.length) (x : GInt)
    (hxP : x ∈ (vtP w).dom (i + 1)) (hxM : x ∈ (vtM w).dom i) :
    (vtP w).odo (i + 1) x = (vtM w).odo i x := by
  rw [vtP_mem w (i + 1) hi] at hxP
  rw [vtM_mem w i (by omega)] at hxM
  obtain ⟨u, hu, hux⟩ := hxP
  obtain ⟨v, hv, hvx⟩ := hxM
  have hd : v - u = posF .vertical false (lettersOf w false) (i + 1)
      - (posF .vertical true (lettersOf w true) i - verticalStackShift) := by
    have h' : v + (posF .vertical true (lettersOf w true) i - verticalStackShift)
        = u + posF .vertical false (lettersOf w false) (i + 1) := hvx.trans hux.symm
    calc v - u = (v + (posF .vertical true (lettersOf w true) i - verticalStackShift))
          - (posF .vertical true (lettersOf w true) i - verticalStackShift) - u := by abel
      _ = (u + posF .vertical false (lettersOf w false) (i + 1)) - (posF .vertical true (lettersOf w true) i
          - verticalStackShift) - u := by rw [h']
      _ = _ := by abel
  have e : posF .vertical true (lettersOf w true) (i + 1) - verticalStackShift
      = (posF .vertical true (lettersOf w true) i - verticalStackShift)
        + zeroOneVerticalReversedStep (lettersOf w true i) (lettersOf w true (i + 1)) := by
    have e1 : posF .vertical true (lettersOf w true) (i + 1)
        = posF .vertical true (lettersOf w true) i
          + zeroOneVerticalReversedStep (lettersOf w true i) (lettersOf w true (i + 1)) := rfl
    rw [e1]
    abel
  rw [vtP_odo w (i + 1) hi x, vtM_odo w i (by omega) x, vtCM_eq w hw hf hl hn i (by omega)]
  have ex : x - posF .vertical false (lettersOf w false) (i + 1) = u := by rw [← hux]; abel
  have ey : x - (posF .vertical true (lettersOf w true) i - verticalStackShift) = v := by
    rw [← hvx]; abel
  rw [ex, ey]
  by_cases hmidc : i + 3 ≤ w.length
  · -- the tile `i+1` is a middle tile: the letters agree there
    have hm := vt_mid_letters w hw (i + 1) (by omega) (by omega)
    have hfix := vt_fixed_le w hw hf hl hn (i + 1) (by omega)
    rw [hm] at hfix e
    have hd2 : v - u = vtG (lettersOf w false (i + 1))
        + zeroOneVerticalReversedStep (lettersOf w true i) (lettersOf w false (i + 1)) := by
      rw [hd, ← hfix, e]
      abel
    obtain ⟨hm1, ha, rfl, rfl⟩ := vtOvCmid _ _ u hu v hv hd2
    rw [vtCP_succ, ha, hm1]
    have hq10 : zTileOdo (letterZTile Letter.q) ((1 : ℤ), (0 : ℤ)) = 0 := by decide
    have hq01 : zTileOdo (letterZTile Letter.q) ((0 : ℤ), (1 : ℤ)) = -1 := by decide
    rw [hq10, hq01]
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · have hfz := vt_fwd_zero w hf
      rw [hfz, vtDelta_zero]
      simp only [vtAff, ptDot, vtBetaP, zeroOneVerticalStep, vtCP, vtCnt, hfz]
      simp
    · have hmi := vt_mid_letters w hw i hi0 (by omega)
      have hli : lettersOf w false i = .q := by rw [← hmi]; exact hm1
      rw [vtDelta_mid w i hi0 (by omega), hli]
      simp only [vtAff, ptDot, vtBetaP, zeroOneVerticalStep, vtDeltaF, vtCnt, hli, if_true]
      push_cast
      linarith
  · -- the tile `i+1` is the last tile
    have hi1 : i + 1 = w.length - 1 := by omega
    have hF : lettersOf w false (i + 1) = .q := by
      rw [hi1]
      exact vt_fwd_last w hl
    have hR : lettersOf w true (i + 1) = .p := by
      rw [hi1]
      exact vt_rev_last w (by omega) hf
    have hfix := vt_fixed_last w hw hf hl hn
    rw [← hi1] at hfix
    rw [hR] at e
    have hd2 : v - u = ((-1 : ℤ), (0 : ℤ)) + zeroOneVerticalReversedStep (lettersOf w true i) Letter.p := by
      rw [hd, ← hfix, e]
      abel
    rw [hF] at hu
    obtain ⟨hm1, rfl, rfl⟩ := vtOvClast _ u hu v hv hd2
    rw [vtCP_succ, hF, hm1]
    have hq10 : zTileOdo (letterZTile Letter.q) ((1 : ℤ), (0 : ℤ)) = 0 := by decide
    have hq01 : zTileOdo (letterZTile Letter.q) ((0 : ℤ), (1 : ℤ)) = -1 := by decide
    rw [hq10, hq01]
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · have hfz := vt_fwd_zero w hf
      rw [hfz, vtDelta_zero]
      simp only [vtAff, ptDot, vtBetaP, zeroOneVerticalStep, vtCP, vtCnt, hfz]
      simp
    · have hmi := vt_mid_letters w hw i hi0 (by omega)
      have hli : lettersOf w false i = .q := by rw [← hmi]; exact hm1
      rw [vtDelta_mid w i hi0 (by omega), hli]
      simp only [vtAff, ptDot, vtBetaP, zeroOneVerticalStep, vtDeltaF, vtCnt, hli, if_true]
      push_cast
      linarith

end FLatticePaper.Tiles
