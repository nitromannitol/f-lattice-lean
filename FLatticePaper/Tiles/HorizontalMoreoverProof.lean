import FLatticePaper.Tiles.HorizontalFamily
import FLatticePaper.Tiles.ZeroOneSlopes

/-! # Assembly of the horizontal half of the Moreover (the explicit family `HP`, `HM`)

The local identities of `HorizontalFamily` are transported to the placed tiles: the relative positions of consecutive tiles,
the membership in the domains, and the exclusion of non-consecutive overlaps by the `x`-coordinates. -/

namespace FLatticePaper.Tiles

theorem zTileLetter_letterZTile (l : Letter) : zTileLetter (letterZTile l) = l := by
  cases l <;> rfl

/-- The forward positions: the next tile is one zero-one step further. -/
theorem posF_fwd_succ (ℓ : ℕ → Letter) (k : ℕ) :
    posF .horizontal false ℓ (k + 1) = posF .horizontal false ℓ k + zeroOneHorizontalStep (ℓ (k + 1)) := rfl

/-- The reversed positions: the next minus tile is one reversed step further. -/
theorem posF_rev_succ (ℓ : ℕ → Letter) (k : ℕ) :
    posF .horizontal true ℓ (k + 1) = posF .horizontal true ℓ k + rsH (ℓ k) (ℓ (k + 1)) := rfl

/-- The forward zero-one step has a positive `x`-component. -/
theorem stepF_x_pos (b : Letter) : 1 ≤ (zeroOneHorizontalStep b).1 := by
  cases b <;> decide

/-- The forward positions grow by at least one in `x` per tile. -/
theorem posF_fwd_x_ge (ℓ : ℕ → Letter) (j m : ℕ) :
    (posF .horizontal false ℓ j).1 + (m : ℤ) ≤ (posF .horizontal false ℓ (j + m)).1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show j + (m + 1) = (j + m) + 1 by omega, posF_fwd_succ]
    have := stepF_x_pos (ℓ (j + m + 1))
    simp only [Prod.fst_add]
    push_cast
    linarith

/-- The `x`-coordinates of the sites of a placed tile lie in `[0, 1]` relative to the tile position. -/
theorem tile_rel_x (x : Letter) (u : GInt) (hu : u ∈ tileShape (letterZTile x)) : 0 ≤ u.1 ∧ u.1 ≤ 1 :=
  tileShape_x_bounds x u hu

/-- The domain of the `k`-th plus tile, relative to its position. -/
theorem mem_HP_dom (w : BinaryWord) (k : ℕ) (hk : k < w.length) (x : GInt) :
    x ∈ (HP w).dom k ↔
      ∃ u ∈ tileShape (letterZTile (lettersOf w false k)),
        u + posF .horizontal false (lettersOf w false) k = x := by
  unfold PTFamily.dom
  rw [HP_tile w k hk]
  simp only [List.mem_map]

/-- The domain of the `j`-th minus tile, relative to its position. -/
theorem mem_HM_dom (w : BinaryWord) (j : ℕ) (hj : j < w.length) (x : GInt) :
    x ∈ (HM w).dom j ↔
      ∃ u ∈ tileShape (letterZTile (lettersOf w true j)), u + posMH w j = x := by
  unfold PTFamily.dom
  rw [HM_tile w j hj]
  simp only [List.mem_map]

theorem HP_n (w : BinaryWord) : (HP w).n = w.length := by
  simp [PTFamily.n, HP, zoForward]

theorem HM_n (w : BinaryWord) : (HM w).n = w.length := by
  simp [PTFamily.n, HM, zoReversedStacked]

theorem posMH_succ (w : BinaryWord) (j : ℕ) :
    posMH w (j + 1) = posMH w j + rsH (lettersOf w true j) (lettersOf w true (j + 1)) := by
  unfold posMH
  rw [posF_rev_succ]
  abel

/-- The plus odometers of two consecutive tiles agree on their overlap. -/
theorem HP_pair_succ (w : BinaryWord) (k : ℕ) (hk : k + 1 < w.length) (x : GInt)
    (hx1 : x ∈ (HP w).dom k) (hx2 : x ∈ (HP w).dom (k + 1)) :
    (HP w).odo k x = (HP w).odo (k + 1) x := by
  rw [mem_HP_dom w k (by omega)] at hx1
  rw [mem_HP_dom w (k + 1) hk] at hx2
  obtain ⟨u, hu, hux⟩ := hx1
  obtain ⟨v, hv, hvx⟩ := hx2
  rw [HP_odo w k (by omega) x, HP_odo w (k + 1) hk x]
  have e1 : x - posF .horizontal false (lettersOf w false) k = u := by rw [← hux]; abel
  have e2 : x - posF .horizontal false (lettersOf w false) (k + 1) = u - zeroOneHorizontalStep (lettersOf w false (k + 1)) := by
    rw [posF_fwd_succ, ← hux]; abel
  have hv' : u - zeroOneHorizontalStep (lettersOf w false (k + 1)) = v := by
    have h3 : x - posF .horizontal false (lettersOf w false) (k + 1) = v := by rw [← hvx]; abel
    rw [← e2, h3]
  rw [e1, e2]
  apply local_plus_overlap (lettersOf w false k) (lettersOf w false (k + 1)) u hu
  rw [hv']
  exact hv

/-- Two plus tiles at index distance at least two do not overlap. -/
theorem HP_pair_far (w : BinaryWord) (k j : ℕ) (hjk : k + 2 ≤ j) (hj : j < w.length) (x : GInt)
    (hx1 : x ∈ (HP w).dom k) (hx2 : x ∈ (HP w).dom j) : False := by
  rw [mem_HP_dom w k (by omega)] at hx1
  rw [mem_HP_dom w j hj] at hx2
  obtain ⟨u, hu, hux⟩ := hx1
  obtain ⟨v, hv, hvx⟩ := hx2
  have hxu := tile_rel_x (lettersOf w false k) u hu
  have hxv := tile_rel_x (lettersOf w false j) v hv
  have hmono := posF_fwd_x_ge (lettersOf w false) k (j - k)
  rw [show k + (j - k) = j by omega] at hmono
  have e := congrArg Prod.fst (hux.trans hvx.symm)
  simp only [Prod.fst_add] at e
  omega

/-- The minus odometers of two consecutive tiles agree on their overlap. -/
theorem HM_pair_succ (w : BinaryWord) (j : ℕ) (hj : j + 1 < w.length) (x : GInt)
    (hx1 : x ∈ (HM w).dom j) (hx2 : x ∈ (HM w).dom (j + 1)) :
    (HM w).odo j x = (HM w).odo (j + 1) x := by
  rw [mem_HM_dom w j (by omega)] at hx1
  rw [mem_HM_dom w (j + 1) hj] at hx2
  obtain ⟨u, hu, hux⟩ := hx1
  obtain ⟨v, hv, hvx⟩ := hx2
  rw [HM_odo_rel w j (by omega) x, HM_odo_rel w (j + 1) hj x]
  have e1 : x - posMH w j = u := by rw [← hux]; abel
  have e2 : x - posMH w (j + 1) = u - rsH (lettersOf w true j) (lettersOf w true (j + 1)) := by
    rw [posMH_succ, ← hux]; abel
  have hv' : u - rsH (lettersOf w true j) (lettersOf w true (j + 1)) = v := by
    have h3 : x - posMH w (j + 1) = v := by rw [← hvx]; abel
    rw [← e2, h3]
  rw [e1, e2]
  apply local_minus_overlap (lettersOf w true j) (lettersOf w true (j + 1)) u hu
  rw [hv']
  exact hv

/-- Two minus tiles at index distance at least two do not overlap. -/
theorem HM_pair_far (w : BinaryWord) (k j : ℕ) (hjk : k + 2 ≤ j) (hj : j < w.length) (x : GInt)
    (hx1 : x ∈ (HM w).dom k) (hx2 : x ∈ (HM w).dom j) : False := by
  rw [mem_HM_dom w k (by omega)] at hx1
  rw [mem_HM_dom w j hj] at hx2
  obtain ⟨u, hu, hux⟩ := hx1
  obtain ⟨v, hv, hvx⟩ := hx2
  have hxu := tile_rel_x (lettersOf w true k) u hu
  have hxv := tile_rel_x (lettersOf w true j) v hv
  have hmono := posRev_x_ge (lettersOf w true) k (j - k)
  rw [show k + (j - k) = j by omega] at hmono
  have e := congrArg Prod.fst (hux.trans hvx.symm)
  simp only [Prod.fst_add, posMH, Prod.fst_sub, horizontalStackShift] at e hmono
  omega

theorem tileShape_unitSquares_ne (l : Letter) : unitSquares (tileShape (letterZTile l)) ≠ [] := by
  cases l <;> decide

/-- The slope of a placed odometer: the base slope of its tile, plus its affine factor. -/
theorem slope_odo_gen (F : PTFamily) (k : ℕ) (l : Letter) (p : GInt) (htile : F.tile k = (letterZTile l, p)) :
    slopeOf (F.odo k) (F.dom k) =
      slopeOf (zTileOdo (letterZTile l)) (tileShape (letterZTile l)) + (((F.a k).1 : ℚ), ((F.a k).2 : ℚ)) := by
  have hodo : F.odo k = fun x => zTileOdo (letterZTile l) (x - p) + dotS (F.a k) x + F.b k := by
    funext x
    unfold PTFamily.odo dotS
    rw [htile]
    dsimp only
    ring
  have hdom : F.dom k = (tileShape (letterZTile l)).map (· + p) := by
    unfold PTFamily.dom; rw [htile]
  have hT : unitSquares ((tileShape (letterZTile l)).map (· + p)) ≠ [] := by
    rw [unitSquares_map_add]
    intro h
    exact tileShape_unitSquares_ne l (List.map_eq_nil_iff.mp h)
  rw [hodo, hdom, slopeOf_affine _ _ _ _ hT, slopeOf_translate]

/-- The base slope of a plus tile plus the (zero) affine part of the plus family, in the surgical table. -/
theorem slope_diff_plus (a b : Letter) :
    (slopeOf (zTileOdo (letterZTile b)) (tileShape (letterZTile b)) + (((0 : GInt).1 : ℚ), ((0 : GInt).2 : ℚ))) -
        (slopeOf (zTileOdo (letterZTile a)) (tileShape (letterZTile a)) + (((0 : GInt).1 : ℚ), ((0 : GInt).2 : ℚ))) =
      surgicalSlopeDiff .horizontal false a b := by
  cases a <;> cases b <;> simp only [slope_base_p, slope_base_q, surgicalSlopeDiff, Prod.fst_zero, Prod.snd_zero, Prod.mk_zero_zero] <;> norm_num

/-- The base slope of a minus tile plus its affine factor `alphaH`, in the reversed surgical table. -/
theorem slope_diff_minus (a b : Letter) :
    (slopeOf (zTileOdo (letterZTile b)) (tileShape (letterZTile b)) + (((alphaH b).1 : ℚ), ((alphaH b).2 : ℚ))) -
        (slopeOf (zTileOdo (letterZTile a)) (tileShape (letterZTile a)) + (((alphaH a).1 : ℚ), ((alphaH a).2 : ℚ))) =
      surgicalSlopeDiff .horizontal true a b := by
  cases a <;> cases b <;> simp only [slope_base_p, slope_base_q, surgicalSlopeDiff, alphaH, Prod.mk_zero_zero] <;> norm_num


theorem HP_slope (w : BinaryWord) (k : ℕ) (hk : k < w.length) :
    slopeOf ((HP w).odo k) ((HP w).dom k) =
      slopeOf (zTileOdo (letterZTile (lettersOf w false k))) (tileShape (letterZTile (lettersOf w false k)))
        + (((0 : GInt).1 : ℚ), ((0 : GInt).2 : ℚ)) := by
  rw [slope_odo_gen (HP w) k (lettersOf w false k) _ (HP_tile w k hk)]
  rfl

theorem HP_respects (w : BinaryWord) : (HP w).Respects .horizontal false := by
  intro k hk'
  rw [HP_n] at hk'
  have hk1 : k + 1 < w.length := hk'
  have hk0 : k < w.length := by omega
  refine ⟨?_, ?_⟩
  · rw [HP_slope w (k + 1) hk1, HP_slope w k hk0, HP_tile w k hk0, HP_tile w (k + 1) hk1]
    simp only [zTileLetter_letterZTile]
    exact slope_diff_plus _ _
  · intro hno x hx y hy hunit
    refine ⟨fun _ => ?_, fun h => by cases h⟩
    rw [mem_HP_dom w k hk0] at hx
    rw [mem_HP_dom w (k + 1) hk1] at hy
    obtain ⟨u, hu, hux⟩ := hx
    obtain ⟨v, hv, hvy⟩ := hy
    have hE : u - v - zeroOneHorizontalStep (lettersOf w false (k + 1)) = x - y := by
      rw [← hux, ← hvy, posF_fwd_succ]; abel
    have hE' : (u - v - zeroOneHorizontalStep (lettersOf w false (k + 1))).1.natAbs
        + (u - v - zeroOneHorizontalStep (lettersOf w false (k + 1))).2.natAbs = 1 := by
      rw [hE]; simpa only [unitApart, Prod.fst_sub, Prod.snd_sub] using hunit
    have hno' : ∀ u' ∈ tileShape (letterZTile (lettersOf w false k)),
        ∀ v' ∈ tileShape (letterZTile (lettersOf w false (k + 1))),
        u' - v' ≠ zeroOneHorizontalStep (lettersOf w false (k + 1)) := by
      intro u' hu' v' hv' heq
      apply hno
      refine ⟨u' + posF .horizontal false (lettersOf w false) k,
        (mem_HP_dom w k hk0 _).2 ⟨u', hu', rfl⟩, (mem_HP_dom w (k + 1) hk1 _).2 ⟨v', hv', ?_⟩⟩
      rw [posF_fwd_succ]
      have h' : u' = v' + zeroOneHorizontalStep (lettersOf w false (k + 1)) := by rw [← heq]; abel
      rw [h']; abel
    have hloc := local_plus_adj (lettersOf w false k) (lettersOf w false (k + 1)) u hu v hv hno' hE'
    have ex : x - posF .horizontal false (lettersOf w false) k = u := by rw [← hux]; abel
    have ey : y - posF .horizontal false (lettersOf w false) (k + 1) = v := by rw [← hvy]; abel
    have ha : ∀ (j : ℕ) (z : GInt), ptDot ((HP w).a j) z = 0 := fun j z => by simp [HP, ptDot]
    rw [HP_odo w k hk0 x, HP_odo w (k + 1) hk1 y, ex, ey, ha k x, ha k y, sub_zero, sub_zero]
    exact hloc

theorem HM_slope (w : BinaryWord) (j : ℕ) (hj : j < w.length) :
    slopeOf ((HM w).odo j) ((HM w).dom j) =
      slopeOf (zTileOdo (letterZTile (lettersOf w true j))) (tileShape (letterZTile (lettersOf w true j)))
        + (((alphaH (lettersOf w true j)).1 : ℚ), ((alphaH (lettersOf w true j)).2 : ℚ)) := by
  rw [slope_odo_gen (HM w) j (lettersOf w true j) _ (HM_tile w j hj)]
  rfl

theorem HM_respects (w : BinaryWord) : (HM w).Respects .horizontal true := by
  intro j hj'
  rw [HM_n] at hj'
  have hj1 : j + 1 < w.length := hj'
  have hj0 : j < w.length := by omega
  refine ⟨?_, ?_⟩
  · rw [HM_slope w (j + 1) hj1, HM_slope w j hj0, HM_tile w j hj0, HM_tile w (j + 1) hj1]
    simp only [zTileLetter_letterZTile]
    exact slope_diff_minus _ _
  · intro hno x hx y hy hunit
    refine ⟨fun _ => ?_, fun h => by cases h⟩
    rw [mem_HM_dom w j hj0] at hx
    rw [mem_HM_dom w (j + 1) hj1] at hy
    obtain ⟨u, hu, hux⟩ := hx
    obtain ⟨v, hv, hvy⟩ := hy
    have hE : u - v - rsH (lettersOf w true j) (lettersOf w true (j + 1)) = x - y := by
      rw [← hux, ← hvy, posMH_succ]; abel
    have hE' : (u - v - rsH (lettersOf w true j) (lettersOf w true (j + 1))).1.natAbs
        + (u - v - rsH (lettersOf w true j) (lettersOf w true (j + 1))).2.natAbs = 1 := by
      rw [hE]; simpa only [unitApart, Prod.fst_sub, Prod.snd_sub] using hunit
    have hno' : ∀ u' ∈ tileShape (letterZTile (lettersOf w true j)),
        ∀ v' ∈ tileShape (letterZTile (lettersOf w true (j + 1))),
        u' - v' ≠ rsH (lettersOf w true j) (lettersOf w true (j + 1)) := by
      intro u' hu' v' hv' heq
      apply hno
      refine ⟨u' + posMH w j, (mem_HM_dom w j hj0 _).2 ⟨u', hu', rfl⟩,
        (mem_HM_dom w (j + 1) hj1 _).2 ⟨v', hv', ?_⟩⟩
      rw [posMH_succ]
      have h' : u' = v' + rsH (lettersOf w true j) (lettersOf w true (j + 1)) := by rw [← heq]; abel
      rw [h']; abel
    have hloc := local_minus_adj (lettersOf w true j) (lettersOf w true (j + 1)) u hu v hv hno' hE'
    rw [HM_odo_rel w j hj0 x, HM_odo_rel w (j + 1) hj1 y]
    have ha : ∀ i : ℕ, (HM w).a i = alphaH (lettersOf w true i) := fun i => rfl
    rw [ha j]
    rw [← hux, ← hvy, posMH_succ]
    unfold ptDot at hloc ⊢
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, add_sub_cancel_right] at hloc ⊢
    linarith [hloc]


theorem HMo_letter_zero (w : BinaryWord) (hf : w.head? = some Letter.q) : lettersOf w false 0 = Letter.q := by
  simpa [lettersOf] using getD_zero_of_head? hf

theorem HMo_letter_last (w : BinaryWord) (hl : w.getLast? = some Letter.p) :
    lettersOf w false (w.length - 1) = Letter.p := by
  simpa [lettersOf] using getD_last_of_getLast? hl

theorem HMo_letter_rev_last (w : BinaryWord) (hf : w.head? = some Letter.q) :
    lettersOf w true (w.length - 1) = Letter.q := by
  have h1 : w.reverse.getLast? = some Letter.q := by rw [List.getLast?_reverse]; exact hf
  simpa [lettersOf, List.length_reverse] using getD_last_of_getLast? h1

theorem HMo_letter_rev_zero (w : BinaryWord) (hl : w.getLast? = some Letter.p) :
    lettersOf w true 0 = Letter.p := by
  have h1 : w.reverse.head? = some Letter.p := by rw [List.head?_reverse]; exact hl
  simpa [lettersOf] using getD_zero_of_head? h1

theorem HMo_within_HP (w : BinaryWord) : WithinCommon (HP w) := by
  intro k hk j hj x hxk hxj
  have hk' : k < w.length := by simpa only [HP_n] using hk
  have hj' : j < w.length := by simpa only [HP_n] using hj
  rcases lt_trichotomy k j with h | h | h
  · by_cases h1 : j = k + 1
    · subst h1
      exact HP_pair_succ w k hj' x hxk hxj
    · exact (HP_pair_far w k j (by omega) hj' x hxk hxj).elim
  · subst h; rfl
  · by_cases h1 : k = j + 1
    · subst h1
      exact (HP_pair_succ w j hk' x hxj hxk).symm
    · exact (HP_pair_far w j k (by omega) hk' x hxj hxk).elim

theorem HMo_within_HM (w : BinaryWord) : WithinCommon (HM w) := by
  intro k hk j hj x hxk hxj
  have hk' : k < w.length := by simpa only [HM_n] using hk
  have hj' : j < w.length := by simpa only [HM_n] using hj
  rcases lt_trichotomy k j with h | h | h
  · by_cases h1 : j = k + 1
    · subst h1
      exact HM_pair_succ w k hj' x hxk hxj
    · exact (HM_pair_far w k j (by omega) hj' x hxk hxj).elim
  · subst h; rfl
  · by_cases h1 : k = j + 1
    · subst h1
      exact (HM_pair_succ w j hk' x hxj hxk).symm
    · exact (HM_pair_far w j k (by omega) hk' x hxj hxk).elim

theorem HMo_cross_same (w : BinaryWord) (hw : IsAlmostPalindrome w) (hf : w.head? = some Letter.q)
    (hl : w.getLast? = some Letter.p) (k : ℕ) (hk : k < w.length) (x : GInt)
    (hxP : x ∈ (HP w).dom k) (hxM : x ∈ (HM w).dom k) : (HP w).odo k x = (HM w).odo k x := by
  rw [mem_HP_dom w k hk] at hxP
  rw [mem_HM_dom w k hk] at hxM
  obtain ⟨u, hu, hux⟩ := hxP
  obtain ⟨v, hv, hvx⟩ := hxM
  have ev : x - posMH w k = v := by rw [← hvx]; abel
  have ex0 : x - posF .horizontal false (lettersOf w false) k = u := by rw [← hux]; abel
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · have h0 := HMo_letter_zero w hf
    have hpm : posF .horizontal false (lettersOf w false) 0 - posMH w 0 = ((-1 : ℤ), (2 : ℤ)) := fixed_hstack w
    have ex : x - posMH w 0 = u + ((-1 : ℤ), (2 : ℤ)) := by rw [← hux, ← hpm]; abel
    have hmem : u + ((-1 : ℤ), (2 : ℤ)) ∈ tileShape (letterZTile (lettersOf w true 0)) := by
      rw [← ex, ev]; exact hv
    rw [h0] at hu
    rw [HP_odo w 0 hk x, HM_odo_rel w 0 hk x, h0, ex0, ex]
    exact local_cross_first (lettersOf w true 0) u hu hmem
  · have hpm : posF .horizontal false (lettersOf w false) k - posMH w k
        = offH (lettersOf w false k) (decide (k + 1 = w.length)) := fixed_off w hw hf hl k hk hk0
    have ex : x - posMH w k = u + offH (lettersOf w false k) (decide (k + 1 = w.length)) := by
      rw [← hux, ← hpm]; abel
    have hmem : u + offH (lettersOf w false k) (decide (k + 1 = w.length))
        ∈ tileShape (letterZTile (lettersOf w true k)) := by
      rw [← ex, ev]; exact hv
    rw [HP_odo w k hk x, HM_odo_rel w k hk x, ex0, ex]
    exact local_cross_kk (lettersOf w false k) (lettersOf w true k) (decide (k + 1 = w.length)) u hu hmem

theorem HMo_cross_succ (w : BinaryWord) (hw : IsAlmostPalindrome w) (hf : w.head? = some Letter.q)
    (hl : w.getLast? = some Letter.p) (j : ℕ) (hj : j + 1 < w.length) (x : GInt)
    (hxP : x ∈ (HP w).dom (j + 1)) (hxM : x ∈ (HM w).dom j) :
    (HP w).odo (j + 1) x = (HM w).odo j x := by
  rw [mem_HP_dom w (j + 1) hj] at hxP
  rw [mem_HM_dom w j (by omega)] at hxM
  obtain ⟨u, hu, hux⟩ := hxP
  obtain ⟨v, hv, hvx⟩ := hxM
  have hpm : posF .horizontal false (lettersOf w false) (j + 1) - posMH w (j + 1)
      = offH (lettersOf w false (j + 1)) (decide (j + 1 + 1 = w.length)) :=
    fixed_off w hw hf hl (j + 1) hj (Nat.succ_pos j)
  have hsum : posF .horizontal false (lettersOf w false) (j + 1) - posMH w j
      = offH (lettersOf w false (j + 1)) (decide (j + 1 + 1 = w.length))
        + rsH (lettersOf w true j) (lettersOf w true (j + 1)) := by
    rw [← hpm, posMH_succ]; abel
  have ex : x - posF .horizontal false (lettersOf w false) (j + 1) = u := by rw [← hux]; abel
  have ex2 : x - posMH w j = u + (offH (lettersOf w false (j + 1)) (decide (j + 1 + 1 = w.length))
      + rsH (lettersOf w true j) (lettersOf w true (j + 1))) := by
    rw [← hux, ← hsum]; abel
  have ev : x - posMH w j = v := by rw [← hvx]; abel
  have hmem : u + (offH (lettersOf w false (j + 1)) (decide (j + 1 + 1 = w.length))
      + rsH (lettersOf w true j) (lettersOf w true (j + 1))) ∈ tileShape (letterZTile (lettersOf w true j)) := by
    rw [← ex2, ev]; exact hv
  have hL : decide (j + 1 + 1 = w.length) = true →
      lettersOf w false (j + 1) = Letter.p ∧ lettersOf w true (j + 1) = Letter.q := by
    intro h
    have hn : j + 1 + 1 = w.length := of_decide_eq_true h
    have e : j + 1 = w.length - 1 := by omega
    rw [e]
    exact ⟨HMo_letter_last w hl, HMo_letter_rev_last w hf⟩
  rw [HP_odo w (j + 1) hj x, HM_odo_rel w j (by omega) x, ex, ex2]
  exact local_cross_km1 (lettersOf w false (j + 1)) (lettersOf w true j) (lettersOf w true (j + 1))
    (decide (j + 1 + 1 = w.length)) hL u hu hmem

theorem HMo_cross (w : BinaryWord) (hw : IsAlmostPalindrome w) (hf : w.head? = some Letter.q)
    (hl : w.getLast? = some Letter.p) : CrossCommon (HP w) (HM w) := by
  intro k hk j hj x hxP hxM
  have hk' : k < w.length := by simpa only [HP_n] using hk
  have hcl : CrossLocal (HP w) (HM w) := crossLocal_horizontal w hw hf hl (HP w) (HM w) rfl rfl
  rcases hcl k hk j hj ⟨x, hxP, hxM⟩ with h | h
  · have hkj : j = k := h
    rw [hkj] at hxM ⊢
    exact HMo_cross_same w hw hf hl k hk' x hxP hxM
  · have hkj : k = j + 1 := h.symm
    have hjn : j + 1 < w.length := by omega
    rw [hkj] at hxP ⊢
    exact HMo_cross_succ w hw hf hl j hjn x hxP hxM

theorem horizontalMoreover_proof (w : BinaryWord) : HorizontalMoreover w := by
  unfold HorizontalMoreover
  intro hw hf hl
  refine ⟨HP w, HM w, rfl, rfl, HP_respects w, HM_respects w, HMo_within_HP w, HMo_within_HM w,
    HMo_cross w hw hf hl, ?_⟩
  show (0 : GInt) - alphaH (lettersOf w true 0) = ((0 : ℤ), (-1 : ℤ))
  rw [HMo_letter_rev_zero w hl]
  decide

end FLatticePaper.Tiles
