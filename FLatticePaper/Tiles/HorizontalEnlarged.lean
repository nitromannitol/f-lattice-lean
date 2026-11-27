import FLatticePaper.Tiles.RespectsLetters

/-! # The horizontal zero-one strings with the enlarged tiles (surgical lines 1293-1300; the operator's answer)

In every horizontal zero-one string, the tile after a `qq` interface is the enlarged tile `T^d_{1/1} = oneD` with the same corner.
Each part of the stacked string is taken in its own letter order. The tile of the letter `k` is `hTt (ℓ (k-1)) (ℓ k)`, with
`ℓ (-1) = p`. The base slope of `oneD` equals that of `one`, and every boundary and overlap constant is zero for every triple of
letters, so the affine factors and constants of the plain strings are kept; only the tile types change. -/

namespace FLatticePaper.Tiles

/-- The forward explicit family with the enlarged tiles (no affine part, no constant). -/
def HPE (w : BinaryWord) : PTFamily :=
  { ts := zoForwardE (lettersOf w false) w.length, a := fun _ => 0, b := fun _ => 0 }

/-- The reversed explicit family with the enlarged tiles (affine factor `alphaH`, constant `cstH`). -/
def HME (w : BinaryWord) : PTFamily :=
  { ts := zoReversedStackedE (lettersOf w true) w.length,
    a := fun j => alphaH (lettersOf w true j),
    b := fun j => cstH (lettersOf w true j) - ptDot (alphaH (lettersOf w true j)) (posMH w j) }

theorem hTt_letter (x y : Letter) : zTileLetter (hTt x y) = y := by
  cases x <;> cases y <;> rfl

theorem hPrev_succ (ℓ : ℕ → Letter) (k : ℕ) : hPrev ℓ (k + 1) = ℓ k := by
  simp [hPrev]

theorem zoE_tile_fwd (ℓ : ℕ → Letter) (n k : ℕ) (hk : k < n) :
    (zoForwardE ℓ n).getD k (ZTile.zero, (0 : GInt)) = (hTileAt ℓ k, posF .horizontal false ℓ k) := by
  unfold zoForwardE
  rw [List.getD_eq_getElem _ _ (by simp [hk])]
  simp

theorem zoE_tile_rev (ℓ : ℕ → Letter) (n k : ℕ) (hk : k < n) :
    (zoReversedStackedE ℓ n).getD k (ZTile.zero, (0 : GInt)) =
      (hTileAt ℓ k, posF .horizontal true ℓ k - horizontalStackShift) := by
  unfold zoReversedStackedE
  rw [List.getD_eq_getElem _ _ (by simp [hk])]
  simp

theorem HPE_n (w : BinaryWord) : (HPE w).n = w.length := by
  simp [PTFamily.n, HPE, zoForwardE]

theorem HME_n (w : BinaryWord) : (HME w).n = w.length := by
  simp [PTFamily.n, HME, zoReversedStackedE]

theorem HPE_tile (w : BinaryWord) (k : ℕ) (hk : k < w.length) :
    (HPE w).tile k = (hTileAt (lettersOf w false) k, posF .horizontal false (lettersOf w false) k) := by
  unfold PTFamily.tile
  exact zoE_tile_fwd (lettersOf w false) w.length k hk

theorem HME_tile (w : BinaryWord) (j : ℕ) (hj : j < w.length) :
    (HME w).tile j = (hTileAt (lettersOf w true) j, posMH w j) := by
  unfold PTFamily.tile
  exact zoE_tile_rev (lettersOf w true) w.length j hj

/-- The base slope of the enlarged tile equals that of the one tile. -/
theorem slope_base_oneD : slopeOf (zTileOdo ZTile.oneD) (tileShape ZTile.oneD) = (1 / 2, -1 / 2) := by
  unfold slopeOf unitSquares tileShape zTileOdo oneOdometer
  norm_num

/-- The base slope of a tile of a horizontal string ending in `p`: the zero tile. -/
theorem hTt_base_p (x : Letter) :
    slopeOf (zTileOdo (hTt x Letter.p)) (tileShape (hTt x Letter.p)) = (0, -1 / 2) := by
  cases x
  · exact slope_base_p
  · exact slope_base_p

/-- The base slope of a tile of a horizontal string ending in `q`: the one tile or the enlarged one. -/
theorem hTt_base_q (x : Letter) :
    slopeOf (zTileOdo (hTt x Letter.q)) (tileShape (hTt x Letter.q)) = (1 / 2, -1 / 2) := by
  cases x
  · exact slope_base_q
  · exact slope_base_oneD

theorem hTt_xbounds : ∀ x y : Letter, ∀ s ∈ tileShape (hTt x y), -1 ≤ s.1 ∧ s.1 ≤ 1 := by
  intro x y; cases x <;> cases y <;> decide

/-- Forward boundary identity of the enlarged tiles (decided). -/
theorem hE_fwd : ∀ x y z : Letter, ∀ u ∈ tileShape (hTt x y), ∀ v ∈ tileShape (hTt y z),
    (∀ u' ∈ tileShape (hTt x y), ∀ v' ∈ tileShape (hTt y z), u' - v' ≠ zeroOneHorizontalStep z) →
    (u - v - zeroOneHorizontalStep z).1.natAbs + (u - v - zeroOneHorizontalStep z).2.natAbs = 1 →
    zTileOdo (hTt x y) u - zTileOdo (hTt y z) v - ptDot ((0 : GInt)) v = 0 := by
  intro x y z; cases x <;> cases y <;> cases z <;> decide

/-- Forward overlap identity of the enlarged tiles (decided). -/
theorem hO_fwd : ∀ x y z : Letter, ∀ u ∈ tileShape (hTt x y), ∀ v ∈ tileShape (hTt y z),
    u - v = zeroOneHorizontalStep z →
    zTileOdo (hTt x y) u - zTileOdo (hTt y z) v - ptDot ((0 : GInt)) v = 0 := by
  intro x y z; cases x <;> cases y <;> cases z <;> decide

/-- Reversed boundary identity of the enlarged tiles, with the affine increment `alphaH z - alphaH y` (decided). -/
theorem hE_rev : ∀ x y z : Letter, ∀ u ∈ tileShape (hTt x y), ∀ v ∈ tileShape (hTt y z),
    (∀ u' ∈ tileShape (hTt x y), ∀ v' ∈ tileShape (hTt y z), u' - v' ≠ zeroOneHorizontalReversedStep y z) →
    (u - v - zeroOneHorizontalReversedStep y z).1.natAbs + (u - v - zeroOneHorizontalReversedStep y z).2.natAbs = 1 →
    zTileOdo (hTt x y) u - zTileOdo (hTt y z) v - ptDot (alphaH z - alphaH y) v = 0 := by
  intro x y z; cases x <;> cases y <;> cases z <;> decide

/-- Reversed overlap identity of the enlarged tiles (decided). -/
theorem hO_rev : ∀ x y z : Letter, ∀ u ∈ tileShape (hTt x y), ∀ v ∈ tileShape (hTt y z),
    u - v = zeroOneHorizontalReversedStep y z →
    zTileOdo (hTt x y) u - zTileOdo (hTt y z) v - ptDot (alphaH z - alphaH y) v = 0 := by
  intro x y z; cases x <;> cases y <;> cases z <;> decide

/-- The reversed centred constants step by the reversed position step (decided). -/
theorem hcst_rev : ∀ y z : Letter, cstH z = cstH y + ptDot (alphaH y) (zeroOneHorizontalReversedStep y z) := by
  intro y z; cases y <;> cases z <;> decide

/-- Tiles at index distance two of the forward enlarged family do not overlap (decided). -/
theorem hFar2_fwd : ∀ a0 a b c : Letter, ∀ u ∈ tileShape (hTt a0 a), ∀ v ∈ tileShape (hTt b c),
    u - v ≠ zeroOneHorizontalStep b + zeroOneHorizontalStep c := by
  intro a0 a b c; cases a0 <;> cases a <;> cases b <;> cases c <;> decide

/-- Tiles at index distance two of the reversed enlarged family do not overlap (decided). -/
theorem hFar2_rev : ∀ a0 a b c : Letter, ∀ u ∈ tileShape (hTt a0 a), ∀ v ∈ tileShape (hTt b c),
    u - v ≠ zeroOneHorizontalReversedStep a b + zeroOneHorizontalReversedStep b c := by
  intro a0 a b c; cases a0 <;> cases a <;> cases b <;> cases c <;> decide

theorem HPE_respects (w : BinaryWord) : (HPE w).Respects .horizontal false :=
  PTFamily.respects_of_triples (HPE w) .horizontal false (lettersOf w false) (hPrev (lettersOf w false))
    (fun k => posF .horizontal false (lettersOf w false) k) hTt
    (fun _ z => zeroOneHorizontalStep z) (fun _ _ _ => (0 : GInt)) (fun _ => (0 : ℤ))
    (fun _ _ _ => (0 : ℤ)) (fun _ _ _ => True)
    (fun k hk => by
      rw [HPE_n] at hk
      exact HPE_tile w k hk)
    (fun k _ => hPrev_succ _ k)
    (fun k _ => rfl)
    (fun k _ => by simp [HPE])
    (fun k _ => by simp [HPE, ptDot])
    (fun k _ => by simp [HPE, ptDot])
    (fun _ _ => trivial)
    (fun x y => hTt_letter x y)
    (fun x y z _ => by
      cases y <;> cases z
      all_goals simp [hTt_base_p, hTt_base_q, surgicalSlopeDiff, Prod.ext_iff]
      all_goals norm_num)
    (fun _ x y z _ u hu v hv hno hunit => hE_fwd x y z u hu v hv hno hunit)
    (fun h => by cases h)

theorem HME_respects (w : BinaryWord) : (HME w).Respects .horizontal true :=
  PTFamily.respects_of_triples (HME w) .horizontal true (lettersOf w true) (hPrev (lettersOf w true))
    (fun k => posMH w k) hTt
    (fun y z => zeroOneHorizontalReversedStep y z) (fun _ y z => alphaH z - alphaH y)
    (fun k => cstH (lettersOf w true k)) (fun _ _ _ => (0 : ℤ)) (fun _ _ _ => True)
    (fun k hk => by
      rw [HME_n] at hk
      exact HME_tile w k hk)
    (fun k _ => hPrev_succ _ k)
    (fun k hk => posMH_succ w k)
    (fun k hk => by
      show alphaH (lettersOf w true (k + 1)) = alphaH (lettersOf w true k)
        + (alphaH (lettersOf w true (k + 1)) - alphaH (lettersOf w true k))
      abel)
    (fun k _ => rfl)
    (fun k hk => by
      show cstH (lettersOf w true (k + 1)) = cstH (lettersOf w true k) + (0 : ℤ)
        + ptDot (alphaH (lettersOf w true k)) (zeroOneHorizontalReversedStep (lettersOf w true k) (lettersOf w true (k + 1)))
      rw [hcst_rev]
      ring)
    (fun _ _ => trivial)
    (fun x y => hTt_letter x y)
    (fun x y z _ => by
      cases y <;> cases z <;> simp [hTt_base_p, hTt_base_q, surgicalSlopeDiff, alphaH, Prod.ext_iff] <;> norm_num)
    (fun _ x y z _ u hu v hv hno hunit => hE_rev x y z u hu v hv hno hunit)
    (fun h => by cases h)

theorem HPE_mem (w : BinaryWord) (k : ℕ) (hk : k < w.length) (x : GInt) :
    x ∈ (HPE w).dom k ↔ ∃ u ∈ tileShape (hTileAt (lettersOf w false) k),
      u + posF .horizontal false (lettersOf w false) k = x := by
  unfold PTFamily.dom
  rw [HPE_tile w k hk]
  simp only [List.mem_map]

theorem HME_mem (w : BinaryWord) (j : ℕ) (hj : j < w.length) (x : GInt) :
    x ∈ (HME w).dom j ↔ ∃ u ∈ tileShape (hTileAt (lettersOf w true) j), u + posMH w j = x := by
  unfold PTFamily.dom
  rw [HME_tile w j hj]
  simp only [List.mem_map]

/-- Tiles of the forward enlarged family at index distance at least two do not overlap. -/
theorem HPE_far (w : BinaryWord) (k j : ℕ) (hkj : k + 2 ≤ j) (hj : j < w.length) (x : GInt)
    (hx1 : x ∈ (HPE w).dom k) (hx2 : x ∈ (HPE w).dom j) : False := by
  have hk : k < w.length := by omega
  rw [HPE_mem w k hk] at hx1
  rw [HPE_mem w j hj] at hx2
  obtain ⟨u, hu, hux⟩ := hx1
  obtain ⟨v, hv, hvx⟩ := hx2
  rcases Nat.lt_or_ge j (k + 3) with h3 | h3
  · have hjk : j = k + 2 := by omega
    subst hjk
    have e1 : posF .horizontal false (lettersOf w false) (k + 1)
        = posF .horizontal false (lettersOf w false) k + zeroOneHorizontalStep (lettersOf w false (k + 1)) := rfl
    have e2 : posF .horizontal false (lettersOf w false) (k + 2)
        = posF .horizontal false (lettersOf w false) (k + 1) + zeroOneHorizontalStep (lettersOf w false (k + 2)) := rfl
    have hp2 : hPrev (lettersOf w false) (k + 2) = lettersOf w false (k + 1) := hPrev_succ _ (k + 1)
    have hu' : u ∈ tileShape (hTt (hPrev (lettersOf w false) k) (lettersOf w false k)) := hu
    have hv' : v ∈ tileShape (hTt (lettersOf w false (k + 1)) (lettersOf w false (k + 2))) := by
      have h := hv
      unfold hTileAt at h
      rw [hp2] at h
      exact h
    have h := hux.trans hvx.symm
    have huv : u - v = posF .horizontal false (lettersOf w false) (k + 2)
        - posF .horizontal false (lettersOf w false) k := by
      calc u - v = (u + posF .horizontal false (lettersOf w false) k)
            - (v + posF .horizontal false (lettersOf w false) (k + 2))
            + (posF .horizontal false (lettersOf w false) (k + 2) - posF .horizontal false (lettersOf w false) k) := by
            abel
        _ = posF .horizontal false (lettersOf w false) (k + 2)
            - posF .horizontal false (lettersOf w false) k := by
            rw [h, sub_self, zero_add]
    rw [e2, e1] at huv
    have huv' : u - v = zeroOneHorizontalStep (lettersOf w false (k + 1))
        + zeroOneHorizontalStep (lettersOf w false (k + 2)) := by
      rw [huv]
      abel
    exact hFar2_fwd (hPrev (lettersOf w false) k) (lettersOf w false k) (lettersOf w false (k + 1))
      (lettersOf w false (k + 2)) u hu' v hv' huv'
  · have hx := posF_fwd_x_ge (lettersOf w false) k (j - k)
    rw [show k + (j - k) = j by omega] at hx
    have hu1 := hTt_xbounds _ _ u hu
    have hv1 := hTt_xbounds _ _ v hv
    have e := congrArg Prod.fst (hux.trans hvx.symm)
    simp only [Prod.fst_add] at e
    have hm : ((j - k : ℕ) : ℤ) ≥ 3 := by omega
    omega

/-- Tiles of the reversed enlarged family at index distance at least two do not overlap. -/
theorem HME_far (w : BinaryWord) (k j : ℕ) (hkj : k + 2 ≤ j) (hj : j < w.length) (x : GInt)
    (hx1 : x ∈ (HME w).dom k) (hx2 : x ∈ (HME w).dom j) : False := by
  have hk : k < w.length := by omega
  rw [HME_mem w k hk] at hx1
  rw [HME_mem w j hj] at hx2
  obtain ⟨u, hu, hux⟩ := hx1
  obtain ⟨v, hv, hvx⟩ := hx2
  rcases Nat.lt_or_ge j (k + 3) with h3 | h3
  · have hjk : j = k + 2 := by omega
    subst hjk
    have e1 : posF .horizontal true (lettersOf w true) (k + 1)
        = posF .horizontal true (lettersOf w true) k + zeroOneHorizontalReversedStep (lettersOf w true k) (lettersOf w true (k + 1)) := rfl
    have e2 : posF .horizontal true (lettersOf w true) (k + 2)
        = posF .horizontal true (lettersOf w true) (k + 1) + zeroOneHorizontalReversedStep (lettersOf w true (k + 1)) (lettersOf w true (k + 2)) := rfl
    have hp2 : hPrev (lettersOf w true) (k + 2) = lettersOf w true (k + 1) := hPrev_succ _ (k + 1)
    have hu' : u ∈ tileShape (hTt (hPrev (lettersOf w true) k) (lettersOf w true k)) := hu
    have hv' : v ∈ tileShape (hTt (lettersOf w true (k + 1)) (lettersOf w true (k + 2))) := by
      have h := hv
      unfold hTileAt at h
      rw [hp2] at h
      exact h
    have h := hux.trans hvx.symm
    have huv : u - v = posMH w (k + 2) - posMH w k := by
      calc u - v = (u + posMH w k) - (v + posMH w (k + 2)) + (posMH w (k + 2) - posMH w k) := by
            abel
        _ = posMH w (k + 2) - posMH w k := by
            rw [h, sub_self, zero_add]
    rw [show posMH w (k + 2) = posF .horizontal true (lettersOf w true) (k + 2) - horizontalStackShift from rfl,
      show posMH w k = posF .horizontal true (lettersOf w true) k - horizontalStackShift from rfl, e2, e1] at huv
    have huv' : u - v = zeroOneHorizontalReversedStep (lettersOf w true k) (lettersOf w true (k + 1))
        + zeroOneHorizontalReversedStep (lettersOf w true (k + 1)) (lettersOf w true (k + 2)) := by
      rw [huv]
      abel
    exact hFar2_rev (hPrev (lettersOf w true) k) (lettersOf w true k) (lettersOf w true (k + 1))
      (lettersOf w true (k + 2)) u hu' v hv' huv'
  · have hx := posRev_x_ge (lettersOf w true) k (j - k)
    rw [show k + (j - k) = j by omega] at hx
    have hu1 := hTt_xbounds _ _ u hu
    have hv1 := hTt_xbounds _ _ v hv
    have e := congrArg Prod.fst (hux.trans hvx.symm)
    simp only [Prod.fst_add, posMH, Prod.fst_sub, horizontalStackShift] at e hx
    have hm : ((j - k : ℕ) : ℤ) ≥ 3 := by omega
    omega

theorem HPE_within (w : BinaryWord) : WithinCommon (HPE w) := by
  have hcons := PTFamily.within_consecutive_of_triples (HPE w) (lettersOf w false) (hPrev (lettersOf w false))
    (fun k => posF .horizontal false (lettersOf w false) k) hTt (fun _ z => zeroOneHorizontalStep z)
    (fun _ _ _ => (0 : GInt)) (fun _ => (0 : ℤ)) (fun _ _ _ => (0 : ℤ)) (fun _ _ _ => True)
    (fun k hk => by
      rw [HPE_n] at hk
      exact HPE_tile w k hk)
    (fun k _ => hPrev_succ _ k)
    (fun k _ => rfl)
    (fun k _ => by simp [HPE])
    (fun k _ => by simp [HPE, ptDot])
    (fun k _ => by simp [HPE, ptDot])
    (fun _ _ => trivial)
    (fun x y z _ u hu v hv huv => hO_fwd x y z u hu v hv huv)
  intro k hk j hj x hxk hxj
  have hk' : k < w.length := by simpa only [HPE_n] using hk
  have hj' : j < w.length := by simpa only [HPE_n] using hj
  rcases lt_trichotomy k j with h | h | h
  · by_cases h1 : j = k + 1
    · subst h1
      exact hcons k (by rw [HPE_n]; omega) x hxk hxj
    · exact (HPE_far w k j (by omega) hj' x hxk hxj).elim
  · subst h
    rfl
  · by_cases h1 : k = j + 1
    · subst h1
      exact (hcons j (by rw [HPE_n]; omega) x hxj hxk).symm
    · exact (HPE_far w j k (by omega) hk' x hxj hxk).elim

theorem HME_within (w : BinaryWord) : WithinCommon (HME w) := by
  have hcons := PTFamily.within_consecutive_of_triples (HME w) (lettersOf w true) (hPrev (lettersOf w true))
    (fun k => posMH w k) hTt (fun y z => zeroOneHorizontalReversedStep y z) (fun _ y z => alphaH z - alphaH y)
    (fun k => cstH (lettersOf w true k)) (fun _ _ _ => (0 : ℤ)) (fun _ _ _ => True)
    (fun k hk => by
      rw [HME_n] at hk
      exact HME_tile w k hk)
    (fun k _ => hPrev_succ _ k)
    (fun k hk => posMH_succ w k)
    (fun k hk => by
      show alphaH (lettersOf w true (k + 1)) = alphaH (lettersOf w true k)
        + (alphaH (lettersOf w true (k + 1)) - alphaH (lettersOf w true k))
      abel)
    (fun k _ => rfl)
    (fun k hk => by
      show cstH (lettersOf w true (k + 1)) = cstH (lettersOf w true k) + (0 : ℤ)
        + ptDot (alphaH (lettersOf w true k)) (zeroOneHorizontalReversedStep (lettersOf w true k) (lettersOf w true (k + 1)))
      rw [hcst_rev]
      ring)
    (fun _ _ => trivial)
    (fun x y z _ u hu v hv huv => hO_rev x y z u hu v hv huv)
  intro k hk j hj x hxk hxj
  have hk' : k < w.length := by simpa only [HME_n] using hk
  have hj' : j < w.length := by simpa only [HME_n] using hj
  rcases lt_trichotomy k j with h | h | h
  · by_cases h1 : j = k + 1
    · subst h1
      exact hcons k (by rw [HME_n]; omega) x hxk hxj
    · exact (HME_far w k j (by omega) hj' x hxk hxj).elim
  · subst h
    rfl
  · by_cases h1 : k = j + 1
    · subst h1
      exact (hcons j (by rw [HME_n]; omega) x hxj hxk).symm
    · exact (HME_far w j k (by omega) hk' x hxj hxk).elim

end FLatticePaper.Tiles
