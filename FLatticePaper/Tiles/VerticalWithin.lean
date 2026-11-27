import FLatticePaper.Tiles.VerticalFamily

/-! # Within-family overlaps of the explicit vertical families

Consecutive tiles of `vtP w` and `vtM w` agree on their common points: the boundary quantity is `vtBetaP` (resp. `vtBetaM`) on
the overlaps, checked for every pair of letters by `decide`. Tiles at index distance at least two never overlap: distance two
by a finite check on three letters, distance at least three because the `y`-coordinate of the positions increases by at
least one per tile, while the tiles have rows `0, 1, 2`. -/

namespace FLatticePaper.Tiles

theorem vtRows : ∀ x : Letter, ∀ s ∈ tileShape (letterZTile x), 0 ≤ s.2 ∧ s.2 ≤ 2 := by
  intro x; cases x <;> decide

theorem vtStepY_P (b : Letter) : 1 ≤ (zeroOneVerticalStep b).2 := by
  cases b <;> decide

theorem vtStepY_M (a b : Letter) : 1 ≤ (zeroOneVerticalReversedStep a b).2 := by
  cases a <;> cases b <;> decide

/-- The overlap identity of the forward family, for all letter pairs (decided). -/
theorem vtOvP : ∀ y z : Letter, ∀ u ∈ tileShape (letterZTile y), ∀ v ∈ tileShape (letterZTile z),
    u - v = zeroOneVerticalStep z →
    zTileOdo (letterZTile y) u - zTileOdo (letterZTile z) v - ptDot (vtGam y) v = vtBetaP y z := by
  intro y z; cases y <;> cases z <;> decide

/-- The overlap identity of the reversed family, for all letter pairs (decided). -/
theorem vtOvM : ∀ y z : Letter, ∀ u ∈ tileShape (letterZTile y), ∀ v ∈ tileShape (letterZTile z),
    u - v = zeroOneVerticalReversedStep y z →
    zTileOdo (letterZTile y) u - zTileOdo (letterZTile z) v - ptDot (vtGam y) v = vtBetaM y z := by
  intro y z; cases y <;> cases z <;> decide

/-- Tiles at distance two of the forward family do not overlap. -/
theorem vtTwoP : ∀ a b c : Letter, ∀ u ∈ tileShape (letterZTile a), ∀ v ∈ tileShape (letterZTile c),
    u - v ≠ zeroOneVerticalStep b + zeroOneVerticalStep c := by
  intro a b c; cases a <;> cases b <;> cases c <;> decide

/-- Tiles at distance two of the reversed family do not overlap. -/
theorem vtTwoM : ∀ a b c : Letter, ∀ u ∈ tileShape (letterZTile a), ∀ v ∈ tileShape (letterZTile c),
    u - v ≠ zeroOneVerticalReversedStep a b + zeroOneVerticalReversedStep b c := by
  intro a b c; cases a <;> cases b <;> cases c <;> decide

theorem vtPos_y_ge_P (ℓ : ℕ → Letter) (k m : ℕ) :
    (posF .vertical false ℓ k).2 + (m : ℤ) ≤ (posF .vertical false ℓ (k + m)).2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show k + (m + 1) = (k + m) + 1 by omega]
    have e : posF .vertical false ℓ (k + m + 1)
        = posF .vertical false ℓ (k + m) + zeroOneVerticalStep (ℓ (k + m + 1)) := rfl
    rw [e, Prod.snd_add]
    have := vtStepY_P (ℓ (k + m + 1))
    push_cast
    linarith

theorem vtPos_y_ge_M (ℓ : ℕ → Letter) (k m : ℕ) :
    (posF .vertical true ℓ k).2 + (m : ℤ) ≤ (posF .vertical true ℓ (k + m)).2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show k + (m + 1) = (k + m) + 1 by omega]
    have e : posF .vertical true ℓ (k + m + 1)
        = posF .vertical true ℓ (k + m) + zeroOneVerticalReversedStep (ℓ (k + m)) (ℓ (k + m + 1)) := rfl
    rw [e, Prod.snd_add]
    have := vtStepY_M (ℓ (k + m)) (ℓ (k + m + 1))
    push_cast
    linarith

theorem vtP_mem (w : BinaryWord) (k : ℕ) (hk : k < w.length) (x : GInt) :
    x ∈ (vtP w).dom k ↔ ∃ u ∈ tileShape (letterZTile (lettersOf w false k)),
      u + posF .vertical false (lettersOf w false) k = x := by
  unfold PTFamily.dom
  rw [vtP_tile w k hk]
  simp only [List.mem_map]

theorem vtM_mem (w : BinaryWord) (j : ℕ) (hj : j < w.length) (x : GInt) :
    x ∈ (vtM w).dom j ↔ ∃ u ∈ tileShape (letterZTile (lettersOf w true j)),
      u + (posF .vertical true (lettersOf w true) j - verticalStackShift) = x := by
  unfold PTFamily.dom
  rw [vtM_tile w j hj]
  simp only [List.mem_map]

/-- Tiles of the forward family at distance at least two do not overlap. -/
theorem vtP_far (w : BinaryWord) (k j : ℕ) (hkj : k + 2 ≤ j) (hj : j < w.length) (x : GInt)
    (hx1 : x ∈ (vtP w).dom k) (hx2 : x ∈ (vtP w).dom j) : False := by
  have hk : k < w.length := by omega
  rw [vtP_mem w k hk] at hx1
  rw [vtP_mem w j hj] at hx2
  obtain ⟨u, hu, hux⟩ := hx1
  obtain ⟨v, hv, hvx⟩ := hx2
  rcases Nat.lt_or_ge j (k + 3) with h3 | h3
  · have hjk : j = k + 2 := by omega
    subst hjk
    have e1 : posF .vertical false (lettersOf w false) (k + 1)
        = posF .vertical false (lettersOf w false) k + zeroOneVerticalStep (lettersOf w false (k + 1)) := rfl
    have e2 : posF .vertical false (lettersOf w false) (k + 2)
        = posF .vertical false (lettersOf w false) (k + 1) + zeroOneVerticalStep (lettersOf w false (k + 2)) := rfl
    have h := hux.trans hvx.symm
    have huv : u - v = posF .vertical false (lettersOf w false) (k + 2)
        - posF .vertical false (lettersOf w false) k := by
      calc u - v = (u + posF .vertical false (lettersOf w false) k)
            - (v + posF .vertical false (lettersOf w false) (k + 2))
            + (posF .vertical false (lettersOf w false) (k + 2) - posF .vertical false (lettersOf w false) k) := by
            abel
        _ = posF .vertical false (lettersOf w false) (k + 2)
            - posF .vertical false (lettersOf w false) k := by
            rw [h, sub_self, zero_add]
    rw [e2, e1] at huv
    have huv' : u - v = zeroOneVerticalStep (lettersOf w false (k + 1))
        + zeroOneVerticalStep (lettersOf w false (k + 2)) := by
      rw [huv]; abel
    exact vtTwoP (lettersOf w false k) (lettersOf w false (k + 1)) (lettersOf w false (k + 2)) u hu v hv huv'
  · have hy := vtPos_y_ge_P (lettersOf w false) k (j - k)
    rw [show k + (j - k) = j by omega] at hy
    have hr1 := vtRows _ u hu
    have hr2 := vtRows _ v hv
    have e := congrArg Prod.snd (hux.trans hvx.symm)
    simp only [Prod.snd_add] at e
    have hm : ((j - k : ℕ) : ℤ) ≥ 3 := by omega
    omega

/-- Tiles of the reversed family at distance at least two do not overlap. -/
theorem vtM_far (w : BinaryWord) (k j : ℕ) (hkj : k + 2 ≤ j) (hj : j < w.length) (x : GInt)
    (hx1 : x ∈ (vtM w).dom k) (hx2 : x ∈ (vtM w).dom j) : False := by
  have hk : k < w.length := by omega
  rw [vtM_mem w k hk] at hx1
  rw [vtM_mem w j hj] at hx2
  obtain ⟨u, hu, hux⟩ := hx1
  obtain ⟨v, hv, hvx⟩ := hx2
  rcases Nat.lt_or_ge j (k + 3) with h3 | h3
  · have hjk : j = k + 2 := by omega
    subst hjk
    have e1 : posF .vertical true (lettersOf w true) (k + 1)
        = posF .vertical true (lettersOf w true) k
          + zeroOneVerticalReversedStep (lettersOf w true k) (lettersOf w true (k + 1)) := rfl
    have e2 : posF .vertical true (lettersOf w true) (k + 2)
        = posF .vertical true (lettersOf w true) (k + 1)
          + zeroOneVerticalReversedStep (lettersOf w true (k + 1)) (lettersOf w true (k + 2)) := rfl
    have h := hux.trans hvx.symm
    have huv : u - v = posF .vertical true (lettersOf w true) (k + 2)
        - posF .vertical true (lettersOf w true) k := by
      calc u - v = (u + (posF .vertical true (lettersOf w true) k - verticalStackShift))
            - (v + (posF .vertical true (lettersOf w true) (k + 2) - verticalStackShift))
            + (posF .vertical true (lettersOf w true) (k + 2) - posF .vertical true (lettersOf w true) k) := by
            abel
        _ = posF .vertical true (lettersOf w true) (k + 2)
            - posF .vertical true (lettersOf w true) k := by
            rw [h, sub_self, zero_add]
    rw [e2, e1] at huv
    have huv' : u - v = zeroOneVerticalReversedStep (lettersOf w true k) (lettersOf w true (k + 1))
        + zeroOneVerticalReversedStep (lettersOf w true (k + 1)) (lettersOf w true (k + 2)) := by
      rw [huv]; abel
    exact vtTwoM (lettersOf w true k) (lettersOf w true (k + 1)) (lettersOf w true (k + 2)) u hu v hv huv'
  · have hy := vtPos_y_ge_M (lettersOf w true) k (j - k)
    rw [show k + (j - k) = j by omega] at hy
    have hr1 := vtRows _ u hu
    have hr2 := vtRows _ v hv
    have e := congrArg Prod.snd (hux.trans hvx.symm)
    simp only [Prod.snd_add, Prod.snd_sub, verticalStackShift] at e
    have hm : ((j - k : ℕ) : ℤ) ≥ 3 := by omega
    omega

theorem vtP_pair (w : BinaryWord) (k : ℕ) (hk : k + 1 < w.length) (x : GInt)
    (hx1 : x ∈ (vtP w).dom k) (hx2 : x ∈ (vtP w).dom (k + 1)) :
    (vtP w).odo k x = (vtP w).odo (k + 1) x :=
  PTFamily.within_consecutive_of_triples (vtP w) (lettersOf w false)
    (fun k => if k = 0 then lettersOf w false 0 else lettersOf w false (k - 1))
    (fun k => posF .vertical false (lettersOf w false) k) (fun _ y => letterZTile y)
    (fun y z => zeroOneVerticalStep z) (fun _ y _ => vtGam y) (fun k => vtCP (lettersOf w false) k)
    (fun _ y z => vtBetaP y z) (fun _ _ _ => True)
    (fun k hk => vtP_tile w k (by rw [vtP_n] at hk; exact hk))
    (fun k _ => by
      show (if k + 1 = 0 then lettersOf w false 0 else lettersOf w false (k + 1 - 1)) = lettersOf w false k
      simp)
    (fun k _ => rfl)
    (fun k hk => by
      show vtAff (lettersOf w false) (k + 1) = vtAff (lettersOf w false) k + vtGam (lettersOf w false k)
      exact vtAff_succ _ k)
    (fun k _ => rfl)
    (fun k _ => rfl)
    (fun _ _ => trivial)
    (fun x y z _ u hu v hv huv => vtOvP y z u hu v hv huv)
    k (by rw [vtP_n]; exact hk) x hx1 hx2

theorem vtM_pair (w : BinaryWord) (j : ℕ) (hj : j + 1 < w.length) (x : GInt)
    (hx1 : x ∈ (vtM w).dom j) (hx2 : x ∈ (vtM w).dom (j + 1)) :
    (vtM w).odo j x = (vtM w).odo (j + 1) x :=
  PTFamily.within_consecutive_of_triples (vtM w) (lettersOf w true)
    (fun k => if k = 0 then lettersOf w true 0 else lettersOf w true (k - 1))
    (fun k => posF .vertical true (lettersOf w true) k - verticalStackShift) (fun _ y => letterZTile y)
    (fun y z => zeroOneVerticalReversedStep y z) (fun _ y _ => vtGam y) (fun k => vtCM (lettersOf w true) k)
    (fun _ y z => vtBetaM y z) (fun _ _ _ => True)
    (fun k hk => vtM_tile w k (by rw [vtM_n] at hk; exact hk))
    (fun k _ => by
      show (if k + 1 = 0 then lettersOf w true 0 else lettersOf w true (k + 1 - 1)) = lettersOf w true k
      simp)
    (fun k _ => by
      show posF .vertical true (lettersOf w true) (k + 1) - verticalStackShift
        = (posF .vertical true (lettersOf w true) k - verticalStackShift)
          + zeroOneVerticalReversedStep (lettersOf w true k) (lettersOf w true (k + 1))
      have e : posF .vertical true (lettersOf w true) (k + 1)
          = posF .vertical true (lettersOf w true) k
            + zeroOneVerticalReversedStep (lettersOf w true k) (lettersOf w true (k + 1)) := rfl
      rw [e]
      abel)
    (fun k hk => by
      show vtAff (lettersOf w true) (k + 1) = vtAff (lettersOf w true) k + vtGam (lettersOf w true k)
      exact vtAff_succ _ k)
    (fun k _ => rfl)
    (fun k _ => rfl)
    (fun _ _ => trivial)
    (fun x y z _ u hu v hv huv => vtOvM y z u hu v hv huv)
    j (by rw [vtM_n]; exact hj) x hx1 hx2

/-- The forward family is within-common: overlapping tiles have equal odometers. -/
theorem vtP_within (w : BinaryWord) : WithinCommon (vtP w) := by
  intro k hk j hj x hxk hxj
  have hk' : k < w.length := by simpa only [vtP_n] using hk
  have hj' : j < w.length := by simpa only [vtP_n] using hj
  rcases lt_trichotomy k j with h | h | h
  · by_cases h1 : j = k + 1
    · subst h1
      exact vtP_pair w k hj' x hxk hxj
    · exact (vtP_far w k j (by omega) hj' x hxk hxj).elim
  · subst h
    rfl
  · by_cases h1 : k = j + 1
    · subst h1
      exact (vtP_pair w j hk' x hxj hxk).symm
    · exact (vtP_far w j k (by omega) hk' x hxj hxk).elim

/-- The reversed family is within-common. -/
theorem vtM_within (w : BinaryWord) : WithinCommon (vtM w) := by
  intro k hk j hj x hxk hxj
  have hk' : k < w.length := by simpa only [vtM_n] using hk
  have hj' : j < w.length := by simpa only [vtM_n] using hj
  rcases lt_trichotomy k j with h | h | h
  · by_cases h1 : j = k + 1
    · subst h1
      exact vtM_pair w k hj' x hxk hxj
    · exact (vtM_far w k j (by omega) hj' x hxk hxj).elim
  · subst h
    rfl
  · by_cases h1 : k = j + 1
    · subst h1
      exact (vtM_pair w j hk' x hxj hxk).symm
    · exact (vtM_far w j k (by omega) hk' x hxj hxk).elim

end FLatticePaper.Tiles
