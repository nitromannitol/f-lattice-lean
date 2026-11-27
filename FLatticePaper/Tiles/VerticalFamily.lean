import FLatticePaper.Tiles.RespectsLetters

/-! # The explicit vertical families of the vertical Moreover

For a word `w` the forward family `vtP w` lies on the vertical zero-one string of `w` and the reversed family `vtM w` on the
reversed stacked string. Both have tile types `letterZTile` of their letter; affine factors `vtAff ℓ k = (#q before k, -k)`;
positions as in `zoForwardV` and `zoReversedStackedV`; and centred constants given by the recurrences `vtCP`, `vtCM` with the
per-pair increments `vtBetaP`, `vtBetaM` (the overlap constants of overlapping pairs, and the boundary constant minus one for the
pair `(q,q)`, which is the only non-overlapping pair). The `Respects` clauses follow from `PTFamily.respects_of_triples`. -/

namespace FLatticePaper.Tiles

/-- The number of `q` among the first `k` letters of `ℓ`. -/
def vtCnt (ℓ : ℕ → Letter) : ℕ → ℤ
  | 0 => 0
  | k + 1 => vtCnt ℓ k + (if ℓ k = Letter.q then 1 else 0)

/-- The affine factor of the vertical families: `(#q before k, -k)`. -/
def vtAff (ℓ : ℕ → Letter) (k : ℕ) : GInt := (vtCnt ℓ k, -(k : ℤ))

/-- The affine increment of the vertical families after the letter `y`: `(1,-1)` after `q`, `(0,-1)` after `p`. -/
def vtGam (y : Letter) : GInt := (if y = Letter.q then 1 else 0, -1)

/-- The boundary increment of the forward family for the pair `(y,z)`. -/
def vtBetaP : Letter → Letter → ℤ
  | .p, .p => 0
  | .p, .q => -1
  | .q, .p => -2
  | .q, .q => -2

/-- The boundary increment of the reversed family for the pair `(y,z)`. -/
def vtBetaM : Letter → Letter → ℤ
  | .p, .p => 0
  | .p, .q => -1
  | .q, .p => -1
  | .q, .q => -2

/-- The centred constants of the forward family. -/
def vtCP (ℓ : ℕ → Letter) : ℕ → ℤ
  | 0 => 0
  | k + 1 => vtCP ℓ k + vtBetaP (ℓ k) (ℓ (k + 1)) + ptDot (vtAff ℓ k) (zeroOneVerticalStep (ℓ (k + 1)))

/-- The centred constants of the reversed family. -/
def vtCM (ℓ : ℕ → Letter) : ℕ → ℤ
  | 0 => 0
  | k + 1 => vtCM ℓ k + vtBetaM (ℓ k) (ℓ (k + 1))
      + ptDot (vtAff ℓ k) (zeroOneVerticalReversedStep (ℓ k) (ℓ (k + 1)))

/-- The forward vertical family of `w`. -/
def vtP (w : BinaryWord) : PTFamily :=
  { ts := zoForwardV (lettersOf w false) w.length, a := vtAff (lettersOf w false),
    b := fun k => vtCP (lettersOf w false) k
      - ptDot (vtAff (lettersOf w false) k) (posF .vertical false (lettersOf w false) k) }

/-- The reversed vertical family of `w` (on the stacked string). -/
def vtM (w : BinaryWord) : PTFamily :=
  { ts := zoReversedStackedV (lettersOf w true) w.length, a := vtAff (lettersOf w true),
    b := fun j => vtCM (lettersOf w true) j
      - ptDot (vtAff (lettersOf w true) j) (posF .vertical true (lettersOf w true) j - verticalStackShift) }

theorem vtP_n (w : BinaryWord) : (vtP w).n = w.length := by
  simp [PTFamily.n, vtP, zoForwardV]

theorem vtM_n (w : BinaryWord) : (vtM w).n = w.length := by
  simp [PTFamily.n, vtM, zoReversedStackedV]

theorem vtP_tile (w : BinaryWord) (k : ℕ) (hk : k < w.length) :
    (vtP w).tile k = (letterZTile (lettersOf w false k), posF .vertical false (lettersOf w false) k) := by
  unfold PTFamily.tile
  show (zoForwardV (lettersOf w false) w.length).getD k _ = _
  unfold zoForwardV
  rw [List.getD_eq_getElem _ _ (by simp [hk])]
  simp

theorem vtM_tile (w : BinaryWord) (j : ℕ) (hj : j < w.length) :
    (vtM w).tile j = (letterZTile (lettersOf w true j),
      posF .vertical true (lettersOf w true) j - verticalStackShift) := by
  unfold PTFamily.tile
  show (zoReversedStackedV (lettersOf w true) w.length).getD j _ = _
  unfold zoReversedStackedV
  rw [List.getD_eq_getElem _ _ (by simp [hj])]
  simp

/-- The affine factors step by `vtGam` of the current letter. -/
theorem vtAff_succ (ℓ : ℕ → Letter) (k : ℕ) : vtAff ℓ (k + 1) = vtAff ℓ k + vtGam (ℓ k) := by
  ext
  · simp [vtAff, vtGam, vtCnt]
  · simp only [vtAff, vtGam, Prod.snd_add]
    push_cast
    ring

/-- The per-pair boundary identity of the forward family, for all letter pairs (decided). -/
theorem vtBdP : ∀ y z : Letter, ∀ u ∈ tileShape (letterZTile y), ∀ v ∈ tileShape (letterZTile z),
    (∀ u' ∈ tileShape (letterZTile y), ∀ v' ∈ tileShape (letterZTile z), u' - v' ≠ zeroOneVerticalStep z) →
    (u - v - zeroOneVerticalStep z).1.natAbs + (u - v - zeroOneVerticalStep z).2.natAbs = 1 →
    zTileOdo (letterZTile y) u - zTileOdo (letterZTile z) v - ptDot (vtGam y) v = vtBetaP y z + 1 := by
  intro y z; cases y <;> cases z <;> decide

/-- The per-pair boundary identity of the reversed family, for all letter pairs (decided). -/
theorem vtBdM : ∀ y z : Letter, ∀ u ∈ tileShape (letterZTile y), ∀ v ∈ tileShape (letterZTile z),
    (∀ u' ∈ tileShape (letterZTile y), ∀ v' ∈ tileShape (letterZTile z),
      u' - v' ≠ zeroOneVerticalReversedStep y z) →
    (u - v - zeroOneVerticalReversedStep y z).1.natAbs + (u - v - zeroOneVerticalReversedStep y z).2.natAbs = 1 →
    zTileOdo (letterZTile y) u - zTileOdo (letterZTile z) v - ptDot (vtGam y) v = vtBetaM y z + 1 := by
  intro y z; cases y <;> cases z <;> decide

/-- The forward vertical family respects the forward vertical string. -/
theorem vtP_respects (w : BinaryWord) : (vtP w).Respects .vertical false :=
  PTFamily.respects_of_triples (vtP w) .vertical false (lettersOf w false)
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
    (fun _ y => zTileLetter_letterZTile y)
    (fun x y z _ => by
      cases y <;> cases z
      all_goals simp [slope_base_p, slope_base_q, vtGam, surgicalSlopeDiff]
      all_goals norm_num)
    (fun h => by cases h)
    (fun h x y z _ u hu v hv hno hunit => vtBdP y z u hu v hv hno hunit)

/-- The reversed vertical family respects the reversed stacked vertical string. -/
theorem vtM_respects (w : BinaryWord) : (vtM w).Respects .vertical true :=
  PTFamily.respects_of_triples (vtM w) .vertical true (lettersOf w true)
    (fun k => if k = 0 then lettersOf w true 0 else lettersOf w true (k - 1))
    (fun k => posF .vertical true (lettersOf w true) k - verticalStackShift) (fun _ y => letterZTile y)
    (fun y z => zeroOneVerticalReversedStep y z) (fun _ y _ => vtGam y)
    (fun k => vtCM (lettersOf w true) k)
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
    (fun _ y => zTileLetter_letterZTile y)
    (fun x y z _ => by
      cases y <;> cases z
      all_goals simp [slope_base_p, slope_base_q, vtGam, surgicalSlopeDiff]
      all_goals norm_num)
    (fun h => by cases h)
    (fun h x y z _ u hu v hv hno hunit => vtBdM y z u hu v hv hno hunit)

end FLatticePaper.Tiles
