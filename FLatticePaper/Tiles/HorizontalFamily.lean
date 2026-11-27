import FLatticePaper.Tiles.StackedLocal

/-! # The explicit horizontal family of the Moreover

For an almost palindrome `w` starting with `q` and ending with `p`, the plus family `HP w` is the forward zero-one string with
the odometers `zTileOdo` (no affine part, no constant); the minus family `HM w` is the reversed stacked string, with affine
factor `alphaH ℓ` and constant `cstH ℓ - alphaH ℓ · M` at its own letter `ℓ` and position `M`. In relative coordinates the
minus odometer is `zTileOdo ℓ (x - M) + alphaH ℓ · (x - M) + cstH ℓ`, so every overlap and adjacency relation is a relation in
the letters and the relative offsets (a finite check). The first affine factors are `0` and `alphaH p = (0, 1)`, so their
difference is `(0, -1) = a_{p,2}`. -/

namespace FLatticePaper.Tiles

/-- The first-factor parameter of a minus tile of letter `ℓ`: `(0,1)` for `p`, `(-1,1)` for `q`. -/
def alphaH : Letter → GInt
  | .p => ((0 : ℤ), (1 : ℤ))
  | .q => ((-1 : ℤ), (1 : ℤ))

/-- The constant of a minus tile of letter `ℓ` in relative coordinates. -/
def cstH : Letter → ℤ
  | .p => -1
  | .q => 0

/-- The explicit plus family: the forward zero-one string of `w`, with no affine part and no constant. -/
def HP (w : BinaryWord) : PTFamily :=
  { ts := zoForward (lettersOf w false) w.length, a := fun _ => 0, b := fun _ => 0 }

/-- The position of the `j`-th minus tile of the stacked string. -/
def posMH (w : BinaryWord) (j : ℕ) : GInt :=
  posF .horizontal true (lettersOf w true) j - horizontalStackShift

/-- The explicit minus family: the reversed stacked string of `w`, with affine factor `alphaH ℓ` and constant
`cstH ℓ - alphaH ℓ · M` at its own position `M`. -/
def HM (w : BinaryWord) : PTFamily :=
  { ts := zoReversedStacked (lettersOf w true) w.length,
    a := fun j => alphaH (lettersOf w true j),
    b := fun j => cstH (lettersOf w true j) - ptDot (alphaH (lettersOf w true j)) (posMH w j) }

/-- The base odometer of a zero or one tile, as a function of the letter. -/
theorem zTileOdo_letter (l : Letter) (y : GInt) : zTileOdo (letterZTile l) y = (match l with
    | .p => zeroOdometer y
    | .q => oneOdometer y) := by
  cases l <;> rfl

/-- The `j`-th placed tile of `HP w`. -/
theorem HP_tile (w : BinaryWord) (k : ℕ) (hk : k < w.length) :
    (HP w).tile k = (letterZTile (lettersOf w false k), posF .horizontal false (lettersOf w false) k) := by
  unfold HP
  rw [ptile_of_ts _ _ rfl k, zoF_tile _ _ k hk]

/-- The `j`-th placed tile of `HM w`. -/
theorem HM_tile (w : BinaryWord) (j : ℕ) (hj : j < w.length) :
    (HM w).tile j = (letterZTile (lettersOf w true j), posMH w j) := by
  unfold HM
  rw [ptile_of_ts _ _ rfl j, zoR_tile _ _ j hj]
  rfl

/-- The `j`-th minus odometer in relative coordinates. -/
theorem HM_odo_rel (w : BinaryWord) (j : ℕ) (hj : j < w.length) (x : GInt) :
    (HM w).odo j x = zTileOdo (letterZTile (lettersOf w true j)) (x - posMH w j)
      + ptDot (alphaH (lettersOf w true j)) (x - posMH w j) + cstH (lettersOf w true j) := by
  unfold PTFamily.odo
  rw [HM_tile w j hj]
  simp only [HM, ptDot, Prod.fst_sub, Prod.snd_sub]
  ring

/-- The `j`-th plus odometer. -/
theorem HP_odo (w : BinaryWord) (k : ℕ) (hk : k < w.length) (x : GInt) :
    (HP w).odo k x = zTileOdo (letterZTile (lettersOf w false k)) (x - posF .horizontal false (lettersOf w false) k) := by
  unfold PTFamily.odo
  rw [HP_tile w k hk]
  simp [HP]

/-- The slope of the base zero-tile odometer: `s(o_{0/1}) = -i/2`. -/
theorem slope_base_p : slopeOf (zTileOdo (letterZTile .p)) (tileShape (letterZTile .p)) = (0, -1 / 2) := by
  unfold slopeOf unitSquares tileShape letterZTile zTileOdo zeroOdometer
  norm_num

/-- The slope of the base one-tile odometer: `s(o_{1/1}) = (1 - i)/2`. -/
theorem slope_base_q : slopeOf (zTileOdo (letterZTile .q)) (tileShape (letterZTile .q)) = (1 / 2, -1 / 2) := by
  unfold slopeOf unitSquares tileShape letterZTile zTileOdo oneOdometer
  norm_num

/-! The local identities of the explicit horizontal family, as finite checks over the letters and the tile shapes. -/

/-- Plus consecutive overlap: the forward steps agree on the overlap. -/
theorem local_plus_overlap : ∀ a b : Letter, ∀ y ∈ tileShape (letterZTile a),
    y - zeroOneHorizontalStep b ∈ tileShape (letterZTile b) →
    zTileOdo (letterZTile a) y = zTileOdo (letterZTile b) (y - zeroOneHorizontalStep b) := by
  intro a b; cases a <;> cases b <;> decide

/-- Minus consecutive overlap: the affine parts and constants agree on the overlap. -/
theorem local_minus_overlap : ∀ a b : Letter, ∀ y ∈ tileShape (letterZTile a),
    y - rsH a b ∈ tileShape (letterZTile b) →
    zTileOdo (letterZTile a) y + ptDot (alphaH a) y + cstH a =
      zTileOdo (letterZTile b) (y - rsH a b) + ptDot (alphaH b) (y - rsH a b) + cstH b := by
  intro a b; cases a <;> cases b <;> decide

/-- Plus consecutive non-overlapping tiles: the boundary condition across a unit step. -/
theorem local_plus_adj : ∀ a b : Letter, ∀ u ∈ tileShape (letterZTile a), ∀ v ∈ tileShape (letterZTile b),
    (∀ u' ∈ tileShape (letterZTile a), ∀ v' ∈ tileShape (letterZTile b), u' - v' ≠ zeroOneHorizontalStep b) →
    (u - v - zeroOneHorizontalStep b).1.natAbs + (u - v - zeroOneHorizontalStep b).2.natAbs = 1 →
    zTileOdo (letterZTile a) u = zTileOdo (letterZTile b) v := by
  intro a b; cases a <;> cases b <;> decide

/-- Minus consecutive non-overlapping tiles: the boundary condition after the shared translation by `α_a`. -/
theorem local_minus_adj : ∀ a b : Letter, ∀ u ∈ tileShape (letterZTile a), ∀ v ∈ tileShape (letterZTile b),
    (∀ u' ∈ tileShape (letterZTile a), ∀ v' ∈ tileShape (letterZTile b), u' - v' ≠ rsH a b) →
    (u - v - rsH a b).1.natAbs + (u - v - rsH a b).2.natAbs = 1 →
    zTileOdo (letterZTile a) u + cstH a =
      zTileOdo (letterZTile b) v + ptDot (alphaH b - alphaH a) v + cstH b - ptDot (alphaH a) (rsH a b) := by
  intro a b; cases a <;> cases b <;> decide

/-- Cross, same index: the plus tile of letter `x` against the minus tile of letter `b` at offset `offH x last`. -/
theorem local_cross_kk : ∀ x b : Letter, ∀ last : Bool, ∀ y ∈ tileShape (letterZTile x),
    y + offH x last ∈ tileShape (letterZTile b) →
    zTileOdo (letterZTile x) y =
      zTileOdo (letterZTile b) (y + offH x last) + ptDot (alphaH b) (y + offH x last) + cstH b := by
  intro x b last; cases x <;> cases b <;> cases last <;> decide

/-- Cross, first index: the plus tile of letter `q` against the minus tile of letter `b` at offset `(-1, 2)`. -/
theorem local_cross_first : ∀ b : Letter, ∀ y ∈ tileShape (letterZTile .q),
    y + ((-1 : ℤ), (2 : ℤ)) ∈ tileShape (letterZTile b) →
    zTileOdo (letterZTile .q) y =
      zTileOdo (letterZTile b) (y + ((-1 : ℤ), (2 : ℤ))) + ptDot (alphaH b) (y + ((-1 : ℤ), (2 : ℤ))) + cstH b := by
  intro b; cases b <;> decide

/-- Cross, the previous minus index: the plus tile of letter `x` against the minus tile of letter `a` at `offH x last + rsH a b`. -/
theorem local_cross_km1 : ∀ x a b : Letter, ∀ last : Bool, (last = true → x = Letter.p ∧ b = Letter.q) →
    ∀ y ∈ tileShape (letterZTile x),
    y + (offH x last + rsH a b) ∈ tileShape (letterZTile a) →
    zTileOdo (letterZTile x) y =
      zTileOdo (letterZTile a) (y + (offH x last + rsH a b)) + ptDot (alphaH a) (y + (offH x last + rsH a b))
        + cstH a := by
  intro x a b last hL; cases x <;> cases a <;> cases b <;> cases last <;> revert hL <;> decide

end FLatticePaper.Tiles
