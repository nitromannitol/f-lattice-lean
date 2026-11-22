import FLatticePaper.Tiles.StackedStringConnected
import Mathlib.Order.Interval.Finset.Nat

/-! The local union of a stacked zero-one string, for an arbitrary letter sequence `ℓ`.

For the first `m` letters: the plus tiles `k < m` (at `posO k`, enlarged by `flagO k` horizontally), the shadow tiles
`2 ≤ k < m` (the minus tiles of the same index, at `posO k + shadowO (ℓ k)`), and the two minus tiles at the start
(`m0Piece`, and the minus tile of index one). For an almost palindrome of length `n` the stacked string is this union for
`m = n - 1`, plus the last plus tile and a final minus tile (`stacked_decomposition`, in `StackGeneral`). -/

namespace FLatticePaper.Tiles

/-- The plus step of a new letter (`zeroOneHorizontalStep`, `zeroOneVerticalStep`). -/
def plusStepO : Orientation → Letter → Site
  | .horizontal, l => zeroOneHorizontalStep l
  | .vertical, l => zeroOneVerticalStep l

/-- The offset of the shadow of a tile (the minus tile of the same index, after the palindrome identity). -/
def shadowO : Orientation → Letter → Site
  | .horizontal, .p => ((1 : ℤ), (-2 : ℤ))
  | .horizontal, .q => ((2 : ℤ), (-2 : ℤ))
  | .vertical, .p => ((2 : ℤ), (1 : ℤ))
  | .vertical, .q => ((1 : ℤ), (1 : ℤ))

/-- The enlargement flag of the plus tile at index `k` (horizontal only): a one-tile following a one-tile. -/
def flagO (o : Orientation) (ℓ : ℕ → Letter) : ℕ → Bool
  | 0 => false
  | k + 1 => decide (o = Orientation.horizontal) && decide (ℓ k = Letter.q) && decide (ℓ (k + 1) = Letter.q)

/-- The plus positions: `posO k` is the lower-left corner of the `k`-th plus tile. -/
def posO (o : Orientation) (ℓ : ℕ → Letter) : ℕ → Site
  | 0 => (0, 0)
  | k + 1 => posO o ℓ k + plusStepO o (ℓ (k + 1))

/-- One tile placed at a site. -/
def pieceAt (l : Letter) (e : Bool) (p : Site) : Finset Site :=
  ((tileSitesOf l e).map (fun c => c + p)).toFinset

/-- The first minus tile: its letter is the last letter of the word, which is `p` horizontally and `q` vertically. -/
def m0Piece : Orientation → Finset Site
  | .horizontal => pieceAt .p false (1, -2)
  | .vertical => pieceAt .q false (1, 1)

/-- The local union of the first `m` letters. -/
def lamO (o : Orientation) (ℓ : ℕ → Letter) (m : ℕ) : Finset Site :=
  ((Finset.range m).biUnion fun k => pieceAt (ℓ k) (flagO o ℓ k) (posO o ℓ k))
    ∪ ((Finset.Ico 2 m).biUnion fun k => pieceAt (ℓ k) (flagO o ℓ k) (posO o ℓ k + shadowO o (ℓ k)))
    ∪ (if 1 ≤ m then m0Piece o else ∅)
    ∪ (if 2 ≤ m then pieceAt (ℓ 1) false (posO o ℓ 1 + shadowO o (ℓ 1)) else ∅)

theorem mem_pieceAt {l : Letter} {e : Bool} {p c : Site} :
    c ∈ pieceAt l e p ↔ ∃ t ∈ tileSitesOf l e, t + p = c := by
  simp [pieceAt, List.mem_toFinset, List.mem_map]

/-- Tile bounds: every tile lies in `[-1,1] × [-1,2]`, and a vertical tile (no enlargement) in `[0,1] × [0,2]`. -/
theorem tile_bound (l : Letter) (e : Bool) :
    ∀ t ∈ tileSitesOf l e, -1 ≤ t.1 ∧ t.1 ≤ 1 ∧ -1 ≤ t.2 ∧ t.2 ≤ 2 := by
  cases l <;> cases e <;> decide

theorem tile_bound_plain (l : Letter) : ∀ t ∈ tileSitesOf l false, 0 ≤ t.1 ∧ t.1 ≤ 1 ∧ 0 ≤ t.2 ∧ t.2 ≤ 2 := by
  cases l <;> decide

/-- The lower-left corner of the first plus tile is the origin. -/
theorem posO_zero (o : Orientation) (ℓ : ℕ → Letter) : posO o ℓ 0 = (0, 0) := rfl

theorem posO_succ (o : Orientation) (ℓ : ℕ → Letter) (k : ℕ) :
    posO o ℓ (k + 1) = posO o ℓ k + plusStepO o (ℓ (k + 1)) := rfl

/-- The plus step never decreases the second coordinate. -/
theorem plusStep_snd_nonneg (o : Orientation) (l : Letter) : 0 ≤ (plusStepO o l).2 := by
  cases o <;> cases l <;> decide

/-- The horizontal plus step never decreases the first coordinate. -/
theorem plusStep_fst_nonneg_h (l : Letter) : 0 ≤ (plusStepO .horizontal l).1 := by
  cases l <;> decide

/-- The vertical plus step never increases the first coordinate. -/
theorem plusStep_fst_nonpos_v (l : Letter) : (plusStepO .vertical l).1 ≤ 0 := by
  cases l <;> decide

/-- Plus positions do not decrease in the second coordinate. -/
theorem posO_snd_mono (o : Orientation) (ℓ : ℕ → Letter) {k j : ℕ} (h : k ≤ j) :
    (posO o ℓ k).2 ≤ (posO o ℓ j).2 := by
  induction j, h using Nat.le_induction with
  | base => exact le_rfl
  | succ j hj ih =>
    rw [posO_succ]
    have := plusStep_snd_nonneg o (ℓ (j + 1))
    simp only [Prod.snd_add]
    omega

/-- Horizontal plus positions do not decrease in the first coordinate. -/
theorem posO_fst_mono_h (ℓ : ℕ → Letter) {k j : ℕ} (h : k ≤ j) :
    (posO .horizontal ℓ k).1 ≤ (posO .horizontal ℓ j).1 := by
  induction j, h using Nat.le_induction with
  | base => exact le_rfl
  | succ j hj ih =>
    rw [posO_succ]
    have := plusStep_fst_nonneg_h (ℓ (j + 1))
    simp only [Prod.fst_add]
    omega

/-- Vertical plus positions do not increase in the first coordinate. -/
theorem posO_fst_anti_v (ℓ : ℕ → Letter) {k j : ℕ} (h : k ≤ j) :
    (posO .vertical ℓ j).1 ≤ (posO .vertical ℓ k).1 := by
  induction j, h using Nat.le_induction with
  | base => exact le_rfl
  | succ j hj ih =>
    rw [posO_succ]
    have := plusStep_fst_nonpos_v (ℓ (j + 1))
    simp only [Prod.fst_add]
    omega

/-- Horizontal positions are nonnegative. -/
theorem posO_fst_nonneg_h (ℓ : ℕ → Letter) (k : ℕ) : 0 ≤ (posO .horizontal ℓ k).1 := by
  have := posO_fst_mono_h ℓ (Nat.zero_le k)
  rw [posO_zero] at this
  simpa using this

/-- Vertical positions are at most zero in the first coordinate. -/
theorem posO_fst_nonpos_v (ℓ : ℕ → Letter) (k : ℕ) : (posO .vertical ℓ k).1 ≤ 0 := by
  have := posO_fst_anti_v ℓ (Nat.zero_le k)
  rw [posO_zero] at this
  simpa using this

/-- Second coordinates are nonnegative. -/
theorem posO_snd_nonneg (o : Orientation) (ℓ : ℕ → Letter) (k : ℕ) : 0 ≤ (posO o ℓ k).2 := by
  have := posO_snd_mono o ℓ (Nat.zero_le k)
  rw [posO_zero] at this
  simpa using this

/-- Adding the `(m+1)`-st tile to the union of the first `m` letters, for `m ≥ 2`. -/
theorem lamO_succ (o : Orientation) (ℓ : ℕ → Letter) {m : ℕ} (hm : 2 ≤ m) :
    lamO o ℓ (m + 1) = lamO o ℓ m ∪ pieceAt (ℓ m) (flagO o ℓ m) (posO o ℓ m)
      ∪ pieceAt (ℓ m) (flagO o ℓ m) (posO o ℓ m + shadowO o (ℓ m)) := by
  unfold lamO
  have hr : Finset.range (m + 1) = insert m (Finset.range m) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert]
    omega
  have hi : Finset.Ico 2 (m + 1) = insert m (Finset.Ico 2 m) := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_insert]
    omega
  rw [hr, hi, Finset.biUnion_insert, Finset.biUnion_insert]
  simp only [show 1 ≤ m + 1 from by omega, show 1 ≤ m from by omega, show 2 ≤ m + 1 from by omega,
    show 2 ≤ m from hm, if_true, Finset.union_assoc]
  ext x
  simp only [Finset.mem_union]
  tauto

end FLatticePaper.Tiles
