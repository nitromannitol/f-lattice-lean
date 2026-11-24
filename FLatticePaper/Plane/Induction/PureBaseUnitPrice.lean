import FLatticePaper.Plane.Induction.PureBasePrice

/-! The unit price increments of the pure word `3^k`, from explicit representatives.

`priceStep k z e = P(z+e) − P(z)` for `P z = F z − F(z − (1,−1)) − z.2` (`price_threes`). For a unit step `e` and a site `z`,
`strong_rep_unit` gives a raw representative `y` of `z` with `y + e` raw. The second site `z − (1,−1)` has its own representative
`y' = pairY y a b = y − (1,−1) − combine a b`, with `a, b` from a small candidate list (`pair_cover_*`). The increment is then the
difference of two staircase increments plus `b · (d e₂ − e₁)` (`price_pair_increment`), and each candidate gives a bound in `[−1, 1]`
(`pair_bound_*`). -/

namespace FLatticePaper.Induction

open Farey Construction

/-- The corner indicator of the staircase value. -/
def cornerInd (d : ℤ) (q : Site) : ℤ := if BaseMask.StairEvenCorner d q then 1 else 0

/-- The triangular identity `C(n+1) = C(n) + n`. -/
theorem tri_succ (n : ℤ) : (n + 1) * n / 2 = n * (n - 1) / 2 + n := by
  have h : (n + 1) * n = n * (n - 1) + n * 2 := by ring
  rw [h, Int.add_mul_ediv_right _ _ two_ne_zero]

/-- The row increment `+y`. -/
theorem stairEvenValue_up (d x y : ℤ) :
    BaseMask.stairEvenValue d (x, y + 1) - BaseMask.stairEvenValue d (x, y) =
      -y + (cornerInd d (x, y + 1) - cornerInd d (x, y)) := by
  unfold BaseMask.stairEvenValue cornerInd
  have h := tri_succ y
  simp only [add_sub_cancel_right] at h ⊢
  linarith

/-- The row increment `−y`. -/
theorem stairEvenValue_down (d x y : ℤ) :
    BaseMask.stairEvenValue d (x, y - 1) - BaseMask.stairEvenValue d (x, y) =
      (y - 1) + (cornerInd d (x, y - 1) - cornerInd d (x, y)) := by
  unfold BaseMask.stairEvenValue cornerInd
  have h := tri_succ (y - 1)
  have h2 : (y - 1 + 1) = y := by ring
  simp only [h2] at h ⊢
  linarith

/-- The `min` difference of the column increment `+x`. -/
theorem min_right_diff (x : ℤ) : min x 0 - min (x - 1) 0 = if x ≤ 0 then 1 else 0 := by
  by_cases hx : x ≤ 0
  · rw [if_pos hx, min_eq_left hx, min_eq_left (by omega : x - 1 ≤ 0)]
    ring
  · rw [if_neg hx, min_eq_right (by omega : 0 ≤ x), min_eq_right (by omega : 0 ≤ x - 1)]
    ring

/-- The `min` difference of the column increment `−x`. -/
theorem min_left_diff (x : ℤ) : min (x - 1 - 1) 0 - min (x - 1) 0 = -(if x ≤ 1 then 1 else 0) := by
  by_cases hx : x ≤ 1
  · rw [if_pos hx, min_eq_left (by omega : x - 1 - 1 ≤ 0), min_eq_left (by omega : x - 1 ≤ 0)]
    ring
  · rw [if_neg hx, min_eq_right (by omega : 0 ≤ x - 1 - 1), min_eq_right (by omega : 0 ≤ x - 1)]
    ring

/-- The column increment `+x`. -/
theorem stairEvenValue_right (d x y : ℤ) :
    BaseMask.stairEvenValue d (x + 1, y) - BaseMask.stairEvenValue d (x, y) =
      (if x ≤ 0 then 1 else 0) + (cornerInd d (x + 1, y) - cornerInd d (x, y)) := by
  unfold BaseMask.stairEvenValue cornerInd
  simp only [add_sub_cancel_right]
  have h := min_right_diff x
  linarith

/-- The column increment `−x`. -/
theorem stairEvenValue_left (d x y : ℤ) :
    BaseMask.stairEvenValue d (x - 1, y) - BaseMask.stairEvenValue d (x, y) =
      -(if x ≤ 1 then 1 else 0) + (cornerInd d (x - 1, y) - cornerInd d (x, y)) := by
  unfold BaseMask.stairEvenValue cornerInd
  have h := min_left_diff x
  linarith

/-- The second representative `y − (1,−1) − combine a b`, in coordinates. -/
def pairY (d x w a b : ℤ) : ℤ × ℤ :=
  (x - 1 - (a * d + b * (1 - d)), w + 1 - (a + b * (1 + d)))

/-- The unit price increment: `P(z+e) − P(z)` with `P z = F z − F(z − (1,−1)) − z.2`. -/
noncomputable def priceStep (k : ℕ) (z e : Site) : ℤ :=
  (reciprocalField k (z + e) - reciprocalField k (z + e - (1, -1)) - (z + e).2) -
    (reciprocalField k z - reciprocalField k (z - (1, -1)) - z.2)

theorem raw_mem_site (d : ℤ) (p : Site) :
    p ∈ (BaseMask.stairEven.raw d).sites ↔ RawMem d p.1 p.2 := by
  obtain ⟨x, y⟩ := p
  exact raw_mem_iff d x y

theorem pairY_eq (d : ℤ) (hodd : d % 2 = 1) (y : Site) (a b : ℤ) :
    pairY d y.1 y.2 a b = y - (1, -1) - (Fraction.mk 1 d).modifiedDeck.combine a b := by
  rw [combine_eq d hodd]
  ext <;> simp [pairY]

theorem combine_add_pair (d : ℤ) (hodd : d % 2 = 1) (i j a b : ℤ) :
    (Fraction.mk 1 d).modifiedDeck.combine (i + a) (j + b) =
      (Fraction.mk 1 d).modifiedDeck.combine i j + (Fraction.mk 1 d).modifiedDeck.combine a b := by
  rw [combine_eq d hodd, combine_eq d hodd, combine_eq d hodd]
  refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring

set_option maxHeartbeats 400000 in
/-- The pair identity: the price increment at `z = y + combine i j` is the difference of two staircase increments (at `y` and at
`y' = y − (1,−1) − combine a b`, whose index pair is `(i + a, j + b)`) plus `b · (d e₂ − e₁)` and `−e₂`. -/
theorem price_pair_increment (k : ℕ) {y e y' z : Site} {i j a b : ℤ}
    (hy : y ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites)
    (hye : y + e ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites)
    (hz : z = y + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j)
    (hy' : y' = y - (1, -1) - (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine a b)
    (hy'0 : y' ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites)
    (hy'e : y' + e ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites) :
    priceStep k z e =
      (BaseMask.stairEvenValue (2 * (k : ℤ) + 3) (y + e) - BaseMask.stairEvenValue (2 * (k : ℤ) + 3) y) -
        (BaseMask.stairEvenValue (2 * (k : ℤ) + 3) (y' + e) - BaseMask.stairEvenValue (2 * (k : ℤ) + 3) y') +
        b * ((2 * (k : ℤ) + 3) * e.2 - e.1) - e.2 := by
  have hodd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  have h1 := reciprocal_native_step k hy hye hz
  have hz' : z - (1, -1) =
      y' + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine (i + a) (j + b) := by
    rw [hy', hz, combine_add_pair _ hodd]
    abel
  have h2 := reciprocal_native_step k hy'0 hy'e hz'
  have hze : z + e - (1, -1) = z - (1, -1) + e := by abel
  unfold priceStep
  rw [hze, Prod.snd_add]
  linear_combination h1 - h2

/-! ### Candidate covers -/

set_option maxHeartbeats 400000 in
theorem pair_cover_right (d x w : ℤ) (hodd : d % 2 = 1)
    (hy : RawMem d x w) (hye : RawMem d (x + 1) w) :
    ∃ a b : ℤ, (a = -1 ∧ b = 0 ∨ a = 0 ∧ b = 0 ∨ a = 0 ∧ b = 1) ∧
      RawMem d (pairY d x w a b).1 (pairY d x w a b).2 ∧
      RawMem d ((pairY d x w a b).1 + 1) (pairY d x w a b).2 := by
  have key : (RawMem d (pairY d x w (-1) 0).1 (pairY d x w (-1) 0).2 ∧
        RawMem d ((pairY d x w (-1) 0).1 + 1) (pairY d x w (-1) 0).2) ∨
      (RawMem d (pairY d x w 0 0).1 (pairY d x w 0 0).2 ∧
        RawMem d ((pairY d x w 0 0).1 + 1) (pairY d x w 0 0).2) ∨
      (RawMem d (pairY d x w 0 1).1 (pairY d x w 0 1).2 ∧
        RawMem d ((pairY d x w 0 1).1 + 1) (pairY d x w 0 1).2) := by
    simp only [pairY, RawMem] at hy hye ⊢
    obtain ⟨hx, hw, hc⟩ := hy
    obtain ⟨hx', hw', hc'⟩ := hye
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases hc' with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega
  rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨-1, 0, Or.inl ⟨rfl, rfl⟩, h1, h2⟩
  · exact ⟨0, 0, Or.inr (Or.inl ⟨rfl, rfl⟩), h1, h2⟩
  · exact ⟨0, 1, Or.inr (Or.inr ⟨rfl, rfl⟩), h1, h2⟩

set_option maxHeartbeats 400000 in
theorem pair_cover_left (d x w : ℤ) (hodd : d % 2 = 1)
    (hy : RawMem d x w) (hye : RawMem d (x - 1) w) :
    ∃ a b : ℤ, (a = -1 ∧ b = 0 ∨ a = 0 ∧ b = 0 ∨ a = 0 ∧ b = 1) ∧
      RawMem d (pairY d x w a b).1 (pairY d x w a b).2 ∧
      RawMem d ((pairY d x w a b).1 - 1) (pairY d x w a b).2 := by
  have key : (RawMem d (pairY d x w (-1) 0).1 (pairY d x w (-1) 0).2 ∧
        RawMem d ((pairY d x w (-1) 0).1 - 1) (pairY d x w (-1) 0).2) ∨
      (RawMem d (pairY d x w 0 0).1 (pairY d x w 0 0).2 ∧
        RawMem d ((pairY d x w 0 0).1 - 1) (pairY d x w 0 0).2) ∨
      (RawMem d (pairY d x w 0 1).1 (pairY d x w 0 1).2 ∧
        RawMem d ((pairY d x w 0 1).1 - 1) (pairY d x w 0 1).2) := by
    simp only [pairY, RawMem] at hy hye ⊢
    obtain ⟨hx, hw, hc⟩ := hy
    obtain ⟨hx', hw', hc'⟩ := hye
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases hc' with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega
  rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨-1, 0, Or.inl ⟨rfl, rfl⟩, h1, h2⟩
  · exact ⟨0, 0, Or.inr (Or.inl ⟨rfl, rfl⟩), h1, h2⟩
  · exact ⟨0, 1, Or.inr (Or.inr ⟨rfl, rfl⟩), h1, h2⟩

set_option maxHeartbeats 400000 in
theorem pair_cover_up (d x w : ℤ) (hd : 3 ≤ d) (hodd : d % 2 = 1)
    (hy : RawMem d x w) (hye : RawMem d x (w + 1)) :
    ∃ a b : ℤ, (a = -1 ∧ b = 0 ∨ a = -1 ∧ b = 1 ∨ a = 0 ∧ b = 0 ∨ a = 0 ∧ b = 1) ∧
      RawMem d (pairY d x w a b).1 (pairY d x w a b).2 ∧
      RawMem d (pairY d x w a b).1 ((pairY d x w a b).2 + 1) := by
  have key : (RawMem d (pairY d x w (-1) 0).1 (pairY d x w (-1) 0).2 ∧
        RawMem d (pairY d x w (-1) 0).1 ((pairY d x w (-1) 0).2 + 1)) ∨
      (RawMem d (pairY d x w (-1) 1).1 (pairY d x w (-1) 1).2 ∧
        RawMem d (pairY d x w (-1) 1).1 ((pairY d x w (-1) 1).2 + 1)) ∨
      (RawMem d (pairY d x w 0 0).1 (pairY d x w 0 0).2 ∧
        RawMem d (pairY d x w 0 0).1 ((pairY d x w 0 0).2 + 1)) ∨
      (RawMem d (pairY d x w 0 1).1 (pairY d x w 0 1).2 ∧
        RawMem d (pairY d x w 0 1).1 ((pairY d x w 0 1).2 + 1)) := by
    simp only [pairY, RawMem] at hy hye ⊢
    obtain ⟨hx, hw, hc⟩ := hy
    obtain ⟨hx', hw', hc'⟩ := hye
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases hc' with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega
  rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨-1, 0, Or.inl ⟨rfl, rfl⟩, h1, h2⟩
  · exact ⟨-1, 1, Or.inr (Or.inl ⟨rfl, rfl⟩), h1, h2⟩
  · exact ⟨0, 0, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)), h1, h2⟩
  · exact ⟨0, 1, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)), h1, h2⟩

set_option maxHeartbeats 400000 in
theorem pair_cover_down (d x w : ℤ) (hd : 3 ≤ d) (hodd : d % 2 = 1)
    (hy : RawMem d x w) (hye : RawMem d x (w - 1)) :
    ∃ a b : ℤ, (a = -1 ∧ b = 0 ∨ a = -1 ∧ b = 1 ∨ a = 0 ∧ b = 0 ∨ a = 0 ∧ b = 1) ∧
      RawMem d (pairY d x w a b).1 (pairY d x w a b).2 ∧
      RawMem d (pairY d x w a b).1 ((pairY d x w a b).2 - 1) := by
  have key : (RawMem d (pairY d x w (-1) 0).1 (pairY d x w (-1) 0).2 ∧
        RawMem d (pairY d x w (-1) 0).1 ((pairY d x w (-1) 0).2 - 1)) ∨
      (RawMem d (pairY d x w (-1) 1).1 (pairY d x w (-1) 1).2 ∧
        RawMem d (pairY d x w (-1) 1).1 ((pairY d x w (-1) 1).2 - 1)) ∨
      (RawMem d (pairY d x w 0 0).1 (pairY d x w 0 0).2 ∧
        RawMem d (pairY d x w 0 0).1 ((pairY d x w 0 0).2 - 1)) ∨
      (RawMem d (pairY d x w 0 1).1 (pairY d x w 0 1).2 ∧
        RawMem d (pairY d x w 0 1).1 ((pairY d x w 0 1).2 - 1)) := by
    simp only [pairY, RawMem] at hy hye ⊢
    obtain ⟨hx, hw, hc⟩ := hy
    obtain ⟨hx', hw', hc'⟩ := hye
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases hc' with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega
  rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨-1, 0, Or.inl ⟨rfl, rfl⟩, h1, h2⟩
  · exact ⟨-1, 1, Or.inr (Or.inl ⟨rfl, rfl⟩), h1, h2⟩
  · exact ⟨0, 0, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)), h1, h2⟩
  · exact ⟨0, 1, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)), h1, h2⟩

/-! ### The four bounds, one per unit step -/

set_option maxHeartbeats 400000 in
theorem pair_bound_right (d x w a b : ℤ)
    (hy : RawMem d x w) (hye : RawMem d (x + 1) w)
    (hab : a = -1 ∧ b = 0 ∨ a = 0 ∧ b = 0 ∨ a = 0 ∧ b = 1)
    (hp : RawMem d (pairY d x w a b).1 (pairY d x w a b).2)
    (hpe : RawMem d ((pairY d x w a b).1 + 1) (pairY d x w a b).2) :
    -1 ≤ (BaseMask.stairEvenValue d ((x, w) + (1, 0)) - BaseMask.stairEvenValue d (x, w)) -
        (BaseMask.stairEvenValue d (pairY d x w a b + (1, 0)) - BaseMask.stairEvenValue d (pairY d x w a b)) +
        b * (d * (1, 0).2 - (1, 0).1) - (1, 0).2 ∧
      (BaseMask.stairEvenValue d ((x, w) + (1, 0)) - BaseMask.stairEvenValue d (x, w)) -
        (BaseMask.stairEvenValue d (pairY d x w a b + (1, 0)) - BaseMask.stairEvenValue d (pairY d x w a b)) +
        b * (d * (1, 0).2 - (1, 0).1) - (1, 0).2 ≤ 1 := by
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [pairY, RawMem, Prod.mk_add_mk, add_zero] at hy hye hp hpe ⊢ <;>
    rw [stairEvenValue_right, stairEvenValue_right] <;>
    simp only [cornerInd, BaseMask.StairEvenCorner] <;>
    constructor <;> split_ifs <;> omega

set_option maxHeartbeats 400000 in
theorem pair_bound_left (d x w a b : ℤ)
    (hy : RawMem d x w) (hye : RawMem d (x - 1) w)
    (hab : a = -1 ∧ b = 0 ∨ a = 0 ∧ b = 0 ∨ a = 0 ∧ b = 1)
    (hp : RawMem d (pairY d x w a b).1 (pairY d x w a b).2)
    (hpe : RawMem d ((pairY d x w a b).1 - 1) (pairY d x w a b).2) :
    -1 ≤ (BaseMask.stairEvenValue d ((x, w) + (-1, 0)) - BaseMask.stairEvenValue d (x, w)) -
        (BaseMask.stairEvenValue d (pairY d x w a b + (-1, 0)) - BaseMask.stairEvenValue d (pairY d x w a b)) +
        b * (d * (-1, 0).2 - (-1, 0).1) - (-1, 0).2 ∧
      (BaseMask.stairEvenValue d ((x, w) + (-1, 0)) - BaseMask.stairEvenValue d (x, w)) -
        (BaseMask.stairEvenValue d (pairY d x w a b + (-1, 0)) - BaseMask.stairEvenValue d (pairY d x w a b)) +
        b * (d * (-1, 0).2 - (-1, 0).1) - (-1, 0).2 ≤ 1 := by
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [pairY, RawMem, Prod.mk_add_mk, add_zero, ← sub_eq_add_neg] at hy hye hp hpe ⊢ <;>
    rw [stairEvenValue_left, stairEvenValue_left] <;>
    simp only [cornerInd, BaseMask.StairEvenCorner] <;>
    constructor <;> split_ifs <;> omega

set_option maxHeartbeats 400000 in
theorem pair_bound_up (d x w a b : ℤ)
    (hy : RawMem d x w) (hye : RawMem d x (w + 1))
    (hab : a = -1 ∧ b = 0 ∨ a = -1 ∧ b = 1 ∨ a = 0 ∧ b = 0 ∨ a = 0 ∧ b = 1)
    (hp : RawMem d (pairY d x w a b).1 (pairY d x w a b).2)
    (hpe : RawMem d (pairY d x w a b).1 ((pairY d x w a b).2 + 1)) :
    -1 ≤ (BaseMask.stairEvenValue d ((x, w) + (0, 1)) - BaseMask.stairEvenValue d (x, w)) -
        (BaseMask.stairEvenValue d (pairY d x w a b + (0, 1)) - BaseMask.stairEvenValue d (pairY d x w a b)) +
        b * (d * (0, 1).2 - (0, 1).1) - (0, 1).2 ∧
      (BaseMask.stairEvenValue d ((x, w) + (0, 1)) - BaseMask.stairEvenValue d (x, w)) -
        (BaseMask.stairEvenValue d (pairY d x w a b + (0, 1)) - BaseMask.stairEvenValue d (pairY d x w a b)) +
        b * (d * (0, 1).2 - (0, 1).1) - (0, 1).2 ≤ 1 := by
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [pairY, RawMem, Prod.mk_add_mk, add_zero] at hy hye hp hpe ⊢ <;>
    rw [stairEvenValue_up, stairEvenValue_up] <;>
    simp only [cornerInd, BaseMask.StairEvenCorner] <;>
    constructor <;> split_ifs <;> omega

set_option maxHeartbeats 400000 in
theorem pair_bound_down (d x w a b : ℤ)
    (hy : RawMem d x w) (hye : RawMem d x (w - 1))
    (hab : a = -1 ∧ b = 0 ∨ a = -1 ∧ b = 1 ∨ a = 0 ∧ b = 0 ∨ a = 0 ∧ b = 1)
    (hp : RawMem d (pairY d x w a b).1 (pairY d x w a b).2)
    (hpe : RawMem d (pairY d x w a b).1 ((pairY d x w a b).2 - 1)) :
    -1 ≤ (BaseMask.stairEvenValue d ((x, w) + (0, -1)) - BaseMask.stairEvenValue d (x, w)) -
        (BaseMask.stairEvenValue d (pairY d x w a b + (0, -1)) - BaseMask.stairEvenValue d (pairY d x w a b)) +
        b * (d * (0, -1).2 - (0, -1).1) - (0, -1).2 ∧
      (BaseMask.stairEvenValue d ((x, w) + (0, -1)) - BaseMask.stairEvenValue d (x, w)) -
        (BaseMask.stairEvenValue d (pairY d x w a b + (0, -1)) - BaseMask.stairEvenValue d (pairY d x w a b)) +
        b * (d * (0, -1).2 - (0, -1).1) - (0, -1).2 ≤ 1 := by
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [pairY, RawMem, Prod.mk_add_mk, add_zero, ← sub_eq_add_neg] at hy hye hp hpe ⊢ <;>
    rw [stairEvenValue_down, stairEvenValue_down] <;>
    simp only [cornerInd, BaseMask.StairEvenCorner] <;>
    constructor <;> split_ifs <;> omega

/-! ### The unit price increment at each unit step -/

set_option maxHeartbeats 400000 in
theorem priceStep_unit_right (k : ℕ) (z : Site) :
    -1 ≤ priceStep k z (1, 0) ∧ priceStep k z (1, 0) ≤ 1 := by
  have hodd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  obtain ⟨⟨y1, y2⟩, hyr, hyer, i, j, hz⟩ := strong_rep_unit k z (1, 0) (Or.inl rfl)
  have hyer' : RawMem (2 * (k : ℤ) + 3) (y1 + 1) y2 := by simpa using hyer
  obtain ⟨a, b, hab, hp, hpe⟩ := pair_cover_right (2 * (k : ℤ) + 3) y1 y2 hodd hyr hyer'
  have key := price_pair_increment k (e := (1, 0))
    ((raw_mem_site (2 * (k : ℤ) + 3) (y1, y2)).mpr hyr)
    ((raw_mem_site (2 * (k : ℤ) + 3) ((y1, y2) + (1, 0))).mpr (by simpa using hyer'))
    hz (pairY_eq _ hodd (y1, y2) a b)
    ((raw_mem_site (2 * (k : ℤ) + 3) (pairY (2 * (k : ℤ) + 3) y1 y2 a b)).mpr hp)
    ((raw_mem_site (2 * (k : ℤ) + 3) (pairY (2 * (k : ℤ) + 3) y1 y2 a b + (1, 0))).mpr
      (by simpa using hpe))
  rw [key]
  exact pair_bound_right (2 * (k : ℤ) + 3) y1 y2 a b hyr hyer' hab hp hpe

set_option maxHeartbeats 400000 in
theorem priceStep_unit_left (k : ℕ) (z : Site) :
    -1 ≤ priceStep k z (-1, 0) ∧ priceStep k z (-1, 0) ≤ 1 := by
  have hodd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  obtain ⟨⟨y1, y2⟩, hyr, hyer, i, j, hz⟩ := strong_rep_unit k z (-1, 0) (Or.inr (Or.inl rfl))
  have hyer' : RawMem (2 * (k : ℤ) + 3) (y1 - 1) y2 := by simpa [sub_eq_add_neg] using hyer
  obtain ⟨a, b, hab, hp, hpe⟩ := pair_cover_left (2 * (k : ℤ) + 3) y1 y2 hodd hyr hyer'
  have key := price_pair_increment k (e := (-1, 0))
    ((raw_mem_site (2 * (k : ℤ) + 3) (y1, y2)).mpr hyr)
    ((raw_mem_site (2 * (k : ℤ) + 3) ((y1, y2) + (-1, 0))).mpr
      (by simpa [sub_eq_add_neg] using hyer'))
    hz (pairY_eq _ hodd (y1, y2) a b)
    ((raw_mem_site (2 * (k : ℤ) + 3) (pairY (2 * (k : ℤ) + 3) y1 y2 a b)).mpr hp)
    ((raw_mem_site (2 * (k : ℤ) + 3) (pairY (2 * (k : ℤ) + 3) y1 y2 a b + (-1, 0))).mpr
      (by simpa [sub_eq_add_neg] using hpe))
  rw [key]
  exact pair_bound_left (2 * (k : ℤ) + 3) y1 y2 a b hyr hyer' hab hp hpe

set_option maxHeartbeats 400000 in
theorem priceStep_unit_up (k : ℕ) (z : Site) :
    -1 ≤ priceStep k z (0, 1) ∧ priceStep k z (0, 1) ≤ 1 := by
  have hodd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  have hd : (3 : ℤ) ≤ 2 * (k : ℤ) + 3 := by omega
  obtain ⟨⟨y1, y2⟩, hyr, hyer, i, j, hz⟩ := strong_rep_unit k z (0, 1) (Or.inr (Or.inr (Or.inl rfl)))
  have hyer' : RawMem (2 * (k : ℤ) + 3) y1 (y2 + 1) := by simpa using hyer
  obtain ⟨a, b, hab, hp, hpe⟩ := pair_cover_up (2 * (k : ℤ) + 3) y1 y2 hd hodd hyr hyer'
  have key := price_pair_increment k (e := (0, 1))
    ((raw_mem_site (2 * (k : ℤ) + 3) (y1, y2)).mpr hyr)
    ((raw_mem_site (2 * (k : ℤ) + 3) ((y1, y2) + (0, 1))).mpr (by simpa using hyer'))
    hz (pairY_eq _ hodd (y1, y2) a b)
    ((raw_mem_site (2 * (k : ℤ) + 3) (pairY (2 * (k : ℤ) + 3) y1 y2 a b)).mpr hp)
    ((raw_mem_site (2 * (k : ℤ) + 3) (pairY (2 * (k : ℤ) + 3) y1 y2 a b + (0, 1))).mpr
      (by simpa using hpe))
  rw [key]
  exact pair_bound_up (2 * (k : ℤ) + 3) y1 y2 a b hyr hyer' hab hp hpe

set_option maxHeartbeats 400000 in
theorem priceStep_unit_down (k : ℕ) (z : Site) :
    -1 ≤ priceStep k z (0, -1) ∧ priceStep k z (0, -1) ≤ 1 := by
  have hodd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  have hd : (3 : ℤ) ≤ 2 * (k : ℤ) + 3 := by omega
  obtain ⟨⟨y1, y2⟩, hyr, hyer, i, j, hz⟩ := strong_rep_unit k z (0, -1) (Or.inr (Or.inr (Or.inr rfl)))
  have hyer' : RawMem (2 * (k : ℤ) + 3) y1 (y2 - 1) := by simpa [sub_eq_add_neg] using hyer
  obtain ⟨a, b, hab, hp, hpe⟩ := pair_cover_down (2 * (k : ℤ) + 3) y1 y2 hd hodd hyr hyer'
  have key := price_pair_increment k (e := (0, -1))
    ((raw_mem_site (2 * (k : ℤ) + 3) (y1, y2)).mpr hyr)
    ((raw_mem_site (2 * (k : ℤ) + 3) ((y1, y2) + (0, -1))).mpr
      (by simpa [sub_eq_add_neg] using hyer'))
    hz (pairY_eq _ hodd (y1, y2) a b)
    ((raw_mem_site (2 * (k : ℤ) + 3) (pairY (2 * (k : ℤ) + 3) y1 y2 a b)).mpr hp)
    ((raw_mem_site (2 * (k : ℤ) + 3) (pairY (2 * (k : ℤ) + 3) y1 y2 a b + (0, -1))).mpr
      (by simpa [sub_eq_add_neg] using hpe))
  rw [key]
  exact pair_bound_down (2 * (k : ℤ) + 3) y1 y2 a b hyr hyer' hab hp hpe

/-- The unit price increment along any of the four unit steps. -/
theorem priceStep_unit (k : ℕ) (z e : Site)
    (he : e = (1, 0) ∨ e = (-1, 0) ∨ e = (0, 1) ∨ e = (0, -1)) :
    -1 ≤ priceStep k z e ∧ priceStep k z e ≤ 1 := by
  rcases he with rfl | rfl | rfl | rfl
  · exact priceStep_unit_right k z
  · exact priceStep_unit_left k z
  · exact priceStep_unit_up k z
  · exact priceStep_unit_down k z

/-! ### `HasUnitPrice` at the pure word -/

/-- Every edge of the unit lattice joins a centre to one of its four unit neighbours. -/
theorem edge_unit_step (center input : Site) (hE : FLatticePaper.Edge input center) :
    ∃ e : Site, (e = (1, 0) ∨ e = (-1, 0) ∨ e = (0, 1) ∨ e = (0, -1)) ∧ input = center + e := by
  unfold FLatticePaper.Edge at hE
  by_cases hc : FLatticePaper.EvenSite center
  · rcases hE with h | h
    · refine ⟨(-1, 0), Or.inr (Or.inl rfl), ?_⟩
      rw [h]
      ext <;> simp [FLatticePaper.incomingNeg, hc, sub_eq_add_neg]
    · refine ⟨(1, 0), Or.inl rfl, ?_⟩
      rw [h]
      ext <;> simp [FLatticePaper.incomingPos, hc]
  · rcases hE with h | h
    · refine ⟨(0, -1), Or.inr (Or.inr (Or.inr rfl)), ?_⟩
      rw [h]
      ext <;> simp [FLatticePaper.incomingNeg, hc, sub_eq_add_neg]
    · refine ⟨(0, 1), Or.inr (Or.inr (Or.inl rfl)), ?_⟩
      rw [h]
      ext <;> simp [FLatticePaper.incomingPos, hc]

/-- **`F1_unitPrice` at the pure word `3^k`:** the price has unit increments on every edge of the field `reciprocalField k`. -/
theorem hasUnitPrice_threes (k : ℕ) :
    HasUnitPrice (frameAt (List.replicate k Digit.three)) (standardField (List.replicate k Digit.three)) := by
  intro center input hE
  obtain ⟨e, he, rfl⟩ := edge_unit_step center input hE
  have h := priceStep_unit k center e he
  rw [standardField_threes]
  unfold priceIncrement
  simp only [price_threes]
  exact h

end FLatticePaper.Induction
