import FLatticePaper.Tiles.TileCompatInputs
import FLatticePaper.Tiles.JointGlue
import FLatticePaper.Tiles.StandardBaseBridge
import FLatticePaper.Construction.BaseCaseRecurrence

/-! # Compatibility of the swapped base pairs, the 9-point blocks (Case 1, base cases)

Two entries of a decomposition that are copies of one base odometer `O` at offsets `o1`, `o2` with affine factors `a1`, `a2`
are compatible (`PairCompat`) as soon as the difference `V(x - o1) - V(x - o2) + (a1 - a2) · x` is constant on the points where
both translates of the domain contain `x`. This is the template. The first instance is the ladder family (`u1 = 3^k`) at the
word `3^k 2`, where the overlap is the 3×3 block `x = (2k+2+a, 2k+3+b)`, `a, b ∈ {0,1,2}`, with constant `2k²+3k`. -/

namespace FLatticePaper.Tiles.SwapBaseBlock

open FLatticePaper.Tiles FLatticePaper.Tiles.JointFamily FLatticePaper.Tiles.JointGlue
  FLatticePaper.Tiles.TileCompatInputs FLatticePaper.Construction FLatticePaper.Tiles.Standard

/-- The template: two copies of one odometer `O`, with a constant difference on the overlap, are compatible. -/
theorem pairCompat_of_block (ps : List Piece) (i j : ℕ) (O : PartialOdometer) (o1 o2 a1 a2 : Site)
    (T : Set Site) (V : Site → ℤ) (c : ℤ)
    (hdom : ∀ z, z ∈ O.dom ↔ z ∈ T) (hval : ∀ z ∈ O.dom, O.val z = V z)
    (hp : ps[i]? = some (stdPiece O o1 a1)) (hq : ps[j]? = some (stdPiece O o2 a2))
    (hdiff : ∀ x : Site, x - o1 ∈ T → x - o2 ∈ T →
      V (x - o1) - V (x - o2) + ((a1.1 - a2.1) * x.1 + (a1.2 - a2.2) * x.2) = c) :
    PairCompat ps i j := by
  intro p q hpq hqq
  have hp' : stdPiece O o1 a1 = p := Option.some.inj (hp.symm.trans hpq)
  have hq' : stdPiece O o2 a2 = q := Option.some.inj (hq.symm.trans hqq)
  subst hp' hq'
  refine ⟨c, fun x hxp hxq _ _ => ?_⟩
  simp only [Piece.placed, stdPiece, Finset.mem_image] at hxp hxq
  obtain ⟨t, ht, rfl⟩ := hxp
  obtain ⟨t', ht', htx⟩ := hxq
  have h1 : t + o1 - o1 = t := add_sub_cancel_right t o1
  have h2 : t + o1 - o2 = t' := by
    rw [← htx]
    exact add_sub_cancel_right t' o2
  have hT1 : t ∈ T := (hdom t).mp ht
  have hT2 : t' ∈ T := (hdom t').mp ht'
  have hd := hdiff (t + o1) (by rw [h1]; exact hT1) (by rw [h2]; exact hT2)
  rw [h1, h2] at hd
  simp only [pieceVal, dotS, stdPiece, h1, h2]
  rw [hval t ht, hval t' ht']
  simp only [Prod.fst_add, Prod.snd_add] at hd ⊢
  linear_combination hd

/-- The base value of the ladder family at the first point: `V(-2k+a, 2k+1+b) = a + b - q` when `(2k+1+b)(2k+2+b) = 2q`. -/
theorem ladder_value_t (k a b q : ℤ) (hk : 1 ≤ k) (ha0 : 0 ≤ a) (ha2 : a ≤ 2) (hb0 : 0 ≤ b) (hb2 : b ≤ 2)
    (hq : (2 * k + 1 + b) * (2 * k + 2 + b) = 2 * q) :
    paperLadderValue (2 * k + 2) (-2 * k + a, 2 * k + 1 + b) = a + b - q := by
  unfold paperLadderValue
  dsimp only
  have hfl : (2 * k + 1 + b) * (2 * k + 1 + b + 1) / 2 = q := by
    rw [show (2 * k + 1 + b) * (2 * k + 1 + b + 1) = (2 * k + 1 + b) * (2 * k + 2 + b) by ring, hq]
    simp
  rw [hfl]
  have m1 : min (-2 * k + a - 1) 0 = -2 * k + a - 1 := min_eq_left (by omega)
  have m2 : min 0 (2 * k + 2 + 1 - (-2 * k + a)) = 0 := min_eq_left (by omega)
  have m3 : max (-2 * k + a + (2 * k + 1 + b) - (2 * k + 2) - 2) 0 = 0 := max_eq_right (by omega)
  have ind : (paperLadderA (2 * k + 2) ∪ paperLadderB (2 * k + 2)).indicator (fun _ => (1 : ℤ))
      (-2 * k + a, 2 * k + 1 + b) = 0 := by
    apply Set.indicator_of_notMem
    intro hmem
    unfold paperLadderA paperLadderB at hmem
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.ext_iff] at hmem
    omega
  rw [m1, m2, m3, ind]
  ring

/-- The base value of the ladder family at the second point: `V(4k+2+a, 1+b) = 1 + 2b - q` when `(1+b)(2+b) = 2q`. -/
theorem ladder_value_y (k a b q : ℤ) (hk : 1 ≤ k) (ha0 : 0 ≤ a) (ha2 : a ≤ 2) (hb0 : 0 ≤ b) (hb2 : b ≤ 2)
    (hq : (1 + b) * (2 + b) = 2 * q) :
    paperLadderValue (2 * k + 2) (4 * k + 2 + a, 1 + b) = 1 + 2 * b - q := by
  unfold paperLadderValue
  dsimp only
  have hfl : (1 + b) * (1 + b + 1) / 2 = q := by
    rw [show (1 + b) * (1 + b + 1) = (1 + b) * (2 + b) by ring, hq]
    simp
  rw [hfl]
  have m1 : min (4 * k + 2 + a - 1) 0 = 0 := min_eq_right (by omega)
  have m2 : min 0 (2 * k + 2 + 1 - (4 * k + 2 + a)) = 2 * k + 2 + 1 - (4 * k + 2 + a) :=
    min_eq_right (by omega)
  have m3 : max (4 * k + 2 + a + (1 + b) - (2 * k + 2) - 2) 0 = 4 * k + 2 + a + (1 + b) - (2 * k + 2) - 2 :=
    max_eq_left (by omega)
  have ind : (paperLadderA (2 * k + 2) ∪ paperLadderB (2 * k + 2)).indicator (fun _ => (1 : ℤ))
      (4 * k + 2 + a, 1 + b) = 0 := by
    apply Set.indicator_of_notMem
    intro hmem
    unfold paperLadderA paperLadderB at hmem
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.ext_iff] at hmem
    omega
  rw [m1, m2, m3, ind]
  ring

/-- The arithmetic of the ladder block: on the overlap of the two translates, the difference is `2k²+3k`. -/
theorem ladder_diff (k : ℤ) (hk : 1 ≤ k) (x : Site)
    (h0 : x - (4 * k + 2, 2) ∈ paperLadderTile (2 * k + 2))
    (h1 : x - (-2 * k, 2 * k + 2) ∈ paperLadderTile (2 * k + 2)) :
    paperLadderValue (2 * k + 2) (x - (4 * k + 2, 2)) - paperLadderValue (2 * k + 2) (x - (-2 * k, 2 * k + 2))
      + ((0 - 1) * x.1 + (0 - (-(2 * k + 1))) * x.2) = 2 * k ^ 2 + 3 * k := by
  obtain ⟨x1, x2⟩ := x
  have hb : 2 * k + 2 ≤ x1 ∧ x1 ≤ 2 * k + 4 ∧ 2 * k + 3 ≤ x2 ∧ x2 ≤ 2 * k + 5 := by
    unfold paperLadderTile paperLadderA paperLadderB paperLadderC paperLadderD at h0 h1
    simp only [Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq,
      Prod.ext_iff] at h0 h1
    simp only [Prod.fst_sub, Prod.snd_sub] at h0 h1
    omega
  obtain ⟨a, rfl⟩ : ∃ a, x1 = 2 * k + 2 + a := ⟨x1 - (2 * k + 2), by ring⟩
  obtain ⟨b, rfl⟩ : ∃ b, x2 = 2 * k + 3 + b := ⟨x2 - (2 * k + 3), by ring⟩
  have ha0 : 0 ≤ a := by omega
  have ha2 : a ≤ 2 := by omega
  have hb0 : 0 ≤ b := by omega
  have hb2 : b ≤ 2 := by omega
  have eA : ((2 * k + 2 + a, 2 * k + 3 + b) : Site) - (4 * k + 2, 2) = (-2 * k + a, 2 * k + 1 + b) := by
    ext <;> simp <;> ring
  have eB : ((2 * k + 2 + a, 2 * k + 3 + b) : Site) - (-2 * k, 2 * k + 2) = (4 * k + 2 + a, 1 + b) := by
    ext <;> simp <;> ring
  rw [eA, eB]
  rcases (show b = 0 ∨ b = 1 ∨ b = 2 by omega) with rfl | rfl | rfl
  · rw [ladder_value_t k a 0 (2 * k ^ 2 + 3 * k + 1) hk ha0 ha2 hb0 hb2 (by ring),
      ladder_value_y k a 0 1 hk ha0 ha2 hb0 hb2 (by ring)]
    ring
  · rw [ladder_value_t k a 1 (2 * k ^ 2 + 5 * k + 3) hk ha0 ha2 (by norm_num) (by norm_num) (by ring),
      ladder_value_y k a 1 3 hk ha0 ha2 (by norm_num) (by norm_num) (by ring)]
    ring
  · rw [ladder_value_t k a 2 (2 * k ^ 2 + 7 * k + 6) hk ha0 ha2 (by norm_num) (by norm_num) (by ring),
      ladder_value_y k a 2 6 hk ha0 ha2 (by norm_num) (by norm_num) (by ring)]
    ring

/-- The ladder family (`u1 = 3^k`, `k ≥ 1`) at the word `3^k 2`: the two copies of the odometer `O` at the offsets
`(4k+2, 2)` and `(-2k, 2k+2)`, with affine factors `0` and `(1, -(2k+1))`, are compatible. -/
theorem ladder_pairCompat (k : ℤ) (hk : 1 ≤ k) (ps : List Piece) (i j : ℕ) (O : PartialOdometer)
    (hO : O.dom = ladderF (2 * k + 2)) (hval : ∀ z ∈ O.dom, O.val z = paperLadderValue (2 * k + 2) z)
    (hp : ps[i]? = some (stdPiece O (4 * k + 2, 2) (0, 0)))
    (hq : ps[j]? = some (stdPiece O (-2 * k, 2 * k + 2) (1, -(2 * k + 1)))) : PairCompat ps i j := by
  refine pairCompat_of_block ps i j O (4 * k + 2, 2) (-2 * k, 2 * k + 2) (0, 0) (1, -(2 * k + 1))
    (paperLadderTile (2 * k + 2)) (paperLadderValue (2 * k + 2)) (2 * k ^ 2 + 3 * k) ?_ hval hp hq ?_
  · intro z
    rw [hO]
    exact mem_ladderF_iff_paper (by omega) z
  · intro x h0 h1
    exact ladder_diff k hk x h0 h1

/-! ### The stair block: the pair (2,5) of the odd child at the register `u2 = 3^k`, word `3^k 1` -/

/-- The stair value at the first point: `V(-2k-1+a, 2k+2+b) = a + b - q` when `(2k+2+b)(2k+3+b) = 2q`. -/
theorem stair_value_t (k a b q : ℤ) (hk : 0 ≤ k) (ha0 : 0 ≤ a) (ha2 : a ≤ 2) (hb0 : 0 ≤ b) (hb2 : b ≤ 2)
    (hq : (2 * k + 2 + b) * (2 * k + 3 + b) = 2 * q) :
    paperStairValue (2 * k + 3) (-2 * k - 1 + a, 2 * k + 2 + b) = a + b - q := by
  unfold paperStairValue
  dsimp only
  have hfl : (2 * k + 2 + b) * (2 * k + 2 + b + 1) / 2 = q := by
    rw [show (2 * k + 2 + b) * (2 * k + 2 + b + 1) = (2 * k + 2 + b) * (2 * k + 3 + b) by ring, hq]
    simp
  rw [hfl]
  have m1 : min (-2 * k - 1 + a - 1) 0 = -2 * k - 1 + a - 1 := min_eq_left (by omega)
  have hi : (if (-2 * k - 1 + a, 2 * k + 2 + b) = (0, 0) ∨ (-2 * k - 1 + a, 2 * k + 2 + b) = (2, 2 * k + 3 + 1)
      then (1 : ℤ) else 0) = 0 := by
    rw [if_neg]
    simp only [Prod.ext_iff, not_or, not_and]
    omega
  rw [m1, hi]
  ring

/-- The stair value at the second point: `V(2k+1+a, b) = b - q` when `b(b+1) = 2q`. -/
theorem stair_value_y (k a b q : ℤ) (hk : 0 ≤ k) (ha0 : 0 ≤ a) (ha2 : a ≤ 2) (hb0 : 0 ≤ b) (hb2 : b ≤ 2)
    (hq : b * (b + 1) = 2 * q) :
    paperStairValue (2 * k + 3) (2 * k + 1 + a, b) = b - q := by
  unfold paperStairValue
  dsimp only
  have hfl : b * (b + 1) / 2 = q := by
    rw [hq]
    simp
  rw [hfl]
  have m1 : min (2 * k + 1 + a - 1) 0 = 0 := min_eq_right (by omega)
  have hi : (if (2 * k + 1 + a, b) = (0, 0) ∨ (2 * k + 1 + a, b) = (2, 2 * k + 3 + 1)
      then (1 : ℤ) else 0) = 0 := by
    rw [if_neg]
    simp only [Prod.ext_iff, not_or, not_and]
    omega
  rw [m1, hi]
  ring

/-- The arithmetic of the stair block: on the overlap of the two translates, the difference is `2k²+5k+2`. -/
theorem stair_diff (k : ℤ) (hk : 0 ≤ k) (x : Site)
    (h0 : x - (4 * k + 4, 2) ∈ paperStairTile (2 * k + 3))
    (h1 : x - (2, 2 * k + 4) ∈ paperStairTile (2 * k + 3)) :
    paperStairValue (2 * k + 3) (x - (4 * k + 4, 2)) - paperStairValue (2 * k + 3) (x - (2, 2 * k + 4))
      + ((0 - 1) * x.1 + (0 - (-(2 * k + 2))) * x.2) = 2 * k ^ 2 + 5 * k + 2 := by
  obtain ⟨x1, x2⟩ := x
  have hb : 2 * k + 3 ≤ x1 ∧ x1 ≤ 2 * k + 5 ∧ 2 * k + 4 ≤ x2 ∧ x2 ≤ 2 * k + 6 := by
    unfold paperStairTile at h0 h1
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff] at h0 h1
    simp only [Prod.fst_sub, Prod.snd_sub] at h0 h1
    omega
  obtain ⟨a, rfl⟩ : ∃ a, x1 = 2 * k + 3 + a := ⟨x1 - (2 * k + 3), by ring⟩
  obtain ⟨b, rfl⟩ : ∃ b, x2 = 2 * k + 4 + b := ⟨x2 - (2 * k + 4), by ring⟩
  have ha0 : 0 ≤ a := by omega
  have ha2 : a ≤ 2 := by omega
  have hb0 : 0 ≤ b := by omega
  have hb2 : b ≤ 2 := by omega
  have eA : ((2 * k + 3 + a, 2 * k + 4 + b) : Site) - (4 * k + 4, 2) = (-2 * k - 1 + a, 2 * k + 2 + b) := by
    ext <;> simp <;> ring
  have eB : ((2 * k + 3 + a, 2 * k + 4 + b) : Site) - (2, 2 * k + 4) = (2 * k + 1 + a, b) := by
    simp only [Prod.ext_iff, Prod.fst_sub, Prod.snd_sub]
    constructor <;> ring
  rw [eA, eB]
  rcases (show b = 0 ∨ b = 1 ∨ b = 2 by omega) with rfl | rfl | rfl
  · rw [stair_value_t k a 0 (2 * k ^ 2 + 5 * k + 3) hk ha0 ha2 (by norm_num) (by norm_num) (by ring),
      stair_value_y k a 0 0 hk ha0 ha2 (by norm_num) (by norm_num) (by ring)]
    ring
  · rw [stair_value_t k a 1 (2 * k ^ 2 + 7 * k + 6) hk ha0 ha2 (by norm_num) (by norm_num) (by ring),
      stair_value_y k a 1 1 hk ha0 ha2 (by norm_num) (by norm_num) (by ring)]
    ring
  · rw [stair_value_t k a 2 (2 * k ^ 2 + 9 * k + 10) hk ha0 ha2 (by norm_num) (by norm_num) (by ring),
      stair_value_y k a 2 3 hk ha0 ha2 (by norm_num) (by norm_num) (by ring)]
    ring

/-- The stair family (`u2 = 3^k`, `k ≥ 1`) at the word `3^k 1`: the two copies of the odometer `O` at the offsets
`(4k+4, 2)` and `(2, 2k+4)`, with affine factors `0` and `(1, -(2k+2))`, are compatible. -/
theorem stair_pairCompat (k : ℤ) (hk : 0 ≤ k) (ps : List Piece) (i j : ℕ) (O : PartialOdometer)
    (hO : O.dom = stairF (2 * k + 3)) (hval : ∀ z ∈ O.dom, O.val z = paperStairValue (2 * k + 3) z)
    (hp : ps[i]? = some (stdPiece O (4 * k + 4, 2) (0, 0)))
    (hq : ps[j]? = some (stdPiece O (2, 2 * k + 4) (1, -(2 * k + 2)))) : PairCompat ps i j := by
  refine pairCompat_of_block ps i j O (4 * k + 4, 2) (2, 2 * k + 4) (0, 0) (1, -(2 * k + 2))
    (paperStairTile (2 * k + 3)) (paperStairValue (2 * k + 3)) (2 * k ^ 2 + 5 * k + 2) ?_ hval hp hq ?_
  · intro z
    rw [hO]
    exact mem_stairF_iff_paper (by omega) z
  · intro x h0 h1
    exact stair_diff k hk x h0 h1

/-! ### The near-one ladder block: the pair (4,5) of the even child at the register `u2 = 2^k`, word `2^k 3` -/

/-- The value at the first point: `V(2k+a, 6k+3+b) = -q - 4k + 1 - a - b` when the square of `6k+3+b-(2k+a)` is `4q + r`. -/
theorem nl_value_t (k a b q r : ℤ) (hk : 1 ≤ k) (ha0 : 0 ≤ a) (ha2 : a ≤ 2) (hb0 : 0 ≤ b) (hb2 : b ≤ 2)
    (hq : (6 * k + 3 + b - (2 * k + a)) ^ 2 = 4 * q + r) (hr0 : 0 ≤ r) (hr4 : r < 4) :
    paperNearLadderValue (2 * k + 2) (2 * k + a, 6 * k + 3 + b) = -q - 4 * k + 1 - a - b := by
  unfold paperNearLadderValue
  dsimp only
  have hfl : (6 * k + 3 + b - (2 * k + a)) ^ 2 / 4 = q := by
    rw [hq]
    omega
  rw [hfl]
  have m1 : min 0 (2 * k + 2 - (6 * k + 3 + b)) = 2 * k + 2 - (6 * k + 3 + b) := min_eq_right (by omega)
  have m2 : min 0 (2 * (2 * k + 2) - (6 * k + 3 + b)) = 2 * (2 * k + 2) - (6 * k + 3 + b) :=
    min_eq_right (by omega)
  have m3 : max (6 * k + 3 + b - (2 * k + a) - (2 * k + 2)) 0 = 6 * k + 3 + b - (2 * k + a) - (2 * k + 2) :=
    max_eq_left (by omega)
  have ind : (paperNearLadderA (2 * k + 2) ∪ paperNearLadderB (2 * k + 2)).indicator (fun _ => (1 : ℤ))
      (2 * k + a, 6 * k + 3 + b) = 0 := by
    apply Set.indicator_of_notMem
    intro hmem
    unfold paperNearLadderA paperNearLadderB at hmem
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.ext_iff] at hmem
    omega
  rw [m1, m2, m3, ind]
  ring

/-- The value at the second point: `V(a, b+1) = -g` when the square of `b+1-a` is `4g + r`. -/
theorem nl_value_y (k a b g r : ℤ) (hk : 1 ≤ k) (ha0 : 0 ≤ a) (ha2 : a ≤ 2) (hb0 : 0 ≤ b) (hb2 : b ≤ 2)
    (hq : (b + 1 - a) ^ 2 = 4 * g + r) (hr0 : 0 ≤ r) (hr4 : r < 4) :
    paperNearLadderValue (2 * k + 2) (a, b + 1) = -g := by
  unfold paperNearLadderValue
  dsimp only
  have hfl : (b + 1 - a) ^ 2 / 4 = g := by
    rw [hq]
    omega
  rw [hfl]
  have m1 : min 0 (2 * k + 2 - (b + 1)) = 0 := min_eq_left (by omega)
  have m2 : min 0 (2 * (2 * k + 2) - (b + 1)) = 0 := min_eq_left (by omega)
  have m3 : max (b + 1 - a - (2 * k + 2)) 0 = 0 := max_eq_right (by omega)
  have ind : (paperNearLadderA (2 * k + 2) ∪ paperNearLadderB (2 * k + 2)).indicator (fun _ => (1 : ℤ))
      (a, b + 1) = 0 := by
    apply Set.indicator_of_notMem
    intro hmem
    unfold paperNearLadderA paperNearLadderB at hmem
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.ext_iff] at hmem
    omega
  rw [m1, m2, m3, ind]
  ring

/-- The arithmetic of the near-one ladder block: on the overlap of the two translates, the difference is `4k²+6k+3`. -/
theorem nladder_diff (k : ℤ) (hk : 1 ≤ k) (x : Site)
    (h0 : (x.1 - 0, x.2 - 0 + 1) ∈ paperNearLadderTile (2 * k + 2))
    (h1 : (x.1 - 2 * k, x.2 - (6 * k + 2) + 1) ∈ paperNearLadderTile (2 * k + 2)) :
    paperNearLadderValue (2 * k + 2) (x.1 - 0, x.2 - 0 + 1)
      - paperNearLadderValue (2 * k + 2) (x.1 - 2 * k, x.2 - (6 * k + 2) + 1)
      + ((0 - 2 * k) * x.1 + (0 - -(2 * k + 2)) * x.2) = 4 * k ^ 2 + 6 * k + 3 := by
  obtain ⟨x1, x2⟩ := x
  have hb : 2 * k ≤ x1 ∧ x1 ≤ 2 * k + 2 ∧ 6 * k + 2 ≤ x2 ∧ x2 ≤ 6 * k + 4 := by
    unfold paperNearLadderTile paperNearLadderA paperNearLadderB paperNearLadderC paperNearLadderD at h0 h1
    simp only [Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq,
      Prod.ext_iff] at h0 h1
    omega
  obtain ⟨a, rfl⟩ : ∃ a, x1 = 2 * k + a := ⟨x1 - 2 * k, by ring⟩
  obtain ⟨b, rfl⟩ : ∃ b, x2 = 6 * k + 2 + b := ⟨x2 - (6 * k + 2), by ring⟩
  have ha0 : 0 ≤ a := by omega
  have ha2 : a ≤ 2 := by omega
  have hb0 : 0 ≤ b := by omega
  have hb2 : b ≤ 2 := by omega
  have e1 : (2 * k + a - 0, 6 * k + 2 + b - 0 + 1) = (2 * k + a, 6 * k + 3 + b) := by
    simp only [Prod.mk.injEq]
    exact ⟨by ring, by ring⟩
  have e2 : (2 * k + a - 2 * k, 6 * k + 2 + b - (6 * k + 2) + 1) = (a, b + 1) := by
    simp only [Prod.mk.injEq]
    exact ⟨by ring, by ring⟩
  dsimp only
  rw [e1, e2]
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 by omega) with rfl | rfl | rfl <;>
    rcases (show b = 0 ∨ b = 1 ∨ b = 2 by omega) with rfl | rfl | rfl
  · rw [nl_value_t k 0 0 (4 * k ^ 2 + (6) * k + 2) 1 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring) (by norm_num) (by norm_num),
      nl_value_y k 0 0 0 1 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring) (by norm_num) (by norm_num)]
    ring
  · rw [nl_value_t k 0 1 (4 * k ^ 2 + (8) * k + 4) 0 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring) (by norm_num) (by norm_num),
      nl_value_y k 0 1 1 0 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring) (by norm_num) (by norm_num)]
    ring
  · rw [nl_value_t k 0 2 (4 * k ^ 2 + (10) * k + 6) 1 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring) (by norm_num) (by norm_num),
      nl_value_y k 0 2 2 1 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring) (by norm_num) (by norm_num)]
    ring
  · rw [nl_value_t k 1 0 (4 * k ^ 2 + (4) * k + 1) 0 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring) (by norm_num) (by norm_num),
      nl_value_y k 1 0 0 0 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring) (by norm_num) (by norm_num)]
    ring
  · rw [nl_value_t k 1 1 (4 * k ^ 2 + (6) * k + 2) 1 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring) (by norm_num) (by norm_num),
      nl_value_y k 1 1 0 1 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring) (by norm_num) (by norm_num)]
    ring
  · rw [nl_value_t k 1 2 (4 * k ^ 2 + (8) * k + 4) 0 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring) (by norm_num) (by norm_num),
      nl_value_y k 1 2 1 0 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring) (by norm_num) (by norm_num)]
    ring
  · rw [nl_value_t k 2 0 (4 * k ^ 2 + (2) * k + 0) 1 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring) (by norm_num) (by norm_num),
      nl_value_y k 2 0 0 1 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring) (by norm_num) (by norm_num)]
    ring
  · rw [nl_value_t k 2 1 (4 * k ^ 2 + (4) * k + 1) 0 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring) (by norm_num) (by norm_num),
      nl_value_y k 2 1 0 0 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring) (by norm_num) (by norm_num)]
    ring
  · rw [nl_value_t k 2 2 (4 * k ^ 2 + (6) * k + 2) 1 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring) (by norm_num) (by norm_num),
      nl_value_y k 2 2 0 1 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring) (by norm_num) (by norm_num)]
    ring

theorem nladder_pairCompat (k : ℤ) (hk : 1 ≤ k) (ps : List Piece) (i j : ℕ) (O : PartialOdometer)
    (hO : O.dom = nladderN (2 * k + 2))
    (hval : ∀ z ∈ O.dom, O.val z = paperNearLadderValue (2 * k + 2) (z.1, z.2 + 1))
    (hp : ps[i]? = some (stdPiece O (0, 0) (0, 0)))
    (hq : ps[j]? = some (stdPiece O (2 * k, 6 * k + 2) (2 * k, -(2 * k + 2)))) : PairCompat ps i j := by
  refine pairCompat_of_block ps i j O (0, 0) (2 * k, 6 * k + 2) (0, 0) (2 * k, -(2 * k + 2))
    {z : Site | (z.1, z.2 + 1) ∈ paperNearLadderTile (2 * k + 2)}
    (fun z => paperNearLadderValue (2 * k + 2) (z.1, z.2 + 1)) (4 * k ^ 2 + 6 * k + 3) ?_ hval hp hq ?_
  · intro z
    rw [hO]
    exact mem_nladderN_iff_paper (by omega) z
  · intro x h0 h1
    exact nladder_diff k hk x h0 h1

/-! ### The near-one stair block: the pair (1,2) of the even child at the register `u1 = 2^k` (and `''` at `k = 0`), word `2^k·1` -/

/-- The near-one stair value at the first point: `V(2k+2+a, 4k+3+b) = -q - 2k - b` when the square of `4k+3+b-(2k+2+a)` is `4q + r`. -/
theorem nst_value_t (k a b q r : ℤ) (hk : 0 ≤ k) (ha0 : 0 ≤ a) (ha2 : a ≤ 2) (hb0 : 0 ≤ b) (hb2 : b ≤ 2)
    (hq : (4 * k + 3 + b - (2 * k + 2 + a)) ^ 2 = 4 * q + r) (hr0 : 0 ≤ r) (hr4 : r < 4) :
    paperNearStairValue (2 * k + 3) (2 * k + 2 + a, 4 * k + 3 + b) = -q - 2 * k - b := by
  unfold paperNearStairValue
  dsimp only
  have hfl : (4 * k + 3 + b - (2 * k + 2 + a)) ^ 2 / 4 = q := by
    rw [hq]
    omega
  rw [hfl]
  have m1 : min (2 * k + 3 - (4 * k + 3 + b)) 0 = 2 * k + 3 - (4 * k + 3 + b) := min_eq_left (by omega)
  have hi : (if (2 * k + 2 + a, 4 * k + 3 + b) = (0, 2 * k + 3 + 1) ∨
      (2 * k + 2 + a, 4 * k + 3 + b) = (2 * k + 3 + 1, 2 * k + 3 - 1)
      then (1 : ℤ) else 0) = 0 := by
    rw [if_neg]
    simp only [Prod.ext_iff, not_or, not_and]
    omega
  rw [m1, hi]
  ring

/-- The near-one stair value at the second point: `V(a, b+1) = -g` when the square of `b+1-a` is `4g + r`. -/
theorem nst_value_y (k a b g r : ℤ) (hk : 0 ≤ k) (ha0 : 0 ≤ a) (ha2 : a ≤ 2) (hb0 : 0 ≤ b) (hb2 : b ≤ 2)
    (hq : (b + 1 - a) ^ 2 = 4 * g + r) (hr0 : 0 ≤ r) (hr4 : r < 4) :
    paperNearStairValue (2 * k + 3) (a, b + 1) = -g := by
  unfold paperNearStairValue
  dsimp only
  have hfl : (b + 1 - a) ^ 2 / 4 = g := by
    rw [hq]
    omega
  rw [hfl]
  have m1 : min (2 * k + 3 - (b + 1)) 0 = 0 := min_eq_right (by omega)
  have hi : (if (a, b + 1) = (0, 2 * k + 3 + 1) ∨ (a, b + 1) = (2 * k + 3 + 1, 2 * k + 3 - 1)
      then (1 : ℤ) else 0) = 0 := by
    rw [if_neg]
    simp only [Prod.ext_iff, not_or, not_and]
    omega
  rw [m1, hi]
  ring

/-- The arithmetic of the near-one stair block: on the overlap of the two translates, the difference is `3k²+7k+5`. -/
theorem nstair_diff (k : ℤ) (hk : 0 ≤ k) (x : Site)
    (h0 : (x.1 - -1, x.2 - (2 * k + 3) + 1) ∈ paperNearStairTile (2 * k + 3))
    (h1 : (x.1 - (2 * k + 1), x.2 - (6 * k + 5) + 1) ∈ paperNearStairTile (2 * k + 3)) :
    paperNearStairValue (2 * k + 3) (x.1 - -1, x.2 - (2 * k + 3) + 1)
      - paperNearStairValue (2 * k + 3) (x.1 - (2 * k + 1), x.2 - (6 * k + 5) + 1)
      + ((k + 1 - (2 * k + 1)) * x.1 + (-(k + 2) - -(2 * k + 3)) * x.2) = 3 * k ^ 2 + 7 * k + 5 := by
  obtain ⟨x1, x2⟩ := x
  have hb : 2 * k + 1 ≤ x1 ∧ x1 ≤ 2 * k + 3 ∧ 6 * k + 5 ≤ x2 ∧ x2 ≤ 6 * k + 7 := by
    unfold paperNearStairTile at h0 h1
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff] at h0 h1
    omega
  obtain ⟨a, rfl⟩ : ∃ a, x1 = 2 * k + 1 + a := ⟨x1 - (2 * k + 1), by ring⟩
  obtain ⟨b, rfl⟩ : ∃ b, x2 = 6 * k + 5 + b := ⟨x2 - (6 * k + 5), by ring⟩
  have ha0 : 0 ≤ a := by omega
  have ha2 : a ≤ 2 := by omega
  have hb0 : 0 ≤ b := by omega
  have hb2 : b ≤ 2 := by omega
  have e1 : (2 * k + 1 + a - -1, 6 * k + 5 + b - (2 * k + 3) + 1) = (2 * k + 2 + a, 4 * k + 3 + b) := by
    simp only [Prod.mk.injEq]
    exact ⟨by ring, by ring⟩
  have e2 : (2 * k + 1 + a - (2 * k + 1), 6 * k + 5 + b - (6 * k + 5) + 1) = (a, b + 1) := by
    simp only [Prod.mk.injEq]
    exact ⟨by ring, by ring⟩
  dsimp only
  rw [e1, e2]
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 by omega) with rfl | rfl | rfl <;>
    rcases (show b = 0 ∨ b = 1 ∨ b = 2 by omega) with rfl | rfl | rfl
  · rw [nst_value_t k 0 0 (k ^ 2 + (1) * k + 0) 1 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring) (by norm_num) (by norm_num),
      nst_value_y k 0 0 0 1 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring) (by norm_num) (by norm_num)]
    ring
  · rw [nst_value_t k 0 1 (k ^ 2 + (2) * k + 1) 0 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring) (by norm_num) (by norm_num),
      nst_value_y k 0 1 1 0 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring) (by norm_num) (by norm_num)]
    ring
  · rw [nst_value_t k 0 2 (k ^ 2 + (3) * k + 2) 1 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring) (by norm_num) (by norm_num),
      nst_value_y k 0 2 2 1 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring) (by norm_num) (by norm_num)]
    ring
  · rw [nst_value_t k 1 0 (k ^ 2 + (0) * k + 0) 0 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring) (by norm_num) (by norm_num),
      nst_value_y k 1 0 0 0 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring) (by norm_num) (by norm_num)]
    ring
  · rw [nst_value_t k 1 1 (k ^ 2 + (1) * k + 0) 1 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring) (by norm_num) (by norm_num),
      nst_value_y k 1 1 0 1 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring) (by norm_num) (by norm_num)]
    ring
  · rw [nst_value_t k 1 2 (k ^ 2 + (2) * k + 1) 0 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring) (by norm_num) (by norm_num),
      nst_value_y k 1 2 1 0 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring) (by norm_num) (by norm_num)]
    ring
  · rw [nst_value_t k 2 0 (k ^ 2 + (-1) * k + 0) 1 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring) (by norm_num) (by norm_num),
      nst_value_y k 2 0 0 1 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring) (by norm_num) (by norm_num)]
    ring
  · rw [nst_value_t k 2 1 (k ^ 2 + (0) * k + 0) 0 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring) (by norm_num) (by norm_num),
      nst_value_y k 2 1 0 0 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring) (by norm_num) (by norm_num)]
    ring
  · rw [nst_value_t k 2 2 (k ^ 2 + (1) * k + 0) 1 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring) (by norm_num) (by norm_num),
      nst_value_y k 2 2 0 1 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring) (by norm_num) (by norm_num)]
    ring

theorem nstair_pairCompat (k : ℤ) (hk : 0 ≤ k) (ps : List Piece) (i j : ℕ) (O : PartialOdometer)
    (hO : O.dom = nstairN (2 * k + 3))
    (hval : ∀ z ∈ O.dom, O.val z = paperNearStairValue (2 * k + 3) (z.1, z.2 + 1))
    (hp : ps[i]? = some (stdPiece O (-1, 2 * k + 3) (k + 1, -(k + 2))))
    (hq : ps[j]? = some (stdPiece O (2 * k + 1, 6 * k + 5) (2 * k + 1, -(2 * k + 3)))) : PairCompat ps i j := by
  refine pairCompat_of_block ps i j O (-1, 2 * k + 3) (2 * k + 1, 6 * k + 5) (k + 1, -(k + 2))
    (2 * k + 1, -(2 * k + 3))
    {z : Site | (z.1, z.2 + 1) ∈ paperNearStairTile (2 * k + 3)}
    (fun z => paperNearStairValue (2 * k + 3) (z.1, z.2 + 1)) (3 * k ^ 2 + 7 * k + 5) ?_ hval hp hq ?_
  · intro z
    rw [hO]
    exact mem_nstairN_iff_paper (by omega) z
  · intro x h0 h1
    exact nstair_diff k hk x h0 h1

end FLatticePaper.Tiles.SwapBaseBlock
