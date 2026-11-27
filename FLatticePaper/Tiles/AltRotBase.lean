import FLatticePaper.Tiles.PaperAltBase

/-! Rotation identities of the base alternate tiles of `prop:base_cases` (item (1) of `lemma:alternate_tile_properties`).

For the paper base (`PaperAltBase.paperAltBaseTiles`): the stair `stairAltF d` and the near-one stair `nearStairAltF d`
(`d` the parameter `2k+3` of the words `3^k` and `2^k`, and of the empty word at `d = 3`), and the ladder `ladderAltF d` and the
near-one ladder `nearLadderAltF d` (`d = 2k+2`). Each rotation identity is a translation of a rotated tile, and each is a
linear statement in the coordinates, so it is decided by `omega` for all values of the parameter. -/

namespace FLatticePaper.Tiles.AltRotBase

open FLatticePaper.Tiles.Standard FLatticePaper.Tiles.PaperAltBase FLatticePaper.Farey

/-- A point is in the rotation of a tile iff its rotated-back point is in the tile: `z ∈ rot T ↔ (z₂, -z₁) ∈ T`. -/
theorem mem_rot_iff {T : Tile} {z : Site} : z ∈ rot T ↔ (z.2, -z.1) ∈ T := by
  unfold rot
  constructor
  · intro h
    obtain ⟨y, hy, hyz⟩ := Finset.mem_image.1 h
    have e : (z.2, -z.1) = y := by
      rw [← hyz]
      simp [mulI]
    rw [e]
    exact hy
  · intro h
    exact Finset.mem_image.2 ⟨(z.2, -z.1), h, by simp [mulI]⟩

/-- The box of the stair and near-one stair families (`boxF d`). -/
abbrev boxP (d a b : ℤ) : Prop := (-3 * d ≤ a ∧ a ≤ 3 * d) ∧ (-3 * d ≤ b ∧ b ≤ 3 * d)

/-- The defining predicate of `stairAltF d` (disjunct order as in `PaperAltBase.stairAltF`). -/
abbrev stairP (d a b : ℤ) : Prop :=
  (a = 1 - d ∧ -1 ≤ b ∧ b ≤ 0) ∨ (a = 3 ∧ d ≤ b ∧ b ≤ d + 1) ∨ (a + b = 2 ∧ 0 < b ∧ b < d) ∨
    (1 - d ≤ a ∧ a ≤ 0 ∧ b = -1) ∨ (4 - d ≤ a ∧ a ≤ 3 ∧ b = d + 1) ∨
    (4 - 2 * d ≤ a ∧ a ≤ d ∧ 0 ≤ b ∧ b ≤ d ∧ -d + 2 ≤ a + b ∧ a + b ≤ d + 2)

/-- The defining predicate of `nearStairAltF d` (disjunct order as in `PaperAltBase.nearStairAltF`). -/
abbrev nearP (d a b : ℤ) : Prop :=
  (-1 ≤ a ∧ a ≤ 0 ∧ b = 2 * d) ∨ (d ≤ a ∧ a ≤ d + 1 ∧ b = d - 2) ∨ (b - a = d - 1 ∧ 0 < a ∧ a < d) ∨
    (a = -1 ∧ d + 1 ≤ b ∧ b ≤ 2 * d) ∨ (a = d + 1 ∧ d - 2 ≤ b ∧ b ≤ 2 * d - 3) ∨
    (0 ≤ a ∧ a ≤ d ∧ 1 ≤ b ∧ b ≤ 3 * d - 3 ∧ -1 ≤ b - a ∧ b - a ≤ 2 * d - 1)

theorem mem_stairAltF_iff (d : ℤ) (z : Site) : z ∈ stairAltF d ↔ boxP d z.1 z.2 ∧ stairP d z.1 z.2 := by
  obtain ⟨a, b⟩ := z
  simp [stairAltF, boxF, boxP, stairP, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, and_assoc]

theorem mem_nearStairAltF_iff (d : ℤ) (z : Site) :
    z ∈ nearStairAltF d ↔ boxP d z.1 z.2 ∧ nearP d z.1 z.2 := by
  obtain ⟨a, b⟩ := z
  simp [nearStairAltF, boxF, boxP, nearP, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, and_assoc]

/-- The stair of `d` is the rotated near-one stair of `d`, translated by `(d, 0)`. -/
theorem rot_nearStair_eq_stair (d : ℤ) (hd : 1 ≤ d) :
    shift (rot (shift (nearStairAltF d) (0, -1))) (d, 0) = stairAltF d := by
  ext x
  simp only [mem_shift, mem_rot_iff, mem_stairAltF_iff, mem_nearStairAltF_iff, Prod.fst_sub, Prod.snd_sub,
    boxP, stairP, nearP]
  constructor <;> intro h <;> omega

/-- The rotated stair of `d` is the near-one stair of `d` (shifted by `(0, -1)`), translated by `(d, 2d - 4)`: the two
directions are split, and each stair disjunct is matched with the near-one disjunct of the same shape (the map of the
disjuncts is `(1, 0, 2, 4, 3, 5)`, an involution). -/
theorem rot_stair_eq_nearStair (d : ℤ) (hd : 1 ≤ d) :
    shift (rot (stairAltF d)) (d, 2 * d - 4) = shift (nearStairAltF d) (0, -1) := by
  ext x
  simp only [mem_shift, mem_rot_iff, mem_stairAltF_iff, mem_nearStairAltF_iff, Prod.fst_sub, Prod.snd_sub,
    boxP, stairP, nearP]
  constructor
  · rintro ⟨hb, hs⟩
    rcases hs with h0 | h1 | h2 | h3 | h4 | h5
    · refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, Or.inr (Or.inl ⟨?_, ?_, ?_⟩)⟩ <;> omega
    · refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, Or.inl ⟨?_, ?_, ?_⟩⟩ <;> omega
    · refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩))⟩ <;> omega
    · refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩)))) ⟩ <;> omega
    · refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩)))⟩ <;> omega
    · refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_, ?_, ?_, ?_⟩))))⟩ <;> omega
  · rintro ⟨hb, hs⟩
    rcases hs with h0 | h1 | h2 | h3 | h4 | h5
    · refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, Or.inr (Or.inl ⟨?_, ?_, ?_⟩)⟩ <;> omega
    · refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, Or.inl ⟨?_, ?_, ?_⟩⟩ <;> omega
    · refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩))⟩ <;> omega
    · refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩)))) ⟩ <;> omega
    · refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩)))⟩ <;> omega
    · refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_, ?_, ?_, ?_⟩))))⟩ <;> omega

/-- The rotated ladder of `d` (shifted by `(1,1)`) is the near-one ladder of `d` (shifted by `(0,-1)`), translated by
`(d + 1, d - 2)`. -/
theorem rot_ladder_eq_nearLadder (d : ℤ) :
    shift (rot (shift (ladderAltF d) (1, 1))) (d + 1, d - 2) = shift (nearLadderAltF d) (0, -1) := by
  ext x
  simp only [mem_shift, mem_rot_iff]
  simp [nearLadderAltF, ladderAltF, boxF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Prod.ext_iff]
  constructor <;> intro h <;> omega

/-- The rotated near-one ladder of `d` (shifted by `(0,-1)`) is the ladder of `d` (shifted by `(1,1)`), translated by
`(2d - 1, 2)`. -/
theorem rot_nearLadder_eq_ladder (d : ℤ) :
    shift (rot (shift (nearLadderAltF d) (0, -1))) (2 * d - 1, 2) = shift (ladderAltF d) (1, 1) := by
  ext x
  simp only [mem_shift, mem_rot_iff]
  simp [nearLadderAltF, ladderAltF, boxF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Prod.ext_iff]
  constructor <;> intro h <;> omega

end FLatticePaper.Tiles.AltRotBase
