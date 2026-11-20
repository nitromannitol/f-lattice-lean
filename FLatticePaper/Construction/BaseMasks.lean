import FLatticePaper.Construction.Placement
import FLatticePaper.Plane.QuarterTurn
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Ring

namespace FLatticePaper.Construction

/-- Read the retained heights in an integer rectangle, without assigning values
to any sites omitted by the mask. -/
def maskedTile (lower upper : Site) (entry : Site → Option ℤ) : HeightTile Site where
  sites := ((Finset.Icc lower.1 upper.1).product (Finset.Icc lower.2 upper.2)).filter
    (fun site => (entry site).isSome)
  height site := (entry site.val).get (Finset.mem_filter.mp site.property).2

theorem mem_maskedTile_sites (lower upper : Site) (entry : Site → Option ℤ) (site : Site) :
    site ∈ (maskedTile lower upper entry).sites ↔
      (lower.1 ≤ site.1 ∧ site.1 ≤ upper.1) ∧
      (lower.2 ≤ site.2 ∧ site.2 ≤ upper.2) ∧ (entry site).isSome := by
  simp only [maskedTile, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product,
    Finset.mem_Icc, and_assoc]

/-- The eight literal masks of the sparse constructor's pure initializers. -/
inductive BaseMask where
  | stairEven | stairOdd | stairEvenAlt | stairOddAlt
  | ladderOdd | ladderEven | ladderOddAlt | ladderEvenAlt
  deriving DecidableEq

namespace BaseMask

/-- Staircases use odd denominators from 3, and ladders even denominators from 4. -/
def Valid (kind : BaseMask) (den : ℤ) : Prop :=
  match kind with
  | .stairEven | .stairOdd | .stairEvenAlt | .stairOddAlt => 3 ≤ den ∧ den % 2 = 1
  | .ladderOdd | .ladderEven | .ladderOddAlt | .ladderEvenAlt => 4 ≤ den ∧ den % 2 = 0

def StairEvenCorner (den : ℤ) (point : Site) : Prop :=
  (point.1 = 0 ∧ point.2 = 0) ∨ (point.1 = 2 ∧ point.2 = den + 1)

instance (den : ℤ) (point : Site) : Decidable (StairEvenCorner den point) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The B1 height formula on the occupied mask, including its two corner increments. -/
def stairEvenValue (den : ℤ) (point : Site) : ℤ :=
  -(point.2 * (point.2 - 1) / 2) + min (point.1 - 1) 0 +
    (if StairEvenCorner den point then 1 else 0)

private def window : BaseMask → ℤ → Site × Site
  | .stairEven, den => ((2 - den, 0), (den, den + 1))
  | .stairOdd, den => ((0, 1), (den + 1, 2 * den - 1))
  | .stairEvenAlt, den => ((4 - 2 * den, -1), (den, den + 1))
  | .stairOddAlt, den => ((-1, 1), (den + 1, 3 * den - 3))
  | .ladderOdd, den => ((2 - den, 0), (2 * den, den + 2))
  | .ladderEven, den => ((-1, 1), (den + 1, 3 * den - 1))
  | .ladderOddAlt, den => ((1 - den, -1), (2 * den - 2, den + 2))
  | .ladderEvenAlt, den => ((-2, 1), (den + 1, 3 * den - 2))

private def entry : BaseMask → ℤ → Site → Option ℤ
  | .stairEven, den, (col, row) =>
    if StairEvenCorner den (col, row) ∨ (1 ≤ col + row ∧ col + row ≤ den + 2)
      then some (stairEvenValue den (col, row))
    else none
  | .stairOdd, den, (col, row) =>
    let value := -((col - row) ^ 2 / 4) + min (den - row) 0
    if (col = 0 ∧ row = den + 1) ∨ (col = den + 1 ∧ row = den - 1) then some (value + 1)
    else if -1 ≤ row - col ∧ row - col ≤ den then some value
    else none
  | .stairEvenAlt, den, (col, row) =>
    let value := -(row * (row + 1) / 2) + min 0 (2 - col) +
      min 0 (den - 2 + col) + max (col + row - 2) 0
    if (col + row = 2 ∧ 0 < row ∧ row < den) ∨
        (col = 1 - den ∧ (row = 0 ∨ row = -1)) ∨ (col = 3 ∧ (row = den ∨ row = den + 1))
      then some (value + 1)
    else if (2 - den ≤ col + row ∧ col + row ≤ den + 2 ∧ 0 ≤ row ∧ row ≤ den) ∨
        (row = -1 ∧ 1 - den ≤ col ∧ col ≤ 0) ∨ (row = den + 1 ∧ 4 - den ≤ col ∧ col ≤ 3)
      then some value
    else none
  | .stairOddAlt, den, (col, row) =>
    let value := -((col - row) ^ 2 / 4) + min (den - row - 1) 0 +
      min (2 * den - 1 - row) 0 + max (row - col - den + 1) 0
    if (col = 0 ∧ row = 2 * den) ∨ (col = den ∧ row = den - 2) ∨
        (col = -1 ∧ row = 2 * den) ∨ (col = den + 1 ∧ row = den - 2)
      then some (value + 1)
    else if (col = -1 ∧ den + 1 ≤ row ∧ row ≤ 2 * den) ∨
        (col = den + 1 ∧ den - 2 ≤ row ∧ row ≤ 2 * den - 3)
      then some value
    else if row - col = den - 1 ∧ 0 < col ∧ col < den then some (value + 1)
    else if 0 ≤ col ∧ col ≤ den ∧ -1 ≤ row - col ∧ row - col ≤ 2 * den - 1
      then some value
    else none
  | .ladderOdd, den, (col, row) =>
    let value := -(row * (row - 1) / 2) + min 0 (col - 1) +
      max (row + col - den - 2) 0 + min (den + 1 - col) 0
    if (col = 0 ∧ row = 0) ∨ (col = den + 2 ∧ row = den + 2) ∨
        (col + row = den + 2 ∧ 1 < row ∧ row < den + 1)
      then some (value + 1)
    else if 1 ≤ col + row ∧ col + row ≤ 2 * den + 3 ∧
        ¬ ((row = 0 ∧ den ≤ col) ∨ (row = den + 2 ∧ col ≤ 2))
      then some value
    else none
  | .ladderEven, den, (col, row) =>
    let value := -((col - row) ^ 2 / 4) + min 0 (den - row) +
      max 0 (row - col - den) + min 0 (2 * den - row)
    if (col = -1 ∧ row = 2 * den + 1) ∨ (col = den + 1 ∧ row = den - 1) ∨
        (row - col = den ∧ 0 < col ∧ col < den)
      then some (value + 1)
    else if -1 ≤ row - col ∧ row - col ≤ 2 * den + 1 ∧
        ¬ ((col = -1 ∧ row ≤ den + 1) ∨ (col = den + 1 ∧ 2 * den - 1 ≤ row))
      then some value
    else none
  | .ladderOddAlt, den, (col, row) =>
    let baseline := -(row * (row + 1) / 2) + min col 0 + max (col + row - den) 0
    let value := baseline + min (den - col - 1) 0
    if (col = -1 ∧ row = -1) ∨ (col = den ∧ row = den + 2) then some (value + 1)
    else if -1 ≤ col + row ∧ col + row ≤ 2 * den + 1 ∧
        ¬ ((-1 ≤ row ∧ row ≤ 0 ∧ den ≤ col) ∨ (den + 1 ≤ row ∧ row ≤ den + 2 ∧ col ≤ -1))
      then if col + row = den ∧ 0 < col ∧ col < den - 1 then some (baseline + 1)
        else some value
    else none
  | .ladderEvenAlt, den, (col, row) =>
    let value := -((col - row) ^ 2 / 4) + min 0 (den - row) +
      min (2 * den - 1 - row) 0 + max (row - col - den) 0
    if (col = -2 ∧ row = 2 * den) ∨ (col = den + 1 ∧ row = den - 1) then some (value + 1)
    else if -1 ≤ row - col ∧ row - col ≤ 2 * den + 1 ∧
        ¬ ((col ≤ -1 ∧ row ≤ den - 1) ∨ (den ≤ col ∧ 2 * den ≤ row))
      then if row - col = den ∧ 0 < col ∧ col < den - 1 then some (value + 1)
        else some value
    else none

/-- The literal mask before the constructor's rectangular trim. -/
def raw (kind : BaseMask) (den : ℤ) : HeightTile Site :=
  maskedTile (kind.window den).1 (kind.window den).2 (kind.entry den)

private def witness : BaseMask → Site
  | .stairEven | .stairEvenAlt | .ladderOdd | .ladderOddAlt => (0, 0)
  | .stairOdd | .stairOddAlt | .ladderEven | .ladderEvenAlt => (0, 1)

private theorem raw_nonempty (kind : BaseMask) (den : ℤ) (hden : kind.Valid den) :
    (kind.raw den).sites.Nonempty := by
  refine ⟨kind.witness, ?_⟩
  rw [raw, mem_maskedTile_sites]
  cases kind <;> simp only [witness, window, entry, Valid] at hden ⊢
  all_goals obtain ⟨hmin, _⟩ := hden
  all_goals refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ?_⟩
  all_goals repeat' first | rfl | split | omega

/-- The literal initializer, returned in the rectangular trim convention. -/
def tile (kind : BaseMask) (den : ℤ) (hden : kind.Valid den) : HeightTile Site :=
  (kind.raw den).trim (kind.raw_nonempty den hden)

theorem tile_nonempty (kind : BaseMask) (den : ℤ) (hden : kind.Valid den) :
    (kind.tile den hden).sites.Nonempty :=
  (kind.raw den).trim_sites_nonempty (kind.raw_nonempty den hden)

theorem mem_stairEven_raw_iff {den : ℤ} {point : Site} :
    point ∈ (stairEven.raw den).sites ↔
      (2 - den ≤ point.1 ∧ point.1 ≤ den) ∧ (0 ≤ point.2 ∧ point.2 ≤ den + 1) ∧
        (StairEvenCorner den point ∨ (1 ≤ point.1 + point.2 ∧ point.1 + point.2 ≤ den + 2)) := by
  obtain ⟨col, row⟩ := point
  rw [raw, mem_maskedTile_sites]
  simp only [window, entry, Option.isSome_ite]

theorem stairEven_raw_height (den : ℤ) (point : (stairEven.raw den).sites) :
    (stairEven.raw den).height point = stairEvenValue den point.val := by
  obtain ⟨⟨col, row⟩, hpoint⟩ := point
  have hbody := (mem_stairEven_raw_iff.mp hpoint).2.2
  apply Option.get_of_eq_some
  simp only [entry, if_pos hbody]

/-- For B1 the raw origin is already the occupied lower-left. The rectangular
trim and the final occupied centering therefore cancel in the height chart. -/
theorem stairEven_llCenter_agrees {den : ℤ} (hden : stairEven.Valid den) {field : Field}
    (hagree : (stairEven.raw den).Agrees field 0) :
    ((stairEven.tile den hden).llCenter (stairEven.tile_nonempty den hden)).Agrees field 0 := by
  let raw := stairEven.raw den
  have hraw : raw.sites.Nonempty := stairEven.raw_nonempty den hden
  let origin := raw.boxOrigin hraw
  let tile := stairEven.tile den hden
  have htile : tile.sites.Nonempty := stairEven.tile_nonempty den hden
  have hmin := hden.1
  have hzero : (0 : Site) ∈ raw.sites := by
    apply mem_stairEven_raw_iff.mpr
    exact ⟨⟨by dsimp; omega, by dsimp; omega⟩, ⟨by decide, by dsimp; omega⟩,
      Or.inl (Or.inl ⟨rfl, rfl⟩)⟩
  have hleft : tile.lowerLeft htile = -origin := by
    apply HeightTile.lowerLeft_eq_of_minimal
    · change -origin ∈ (raw.place (-origin) 0).sites
      rwa [HeightTile.mem_place_sites, sub_self]
    · intro site hmem
      change site ∈ (raw.place (-origin) 0).sites at hmem
      rw [HeightTile.mem_place_sites, sub_neg_eq_add] at hmem
      obtain ⟨hx, hy, hband⟩ := mem_stairEven_raw_iff.mp hmem
      simp only [StairEvenCorner, Prod.fst_add, Prod.snd_add] at hx hy hband
      simp only [Prod.fst_neg, Prod.snd_neg]
      omega
  have h := (hagree.trim hraw).place (-tile.lowerLeft htile) 0
  change (tile.place (-tile.lowerLeft htile) 0).Agrees
    (fun site => field (site - -tile.lowerLeft htile + origin) + (0 * site.1 + 0 * site.2)) 0 at h
  change (tile.place (-tile.lowerLeft htile) 0).Agrees field 0
  simpa only [hleft, neg_neg, sub_add_cancel, zero_mul, add_zero] using h

theorem mem_stairEven_body {den : ℤ} {point : Site}
    (hx : 2 - den ≤ point.1 ∧ point.1 ≤ den)
    (hy : 0 ≤ point.2 ∧ point.2 ≤ den + 1)
    (hband : 1 ≤ point.1 + point.2 ∧ point.1 + point.2 ≤ den + 2) :
    point ∈ (BaseMask.stairEven.raw den).sites :=
  mem_stairEven_raw_iff.mpr ⟨hx, hy, Or.inr hband⟩

theorem mem_stairEvenAlt_body_or_rail {den : ℤ} {point : Site}
    (hx : 4 - 2 * den ≤ point.1 ∧ point.1 ≤ den)
    (hy : -1 ≤ point.2 ∧ point.2 ≤ den + 1)
    (hbody : (2 - den ≤ point.1 + point.2 ∧ point.1 + point.2 ≤ den + 2 ∧
      0 ≤ point.2 ∧ point.2 ≤ den) ∨ (point.2 = den + 1 ∧ 4 - den ≤ point.1 ∧ point.1 ≤ 3)) :
    point ∈ (BaseMask.stairEvenAlt.raw den).sites := by
  rw [raw, mem_maskedTile_sites]
  refine ⟨hx, hy, ?_⟩
  obtain ⟨col, row⟩ := point
  simp only [entry]
  split
  · rfl
  · rw [if_pos (hbody.imp_right Or.inr)]
    rfl

private theorem isSome_ite_some {α : Type*} {p : Prop} [Decidable p] (value : α)
    (other : Option α) : (if p then some value else other).isSome ↔ p ∨ other.isSome := by
  by_cases hp : p <;> simp [hp]

private theorem isSome_ite_iff {α : Type*} {p : Prop} [Decidable p] (first second : Option α) :
    (if p then first else second).isSome ↔
      (p ∧ first.isSome) ∨ (¬ p ∧ second.isSome) := by
  by_cases hp : p <;> simp [hp]

/-- The body, both rails, and the two isolated corners of the raw B3 mask. -/
theorem mem_stairEvenAlt_raw_iff {den : ℤ} {point : Site} :
    point ∈ (stairEvenAlt.raw den).sites ↔
      (4 - 2 * den ≤ point.1 ∧ point.1 ≤ den) ∧ (-1 ≤ point.2 ∧ point.2 ≤ den + 1) ∧
      ((0 ≤ point.2 ∧ point.2 ≤ den ∧ 2 - den ≤ point.1 + point.2 ∧ point.1 + point.2 ≤ den + 2) ∨
       (point.2 = -1 ∧ 1 - den ≤ point.1 ∧ point.1 ≤ 0) ∨
       (point.2 = den + 1 ∧ 4 - den ≤ point.1 ∧ point.1 ≤ 3) ∨
       (point.1 = 1 - den ∧ point.2 = 0) ∨ (point.1 = 3 ∧ point.2 = den)) := by
  obtain ⟨col, row⟩ := point
  rw [raw, mem_maskedTile_sites]
  simp only [window, entry, isSome_ite_some, Option.isSome_none, Bool.false_eq_true, or_false]
  omega

/-- The polynomial and the three piecewise linear terms of B3. -/
def stairEvenAltBackground (den : ℤ) (point : Site) : ℤ :=
  -(point.2 * (point.2 + 1) / 2) + min 0 (2 - point.1) +
    min 0 (den - 2 + point.1) + max (point.1 + point.2 - 2) 0

abbrev StairEvenAltBump (den : ℤ) (point : Site) : Prop :=
  (point.1 + point.2 = 2 ∧ 0 < point.2 ∧ point.2 < den) ∨
    (point.1 = 1 - den ∧ (point.2 = 0 ∨ point.2 = -1)) ∨
    (point.1 = 3 ∧ (point.2 = den ∨ point.2 = den + 1))

theorem stairEvenAlt_raw_height (den : ℤ) (point : (stairEvenAlt.raw den).sites) :
    (stairEvenAlt.raw den).height point = stairEvenAltBackground den point.val +
      (if StairEvenAltBump den point.val then 1 else 0) := by
  obtain ⟨⟨col, row⟩, hmem⟩ := point
  have hentry := ((mem_maskedTile_sites _ _ _ _).mp hmem).2.2
  change (entry .stairEvenAlt den (col, row)).isSome at hentry
  apply Option.get_of_eq_some
  change entry .stairEvenAlt den (col, row) = some _
  by_cases h : StairEvenAltBump den (col, row)
  · simp only [entry, stairEvenAltBackground, if_pos h]
  · simp only [entry, if_neg h] at hentry
    simp only [entry, stairEvenAltBackground, if_neg h, if_pos (Option.isSome_ite.mp hentry), add_zero]

/-- Restore the B3 physical chart after the constructor's storage centering. -/
theorem stairEvenAlt_llCenter_agrees {den : ℤ} (hden : stairEvenAlt.Valid den) {field : Field}
    (hagree : (stairEvenAlt.raw den).Agrees field 0) :
    ((stairEvenAlt.tile den hden).llCenter (stairEvenAlt.tile_nonempty den hden)).Agrees
      (fun site => field (site + (1 - den, -1))) 0 := by
  have hmin := hden.1
  apply hagree.llCenter_trim (stairEvenAlt.raw_nonempty den hden)
  · apply mem_stairEvenAlt_raw_iff.mpr
    dsimp
    omega
  · intro site hsite
    obtain ⟨hcol, hrow, hshape⟩ := mem_stairEvenAlt_raw_iff.mp hsite
    dsimp
    omega

/-- The source's B2 pullback in the raw formula coordinates. -/
theorem mem_stairOdd_raw_pullback_iff {den : ℤ} (point : Site) :
    point ∈ (stairOdd.raw den).sites ↔ (den + 1 - point.2, point.1) ∈ (stairEven.raw den).sites := by
  obtain ⟨col, row⟩ := point
  rw [raw, mem_maskedTile_sites, mem_stairEven_raw_iff]
  simp only [window, entry, isSome_ite_some, Option.isSome_none, Bool.false_eq_true, or_false,
    StairEvenCorner]
  omega

/-- On its literal support, the raw B2 height is the B1 pullback plus the
integer correction in the source's formula coordinates. -/
theorem stairOdd_raw_height (den : ℤ) (point : (stairOdd.raw den).sites) :
    (stairOdd.raw den).height point = stairEvenValue den (den + 1 - point.val.2, point.val.1) +
      (point.val.1 * (point.val.1 - 1) / 2 - (point.val.1 - point.val.2) ^ 2 / 4) := by
  obtain ⟨⟨col, row⟩, hmem⟩ := point
  obtain ⟨_, _, hshape⟩ := (mem_stairEven_raw_iff.mp ((mem_stairOdd_raw_pullback_iff _).mp hmem))
  have hcorners : StairEvenCorner den (den + 1 - row, col) ↔
      (col = 0 ∧ row = den + 1) ∨ (col = den + 1 ∧ row = den - 1) := by
    simp only [StairEvenCorner]
    omega
  apply Option.get_of_eq_some
  change entry .stairOdd den (col, row) = some _
  simp only [entry, stairEvenValue, hcorners]
  rw [show den + 1 - row - 1 = den - row by omega]
  by_cases hcorner : (col = 0 ∧ row = den + 1) ∨ (col = den + 1 ∧ row = den - 1)
  · rw [if_pos hcorner, if_pos hcorner, Option.some.injEq]
    omega
  · have hband := hshape.resolve_left (mt hcorners.mp hcorner)
    rw [if_neg hcorner, if_neg hcorner, if_pos (by dsimp at hband; omega : -1 ≤ row - col ∧ row - col ≤ den),
      Option.some.injEq]
    omega

/-- B2's occupied lower-left in raw formula coordinates is `(0,1)`. -/
theorem stairOdd_llCenter_agrees {den : ℤ} (hden : stairOdd.Valid den) {field : Field}
    (hagree : (stairOdd.raw den).Agrees field 0) :
    ((stairOdd.tile den hden).llCenter (stairOdd.tile_nonempty den hden)).Agrees
      (fun site => field (site + (0, 1))) 0 := by
  apply hagree.llCenter_trim (stairOdd.raw_nonempty den hden)
  · apply (mem_stairOdd_raw_pullback_iff _).mpr
    have := hden.1
    apply mem_stairEven_body <;> dsimp <;> omega
  · intro site hmem
    have hbounds := (mem_maskedTile_sites _ _ _ site).mp hmem
    exact ⟨hbounds.2.1.1, fun _ => hbounds.1.1⟩

theorem mem_stairOddAlt_raw_pullback_iff {den : ℤ} (hden : 3 ≤ den) (point : Site) :
    point ∈ (stairOddAlt.raw den).sites ↔ (den + 1 - point.2, point.1) ∈ (stairEvenAlt.raw den).sites := by
  obtain ⟨col, row⟩ := point
  rw [raw, mem_maskedTile_sites, mem_stairEvenAlt_raw_iff]
  simp only [window, entry, isSome_ite_some, Option.isSome_none, Bool.false_eq_true, or_false]
  omega

/-- B4 has the exact B3 pullback height plus the raw harmonic correction. -/
theorem stairOddAlt_raw_height (den : ℤ) (point : (stairOddAlt.raw den).sites) :
    (stairOddAlt.raw den).height point =
      stairEvenAltBackground den (den + 1 - point.val.2, point.val.1) +
        (if StairEvenAltBump den (den + 1 - point.val.2, point.val.1) then 1 else 0) +
      (point.val.1 * (point.val.1 - 1) / 2 - (point.val.1 - point.val.2) ^ 2 / 4) := by
  obtain ⟨⟨col, row⟩, hmem⟩ := point
  let special : Prop := (col = 0 ∧ row = 2 * den) ∨ (col = den ∧ row = den - 2) ∨
    (col = -1 ∧ row = 2 * den) ∨ (col = den + 1 ∧ row = den - 2)
  let rail : Prop := (col = -1 ∧ den + 1 ≤ row ∧ row ≤ 2 * den) ∨
    (col = den + 1 ∧ den - 2 ≤ row ∧ row ≤ 2 * den - 3)
  let diagonal : Prop := row - col = den - 1 ∧ 0 < col ∧ col < den
  let value := -((col - row) ^ 2 / 4) + min (den - row - 1) 0 +
    min (2 * den - 1 - row) 0 + max (row - col - den + 1) 0
  let correction := col * (col - 1) / 2 - (col - row) ^ 2 / 4
  have htri : -(col * (col + 1) / 2) + col * (col - 1) / 2 = -col := by
    rw [show col * (col + 1) = col * (col - 1) + col * 2 by ring,
      Int.add_mul_ediv_right _ _ (by decide)]
    omega
  have hmin (n : ℤ) : min 0 (-n) = min n 0 - n := by
    by_cases h : n ≤ 0
    · rw [min_eq_left h, min_eq_left (by omega : 0 ≤ -n), sub_self]
    · rw [min_eq_right (by omega : 0 ≤ n), min_eq_right (by omega : -n ≤ 0), zero_sub]
  have hmax (n : ℤ) : max (-n) 0 = max n 0 - n := by
    by_cases h : n ≤ 0
    · rw [max_eq_right h, max_eq_left (by omega : 0 ≤ -n), zero_sub]
    · rw [max_eq_left (by omega : 0 ≤ n), max_eq_right (by omega : -n ≤ 0), sub_self]
  have hbackground : stairEvenAltBackground den (den + 1 - row, col) + correction = value := by
    dsimp only [stairEvenAltBackground, correction, value]
    rw [show 2 - (den + 1 - row) = -(den - row - 1) by omega,
      show den - 2 + (den + 1 - row) = 2 * den - 1 - row by omega,
      show den + 1 - row + col - 2 = -(row - col - den + 1) by omega, hmin, hmax,
      min_comm 0 (2 * den - 1 - row)]
    omega
  have hbump : StairEvenAltBump den (den + 1 - row, col) ↔ special ∨ diagonal := by
    simp only [StairEvenAltBump, special, diagonal]
    omega
  have hentry := ((mem_maskedTile_sites _ _ _ _).mp hmem).2.2
  change (entry .stairOddAlt den (col, row)).isSome at hentry
  apply Option.get_of_eq_some
  change entry .stairOddAlt den (col, row) = some (stairEvenAltBackground den (den + 1 - row, col) +
    (if StairEvenAltBump den (den + 1 - row, col) then 1 else 0) + correction)
  rw [add_right_comm, hbackground, if_congr hbump rfl rfl]
  have hrule : entry .stairOddAlt den (col, row) =
      if special then some (value + 1)
      else if rail then some value
      else if diagonal then some (value + 1)
      else if 0 ≤ col ∧ col ≤ den ∧ -1 ≤ row - col ∧ row - col ≤ 2 * den - 1 then some value
      else none := rfl
  rw [hrule] at hentry ⊢
  by_cases hspecial : special
  · simp only [if_pos hspecial, if_pos (Or.inl hspecial : special ∨ diagonal)]
  · by_cases hrail : rail
    · have hno : ¬ diagonal := by dsimp [diagonal, rail] at hrail ⊢; omega
      simp only [if_neg hspecial, if_pos hrail, if_neg (not_or.mpr ⟨hspecial, hno⟩), add_zero]
    · by_cases hdiagonal : diagonal
      · simp only [if_neg hspecial, if_neg hrail, if_pos hdiagonal,
          if_pos (Or.inr hdiagonal : special ∨ diagonal)]
      · simp only [if_neg hspecial, if_neg hrail, if_neg hdiagonal] at hentry
        simp only [if_neg hspecial, if_neg hrail, if_neg hdiagonal,
          if_pos (Option.isSome_ite.mp hentry), if_neg (not_or.mpr ⟨hspecial, hdiagonal⟩), add_zero]

theorem stairOddAlt_llCenter_agrees {den : ℤ} (hden : stairOddAlt.Valid den) {field : Field}
    (hagree : (stairOddAlt.raw den).Agrees field 0) :
    ((stairOddAlt.tile den hden).llCenter (stairOddAlt.tile_nonempty den hden)).Agrees
      (fun site => field (site + (0, 1))) 0 := by
  have hmin := hden.1
  apply hagree.llCenter_trim (stairOddAlt.raw_nonempty den hden)
  · apply (mem_stairOddAlt_raw_pullback_iff hmin _).mpr
    apply mem_stairEvenAlt_raw_iff.mpr
    dsimp
    omega
  · intro site hmem
    have hbounds := (mem_maskedTile_sites _ _ _ site).mp hmem
    have hrow : 1 ≤ site.2 := hbounds.2.1.1
    refine ⟨hrow, ?_⟩
    intro htop
    have htop : 1 = site.2 := htop
    obtain ⟨_, _, hshape⟩ := mem_stairEvenAlt_raw_iff.mp ((mem_stairOddAlt_raw_pullback_iff hmin _).mp hmem)
    dsimp at hshape ⊢
    omega

/-- The standard raw staircase domains are related by the specified quarter-turn. -/
theorem mem_stairOdd_raw_iff {den : ℤ} (point : Site) :
    QuarterTurn.counterclockwise.mapSite (den + 1, den - 1) point ∈ (stairOdd.raw den).sites ↔
      point ∈ (stairEven.raw den).sites := by
  obtain ⟨col, row⟩ := point
  simp only [raw, mem_maskedTile_sites, window, QuarterTurn.mapSite, QuarterTurn.turn,
    Prod.fst_add, Prod.snd_add, entry, isSome_ite_some, StairEvenCorner, Option.isSome_none, Bool.false_eq_true,
    or_false]
  omega

/-- The alternate quarter-turn carries the body and the two rails, with
the alternate initializer's own translation. -/
theorem mem_stairOddAlt_raw_iff {den : ℤ} (point : Site) :
    QuarterTurn.counterclockwise.mapSite (den, 2 * den - 3) point ∈ (stairOddAlt.raw den).sites ↔
      point ∈ (stairEvenAlt.raw den).sites := by
  obtain ⟨col, row⟩ := point
  simp only [raw, mem_maskedTile_sites, window, QuarterTurn.mapSite, QuarterTurn.turn,
    Prod.fst_add, Prod.snd_add, entry, isSome_ite_some, Option.isSome_none, Bool.false_eq_true,
    or_false]
  omega

theorem mem_ladderOdd_body {den : ℤ} {point : Site}
    (hx : 2 - den ≤ point.1 ∧ point.1 ≤ 2 * den)
    (hy : 0 ≤ point.2 ∧ point.2 ≤ den + 2)
    (hband : 1 ≤ point.1 + point.2 ∧ point.1 + point.2 ≤ 2 * den + 3)
    (hstrip : ¬ ((point.2 = 0 ∧ den ≤ point.1) ∨ (point.2 = den + 2 ∧ point.1 ≤ 2))) :
    point ∈ (ladderOdd.raw den).sites := by
  rw [raw, mem_maskedTile_sites]
  refine ⟨hx, hy, ?_⟩
  obtain ⟨col, row⟩ := point
  simp only [entry, isSome_ite_some, Option.isSome_none, Bool.false_eq_true, or_false]
  exact Or.inr ⟨hband.1, hband.2, hstrip⟩

theorem mem_ladderOddAlt_placed_body {den : ℤ} {point : Site}
    (hx : 2 - den ≤ point.1 ∧ point.1 ≤ 2 * den - 1)
    (hy : 0 ≤ point.2 ∧ point.2 ≤ den + 3)
    (hband : 1 ≤ point.1 + point.2 ∧ point.1 + point.2 ≤ 2 * den + 3)
    (hstrip : ¬ ((point.2 ≤ 1 ∧ den + 1 ≤ point.1) ∨ (den + 2 ≤ point.2 ∧ point.1 ≤ 0))) :
    point ∈ ((ladderOddAlt.raw den).place (1, 1) 0).sites := by
  rw [HeightTile.mem_place_sites, raw, mem_maskedTile_sites]
  obtain ⟨col, row⟩ := point
  simp only [window, Prod.mk_sub_mk, entry, isSome_ite_iff, Option.isSome_some, Option.isSome_none,
    Bool.false_eq_true, and_true, and_false, or_false]
  omega

theorem zero_mem_ladderOddAlt_placed {den : ℤ} (hden : 4 ≤ den) :
    (0 : Site) ∈ ((ladderOddAlt.raw den).place (1, 1) 0).sites := by
  rw [HeightTile.mem_place_sites, raw, mem_maskedTile_sites]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · change 1 - den ≤ -1
    omega
  · change -1 ≤ 2 * den - 2
    omega
  · change (-1 : ℤ) ≤ -1
    decide
  · change -1 ≤ den + 2
    omega
  · simp only [entry]
    rw [if_pos (Or.inl ⟨rfl, rfl⟩)]
    rfl

theorem mem_ladderEven_raw_iff {den : ℤ} (point : Site) :
    QuarterTurn.counterclockwise.mapSite (den + 1, den - 1) point ∈ (ladderEven.raw den).sites ↔
      point ∈ (ladderOdd.raw den).sites := by
  obtain ⟨col, row⟩ := point
  simp only [raw, mem_maskedTile_sites, window, QuarterTurn.mapSite, QuarterTurn.turn,
    Prod.fst_add, Prod.snd_add, entry, isSome_ite_some, Option.isSome_none, Bool.false_eq_true,
    or_false]
  omega

theorem mem_ladderEvenAlt_raw_iff {den : ℤ} (point : Site) :
    QuarterTurn.counterclockwise.mapSite (den, den) point ∈ (ladderEvenAlt.raw den).sites ↔
      point ∈ (ladderOddAlt.raw den).sites := by
  obtain ⟨col, row⟩ := point
  simp only [raw, mem_maskedTile_sites, window, QuarterTurn.mapSite, QuarterTurn.turn,
    Prod.fst_add, Prod.snd_add, entry, isSome_ite_iff, Option.isSome_some, Option.isSome_none,
    Bool.false_eq_true, and_true, and_false, or_false]
  omega

end BaseMask

end FLatticePaper.Construction
