import FLatticePaper.Construction.Placement
import FLatticePaper.Plane.QuarterTurn
import Mathlib.Data.Int.Interval

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
