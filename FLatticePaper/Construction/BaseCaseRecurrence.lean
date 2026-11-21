import FLatticePaper.Construction.AlternateLadderRank
import FLatticePaper.Construction.AlternateStaircaseRank
import FLatticePaper.Construction.LadderCoverage
import FLatticePaper.Construction.LadderRank
import FLatticePaper.Construction.StaircaseCoverage
import FLatticePaper.Construction.StaircaseRank
import FLatticePaper.Plane.PeriodCocycle

/-! The Section 6 base cases in the paper's own notation, with the recurrence lemmas
`lemma:staircase_recurrent`, `lemma:alt-staircase-recurrent`, `lemma:doubled-staircase-recurrent` and
`lemma:doubled-alt-staircase-recurrent`. The paper tiles and heights are transcribed from the TeX, and each is
matched against the literal raw mask of the sparse constructor. -/

namespace FLatticePaper.Construction

open Farey

/-! ### Standard even staircase, `lemma:basecase_3k_even_std` (`paper/farey_recursion.tex` lines 2081–2092) -/

/-- The tile `T_{1/d}` of `lemma:basecase_3k_even_std`. -/
def paperStairTile (d : ℤ) : Set Site :=
  {x | 2 - d ≤ x.1 ∧ x.1 ≤ d ∧ 0 ≤ x.2 ∧ x.2 ≤ d + 1 ∧ 1 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ d + 2} ∪
    {(0, 0), (2, d + 1)}

/-- The height `g_{1/d}` of `lemma:basecase_3k_even_std`. -/
def paperStairValue (d : ℤ) (x : Site) : ℤ :=
  -(x.2 * (x.2 + 1) / 2) + (x.2 + min (x.1 - 1) 0) + if x = (0, 0) ∨ x = (2, d + 1) then 1 else 0

/-! ### Alternate even staircase, `lemma:basecase_3k_even_alt` (lines 2221–2243) -/

/-- The set `A = {-(d-1)} × [-1,0] ∪ {3} × [d,d+1]` of `lemma:basecase_3k_even_alt`. -/
def paperStairAltA (d : ℤ) : Set Site :=
  {x : Site | x.1 = 1 - d ∧ -1 ≤ x.2 ∧ x.2 ≤ 0} ∪ {x : Site | x.1 = 3 ∧ d ≤ x.2 ∧ x.2 ≤ d + 1}

/-- The set `B = {(x_1, x_2) : x_1 + x_2 = 2 and 0 < x_2 < d}` of `lemma:basecase_3k_even_alt`. -/
def paperStairAltB (d : ℤ) : Set Site :=
  {x : Site | x.1 + x.2 = 2 ∧ 0 < x.2 ∧ x.2 < d}

/-- The set `C = [1-d, 0] × {-1} ∪ [4-d, 3] × {d+1}` of `lemma:basecase_3k_even_alt`. -/
def paperStairAltC (d : ℤ) : Set Site :=
  {x : Site | 1 - d ≤ x.1 ∧ x.1 ≤ 0 ∧ x.2 = -1} ∪ {x : Site | 4 - d ≤ x.1 ∧ x.1 ≤ 3 ∧ x.2 = d + 1}

/-- The set `D = {(x_1, x_2) ∈ [4-2d, d] × [0, d] : -d + 2 ≤ x_1 + x_2 ≤ d + 2}` of `lemma:basecase_3k_even_alt`. -/
def paperStairAltD (d : ℤ) : Set Site :=
  {x : Site | 4 - 2 * d ≤ x.1 ∧ x.1 ≤ d ∧ 0 ≤ x.2 ∧ x.2 ≤ d ∧ -d + 2 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ d + 2}

/-- The tile `\hat T_{1/d} = A ∪ B ∪ C ∪ D` of `lemma:basecase_3k_even_alt`. -/
def paperStairAltTile (d : ℤ) : Set Site :=
  paperStairAltA d ∪ paperStairAltB d ∪ paperStairAltC d ∪ paperStairAltD d

/-- The height `\hat g_{1/d}` on `\hat T_{1/d}` in `lemma:basecase_3k_even_alt`, with `1_{A ∪ B}`. -/
noncomputable def paperStairAltValue (d : ℤ) (x : Site) : ℤ :=
  -(x.2 * (x.2 + 1) / 2) + min 0 (2 - x.1) + min 0 (d - 2 + x.1) + max (x.1 + x.2 - 2) 0 +
    (paperStairAltA d ∪ paperStairAltB d).indicator (fun _ => (1 : ℤ)) x

/-! ### Standard odd doubled staircase, `lemma:basecase_3k_odd_std` (lines 2375–2392) -/

/-- The set `A = (0,0) ∪ (d+2,d+2)` of `lemma:basecase_3k_odd_std`. -/
def paperLadderA (d : ℤ) : Set Site := {(0, 0), (d + 2, d + 2)}

/-- The set `B = {(x_1, x_2) : x_1 + x_2 = d+2 and 1 < x_2 < d+1}` of `lemma:basecase_3k_odd_std`. -/
def paperLadderB (d : ℤ) : Set Site :=
  {x : Site | x.1 + x.2 = d + 2 ∧ 1 < x.2 ∧ x.2 < d + 1}

/-- The set `C = {(x_1, x_2) ∈ [-d+2, 2d] × [0, d+2] : 1 ≤ x_1 + x_2 ≤ 2d+3}` of `lemma:basecase_3k_odd_std`. -/
def paperLadderC (d : ℤ) : Set Site :=
  {x : Site | -d + 2 ≤ x.1 ∧ x.1 ≤ 2 * d ∧ 0 ≤ x.2 ∧ x.2 ≤ d + 2 ∧ 1 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ 2 * d + 3}

/-- The set `D = {x_1 ≥ d and x_2 = 0} ∪ {x_1 ≤ 2 and x_2 = d+2}` of `lemma:basecase_3k_odd_std`. -/
def paperLadderD (d : ℤ) : Set Site :=
  {x : Site | d ≤ x.1 ∧ x.2 = 0} ∪ {x : Site | x.1 ≤ 2 ∧ x.2 = d + 2}

/-- The tile `T_{1/d} = (A ∪ B ∪ C) \ D` of `lemma:basecase_3k_odd_std`. -/
def paperLadderTile (d : ℤ) : Set Site :=
  (paperLadderA d ∪ paperLadderB d ∪ paperLadderC d) \ paperLadderD d

/-- The height `g_{1/d}` of `lemma:basecase_3k_odd_std`, with `1_{A ∪ B}`. -/
noncomputable def paperLadderValue (d : ℤ) (x : Site) : ℤ :=
  -(x.2 * (x.2 + 1) / 2) + (x.2 + min (x.1 - 1) 0) + min 0 (d + 1 - x.1) +
    max (x.1 + x.2 - d - 2) 0 + (paperLadderA d ∪ paperLadderB d).indicator (fun _ => (1 : ℤ)) x

/-! ### Alternate odd doubled staircase, `lemma:basecase_3k_odd_alt` (lines 2429–2450) -/

/-- The set `A = (-1,-1) ∪ (d,d+2)` of `lemma:basecase_3k_odd_alt`. -/
def paperLadderAltA (d : ℤ) : Set Site := {(-1, -1), (d, d + 2)}

/-- The set `B = {(x_1, x_2) : x_1 + x_2 = d and 0 < x_1 < d-1}` of `lemma:basecase_3k_odd_alt`. -/
def paperLadderAltB (d : ℤ) : Set Site :=
  {x : Site | x.1 + x.2 = d ∧ 0 < x.1 ∧ x.1 < d - 1}

/-- The set `C = {(x_1, x_2) ∈ [-d+1, 2d-2] × [-1, d+2] : -1 ≤ x_1 + x_2 ≤ 2d+1}` of `lemma:basecase_3k_odd_alt`. -/
def paperLadderAltC (d : ℤ) : Set Site :=
  {x : Site | 1 - d ≤ x.1 ∧ x.1 ≤ 2 * d - 2 ∧ -1 ≤ x.2 ∧ x.2 ≤ d + 2 ∧ -1 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ 2 * d + 1}

/-- The set `D = {x_1 ≥ d and x_2 ∈ [-1,0]} ∪ {x_1 ≤ -1 and x_2 ∈ [d+1,d+2]}` of `lemma:basecase_3k_odd_alt`. -/
def paperLadderAltD (d : ℤ) : Set Site :=
  {x : Site | d ≤ x.1 ∧ -1 ≤ x.2 ∧ x.2 ≤ 0} ∪ {x : Site | x.1 ≤ -1 ∧ d + 1 ≤ x.2 ∧ x.2 ≤ d + 2}

/-- The tile `\hat T_{1/d} = (A ∪ B ∪ C) \ D` of `lemma:basecase_3k_odd_alt`. -/
def paperLadderAltTile (d : ℤ) : Set Site :=
  (paperLadderAltA d ∪ paperLadderAltB d ∪ paperLadderAltC d) \ paperLadderAltD d

/-- The height `\hat g_{1/d}` of `lemma:basecase_3k_odd_alt`, with `1_{A ∪ B}`. -/
noncomputable def paperLadderAltValue (d : ℤ) (x : Site) : ℤ :=
  -(x.2 * (x.2 + 1) / 2) + min 0 x.1 + min 0 (d - x.1 - 1) + max (x.1 + x.2 - d) 0 +
    (paperLadderAltA d ∪ paperLadderAltB d).indicator (fun _ => (1 : ℤ)) x

/-! ### Helpers -/

/-- A field that agrees with a raw tile at gauge zero takes the paper value on the paper tile. -/
private theorem paper_agrees {tile : Set Site} {raw : HeightTile Site} {value : Site → ℤ}
    {field : Field} (hmem : ∀ x, x ∈ tile ↔ x ∈ raw.sites)
    (hheight : ∀ x (hx : x ∈ raw.sites), raw.height ⟨x, hx⟩ = value x)
    (hagree : raw.Agrees field 0) : ∀ x ∈ tile, field x = value x := by
  intro x hx
  have hx' : x ∈ raw.sites := (hmem x).mp hx
  have h1 : raw.height ⟨x, hx'⟩ = field x + 0 := hagree ⟨x, hx'⟩
  have h2 : raw.height ⟨x, hx'⟩ = value x := hheight x hx'
  omega

/-- Two fields with the same generator periods that agree on the covered raw sites are equal. -/
private theorem paper_eq {fraction : Fraction} (hinterval : fraction.InUnitInterval)
    {tile : Set Site} {raw : HeightTile Site} {value : Site → ℤ} {field other : Field}
    {constantU constantV : ℤ} (hmem : ∀ x, x ∈ tile ↔ x ∈ raw.sites)
    (hcover : fraction.modifiedDeck.Covers raw.sites)
    (hfield : ∀ x ∈ tile, field x = value x) (hfieldP : HasGeneratorPeriods fraction field constantU constantV)
    (hother : ∀ x ∈ tile, other x = value x)
    (hotherP : HasGeneratorPeriods fraction other constantU constantV) : other = field :=
  eq_of_covered_generator_periods hinterval hotherP hfieldP hcover fun site hsite => by
    rw [hother site ((hmem site).mpr hsite), hfield site ((hmem site).mpr hsite)]

/-- The fraction `1/d` lies in the unit interval for `d ≥ 1`. -/
private theorem interval_mk_one (d : ℤ) (hd : 1 ≤ d) : (Fraction.mk 1 d).InUnitInterval :=
  ⟨by dsimp; omega, by change (0 : ℤ) ≤ 1; decide, by dsimp; omega⟩

/-- An indicator of a set with a pointwise description is the corresponding `if`. -/
private theorem indicator_eq_ite {S : Set Site} {P : Site → Prop} (hS : ∀ y, y ∈ S ↔ P y)
    (x : Site) [Decidable (P x)] :
    S.indicator (fun _ => (1 : ℤ)) x = if P x then 1 else 0 := by
  by_cases hp : P x
  · rw [Set.indicator_of_mem ((hS x).mpr hp), if_pos hp]
  · rw [Set.indicator_of_notMem (fun h => hp ((hS x).mp h)), if_neg hp]

/-! ### Standard even staircase -/

theorem mem_paperStairTile_iff (d : ℤ) (hd : 3 ≤ d) (x : Site) :
    x ∈ paperStairTile d ↔ x ∈ (BaseMask.stairEven.raw d).sites := by
  rw [BaseMask.mem_stairEven_raw_iff]
  obtain ⟨a, b⟩ := x
  simp only [paperStairTile, Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff, Prod.mk.injEq, BaseMask.StairEvenCorner]
  constructor <;> intro h <;> omega

theorem paperStairValue_eq_stairEvenValue (d : ℤ) (x : Site) :
    paperStairValue d x = BaseMask.stairEvenValue d x := by
  obtain ⟨a, b⟩ := x
  have h : b * (b + 1) = b * (b - 1) + 2 * b := by ring
  simp only [paperStairValue, BaseMask.stairEvenValue, BaseMask.StairEvenCorner, Prod.mk.injEq]
  split_ifs <;> omega

theorem stairEven_height_paper (d : ℤ) (x : Site) (hx : x ∈ (BaseMask.stairEven.raw d).sites) :
    (BaseMask.stairEven.raw d).height ⟨x, hx⟩ = paperStairValue d x :=
  (BaseMask.stairEven_raw_height d ⟨x, hx⟩).trans (paperStairValue_eq_stairEvenValue d x).symm

/-- `lemma:staircase_recurrent`. -/
theorem staircase_recurrent {d : ℤ} (hd : 3 ≤ d ∧ d % 2 = 1) :
    ∃ constantU constantV : ℤ, ∃ field : Field,
      (∀ x ∈ paperStairTile d, field x = paperStairValue d x) ∧
      HasGeneratorPeriods (Fraction.mk 1 d) field constantU constantV ∧
      Superharmonic field ∧ Recurrent field ∧
      ∀ other : Field, (∀ x ∈ paperStairTile d, other x = paperStairValue d x) →
        HasGeneratorPeriods (Fraction.mk 1 d) other constantU constantV → other = field := by
  have hden : BaseMask.stairEven.Valid d := hd
  obtain ⟨field, hagree, hperiod, _, hsuper, hrec⟩ := stairEven_exists_recurrent_extension hden
  have hfield := paper_agrees (mem_paperStairTile_iff d hd.1) (stairEven_height_paper d) hagree
  refine ⟨0, stairEvenConstantV d, field, hfield, hperiod, hsuper, hrec, ?_⟩
  intro other hother hotherP
  exact paper_eq (interval_mk_one d (by omega)) (mem_paperStairTile_iff d hd.1)
    (stairEven_raw_cover hden) hfield hperiod hother hotherP

/-! ### Alternate even staircase -/

theorem mem_paperStairAltTile_iff (d : ℤ) (hd : 3 ≤ d) (x : Site) :
    x ∈ paperStairAltTile d ↔ x ∈ (BaseMask.stairEvenAlt.raw d).sites := by
  rw [BaseMask.mem_stairEvenAlt_raw_iff]
  obtain ⟨a, b⟩ := x
  simp only [paperStairAltTile, paperStairAltA, paperStairAltB, paperStairAltC, paperStairAltD,
    Set.mem_union, Set.mem_setOf_eq]
  constructor <;> intro h <;> omega

theorem mem_paperStairAltAB_iff (d : ℤ) (y : Site) :
    y ∈ paperStairAltA d ∪ paperStairAltB d ↔ BaseMask.StairEvenAltBump d y := by
  obtain ⟨a, b⟩ := y
  simp only [paperStairAltA, paperStairAltB, BaseMask.StairEvenAltBump, Set.mem_union,
    Set.mem_setOf_eq]
  constructor <;> intro h <;> omega

theorem paperStairAltValue_eq (d : ℤ) (x : Site) :
    paperStairAltValue d x = BaseMask.stairEvenAltBackground d x +
      (if BaseMask.StairEvenAltBump d x then 1 else 0) := by
  unfold paperStairAltValue BaseMask.stairEvenAltBackground
  rw [indicator_eq_ite (mem_paperStairAltAB_iff d) x]

theorem stairEvenAlt_height_paper (d : ℤ) (x : Site) (hx : x ∈ (BaseMask.stairEvenAlt.raw d).sites) :
    (BaseMask.stairEvenAlt.raw d).height ⟨x, hx⟩ = paperStairAltValue d x :=
  (BaseMask.stairEvenAlt_raw_height d ⟨x, hx⟩).trans (paperStairAltValue_eq d x).symm

/-- `lemma:alt-staircase-recurrent`. -/
theorem alt_staircase_recurrent {d : ℤ} (hd : 3 ≤ d ∧ d % 2 = 1) :
    ∃ constantU constantV : ℤ, ∃ field : Field,
      (∀ x ∈ paperStairAltTile d, field x = paperStairAltValue d x) ∧
      HasGeneratorPeriods (Fraction.mk 1 d) field constantU constantV ∧
      Superharmonic field ∧ Recurrent field ∧
      ∀ other : Field, (∀ x ∈ paperStairAltTile d, other x = paperStairAltValue d x) →
        HasGeneratorPeriods (Fraction.mk 1 d) other constantU constantV → other = field := by
  have hden : BaseMask.stairEvenAlt.Valid d := hd
  obtain ⟨field, hagree, hperiod, _, hsuper, hrec⟩ := stairEvenAlt_exists_recurrent_extension hden
  have hfield := paper_agrees (mem_paperStairAltTile_iff d hd.1) (stairEvenAlt_height_paper d) hagree
  refine ⟨0, stairEvenConstantV d - 1, field, hfield, hperiod, hsuper, hrec, ?_⟩
  intro other hother hotherP
  exact paper_eq (interval_mk_one d (by omega)) (mem_paperStairAltTile_iff d hd.1)
    (stairEvenAlt_raw_cover hden) hfield hperiod hother hotherP

/-! ### Standard odd doubled staircase -/

theorem mem_paperLadderTile_iff (d : ℤ) (hd : 4 ≤ d) (x : Site) :
    x ∈ paperLadderTile d ↔ x ∈ (BaseMask.ladderOdd.raw d).sites := by
  rw [BaseMask.mem_ladderOdd_raw_iff]
  obtain ⟨a, b⟩ := x
  simp only [paperLadderTile, paperLadderA, paperLadderB, paperLadderC, paperLadderD,
    Set.mem_sdiff, Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
    Prod.mk.injEq, BaseMask.LadderOddCorner, not_or]
  constructor <;> intro h <;> omega

theorem mem_paperLadderAB_iff (d : ℤ) (y : Site) :
    y ∈ paperLadderA d ∪ paperLadderB d ↔ BaseMask.LadderOddBump d y := by
  obtain ⟨a, b⟩ := y
  simp only [paperLadderA, paperLadderB, BaseMask.LadderOddBump, Set.mem_union,
    Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
  constructor <;> intro h <;> omega

theorem paperLadderValue_eq (d : ℤ) (x : Site) :
    paperLadderValue d x = BaseMask.ladderOddValue d x := by
  unfold paperLadderValue BaseMask.ladderOddValue
  rw [indicator_eq_ite (mem_paperLadderAB_iff d) x]
  obtain ⟨a, b⟩ := x
  dsimp only
  have h : b * (b + 1) = b * (b - 1) + 2 * b := by ring
  split_ifs <;> omega

theorem ladderOdd_height_paper (d : ℤ) (x : Site) (hx : x ∈ (BaseMask.ladderOdd.raw d).sites) :
    (BaseMask.ladderOdd.raw d).height ⟨x, hx⟩ = paperLadderValue d x :=
  (BaseMask.ladderOdd_raw_height d ⟨x, hx⟩).trans (paperLadderValue_eq d x).symm

/-- `lemma:doubled-staircase-recurrent`. -/
theorem doubled_staircase_recurrent {d : ℤ} (hd : 4 ≤ d ∧ d % 2 = 0) :
    ∃ constantU constantV : ℤ, ∃ field : Field,
      (∀ x ∈ paperLadderTile d, field x = paperLadderValue d x) ∧
      HasGeneratorPeriods (Fraction.mk 1 d) field constantU constantV ∧
      Superharmonic field ∧ Recurrent field ∧
      ∀ other : Field, (∀ x ∈ paperLadderTile d, other x = paperLadderValue d x) →
        HasGeneratorPeriods (Fraction.mk 1 d) other constantU constantV → other = field := by
  have hden : BaseMask.ladderOdd.Valid d := hd
  obtain ⟨field, hagree, hperiod, _, hsuper, hrec⟩ := ladderOdd_exists_recurrent_extension hden
  have hfield := paper_agrees (mem_paperLadderTile_iff d hd.1) (ladderOdd_height_paper d) hagree
  refine ⟨0, stairEvenConstantV d, field, hfield, hperiod, hsuper, hrec, ?_⟩
  intro other hother hotherP
  exact paper_eq (interval_mk_one d (by omega)) (mem_paperLadderTile_iff d hd.1)
    (ladderOdd_raw_cover hden) hfield hperiod hother hotherP

/-! ### Alternate odd doubled staircase -/

theorem mem_paperLadderAltTile_iff (d : ℤ) (hd : 4 ≤ d) (x : Site) :
    x ∈ paperLadderAltTile d ↔ x ∈ (BaseMask.ladderOddAlt.raw d).sites := by
  rw [BaseMask.mem_ladderOddAlt_raw_iff]
  obtain ⟨a, b⟩ := x
  simp only [paperLadderAltTile, paperLadderAltA, paperLadderAltB, paperLadderAltC,
    paperLadderAltD, Set.mem_sdiff, Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff, Prod.mk.injEq, BaseMask.LadderOddAltCorner, not_or]
  constructor <;> intro h <;> omega

theorem mem_paperLadderAltAB_iff (d : ℤ) (y : Site) :
    y ∈ paperLadderAltA d ∪ paperLadderAltB d ↔
      BaseMask.LadderOddAltCorner d y ∨ BaseMask.LadderOddAltDiagonal d y := by
  obtain ⟨a, b⟩ := y
  simp only [paperLadderAltA, paperLadderAltB, BaseMask.LadderOddAltCorner,
    BaseMask.LadderOddAltDiagonal, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_setOf_eq, Prod.mk.injEq]

theorem paperLadderAltValue_eq (d : ℤ) (x : Site) :
    paperLadderAltValue d x = BaseMask.ladderOddAltValue d x := by
  unfold paperLadderAltValue BaseMask.ladderOddAltValue
  rw [indicator_eq_ite (mem_paperLadderAltAB_iff d) x]
  obtain ⟨a, b⟩ := x
  split_ifs <;> omega

theorem ladderOddAlt_height_paper (d : ℤ) (x : Site) (hx : x ∈ (BaseMask.ladderOddAlt.raw d).sites) :
    (BaseMask.ladderOddAlt.raw d).height ⟨x, hx⟩ = paperLadderAltValue d x :=
  (BaseMask.ladderOddAlt_raw_height d ⟨x, hx⟩).trans (paperLadderAltValue_eq d x).symm

/-- `lemma:doubled-alt-staircase-recurrent`. -/
theorem doubled_alt_staircase_recurrent {d : ℤ} (hd : 4 ≤ d ∧ d % 2 = 0) :
    ∃ constantU constantV : ℤ, ∃ field : Field,
      (∀ x ∈ paperLadderAltTile d, field x = paperLadderAltValue d x) ∧
      HasGeneratorPeriods (Fraction.mk 1 d) field constantU constantV ∧
      Superharmonic field ∧ Recurrent field ∧
      ∀ other : Field, (∀ x ∈ paperLadderAltTile d, other x = paperLadderAltValue d x) →
        HasGeneratorPeriods (Fraction.mk 1 d) other constantU constantV → other = field := by
  have hden : BaseMask.ladderOddAlt.Valid d := hd
  obtain ⟨field, hagree, hperiod, _, hsuper, hrec⟩ := ladderOddAlt_exists_recurrent_extension hden
  have hfield := paper_agrees (mem_paperLadderAltTile_iff d hd.1) (ladderOddAlt_height_paper d) hagree
  refine ⟨-1, ladderOddAltConstantV d, field, hfield, hperiod, hsuper, hrec, ?_⟩
  intro other hother hotherP
  exact paper_eq (interval_mk_one d (by omega)) (mem_paperLadderAltTile_iff d hd.1)
    (ladderOddAlt_raw_cover hden) hfield hperiod hother hotherP

end FLatticePaper.Construction
