import FLatticePaper.Construction.StaircaseExtension

namespace FLatticePaper.Construction

open Farey

def staircaseLevel (den : ℤ) (point : Site) : ℤ := point.1 - den * point.2

/-- B3 adds one on the `d-1` transverse classes through its inner diagonal. -/
def stairEvenAltMarker (den : ℤ) (point : Site) : ℤ :=
  let period := (Fraction.mk 1 den).periodDenominator
  if ∃ row ∈ Finset.Ico (1 : ℤ) den,
      staircaseLevel den point % period = (2 - (den + 1) * row) % period then 1 else 0

theorem stairEvenAltMarker_periodic {den : ℤ} {offset : Site}
    (hoffset : offset ∈ (reciprocalEvenDeck den).span) :
    Function.Periodic (stairEvenAltMarker den) offset := by
  obtain ⟨i, j, rfl⟩ := hoffset
  intro point
  let fraction := Fraction.mk 1 den
  change stairEvenAltMarker den (point + fraction.modifiedDeck.combine i j) = _
  have hgrade : fraction.transverseGrade (fraction.modifiedDeck.combine i j) = fraction.periodDenominator * j := by
    rw [Fraction.modifiedDeck_combine, Fraction.transverseGrade_combine]
  have hlevel : staircaseLevel den (point + fraction.modifiedDeck.combine i j) =
      staircaseLevel den point + (-j) * fraction.periodDenominator := by
    change (den * (fraction.modifiedDeck.combine i j).2 - 1 * (fraction.modifiedDeck.combine i j).1) = _ at hgrade
    simp only [staircaseLevel, Prod.fst_add, Prod.snd_add]
    linear_combination -hgrade
  unfold stairEvenAltMarker
  change (if ∃ row ∈ Finset.Ico (1 : ℤ) den,
      staircaseLevel den (point + fraction.modifiedDeck.combine i j) % fraction.periodDenominator =
        (2 - (den + 1) * row) % fraction.periodDenominator then 1 else 0) = _
  rw [hlevel, Int.add_mul_emod_self_right]

/-- The source B3 plane candidate: the reciprocal standard shifted by one
horizontal unit, with the indicated periodic correction. -/
def stairEvenAltField (den : ℤ) (standard : Field) : Field :=
  fun point => standard (point - (1, 0)) + stairEvenAltMarker den point

theorem stairEvenAltField_periods {den : ℤ} {standard : Field} {constantU constantV : ℤ}
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) standard constantU constantV) :
    HasGeneratorPeriods (Fraction.mk 1 den) (stairEvenAltField den standard) constantU (constantV - 1) := by
  let fraction := Fraction.mk 1 den
  let deck := fraction.modifiedDeck
  have hU : deck.kernel ∈ deck.span := ⟨1, 0, by apply Prod.ext <;> simp [PeriodDeck.combine]⟩
  have hV : deck.transverse ∈ deck.span := ⟨0, 1, by apply Prod.ext <;> simp [PeriodDeck.combine]⟩
  have hshift (point offset : Site) : point + offset - (1, 0) = (point - (1, 0)) + offset := by
    apply Prod.ext <;> dsimp <;> omega
  constructor
  · intro point
    change standard (point + deck.kernel - (1, 0)) + stairEvenAltMarker den (point + deck.kernel) = _
    rw [hshift, stairEvenAltMarker_periodic hU point, hperiod.1]
    unfold stairEvenAltField
    omega
  · intro point
    change standard (point + deck.transverse - (1, 0)) + stairEvenAltMarker den (point + deck.transverse) = _
    rw [hshift, stairEvenAltMarker_periodic hV point, hperiod.2]
    unfold stairEvenAltField
    have hgrade : fraction.transverseGrade (point - (1, 0)) = fraction.transverseGrade point + 1 := by
      simp only [fraction, Fraction.transverseGrade, Prod.fst_sub, Prod.snd_sub]
      ring
    rw [hgrade]
    dsimp only [fraction]
    omega

private theorem eq_of_emod_eq_of_within_period {period first second : ℤ} (hperiod : 0 < period)
    (hlo : second - period < first) (hhi : first < second + period)
    (hmod : first % period = second % period) : first = second := by
  have hdvd : period ∣ first - second := Int.dvd_iff_emod_eq_zero.mpr
    (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hmod)
  obtain ⟨index, hindex⟩ := hdvd
  by_contra hne
  have hindex_ne : index ≠ 0 := by
    intro heq
    rw [heq, mul_zero] at hindex
    omega
  by_cases hin : 0 < index
  · have h := mul_le_mul_of_nonneg_left (show 1 ≤ index by omega) hperiod.le
    rw [mul_one] at h
    omega
  · have h := mul_le_mul_of_nonneg_left (show index ≤ -1 by omega) hperiod.le
    rw [mul_neg, mul_one] at h
    omega

/-- The range containing both the occupied B3 levels and its left and lower
exit levels meets the marker classes only at their displayed levels. -/
theorem stairEvenAltMarker_eq_of_level_bounds {den : ℤ} (hmin : 3 ≤ den) (point : Site)
    (hlo : 3 - den - (Fraction.mk 1 den).periodDenominator ≤ staircaseLevel den point)
    (hhi : staircaseLevel den point ≤ 2 * den) :
    stairEvenAltMarker den point =
      if ∃ row ∈ Finset.Ico (1 : ℤ) den, staircaseLevel den point = 2 - (den + 1) * row then 1 else 0 := by
  unfold stairEvenAltMarker
  dsimp only
  apply if_congr ?_ rfl rfl
  constructor
  · rintro ⟨row, hrow, hmod⟩
    have hrow' := Finset.mem_Ico.mp hrow
    have hlow := mul_le_mul_of_nonneg_left (show row ≤ den - 1 by omega) (show 0 ≤ den + 1 by omega)
    have hhigh := mul_le_mul_of_nonneg_left hrow'.1 (show 0 ≤ den + 1 by omega)
    refine ⟨row, hrow, eq_of_emod_eq_of_within_period ?_ ?_ ?_ hmod⟩
    · simp only [Fraction.periodDenominator]
      nlinarith only [hmin, sq_nonneg (den - 1)]
    · rw [mul_one] at hhigh
      omega
    · simp only [Fraction.periodDenominator]
      nlinarith only [hmin, hlow, hhi]
  · rintro ⟨row, hrow, heq⟩
    exact ⟨row, hrow, congrArg (· % (Fraction.mk 1 den).periodDenominator) heq⟩

private theorem stairEvenAlt_level_bounds {den : ℤ} (hmin : 3 ≤ den) {point : Site}
    (hmem : point ∈ (BaseMask.stairEvenAlt.raw den).sites) :
    3 - (Fraction.mk 1 den).periodDenominator ≤ staircaseLevel den point ∧ staircaseLevel den point ≤ den := by
  obtain ⟨hx, _, hshape⟩ := BaseMask.mem_stairEvenAlt_raw_iff.mp hmem
  have hm (hy₀ : 0 ≤ point.2) (hyd : point.2 ≤ den) :
      3 - (Fraction.mk 1 den).periodDenominator ≤ staircaseLevel den point ∧ staircaseLevel den point ≤ den := by
    have hmulLo := mul_nonneg (by omega : 0 ≤ den) hy₀
    have hmulHi := mul_le_mul_of_nonneg_left hyd (by omega : 0 ≤ den)
    simp only [Fraction.periodDenominator, staircaseLevel]
    constructor <;> nlinarith only [hx.1, hx.2, hmulLo, hmulHi]
  rcases hshape with ⟨hlo, hhi, _⟩ | ⟨hrow, hleft, hright⟩ | ⟨hrow, hleft, hright⟩ |
      ⟨_, hrow⟩ | ⟨_, hrow⟩
  · exact hm hlo hhi
  · simp only [Fraction.periodDenominator, staircaseLevel, hrow]
    constructor <;> nlinarith only [hmin, hleft, hright, sq_nonneg den]
  · simp only [Fraction.periodDenominator, staircaseLevel, hrow]
    constructor <;> nlinarith only [hmin, hleft, hright, sq_nonneg den]
  · exact hm (by omega) (by omega)
  · exact hm (by omega) (by omega)

private abbrev MarkedSite (den : ℤ) (point : Site) : Prop :=
  (point.1 + point.2 = 2 ∧ 0 < point.2 ∧ point.2 < den) ∨
    (point.1 = 1 - den ∧ point.2 = 0) ∨ (point.1 = 3 ∧ point.2 = den)

/-- The periodic class indicator gives just the inner diagonal and the two
isolated corner bumps on the literal alternate support. -/
private theorem stairEvenAltMarker_on_raw {den : ℤ} (hmin : 3 ≤ den) {point : Site}
    (hmem : point ∈ (BaseMask.stairEvenAlt.raw den).sites) :
    stairEvenAltMarker den point = if MarkedSite den point then 1 else 0 := by
  obtain ⟨hlo, hhi⟩ := stairEvenAlt_level_bounds hmin hmem
  obtain ⟨_, _, hshape⟩ := BaseMask.mem_stairEvenAlt_raw_iff.mp hmem
  rw [stairEvenAltMarker_eq_of_level_bounds hmin point (by omega) (by omega)]
  apply if_congr ?_ rfl rfl
  constructor
  · rintro ⟨row, hrow, hlevel⟩
    have hrow' := Finset.mem_Ico.mp hrow
    let kernelIndex := point.2 - row
    have hsum : point.1 + point.2 = 2 + (den + 1) * kernelIndex := by
      unfold staircaseLevel at hlevel
      dsimp [kernelIndex]
      linear_combination hlevel
    have hbounds : -den ≤ point.1 + point.2 ∧ point.1 + point.2 ≤ den + 4 := by omega
    have hzero (h : kernelIndex = 0) : MarkedSite den point := by
      rw [h, mul_zero, add_zero] at hsum
      exact Or.inl ⟨hsum, by dsimp [kernelIndex] at h; omega, by dsimp [kernelIndex] at h; omega⟩
    have hminus (h : kernelIndex = -1) : MarkedSite den point := by
      rw [h, mul_neg, mul_one] at hsum
      have hrowEq : point.2 = row - 1 := by dsimp [kernelIndex] at h; omega
      omega
    have hplus (h : kernelIndex = 1) : MarkedSite den point := by
      rw [h, mul_one] at hsum
      have hrowEq : point.2 = row + 1 := by dsimp [kernelIndex] at h; omega
      omega
    have hklo : -1 ≤ kernelIndex := by
      by_contra! h
      have hmul := mul_le_mul_of_nonneg_left (show kernelIndex ≤ -2 by omega) (show 0 ≤ den + 1 by omega)
      nlinarith only [hbounds.1, hsum, hmul, hmin]
    have hkhi : kernelIndex ≤ 1 := by
      by_contra! h
      have hmul := mul_le_mul_of_nonneg_left (show 2 ≤ kernelIndex by omega) (show 0 ≤ den + 1 by omega)
      nlinarith only [hbounds.2, hsum, hmul, hmin]
    rcases (show kernelIndex = -1 ∨ kernelIndex = 0 ∨ kernelIndex = 1 by omega) with h | h | h
    · exact hminus h
    · exact hzero h
    · exact hplus h
  · rintro (⟨hsum, hlo, hhi⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩)
    · refine ⟨point.2, Finset.mem_Ico.mpr ⟨by omega, hhi⟩, ?_⟩
      unfold staircaseLevel
      linear_combination hsum
    · refine ⟨1, Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩, ?_⟩
      simp only [staircaseLevel, hx, hy, mul_zero, mul_one]
      omega
    · refine ⟨den - 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
      simp only [staircaseLevel, hx, hy]
      ring

private abbrev RailCorner (den : ℤ) (point : Site) : Prop :=
  (point.1 = 1 - den ∧ point.2 = -1) ∨ (point.1 = 3 ∧ point.2 = den + 1)

private theorem chooseTwo_succ (row : ℤ) : chooseTwo (row + 1) = chooseTwo row + row := by
  simpa [chooseTwo] using chooseTwo_add row 1

private theorem triangular_succ (row : ℤ) : row * (row + 1) / 2 = chooseTwo (row + 1) := by
  unfold chooseTwo
  rw [show row * (row + 1) = (row + 1) * (row + 1 - 1) by ring]

/-- Evaluate the shifted B1 field using the actual representatives specified
in the B3 height proof. Only the two rail corners retain a B1 bump. -/
private theorem shifted_standard_on_alternate_raw {den : ℤ} (hden : BaseMask.stairEvenAlt.Valid den)
    {standard : Field} (hstandard : (BaseMask.stairEven.raw den).Agrees standard 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) standard 0 (stairEvenConstantV den))
    (point : Site) (hmem : point ∈ (BaseMask.stairEvenAlt.raw den).sites) :
    standard (point - (1, 0)) = BaseMask.stairEvenAltBackground den point +
      (if RailCorner den point then 1 else 0) := by
  have hmin := hden.1
  have hvalue (x y : ℤ) (hpoint : (x, y) ∈ (BaseMask.stairEven.raw den).sites) :
      standard (x, y) = -chooseTwo y + min (x - 1) 0 +
        (if BaseMask.StairEvenCorner den (x, y) then 1 else 0) := by
    have heq := hstandard ⟨(x, y), hpoint⟩
    rw [BaseMask.stairEven_raw_height] at heq
    simpa only [BaseMask.stairEvenValue, chooseTwo, add_zero] using heq.symm
  have hkernel (x y : ℤ) : standard (x - 1, y) = standard (x + den - 1, y + 1) := by
    have h := hperiod.1 (x - 1, y)
    change standard ((x - 1, y) + (reciprocalEvenDeck den).kernel) = _ at h
    rw [reciprocalEvenDeck_eq hden.2, add_zero] at h
    change standard (x - 1 + den, y + 1) = standard (x - 1, y) at h
    simpa only [show x - 1 + den = x + den - 1 by omega] using h.symm
  obtain ⟨x, y⟩ := point
  obtain ⟨hx, hy, hshape⟩ := BaseMask.mem_stairEvenAlt_raw_iff.mp hmem
  simp only [BaseMask.stairEvenAltBackground, Prod.mk_sub_mk, sub_zero, triangular_succ]
  rcases hshape with hbody | ⟨hyb, hleft, hright⟩ | ⟨hyt, hleft, hright⟩ |
    ⟨hxl, hyl⟩ | ⟨hxr, hyr⟩
  · have hrail : ¬ RailCorner den (x, y) := by dsimp at hbody ⊢; omega
    rw [if_neg hrail, add_zero]
    by_cases hsum : 2 ≤ x + y
    · by_cases hcorner : x = 2 - den ∧ y = den
      · obtain ⟨hcx, hcy⟩ := hcorner
        subst x
        subst y
        have hp : (1, den + 1) ∈ (BaseMask.stairEven.raw den).sites := by
          apply BaseMask.mem_stairEven_body <;> dsimp <;> omega
        rw [hkernel, show 2 - den + den - 1 = 1 by omega, hvalue _ _ hp]
        have hno : ¬ BaseMask.StairEvenCorner den (1, den + 1) := by simp [BaseMask.StairEvenCorner]
        simp only [if_neg hno, sub_self, min_self, add_zero]
        rw [min_eq_left (by omega : 0 ≤ 2 - (2 - den)),
          show den - 2 + (2 - den) = 0 by omega, show 2 - den + den - 2 = 0 by omega,
          min_self, max_self]
        omega
      · have hp : (x - 1, y) ∈ (BaseMask.stairEven.raw den).sites := by
          apply BaseMask.mem_stairEven_body <;> dsimp at * <;> omega
        have hno : ¬ BaseMask.StairEvenCorner den (x - 1, y) := by
          simp only [BaseMask.StairEvenCorner]
          dsimp at hbody
          omega
        rw [hvalue _ _ hp, if_neg hno, add_zero, chooseTwo_succ,
          min_eq_left (by dsimp at hbody; omega : 0 ≤ den - 2 + x),
          max_eq_left (by omega : 0 ≤ x + y - 2), show x - 1 - 1 = x - 2 by omega]
        by_cases h : x ≤ 2
        · rw [min_eq_left (by omega : x - 2 ≤ 0), min_eq_left (by omega : 0 ≤ 2 - x)]
          omega
        · rw [min_eq_right (by omega : 0 ≤ x - 2), min_eq_right (by omega : 2 - x ≤ 0)]
          omega
    · have hp : (x + den - 1, y + 1) ∈ (BaseMask.stairEven.raw den).sites := by
        apply BaseMask.mem_stairEven_body <;> dsimp at * <;> omega
      have hno : ¬ BaseMask.StairEvenCorner den (x + den - 1, y + 1) := by
        simp only [BaseMask.StairEvenCorner]
        dsimp at hbody
        omega
      rw [hkernel, hvalue _ _ hp, if_neg hno, add_zero,
        min_eq_left (by dsimp at hbody; omega : 0 ≤ 2 - x), max_eq_right (by omega : x + y - 2 ≤ 0),
        show x + den - 1 - 1 = den - 2 + x by omega, min_comm (den - 2 + x) 0]
      omega
  · have hyb : y = -1 := hyb
    subst y
    have hp : (x + den - 1, (0 : ℤ)) ∈ (BaseMask.stairEven.raw den).sites := by
      apply BaseMask.mem_stairEven_raw_iff.mpr
      simp only [BaseMask.StairEvenCorner]
      dsimp at *
      simp only [and_true]
      omega
    rw [hkernel, show (-1 : ℤ) + 1 = 0 by decide, hvalue _ _ hp]
    simp only [RailCorner, BaseMask.StairEvenCorner, show chooseTwo 0 = 0 from rfl, and_true]
    rw [min_eq_left (by dsimp at hright; omega : 0 ≤ 2 - x),
      max_eq_right (by dsimp at hright; omega : x + -1 - 2 ≤ 0),
      show x + den - 1 - 1 = den - 2 + x by omega, min_comm (den - 2 + x) 0]
    split <;> split <;> omega
  · have hyt : y = den + 1 := hyt
    subst y
    have hp : (x - 1, den + 1) ∈ (BaseMask.stairEven.raw den).sites := by
      apply BaseMask.mem_stairEven_raw_iff.mpr
      simp only [BaseMask.StairEvenCorner]
      dsimp at *
      simp only [and_true]
      omega
    rw [hvalue _ _ hp, chooseTwo_succ (den + 1), min_eq_left (by dsimp at hleft; omega : 0 ≤ den - 2 + x),
      max_eq_left (by dsimp at hleft; omega : 0 ≤ x + (den + 1) - 2), show x - 1 - 1 = x - 2 by omega]
    simp only [BaseMask.StairEvenCorner, RailCorner, and_true]
    by_cases hx2 : x ≤ 2
    · rw [min_eq_left (by omega : x - 2 ≤ 0), min_eq_left (by omega : 0 ≤ 2 - x)]
      split <;> split <;> omega
    · rw [min_eq_right (by omega : 0 ≤ x - 2), min_eq_right (by omega : 2 - x ≤ 0)]
      split <;> split <;> omega
  · have hxl : x = 1 - den := hxl
    have hyl : y = 0 := hyl
    subst x
    subst y
    have hp : (0, 1) ∈ (BaseMask.stairEven.raw den).sites := by
      apply BaseMask.mem_stairEven_body <;> dsimp <;> omega
    rw [hkernel, show 1 - den + den - 1 = 0 by omega, show (0 : ℤ) + 1 = 1 by decide, hvalue _ _ hp]
    simp only [BaseMask.StairEvenCorner, RailCorner]
    rw [min_eq_left (by omega : 0 ≤ 2 - (1 - den)), max_eq_right (by omega : 1 - den + 0 - 2 ≤ 0),
      show den - 2 + (1 - den) = -1 by omega]
    split <;> split <;> omega
  · have hxr : x = 3 := hxr
    have hyr : y = den := hyr
    subst x
    subst y
    have hp : (2, den) ∈ (BaseMask.stairEven.raw den).sites := by
      apply BaseMask.mem_stairEven_body <;> dsimp <;> omega
    rw [show (3 : ℤ) - 1 = 2 by decide, hvalue _ _ hp, chooseTwo_succ]
    simp only [BaseMask.StairEvenCorner, RailCorner]
    rw [min_eq_left (by omega : 0 ≤ den - 2 + 3), max_eq_left (by omega : 0 ≤ 3 + den - 2)]
    split <;> split <;> omega

/-- The B3 plane construction agrees with every occupied raw alternate height. -/
theorem stairEvenAltField_agrees {den : ℤ} (hden : BaseMask.stairEvenAlt.Valid den)
    {standard : Field} (hstandard : (BaseMask.stairEven.raw den).Agrees standard 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) standard 0 (stairEvenConstantV den)) :
    (BaseMask.stairEvenAlt.raw den).Agrees (stairEvenAltField den standard) 0 := by
  intro point
  have hmin := hden.1
  rw [BaseMask.stairEvenAlt_raw_height]
  change _ = stairEvenAltField den standard point.val + 0
  rw [stairEvenAltField, shifted_standard_on_alternate_raw hden hstandard hperiod _ point.property,
    stairEvenAltMarker_on_raw hmin point.property]
  simp only [BaseMask.StairEvenAltBump, RailCorner, MarkedSite]
  split <;> split <;> split <;> omega

/-- A compatible B3 plane extension with the source transverse constant. -/
theorem stairEvenAlt_exists_extension {den : ℤ} (hden : BaseMask.stairEvenAlt.Valid den) :
    ∃ field : Field, (BaseMask.stairEvenAlt.raw den).Agrees field 0 ∧
      HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den - 1) ∧
      HasQuadraticGrowth field (Fraction.mk 1 den).matrix := by
  obtain ⟨standard, hagree, hperiod, _⟩ := stairEven_exists_extension hden
  have hperiod' := stairEvenAltField_periods hperiod
  have hinterval : (Fraction.mk 1 den).InUnitInterval := by
    have := hden.1
    exact ⟨by dsimp; omega, by change (0 : ℤ) ≤ 1; decide, by dsimp; omega⟩
  exact ⟨stairEvenAltField den standard, stairEvenAltField_agrees hden hagree hperiod, hperiod',
    generator_periods_growth hinterval hperiod'⟩

/-- At the root the even alternate is stored with its raw lower-left
translated to zero. The agreement explicitly restores the physical chart. -/
theorem evaluateNative_empty_even_alternate_extension :
    ∃ registers : TileRegisters, ∃ field : Field,
      evaluateNative [] = .ok registers ∧
      registers.alternate.currentEven.val.Agrees (fun site => field (site + (-2, -1))) 0 ∧
      HasGeneratorPeriods ((parentsAt []).current .even) field 0 (stairEvenConstantV 3 - 1) ∧
      HasQuadraticGrowth field ((parentsAt []).current .even).matrix := by
  have hvalid : BaseMask.stairEvenAlt.Valid 3 := by simp [BaseMask.Valid]
  obtain ⟨field, hagree, hperiod, hgrowth⟩ := stairEvenAlt_exists_extension hvalid
  exact ⟨BaseRun.empty.registers.llCenter, field, evaluateNative_base .empty,
    BaseMask.stairEvenAlt_llCenter_agrees hvalid hagree, hperiod, hgrowth⟩

theorem evaluateNative_threes_even_alternate_extension (extra : ℕ) :
    let word := (BaseRun.threes extra).word
    let den : ℤ := 2 * (extra : ℤ) + 3 + 2
    let fraction := (parentsAt word).current .even
    ∃ registers : TileRegisters, ∃ field : Field,
      evaluateNative word = .ok registers ∧
      registers.alternate.currentEven.val.Agrees (fun site => field (site + (1 - den, -1))) 0 ∧
      HasGeneratorPeriods fraction field 0 (stairEvenConstantV den - 1) ∧
      HasQuadraticGrowth field fraction.matrix := by
  dsimp only
  rw [threes_current_even]
  have hvalid : BaseMask.stairEvenAlt.Valid (2 * (extra : ℤ) + 3 + 2) := by
    change 3 ≤ 2 * (extra : ℤ) + 3 + 2 ∧ (2 * (extra : ℤ) + 3 + 2) % 2 = 1
    omega
  obtain ⟨field, hagree, hperiod, hgrowth⟩ := stairEvenAlt_exists_extension hvalid
  exact ⟨(BaseRun.threes extra).registers.llCenter, field, evaluateNative_base _,
    BaseMask.stairEvenAlt_llCenter_agrees hvalid hagree, hperiod, hgrowth⟩

end FLatticePaper.Construction
