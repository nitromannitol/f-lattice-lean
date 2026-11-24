import FLatticePaper.Construction.AlternateLadderReflection
import FLatticePaper.Construction.StaircaseLaplacian

namespace FLatticePaper.Construction

open Farey

/-- The three lower exits at odd B7 centers. -/
abbrev LadderOddAltLowerExit (den : ℤ) (point : Site) : Prop :=
  (point.2 = -1 ∧ 0 ≤ point.1 ∧ point.1 ≤ den - 2) ∨
  (point.1 + point.2 = -1 ∧ 1 ≤ point.2 ∧ point.2 ≤ den - 2) ∨
  (point.2 = 1 ∧ den ≤ point.1 ∧ point.1 ≤ 2 * den - 2)

abbrev LadderOddAltEvenBlack (den : ℤ) (point : Site) : Prop :=
  (point.1 = 0 ∧ 0 ≤ point.2 ∧ point.2 ≤ den - 2) ∨
  (point.1 = den - 1 ∧ 3 ≤ point.2 ∧ point.2 ≤ den + 1) ∨ BaseMask.LadderOddAltDiagonal den point

abbrev LadderOddAltOddWhite (den : ℤ) (point : Site) : Prop :=
  LadderOddAltLowerExit den point ∨ LadderOddAltLowerExit den (reflectLadderOddAlt den point) ∨
  (point.1 = -1 ∧ point.2 = 0) ∨ (point.1 = den ∧ point.2 = den + 1) ∨
  (1 ≤ point.1 ∧ point.1 ≤ den - 2 ∧ (point.1 + point.2 = den - 1 ∨ point.1 + point.2 = den + 1))

theorem ladderOddAlt_left_notMem_iff {den x y : ℤ} (hden : BaseMask.ladderOddAlt.Valid den)
    (hsite : (x, y) ∈ (BaseMask.ladderOddAlt.raw den).sites) (heven : (x + y) % 2 = 0) :
    (x - 1, y) ∉ (BaseMask.ladderOddAlt.raw den).sites ↔
      (x = -1 ∧ y = -1) ∨ (x = 0 ∧ y = den + 2) ∨ (x = 1 - den ∧ y = den - 1) := by
  have ⟨hmin, hd⟩ := hden
  obtain ⟨hx, hy, hshape⟩ := BaseMask.mem_ladderOddAlt_raw_iff.mp hsite
  simp only [BaseMask.mem_ladderOddAlt_raw_iff, BaseMask.LadderOddAltCorner] at hshape ⊢
  rcases hshape with (h | h) | h <;> omega

theorem ladderOddAlt_down_notMem_iff {den x y : ℤ} (hden : BaseMask.ladderOddAlt.Valid den)
    (hsite : (x, y) ∈ (BaseMask.ladderOddAlt.raw den).sites) (hodd : (x + y) % 2 ≠ 0) :
    (x, y - 1) ∉ (BaseMask.ladderOddAlt.raw den).sites ↔ LadderOddAltLowerExit den (x, y) := by
  have ⟨hmin, hd⟩ := hden
  obtain ⟨hx, hy, hshape⟩ := BaseMask.mem_ladderOddAlt_raw_iff.mp hsite
  simp only [BaseMask.mem_ladderOddAlt_raw_iff, BaseMask.LadderOddAltCorner, LadderOddAltLowerExit] at hshape ⊢
  rcases hshape with (h | h) | h <;> omega

private theorem min_kink (n : ℤ) :
    min (n - 1) 0 + min (n + 1) 0 - 2 * min n 0 = if n = 0 then -1 else 0 := by
  split <;> omega

private theorem max_kink (n : ℤ) :
    max (n - 1) 0 + max (n + 1) 0 - 2 * max n 0 = if n = 0 then 1 else 0 := by
  split <;> omega

theorem laplacian_ladderOddAltBackground {den : ℤ} (heven : den % 2 = 0) (point : Site) :
    laplacian (ladderOddAltBackground den) point =
      if EvenSite point then
        (if point.1 = 0 then -1 else 0) + (if point.1 = den - 1 then -1 else 0) +
          (if point.1 + point.2 = den then 1 else 0)
      else -1 := by
  obtain ⟨x, y⟩ := point
  have hmax := max_kink (x + y - den)
  by_cases hphase : EvenSite (x, y)
  · have hleft := min_kink x
    have hright := min_kink (den - x - 1)
    rw [if_congr (show den - x - 1 = 0 ↔ x = den - 1 by omega) rfl rfl] at hright
    rw [if_congr (show x + y - den = 0 ↔ x + y = den by omega) rfl rfl] at hmax
    simp only [laplacian, incomingNeg, incomingPos, if_pos hphase, ladderOddAltBackground]
    rw [show den - (x - 1) - 1 = den - x - 1 + 1 by omega,
      show den - (x + 1) - 1 = den - x - 1 - 1 by omega,
      show x - 1 + y - den = x + y - den - 1 by omega,
      show x + 1 + y - den = x + y - den + 1 by omega]
    omega
  · have hodd : (x + y) % 2 ≠ 0 := hphase
    rw [if_neg (show x + y - den ≠ 0 by omega)] at hmax
    have hquad : -chooseTwo (y - 1 + 1) - chooseTwo (y + 1 + 1) + 2 * chooseTwo (y + 1) = -1 := by
      apply mul_left_cancel₀ (show (2 : ℤ) ≠ 0 by decide)
      linear_combination -two_mul_chooseTwo (y - 1 + 1) - two_mul_chooseTwo (y + 1 + 1) +
        2 * two_mul_chooseTwo (y + 1)
    simp only [laplacian, incomingNeg, incomingPos, if_neg hphase, ladderOddAltBackground]
    rw [show x + (y - 1) - den = x + y - den - 1 by omega,
      show x + (y + 1) - den = x + y - den + 1 by omega]
    omega

def ladderOddAltResidual (den : ℤ) (field : Field) (point : Site) : ℤ :=
  field point - ladderOddAltBackground den point

theorem ladderOddAltResidual_on_raw {den : ℤ} {field : Field}
    (hagree : (BaseMask.ladderOddAlt.raw den).Agrees field 0) {point : Site}
    (hsite : point ∈ (BaseMask.ladderOddAlt.raw den).sites) :
    ladderOddAltResidual den field point = if LadderOddAltBump den point then 1 else 0 := by
  rw [ladderOddAltResidual, ladderOddAlt_agrees_value hagree hsite, ladderOddAltValue_eq_background_add_bump]
  ring

theorem ladderOddAltResidual_incomingPos_reflect {den : ℤ} (hden : BaseMask.ladderOddAlt.Valid den)
    {field : Field} (hagree : (BaseMask.ladderOddAlt.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field (-1) (ladderOddAltConstantV den))
    (point : Site) : ladderOddAltResidual den field (incomingPos point) =
      ladderOddAltResidual den field (incomingNeg (reflectLadderOddAlt den point)) := by
  rw [(incomingStar_reflectLadderOddAlt den point).1]
  simp only [ladderOddAltResidual, ladderOddAltField_reflection hden hagree hperiod,
    ladderOddAltBackground_reflection]
  ring

local macro "alternate_ladder_mem" : tactic => `(tactic|
  (apply BaseMask.mem_ladderOddAlt_raw_iff.mpr
   simp only [BaseMask.LadderOddAltCorner, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
   omega))

local macro "alternate_ladder_residual" : tactic => `(tactic|
  (simp (disch := omega) only [LadderOddAltBump, BaseMask.LadderOddAltCorner, BaseMask.LadderOddAltDiagonal,
    Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, if_pos, if_neg,
      min_eq_left, min_eq_right, max_eq_left, max_eq_right] at *
   omega))

private theorem ladderOddAlt_kernel_shift {den : ℤ} (hd : den % 2 = 0) {field : Field}
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field (-1) (ladderOddAltConstantV den)) (point : Site) :
    field (point + (2 * den, 2)) = field point - 1 := by
  have h := hperiod.1 point
  change field (point + (reciprocalLadderDeck den).kernel) = field point - 1 at h
  rwa [reciprocalLadderDeck_eq hd] at h

private theorem ladderOddAlt_transverse_shift {den : ℤ} (hd : den % 2 = 0) {field : Field}
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field (-1) (ladderOddAltConstantV den)) (point : Site) :
    field (point + (1 - den, den + 1)) =
      field point - (Fraction.mk 1 den).transverseGrade point + ladderOddAltConstantV den := by
  have h := hperiod.2 point
  change field (point + (reciprocalLadderDeck den).transverse) = _ at h
  rwa [reciprocalLadderDeck_eq hd, add_comm 1 den] at h

private theorem binomial_succ (n : ℤ) : chooseTwo (n + 1) = chooseTwo n + n := by
  simpa [show chooseTwo (1 : ℤ) = 0 by decide] using chooseTwo_add n 1

private theorem binomial_succ_succ (n : ℤ) : chooseTwo (n + 2) = chooseTwo n + 2 * n + 1 := by
  have h := chooseTwo_add n 2
  rw [show chooseTwo (2 : ℤ) = 1 by decide] at h
  omega

private theorem ladderOddAlt_left_corner_residual {den : ℤ} (hden : BaseMask.ladderOddAlt.Valid den)
    {field : Field} (hagree : (BaseMask.ladderOddAlt.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field (-1) (ladderOddAltConstantV den)) :
    ladderOddAltResidual den field (-2, -1) = 2 := by
  have ⟨hmin, hd⟩ := hden
  have hp : ((-2, -1) : Site) + (2 * den, 2) ∈ (BaseMask.ladderOddAlt.raw den).sites := by
    alternate_ladder_mem
  have h := ladderOddAlt_agrees_value hagree hp
  rw [ladderOddAlt_kernel_shift hd hperiod, ladderOddAltValue_eq_background_add_bump] at h
  unfold ladderOddAltResidual
  simp only [ladderOddAltBackground, Prod.fst_add, Prod.snd_add,
    show chooseTwo ((-1 : ℤ) + 1) = 0 by decide, show chooseTwo ((-1 : ℤ) + 2 + 1) = 1 by decide] at h ⊢
  clear hperiod hagree hp
  alternate_ladder_residual

private theorem ladderOddAlt_left_top_residual {den : ℤ} (hden : BaseMask.ladderOddAlt.Valid den)
    {field : Field} (hagree : (BaseMask.ladderOddAlt.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field (-1) (ladderOddAltConstantV den)) :
    ladderOddAltResidual den field (-1, den + 2) = 1 := by
  have ⟨hmin, hd⟩ := hden
  have hp : (den - 2, 1) ∈ (BaseMask.ladderOddAlt.raw den).sites := by alternate_ladder_mem
  have heq : ((den - 2, 1) : Site) + (1 - den, den + 1) = (-1, den + 2) := by
    apply Prod.ext <;> dsimp <;> omega
  have hv := ladderOddAlt_transverse_shift hd hperiod (den - 2, 1)
  rw [heq, ladderOddAlt_agrees_value hagree hp, ladderOddAltValue_eq_background_add_bump] at hv
  unfold ladderOddAltResidual
  simp only [ladderOddAltBackground, ladderOddAltConstantV, Fraction.transverseGrade, one_mul,
    show chooseTwo ((1 : ℤ) + 1) = 1 by decide,
    show den + 2 + 1 = den + 1 + 2 by omega, binomial_succ_succ (den + 1)] at hv ⊢
  clear hperiod hagree hp
  alternate_ladder_residual

private theorem ladderOddAlt_left_side_residual {den : ℤ} (hden : BaseMask.ladderOddAlt.Valid den)
    {field : Field} (hagree : (BaseMask.ladderOddAlt.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field (-1) (ladderOddAltConstantV den)) :
    ladderOddAltResidual den field (-den, den - 1) = 0 := by
  have ⟨hmin, hd⟩ := hden
  have hp : (den, den + 1) ∈ (BaseMask.ladderOddAlt.raw den).sites := by alternate_ladder_mem
  have heq : ((-den, den - 1) : Site) + (2 * den, 2) = (den, den + 1) := by
    apply Prod.ext <;> dsimp <;> omega
  have hv := ladderOddAlt_kernel_shift hd hperiod (-den, den - 1)
  rw [heq, ladderOddAlt_agrees_value hagree hp, ladderOddAltValue_eq_background_add_bump] at hv
  unfold ladderOddAltResidual
  simp only [ladderOddAltBackground, show den - 1 + 1 = den by omega,
    binomial_succ (den + 1), binomial_succ den] at hv ⊢
  clear hperiod hagree hp
  alternate_ladder_residual

theorem ladderOddAltResidual_incomingNeg_even {den : ℤ} (hden : BaseMask.ladderOddAlt.Valid den)
    {field : Field} (hagree : (BaseMask.ladderOddAlt.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field (-1) (ladderOddAltConstantV den))
    (point : Site) (hsite : point ∈ (BaseMask.ladderOddAlt.raw den).sites) (heven : EvenSite point) :
    ladderOddAltResidual den field (incomingNeg point) =
      if point.1 = -1 ∧ point.2 = -1 then 2 else if point.1 = 0 ∧ point.2 = den + 2 then 1 else 0 := by
  obtain ⟨x, y⟩ := point
  have ⟨hmin, hd⟩ := hden
  have hxy : (x + y) % 2 = 0 := heven
  have hexit := ladderOddAlt_left_notMem_iff hden hsite hxy
  simp only [incomingNeg, if_pos heven]
  by_cases hl : x = -1 ∧ y = -1
  · obtain ⟨rfl, rfl⟩ := hl
    rw [if_pos (by decide : (-1 : ℤ) = -1 ∧ (-1 : ℤ) = -1)]
    exact ladderOddAlt_left_corner_residual hden hagree hperiod
  rw [if_neg hl]
  by_cases ht : x = 0 ∧ y = den + 2
  · obtain ⟨rfl, rfl⟩ := ht
    rw [if_pos (show (0 : ℤ) = 0 ∧ den + 2 = den + 2 from ⟨rfl, rfl⟩)]
    exact ladderOddAlt_left_top_residual hden hagree hperiod
  rw [if_neg ht]
  by_cases hs : x = 1 - den ∧ y = den - 1
  · obtain ⟨hx, hy⟩ := hs
    rw [hx, hy, show 1 - den - 1 = -den by omega]
    exact ladderOddAlt_left_side_residual hden hagree hperiod
  · have hin : (x - 1, y) ∈ (BaseMask.ladderOddAlt.raw den).sites := not_not.mp (fun h => by
      rcases hexit.mp h with h | h | h
      · exact hl h
      · exact ht h
      · exact hs h)
    rw [ladderOddAltResidual_on_raw hagree hin]
    apply if_neg
    simp only [LadderOddAltBump, BaseMask.LadderOddAltCorner, BaseMask.LadderOddAltDiagonal]
    omega

private theorem ladderOddAlt_lower_exit_residual {den x y : ℤ} (hden : BaseMask.ladderOddAlt.Valid den)
    {field : Field} (hagree : (BaseMask.ladderOddAlt.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field (-1) (ladderOddAltConstantV den))
    (hexit : LadderOddAltLowerExit den (x, y)) : ladderOddAltResidual den field (x, y - 1) = 1 := by
  have ⟨hmin, hd⟩ := hden
  rcases hexit with ⟨rfl, hx⟩ | hdiag | ⟨rfl, hx⟩
  · have hp : ((x, -2) : Site) + (1 - den, den + 1) ∈ (BaseMask.ladderOddAlt.raw den).sites := by
      alternate_ladder_mem
    have hv := ladderOddAlt_agrees_value hagree hp
    rw [ladderOddAlt_transverse_shift hd hperiod, ladderOddAltValue_eq_background_add_bump] at hv
    change field (x, -2) - ladderOddAltBackground den (x, -2) = 1
    simp only [ladderOddAltBackground, ladderOddAltConstantV, Fraction.transverseGrade, one_mul,
      Prod.fst_add, Prod.snd_add, show (-2 : ℤ) + (den + 1) + 1 = den by omega,
      show chooseTwo ((-2 : ℤ) + 1) = 1 by decide, binomial_succ den] at hv ⊢
    clear hp hperiod hagree
    alternate_ladder_residual
  · have hp : ((x, y - 1) : Site) + (2 * den, 2) ∈ (BaseMask.ladderOddAlt.raw den).sites := by
      alternate_ladder_mem
    have hv := ladderOddAlt_agrees_value hagree hp
    rw [ladderOddAlt_kernel_shift hd hperiod, ladderOddAltValue_eq_background_add_bump] at hv
    unfold ladderOddAltResidual
    simp only [ladderOddAltBackground, Prod.fst_add, Prod.snd_add, sub_add_cancel,
      show y - 1 + 2 + 1 = y + 2 by omega, binomial_succ_succ y] at hv ⊢
    clear hp hperiod hagree
    alternate_ladder_residual
  · have hp : ((x, 0) : Site) + (1 - den, den + 1) ∈ (BaseMask.ladderOddAlt.raw den).sites := by
      alternate_ladder_mem
    have hv := ladderOddAlt_agrees_value hagree hp
    rw [ladderOddAlt_transverse_shift hd hperiod, ladderOddAltValue_eq_background_add_bump] at hv
    change field (x, 0) - ladderOddAltBackground den (x, 0) = 1
    simp only [ladderOddAltBackground, ladderOddAltConstantV, Fraction.transverseGrade, one_mul,
      Prod.fst_add, Prod.snd_add, zero_add, binomial_succ (den + 1),
      show chooseTwo (1 : ℤ) = 0 by decide] at hv ⊢
    clear hp hperiod hagree
    alternate_ladder_residual

theorem ladderOddAltResidual_incomingNeg_odd {den : ℤ} (hden : BaseMask.ladderOddAlt.Valid den)
    {field : Field} (hagree : (BaseMask.ladderOddAlt.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field (-1) (ladderOddAltConstantV den))
    (point : Site) (hsite : point ∈ (BaseMask.ladderOddAlt.raw den).sites) (hodd : ¬ EvenSite point) :
    ladderOddAltResidual den field (incomingNeg point) =
      if LadderOddAltLowerExit den point ∨ (point.1 = -1 ∧ point.2 = 0) ∨
        (1 ≤ point.1 ∧ point.1 ≤ den - 2 ∧ point.1 + point.2 = den + 1) then 1 else 0 := by
  obtain ⟨x, y⟩ := point
  have hxy : (x + y) % 2 ≠ 0 := hodd
  simp only [incomingNeg, if_neg hodd]
  by_cases hlo : LadderOddAltLowerExit den (x, y)
  · rw [if_pos (Or.inl hlo)]
    exact ladderOddAlt_lower_exit_residual hden hagree hperiod hlo
  · have hn : (x, y - 1) ∈ (BaseMask.ladderOddAlt.raw den).sites :=
      not_not.mp fun h => hlo ((ladderOddAlt_down_notMem_iff hden hsite hxy).mp h)
    rw [ladderOddAltResidual_on_raw hagree hn]
    apply if_congr ?_ rfl rfl
    obtain ⟨_, hy, _⟩ := BaseMask.mem_ladderOddAlt_raw_iff.mp hsite
    simp only [hlo, false_or, LadderOddAltBump, BaseMask.LadderOddAltCorner, BaseMask.LadderOddAltDiagonal]
    omega

private theorem ladderOddAlt_laplacian_eq_residual {den : ℤ} {field : Field} (point : Site) :
    laplacian field point = laplacian (ladderOddAltBackground den) point +
      ladderOddAltResidual den field (incomingNeg point) + ladderOddAltResidual den field (incomingPos point) -
      2 * ladderOddAltResidual den field point := by
  simp only [laplacian, ladderOddAltResidual]
  ring

local macro "alternate_ladder_charge" : tactic => `(tactic|
  (simp (disch := omega) only [if_pos, if_neg]
   repeat' first | omega | (split <;> rename_i hclause <;>
     simp only [true_and, and_true, true_or, or_true, false_and, and_false, false_or, or_false,
       not_true_eq_false, not_false_eq_true] at hclause)))

theorem ladderOddAlt_laplacian_on_even_raw {den : ℤ} (hden : BaseMask.ladderOddAlt.Valid den)
    {field : Field} (hagree : (BaseMask.ladderOddAlt.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field (-1) (ladderOddAltConstantV den))
    (point : Site) (hsite : point ∈ (BaseMask.ladderOddAlt.raw den).sites) (heven : EvenSite point) :
    laplacian field point = if LadderOddAltEvenBlack den point then -1 else 0 := by
  have ⟨hmin, hd⟩ := hden
  have href := (reflectLadderOddAlt_mem_iff den point).mpr hsite
  have hpar := (evenSite_reflectLadderOddAlt_iff den point).mpr heven
  rw [ladderOddAlt_laplacian_eq_residual, laplacian_ladderOddAltBackground hd, if_pos heven,
    ladderOddAltResidual_incomingNeg_even hden hagree hperiod point hsite heven,
    ladderOddAltResidual_incomingPos_reflect hden hagree hperiod,
    ladderOddAltResidual_incomingNeg_even hden hagree hperiod _ href hpar,
    ladderOddAltResidual_on_raw hagree hsite]
  obtain ⟨x, y⟩ := point
  have hxy : (x + y) % 2 = 0 := heven
  obtain ⟨hx, hy, hshape⟩ := BaseMask.mem_ladderOddAlt_raw_iff.mp hsite
  dsimp only at hx hy
  simp only [BaseMask.LadderOddAltCorner] at hshape
  simp only [LadderOddAltEvenBlack, LadderOddAltBump, BaseMask.LadderOddAltCorner,
    BaseMask.LadderOddAltDiagonal, reflectLadderOddAlt, Prod.fst_sub, Prod.snd_sub]
  rcases hshape with (ha | hb) | hbody
  · alternate_ladder_charge
  · alternate_ladder_charge
  · by_cases hdiag : x + y = den
    · have hwidth : 0 ≤ x ∧ x ≤ den - 1 := by omega
      by_cases hx0 : x = 0
      · alternate_ladder_charge
      · by_cases hx1 : x = den - 1 <;> alternate_ladder_charge
    · by_cases hx0 : x = 0
      · by_cases hyLast : y = den + 2 <;> alternate_ladder_charge
      · by_cases hx1 : x = den - 1
        · by_cases hyFirst : y = -1 <;> alternate_ladder_charge
        · alternate_ladder_charge

theorem ladderOddAlt_laplacian_on_odd_raw {den : ℤ} (hden : BaseMask.ladderOddAlt.Valid den)
    {field : Field} (hagree : (BaseMask.ladderOddAlt.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field (-1) (ladderOddAltConstantV den))
    (point : Site) (hsite : point ∈ (BaseMask.ladderOddAlt.raw den).sites) (hodd : ¬ EvenSite point) :
    laplacian field point = if LadderOddAltOddWhite den point then 0 else -1 := by
  have ⟨hmin, hd⟩ := hden
  have href := (reflectLadderOddAlt_mem_iff den point).mpr hsite
  have hpar : ¬ EvenSite (reflectLadderOddAlt den point) :=
    fun h => hodd ((evenSite_reflectLadderOddAlt_iff den point).mp h)
  rw [ladderOddAlt_laplacian_eq_residual, laplacian_ladderOddAltBackground hd, if_neg hodd,
    ladderOddAltResidual_incomingNeg_odd hden hagree hperiod point hsite hodd,
    ladderOddAltResidual_incomingPos_reflect hden hagree hperiod,
    ladderOddAltResidual_incomingNeg_odd hden hagree hperiod _ href hpar,
    ladderOddAltResidual_on_raw hagree hsite]
  obtain ⟨x, y⟩ := point
  have hxy : (x + y) % 2 ≠ 0 := hodd
  clear hagree hperiod hsite href hpar hodd hden
  have hc : ¬ LadderOddAltBump den (x, y) := by
    simp only [LadderOddAltBump, BaseMask.LadderOddAltCorner, BaseMask.LadderOddAltDiagonal]
    omega
  let neg := LadderOddAltLowerExit den (x, y) ∨ (x = -1 ∧ y = 0) ∨
    (1 ≤ x ∧ x ≤ den - 2 ∧ x + y = den + 1)
  let pos := LadderOddAltLowerExit den (reflectLadderOddAlt den (x, y)) ∨ (x = den ∧ y = den + 1) ∨
    (1 ≤ x ∧ x ≤ den - 2 ∧ x + y = den - 1)
  have hdisjoint : ¬ (neg ∧ pos) := by
    simp only [neg, pos, LadderOddAltLowerExit, reflectLadderOddAlt, Prod.fst_sub, Prod.snd_sub]
    omega
  have hp : (LadderOddAltLowerExit den (reflectLadderOddAlt den (x, y)) ∨
      ((reflectLadderOddAlt den (x, y)).1 = -1 ∧ (reflectLadderOddAlt den (x, y)).2 = 0) ∨
      (1 ≤ (reflectLadderOddAlt den (x, y)).1 ∧ (reflectLadderOddAlt den (x, y)).1 ≤ den - 2 ∧
        (reflectLadderOddAlt den (x, y)).1 + (reflectLadderOddAlt den (x, y)).2 = den + 1)) ↔ pos := by
    unfold pos
    apply or_congr Iff.rfl
    simp only [reflectLadderOddAlt, Prod.fst_sub, Prod.snd_sub]
    omega
  have hwhite : LadderOddAltOddWhite den (x, y) ↔ neg ∨ pos := by
    simp only [LadderOddAltOddWhite, neg, pos]
    constructor
    · rintro (h | h | h | h | ⟨hx₀, hx₁, hs | hs⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr ⟨hx₀, hx₁, hs⟩))
      · exact Or.inl (Or.inr (Or.inr ⟨hx₀, hx₁, hs⟩))
    · rintro ((h | h | ⟨hx₀, hx₁, hs⟩) | (h | h | ⟨hx₀, hx₁, hs⟩))
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hx₀, hx₁, Or.inr hs⟩)))
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hx₀, hx₁, Or.inl hs⟩)))
  rw [if_congr hp rfl rfl, if_neg hc, if_congr hwhite rfl rfl]
  change -1 + (if neg then 1 else 0) + (if pos then 1 else 0) - 2 * 0 = if neg ∨ pos then 0 else -1
  by_cases hn : neg
  · have hp' : ¬ pos := fun h => hdisjoint ⟨hn, h⟩
    simp [hn, hp']
  · by_cases hp' : pos <;> simp [hn, hp']

/-- The B7 charge table on the occupied period representatives. -/
theorem ladderOddAlt_laplacian_on_raw {den : ℤ} (hden : BaseMask.ladderOddAlt.Valid den)
    {field : Field} (hagree : (BaseMask.ladderOddAlt.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field (-1) (ladderOddAltConstantV den))
    (point : Site) (hsite : point ∈ (BaseMask.ladderOddAlt.raw den).sites) :
    laplacian field point = if EvenSite point then (if LadderOddAltEvenBlack den point then -1 else 0)
      else (if LadderOddAltOddWhite den point then 0 else -1) := by
  by_cases he : EvenSite point
  · simpa only [if_pos he] using ladderOddAlt_laplacian_on_even_raw hden hagree hperiod point hsite he
  · simpa only [if_neg he] using ladderOddAlt_laplacian_on_odd_raw hden hagree hperiod point hsite he

theorem ladderOddAlt_binary_laplacian {den : ℤ} (hden : BaseMask.ladderOddAlt.Valid den)
    {field : Field} (hagree : (BaseMask.ladderOddAlt.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field (-1) (ladderOddAltConstantV den))
    (point : Site) : laplacian field point = -1 ∨ laplacian field point = 0 := by
  have hinterval : (Fraction.mk 1 den).InUnitInterval := by
    have := hden.1
    exact ⟨by dsimp; omega, by change (0 : ℤ) ≤ 1; decide, by dsimp; omega⟩
  obtain ⟨site, hsite, hspan⟩ := ladderOddAlt_raw_cover hden point
  have h := laplacian_periodic_of_generatorPeriods hinterval hperiod hspan site
  rw [show site + (point - site) = point by rw [add_comm, sub_add_cancel],
    ladderOddAlt_laplacian_on_raw hden hagree hperiod site hsite] at h
  rw [h]
  split <;> split <;> simp

end FLatticePaper.Construction
