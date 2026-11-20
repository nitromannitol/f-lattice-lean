import FLatticePaper.Construction.LadderReflection
import FLatticePaper.Construction.StaircaseLaplacian

namespace FLatticePaper.Construction

open Farey

/-- The even B5 sites of charge one in the physical chart. -/
abbrev LadderOddEvenBlack (den : ℤ) (point : Site) : Prop :=
  (point.1 = 1 ∧ 1 ≤ point.2 ∧ point.2 ≤ den - 1) ∨
  (point.1 = den + 1 ∧ 3 ≤ point.2 ∧ point.2 ≤ den + 1) ∨
  (point.1 + point.2 = den + 2 ∧ 2 ≤ point.2 ∧ point.2 ≤ den)

/-- The lower exits at odd physical B5 centers. -/
abbrev LadderOddLowerBoundary (den : ℤ) (point : Site) : Prop :=
  (point.1 + point.2 = 1 ∧ 2 - den ≤ point.1 ∧ point.1 ≤ -1) ∨
  (point.2 = 0 ∧ 1 ≤ point.1 ∧ point.1 ≤ den - 1) ∨
  (point.2 = 1 ∧ den ≤ point.1 ∧ point.1 ≤ 2 * den)

/-- The odd charge-zero lists in the raw B5 formula. -/
abbrev LadderOddOddWhite (den : ℤ) (point : Site) : Prop :=
  LadderOddLowerBoundary den point ∨ LadderOddLowerBoundary den (reflectLadderOdd den point) ∨
  (point.1 + point.2 = den + 1 ∧ 1 ≤ point.2 ∧ point.2 ≤ den - 1) ∨
  (point.1 + point.2 = den + 3 ∧ 3 ≤ point.2 ∧ point.2 ≤ den + 1) ∨
  (point.1 = 0 ∧ point.2 = 1) ∨ (point.1 = den + 2 ∧ point.2 = den + 1)

theorem ladderOdd_left_notMem_iff {den x y : ℤ} (hden : BaseMask.ladderOdd.Valid den)
    (hsite : (x, y) ∈ (BaseMask.ladderOdd.raw den).sites) (heven : (x + y) % 2 = 0) :
    (x - 1, y) ∉ (BaseMask.ladderOdd.raw den).sites ↔ (x = 0 ∧ y = 0) ∨ (x = 2 - den ∧ y = den) := by
  have ⟨hmin, hd⟩ := hden
  obtain ⟨hx, hy, hshape⟩ := BaseMask.mem_ladderOdd_raw_iff.mp hsite
  simp only [BaseMask.mem_ladderOdd_raw_iff, BaseMask.LadderOddCorner] at hshape ⊢
  rcases hshape with (h | h) | h <;> omega

theorem ladderOdd_down_notMem_iff {den x y : ℤ} (hden : BaseMask.ladderOdd.Valid den)
    (hsite : (x, y) ∈ (BaseMask.ladderOdd.raw den).sites) (hodd : (x + y) % 2 ≠ 0) :
    (x, y - 1) ∉ (BaseMask.ladderOdd.raw den).sites ↔ LadderOddLowerBoundary den (x, y) := by
  have ⟨hmin, hd⟩ := hden
  obtain ⟨hx, hy, hshape⟩ := BaseMask.mem_ladderOdd_raw_iff.mp hsite
  simp only [BaseMask.mem_ladderOdd_raw_iff, BaseMask.LadderOddCorner, LadderOddLowerBoundary] at hshape ⊢
  rcases hshape with (h | h) | h <;> omega

private theorem min_zero_kink (n : ℤ) :
    min 0 (n - 1) + min 0 (n + 1) - 2 * min 0 n = (if n = 0 then -1 else 0) := by
  split <;> omega

private theorem max_zero_kink (n : ℤ) :
    max (n - 1) 0 + max (n + 1) 0 - 2 * max n 0 = (if n = 0 then 1 else 0) := by
  split <;> omega

theorem laplacian_ladderOddBackground {den : ℤ} (heven : den % 2 = 0) (point : Site) :
    laplacian (ladderOddBackground den) point =
      if EvenSite point then
        (if point.1 = 1 then -1 else 0) + (if point.1 = den + 1 then -1 else 0) +
          (if point.1 + point.2 = den + 2 then 1 else 0)
      else -1 := by
  obtain ⟨x, y⟩ := point
  have hmax := max_zero_kink (y + x - den - 2)
  by_cases hphase : EvenSite (x, y)
  · have hleft := min_zero_kink (x - 1)
    have hright := min_zero_kink (den + 1 - x)
    rw [if_congr (show x - 1 = 0 ↔ x = 1 by omega) rfl rfl] at hleft
    rw [if_congr (show den + 1 - x = 0 ↔ x = den + 1 by omega) rfl rfl] at hright
    rw [if_congr (show y + x - den - 2 = 0 ↔ x + y = den + 2 by omega) rfl rfl] at hmax
    rw [min_comm 0 (den + 1 - x - 1), min_comm 0 (den + 1 - x + 1), min_comm 0 (den + 1 - x)] at hright
    simp only [laplacian, incomingNeg, incomingPos, if_pos hphase, ladderOddBackground]
    rw [show x + 1 - 1 = x - 1 + 1 by omega,
      show den + 1 - (x - 1) = den + 1 - x + 1 by omega,
      show den + 1 - (x + 1) = den + 1 - x - 1 by omega,
      show y + (x - 1) - den - 2 = y + x - den - 2 - 1 by omega,
      show y + (x + 1) - den - 2 = y + x - den - 2 + 1 by omega]
    omega
  · have hodd : (x + y) % 2 ≠ 0 := hphase
    rw [if_neg (show y + x - den - 2 ≠ 0 by omega)] at hmax
    have hquad : -chooseTwo (y - 1) - chooseTwo (y + 1) + 2 * chooseTwo y = -1 := by
      apply mul_left_cancel₀ (show (2 : ℤ) ≠ 0 by decide)
      linear_combination -two_mul_chooseTwo (y - 1) - two_mul_chooseTwo (y + 1) + 2 * two_mul_chooseTwo y
    simp only [laplacian, incomingNeg, incomingPos, if_neg hphase, ladderOddBackground]
    rw [show y - 1 + x - den - 2 = y + x - den - 2 - 1 by omega,
      show y + 1 + x - den - 2 = y + x - den - 2 + 1 by omega]
    omega

local macro "ladder_raw_mem" : tactic => `(tactic|
  (apply BaseMask.mem_ladderOdd_raw_iff.mpr
   simp only [BaseMask.LadderOddCorner, Prod.fst_add, Prod.snd_add]
   omega))

local macro "ladder_value" : tactic => `(tactic|
  (simp (disch := omega) only [BaseMask.ladderOddValue, BaseMask.LadderOddBump, Prod.fst_add, Prod.snd_add,
    show ∀ n : ℤ, n * (n - 1) / 2 = chooseTwo n from fun _ => rfl,
    if_pos, if_neg, min_eq_left, min_eq_right, max_eq_left, max_eq_right]
   omega))

private theorem ladderOdd_kernel_shift {den : ℤ} (hd : den % 2 = 0) {field : Field}
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den)) (point : Site) :
    field (point + (2 * den, 2)) = field point := by
  have h := hperiod.1 point
  change field (point + (reciprocalLadderDeck den).kernel) = field point + 0 at h
  rwa [reciprocalLadderDeck_eq hd, add_zero] at h

private theorem ladderOdd_transverse_shift {den : ℤ} (hd : den % 2 = 0) {field : Field}
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den)) (point : Site) :
    field (point + (1 - den, den + 1)) =
      field point - (Fraction.mk 1 den).transverseGrade point + stairEvenConstantV den := by
  have h := hperiod.2 point
  change field (point + (reciprocalLadderDeck den).transverse) = _ at h
  rwa [reciprocalLadderDeck_eq hd, add_comm 1 den] at h

private theorem chooseTwo_add_one (n : ℤ) : chooseTwo (n + 1) = chooseTwo n + n := by
  simpa [show chooseTwo (1 : ℤ) = 0 by decide] using chooseTwo_add n 1

private theorem chooseTwo_add_two (n : ℤ) : chooseTwo (n + 2) = chooseTwo n + 2 * n + 1 := by
  have h := chooseTwo_add n 2
  rw [show chooseTwo (2 : ℤ) = 1 by decide] at h
  omega

theorem ladderOdd_laplacian_on_even_left_exit {den x y : ℤ} (hden : BaseMask.ladderOdd.Valid den)
    {field : Field} (hagree : (BaseMask.ladderOdd.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den))
    (heven : EvenSite (x, y)) (hexit : (x = 0 ∧ y = 0) ∨ (x = 2 - den ∧ y = den)) :
    laplacian field (x, y) = 0 := by
  have ⟨hmin, hd⟩ := hden
  simp only [laplacian, incomingNeg, incomingPos, if_pos heven]
  rcases hexit with ⟨rfl, rfl⟩ | ⟨hx, hy⟩
  · have hc : (0, 0) ∈ (BaseMask.ladderOdd.raw den).sites := by
      exact BaseMask.mem_ladderOdd_raw_iff.mpr
        ⟨⟨by dsimp; omega, by dsimp; omega⟩, ⟨le_rfl, by dsimp; omega⟩, Or.inl (Or.inl ⟨rfl, rfl⟩)⟩
    have hr : (1, 0) ∈ (BaseMask.ladderOdd.raw den).sites := by ladder_raw_mem
    have hrepr : ((-1, 0) : Site) + (2 * den, 2) ∈ (BaseMask.ladderOdd.raw den).sites := by ladder_raw_mem
    change field (-1, 0) - field (0, 0) + (field (1, 0) - field (0, 0)) = 0
    rw [← ladderOdd_kernel_shift hd hperiod (-1, 0), ladderOdd_agrees_value hagree hrepr,
      ladderOdd_agrees_value hagree hc, ladderOdd_agrees_value hagree hr]
    have hq0 : chooseTwo 0 = 0 := by decide
    have hq2 : chooseTwo ((0 : ℤ) + 2) = 1 := by decide
    have hbump : BaseMask.LadderOddBump den (0, 0) := Or.inl ⟨rfl, rfl⟩
    simp only [BaseMask.ladderOddValue, if_pos hbump]
    simp (disch := omega) only [BaseMask.LadderOddBump, Prod.fst_add, Prod.snd_add,
      show ∀ n : ℤ, n * (n - 1) / 2 = chooseTwo n from fun _ => rfl, hq0, hq2,
      if_neg, min_eq_left, min_eq_right, max_eq_left, max_eq_right]
    omega
  · subst x
    subst y
    have hc : (2 - den, den) ∈ (BaseMask.ladderOdd.raw den).sites := by ladder_raw_mem
    have hr : (2 - den + 1, den) ∈ (BaseMask.ladderOdd.raw den).sites := by ladder_raw_mem
    have hrepr : ((2 - den - 1, den) : Site) + (2 * den, 2) ∈ (BaseMask.ladderOdd.raw den).sites := by
      ladder_raw_mem
    rw [← ladderOdd_kernel_shift hd hperiod (2 - den - 1, den), ladderOdd_agrees_value hagree hrepr,
      ladderOdd_agrees_value hagree hc, ladderOdd_agrees_value hagree hr]
    simp (disch := omega) only [BaseMask.ladderOddValue, BaseMask.LadderOddBump, Prod.fst_add, Prod.snd_add,
      show ∀ n : ℤ, n * (n - 1) / 2 = chooseTwo n from fun _ => rfl, chooseTwo_add_two den,
      if_neg, min_eq_left, min_eq_right, max_eq_left, max_eq_right]
    omega

theorem ladderOdd_laplacian_on_odd_lower_exit {den x y : ℤ} (hden : BaseMask.ladderOdd.Valid den)
    {field : Field} (hagree : (BaseMask.ladderOdd.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den))
    (hodd : ¬ EvenSite (x, y)) (hexit : LadderOddLowerBoundary den (x, y)) :
    laplacian field (x, y) = 0 := by
  have ⟨hmin, hd⟩ := hden
  have hxy : (x + y) % 2 ≠ 0 := hodd
  simp only [laplacian, incomingNeg, incomingPos, if_neg hodd]
  simp only [LadderOddLowerBoundary] at hexit
  rcases hexit with h | ⟨rfl, hx⟩ | ⟨rfl, hx⟩
  · have hc : (x, y) ∈ (BaseMask.ladderOdd.raw den).sites := by ladder_raw_mem
    have hup : (x, y + 1) ∈ (BaseMask.ladderOdd.raw den).sites := by ladder_raw_mem
    have hrepr : ((x, y - 1) : Site) + (2 * den, 2) ∈ (BaseMask.ladderOdd.raw den).sites := by
      ladder_raw_mem
    rw [← ladderOdd_kernel_shift hd hperiod (x, y - 1), ladderOdd_agrees_value hagree hrepr,
      ladderOdd_agrees_value hagree hc, ladderOdd_agrees_value hagree hup]
    simp only [BaseMask.ladderOddValue, Prod.fst_add, Prod.snd_add,
      show ∀ n : ℤ, n * (n - 1) / 2 = chooseTwo n from fun _ => rfl,
      show y - 1 + 2 = y + 1 by omega, chooseTwo_add_one y]
    ladder_value
  · have hc : (x, 0) ∈ (BaseMask.ladderOdd.raw den).sites := by ladder_raw_mem
    have hup : (x, 1) ∈ (BaseMask.ladderOdd.raw den).sites := by ladder_raw_mem
    have hrepr : ((x, -1) : Site) + (1 - den, den + 1) ∈ (BaseMask.ladderOdd.raw den).sites := by
      ladder_raw_mem
    have hval := ladderOdd_agrees_value hagree hrepr
    rw [ladderOdd_transverse_shift hd hperiod] at hval
    change field (x, -1) - field (x, 0) + (field (x, 1) - field (x, 0)) = 0
    rw [ladderOdd_agrees_value hagree hc, ladderOdd_agrees_value hagree hup]
    simp only [BaseMask.ladderOddValue, Prod.fst_add, Prod.snd_add,
      show ∀ n : ℤ, n * (n - 1) / 2 = chooseTwo n from fun _ => rfl,
      show chooseTwo (0 : ℤ) = 0 by decide,
      Fraction.transverseGrade, one_mul, mul_neg, mul_one, stairEvenConstantV,
      show (-1 : ℤ) + (den + 1) = den by omega, chooseTwo_add_one den] at hval ⊢
    simp (disch := omega) only [BaseMask.LadderOddBump, Prod.fst_add, Prod.snd_add,
      if_neg, min_eq_left, min_eq_right, max_eq_right] at hval ⊢
    omega
  · have hc : (x, 1) ∈ (BaseMask.ladderOdd.raw den).sites := by ladder_raw_mem
    have hup : (x, 2) ∈ (BaseMask.ladderOdd.raw den).sites := by ladder_raw_mem
    have hrepr : ((x, 0) : Site) + (1 - den, den + 1) ∈ (BaseMask.ladderOdd.raw den).sites := by
      ladder_raw_mem
    have hval := ladderOdd_agrees_value hagree hrepr
    rw [ladderOdd_transverse_shift hd hperiod] at hval
    change field (x, 0) - field (x, 1) + (field (x, 2) - field (x, 1)) = 0
    rw [ladderOdd_agrees_value hagree hc, ladderOdd_agrees_value hagree hup]
    simp only [BaseMask.ladderOddValue, Prod.fst_add, Prod.snd_add, zero_add,
      show ∀ n : ℤ, n * (n - 1) / 2 = chooseTwo n from fun _ => rfl,
      show chooseTwo (2 : ℤ) = 1 by decide,
      Fraction.transverseGrade, one_mul, mul_zero, zero_sub, stairEvenConstantV] at hval ⊢
    by_cases hxFirst : x = den <;>
      (simp (disch := omega) only [BaseMask.LadderOddBump, Prod.fst_add, Prod.snd_add,
        if_pos, if_neg, min_eq_left, min_eq_right, max_eq_left, max_eq_right] at hval ⊢
       omega)

private theorem ladderOdd_interior_laplacian {den : ℤ} {field : Field}
    (hagree : (BaseMask.ladderOdd.raw den).Agrees field 0) {point : Site}
    (hpoint : point ∈ (BaseMask.ladderOdd.raw den).sites)
    (hneg : incomingNeg point ∈ (BaseMask.ladderOdd.raw den).sites)
    (hpos : incomingPos point ∈ (BaseMask.ladderOdd.raw den).sites) :
    laplacian field point = laplacian (ladderOddBackground den) point +
      (if BaseMask.LadderOddBump den (incomingNeg point) then 1 else 0) +
      (if BaseMask.LadderOddBump den (incomingPos point) then 1 else 0) -
      2 * (if BaseMask.LadderOddBump den point then 1 else 0) := by
  simp only [laplacian, ladderOdd_agrees_value hagree hpoint, ladderOdd_agrees_value hagree hneg,
    ladderOdd_agrees_value hagree hpos, ladderOddValue_eq_background_add_bump]
  ring

private abbrev LadderOddLeftExit (den : ℤ) (point : Site) : Prop :=
  (point.1 = 0 ∧ point.2 = 0) ∨ (point.1 = 2 - den ∧ point.2 = den)

private theorem ladderOdd_right_notMem_iff {den x y : ℤ} (hden : BaseMask.ladderOdd.Valid den)
    (hsite : (x, y) ∈ (BaseMask.ladderOdd.raw den).sites) (heven : (x + y) % 2 = 0) :
    (x + 1, y) ∉ (BaseMask.ladderOdd.raw den).sites ↔ LadderOddLeftExit den (reflectLadderOdd den (x, y)) := by
  have href := (reflectLadderOdd_mem_iff den (x, y)).mpr hsite
  have hpar := (evenSite_reflectLadderOdd_iff den (x, y)).mpr heven
  have hshift : reflectLadderOdd den (x + 1, y) = (den + 2 - x - 1, den + 2 - y) := by
    exact Prod.ext (by dsimp [reflectLadderOdd]; omega) rfl
  rw [← reflectLadderOdd_mem_iff den (x + 1, y), hshift]
  exact ladderOdd_left_notMem_iff hden href hpar

theorem ladderOdd_up_notMem_iff {den x y : ℤ} (hden : BaseMask.ladderOdd.Valid den)
    (hsite : (x, y) ∈ (BaseMask.ladderOdd.raw den).sites) (hodd : ¬ EvenSite (x, y)) :
    (x, y + 1) ∉ (BaseMask.ladderOdd.raw den).sites ↔
      LadderOddLowerBoundary den (reflectLadderOdd den (x, y)) := by
  have href := (reflectLadderOdd_mem_iff den (x, y)).mpr hsite
  have hpar : ¬ EvenSite (reflectLadderOdd den (x, y)) :=
    fun h => hodd ((evenSite_reflectLadderOdd_iff den (x, y)).mp h)
  have hshift : reflectLadderOdd den (x, y + 1) = (den + 2 - x, den + 2 - y - 1) := by
    exact Prod.ext rfl (by dsimp [reflectLadderOdd]; omega)
  rw [← reflectLadderOdd_mem_iff den (x, y + 1), hshift]
  exact ladderOdd_down_notMem_iff hden href hpar

set_option maxHeartbeats 600000 in
theorem ladderOdd_laplacian_on_even_raw {den x y : ℤ} (hden : BaseMask.ladderOdd.Valid den)
    {field : Field} (hagree : (BaseMask.ladderOdd.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den))
    (hpoint : (x, y) ∈ (BaseMask.ladderOdd.raw den).sites) (heven : EvenSite (x, y)) :
    laplacian field (x, y) = if LadderOddEvenBlack den (x, y) then -1 else 0 := by
  have hmin := hden.1
  have hd := hden.2
  have hxy : (x + y) % 2 = 0 := heven
  have hleft := ladderOdd_left_notMem_iff hden hpoint hxy
  have hright := ladderOdd_right_notMem_iff hden hpoint hxy
  by_cases hl : LadderOddLeftExit den (x, y)
  · rw [ladderOdd_laplacian_on_even_left_exit hden hagree hperiod heven hl]
    apply Eq.symm
    apply if_neg
    simp only [LadderOddLeftExit] at hl
    simp only [LadderOddEvenBlack]
    omega
  by_cases hr : LadderOddLeftExit den (reflectLadderOdd den (x, y))
  · have hpar := (evenSite_reflectLadderOdd_iff den (x, y)).mpr heven
    have h := ladderOdd_laplacian_on_even_left_exit hden hagree hperiod hpar hr
    change laplacian field (reflectLadderOdd den (x, y)) = 0 at h
    rw [laplacian_ladderOddField_reflection hden hagree hperiod] at h
    rw [h]
    apply Eq.symm
    apply if_neg
    simp only [LadderOddLeftExit, reflectLadderOdd, Prod.fst_sub, Prod.snd_sub] at hr
    simp only [LadderOddEvenBlack]
    omega
  have hn : (x - 1, y) ∈ (BaseMask.ladderOdd.raw den).sites :=
    not_not.mp (fun h => hl (hleft.mp h))
  have hp : (x + 1, y) ∈ (BaseMask.ladderOdd.raw den).sites :=
    not_not.mp (fun h => hr (hright.mp h))
  rw [ladderOdd_interior_laplacian hagree hpoint
      (by simpa only [incomingNeg, if_pos heven] using hn)
      (by simpa only [incomingPos, if_pos heven] using hp),
    laplacian_ladderOddBackground hd, if_pos heven]
  simp only [incomingNeg, incomingPos, if_pos heven]
  have hnBump : ¬ BaseMask.LadderOddBump den (x - 1, y) := by
    simp only [BaseMask.LadderOddBump]
    omega
  have hpBump : ¬ BaseMask.LadderOddBump den (x + 1, y) := by
    simp only [BaseMask.LadderOddBump]
    omega
  have hcenter : BaseMask.LadderOddBump den (x, y) ↔
      x + y = den + 2 ∧ 2 ≤ y ∧ y ≤ den := by
    simp only [LadderOddLeftExit, reflectLadderOdd, Prod.fst_sub, Prod.snd_sub] at hl hr
    simp only [BaseMask.LadderOddBump]
    omega
  rw [if_neg hnBump, if_neg hpBump, if_congr hcenter rfl rfl]
  obtain ⟨hx, hy, hshape⟩ := BaseMask.mem_ladderOdd_raw_iff.mp hpoint
  simp only [BaseMask.LadderOddCorner] at hshape
  dsimp only at hx hy
  simp only [LadderOddEvenBlack]
  by_cases hdiag : x + y = den + 2
  · have hrow : 1 ≤ y ∧ y ≤ den + 1 := by omega
    clear hshape
    by_cases hy1 : y = 1
    · simp (disch := omega) only [if_pos, if_neg]
      omega
    · by_cases hyLast : y = den + 1
      · simp (disch := omega) only [if_pos, if_neg]
        omega
      · simp (disch := omega) only [if_pos, if_neg]
        omega
  · by_cases hx1 : x = 1
    · simp (disch := omega) only [if_pos, if_neg]
      omega
    · by_cases hxLast : x = den + 1 <;>
        (simp (disch := omega) only [if_pos, if_neg]; omega)

theorem ladderOdd_laplacian_on_odd_raw {den x y : ℤ} (hden : BaseMask.ladderOdd.Valid den)
    {field : Field} (hagree : (BaseMask.ladderOdd.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den))
    (hpoint : (x, y) ∈ (BaseMask.ladderOdd.raw den).sites) (hodd : ¬ EvenSite (x, y)) :
    laplacian field (x, y) = if LadderOddOddWhite den (x, y) then 0 else -1 := by
  have hmin := hden.1
  have hd := hden.2
  have hxy : (x + y) % 2 ≠ 0 := hodd
  by_cases hlo : LadderOddLowerBoundary den (x, y)
  · rw [ladderOdd_laplacian_on_odd_lower_exit hden hagree hperiod hodd hlo, if_pos (Or.inl hlo)]
  by_cases hup : LadderOddLowerBoundary den (reflectLadderOdd den (x, y))
  · have hpar : ¬ EvenSite (reflectLadderOdd den (x, y)) :=
      fun h => hodd ((evenSite_reflectLadderOdd_iff den (x, y)).mp h)
    have h := ladderOdd_laplacian_on_odd_lower_exit hden hagree hperiod hpar hup
    change laplacian field (reflectLadderOdd den (x, y)) = 0 at h
    rw [laplacian_ladderOddField_reflection hden hagree hperiod] at h
    rw [h, if_pos (Or.inr (Or.inl hup))]
  have hn : (x, y - 1) ∈ (BaseMask.ladderOdd.raw den).sites :=
    not_not.mp (fun h => hlo ((ladderOdd_down_notMem_iff hden hpoint hxy).mp h))
  have hp : (x, y + 1) ∈ (BaseMask.ladderOdd.raw den).sites :=
    not_not.mp (fun h => hup ((ladderOdd_up_notMem_iff hden hpoint hodd).mp h))
  rw [ladderOdd_interior_laplacian hagree hpoint
      (by simpa only [incomingNeg, if_neg hodd] using hn)
      (by simpa only [incomingPos, if_neg hodd] using hp),
    laplacian_ladderOddBackground hd, if_neg hodd]
  simp only [incomingNeg, incomingPos, if_neg hodd]
  have hc : ¬ BaseMask.LadderOddBump den (x, y) := by
    simp only [BaseMask.LadderOddBump]
    omega
  obtain ⟨_, hy, _⟩ := BaseMask.mem_ladderOdd_raw_iff.mp hpoint
  dsimp only at hy
  have hwhite : LadderOddOddWhite den (x, y) ↔
      BaseMask.LadderOddBump den (x, y - 1) ∨ BaseMask.LadderOddBump den (x, y + 1) := by
    simp only [LadderOddOddWhite, hlo, hup, false_or, BaseMask.LadderOddBump]
    omega
  have hdisjoint : ¬ (BaseMask.LadderOddBump den (x, y - 1) ∧ BaseMask.LadderOddBump den (x, y + 1)) := by
    simp only [BaseMask.LadderOddBump]
    omega
  rw [if_neg hc, if_congr hwhite rfl rfl]
  by_cases hnb : BaseMask.LadderOddBump den (x, y - 1)
  · have hpb : ¬ BaseMask.LadderOddBump den (x, y + 1) := fun h => hdisjoint ⟨hnb, h⟩
    simp [hnb, hpb]
  · by_cases hpb : BaseMask.LadderOddBump den (x, y + 1) <;> simp [hnb, hpb]

/-- The B5 charge table on the actual occupied representatives. -/
theorem ladderOdd_laplacian_on_raw {den : ℤ} (hden : BaseMask.ladderOdd.Valid den)
    {field : Field} (hagree : (BaseMask.ladderOdd.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den))
    (point : Site) (hpoint : point ∈ (BaseMask.ladderOdd.raw den).sites) :
    laplacian field point = if EvenSite point then (if LadderOddEvenBlack den point then -1 else 0)
      else (if LadderOddOddWhite den point then 0 else -1) := by
  obtain ⟨x, y⟩ := point
  by_cases he : EvenSite (x, y)
  · simpa only [if_pos he] using ladderOdd_laplacian_on_even_raw hden hagree hperiod hpoint he
  · simpa only [if_neg he] using ladderOdd_laplacian_on_odd_raw hden hagree hperiod hpoint he

theorem ladderOdd_binary_laplacian {den : ℤ} (hden : BaseMask.ladderOdd.Valid den)
    {field : Field} (hagree : (BaseMask.ladderOdd.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den))
    (point : Site) : laplacian field point = -1 ∨ laplacian field point = 0 := by
  have hinterval : (Fraction.mk 1 den).InUnitInterval := by
    have := hden.1
    exact ⟨by dsimp; omega, by change (0 : ℤ) ≤ 1; decide, by dsimp; omega⟩
  obtain ⟨site, hsite, hspan⟩ := ladderOdd_raw_cover hden point
  have h := laplacian_periodic_of_generatorPeriods hinterval hperiod hspan site
  rw [show site + (point - site) = point by rw [add_comm, sub_add_cancel],
    ladderOdd_laplacian_on_raw hden hagree hperiod site hsite] at h
  rw [h]
  split <;> split <;> simp

end FLatticePaper.Construction
