import FLatticePaper.Construction.StaircaseExtension
import FLatticePaper.Plane.AlternateSlip

namespace FLatticePaper.Construction

open Farey

private def background (point : Site) : ℤ :=
  -chooseTwo point.2 + min (point.1 - 1) 0

private def reflect (den : ℤ) (point : Site) : Site := (2, den + 1) - point

private def reflectionConstant (den : ℤ) : ℤ := 1 - chooseTwo (den + 1)

private theorem reflect_mem_iff (den : ℤ) (point : Site) :
    reflect den point ∈ (BaseMask.stairEven.raw den).sites ↔ point ∈ (BaseMask.stairEven.raw den).sites := by
  simp only [BaseMask.mem_stairEven_raw_iff, BaseMask.StairEvenCorner, reflect,
    Prod.fst_sub, Prod.snd_sub]
  omega

private theorem corner_reflect_iff (den : ℤ) (point : Site) :
    BaseMask.StairEvenCorner den (reflect den point) ↔ BaseMask.StairEvenCorner den point := by
  simp only [BaseMask.StairEvenCorner, reflect, Prod.fst_sub, Prod.snd_sub]
  omega

private theorem reflect_even_iff {den : ℤ} (hodd : den % 2 = 1) (point : Site) :
    EvenSite (reflect den point) ↔ EvenSite point := by
  simp only [EvenSite, reflect, Prod.fst_sub, Prod.snd_sub]
  omega

private theorem background_reflect (den : ℤ) (point : Site) :
    background (reflect den point) = background point +
      (Fraction.mk 1 den).transverseGrade point + reflectionConstant den := by
  have hbinom : chooseTwo (den + 1 - point.2) =
      chooseTwo (den + 1) + chooseTwo point.2 - den * point.2 := by
    apply mul_left_cancel₀ (show (2 : ℤ) ≠ 0 by decide)
    linear_combination two_mul_chooseTwo (den + 1 - point.2) - two_mul_chooseTwo (den + 1) -
      two_mul_chooseTwo point.2
  simp only [background, reflect, Prod.fst_sub, Prod.snd_sub, hbinom, Fraction.transverseGrade,
    one_mul, reflectionConstant]
  by_cases hx : point.1 ≤ 1
  · rw [min_eq_right (by omega : 0 ≤ 2 - point.1 - 1), min_eq_left (by omega : point.1 - 1 ≤ 0)]
    omega
  · rw [min_eq_left (by omega : 2 - point.1 - 1 ≤ 0), min_eq_right (by omega : 0 ≤ point.1 - 1)]
    omega

private theorem value_eq_background {den : ℤ} {field : Field}
    (hagree : (BaseMask.stairEven.raw den).Agrees field 0) {point : Site}
    (hpoint : point ∈ (BaseMask.stairEven.raw den).sites) :
    field point = background point + (if BaseMask.StairEvenCorner den point then 1 else 0) := by
  have h := hagree ⟨point, hpoint⟩
  rw [BaseMask.stairEven_raw_height] at h
  simpa only [BaseMask.stairEvenValue, background, chooseTwo, add_zero] using h.symm

private theorem kernel_height {den : ℤ} (hodd : den % 2 = 1) {field : Field}
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den))
    (point : Site) : field (point + (den, 1)) = field point := by
  have h := hperiod.1 point
  change field (point + (reciprocalEvenDeck den).kernel) = _ at h
  simpa only [reciprocalEvenDeck_eq hodd, add_zero] using h

private theorem transverse_height {den : ℤ} (hodd : den % 2 = 1) {field : Field}
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den))
    (point : Site) : field (point + (1 - den, den + 1)) =
      field point - (Fraction.mk 1 den).transverseGrade point + stairEvenConstantV den := by
  have h := hperiod.2 point
  change field (point + (reciprocalEvenDeck den).transverse) = _ at h
  simpa only [reciprocalEvenDeck_eq hodd, add_comm 1 den] using h

/-- The B1 central reflection has the exact affine height increment of L24. -/
theorem stairEven_reflection {den : ℤ} (hden : BaseMask.stairEven.Valid den) {field : Field}
    (hagree : (BaseMask.stairEven.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den))
    (point : Site) : field ((2, den + 1) - point) = field point +
      (Fraction.mk 1 den).transverseGrade point + (1 - chooseTwo (den + 1)) := by
  let slope := Fraction.mk 1 den
  let reflected : Field := fun x => field (reflect den x) - slope.transverseGrade x - reflectionConstant den
  have hinterval : slope.InUnitInterval := by
    have := hden.1
    exact ⟨by dsimp [slope]; omega, by change (0 : ℤ) ≤ 1; decide, by dsimp [slope]; omega⟩
  have hperiod' : HasGeneratorPeriods slope reflected 0 (stairEvenConstantV den) := by
    constructor
    · intro site
      change reflected (site + (reciprocalEvenDeck den).kernel) = reflected site + 0
      rw [reciprocalEvenDeck_eq hden.2]
      have hp := kernel_height hden.2 hperiod (reflect den (site + (den, 1)))
      have heq : reflect den (site + (den, 1)) + (den, 1) = reflect den site := by
        apply Prod.ext <;> dsimp [reflect] <;> ring
      rw [heq] at hp
      have hgrade : slope.transverseGrade (site + (den, 1)) = slope.transverseGrade site := by
        dsimp [slope, Fraction.transverseGrade]
        ring
      dsimp only [reflected]
      rw [← hp, hgrade, add_zero]
    · intro site
      change reflected (site + (reciprocalEvenDeck den).transverse) =
        reflected site - slope.transverseGrade site + stairEvenConstantV den
      rw [reciprocalEvenDeck_eq hden.2, add_comm 1 den]
      have hp := transverse_height hden.2 hperiod (reflect den (site + (1 - den, den + 1)))
      have heq : reflect den (site + (1 - den, den + 1)) + (1 - den, den + 1) = reflect den site := by
        apply Prod.ext <;> dsimp [reflect] <;> ring
      rw [heq] at hp
      dsimp only [reflected]
      simp only [slope, Fraction.transverseGrade, reflect, Prod.fst_add, Prod.snd_add,
        Prod.fst_sub, Prod.snd_sub, one_mul, stairEvenConstantV] at hp ⊢
      linear_combination -hp + two_mul_chooseTwo (den + 1)
  have heq := eq_of_covered_generator_periods hinterval hperiod' hperiod (stairEven_raw_cover hden)
    (fun site hsite => by
      have hr := value_eq_background hagree ((reflect_mem_iff den site).mpr hsite)
      have hs := value_eq_background hagree hsite
      rw [background_reflect, if_congr (corner_reflect_iff den site) rfl rfl] at hr
      change field (reflect den site) - slope.transverseGrade site - reflectionConstant den = field site
      dsimp only [slope]
      omega)
  have hp := congrFun heq point
  change field ((2, den + 1) - point) - (Fraction.mk 1 den).transverseGrade point -
    (1 - chooseTwo (den + 1)) = field point at hp
  omega

private theorem residual_reflect {den : ℤ} (hden : BaseMask.stairEven.Valid den) {field : Field}
    (hagree : (BaseMask.stairEven.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den))
    (point : Site) :
    field (reflect den point) - background (reflect den point) = field point - background point := by
  have hf := stairEven_reflection hden hagree hperiod point
  change field (reflect den point) = _ at hf
  rw [hf, background_reflect]
  unfold reflectionConstant
  omega

/-- The west or lower B1 seam paid by `+U`, with the corner term absent at the representative. -/
private theorem value_kernel_representative {den : ℤ} (hden : BaseMask.stairEven.Valid den)
    {field : Field} (hagree : (BaseMask.stairEven.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den))
    (point : Site) (hleft : point.1 ≤ 1) (hrep : 1 ≤ point.1 + den)
    (hmem : point + (den, 1) ∈ (BaseMask.stairEven.raw den).sites)
    (hcorner : ¬ BaseMask.StairEvenCorner den (point + (den, 1))) :
    field point = background point + (1 - point.1 - point.2) := by
  have hz := value_eq_background hagree hmem
  rw [kernel_height hden.2 hperiod, if_neg hcorner, add_zero] at hz
  have hbinom : chooseTwo (point.2 + 1) = chooseTwo point.2 + point.2 := by
    simpa [chooseTwo] using chooseTwo_add point.2 1
  simp only [background, Prod.fst_add, Prod.snd_add, hbinom,
    min_eq_right (by omega : 0 ≤ point.1 + den - 1)] at hz
  rw [hz, background, min_eq_left (by omega : point.1 - 1 ≤ 0)]
  omega

private theorem residual_left {den : ℤ} (hden : BaseMask.stairEven.Valid den) {field : Field}
    (hagree : (BaseMask.stairEven.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den))
    {x y : ℤ} (hcenter : (x, y) ∈ (BaseMask.stairEven.raw den).sites)
    (heven : (x + y) % 2 = 0) :
    field (x - 1, y) - background (x - 1, y) = if x = 0 ∧ y = 0 then 2 else 0 := by
  have hmin := hden.1
  have hodd := hden.2
  obtain ⟨hx, hy, hband⟩ := BaseMask.mem_stairEven_raw_iff.mp hcenter
  simp only [BaseMask.StairEvenCorner] at hband
  by_cases horigin : x = 0 ∧ y = 0
  · obtain ⟨rfl, rfl⟩ := horigin
    rw [if_pos (by decide : (0 : ℤ) = 0 ∧ (0 : ℤ) = 0)]
    have hp : ((-1, 0) : Site) + (den, 1) ∈ (BaseMask.stairEven.raw den).sites := by
      apply BaseMask.mem_stairEven_body <;> dsimp <;> omega
    have hr := value_kernel_representative hden hagree hperiod (-1, 0) (by decide)
      (by dsimp; omega) hp (by simp only [BaseMask.StairEvenCorner, Prod.fst_add, Prod.snd_add]; omega)
    change field (-1, 0) - background (-1, 0) = 2
    dsimp at hr
    omega
  · rw [if_neg horigin]
    by_cases hboundary : x = 2 - den ∧ y = den
    · obtain ⟨hcol, hrow⟩ := hboundary
      subst x
      subst y
      have hp : ((2 - den - 1, den) : Site) + (den, 1) ∈ (BaseMask.stairEven.raw den).sites := by
        apply BaseMask.mem_stairEven_body <;> dsimp <;> omega
      have hr := value_kernel_representative hden hagree hperiod (2 - den - 1, den)
        (by dsimp; omega) (by dsimp; omega) hp
        (by simp only [BaseMask.StairEvenCorner, Prod.fst_add, Prod.snd_add]; omega)
      dsimp at hr
      omega
    · have hp : (x - 1, y) ∈ (BaseMask.stairEven.raw den).sites := by
        apply BaseMask.mem_stairEven_body <;> dsimp at * <;> omega
      have hc : ¬ BaseMask.StairEvenCorner den (x - 1, y) := by
        simp only [BaseMask.StairEvenCorner]
        omega
      rw [value_eq_background hagree hp, if_neg hc, add_zero, sub_self]

private theorem residual_down {den : ℤ} (hden : BaseMask.stairEven.Valid den) {field : Field}
    (hagree : (BaseMask.stairEven.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den))
    {x y : ℤ} (hcenter : (x, y) ∈ (BaseMask.stairEven.raw den).sites)
    (hodd : (x + y) % 2 ≠ 0) :
    field (x, y - 1) - background (x, y - 1) = if y = 0 ∨ x + y = 1 then 1 else 0 := by
  have hmin := hden.1
  have hdOdd := hden.2
  obtain ⟨hx, hy, hband⟩ := BaseMask.mem_stairEven_raw_iff.mp hcenter
  simp only [BaseMask.StairEvenCorner] at hband
  by_cases hbottom : y = 0
  · subst y
    rw [if_pos (Or.inl rfl)]
    have hp : ((x, -1) : Site) + (1 - den, den + 1) ∈ (BaseMask.stairEven.raw den).sites := by
      apply BaseMask.mem_stairEven_body <;> dsimp at * <;> omega
    have hcorner : ¬ BaseMask.StairEvenCorner den (((x, -1) : Site) + (1 - den, den + 1)) := by
      simp only [BaseMask.StairEvenCorner, Prod.fst_add, Prod.snd_add]
      omega
    have hz := value_eq_background hagree hp
    rw [transverse_height hdOdd hperiod, if_neg hcorner, add_zero] at hz
    have hbinom : chooseTwo (den + 1) = chooseTwo den + den := by
      simpa [chooseTwo] using chooseTwo_add den 1
    have hyRep : (-1 : ℤ) + (den + 1) = den := by omega
    simp only [background, Fraction.transverseGrade, Prod.fst_add, Prod.snd_add, one_mul, mul_neg,
      mul_one, hyRep, min_eq_left (by dsimp at *; omega : x + (1 - den) - 1 ≤ 0),
      stairEvenConstantV, hbinom] at hz
    change field (x, -1) - background (x, -1) = 1
    simp only [background, min_eq_right (by dsimp at *; omega : 0 ≤ x - 1),
      show chooseTwo (-1) = 1 from rfl, add_zero]
    omega
  · by_cases hdiagonal : x + y = 1
    · rw [if_pos (Or.inr hdiagonal)]
      by_cases hfirst : y = 1
      · have heq : (x, y - 1) = ((0, 0) : Site) := Prod.ext (by dsimp; omega) (by dsimp; omega)
        have hp : (0, 0) ∈ (BaseMask.stairEven.raw den).sites := by
          apply BaseMask.mem_stairEven_raw_iff.mpr
          refine ⟨⟨by dsimp; omega, by dsimp; omega⟩, ⟨by decide, by dsimp; omega⟩, Or.inl (Or.inl ⟨rfl,rfl⟩)⟩
        rw [heq, value_eq_background hagree hp,
          if_pos (show BaseMask.StairEvenCorner den (0, 0) from Or.inl ⟨rfl, rfl⟩)]
        omega
      · have hp : ((x, y - 1) : Site) + (den, 1) ∈ (BaseMask.stairEven.raw den).sites := by
          apply BaseMask.mem_stairEven_body <;> dsimp at * <;> omega
        have hz := value_kernel_representative hden hagree hperiod (x, y - 1)
          (by dsimp at *; omega) (by dsimp at *; omega) hp
          (by simp only [BaseMask.StairEvenCorner, Prod.fst_add, Prod.snd_add]; dsimp at *; omega)
        dsimp at hz
        omega
    · rw [if_neg (not_or.mpr ⟨hbottom, hdiagonal⟩)]
      have hp : (x, y - 1) ∈ (BaseMask.stairEven.raw den).sites := by
        apply BaseMask.mem_stairEven_body <;> dsimp at * <;> omega
      have hc : ¬ BaseMask.StairEvenCorner den (x, y - 1) := by
        simp only [BaseMask.StairEvenCorner]
        omega
      rw [value_eq_background hagree hp, if_neg hc, add_zero, sub_self]

private theorem residual_right {den : ℤ} (hden : BaseMask.stairEven.Valid den) {field : Field}
    (hagree : (BaseMask.stairEven.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den))
    {x y : ℤ} (hcenter : (x, y) ∈ (BaseMask.stairEven.raw den).sites)
    (heven : (x + y) % 2 = 0) :
    field (x + 1, y) - background (x + 1, y) = if x = 2 ∧ y = den + 1 then 2 else 0 := by
  have hp : (2 - x, den + 1 - y) ∈ (BaseMask.stairEven.raw den).sites :=
    (reflect_mem_iff den (x, y)).mpr hcenter
  have hpEven : (2 - x + (den + 1 - y)) % 2 = 0 :=
    (reflect_even_iff hden.2 (x, y)).mpr heven
  have hl := residual_left hden hagree hperiod hp hpEven
  have hs := residual_reflect hden hagree hperiod (x + 1, y)
  change field (2 - (x + 1), den + 1 - y) - background (2 - (x + 1), den + 1 - y) = _ at hs
  rw [show 2 - (x + 1) = 2 - x - 1 by omega, hl] at hs
  rw [← hs]
  split <;> split <;> omega

private theorem residual_up {den : ℤ} (hden : BaseMask.stairEven.Valid den) {field : Field}
    (hagree : (BaseMask.stairEven.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den))
    {x y : ℤ} (hcenter : (x, y) ∈ (BaseMask.stairEven.raw den).sites)
    (hodd : (x + y) % 2 ≠ 0) :
    field (x, y + 1) - background (x, y + 1) = if y = den + 1 ∨ x + y = den + 2 then 1 else 0 := by
  have hp : (2 - x, den + 1 - y) ∈ (BaseMask.stairEven.raw den).sites :=
    (reflect_mem_iff den (x, y)).mpr hcenter
  have hpOdd : (2 - x + (den + 1 - y)) % 2 ≠ 0 :=
    fun h => hodd ((reflect_even_iff hden.2 (x, y)).mp h)
  have hd := residual_down hden hagree hperiod hp hpOdd
  have hs := residual_reflect hden hagree hperiod (x, y + 1)
  change field (2 - x, den + 1 - (y + 1)) - background (2 - x, den + 1 - (y + 1)) = _ at hs
  rw [show den + 1 - (y + 1) = den + 1 - y - 1 by omega, hd] at hs
  rw [← hs]
  split <;> split <;> omega

private theorem background_second_horizontal (x y : ℤ) :
    background (x - 1, y) + background (x + 1, y) - 2 * background (x, y) =
      if x = 1 then -1 else 0 := by
  change -chooseTwo y + min (x - 1 - 1) 0 + (-chooseTwo y + min (x + 1 - 1) 0) -
    2 * (-chooseTwo y + min (x - 1) 0) = _
  by_cases hx : x = 1
  · subst x
    simp
    ring
  · rw [if_neg hx]
    by_cases hlo : x ≤ 0
    · rw [min_eq_left (by omega : x - 1 - 1 ≤ 0), min_eq_left (by omega : x + 1 - 1 ≤ 0),
        min_eq_left (by omega : x - 1 ≤ 0)]
      omega
    · rw [min_eq_right (by omega : 0 ≤ x - 1 - 1), min_eq_right (by omega : 0 ≤ x + 1 - 1),
        min_eq_right (by omega : 0 ≤ x - 1)]
      omega

private theorem background_second_vertical (x y : ℤ) :
    background (x, y - 1) + background (x, y + 1) - 2 * background (x, y) = -1 := by
  have hnext : chooseTwo (y + 1) = chooseTwo y + y := by
    simpa [chooseTwo] using chooseTwo_add y 1
  have hprev : chooseTwo (y - 1) = chooseTwo y + 1 - y := by
    simpa [sub_eq_add_neg, show chooseTwo (-1) = 1 from rfl] using chooseTwo_add y (-1)
  simp only [background, hnext, hprev]
  omega

/-- The exact B1 in-star formula, with inputs evaluated on the physical plane. -/
theorem stairEven_laplacian_on_raw {den : ℤ} (hden : BaseMask.stairEven.Valid den) {field : Field}
    (hagree : (BaseMask.stairEven.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den))
    (point : Site) (hpoint : point ∈ (BaseMask.stairEven.raw den).sites) :
    laplacian field point = if EvenSite point then (if point.1 = 1 then -1 else 0)
      else (if 0 < point.2 ∧ point.2 < den + 1 ∧ 1 < point.1 + point.2 ∧ point.1 + point.2 < den + 2
        then -1 else 0) := by
  obtain ⟨x, y⟩ := point
  have hc := value_eq_background hagree hpoint
  have hdenMin := hden.1
  have hdenOdd := hden.2
  by_cases hp : EvenSite (x, y)
  · have hl := residual_left hden hagree hperiod hpoint hp
    have hr := residual_right hden hagree hperiod hpoint hp
    have hs := background_second_horizontal x y
    have hcorner : (if x = 0 ∧ y = 0 then (2 : ℤ) else 0) + (if x = 2 ∧ y = den + 1 then 2 else 0) =
        2 * (if BaseMask.StairEvenCorner den (x, y) then 1 else 0) := by
      simp only [BaseMask.StairEvenCorner]
      split <;> split <;> split <;> omega
    simp only [laplacian, incomingNeg, incomingPos, if_pos hp]
    omega
  · have hd := residual_down hden hagree hperiod hpoint hp
    have hu := residual_up hden hagree hperiod hpoint hp
    have hs := background_second_vertical x y
    obtain ⟨hx, hy, hband⟩ := BaseMask.mem_stairEven_raw_iff.mp hpoint
    have hpar : (x + y) % 2 ≠ 0 := hp
    have hcorner : ¬ BaseMask.StairEvenCorner den (x, y) := by
      simp only [BaseMask.StairEvenCorner]
      omega
    have hsum := hband.resolve_left hcorner
    have hboundary : (if y = 0 ∨ x + y = 1 then (1 : ℤ) else 0) +
        (if y = den + 1 ∨ x + y = den + 2 then 1 else 0) =
        if 0 < y ∧ y < den + 1 ∧ 1 < x + y ∧ x + y < den + 2 then 0 else 1 := by
      split <;> split <;> split <;> omega
    simp only [laplacian, incomingNeg, incomingPos, if_neg hp, if_neg hcorner, add_zero] at hc ⊢
    split <;> split at hboundary <;> omega

/-- Affine height increments leave the Laplacian invariant under the modified deck. -/
theorem laplacian_periodic_of_generatorPeriods {fraction : Fraction} (hinterval : fraction.InUnitInterval)
    {field : Field} {constantU constantV : ℤ} (hperiod : HasGeneratorPeriods fraction field constantU constantV)
    {offset : Site} (hoffset : offset ∈ fraction.modifiedDeck.span) : Function.Periodic (laplacian field) offset := by
  have heven := ((fraction.mem_modifiedDeck_iff offset).mp hoffset).2
  obtain ⟨i, j, rfl⟩ := hoffset
  intro point
  have hn := generator_period_formula hinterval hperiod (incomingNeg point) i j
  have hp := generator_period_formula hinterval hperiod (incomingPos point) i j
  have hc := generator_period_formula hinterval hperiod point i j
  have hgrade : (fraction.transverseGrade (incomingNeg point) : ℝ) +
      (fraction.transverseGrade (incomingPos point) : ℝ) = 2 * (fraction.transverseGrade point : ℝ) := by
    by_cases he : EvenSite point <;>
      simp only [incomingNeg, incomingPos, he, if_true, if_false, Fraction.transverseGrade] <;>
      push_cast <;> ring
  have hcast : (laplacian field (point + fraction.modifiedDeck.combine i j) : ℝ) =
      (laplacian field point : ℝ) := by
    simp only [laplacian, incomingNeg_add_of_even point _ heven, incomingPos_add_of_even point _ heven,
      Int.cast_add, Int.cast_sub]
    linear_combination hn + hp - 2 * hc - (j : ℝ) * hgrade
  exact_mod_cast hcast

theorem stairEven_binary_laplacian {den : ℤ} (hden : BaseMask.stairEven.Valid den) {field : Field}
    (hagree : (BaseMask.stairEven.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den)) (point : Site) :
    laplacian field point = -1 ∨ laplacian field point = 0 := by
  have hinterval : (Fraction.mk 1 den).InUnitInterval := by
    have := hden.1
    exact ⟨by dsimp; omega, by change (0 : ℤ) ≤ 1; decide, by dsimp; omega⟩
  obtain ⟨site, hsite, hspan⟩ := stairEven_raw_cover hden point
  have h := laplacian_periodic_of_generatorPeriods hinterval hperiod hspan site
  rw [show site + (point - site) = point by rw [add_comm, sub_add_cancel],
    stairEven_laplacian_on_raw hden hagree hperiod site hsite] at h
  rw [h]
  split <;> split <;> simp

/-- The compatible B1 extension has the prescribed growth and binary Laplacian on the plane. -/
theorem stairEven_exists_binary_extension {den : ℤ} (hden : BaseMask.stairEven.Valid den) :
    ∃ field : Field, (BaseMask.stairEven.raw den).Agrees field 0 ∧
      HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den) ∧
      HasQuadraticGrowth field (Fraction.mk 1 den).matrix ∧
      ∀ point, laplacian field point = -1 ∨ laplacian field point = 0 := by
  obtain ⟨field, hagree, hperiod, hgrowth⟩ := stairEven_exists_extension hden
  exact ⟨field, hagree, hperiod, hgrowth, stairEven_binary_laplacian hden hagree hperiod⟩

end FLatticePaper.Construction
