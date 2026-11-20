import FLatticePaper.Plane.AlternateMidpoint

namespace FLatticePaper

/-- The threshold field uses the minimum of the first sheet and a constant
translate of the second sheet. -/
def thresholdMin (first second : Field) (level : ℤ) : Field :=
  fun site => min (first site) (second site + level)

def thresholdGap (first second : Field) (level : ℤ) : Field :=
  fun site => first site - second site - level

theorem thresholdGap_eq_add_slip (first second : Field) (level : ℤ) (center input : Site) :
    thresholdGap first second level input =
      thresholdGap first second level center + slipIncrement first second center input := by
  unfold thresholdGap slipIncrement
  omega

/-- First compare minus the distance from the tie band, then the winning
sheet's rank. At a tie this version uses the first sheet's rank. -/
def leftThresholdRank {α : Type*} (first second : Field) (level : ℤ)
    (firstRank secondRank : Site → α) : Site → ℤ ×ₗ α :=
  fun site =>
    let gap := thresholdGap first second level site
    toLex (min gap (-gap), if gap ≤ 0 then firstRank site else secondRank site)

def rightThresholdRank {α : Type*} (first second : Field) (level : ℤ)
    (firstRank secondRank : Site → α) : Site → ℤ ×ₗ α :=
  leftThresholdRank second first (-level) secondRank firstRank

theorem leftThresholdRank_eq_at_tie {α : Type*} {first second : Field} {level : ℤ}
    {firstRank secondRank : Site → α} {site : Site} (h : thresholdGap first second level site = 0) :
    leftThresholdRank first second level firstRank secondRank site = toLex (0, firstRank site) := by
  simp [leftThresholdRank, h]

theorem thresholdGap_swap (first second : Field) (level : ℤ) (site : Site) :
    thresholdGap second first (-level) site = -thresholdGap first second level site := by
  unfold thresholdGap
  omega

theorem slipIncrement_swap (first second : Field) (center input : Site) :
    slipIncrement second first center input = -slipIncrement first second center input := by
  unfold slipIncrement
  omega

private theorem thresholdMin_of_nonpos {first second : Field} {level : ℤ} {site : Site}
    (h : thresholdGap first second level site ≤ 0) :
    thresholdMin first second level site = first site := by
  unfold thresholdGap at h
  exact min_eq_left (by omega)

private theorem thresholdMin_of_nonneg {first second : Field} {level : ℤ} {site : Site}
    (h : 0 ≤ thresholdGap first second level site) :
    thresholdMin first second level site = second site + level := by
  unfold thresholdGap at h
  exact min_eq_right (by omega)

private theorem thresholdMin_eq_sub_max (first second : Field) (level : ℤ) (site : Site) :
    thresholdMin first second level site =
      first site - max (thresholdGap first second level site) 0 := by
  by_cases h : thresholdGap first second level site ≤ 0
  · rw [thresholdMin_of_nonpos h, max_eq_right h]
    omega
  · have h' : 0 ≤ thresholdGap first second level site := by omega
    rw [thresholdMin_of_nonneg h', max_eq_left h']
    unfold thresholdGap
    omega

private theorem laplacian_thresholdMin_eq_sub_max (first second : Field) (level : ℤ) (site : Site) :
    laplacian (thresholdMin first second level) site = laplacian first site -
      max (thresholdGap first second level (incomingNeg site)) 0 -
      max (thresholdGap first second level (incomingPos site)) 0 +
      2 * max (thresholdGap first second level site) 0 := by
  simp only [laplacian, thresholdMin_eq_sub_max]
  omega

private theorem grade_nonpos {gap : ℤ} (h : gap ≤ 0) : min gap (-gap) = gap :=
  min_eq_left (by omega)

private theorem grade_nonneg {gap : ℤ} (h : 0 ≤ gap) : min gap (-gap) = -gap :=
  min_eq_right (by omega)

private theorem leftThresholdRank_lt_of_neg {α : Type*} [LT α]
    {first second : Field} {level : ℤ} {firstRank secondRank : Site → α} {center input : Site}
    (hc : thresholdGap first second level center < 0)
    (hstep : slipIncrement first second center input ≤ 0)
    (hrank : firstRank input < firstRank center) :
    leftThresholdRank first second level firstRank secondRank input <
      leftThresholdRank first second level firstRank secondRank center := by
  have hg := thresholdGap_eq_add_slip first second level center input
  have hi : thresholdGap first second level input ≤ thresholdGap first second level center := by omega
  have hin : thresholdGap first second level input ≤ 0 := by omega
  simp only [leftThresholdRank, Prod.Lex.toLex_lt_toLex, if_pos hc.le, if_pos hin,
    grade_nonpos hc.le, grade_nonpos hin]
  exact (lt_or_eq_of_le hi).elim Or.inl (fun h => Or.inr ⟨h, hrank⟩)

private theorem leftThresholdRank_lt_of_pos {α : Type*} [LT α]
    {first second : Field} {level : ℤ} {firstRank secondRank : Site → α} {center input : Site}
    (hc : 0 < thresholdGap first second level center)
    (hstep : 0 ≤ slipIncrement first second center input)
    (hrank : secondRank input < secondRank center) :
    leftThresholdRank first second level firstRank secondRank input <
      leftThresholdRank first second level firstRank secondRank center := by
  have hg := thresholdGap_eq_add_slip first second level center input
  have hi : thresholdGap first second level center ≤ thresholdGap first second level input := by omega
  have hin : 0 < thresholdGap first second level input := by omega
  simp only [leftThresholdRank, Prod.Lex.toLex_lt_toLex, if_neg (not_le_of_gt hc),
    if_neg (not_le_of_gt hin), grade_nonneg hc.le, grade_nonneg hin.le]
  exact (lt_or_eq_of_le (by omega :
    -thresholdGap first second level input ≤ -thresholdGap first second level center)).elim
      Or.inl (fun h => Or.inr ⟨h, hrank⟩)

/-- From a tie, off-band inputs lower the first coordinate. Within the band
the order is exactly that of the first sheet. -/
theorem leftThresholdRank_lt_iff_of_tie {α : Type*} [LT α]
    {first second : Field} {level : ℤ} {firstRank secondRank : Site → α} {center input : Site}
    (hc : thresholdGap first second level center = 0) :
    leftThresholdRank first second level firstRank secondRank input <
      leftThresholdRank first second level firstRank secondRank center ↔
    thresholdGap first second level input ≠ 0 ∨ firstRank input < firstRank center := by
  by_cases hi : thresholdGap first second level input = 0
  · simp [leftThresholdRank, Prod.Lex.toLex_lt_toLex, hc, hi]
  · have hneg : min (thresholdGap first second level input)
        (-thresholdGap first second level input) < 0 := by
      by_cases hnonpos : thresholdGap first second level input ≤ 0
      · rw [grade_nonpos hnonpos]
        omega
      · rw [grade_nonneg (by omega)]
        omega
    simp [leftThresholdRank, Prod.Lex.toLex_lt_toLex, hc, hi, hneg]

private theorem requiredInputs_mono {delta : ℤ} {neg pos neg' pos' : Prop}
    (h : (delta = -1 ∧ neg ∧ pos) ∨ (delta = 0 ∧ (neg ∨ pos)))
    (hn : neg → neg') (hp : pos → pos') :
    (delta = -1 ∧ neg' ∧ pos') ∨ (delta = 0 ∧ (neg' ∨ pos')) := by
  rcases h with ⟨hlap, hneg, hpos⟩ | ⟨hlap, hneg | hpos⟩
  · exact Or.inl ⟨hlap, hn hneg, hp hpos⟩
  · exact Or.inr ⟨hlap, Or.inl (hn hneg)⟩
  · exact Or.inr ⟨hlap, Or.inr (hp hpos)⟩

private theorem thresholdTieStar (firstDelta negStep posStep : ℤ)
    (negFirst posFirst negSecond posSecond : Prop)
    (hneg : -1 ≤ negStep ∧ negStep ≤ 1) (hpos : -1 ≤ posStep ∧ posStep ≤ 1)
    (hfirst : (firstDelta = -1 ∧ (negStep ≤ 0 ∧ negFirst) ∧ (posStep ≤ 0 ∧ posFirst)) ∨
      (firstDelta = 0 ∧ ((negStep ≤ 0 ∧ negFirst) ∨ (posStep ≤ 0 ∧ posFirst))))
    (hsecond : let secondDelta := firstDelta - negStep - posStep
      (secondDelta = -1 ∧ (0 ≤ negStep ∧ negSecond) ∧ (0 ≤ posStep ∧ posSecond)) ∨
      (secondDelta = 0 ∧ ((0 ≤ negStep ∧ negSecond) ∨ (0 ≤ posStep ∧ posSecond)))) :
    let delta := firstDelta - max negStep 0 - max posStep 0
    let neg := negStep ≠ 0 ∨ negFirst
    let pos := posStep ≠ 0 ∨ posFirst
    (delta = -1 ∧ neg ∧ pos) ∨ (delta = 0 ∧ (neg ∨ pos)) := by
  have hnegCases : negStep = -1 ∨ negStep = 0 ∨ negStep = 1 := by omega
  have hposCases : posStep = -1 ∨ posStep = 0 ∨ posStep = 1 := by omega
  dsimp only at hsecond ⊢
  rcases hfirst with ⟨rfl, hfirst⟩ | ⟨rfl, hfirst⟩ <;>
    rcases hnegCases with rfl | rfl | rfl <;> rcases hposCases with rfl | rfl | rfl <;>
    simp_all

/-- The local plane induction step for every integer threshold, with the
first sheet's rank preferred at ties. Both input constraints remain explicit. -/
theorem isBurningRank_leftThreshold {α : Type*} [LT α] {first second : Field}
    {firstRank secondRank : Site → α} (level : ℤ) (hunit : HasUnitSlip first second)
    (hfirst : IsConstrainedBurningRank first firstRank
      (fun center input => slipIncrement first second center input ≤ 0))
    (hsecond : IsConstrainedBurningRank second secondRank
      (fun center input => 0 ≤ slipIncrement first second center input)) :
    IsBurningRank (thresholdMin first second level)
      (leftThresholdRank first second level firstRank secondRank) := by
  intro center
  have hn := hunit center (incomingNeg center) (Or.inl rfl)
  have hp := hunit center (incomingPos center) (Or.inr rfl)
  have hnGap := thresholdGap_eq_add_slip first second level center (incomingNeg center)
  have hpGap := thresholdGap_eq_add_slip first second level center (incomingPos center)
  rcases lt_trichotomy (thresholdGap first second level center) 0 with hc | hc | hc
  · have hlap : laplacian (thresholdMin first second level) center = laplacian first center := by
      simp only [laplacian, thresholdMin_of_nonpos hc.le,
        thresholdMin_of_nonpos (by omega : thresholdGap first second level (incomingNeg center) ≤ 0),
        thresholdMin_of_nonpos (by omega : thresholdGap first second level (incomingPos center) ≤ 0)]
    rw [hlap]
    exact requiredInputs_mono (hfirst center)
      (fun h => leftThresholdRank_lt_of_neg hc h.1 h.2)
      (fun h => leftThresholdRank_lt_of_neg hc h.1 h.2)
  · have hb := hsecond center
    dsimp only at hb
    rw [laplacian_eq_sub_slipIncrements first second center] at hb
    rw [laplacian_thresholdMin_eq_sub_max first second level center, hc,
      leftThresholdRank_lt_iff_of_tie hc, leftThresholdRank_lt_iff_of_tie hc, hnGap, hpGap]
    simp only [hc, Int.zero_add, max_self, Int.mul_zero, Int.add_zero]
    exact thresholdTieStar _ _ _ _ _ _ _ hn hp (hfirst center) hb
  · have hlap : laplacian (thresholdMin first second level) center = laplacian second center := by
      simp only [laplacian, thresholdMin_of_nonneg hc.le,
        thresholdMin_of_nonneg (by omega : 0 ≤ thresholdGap first second level (incomingNeg center)),
        thresholdMin_of_nonneg (by omega : 0 ≤ thresholdGap first second level (incomingPos center))]
      omega
    rw [hlap]
    exact requiredInputs_mono (hsecond center)
      (fun h => leftThresholdRank_lt_of_pos hc h.1 h.2)
      (fun h => leftThresholdRank_lt_of_pos hc h.1 h.2)

private theorem thresholdMin_eq_swap_add (first second : Field) (level : ℤ) (site : Site) :
    thresholdMin first second level site = thresholdMin second first (-level) site + level := by
  unfold thresholdMin
  omega

theorem isBurningRank_rightThreshold {α : Type*} [LT α] {first second : Field}
    {firstRank secondRank : Site → α} (level : ℤ) (hunit : HasUnitSlip first second)
    (hfirst : IsConstrainedBurningRank first firstRank
      (fun center input => slipIncrement first second center input ≤ 0))
    (hsecond : IsConstrainedBurningRank second secondRank
      (fun center input => 0 ≤ slipIncrement first second center input)) :
    IsBurningRank (thresholdMin first second level)
      (rightThresholdRank first second level firstRank secondRank) := by
  have hunit' : HasUnitSlip second first := by
    intro center input hedge
    have := hunit center input hedge
    rw [slipIncrement_swap]
    omega
  have hsecond' : IsConstrainedBurningRank second secondRank
      (fun center input => slipIncrement second first center input ≤ 0) := by
    have hpermits (center input : Site) :
        slipIncrement second first center input ≤ 0 ↔ 0 ≤ slipIncrement first second center input := by
      rw [slipIncrement_swap]
      omega
    simpa only [IsConstrainedBurningRank, hpermits] using hsecond
  have hfirst' : IsConstrainedBurningRank first firstRank
      (fun center input => 0 ≤ slipIncrement second first center input) := by
    have hpermits (center input : Site) :
        0 ≤ slipIncrement second first center input ↔ slipIncrement first second center input ≤ 0 := by
      rw [slipIncrement_swap]
      omega
    simpa only [IsConstrainedBurningRank, hpermits] using hfirst
  intro center
  have hlap : laplacian (thresholdMin first second level) center =
      laplacian (thresholdMin second first (-level)) center := by
    simp only [laplacian, thresholdMin_eq_swap_add first second level]
    omega
  rw [hlap]
  exact isBurningRank_leftThreshold (-level) hunit' hsecond' hfirst' center

theorem rightThresholdRank_lt_iff_of_tie {α : Type*} [LT α]
    {first second : Field} {level : ℤ} {firstRank secondRank : Site → α} {center input : Site}
    (hc : thresholdGap first second level center = 0) :
    rightThresholdRank first second level firstRank secondRank input <
      rightThresholdRank first second level firstRank secondRank center ↔
    thresholdGap first second level input ≠ 0 ∨ secondRank input < secondRank center := by
  have hc' : thresholdGap second first (-level) center = 0 := by rw [thresholdGap_swap, hc]; omega
  unfold rightThresholdRank
  have hne : -thresholdGap first second level input ≠ 0 ↔
      thresholdGap first second level input ≠ 0 := by omega
  rw [leftThresholdRank_lt_iff_of_tie hc', thresholdGap_swap, hne]

theorem rightThresholdRank_eq_at_tie {α : Type*} {first second : Field} {level : ℤ}
    {firstRank secondRank : Site → α} {site : Site} (h : thresholdGap first second level site = 0) :
    rightThresholdRank first second level firstRank secondRank site = toLex (0, secondRank site) := by
  apply leftThresholdRank_eq_at_tie
  rw [thresholdGap_swap, h]
  omega

end FLatticePaper
