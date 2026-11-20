import FLatticePaper.Plane.ThresholdMinimum
import Mathlib.Data.Finset.Card

namespace FLatticePaper

variable {κ : Type*} [DecidableEq κ]

/-- Count the still unburned inputs on the band. This counts physical slots,
even if the quotient identifies their two classes. -/
def pendingBandInputs (gap : Field) (classOf : Site → κ) (remaining : Finset κ)
    (center : Site) : ℤ :=
  (if gap (incomingNeg center) = 0 ∧ classOf (incomingNeg center) ∈ remaining then 1 else 0) +
  (if gap (incomingPos center) = 0 ∧ classOf (incomingPos center) ∈ remaining then 1 else 0)

def BandClassBurnable (field gap : Field) (classOf : Site → κ) (remaining : Finset κ)
    (cell : κ) : Prop :=
  ∀ center, gap center = 0 → classOf center = cell →
    pendingBandInputs gap classOf remaining center ≤ laplacian field center + 1

/-- A sequential burn of exactly the listed classes, after all off-band
inputs have burned. Each step is valid at every physical site of that class. -/
def BandBurns (field gap : Field) (classOf : Site → κ) (remaining : Finset κ) : List κ → Prop
  | [] => remaining = ∅
  | cell :: rest => cell ∈ remaining ∧ BandClassBurnable field gap classOf remaining cell ∧
      BandBurns field gap classOf (remaining.erase cell) rest

theorem exists_burnable_bandClass_of_rank {α : Type*} [LinearOrder α] {field : Field}
    {rank : Site → α} (hrank : IsBurningRank field rank) (gap : Field)
    (classOf : Site → κ) (classRank : κ → α) (remaining : Finset κ) (hne : remaining.Nonempty)
    (hperiod : ∀ site, gap site = 0 → classOf site ∈ remaining → rank site = classRank (classOf site)) :
    ∃ cell ∈ remaining, BandClassBurnable field gap classOf remaining cell := by
  obtain ⟨cell, hcell, hmin⟩ := remaining.exists_min_image classRank hne
  refine ⟨cell, hcell, ?_⟩
  intro center hc heq
  have hmem : classOf center ∈ remaining := heq.symm ▸ hcell
  have outside (input : Site) (hlt : rank input < rank center) :
      ¬ (gap input = 0 ∧ classOf input ∈ remaining) := by
    rintro ⟨htie, hin⟩
    rw [hperiod input htie hin, hperiod center hc hmem, heq] at hlt
    exact (not_lt_of_ge (hmin (classOf input) hin)) hlt
  unfold pendingBandInputs
  rcases hrank center with ⟨hlap, hneg, hpos⟩ | ⟨hlap, hneg | hpos⟩
  · simp [hlap, outside _ hneg, outside _ hpos]
  · simp only [hlap, outside _ hneg, if_false]
    split <;> omega
  · simp only [hlap, outside _ hpos, if_false]
    split <;> omega

theorem exists_bandBurnOrder_of_rank {α : Type*} [LinearOrder α] {field : Field}
    {rank : Site → α} (hrank : IsBurningRank field rank) (gap : Field)
    (classOf : Site → κ) (classRank : κ → α) (classes : Finset κ)
    (hperiod : ∀ site, gap site = 0 → classOf site ∈ classes → rank site = classRank (classOf site)) :
    ∃ order, BandBurns field gap classOf classes order := by
  have gain (remaining : Finset κ) (hsub : remaining ⊆ classes) :
      ∃ order, BandBurns field gap classOf remaining order := by
    refine remaining.strongInductionOn
      (p := fun rem => rem ⊆ classes → ∃ order, BandBurns field gap classOf rem order) ?_ hsub
    intro rem ih hrem
    rcases rem.eq_empty_or_nonempty with hempty | hne
    · exact ⟨[], hempty⟩
    · obtain ⟨first, hfirst, hburn⟩ := exists_burnable_bandClass_of_rank hrank gap classOf
        classRank rem hne (fun site htie hmem => hperiod site htie (hrem hmem))
      obtain ⟨rest, hrest⟩ :=
        ih (rem.erase first) (Finset.erase_ssubset hfirst) ((Finset.erase_subset ..).trans hrem)
      exact ⟨first :: rest, hfirst, hburn, hrest⟩
  exact gain classes Finset.Subset.rfl

/-- A period-compatible tie rank of the first sheet suffices to burn any
finite family of classes on the tie band, without a rank off the band
factoring through the quotient. The threshold field itself is on the plane. -/
theorem exists_leftThreshold_bandBurnOrder {α : Type*} [LinearOrder α] {first second : Field}
    {firstRank secondRank : Site → α} (level : ℤ) (hunit : HasUnitSlip first second)
    (hfirst : IsConstrainedBurningRank first firstRank
      (fun center input => slipIncrement first second center input ≤ 0))
    (hsecond : IsConstrainedBurningRank second secondRank
      (fun center input => 0 ≤ slipIncrement first second center input))
    (classOf : Site → κ) (classRank : κ → α) (classes : Finset κ)
    (hperiod : ∀ site, thresholdGap first second level site = 0 → classOf site ∈ classes →
      firstRank site = classRank (classOf site)) :
    ∃ order, BandBurns (thresholdMin first second level) (thresholdGap first second level)
      classOf classes order := by
  apply exists_bandBurnOrder_of_rank (isBurningRank_leftThreshold level hunit hfirst hsecond)
    _ _ (fun cell => toLex (0, classRank cell))
  intro site htie hmem
  rw [leftThresholdRank_eq_at_tie htie, hperiod site htie hmem]

theorem exists_rightThreshold_bandBurnOrder {α : Type*} [LinearOrder α] {first second : Field}
    {firstRank secondRank : Site → α} (level : ℤ) (hunit : HasUnitSlip first second)
    (hfirst : IsConstrainedBurningRank first firstRank
      (fun center input => slipIncrement first second center input ≤ 0))
    (hsecond : IsConstrainedBurningRank second secondRank
      (fun center input => 0 ≤ slipIncrement first second center input))
    (classOf : Site → κ) (classRank : κ → α) (classes : Finset κ)
    (hperiod : ∀ site, thresholdGap first second level site = 0 → classOf site ∈ classes →
      secondRank site = classRank (classOf site)) :
    ∃ order, BandBurns (thresholdMin first second level) (thresholdGap first second level)
      classOf classes order := by
  apply exists_bandBurnOrder_of_rank (isBurningRank_rightThreshold level hunit hfirst hsecond)
    _ _ (fun cell => toLex (0, classRank cell))
  intro site htie hmem
  rw [rightThresholdRank_eq_at_tie htie, hperiod site htie hmem]

end FLatticePaper
