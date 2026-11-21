import FLatticePaper.Construction.PeriodExtension
import FLatticePaper.Plane.PeriodCocycle
import FLatticePaper.Plane.Induction.Sheets

namespace FLatticePaper.Induction
open Farey Construction

/-- A function respects the period law on a set: deck-related points of the set carry the prescribed increment. -/
def RespectsPeriodsOn (fraction : Fraction) (constantU constantV : ℤ) (S : Set Site) (g : Site → ℤ) : Prop :=
  ∀ y ∈ S, ∀ i j : ℤ, y + fraction.modifiedDeck.combine i j ∈ S →
    g (y + fraction.modifiedDeck.combine i j) = g y + periodIncrement fraction constantU constantV y i j

private theorem periodization_combine_add (deck : PeriodDeck) (i j i' j' : ℤ) :
    deck.combine (i + i') (j + j') = deck.combine i j + deck.combine i' j' := by
  apply Prod.ext <;> simp only [PeriodDeck.combine, Prod.fst_add, Prod.snd_add] <;> ring

private theorem periodization_combine_sub (deck : PeriodDeck) (i j i' j' : ℤ) :
    deck.combine (i - i') (j - j') = deck.combine i j - deck.combine i' j' := by
  apply Prod.ext <;> simp only [PeriodDeck.combine, Prod.fst_sub, Prod.snd_sub] <;> ring

/-- The existence half, with no interval hypothesis: a representative choice in `S` for each site
defines the field, and the period law on `S` makes the value independent of the representative. -/
private theorem exists_field_of_respectsPeriodsOn {fraction : Fraction}
    {constantU constantV : ℤ} {S : Set Site} {g : Site → ℤ}
    (hcover : ∀ z, ∃ y ∈ S, ∃ i j : ℤ, z = y + fraction.modifiedDeck.combine i j)
    (hcompat : RespectsPeriodsOn fraction constantU constantV S g) :
    ∃ field : Field, (∀ y ∈ S, field y = g y) ∧ HasGeneratorPeriods fraction field constantU constantV := by
  classical
  choose point hmem kernel transverse hchart using hcover
  obtain ⟨field, hfield⟩ : ∃ field : Field, ∀ z, field z =
      g (point z) + periodIncrement fraction constantU constantV (point z) (kernel z) (transverse z) :=
    ⟨_, fun z => rfl⟩
  -- the value at `z` computed from any representative `y ∈ S` of `z` agrees with `field z`
  have key : ∀ z y i j, y ∈ S → z = y + fraction.modifiedDeck.combine i j →
      field z = g y + periodIncrement fraction constantU constantV y i j := by
    intro z y i j hy hz
    rw [hfield z]
    have hyz : y + fraction.modifiedDeck.combine i j =
        point z + fraction.modifiedDeck.combine (kernel z) (transverse z) := hz.symm.trans (hchart z)
    have hy' : y = point z + fraction.modifiedDeck.combine (kernel z - i) (transverse z - j) := by
      rw [periodization_combine_sub, ← add_sub_assoc, ← hyz]
      abel
    have hg := hcompat (point z) (hmem z) (kernel z - i) (transverse z - j) (by rw [← hy']; exact hy)
    rw [← hy'] at hg
    have hsum := periodIncrement_add fraction constantU constantV (point z)
      (kernel z - i) (transverse z - j) i j
    rw [← hy', sub_add_cancel, sub_add_cancel] at hsum
    rw [hg, hsum]
    ring
  -- the generator law: moving `z` by a deck translation adds the increment at `z`
  have hlaw : ∀ z i j, field (z + fraction.modifiedDeck.combine i j) =
      field z + periodIncrement fraction constantU constantV z i j := by
    intro z i j
    have hzc : z + fraction.modifiedDeck.combine i j =
        point z + fraction.modifiedDeck.combine (kernel z + i) (transverse z + j) := by
      rw [periodization_combine_add, ← add_assoc, ← hchart z]
    have h1 := key (z + fraction.modifiedDeck.combine i j) (point z) (kernel z + i) (transverse z + j)
      (hmem z) hzc
    have h2 := key z (point z) (kernel z) (transverse z) (hmem z) (hchart z)
    have hsum := periodIncrement_add fraction constantU constantV (point z) (kernel z) (transverse z) i j
    rw [← hchart z] at hsum
    rw [h1, h2, hsum]
    ring
  refine ⟨field, fun y hy => ?_, ?_⟩
  · have h := key y y 0 0 hy (by simp [PeriodDeck.combine])
    rw [h]
    simp [periodIncrement, chooseTwo]
  · refine ⟨?_, ?_⟩
    · intro site
      simpa [PeriodDeck.combine, periodIncrement, chooseTwo] using hlaw site 1 0
    · intro site
      have h := hlaw site 0 1
      simp [PeriodDeck.combine, periodIncrement, chooseTwo] at h
      linarith only [h]

/-- A function on a set meeting every deck class, with the period law on the set, extends uniquely to a field with
the generator identities. -/
theorem exists_unique_extension_of_respectsPeriodsOn {fraction : Fraction} (hinterval : fraction.InUnitInterval)
    {constantU constantV : ℤ} {S : Set Site} {g : Site → ℤ}
    (hcover : ∀ z, ∃ y ∈ S, ∃ i j : ℤ, z = y + fraction.modifiedDeck.combine i j)
    (hcompat : RespectsPeriodsOn fraction constantU constantV S g) :
    ∃ field : Field, (∀ y ∈ S, field y = g y) ∧ HasGeneratorPeriods fraction field constantU constantV ∧
      ∀ other : Field, (∀ y ∈ S, other y = g y) →
        HasGeneratorPeriods fraction other constantU constantV → other = field := by
  obtain ⟨field, hagree, hperiod⟩ := exists_field_of_respectsPeriodsOn hcover hcompat
  refine ⟨field, hagree, hperiod, fun other hother hperiodOther => ?_⟩
  funext z
  obtain ⟨y, hy, i, j, hz⟩ := hcover z
  have hlawO := generator_period_formula hinterval hperiodOther y i j
  have hlawF := generator_period_formula hinterval hperiod y i j
  have hyO : (other y : ℝ) = (field y : ℝ) := by rw [hother y hy, hagree y hy]
  have hreal : (other (y + fraction.modifiedDeck.combine i j) : ℝ) =
      (field (y + fraction.modifiedDeck.combine i j) : ℝ) := by
    linear_combination hlawO - hlawF + hyO
  rw [hz]
  exact_mod_cast hreal

/-- The sewn standard of a frame: the periodization of a function on `E`. -/
theorem ChildFrame.exists_unique_periodization (frame : ChildFrame) {constantU constantV : ℤ} {g : Site → ℤ}
    (hcompat : RespectsPeriodsOn frame.child constantU constantV frame.closedPolygon g) :
    ∃ field : Field, (∀ y ∈ frame.closedPolygon, field y = g y) ∧
      HasGeneratorPeriods frame.child field constantU constantV ∧
      ∀ other : Field, (∀ y ∈ frame.closedPolygon, other y = g y) →
        HasGeneratorPeriods frame.child other constantU constantV → other = field := by
  have hint : frame.child.Interior := frame.valid.current_interior .even
  exact exists_unique_extension_of_respectsPeriodsOn hint.inUnitInterval frame.closedPolygon_covers hcompat

end FLatticePaper.Induction
