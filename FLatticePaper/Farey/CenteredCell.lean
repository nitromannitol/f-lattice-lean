import FLatticePaper.Farey.PeriodDeck
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

namespace FLatticePaper.Farey.PeriodDeck

/-- The half-shifted period cell of the literal-initializer coverage argument.
We can take the two upper endpoints to be open when choosing representatives. -/
def InHalfShiftedCell (deck : PeriodDeck) (point : Site) : Prop :=
  ∃ alongKernel alongTransverse : ℝ,
    0 ≤ alongKernel ∧ alongKernel < 1 ∧ 0 ≤ alongTransverse ∧ alongTransverse < 1 ∧
    (point.1 : ℝ) = 1 / 2 + alongKernel * deck.kernel.1 + alongTransverse * deck.transverse.1 ∧
    (point.2 : ℝ) = -(1 / 2) + alongKernel * deck.kernel.2 + alongTransverse * deck.transverse.2

theorem exists_halfShiftedCell_representative (deck : PeriodDeck) (hnonsingular : deck.det ≠ 0)
    (site : Site) :
    ∃ point : Site, deck.InHalfShiftedCell point ∧ site - point ∈ deck.span := by
  have hdet : (deck.det : ℝ) ≠ 0 := by exact_mod_cast hnonsingular
  let first : ℝ := (site.1 : ℝ) - 1 / 2
  let second : ℝ := (site.2 : ℝ) + 1 / 2
  let alongKernel : ℝ :=
    ((deck.transverse.2 : ℝ) * first - (deck.transverse.1 : ℝ) * second) / (deck.det : ℝ)
  let alongTransverse : ℝ :=
    ((deck.kernel.1 : ℝ) * second - (deck.kernel.2 : ℝ) * first) / (deck.det : ℝ)
  have hfirst : first =
      alongKernel * (deck.kernel.1 : ℝ) + alongTransverse * (deck.transverse.1 : ℝ) := by
    dsimp only [alongKernel, alongTransverse]
    field_simp
    simp only [det, Int.cast_sub, Int.cast_mul]
    ring
  have hsecond : second =
      alongKernel * (deck.kernel.2 : ℝ) + alongTransverse * (deck.transverse.2 : ℝ) := by
    dsimp only [alongKernel, alongTransverse]
    field_simp
    simp only [det, Int.cast_sub, Int.cast_mul]
    ring
  let point := site - deck.combine ⌊alongKernel⌋ ⌊alongTransverse⌋
  refine ⟨point, ?_, ⟨⌊alongKernel⌋, ⌊alongTransverse⌋, sub_sub_cancel ..⟩⟩
  refine ⟨Int.fract alongKernel, Int.fract alongTransverse, Int.fract_nonneg _, Int.fract_lt_one _,
    Int.fract_nonneg _, Int.fract_lt_one _, ?_, ?_⟩
  · dsimp only [point, combine, Int.fract, Prod.fst_sub]
    push_cast
    dsimp only [first] at hfirst
    linear_combination hfirst
  · dsimp only [point, combine, Int.fract, Prod.snd_sub]
    push_cast
    dsimp only [second] at hsecond
    linear_combination hsecond

theorem covers_of_halfShiftedCell (deck : PeriodDeck) (hnonsingular : deck.det ≠ 0)
    (sites : Finset Site)
    (hpay : ∀ point, deck.InHalfShiftedCell point →
      ∃ representative ∈ sites, point - representative ∈ deck.span) :
    deck.Covers sites := by
  intro site
  obtain ⟨point, hcell, hpoint⟩ := deck.exists_halfShiftedCell_representative hnonsingular site
  obtain ⟨representative, hmem, hrep⟩ := hpay point hcell
  have hclass := deck.classCode_eq_iff hnonsingular
  exact ⟨representative, hmem,
    (hclass ..).mp (((hclass ..).mpr hpoint).trans ((hclass ..).mpr hrep))⟩

end FLatticePaper.Farey.PeriodDeck
