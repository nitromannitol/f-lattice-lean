import FLatticePaper.Construction.PeriodExtension
import FLatticePaper.Endpoint
import FLatticePaper.Plane.QuarterTurn

namespace FLatticePaper.Construction

/-- The harmonic correction `K` of the base duality identity, read one row
above the physical chart so the horizontal inputs occur at even sites. -/
def centeredQuarterTurnCorrection (point : Site) : ℤ :=
  chooseTwo point.1 - (point.1 - point.2 - 1) ^ 2 / 4

theorem four_mul_centeredQuarterTurnCorrection (point : Site) :
    4 * centeredQuarterTurnCorrection point = point.1 ^ 2 + 2 * point.1 * point.2 - point.2 ^ 2 -
      2 * point.2 - (point.1 + point.2) % 2 := by
  have hphase : (point.1 - point.2 - 1) % 2 = 1 - (point.1 + point.2) % 2 := by omega
  unfold centeredQuarterTurnCorrection
  linear_combination 2 * two_mul_chooseTwo point.1 -
    four_mul_square_div_four (point.1 - point.2 - 1) + hphase

theorem harmonic_centeredQuarterTurnCorrection : Harmonic centeredQuarterTurnCorrection := by
  rintro ⟨x, y⟩
  apply mul_left_cancel₀ (show (4 : ℤ) ≠ 0 by decide)
  by_cases heven : EvenSite (x, y)
  · have hp : (x + y) % 2 = 0 := heven
    have hn : (x - 1 + y) % 2 = 1 := by omega
    have hs : (x + 1 + y) % 2 = 1 := by omega
    have hcenter := four_mul_centeredQuarterTurnCorrection (x, y)
    have hneg := four_mul_centeredQuarterTurnCorrection (x - 1, y)
    have hpos := four_mul_centeredQuarterTurnCorrection (x + 1, y)
    simp only [hp, hn, hs] at hcenter hneg hpos
    simp only [laplacian, incomingNeg, incomingPos, if_pos heven]
    linear_combination hneg + hpos - 2 * hcenter
  · have hp : (x + y) % 2 = 1 := by change (x + y) % 2 ≠ 0 at heven; omega
    have hn : (x + (y - 1)) % 2 = 0 := by omega
    have hs : (x + (y + 1)) % 2 = 0 := by omega
    have hcenter := four_mul_centeredQuarterTurnCorrection (x, y)
    have hneg := four_mul_centeredQuarterTurnCorrection (x, y - 1)
    have hpos := four_mul_centeredQuarterTurnCorrection (x, y + 1)
    simp only [hp, hn, hs] at hcenter hneg hpos
    simp only [laplacian, incomingNeg, incomingPos, if_neg heven]
    linear_combination hneg + hpos - 2 * hcenter

/-- The exact integral affine increment of the centered correction along an
even vector. Its value at the zero site is zero. -/
theorem centeredQuarterTurnCorrection_add (point : Site) {offset : Site} (heven : EvenSite offset) :
    centeredQuarterTurnCorrection (point + offset) = centeredQuarterTurnCorrection point +
      centeredQuarterTurnCorrection offset + ((offset.1 + offset.2) / 2) * point.1 +
      ((offset.1 - offset.2) / 2) * point.2 := by
  have hv : (offset.1 + offset.2) % 2 = 0 := heven
  have hphase : (point.1 + offset.1 + (point.2 + offset.2)) % 2 = (point.1 + point.2) % 2 := by omega
  have hsum : 2 * ((offset.1 + offset.2) / 2) = offset.1 + offset.2 := by omega
  have hdiff : 2 * ((offset.1 - offset.2) / 2) = offset.1 - offset.2 := by omega
  have hpoint := four_mul_centeredQuarterTurnCorrection point
  have hoffset := four_mul_centeredQuarterTurnCorrection offset
  have hshift := four_mul_centeredQuarterTurnCorrection (point + offset)
  simp only [Prod.fst_add, Prod.snd_add, hphase] at hshift
  rw [hv] at hoffset
  apply mul_left_cancel₀ (show (4 : ℤ) ≠ 0 by decide)
  linear_combination hshift - hpoint - hoffset - 2 * point.1 * hsum - 2 * point.2 * hdiff

end FLatticePaper.Construction
