import FLatticePaper.Construction.QuarterTurnCorrection

/-! The harmonic function `h_0` of the standard-case proof of `lemma:global_odometers` (the rotation step):
`h_0(x) = (1/4)(-x_1^2 - 2 x_1 x_2 + x_2^2 + 2 x_2 + 1{(x_1+x_2) odd})`, integer-valued with `Δh_0 = 0` on Z^2.
This is the negative of the centered quarter-turn correction `K` already in Lean
(`Construction.centeredQuarterTurnCorrection`, with `Harmonic K` by `harmonic_centeredQuarterTurnCorrection`). -/

namespace FLatticePaper

open FLatticePaper.Construction

/-- `h_0` is harmonic, and `4 h_0` is the integer polynomial of the manuscript's formula. -/
theorem surgical_h0_integer_harmonic :
    Harmonic (fun x : Site => -centeredQuarterTurnCorrection x) ∧
      ∀ x : Site, 4 * (-centeredQuarterTurnCorrection x) =
        -(x.1 ^ 2) - 2 * x.1 * x.2 + x.2 ^ 2 + 2 * x.2 + (x.1 + x.2) % 2 := by
  refine ⟨?_, fun x => ?_⟩
  · intro site
    have hK := harmonic_centeredQuarterTurnCorrection site
    simp only [laplacian] at hK ⊢
    linarith
  · linear_combination (-1 : ℤ) * four_mul_centeredQuarterTurnCorrection x

end FLatticePaper
