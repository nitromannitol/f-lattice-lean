import FLatticePaper.Plane.Induction.StarRangeArgument
import FLatticePaper.Plane.Induction.RankFromForts

/-! `PermitLocal` for the slip permits of `F` against `F(· + σ)` (task 39).

Write `D = starDiff F σ = F − F(· + σ)`. At a site `c` with inputs `i₁ = incomingNeg c`, `i₂ = incomingPos c`, the slip
increments are `eᵢ = D(i) − D(c)`, and they satisfy:
* `e₁ + e₂ = laplacian D c = laplacian F c − laplacian F (c + σ)` (`laplacian_starDiff`), which lies in `{−1,0}` at a
  black site (`laplacian F c = −1`) and in `{0,1}` at a white site;
* `eᵢ ∈ {−1,0,1}` (`HasUnitSlip`);
* at a site with `D c` even, the increments are not `{−1,+1}` (`NoEvenSlipSaddle`).

Hence at a white site one increment is `≤ 0`, and at a black site with `D c` even both are. The one configuration not
excluded by these facts is a black site with `D c` odd and an input with `D` one higher. It is the premise
`OddBlackNoRise`, which is not derived here. -/

namespace FLatticePaper

open Farey FLatticePaper.Induction

/-- The premise that a black site with odd `D` has no input with larger `D`: the one case that the unit slip, the
binarity and the no-even-saddle condition do not exclude. -/
def OddBlackNoRise (F : Field) (σ : Site) : Prop :=
  ∀ c : Site, laplacian F c = -1 → (F c - F (c + σ)) % 2 = 1 →
    ∀ i : Site, (i = incomingNeg c ∨ i = incomingPos c) → slipPermits F (fun z => F (z + σ)) c i

/-- The slip sum at a site is the Laplacian of `D`. -/
theorem slip_sum_eq (F : Field) (σ c : Site) (hσ : EvenSite σ) :
    slipIncrement F (fun z => F (z + σ)) c (incomingNeg c) + slipIncrement F (fun z => F (z + σ)) c (incomingPos c) =
      laplacian F c - laplacian F (c + σ) := by
  rw [← laplacian_starDiff F σ c hσ]
  unfold laplacian slipIncrement starDiff
  ring

/-- `PermitLocal` for the slip permits, from the binarity, the unit slip, the no-even-saddle condition and the odd
black premise. -/
theorem permitLocal_of_star_data {F : Field} {σ : Site} (hσ : EvenSite σ)
    (hbin : ∀ z, laplacian F z = -1 ∨ laplacian F z = 0)
    (hU : HasUnitSlip F (fun z => F (z + σ)))
    (hS2 : NoEvenSlipSaddle F (fun z => F (z + σ)))
    (hodd : OddBlackNoRise F σ) :
    PermitLocal F (slipPermits F (fun z => F (z + σ))) := by
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · -- black sites
    by_cases hpar : (F c - F (c + σ)) % 2 = 1
    · exact ⟨hodd c hc hpar _ (Or.inl rfl), hodd c hc hpar _ (Or.inr rfl)⟩
    · have hpar0 : (F c - F (c + σ)) % 2 = 0 := by omega
      have hS : ¬ ((slipIncrement F (fun z => F (z + σ)) c (incomingNeg c) = -1 ∧
          slipIncrement F (fun z => F (z + σ)) c (incomingPos c) = 1) ∨
          (slipIncrement F (fun z => F (z + σ)) c (incomingNeg c) = 1 ∧
          slipIncrement F (fun z => F (z + σ)) c (incomingPos c) = -1)) := hS2 c hpar0
      have hsum := slip_sum_eq F σ c hσ
      have hU1 := hU c (incomingNeg c) (Or.inl rfl)
      have hU2 := hU c (incomingPos c) (Or.inr rfl)
      have hb2 := hbin (c + σ)
      rw [hc] at hsum
      show slipIncrement F (fun z => F (z + σ)) c (incomingNeg c) ≤ 0 ∧
        slipIncrement F (fun z => F (z + σ)) c (incomingPos c) ≤ 0
      omega
  · -- white sites
    have hsum := slip_sum_eq F σ c hσ
    have hU1 := hU c (incomingNeg c) (Or.inl rfl)
    have hU2 := hU c (incomingPos c) (Or.inr rfl)
    have hb2 := hbin (c + σ)
    rw [hc] at hsum
    show slipIncrement F (fun z => F (z + σ)) c (incomingNeg c) ≤ 0 ∨
      slipIncrement F (fun z => F (z + σ)) c (incomingPos c) ≤ 0
    omega

end FLatticePaper
