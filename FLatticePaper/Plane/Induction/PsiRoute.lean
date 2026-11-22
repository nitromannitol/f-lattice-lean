import FLatticePaper.Plane.Induction.SlipPermits

/-! The Psi route to `OddBlackNoRise` (task 40), stated as a conditional lemma.

The archive's argument for the slip monotonicity runs through the sheet difference `Ψ` (STRONG_PRICE section 3:
`D+(w) = −min(0, Ψ(w + X))`, and "the earlier Ψ monotonicity gives the desired inequality"). If the slip difference
satisfies the identity `D z = −min(0, Ψ(z + X))` and `Ψ` does not decrease from an input's shifted site to the centre's
shifted site, then the slip increments are nonpositive at every site, in particular at odd black sites.

Both hypotheses are the new inputs of this route. Neither is a consequence of the headline inputs, and the archive
writes the identity only for native V points. -/

namespace FLatticePaper

open Farey FLatticePaper.Induction

/-- The Psi route: an identity for the slip difference in terms of `Ψ`, and monotonicity of `Ψ` along the input edges,
give the nonpositive slip increments at every site. -/
theorem oddBlackNoRise_of_psi (F : Field) (σ X : Site) (Ψ : Site → ℤ)
    (hformula : ∀ z : Site, starDiff F σ z = -min 0 (Ψ (z + X)))
    (hmono : ∀ c i : Site, (i = incomingNeg c ∨ i = incomingPos c) → Ψ (c + X) ≤ Ψ (i + X)) :
    OddBlackNoRise F σ := by
  intro c _ _ i hi
  show slipIncrement F (fun z => F (z + σ)) c i ≤ 0
  have hD := hformula i
  have hC := hformula c
  have hm := min_le_min (le_refl (0 : ℤ)) (hmono c i hi)
  unfold starDiff at hD hC
  unfold slipIncrement
  simp only at hD hC ⊢
  linarith

end FLatticePaper
