import FLatticePaper.Plane.Induction.PriceReflect
import FLatticePaper.Plane.Induction.PriceDeck
import FLatticePaper.Plane.Induction.FinalRootSlip
import FLatticePaper.Plane.Induction.FreeVOrdinate

/-! Task 72 / Q31 psi (ii): the value at the reflected origin.

`vLast = I + transverse` for any child frame (`FinalRootSlip.vLast_eq_I_add_transverse`), and `vLast ∈ freeV`. The conjugate's price
is constant on its free V cut (`PriceDeck.price_on_freeV`) and invariant along its transverse (`ChainDeck.price_transverse_mul`).
Hence `P'(I) = c₀'`, and `ψ((1,0)) = c₀' − P'(I − Z(1,0)) = c₀' − P'(I) = 0`. -/

namespace FLatticePaper.PriceAtI

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1MSheet

/-- **`P'(I) = c₀'`** for the conjugate. -/
theorem price_reflectI_origin {word : Word} (hSE : StrongEstimates (conjWord word)) :
    (frameAt (conjWord word)).price (standardField (conjWord word)) reflectionI =
      (frameAt (conjWord word)).cutPrice := by
  unfold reflectionI
  set C := frameAt (conjWord word) with hC
  have hp := PriceDeck.price_on_freeV C (standardField (conjWord word)) hSE.packet.strips
    (FreeVOrdinate.vLast_mem_freeV C)
  rw [FinalRootSlip.vLast_eq_I_add_transverse] at hp
  have ht := ChainDeck.price_transverse_mul C hSE.packet 1 ((1, -1) : Site)
  rw [one_smul] at ht
  rw [← ht, hp]

/-- **The jump at the origin vanishes:** `ψ((1, 0)) = 0`. -/
theorem psi_at_one_zero {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word)) :
    FqW word ((1, 0) + (frameAt word).uq) - FqW word (1, 0) = 0 := by
  have hr := PriceReflect.psi_reflect_price h hSE (1, 0)
  have hz : zTurn ((1, 0) : Site) = (0, 0) := by
    unfold zTurn
    ext <;> simp
  rw [hr, hz]
  have hI : reflectionI - (0, 0) = reflectionI := by
    ext <;> simp
  rw [hI, price_reflectI_origin hSE]
  ring

end FLatticePaper.PriceAtI
