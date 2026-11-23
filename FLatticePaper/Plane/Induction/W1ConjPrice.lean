import FLatticePaper.Plane.Induction.StrongDeckSpan
import FLatticePaper.Plane.Induction.StrongEstimates

/-! # Task 72 (3): the conjugate's primitive price at any site

For the strong estimates `S` of the conjugate word `u`, with `P' = (frameAt u).price (standardField u)`:
the price range `c₀' − 1 ≤ P' ≤ c₀'` holds on the closed polygon `E'`, and the drifts are `P'(z + U) = P'(z) − 1` and
`P'(z + V) = P'(z)` (`priceDrift`). Through a deck representative `y = w + lV + kU ∈ E'` (`deck_rep_mem`), the price at any site
`w` is the price at `y` shifted by `k` (`price_of_deck_rep`). So the conjugate's price at `w` lies in `[c₀' − 1 + k, c₀' + k]`. -/

namespace FLatticePaper.W1ConjPrice

open Farey FLatticePaper FLatticePaper.Induction

/-- The conjugate's price at any site: its deck representative `y ∈ E'` has the price range, and the price at the site is that
price shifted by the kernel count `k`. -/
theorem conj_price_at_site {u : Word} (hS : StrongEstimates u) (w : Site) :
    ∃ l k : ℤ,
      w + l • (frameAt u).child.modifiedDeck.transverse + k • (frameAt u).child.modifiedDeck.kernel ∈
        (frameAt u).closedPolygon ∧
      (frameAt u).cutPrice - 1 + k ≤ (frameAt u).price (standardField u) w ∧
      (frameAt u).price (standardField u) w ≤ (frameAt u).cutPrice + k := by
  obtain ⟨l, k, hmem⟩ := StrongDeckSpan.deck_rep_mem (frameAt u) w
  have hPU : ∀ s : Site, (frameAt u).price (standardField u) (s + (frameAt u).child.modifiedDeck.kernel) =
      (frameAt u).price (standardField u) s - 1 := fun s => by linarith [(hS.priceDrift s).1]
  have hPV : ∀ s : Site, (frameAt u).price (standardField u) (s + (frameAt u).child.modifiedDeck.transverse) =
      (frameAt u).price (standardField u) s := fun s => by linarith [(hS.priceDrift s).2]
  have hdeck := StrongDeckSpan.price_of_deck_rep (frameAt u) (standardField u) hPU hPV w l k
  have hr := hS.priceRange _ hmem
  exact ⟨l, k, hmem, by linarith [hr.1], by linarith [hr.2]⟩

end FLatticePaper.W1ConjPrice
