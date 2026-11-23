import FLatticePaper.Plane.Induction.StrongPriceInputs
import FLatticePaper.Plane.Induction.StrongUnitPrice
import FLatticePaper.Plane.Induction.StrongVStar

/-! Task 70 (b): the deck-layer window of a star, the unit fields from star windows, and the deck representative of a site with the price
changing by the drift (P(x + lV + kU) = P x - k). -/

namespace FLatticePaper.StrongDeckSpan

open Farey FLatticePaper FLatticePaper.Induction

/-- The star of a centre: the centre and its two physical inputs. -/
def IsStar (c x : Site) : Prop := x = c ∨ x = FLatticePaper.incomingNeg c ∨ x = FLatticePaper.incomingPos c

/-- **(b) The deck-layer window.** If the star of `c` lies in `E` after the kernel shift `k`, its primitive prices lie in `[c₀ − 1 + k, c₀ + k]`. -/
theorem star_window_of_common_layer (frame : ChildFrame) (F : Field)
    (hPR : ∀ w ∈ frame.closedPolygon, frame.cutPrice - 1 ≤ frame.price F w ∧ frame.price F w ≤ frame.cutPrice)
    (hPU : ∀ w, frame.price F (w + frame.child.modifiedDeck.kernel) = frame.price F w - 1)
    (c : Site) (k : ℤ) (hL : ∀ x, IsStar c x → x + k • frame.child.modifiedDeck.kernel ∈ frame.closedPolygon) :
    ∀ x, IsStar c x → frame.cutPrice - 1 + k ≤ frame.price F x ∧ frame.price F x ≤ frame.cutPrice + k := by
  intro x hx
  have h1 := StrongPriceRange.price_zsmul_kernel frame F hPU x k
  have h2 := hPR _ (hL x hx)
  constructor <;> linarith [h1, h2.1, h2.2]

/-- **(b) The unit fields from star windows.** If each star has all its primitive prices in a window `[a, a + 1]`, then the price has unit
increments and no saddle. -/
theorem unitPrice_of_star_windows (frame : ChildFrame) (F : Field)
    (hwin : ∀ c, ∃ a : ℤ, ∀ x, IsStar c x → a ≤ frame.price F x ∧ frame.price F x ≤ a + 1) :
    HasUnitPrice frame F ∧ NoPriceSaddle frame F := by
  constructor
  · intro center input hE
    have hin : input = FLatticePaper.incomingNeg center ∨ input = FLatticePaper.incomingPos center := hE
    obtain ⟨a, ha⟩ := hwin center
    have hi := ha input (Or.inr hin)
    have hc := ha center (Or.inl rfl)
    unfold priceIncrement
    constructor <;> linarith [hi.1, hi.2, hc.1, hc.2]
  · intro site
    obtain ⟨a, ha⟩ := hwin site
    have hn := ha (FLatticePaper.incomingNeg site) (Or.inr (Or.inl rfl))
    have hp := ha (FLatticePaper.incomingPos site) (Or.inr (Or.inr rfl))
    have hs := ha site (Or.inl rfl)
    unfold priceIncrement
    simp only
    omega

/-- **(b) Every site has a deck representative in `E`.** A transverse shift puts the `t`-grade into the `t`-range of `E`, and then a kernel
shift puts the `s`-grade into the closed polygon (`StrongVStar.exists_kernel_mem_of_tWindow`). -/
theorem deck_rep_mem (frame : ChildFrame) (x : Site) :
    ∃ l k : ℤ, x + l • frame.child.modifiedDeck.transverse + k • frame.child.modifiedDeck.kernel ∈ frame.closedPolygon := by
  obtain ⟨l, hpar, hw⟩ := StrongPriceRange.exists_transverse_t_window frame x
  obtain ⟨k, hk⟩ := StrongVStar.exists_kernel_mem_of_tWindow frame (x + l • frame.child.modifiedDeck.transverse)
    ⟨fun hy => hw.1 (hpar.mp hy), fun hy => hw.2 (fun h => hy (hpar.mpr h))⟩
  exact ⟨l, k, hk⟩

/-- **(b) The price changes by the drift along the deck.** At the representative `x + lV + kU ∈ E`, `P x = P(rep) + k`. -/
theorem price_of_deck_rep (frame : ChildFrame) (F : Field)
    (hPU : ∀ w, frame.price F (w + frame.child.modifiedDeck.kernel) = frame.price F w - 1)
    (hPV : ∀ w, frame.price F (w + frame.child.modifiedDeck.transverse) = frame.price F w)
    (x : Site) (l k : ℤ) :
    frame.price F (x + l • frame.child.modifiedDeck.transverse + k • frame.child.modifiedDeck.kernel) =
      frame.price F x - k := by
  rw [StrongPriceRange.price_zsmul_kernel frame F hPU (x + l • frame.child.modifiedDeck.transverse) k,
    StrongHSpan.price_zsmul_transverse frame F hPV x l]

end FLatticePaper.StrongDeckSpan
