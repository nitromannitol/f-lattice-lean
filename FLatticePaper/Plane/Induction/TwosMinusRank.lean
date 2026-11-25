import FLatticePaper.Plane.Induction.TwosTileRho
import FLatticePaper.Plane.Induction.TwosDeckEta

/-! Twos flatness, the rank `rhoTwos` at the tile points for every sign `η`: the sign-general versions of the sign `+1` lemmas
`rhoTwos_tile*` and `rhoTwos_add_U/V` of `TwosTileRho`. The proofs are the same, with the sign-general deck lemmas of
`TwosDeckEta`; the sign `-1` case is used by the minus flatness claim. -/

noncomputable section

namespace FLatticePaper.TwosEPolicy

open FLatticePaper
open scoped Classical

/-- At a tile point, `rhoTwos` (any sign) is the deck value at that point. -/
theorem rhoTwos_tile_eta (η : ℤ) {a x y : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hp : TwosTile a (x, y)) :
    rhoTwos a η (x, y) = deckAt a η x y := by
  unfold rhoTwos
  rw [tilePoint_classKey_of_tile ha he2 hp]

/-- A free H tile point has the H value (any sign). -/
theorem rhoTwos_tile_freeH_eta (η : ℤ) {a x y : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hp : TwosTile a (x, y))
    (hF : FreeHSite a x y) : rhoTwos a η (x, y) = freeH a η x y := by
  rw [rhoTwos_tile_eta η ha he2 hp, deck_freeH_eta η hF]

/-- A free V tile point (not free H) has the V value (any sign). -/
theorem rhoTwos_tile_freeV_eta (η : ℤ) {a x y : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hp : TwosTile a (x, y))
    (hnH : ¬ FreeHSite a x y) (hV : FreeVSite a x y) : rhoTwos a η (x, y) = freeV a η x y := by
  rw [rhoTwos_tile_eta η ha he2 hp, deck_freeV_eta η hnH hV]

/-- A non-free tile point other than `(a, 2a-1)` has the bulk value (any sign). -/
theorem rhoTwos_tile_bulk_eta (η : ℤ) {a x y : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hp : TwosTile a (x, y))
    (hF : ¬ FreeSite a x y) (hsp : ¬ (x = a ∧ y = 2 * a - 1)) : rhoTwos a η (x, y) = bulkR a η x y := by
  rw [rhoTwos_tile_eta η ha he2 hp, tile_deck_bulk_eta η ha hp hF hsp]

/-- `rhoTwos` (any sign) is invariant under `U`. -/
theorem rhoTwos_add_U_eta (η : ℤ) (a x y : ℤ) :
    rhoTwos a η (x + (a + 1), y + (a - 1)) = rhoTwos a η (x, y) := by
  unfold rhoTwos
  rw [classKey_add_U]

/-- `rhoTwos` (any sign) is invariant under `V`. -/
theorem rhoTwos_add_V_eta (η : ℤ) (a x y : ℤ) :
    rhoTwos a η (x + (-2), y + 2 * a) = rhoTwos a η (x, y) := by
  unfold rhoTwos
  rw [classKey_add_V]

end FLatticePaper.TwosEPolicy
