import FLatticePaper.Plane.Induction.TwosDeckTile

/-! Twos flatness, step (b), tile points: the deck-periodic rank `rhoTwos` at a tile point is the deck value at that point, and
its closed forms by the type of the point (sign `+1`). -/

noncomputable section

namespace FLatticePaper.TwosEPolicy

open FLatticePaper
open scoped Classical

/-- At a tile point `p`, the tile point of its class is `p` itself. -/
theorem tilePoint_classKey_of_tile {a x y : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hp : TwosTile a (x, y)) :
    tilePoint a (classKey a (x, y)) = (x, y) := by
  have hex : ∃ q : Site, TwosTile a q ∧ classKey a q = classKey a (x, y) := ⟨(x, y), hp, rfl⟩
  have hs : TwosTile a (tilePoint a (classKey a (x, y))) ∧
      classKey a (tilePoint a (classKey a (x, y))) = classKey a (x, y) := Classical.epsilon_spec hex
  obtain ⟨h1, h2⟩ := tile_unique ha he2 hs.1 hp hs.2
  exact Prod.ext h1 h2

/-- At a tile point, `rhoTwos` (sign `+1`) is the deck value at that point. -/
theorem rhoTwos_tile {a x y : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hp : TwosTile a (x, y)) :
    rhoTwos a 1 (x, y) = deckAt a 1 x y := by
  unfold rhoTwos
  rw [tilePoint_classKey_of_tile ha he2 hp]

/-- A free H tile point has the H value. -/
theorem rhoTwos_tile_freeH {a x y : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hp : TwosTile a (x, y))
    (hF : FreeHSite a x y) : rhoTwos a 1 (x, y) = freeH a 1 x y := by
  rw [rhoTwos_tile ha he2 hp, deck_freeH hF]

/-- A free V tile point (not free H) has the V value. -/
theorem rhoTwos_tile_freeV {a x y : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hp : TwosTile a (x, y))
    (hnH : ¬ FreeHSite a x y) (hV : FreeVSite a x y) : rhoTwos a 1 (x, y) = freeV a 1 x y := by
  rw [rhoTwos_tile ha he2 hp, deck_freeV hnH hV]

/-- A non-free tile point other than `(a, 2a−1)` has the bulk value. -/
theorem rhoTwos_tile_bulk {a x y : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hp : TwosTile a (x, y))
    (hF : ¬ FreeSite a x y) (hsp : ¬ (x = a ∧ y = 2 * a - 1)) : rhoTwos a 1 (x, y) = bulkR a 1 x y := by
  rw [rhoTwos_tile ha he2 hp, tile_deck_bulk ha hp hF hsp]


/-- `classKey` is invariant under the lattice vector `U = (a+1, a-1)`. -/
theorem classKey_add_U (a x y : ℤ) : classKey a (x + (a + 1), y + (a - 1)) = classKey a (x, y) := by
  unfold classKey
  congr 1
  ring

/-- `classKey` is invariant under the lattice vector `V = (-2, 2a)`, modulo the period `2a²+4a−2`. -/
theorem classKey_add_V (a x y : ℤ) : classKey a (x + (-2), y + 2 * a) = classKey a (x, y) := by
  unfold classKey
  dsimp only
  have h : (a - 1) * (x + (-2)) - (a + 1) * (y + 2 * a) =
      ((a - 1) * x - (a + 1) * y) + (2 * a * a + 4 * a - 2) * (-1) := by ring
  rw [h, Int.add_mul_emod_self_left]

/-- `rhoTwos` (sign `+1`) is invariant under `U`. -/
theorem rhoTwos_add_U (a x y : ℤ) : rhoTwos a 1 (x + (a + 1), y + (a - 1)) = rhoTwos a 1 (x, y) := by
  unfold rhoTwos
  rw [classKey_add_U]

/-- `rhoTwos` (sign `+1`) is invariant under `V`. -/
theorem rhoTwos_add_V (a x y : ℤ) : rhoTwos a 1 (x + (-2), y + 2 * a) = rhoTwos a 1 (x, y) := by
  unfold rhoTwos
  rw [classKey_add_V]

end FLatticePaper.TwosEPolicy
