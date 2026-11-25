import FLatticePaper.Plane.Induction.TwosTileRep
import FLatticePaper.Plane.Induction.TwosTileRho
import FLatticePaper.Plane.Induction.TwosFlatReduce
import FLatticePaper.Plane.Induction.TwosBlackOdd

/-! Twos flatness, black centres on the odd lines. An odd black tile point lies on one of the three lines of
`odd_black_explicit`: `L1: y = 2a-1, 0 ≤ x ≤ a-2` (value `2a-1`), `L2: y = a-1, 2 ≤ x ≤ a` (value `2a-3`),
`L3: y - x = a-1, 1 ≤ x ≤ a-1` (value `2x+3`). The upper vertical neighbour `(x, y+1)` has rank one less; the single
`V`-duplicate `(0, 2a) = (2, 0) + V` has the rank of the free H site `(2, 0)`. -/

noncomputable section

namespace FLatticePaper.TwosEPolicy

open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey
open scoped Classical

/-- A native point with no duplicate free copy is a tile point. -/
theorem tile_of_nodup {a x y : ℤ} (hN : NativeT a x y)
    (h1 : ¬ (FreeSite a (x - (a + 1)) (y - (a - 1)) ∧ NativeT a (x - (a + 1)) (y - (a - 1))))
    (h2 : ¬ (FreeSite a (x + 2) (y - 2 * a) ∧ NativeT a (x + 2) (y - 2 * a))) :
    TwosTile a (x, y) := by
  rw [tile_iff_lin]
  refine ⟨hN, ?_⟩
  rintro ⟨h | h, -⟩
  · exact h1 h
  · exact h2 h

/-- The tile point with its two duplicate conditions checked by linear arithmetic. -/
theorem tile_pt {a x y : ℤ} (hN : NativeT a x y)
    (hF1 : ¬ FreeSite a (x - (a + 1)) (y - (a - 1))) (hF2 : ¬ FreeSite a (x + 2) (y - 2 * a)) :
    TwosTile a (x, y) :=
  tile_of_nodup hN (fun h => hF1 h.1) (fun h => hF2 h.1)

/-- The potential at a tile point off the three specials, in its level form. -/
theorem phi_tile_lev {a : ℤ} {k : ℕ} (hk : a = 2 * (k : ℤ) + 4) {x y : ℤ} (ht : TwosTile a (x, y))
    (h1 : ¬ (x = a ∧ y = 2 * a - 2)) (h2 : ¬ (x = a ∧ y = 2 * a - 1)) (h3 : ¬ (x = a + 1 ∧ y = a - 2)) :
    twosPhi k 1 (x, y) = ((k : ℤ) + 2) * ((k : ℤ) + 3) + twosLev a x y := by
  subst hk
  have hN : NativeT (2 * (k : ℤ) + 4) x y := ((tile_iff_lin _ _ _).mp ht).1
  exact chain_level_native k hN (tile_key_succ _ x y (by omega) ht h1 h2 h3)

/-- The potential at a `V`-translate: `Φ(v + V) = Φ(v) + 2`. -/
theorem phi_dupV {a : ℤ} {k : ℕ} (hk : a = 2 * (k : ℤ) + 4) (v1 v2 : ℤ) :
    twosPhi k 1 (v1 + (-2), v2 + 2 * a) = twosPhi k 1 (v1, v2) + 2 := by
  subst hk
  rw [show 2 * (2 * (k : ℤ) + 4) = 4 * (k : ℤ) + 8 by ring]
  exact twosPhi_transverse_plus k (v1, v2)

/-- The rank on the line `L1`: `ρ = 2a-1` at an even `x`. -/
theorem rho_L1 {a x : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hxe : x % 2 = 0)
    (hp : TwosTile a (x, 2 * a - 1)) (hx0 : 0 ≤ x) (hx1 : x ≤ a - 2) :
    rhoTwos a 1 (x, 2 * a - 1) = 2 * a - 1 := by
  rw [rhoTwos_tile_bulk ha he2 hp (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega)]
  simp only [bulkR]
  split_ifs <;> first | exact False.elim ‹False› | omega

/-- The rank on the line `L2`: `ρ = 2a-3` at an even `x`. -/
theorem rho_L2 {a x : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hxe : x % 2 = 0)
    (hp : TwosTile a (x, a - 1)) (hx0 : 2 ≤ x) :
    rhoTwos a 1 (x, a - 1) = 2 * a - 3 := by
  rw [rhoTwos_tile_bulk ha he2 hp (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega)]
  simp only [bulkR]
  split_ifs <;> first | exact False.elim ‹False› | omega

/-- The rank on the line `L3`: `ρ = 2x+3`. -/
theorem rho_L3 {a x : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hp : TwosTile a (x, x + a - 1))
    (hx0 : 1 ≤ x) (hx1 : x ≤ a - 1) : rhoTwos a 1 (x, x + a - 1) = 2 * x + 3 := by
  rw [rhoTwos_tile_bulk ha he2 hp (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega)]
  simp only [bulkR]
  split_ifs <;> first | exact False.elim ‹False› | omega

/-- The upper vertical neighbour of an odd black tile point has rank one less. -/
theorem odd_black_drop_up {a : ℤ} {k : ℕ} (hk : a = 2 * (k : ℤ) + 4) {x y : ℤ}
    (hB : (y = 2 * a - 1 ∧ 0 ≤ x ∧ x ≤ a - 2) ∨ (y = a - 1 ∧ 2 ≤ x ∧ x ≤ a) ∨
      (y - x = a - 1 ∧ 1 ≤ x ∧ x ≤ a - 1))
    (hp : TwosTile a (x, y)) (hodd : (x + y) % 2 = 1) :
    rhoTwos a 1 (x, y + 1) < rhoTwos a 1 (x, y) := by
  have ha : (4 : ℤ) ≤ a := by omega
  have he2 : a % 2 = 0 := by omega
  rcases hB with ⟨hy, hx0, hx1⟩ | ⟨hy, hx0, hx1⟩ | ⟨hy, hx0, hx1⟩
  · subst hy
    rcases (show x = 0 ∨ 2 ≤ x by omega) with rfl | hx2
    · -- the V-duplicate (0, 2a) = (2, 0) + V, a free H site
      have hv : TwosTile a (2, 0) := tile_pt (by unfold NativeT; omega)
        (by unfold FreeSite FreeHSite FreeVSite; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
      have e : rhoTwos a 1 (0, 2 * a) = rhoTwos a 1 (2, 0) := by
        have h := rhoTwos_add_V a 2 0
        rw [show (2 : ℤ) + -2 = 0 by norm_num, show (0 : ℤ) + 2 * a = 2 * a by ring] at h
        exact h
      rw [show 2 * a - 1 + 1 = 2 * a by ring, e, rhoTwos_tile_freeH ha he2 hv (by unfold FreeHSite; omega),
        rho_L1 ha he2 (by omega) hp (by omega) (by omega)]
      simp only [freeH]
      split_ifs <;> first | exact False.elim ‹False› | omega
    · have hi : TwosTile a (x, 2 * a) := tile_pt (by unfold NativeT; omega)
        (by unfold FreeSite FreeHSite FreeVSite; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
      rw [show 2 * a - 1 + 1 = 2 * a by ring, rho_L1 ha he2 (by omega) hp (by omega) (by omega),
        rhoTwos_tile_bulk ha he2 hi (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega)]
      simp only [bulkR]
      split_ifs <;> first | exact False.elim ‹False› | omega
  · subst hy
    have hi : TwosTile a (x, a) := tile_pt (by unfold NativeT; omega)
      (by unfold FreeSite FreeHSite FreeVSite; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
    rw [show a - 1 + 1 = a by ring, rho_L2 ha he2 (by omega) hp hx0,
      rhoTwos_tile_bulk ha he2 hi (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega)]
    simp only [bulkR]
    split_ifs <;> first | exact False.elim ‹False› | omega
  · have hy' : y = x + a - 1 := by omega
    subst hy'
    have hi : TwosTile a (x, x + a) := tile_pt (by unfold NativeT; omega)
      (by unfold FreeSite FreeHSite FreeVSite; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
    rw [show x + a - 1 + 1 = x + a by ring, rho_L3 ha he2 hp hx0 hx1,
      rhoTwos_tile_bulk ha he2 hi (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega)]
    simp only [bulkR]
    split_ifs <;> first | exact False.elim ‹False› | omega

/-- The lower vertical neighbour of an odd black tile point: the rank drops by one on a flat edge. -/
theorem odd_black_drop_down {a : ℤ} {k : ℕ} (hk : a = 2 * (k : ℤ) + 4) {x y : ℤ}
    (hB : (y = 2 * a - 1 ∧ 0 ≤ x ∧ x ≤ a - 2) ∨ (y = a - 1 ∧ 2 ≤ x ∧ x ≤ a) ∨
      (y - x = a - 1 ∧ 1 ≤ x ∧ x ≤ a - 1))
    (hp : TwosTile a (x, y)) (hodd : (x + y) % 2 = 1)
    (hΦ : twosPhi k 1 (x, y - 1) = twosPhi k 1 (x, y)) :
    rhoTwos a 1 (x, y - 1) < rhoTwos a 1 (x, y) := by
  have ha : (4 : ℤ) ≤ a := by omega
  have he2 : a % 2 = 0 := by omega
  rcases hB with ⟨hy, hx0, hx1⟩ | ⟨hy, hx0, hx1⟩ | ⟨hy, hx0, hx1⟩
  · subst hy
    have hi : TwosTile a (x, 2 * a - 1 - 1) := tile_pt (by unfold NativeT; omega)
      (by unfold FreeSite FreeHSite FreeVSite; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
    rw [rho_L1 ha he2 (by omega) hp hx0 hx1, rhoTwos_tile_bulk ha he2 hi
      (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega)]
    simp only [bulkR]
    split_ifs <;> first | exact False.elim ‹False› | omega
  · subst hy
    by_cases hxa : x = a
    · exfalso
      have hi : TwosTile a (x, a - 1 - 1) := tile_pt (by unfold NativeT; omega)
        (by unfold FreeSite FreeHSite FreeVSite; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
      have e1 := phi_tile_lev hk hi (by omega) (by omega) (by omega)
      have e2 := phi_tile_lev hk hp (by omega) (by omega) (by omega)
      have hl : twosLev a x (a - 1 - 1) = twosLev a x (a - 1) := by linarith
      unfold twosLev at hl
      split_ifs at hl <;> omega
    · have hi : TwosTile a (x, a - 1 - 1) := tile_pt (by unfold NativeT; omega)
        (by unfold FreeSite FreeHSite FreeVSite; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
      rw [rho_L2 ha he2 (by omega) hp hx0, rhoTwos_tile_bulk ha he2 hi
        (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega)]
      simp only [bulkR]
      split_ifs <;> first | exact False.elim ‹False› | omega
  · have hy' : y = x + a - 1 := by omega
    subst hy'
    exfalso
    have hi : TwosTile a (x, x + a - 1 - 1) := tile_pt (by unfold NativeT; omega)
      (by unfold FreeSite FreeHSite FreeVSite; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
    have e1 := phi_tile_lev hk hi (by omega) (by omega) (by omega)
    have e2 := phi_tile_lev hk hp (by omega) (by omega) (by omega)
    have hl : twosLev a x (x + a - 1 - 1) = twosLev a x (x + a - 1) := by linarith
    unfold twosLev at hl
    split_ifs at hl <;> omega

end FLatticePaper.TwosEPolicy
