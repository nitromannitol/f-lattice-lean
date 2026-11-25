import FLatticePaper.Plane.Induction.TwosFreeDrop
import FLatticePaper.Plane.Induction.TwosSpecialCentres

/-! Twos flatness, the remaining free centres (sign `+1`): `(0,0)` is not flat, `(1,0)` moves to the `V`-translate `(1,-1)`
of the free site `(-1, 2a-1)`, the H centres `(x, x-2)` with `2 ≤ x ≤ a-1` move to the `V`-translate `(x+1, x-2)` of a
tile point of height `2a-1`, and the H centre `(a, a-2)` moves to the special `(a+1, a-2)`. -/

noncomputable section

namespace FLatticePaper.TwosEPolicy

/-- The centre `(0,0)` is not flat: its destination `(1,0)` has potential `C-1`, the centre `C`. -/
theorem V00_nonflat {a : ℤ} {k : ℕ} (hk : a = 2 * (k : ℤ) + 4)
    (hΦ : twosPhi k 1 (1, 0) = twosPhi k 1 (0, 0)) : False := by
  have ha : (4 : ℤ) ≤ a := by omega
  have h1 : TwosTile a (1, 0) := free_tile (Or.inl (Or.inl ⟨rfl, rfl⟩)) (by unfold NativeT; omega)
  have h0 : TwosTile a (0, 0) := free_tile (Or.inr (Or.inl ⟨rfl, le_refl 0, by omega⟩)) (by unfold NativeT; omega)
  have e1 := phi_tile_lev hk h1 (by omega) (by omega) (by omega)
  have e0 := phi_tile_lev hk h0 (by omega) (by omega) (by omega)
  have l1 : twosLev a 1 0 = -1 := by
    unfold twosLev
    rw [if_neg (by omega), if_pos (by omega)]
    norm_num
  have l0 : twosLev a 0 0 = 0 := by
    unfold twosLev
    rw [if_neg (by omega), if_neg (by omega)]
    norm_num
  linarith

/-- The H centre `(1, 0)` moves to `(1, -1)`, and the rank drops from `2a+1` to `2a`. -/
theorem H1_drop {a : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) : rhoTwos a 1 (1, -1) < rhoTwos a 1 (1, 0) := by
  have hV := rhoTwos_add_V a 1 (-1)
  rw [show (1 : ℤ) + -2 = -1 by ring, show (-1 : ℤ) + 2 * a = 2 * a - 1 by ring] at hV
  rw [← hV]
  have hq : TwosTile a (-1, 2 * a - 1) := free_tile (Or.inr (Or.inr ⟨rfl, by omega, by omega⟩))
    (by unfold NativeT; omega)
  rw [rhoTwos_tile_freeV ha he2 hq (by unfold FreeHSite; omega) (Or.inr ⟨rfl, by omega, by omega⟩)]
  have hp : TwosTile a (1, 0) := free_tile (Or.inl (Or.inl ⟨rfl, rfl⟩)) (by unfold NativeT; omega)
  rw [rhoTwos_tile_freeH ha he2 hp (Or.inl ⟨rfl, rfl⟩), freeH_one rfl, freeV_hi (by omega)]
  omega

/-- The H centre `(x, x-2)` with `2 ≤ x ≤ a-1` moves to `(x+1, x-2)`, the `V`-translate of a tile point of height `2a-1`,
and the rank drops from `2a+2-2x` to `2a+1-2x`. -/
theorem H2_drop {a x : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hx0 : 2 ≤ x) (hx1 : x ≤ a - 1) :
    rhoTwos a 1 (x + 1, x - 2) < rhoTwos a 1 (x, x - 2) := by
  have hV := rhoTwos_add_V a (x + 1) (x - 2)
  rw [show x + 1 + -2 = x - 1 by ring, show x - 2 + 2 * a = x + 2 * a - 2 by ring] at hV
  rw [← hV]
  have hq : TwosTile a (x - 1, x + 2 * a - 2) := tile_pt (by unfold NativeT; omega)
    (by unfold FreeSite FreeHSite FreeVSite; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
  rw [rhoTwos_tile_bulk ha he2 hq (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega),
    bulk_high_hi (by omega) (by omega) (by omega)]
  have hp : TwosTile a (x, x - 2) := free_tile (Or.inl (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))
    (by unfold NativeT; omega)
  rw [rhoTwos_tile_freeH ha he2 hp (Or.inr (Or.inl ⟨by omega, by omega, by ring⟩)),
    freeH_mid (by omega) (by omega)]
  omega

/-- The H centre `(a, a-2)` moves to the special free site `(a+1, a-2)`, the rank drops from `2` to `1`. -/
theorem H3_drop {a : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) : rhoTwos a 1 (a + 1, a - 2) < rhoTwos a 1 (a, a - 2) := by
  rw [rho_ap1 ha he2]
  have hF : FreeSite a a (a - 2) := Or.inl (Or.inr (Or.inl ⟨by omega, le_refl a, rfl⟩))
  have hp : TwosTile a (a, a - 2) := free_tile hF (by unfold NativeT; omega)
  rw [rhoTwos_tile_freeH ha he2 hp (Or.inr (Or.inl ⟨by omega, le_refl a, rfl⟩)), freeH_mid (by omega) (le_refl a)]
  norm_num

end FLatticePaper.TwosEPolicy
