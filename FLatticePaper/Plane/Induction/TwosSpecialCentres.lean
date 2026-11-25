import FLatticePaper.Plane.Induction.TwosSpecialRho
import FLatticePaper.Plane.Induction.TwosWhiteSel
import FLatticePaper.Plane.Induction.TwosSpecialPhi

/-! Twos flatness, the special tile points as centres (sign `+1`).

`(a, 2a-1)` moves to `(a, 2a-2)` (its selected input, `twosSel_special_1`), and its rank drops from `1` to `0`.
`(a+1, a-2)` is a free H centre: its selected input is `(a+1, a-1)`, a `U`-translate of the free site `(0,0)`, with rank `0`
against the rank `1` of the centre. -/

noncomputable section

namespace FLatticePaper.TwosEPolicy

/-- The rank drops at the special centre `(a, 2a-1)` on its selected input `(a, 2a-2)`. -/
theorem special1_rho_drop {a : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) :
    rhoTwos a 1 (a, 2 * a - 2) < rhoTwos a 1 (a, 2 * a - 1) := by
  rw [rhoTwos_tile ha he2 (tile_a_2a1 ha), deck_special_1 ha]
  have hp : TwosTile a (a, 2 * a - 2) := tile_pt (by unfold NativeT; omega)
    (by unfold FreeSite FreeHSite FreeVSite; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
  have hF : ¬ FreeSite a a (2 * a - 2) := by
    unfold FreeSite FreeHSite FreeVSite
    omega
  have hsp : ¬ (a = a ∧ 2 * a - 2 = 2 * a - 1) := by
    intro h
    omega
  rw [rhoTwos_tile_bulk ha he2 hp hF hsp, bulk_low_hi (by omega) (by omega) (by omega)]
  omega

/-- The free centre `(a+1, a-2)` has free displacement `(0, 1)`. -/
theorem freeDisp_ap1 {a : ℤ} (ha : 4 ≤ a) : freeDisp a 1 (a + 1) (a - 2) = (0, 1) := by
  unfold freeDisp
  rw [if_pos (by unfold FreeHSite; omega), if_neg (by omega), if_neg (by unfold EvenSite; dsimp only; omega)]

/-- The rank of `(a+1, a-1)` is `0` (it is the `U`-translate of the free site `(0,0)`). -/
theorem rho_ap1_up {a : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) : rhoTwos a 1 (a + 1, a - 1) = 0 := by
  rw [rho_dupU' (a := a) (a + 1) (a - 1)]
  rw [show a + 1 - (a + 1) = 0 by ring, show a - 1 - (a - 1) = 0 by ring]
  have hq : TwosTile a (0, 0) := free_tile (Or.inr (Or.inl ⟨rfl, le_refl 0, by omega⟩))
    (by unfold NativeT; omega)
  rw [rhoTwos_tile_freeV ha he2 hq (by unfold FreeHSite; omega) (Or.inl ⟨rfl, le_refl 0, by omega⟩)]
  rw [freeV_lo (by omega)]
  omega

/-- The free H centre `(a+1, a-2)` has rank `1`. -/
theorem rho_ap1 {a : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) : rhoTwos a 1 (a + 1, a - 2) = 1 := by
  have hp : TwosTile a (a + 1, a - 2) := free_tile (Or.inl (Or.inr (Or.inr ⟨rfl, rfl⟩)))
    (Or.inr (Or.inr ⟨rfl, by ring⟩))
  rw [rhoTwos_tile_freeH ha he2 hp (Or.inr (Or.inr ⟨rfl, rfl⟩))]
  exact freeH_last rfl ha

/-- The selected input of the free centre `(a+1, a-2)` has smaller rank (`0 < 1`). -/
theorem ap1_rho_drop {a : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) :
    rhoTwos a 1 (a + 1, a - 1) < rhoTwos a 1 (a + 1, a - 2) := by
  rw [rho_ap1_up ha he2, rho_ap1 ha he2]
  norm_num

end FLatticePaper.TwosEPolicy
