import FLatticePaper.Plane.Induction.TwosCandDrop2
import FLatticePaper.Plane.Induction.TwosSpecialCentres
import FLatticePaper.Plane.Induction.TwosSpecialPhi
import FLatticePaper.Plane.Induction.TwosFlatClass

/-! Twos flatness, the candidate displacement by band, and the candidate cases that are not tile destinations or need the
special values: `E` at `x = a` (not flat), `W` at `x = 0` (the destination is `(-1, a)`), and `High-up` at `y = 2a+x-1`
(the destination is the `V`-duplicate of the free H site `(x+2, x)`). -/

noncomputable section

namespace FLatticePaper.TwosEPolicy

open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey
open scoped Classical

theorem candDisp_Eval {a x y : ℤ} (h : CandE a x y) : candDisp a x y = (1, 0) := by
  have hw : ¬ CandW a x y := by
    unfold CandW CandE at *
    omega
  have hl : ¬ (CandLow a x y ∨ CandHigh a x y) := by
    unfold CandLow CandHigh CandE at *
    omega
  unfold candDisp
  rw [if_pos h, if_neg hl]

theorem candDisp_Wval {a x y : ℤ} (h : CandW a x y) : candDisp a x y = (-1, 0) := by
  have he : ¬ CandE a x y := by
    unfold CandW CandE at *
    omega
  have hl : ¬ (CandLow a x y ∨ CandHigh a x y) := by
    unfold CandLow CandHigh CandW at *
    omega
  unfold candDisp
  rw [if_neg he, if_pos h, if_neg hl]

theorem candDisp_low {a x y : ℤ} (h : CandLow a x y) :
    candDisp a x y = (0, if y < a - 1 then -1 else 1) := by
  have he : ¬ CandE a x y := by
    unfold CandLow CandE at *
    omega
  have hw : ¬ CandW a x y := by
    unfold CandLow CandW at *
    omega
  unfold candDisp
  rw [if_neg he, if_neg hw, if_pos (Or.inl h), if_pos h]

theorem candDisp_high {a x y : ℤ} (h : CandHigh a x y) :
    candDisp a x y = (0, if y < 2 * a - 1 then -1 else 1) := by
  have he : ¬ CandE a x y := by
    unfold CandHigh CandE at *
    omega
  have hw : ¬ CandW a x y := by
    unfold CandHigh CandW at *
    omega
  have hl : ¬ CandLow a x y := by
    unfold CandHigh CandLow at *
    omega
  unfold candDisp
  rw [if_neg he, if_neg hw, if_pos (Or.inr h), if_neg hl]

/-- The `E` centre at `x = a`, `(a, 2a-2)`: its destination `(a+1, 2a-2)` has potential `C-1`, so it is not flat. -/
theorem candE_a_nonflat {a : ℤ} {k : ℕ} (hk : a = 2 * (k : ℤ) + 4)
    (hΦ : twosPhi k 1 (a + 1, 2 * a - 2) = twosPhi k 1 (a, 2 * a - 2)) : False := by
  have ha : (4 : ℤ) ≤ a := by omega
  have hq : TwosTile a (0, a - 1) := free_tile (Or.inr (Or.inl ⟨rfl, by omega, by omega⟩))
    (by unfold NativeT; omega)
  have e1 := phi_dupU' hk (a + 1) (2 * a - 2)
  rw [show a + 1 - (a + 1) = 0 by ring, show 2 * a - 2 - (a - 1) = a - 1 by ring] at e1
  have e2 := phi_tile_lev hk hq (by omega) (by omega) (by omega)
  have e3 := phi_spec_2a2 k
  rw [show 2 * (k : ℤ) + 4 = a by omega] at e3
  have hl : twosLev a 0 (a - 1) = 0 := by
    unfold twosLev
    rw [if_neg (by omega), if_neg (by omega)]
    norm_num
  linarith

/-- The `W` centre at `x = 0`, `(0, a)`: its destination `(-1, a) = (a, 2a-1) - U` has rank `1 < 2`. -/
theorem candW0_drop {a : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) :
    rhoTwos a 1 (-1, a) < rhoTwos a 1 (0, a) := by
  have hU := rhoTwos_add_U a (-1) a
  rw [show (-1 : ℤ) + (a + 1) = a by ring, show a + (a - 1) = 2 * a - 1 by ring] at hU
  rw [← hU, rhoTwos_tile ha he2 (tile_a_2a1 ha), deck_special_1 ha]
  have hp : TwosTile a (0, a) := tile_pt (by unfold NativeT; omega)
    (by unfold FreeSite FreeHSite FreeVSite; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
  have hF : ¬ FreeSite a 0 a := by
    unfold FreeSite FreeHSite FreeVSite
    omega
  have hsp : ¬ (0 = a ∧ a = 2 * a - 1) := by
    intro h
    omega
  rw [rhoTwos_tile_bulk ha he2 hp hF hsp, bulk_high_lo ha (by omega) (by omega)]
  omega

/-- The `High-up` centre `(x, x+2a-1)` with `x ≤ a-2`: its destination `(x, x+2a)` is the `V`-duplicate of the free H site
`(x+2, x)`, of rank `2a-2-2x`, and the centre has rank `2a-1-2x`. -/
theorem candHigh_dupV_drop {a x : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hx0 : 0 ≤ x) (hx1 : x ≤ a - 2)
    (hp : TwosTile a (x, x + 2 * a - 1)) :
    rhoTwos a 1 (x, x + 2 * a) < rhoTwos a 1 (x, x + 2 * a - 1) := by
  have hV := rho_dupV' (a := a) x (x + 2 * a)
  rw [show x + 2 * a - 2 * a = x by ring] at hV
  rw [hV]
  have hq : TwosTile a (x + 2, x) := free_tile (Or.inl (Or.inr (Or.inl ⟨by omega, by omega, by ring⟩)))
    (by unfold NativeT; omega)
  rw [rhoTwos_tile_freeH ha he2 hq (Or.inr (Or.inl ⟨by omega, by omega, by ring⟩)), freeH_mid (by omega) (by omega)]
  have hF : ¬ FreeSite a x (x + 2 * a - 1) := by
    unfold FreeSite FreeHSite FreeVSite
    omega
  have hsp : ¬ (x = a ∧ x + 2 * a - 1 = 2 * a - 1) := by
    intro h
    omega
  rw [rhoTwos_tile_bulk ha he2 hp hF hsp, bulk_high_hi (by omega) (by omega) (by omega)]
  omega

end FLatticePaper.TwosEPolicy
