import FLatticePaper.Plane.Induction.TwosCandDrop2
import FLatticePaper.Plane.Induction.TwosCandSpecial

/-! Twos flatness, the candidate centres: a non-free white tile centre `p ≠ (a, 2a-1)` with the candidate guard and equal
potential at its candidate destination has a strictly smaller rank there. Each band is one lemma (`TwosCandDrop`,
`TwosCandDrop2`, `TwosCandSpecial`), with the destination shown to be a tile point and the level equation from the potential. -/

noncomputable section

namespace FLatticePaper.TwosEPolicy

/-- The rank at the special point `(a, 2a-2)` is `0`. -/
theorem rho_a_2a2 {a : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) : rhoTwos a 1 (a, 2 * a - 2) = 0 := by
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

/-- The rank at `(a, 2a-3)` is `1`. -/
theorem rho_a_2a3 {a : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) : rhoTwos a 1 (a, 2 * a - 3) = 1 := by
  have hp : TwosTile a (a, 2 * a - 3) := tile_pt (by unfold NativeT; omega)
    (by unfold FreeSite FreeHSite FreeVSite; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
  have hF : ¬ FreeSite a a (2 * a - 3) := by
    unfold FreeSite FreeHSite FreeVSite
    omega
  have hsp : ¬ (a = a ∧ 2 * a - 3 = 2 * a - 1) := by
    intro h
    omega
  rw [rhoTwos_tile_bulk ha he2 hp hF hsp, bulk_low_hi (by omega) (by omega) (by omega)]
  omega

/-- The `Low-up` centre `(a, 2a-3)` moves to the special point `(a, 2a-2)`: the rank drops from `1` to `0`. -/
theorem candLow_up_special {a : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) :
    rhoTwos a 1 (a, 2 * a - 2) < rhoTwos a 1 (a, 2 * a - 3) := by
  rw [rho_a_2a2 ha he2, rho_a_2a3 ha he2]
  norm_num

set_option maxHeartbeats 400000 in
theorem candidate_flat_drop {a : ℤ} {k : ℕ} (hk : a = 2 * (k : ℤ) + 4) {x y : ℤ}
    (hp : TwosTile a (x, y)) (hpF : ¬ FreeSite a x y) (hpS : ¬ (x = a ∧ y = 2 * a - 1))
    (hG : CandGuard a x y)
    (hΦ : twosPhi k 1 (x + (candDisp a x y).1, y + (candDisp a x y).2) = twosPhi k 1 (x, y)) :
    rhoTwos a 1 (x + (candDisp a x y).1, y + (candDisp a x y).2) < rhoTwos a 1 (x, y) := by
  have ha : (4 : ℤ) ≤ a := by omega
  have he2 : a % 2 = 0 := by omega
  unfold CandGuard at hG
  rcases hG with hL | hH | hE | hW
  · -- the `Low` band
    have hLu := hL
    unfold CandLow at hLu
    rw [candDisp_low hL] at hΦ ⊢
    dsimp only at hΦ ⊢
    by_cases hy : y < a - 1
    · rw [if_pos hy] at hΦ ⊢
      have hi : TwosTile a (x + 0, y + -1) := tile_pt (by unfold NativeT; omega)
        (by unfold FreeSite FreeHSite FreeVSite; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
      have hl : twosLev a (x + 0) (y + -1) = twosLev a x y := by
        have e1 := phi_tile_lev hk hi (by omega) (by omega) (by omega)
        have e2 := phi_tile_lev hk hp (by omega) (by omega) (by omega)
        linarith
      exact candLow_down ha he2 hp hpF (by omega) hi hl
    · rw [if_neg hy] at hΦ ⊢
      by_cases hsp2 : x = a ∧ y = 2 * a - 3
      · obtain ⟨hx, hy⟩ := hsp2
        rw [hx, hy]
        simp only [add_zero]
        rw [show 2 * a - 3 + 1 = 2 * a - 2 by ring]
        exact candLow_up_special ha he2
      have hi : TwosTile a (x + 0, y + 1) := tile_pt (by unfold NativeT; omega)
        (by unfold FreeSite FreeHSite FreeVSite; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
      have hl : twosLev a (x + 0) (y + 1) = twosLev a x y := by
        have e1 := phi_tile_lev hk hi (by omega) (by omega) (by omega)
        have e2 := phi_tile_lev hk hp (by omega) (by omega) (by omega)
        linarith
      exact candLow_up ha he2 hp hpF (by omega) hi hl
  · -- the `High` band
    have hHu := hH
    unfold CandHigh at hHu
    rw [candDisp_high hH] at hΦ ⊢
    dsimp only at hΦ ⊢
    by_cases hy : y < 2 * a - 1
    · rw [if_pos hy] at hΦ ⊢
      have hi : TwosTile a (x + 0, y + -1) := tile_pt (by unfold NativeT; omega)
        (by unfold FreeSite FreeHSite FreeVSite; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
      have hl : twosLev a (x + 0) (y + -1) = twosLev a x y := by
        have e1 := phi_tile_lev hk hi (by omega) (by omega) (by omega)
        have e2 := phi_tile_lev hk hp (by omega) (by omega) (by omega)
        linarith
      exact candHigh_down ha he2 hp hpF (by omega) hi hl
    · rw [if_neg hy] at hΦ ⊢
      by_cases hd : y = x + 2 * a - 1
      · -- the `V`-duplicate of the free H site `(x+2, x)`
        subst hd
        have := candHigh_dupV_drop ha he2 (by omega) (by omega) hp
        simp only [add_zero]
        rw [show x + 2 * a - 1 + 1 = x + 2 * a by ring]
        exact this
      · have hi : TwosTile a (x + 0, y + 1) := tile_pt (by unfold NativeT; omega)
          (by unfold FreeSite FreeHSite FreeVSite; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
        have hl : twosLev a (x + 0) (y + 1) = twosLev a x y := by
          have e1 := phi_tile_lev hk hi (by omega) (by omega) (by omega)
          have e2 := phi_tile_lev hk hp (by omega) (by omega) (by omega)
          linarith
        exact candHigh_up ha he2 hp hpF (by omega) hi hl
  · -- the `E` band
    have hEu := hE
    unfold CandE at hEu
    rw [candDisp_Eval hE] at hΦ ⊢
    dsimp only at hΦ ⊢
    simp only [add_zero] at hΦ ⊢
    by_cases hxa : x = a
    · exfalso
      subst x
      have hy' : y = 2 * a - 2 := by omega
      subst y
      exact candE_a_nonflat hk (by simpa using hΦ)
    · have hi : TwosTile a (x + 1, y) := tile_pt (by unfold NativeT; omega)
        (by unfold FreeSite FreeHSite FreeVSite; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
      have hl : twosLev a (x + 1) y = twosLev a x y := by
        have e1 := phi_tile_lev hk hi (by omega) (by omega) (by omega)
        have e2 := phi_tile_lev hk hp (by omega) (by omega) (by omega)
        linarith
      exact candE_tile_drop ha he2 hp hpF (by omega) hi hl
  · -- the `W` band
    have hWu := hW
    unfold CandW at hWu
    rw [candDisp_Wval hW] at hΦ ⊢
    dsimp only at hΦ ⊢
    by_cases hx0 : x = 0
    · subst hx0
      have hy' : y = a := by omega
      subst y
      simpa using candW0_drop ha he2
    · have hi : TwosTile a (x + -1, y + 0) := tile_pt (by unfold NativeT; omega)
        (by unfold FreeSite FreeHSite FreeVSite; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
      have hl : twosLev a (x + -1) (y + 0) = twosLev a x y := by
        have e1 := phi_tile_lev hk hi (by omega) (by omega) (by omega)
        have e2 := phi_tile_lev hk hp (by omega) (by omega) (by omega)
        linarith
      exact candW ha he2 hp hpF (by omega) hi hl

end FLatticePaper.TwosEPolicy
