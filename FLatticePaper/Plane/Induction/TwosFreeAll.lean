import FLatticePaper.Plane.Induction.TwosFreeFlat
import FLatticePaper.Plane.Induction.TwosSpecialCentres

/-! Twos flatness, the free centres (sign `+1`): on every flat free edge the rank drops by one. The destinations are the
free displacements (`freeDisp`), and each family is one lemma: H (1,0), H (x,x-2) with 2 ≤ x ≤ a, H (a+1,a-2), V (0,0)
(not flat), V (0,j) with j even or odd, V (-1,j) with j odd or even. -/

noncomputable section

namespace FLatticePaper.TwosEPolicy

/-- Two non-special tile points of equal potential have equal level. -/
theorem lev_of_phi {a x y i1 i2 : ℤ} {k : ℕ} (hk : a = 2 * (k : ℤ) + 4)
    (hp : TwosTile a (x, y)) (hp1 : ¬ (x = a ∧ y = 2 * a - 2)) (hp2 : ¬ (x = a ∧ y = 2 * a - 1))
    (hp3 : ¬ (x = a + 1 ∧ y = a - 2))
    (hi : TwosTile a (i1, i2)) (hi1 : ¬ (i1 = a ∧ i2 = 2 * a - 2)) (hi2 : ¬ (i1 = a ∧ i2 = 2 * a - 1))
    (hi3 : ¬ (i1 = a + 1 ∧ i2 = a - 2))
    (hΦ : twosPhi k 1 (i1, i2) = twosPhi k 1 (x, y)) : twosLev a i1 i2 = twosLev a x y := by
  have e1 := phi_tile_lev hk hi hi1 hi2 hi3
  have e2 := phi_tile_lev hk hp hp1 hp2 hp3
  linarith

/-- **The free flat drop.** A free tile centre whose selected input is its free displacement has, on a flat edge, a
destination of smaller rank. -/
theorem free_flat_drop {a : ℤ} {k : ℕ} (hk : a = 2 * (k : ℤ) + 4) {x y i1 i2 : ℤ}
    (hp : TwosTile a (x, y)) (hF : FreeSite a x y)
    (hd : (i1, i2) = (x + (freeDisp a 1 x y).1, y + (freeDisp a 1 x y).2))
    (hΦ : twosPhi k 1 (i1, i2) = twosPhi k 1 (x, y)) :
    rhoTwos a 1 (i1, i2) < rhoTwos a 1 (x, y) := by
  have ha : (4 : ℤ) ≤ a := by omega
  have he2 : a % 2 = 0 := by omega
  have hN : NativeT a x y := ((tile_iff_lin _ _ _).mp hp).1
  unfold FreeSite FreeHSite FreeVSite at hF
  rcases hF with (H1 | H2 | H3) | (V1 | V2)
  · -- the free H site (1, 0)
    obtain ⟨hx, hy⟩ := H1
    subst hx
    subst hy
    rw [fd_H1] at hd
    dsimp only at hd
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hd
    simpa using H1_drop ha he2
  · obtain ⟨h2, h3, hy⟩ := H2
    subst hy
    rw [fd_Heven h2 h3] at hd
    dsimp only at hd
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hd
    by_cases hxa : x = a
    · rw [hxa]
      simpa using H3_drop ha he2
    · simpa using H2_drop ha he2 h2 (by omega)
  · -- the free H site (a+1, a-2)
    obtain ⟨hx, hy⟩ := H3
    subst hx
    subst hy
    rw [freeDisp_ap1 ha] at hd
    dsimp only at hd
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hd
    rw [show a + 1 + 0 = a + 1 by ring, show a - 2 + 1 = a - 1 by ring]
    exact ap1_rho_drop ha he2
  · -- the free V site (0, y)
    obtain ⟨hx, hy0, hya⟩ := V1
    subst hx
    by_cases hy0' : y = 0
    · exfalso
      subst hy0'
      rw [fd_V00] at hd
      dsimp only at hd
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hd
      simp only [zero_add, add_zero] at hΦ
      exact V00_nonflat hk hΦ
    · by_cases hpar : y % 2 = 0
      · rw [fd_Veven (by omega) hya hpar] at hd
        dsimp only at hd
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hd
        have hi : TwosTile a (0 + 1, y + 0) := tile_pt (by unfold NativeT; omega)
          (by unfold FreeSite FreeHSite FreeVSite; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
        have hL : twosLev a (0 + 1) (y + 0) = twosLev a 0 y :=
          lev_of_phi hk hp (by omega) (by omega) (by omega) hi (by omega) (by omega) (by omega) hΦ
        exact freeV2 ha he2 hp (Or.inr (Or.inl ⟨rfl, by omega, hya⟩)) ⟨rfl, by omega, hya, hpar⟩ hi hL
      · rw [fd_Vodd (by omega) hya (by omega)] at hd
        dsimp only at hd
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hd
        have hi : TwosTile a (0 + 0, y + -1) := free_tile (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))
          (by unfold NativeT; omega)
        have hL : twosLev a (0 + 0) (y + -1) = twosLev a 0 y :=
          lev_of_phi hk hp (by omega) (by omega) (by omega) hi (by omega) (by omega) (by omega) hΦ
        exact freeV3 ha he2 hp (Or.inr (Or.inl ⟨rfl, by omega, hya⟩)) ⟨rfl, by omega, hya, by omega⟩ hi hL
  · -- the free V site (-1, y)
    obtain ⟨hx, hy1, hy2⟩ := V2
    subst hx
    by_cases hya : y = a
    · exfalso
      subst hya
      unfold NativeT at hN
      omega
    · by_cases hpar : y % 2 = 1
      · rw [fd_m1odd (by omega) hy2 hpar] at hd
        dsimp only at hd
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hd
        have hi : TwosTile a (-1 + 1, y + 0) := tile_pt (by unfold NativeT; omega)
          (by unfold FreeSite FreeHSite FreeVSite; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
        have hL : twosLev a (-1 + 1) (y + 0) = twosLev a (-1) y :=
          lev_of_phi hk hp (by omega) (by omega) (by omega) hi (by omega) (by omega) (by omega) hΦ
        exact freeV4 ha he2 hp (Or.inr (Or.inr ⟨rfl, by omega, hy2⟩)) ⟨rfl, by omega, hy2, hpar⟩ hi hL
      · rw [fd_m1even (by omega) hy2 (by omega)] at hd
        dsimp only at hd
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hd
        have hi : TwosTile a (-1 + 0, y + -1) := free_tile (Or.inr (Or.inr ⟨by omega, by omega, by omega⟩))
          (by unfold NativeT; omega)
        have hL : twosLev a (-1 + 0) (y + -1) = twosLev a (-1) y :=
          lev_of_phi hk hp (by omega) (by omega) (by omega) hi (by omega) (by omega) (by omega) hΦ
        exact freeV5 ha he2 hp (Or.inr (Or.inr ⟨rfl, by omega, hy2⟩)) ⟨rfl, by omega, hy2, by omega⟩ hi hL

end FLatticePaper.TwosEPolicy
