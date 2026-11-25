import FLatticePaper.Plane.Induction.TwosBlackEvenNb
import FLatticePaper.Plane.Induction.TwosFlatClass
import FLatticePaper.Plane.Induction.TwosRhoCases
import FLatticePaper.Plane.Induction.TwosSpecialPhi

/-! Twos flatness, the even black drop on the left: for a black even tile point `p` (not special) and its left neighbour
`i = (x-1, y)` with equal potential, the rank of `i` is one less than the rank of `p`.

By `flat_levels`, `i` is a tile point of the same level, or a duplicate of a free site (which is impossible here), or the
special duplicate. The tile case is the arithmetic of the rank cases with the level equation. -/

noncomputable section

namespace FLatticePaper.TwosEPolicy

/-- The duplicate `U` branch of the left neighbour of an even native point is impossible. -/
theorem even_left_dupU_false {a x y : ℤ} (hN : NativeT a x y) (he : (x + y) % 2 = 0)
    (hF : FreeSite a (x - 1 - (a + 1)) (y - (a - 1))) : False := by
  unfold FreeSite FreeHSite FreeVSite at hF
  unfold NativeT at hN
  omega

/-- The duplicate `V` branch of the left neighbour of a black even native point is impossible, away from the special. -/
theorem even_left_dupV_false {a x y : ℤ} (hN : NativeT a x y) (he : (x + y) % 2 = 0)
    (hE : ¬ (x = 0 ∧ y = 2 * a))
    (hF : FreeSite a (x - 1 + 2) (y - 2 * a)) (hq : ¬ (x - 1 + 2 = a + 1 ∧ y - 2 * a = a - 2)) : False := by
  unfold FreeSite FreeHSite FreeVSite at hF
  unfold NativeT at hN
  omega

set_option maxHeartbeats 400000 in
/-- The tile branch of the even black left drop: equal level and both tile points give a drop of one. -/
theorem even_left_tile_drop {a x y : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hp : TwosTile a (x, y))
    (hp2 : ¬ (x = a ∧ y = 2 * a - 1)) (hB1 : ¬ (y - x = -2 ∧ 2 ≤ x ∧ x ≤ a - 1))
    (hF : ¬ (x = a ∧ y = a - 2)) (hi : TwosTile a (x - 1, y)) (hi2 : ¬ (x - 1 = a ∧ y = 2 * a - 1))
    (he : (x + y) % 2 = 0)
    (hbp : -1 ≤ x ∧ x ≤ a + 1 ∧ 0 ≤ y ∧ y ≤ 3 * a - 2 ∧ -2 ≤ y - x ∧ y - x ≤ 2 * a)
    (hbi : -1 ≤ x - 1 ∧ x - 1 ≤ a + 1 ∧ 0 ≤ y ∧ y ≤ 3 * a - 2 ∧ -2 ≤ y - (x - 1) ∧ y - (x - 1) ≤ 2 * a)
    (hL : twosLev a (x - 1) y = twosLev a x y) :
    rhoTwos a 1 (x - 1, y) < rhoTwos a 1 (x, y) := by
  unfold twosLev at hL
  split_ifs at hL
  all_goals
    by_cases fp : FreeSite a x y <;> by_cases fi : FreeSite a (x - 1) y
    · rcases rho_free_cases ha he2 hp fp with Hp | Hp | Hp | Hp | Hp <;>
        rcases rho_free_cases ha he2 hi fi with Hi | Hi | Hi | Hi | Hi <;> omega
    · rcases rho_free_cases ha he2 hp fp with Hp | Hp | Hp | Hp | Hp <;>
        rcases rho_bulk_cases ha he2 hi fi hi2 with Hi | Hi | Hi | Hi | Hi | Hi | Hi <;> omega
    · rcases rho_bulk_cases ha he2 hp fp hp2 with Hp | Hp | Hp | Hp | Hp | Hp | Hp <;>
        rcases rho_free_cases ha he2 hi fi with Hi | Hi | Hi | Hi | Hi <;> omega
    · rcases rho_bulk_cases ha he2 hp fp hp2 with Hp | Hp | Hp | Hp | Hp | Hp | Hp <;>
        rcases rho_bulk_cases ha he2 hi fi hi2 with Hi | Hi | Hi | Hi | Hi | Hi | Hi <;> omega

set_option maxHeartbeats 400000 in
/-- **The even black left drop.** For a black even non-special tile point `p = (x, y)` whose left neighbour `(x-1, y)` has
the same potential, the rank of the neighbour is one less. -/
theorem even_black_drop_left {a x y : ℤ} {k : ℕ} (hk : a = 2 * (k : ℤ) + 4)
    (hp : TwosTile a (x, y)) (hp1 : ¬ (x = a ∧ y = 2 * a - 2)) (hp2 : ¬ (x = a ∧ y = 2 * a - 1))
    (hp3 : ¬ (x = a + 1 ∧ y = a - 2)) (hB : ¬ EvenWhitePiece a x y) (he : (x + y) % 2 = 0)
    (hΦ : twosPhi k 1 (x - 1, y) = twosPhi k 1 (x, y)) :
    rhoTwos a 1 (x - 1, y) < rhoTwos a 1 (x, y) := by
  have ha : (4 : ℤ) ≤ a := by omega
  have he2 : a % 2 = 0 := by omega
  have hN_p : NativeT a x y := ((tile_iff_lin _ _ _).mp hp).1
  have hbp : -1 ≤ x ∧ x ≤ a + 1 ∧ 0 ≤ y ∧ y ≤ 3 * a - 2 ∧ -2 ≤ y - x ∧ y - x ≤ 2 * a := by
    unfold NativeT at hN_p
    omega
  have hN_i : NativeT a (x - 1) y := even_black_nat_left ha hN_p hB he
  have hE : ¬ (x = 0 ∧ y = 2 * a) := fun h => hB (ewp_9 h)
  have hB1 : ¬ (y - x = -2 ∧ 2 ≤ x ∧ x ≤ a - 1) := fun h => hB (ewp_4 h)
  have hF : ¬ (x = a ∧ y = a - 2) := fun h => hB (ewp_10 h)
  have hi1 : ¬ (x - 1 = a ∧ y = 2 * a - 2) := by
    intro h
    omega
  have hi2 : ¬ (x - 1 = a ∧ y = 2 * a - 1) := by
    intro h
    unfold NativeT at hN_p
    omega
  have hi3 : ¬ (x - 1 = a + 1 ∧ y = a - 2) := by
    intro h
    omega
  have hbi : -1 ≤ x - 1 ∧ x - 1 ≤ a + 1 ∧ 0 ≤ y ∧ y ≤ 3 * a - 2 ∧ -2 ≤ y - (x - 1) ∧ y - (x - 1) ≤ 2 * a := by
    unfold NativeT at hN_i
    have hE' : ¬ (x - 1 = -1 ∧ y = 2 * a) := by
      intro h
      exact hE ⟨by omega, h.2⟩
    omega
  rcases flat_levels hk hp hp1 hp2 hp3 hN_i hi1 hi2 hi3 hΦ with ⟨hT, hL⟩ | ⟨hFq, hNq, hL⟩ | ⟨hFq, hNq, hL, hq⟩ | hq
  · exact even_left_tile_drop ha he2 hp hp2 hB1 hF hT hi2 he hbp hbi hL
  · exact absurd hFq (fun h => even_left_dupU_false hN_p he h)
  · exact absurd hFq (fun h => even_left_dupV_false hN_p he hE h hq)
  · exfalso
    exact hB (ewp_6 ⟨by omega, by omega, by omega⟩)

/-- A bulk tile point has no `U`-duplicate of a free native site. -/
theorem bulk_nodup_U {a x y : ℤ} (hp : TwosTile a (x, y)) (hF : ¬ FreeSite a x y) :
    ¬ (FreeSite a (x - (a + 1)) (y - (a - 1)) ∧ NativeT a (x - (a + 1)) (y - (a - 1))) := by
  have h := ((tile_iff_lin _ _ _).mp hp).2
  intro hd
  exact h ⟨Or.inl hd, hF⟩

/-- A bulk tile point has no `V`-duplicate of a free native site. -/
theorem bulk_nodup_V {a x y : ℤ} (hp : TwosTile a (x, y)) (hF : ¬ FreeSite a x y) :
    ¬ (FreeSite a (x + 2) (y - 2 * a) ∧ NativeT a (x + 2) (y - 2 * a)) := by
  have h := ((tile_iff_lin _ _ _).mp hp).2
  intro hd
  exact h ⟨Or.inr hd, hF⟩

/-- The duplicate `U` branch of the right neighbour of a black even native point is impossible. -/
theorem even_right_dupU_false {a x y : ℤ} (hN : NativeT a x y) (he : (x + y) % 2 = 0)
    (hB2 : ¬ (x = a + 1 ∧ a - 1 ≤ y ∧ y ≤ 2 * a - 3))
    (hF : FreeSite a (x + 1 - (a + 1)) (y - (a - 1)))
    (hL : twosLev a (x + 1 - (a + 1)) (y - (a - 1)) = twosLev a x y + 1) : False := by
  unfold twosLev at hL
  unfold FreeSite FreeHSite FreeVSite at hF
  unfold NativeT at hN
  split_ifs at hL <;> omega

/-- The duplicate `V` branch of the right neighbour of an even native point is impossible, away from the special. -/
theorem even_right_dupV_false {a x y : ℤ} (he : (x + y) % 2 = 0) (hx : -1 ≤ x)
    (hF : FreeSite a (x + 1 + 2) (y - 2 * a)) (hq : ¬ (x + 1 + 2 = a + 1 ∧ y - 2 * a = a - 2)) : False := by
  unfold FreeSite FreeHSite FreeVSite at hF
  omega

set_option maxHeartbeats 400000 in
/-- The tile branch of the even black right drop: equal level and both tile points give a drop of one. -/
theorem even_right_tile_drop {a x y : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hp : TwosTile a (x, y))
    (hp2 : ¬ (x = a ∧ y = 2 * a - 1)) (hC : ¬ (y - x = a ∧ 0 ≤ x ∧ x ≤ a - 2))
    (hB3 : ¬ (x = a ∧ 2 * a - 2 ≤ y ∧ y ≤ 3 * a - 2))
    (hi : TwosTile a (x + 1, y)) (hi2 : ¬ (x + 1 = a ∧ y = 2 * a - 1))
    (he : (x + y) % 2 = 0)
    (hbp : -1 ≤ x ∧ x ≤ a ∧ 0 ≤ y ∧ y ≤ 3 * a - 2 ∧ -2 ≤ y - x ∧ y - x ≤ 2 * a)
    (hbi : -1 ≤ x + 1 ∧ x + 1 ≤ a + 1 ∧ 0 ≤ y ∧ y ≤ 3 * a - 2 ∧ -2 ≤ y - (x + 1) ∧ y - (x + 1) ≤ 2 * a)
    (hL : twosLev a (x + 1) y = twosLev a x y) :
    rhoTwos a 1 (x + 1, y) < rhoTwos a 1 (x, y) := by
  unfold twosLev at hL
  split_ifs at hL
  all_goals
    by_cases fp : FreeSite a x y <;> by_cases fi : FreeSite a (x + 1) y
    · rcases rho_free_cases ha he2 hp fp with Hp | Hp | Hp | Hp | Hp <;>
        rcases rho_free_cases ha he2 hi fi with Hi | Hi | Hi | Hi | Hi <;> omega
    · have di1 := bulk_nodup_U hi fi
      have di2 := bulk_nodup_V hi fi
      rcases rho_free_cases ha he2 hp fp with Hp | Hp | Hp | Hp | Hp <;>
        rcases rho_bulk_cases ha he2 hi fi hi2 with Hi | Hi | Hi | Hi | Hi | Hi | Hi <;> omega
    · have dp1 := bulk_nodup_U hp fp
      have dp2 := bulk_nodup_V hp fp
      rcases rho_bulk_cases ha he2 hp fp hp2 with Hp | Hp | Hp | Hp | Hp | Hp | Hp <;>
        rcases rho_free_cases ha he2 hi fi with Hi | Hi | Hi | Hi | Hi <;> omega
    · have dp1 := bulk_nodup_U hp fp
      have dp2 := bulk_nodup_V hp fp
      have di1 := bulk_nodup_U hi fi
      have di2 := bulk_nodup_V hi fi
      rcases rho_bulk_cases ha he2 hp fp hp2 with Hp | Hp | Hp | Hp | Hp | Hp | Hp <;>
        rcases rho_bulk_cases ha he2 hi fi hi2 with Hi | Hi | Hi | Hi | Hi | Hi | Hi <;> omega

set_option maxHeartbeats 400000 in
/-- **The even black right drop.** For a black even non-special tile point `p = (x, y)` whose right neighbour `(x+1, y)` has
the same potential and is not the special `(a, 2a-1)`, the rank of the neighbour is one less. -/
theorem even_black_drop_right {a x y : ℤ} {k : ℕ} (hk : a = 2 * (k : ℤ) + 4)
    (hp : TwosTile a (x, y)) (hp1 : ¬ (x = a ∧ y = 2 * a - 2)) (hp2 : ¬ (x = a ∧ y = 2 * a - 1))
    (hp3 : ¬ (x = a + 1 ∧ y = a - 2)) (hB : ¬ EvenWhitePiece a x y) (he : (x + y) % 2 = 0)
    (hΦ : twosPhi k 1 (x + 1, y) = twosPhi k 1 (x, y)) :
    rhoTwos a 1 (x + 1, y) < rhoTwos a 1 (x, y) := by
  by_cases hsp : x + 1 = a ∧ y = 2 * a - 1
  · exfalso
    have hx : x = a - 1 := by omega
    have hy : y = 2 * a - 1 := hsp.2
    subst hx
    subst hy
    have hp' : TwosTile a (a - 1, 2 * a - 1) := hp
    have hΦ' : twosPhi k 1 (a, 2 * a - 1) = twosPhi k 1 (a - 1, 2 * a - 1) := by
      rw [show a - 1 + 1 = a by ring] at hΦ
      exact hΦ
    exact right_special_nonflat hk hp' hΦ'
  have ha : (4 : ℤ) ≤ a := by omega
  have he2 : a % 2 = 0 := by omega
  have hN_p : NativeT a x y := ((tile_iff_lin _ _ _).mp hp).1
  have hC : ¬ (y - x = a ∧ 0 ≤ x ∧ x ≤ a - 2) := fun h => hB (ewp_7 h)
  have hF : ¬ (x = a ∧ y = a - 2) := fun h => hB (ewp_10 h)
  have hB2 : ¬ (x = a + 1 ∧ a - 1 ≤ y ∧ y ≤ 2 * a - 3) := fun h => hB (ewp_5 h)
  have hB3 : ¬ (x = a ∧ 2 * a - 2 ≤ y ∧ y ≤ 3 * a - 2) := fun h => hB (ewp_6 h)
  have hbp : -1 ≤ x ∧ x ≤ a ∧ 0 ≤ y ∧ y ≤ 3 * a - 2 ∧ -2 ≤ y - x ∧ y - x ≤ 2 * a := by
    unfold NativeT at hN_p
    omega
  have hN_i : NativeT a (x + 1) y := even_black_nat_right ha hN_p hB he
  have hA1 : ¬ (y - x = 2 * a ∧ 1 ≤ x ∧ x ≤ a - 2) := fun h => hB (ewp_1 h)
  have hi1 : ¬ (x + 1 = a ∧ y = 2 * a - 2) := by
    intro h
    omega
  have hi3 : ¬ (x + 1 = a + 1 ∧ y = a - 2) := by
    intro h
    exact hF ⟨by omega, by omega⟩
  have hbi : -1 ≤ x + 1 ∧ x + 1 ≤ a + 1 ∧ 0 ≤ y ∧ y ≤ 3 * a - 2 ∧ -2 ≤ y - (x + 1) ∧ y - (x + 1) ≤ 2 * a := by
    unfold NativeT at hN_i
    omega
  rcases flat_levels hk hp hp1 hp2 hp3 hN_i hi1 hsp hi3 hΦ with ⟨hT, hL⟩ | ⟨hFq, hNq, hL⟩ | ⟨hFq, hNq, hL, hq⟩ | hq
  · exact even_right_tile_drop ha he2 hp hp2 hC hB3 hT hsp he hbp hbi hL
  · exact absurd hFq (fun h => even_right_dupU_false hN_p he hB2 h hL)
  · exact absurd hFq (fun h => even_right_dupV_false he (by omega) h hq)
  · exfalso
    exact hB (ewp_1 ⟨by omega, by omega, by omega⟩)

end FLatticePaper.TwosEPolicy
