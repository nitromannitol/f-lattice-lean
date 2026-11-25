import FLatticePaper.Plane.Induction.TwosMinusRank
import FLatticePaper.Plane.Induction.TwosMinusLevel
import FLatticePaper.Plane.Induction.TwosBlackDrop

/-! Twos flatness, sign `-1`, the odd black centres. An odd black tile point lies on one of the lines `L1: y = 2a-1, 0 ≤ x ≤ a-2`,
`L2: y = a-1, 2 ≤ x ≤ a`, `L3: y - x = a-1, 1 ≤ x ≤ a-1`. The upper vertical neighbour has rank one less, for every potential
(`odd_black_up_m`). The lower neighbour has rank one less, except on the diagonal `L3` with `3 ≤ x ≤ a/2`, where the two points
have different sign `-1` potentials (`diag_down_ne`), so the edge is not flat (`odd_black_down_m`). The rank values are the
closed forms of `bulkR` and `freeH` at sign `-1`, each proved by unfolding the definition and splitting its conditions. -/

noncomputable section

namespace FLatticePaper.TwosEPolicy

open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey
open scoped Classical

/-! ### Rank values at the odd black lines (sign `-1`) -/

theorem bulkM_top {a x : ℤ} (_ha : 4 ≤ a) (he2 : a % 2 = 0) (hx0 : 0 ≤ x) (hx1 : x ≤ a - 2) (hxe : x % 2 = 0) :
    bulkR a (-1) x (2 * a - 1) = 2 * a := by
  unfold bulkR
  simp only [show ((-1 : ℤ) = 1) = False from by norm_num, if_false]
  split_ifs <;> omega

theorem bulkM_top_up {a x : ℤ} (_ha : 4 ≤ a) (he2 : a % 2 = 0) (hx2 : 2 ≤ x) (hx1 : x ≤ a - 2) (hxe : x % 2 = 0) :
    bulkR a (-1) x (2 * a) = 1 := by
  unfold bulkR
  simp only [show ((-1 : ℤ) = 1) = False from by norm_num, if_false]
  split_ifs <;> omega

theorem bulkM_top_dn {a x : ℤ} (_ha : 4 ≤ a) (he2 : a % 2 = 0) (_hx0 : 0 ≤ x) (hx1 : x ≤ a - 2) (hxe : x % 2 = 0) :
    bulkR a (-1) x (2 * a - 2) = 2 * a - 1 := by
  unfold bulkR
  simp only [show ((-1 : ℤ) = 1) = False from by norm_num, if_false]
  split_ifs <;> omega

theorem bulkM_mid_line {a x : ℤ} (_ha : 4 ≤ a) (he2 : a % 2 = 0) (hx2 : 2 ≤ x) (hx1 : x ≤ a - 2) (hxe : x % 2 = 0) :
    bulkR a (-1) x (a - 1) = 2 * a - 2 := by
  unfold bulkR
  simp only [show ((-1 : ℤ) = 1) = False from by norm_num, if_false]
  split_ifs <;> omega

theorem bulkM_up_line {a x : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hx2 : 2 ≤ x) (hx1 : x ≤ a - 2) (hxe : x % 2 = 0) :
    bulkR a (-1) x a = 1 := by
  unfold bulkR
  simp only [show ((-1 : ℤ) = 1) = False from by norm_num, if_false]
  split_ifs <;> omega

theorem bulkM_dn_line {a x : ℤ} (_ha : 4 ≤ a) (he2 : a % 2 = 0) (hx2 : 2 ≤ x) (_hx1 : x ≤ a - 2) (hxe : x % 2 = 0) :
    bulkR a (-1) x (a - 2) = 2 * a - 3 := by
  unfold bulkR
  simp only [show ((-1 : ℤ) = 1) = False from by norm_num, if_false]
  split_ifs <;> omega

theorem bulkM_aa1 {a : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) : bulkR a (-1) a (a - 1) = 8 := by
  unfold bulkR
  simp only [show ((-1 : ℤ) = 1) = False from by norm_num, if_false]
  split_ifs <;> omega

theorem bulkM_aa {a : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) : bulkR a (-1) a a = 1 := by
  unfold bulkR
  simp only [show ((-1 : ℤ) = 1) = False from by norm_num, if_false]
  split_ifs <;> omega

theorem bulkM_diag_one {a : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) : bulkR a (-1) 1 (1 + a - 1) = 2 * a := by
  unfold bulkR
  simp only [show ((-1 : ℤ) = 1) = False from by norm_num, if_false]
  split_ifs <;> omega

theorem bulkM_diag {a x : ℤ} (_ha : 4 ≤ a) (he2 : a % 2 = 0) (hx2 : 2 ≤ x) (hx1 : x ≤ a - 1) :
    bulkR a (-1) x (x + a - 1) = 2 * x + 4 := by
  unfold bulkR
  simp only [show ((-1 : ℤ) = 1) = False from by norm_num, if_false]
  split_ifs <;> omega

theorem bulkM_diag_up {a x : ℤ} (_ha : 4 ≤ a) (he2 : a % 2 = 0) (_hx0 : 1 ≤ x) (hx1 : x ≤ a - 1) :
    bulkR a (-1) x (x + a) = 2 * x + 3 := by
  unfold bulkR
  simp only [show ((-1 : ℤ) = 1) = False from by norm_num, if_false]
  split_ifs <;> omega

theorem bulkM_diag_dn_one {a : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) : bulkR a (-1) 1 (1 + a - 2) = 2 * a - 1 := by
  unfold bulkR
  simp only [show ((-1 : ℤ) = 1) = False from by norm_num, if_false]
  split_ifs <;> omega

theorem bulkM_diag_dn_two {a : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) : bulkR a (-1) 2 (2 + a - 2) = 1 := by
  unfold bulkR
  simp only [show ((-1 : ℤ) = 1) = False from by norm_num, if_false]
  split_ifs <;> omega

theorem bulkM_diag_dn {a x : ℤ} (_ha : 4 ≤ a) (he2 : a % 2 = 0) (hx3 : 3 ≤ x) (_hx1 : x ≤ a - 1) :
    bulkR a (-1) x (x + a - 2) = 2 * a - 2 * x + 5 := by
  unfold bulkR
  simp only [show ((-1 : ℤ) = 1) = False from by norm_num, if_false]
  split_ifs <;> omega

theorem freeH_minus_two {a : ℤ} (ha : 4 ≤ a) : freeH a (-1) 2 0 = 1 := by
  unfold freeH
  simp only [show ((-1 : ℤ) = 1) = False from by norm_num, if_false]
  split_ifs <;> omega

theorem freeH_minus_last {a : ℤ} (ha : 4 ≤ a) : freeH a (-1) a (a - 2) = 7 := by
  unfold freeH
  simp only [show ((-1 : ℤ) = 1) = False from by norm_num, if_false]
  split_ifs <;> omega

/-! ### The diagonal exception -/

/-- A key point which is in neither slip band has slip `1`. -/
theorem twosSlip_eq_one_of (k : ℕ) {z1 z2 : ℤ} (hk : TwosKey (2 * (k : ℤ) + 4) z1 z2)
    (h0 : ¬ TwosSlipZ0 (2 * (k : ℤ) + 4) z1 z2) (h2 : ¬ TwosSlipZ2 (2 * (k : ℤ) + 4) z1 z2) :
    twosSlip k (z1, z2) = 1 := by
  rcases twos_slip_value k hk with ⟨hs, hz⟩ | ⟨hs, -, -⟩ | ⟨hs, hz⟩
  · exact absurd hz h0
  · exact hs
  · exact absurd hz h2

/-- On the diagonal `L3` with `3 ≤ x ≤ a/2` (`y = x+a-1`), the sign `-1` potentials of `(x, y-1)` and `(x, y)` differ. -/
theorem diag_down_ne (k : ℕ) {x y : ℤ} (hy : y = x + 2 * (k : ℤ) + 3) (hx3 : 3 ≤ x) (hxh : x ≤ (k : ℤ) + 2) :
    (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1)
        (x, y - 1) ≠
      (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1)
        (x, y) := by
  have hNp : NativeT (2 * (k : ℤ) + 4) x y := by
    unfold NativeT
    omega
  have hNi : NativeT (2 * (k : ℤ) + 4) x (y - 1) := by
    unfold NativeT
    omega
  rw [chainM_native_level k hNi (by omega), chainM_native_level k hNp (by omega)]
  intro h
  have hkp : TwosKey (2 * (k : ℤ) + 4) (x - 1) (y - 1) := by
    unfold TwosKey
    omega
  have hki : TwosKey (2 * (k : ℤ) + 4) (x - 1) (y - 1 - 1) := by
    unfold TwosKey
    omega
  have sp := twosSlip_eq_one_of k hkp (by unfold TwosSlipZ0; omega) (by unfold TwosSlipZ2; omega)
  have si := twosSlip_eq_one_of k hki (by unfold TwosSlipZ0; omega) (by unfold TwosSlipZ2; omega)
  have dp : ¬ TwosDelta k (x - 1) (y - 1) := by
    unfold TwosDelta
    omega
  have di : TwosDelta k (x - 1) (y - 1 - 1) := by
    unfold TwosDelta
    omega
  rw [if_pos di, if_neg dp, si, sp] at h
  omega

/-! ### The up and down neighbours -/

/-- The upper vertical neighbour of an odd black tile point has rank one less, for every potential. -/
theorem odd_black_up_m {a : ℤ} {k : ℕ} (hk : a = 2 * (k : ℤ) + 4) {x y : ℤ}
    (hB : (y = 2 * a - 1 ∧ 0 ≤ x ∧ x ≤ a - 2) ∨ (y = a - 1 ∧ 2 ≤ x ∧ x ≤ a) ∨
      (y - x = a - 1 ∧ 1 ≤ x ∧ x ≤ a - 1))
    (hp : TwosTile a (x, y)) (hodd : (x + y) % 2 = 1) :
    rhoTwos a (-1) (x, y + 1) < rhoTwos a (-1) (x, y) := by
  have ha : (4 : ℤ) ≤ a := by omega
  have he2 : a % 2 = 0 := by omega
  rcases hB with ⟨hy, hx0, hx1⟩ | ⟨hy, hx0, hx1⟩ | ⟨hy, hx0, hx1⟩
  · subst hy
    have hxe : x % 2 = 0 := by omega
    rcases (show x = 0 ∨ 2 ≤ x by omega) with rfl | hx2
    · have hv : TwosTile a (2, 0) := tile_pt (by unfold NativeT; omega)
        (by unfold FreeSite FreeHSite FreeVSite; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
      have e : rhoTwos a (-1) (0, 2 * a) = rhoTwos a (-1) (2, 0) := by
        have h := rhoTwos_add_V_eta (-1) a 2 0
        rw [show (2 : ℤ) + -2 = 0 by norm_num, show (0 : ℤ) + 2 * a = 2 * a by ring] at h
        exact h
      rw [show 2 * a - 1 + 1 = 2 * a by ring, e,
        rhoTwos_tile_freeH_eta (-1) ha he2 hv (by unfold FreeHSite; omega),
        rhoTwos_tile_bulk_eta (-1) ha he2 hp (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega),
        freeH_minus_two ha, bulkM_top ha he2 hx0 hx1 hxe]
      omega
    · have hi : TwosTile a (x, 2 * a) := tile_pt (by unfold NativeT; omega)
        (by unfold FreeSite FreeHSite FreeVSite; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
      rw [show 2 * a - 1 + 1 = 2 * a by ring,
        rhoTwos_tile_bulk_eta (-1) ha he2 hi (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega),
        rhoTwos_tile_bulk_eta (-1) ha he2 hp (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega),
        bulkM_top_up ha he2 hx2 hx1 hxe, bulkM_top ha he2 hx0 hx1 hxe]
      omega
  · subst hy
    have hxe : x % 2 = 0 := by omega
    by_cases hxa : x = a
    · subst x
      have hi : TwosTile a (a, a) := tile_pt (by unfold NativeT; omega)
        (by unfold FreeSite FreeHSite FreeVSite; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
      rw [show a - 1 + 1 = a by ring,
        rhoTwos_tile_bulk_eta (-1) ha he2 hi (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega),
        rhoTwos_tile_bulk_eta (-1) ha he2 hp (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega),
        bulkM_aa ha he2, bulkM_aa1 ha he2]
      omega
    · have hi : TwosTile a (x, a) := tile_pt (by unfold NativeT; omega)
        (by unfold FreeSite FreeHSite FreeVSite; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
      rw [show a - 1 + 1 = a by ring,
        rhoTwos_tile_bulk_eta (-1) ha he2 hi (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega),
        rhoTwos_tile_bulk_eta (-1) ha he2 hp (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega),
        bulkM_up_line ha he2 hx0 (by omega) hxe, bulkM_mid_line ha he2 hx0 (by omega) hxe]
      omega
  · have hy' : y = x + a - 1 := by omega
    subst hy'
    have hi : TwosTile a (x, x + a) := tile_pt (by unfold NativeT; omega)
      (by unfold FreeSite FreeHSite FreeVSite; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
    rw [show x + a - 1 + 1 = x + a by ring,
      rhoTwos_tile_bulk_eta (-1) ha he2 hi (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega),
      rhoTwos_tile_bulk_eta (-1) ha he2 hp (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega),
      bulkM_diag_up ha he2 hx0 hx1]
    by_cases h1 : x = 1
    · subst h1
      rw [bulkM_diag_one ha he2]
      omega
    · rw [bulkM_diag ha he2 (by omega) hx1]
      omega

/-- The lower vertical neighbour of an odd black tile point has rank one less on a flat edge. -/
theorem odd_black_down_m {a : ℤ} {k : ℕ} (hk : a = 2 * (k : ℤ) + 4) {x y : ℤ}
    (hB : (y = 2 * a - 1 ∧ 0 ≤ x ∧ x ≤ a - 2) ∨ (y = a - 1 ∧ 2 ≤ x ∧ x ≤ a) ∨
      (y - x = a - 1 ∧ 1 ≤ x ∧ x ≤ a - 1))
    (hp : TwosTile a (x, y)) (hodd : (x + y) % 2 = 1)
    (hΦ : (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1)
        (x, y - 1) =
      (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1)
        (x, y)) :
    rhoTwos a (-1) (x, y - 1) < rhoTwos a (-1) (x, y) := by
  have ha : (4 : ℤ) ≤ a := by omega
  have he2 : a % 2 = 0 := by omega
  rcases hB with ⟨hy, hx0, hx1⟩ | ⟨hy, hx0, hx1⟩ | ⟨hy, hx0, hx1⟩
  · subst hy
    have hxe : x % 2 = 0 := by omega
    have hi : TwosTile a (x, 2 * a - 2) := tile_pt (by unfold NativeT; omega)
      (by unfold FreeSite FreeHSite FreeVSite; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
    rw [show 2 * a - 1 - 1 = 2 * a - 2 by ring,
      rhoTwos_tile_bulk_eta (-1) ha he2 hi (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega),
      rhoTwos_tile_bulk_eta (-1) ha he2 hp (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega),
      bulkM_top_dn ha he2 hx0 hx1 hxe, bulkM_top ha he2 hx0 hx1 hxe]
    omega
  · subst hy
    have hxe : x % 2 = 0 := by omega
    by_cases hxa : x = a
    · subst x
      have hi : TwosTile a (a, a - 2) := tile_pt (by unfold NativeT; omega)
        (by unfold FreeSite FreeHSite FreeVSite; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
      rw [show a - 1 - 1 = a - 2 by ring]
      rw [rhoTwos_tile_freeH_eta (-1) ha he2 hi (by unfold FreeHSite; omega),
        rhoTwos_tile_bulk_eta (-1) ha he2 hp (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega),
        freeH_minus_last ha, bulkM_aa1 ha he2]
      omega
    · have hi : TwosTile a (x, a - 2) := tile_pt (by unfold NativeT; omega)
        (by unfold FreeSite FreeHSite FreeVSite; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
      rw [show a - 1 - 1 = a - 2 by ring,
        rhoTwos_tile_bulk_eta (-1) ha he2 hi (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega),
        rhoTwos_tile_bulk_eta (-1) ha he2 hp (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega),
        bulkM_dn_line ha he2 hx0 (by omega) hxe, bulkM_mid_line ha he2 hx0 (by omega) hxe]
      omega
  · have hy' : y = x + a - 1 := by omega
    subst hy'
    rw [show x + a - 1 - 1 = x + a - 2 by ring]
    by_cases hflat : x ≤ 2 ∨ (k : ℤ) + 3 ≤ x
    · have hi : TwosTile a (x, x + a - 2) := tile_pt (by unfold NativeT; omega)
        (by unfold FreeSite FreeHSite FreeVSite; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
      rw [rhoTwos_tile_bulk_eta (-1) ha he2 hi (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega),
        rhoTwos_tile_bulk_eta (-1) ha he2 hp (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega)]
      by_cases h1 : x = 1
      · subst h1
        rw [bulkM_diag_dn_one ha he2, bulkM_diag_one ha he2]
        omega
      · by_cases h2 : x = 2
        · subst h2
          rw [bulkM_diag_dn_two ha he2, bulkM_diag ha he2 (by omega) (by omega)]
          omega
        · rw [bulkM_diag_dn ha he2 (by omega) (by omega), bulkM_diag ha he2 (by omega) (by omega)]
          omega
    · exfalso
      exact diag_down_ne k (by omega) (by omega) (by omega) hΦ

end FLatticePaper.TwosEPolicy
