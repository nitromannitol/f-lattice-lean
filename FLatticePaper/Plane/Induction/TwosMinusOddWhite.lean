import FLatticePaper.Plane.Induction.TwosMinusEvenBlack
import FLatticePaper.Plane.Induction.TwosFreeCases
import FLatticePaper.Plane.Induction.TwosWhiteSel
import FLatticePaper.Plane.Induction.TwosFreeAlias
import FLatticePaper.Plane.Induction.TwosTileUnique
import FLatticePaper.Plane.Induction.TwosDeckMinus
import FLatticePaper.Plane.Induction.TwosMinusRank
import FLatticePaper.Plane.Induction.TwosSquares
import FLatticePaper.Plane.Induction.TwosCandSel

/-! Twos flatness, sign `-1`, the odd white centres: the free H site `(1, 0)`. Its sign `-1` selected target is `(1, 1)`
(`freeDisp a (-1) 1 0 = (0, 1)`), in the bulk box. -/

noncomputable section

namespace FLatticePaper.TwosEPolicy

open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey
open scoped Classical

/-- The free H site `(1, 0)` has rank `4` for sign `-1`. -/
theorem freeH_minus_one_zero {a : ℤ} : freeH a (-1) 1 0 = 4 := by
  unfold freeH
  norm_num

/-- The sign `-1` rank of the bulk point `(1, 1)` is `3`. -/
theorem bulkTreeM_one_one {a : ℤ} (ha : 4 ≤ a) : bulkTreeM a 1 1 = 3 := by
  unfold bulkTreeM
  split_ifs <;> omega

/-- The free H site `(1, 0)`: its sign `-1` selected target `(1, 1)` has rank one less. -/
theorem free_H1_minus {a : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) :
    rhoTwos a (-1) (1, 1) < rhoTwos a (-1) (1, 0) := by
  have hp : TwosTile a (1, 0) := free_tile (Or.inl (Or.inl ⟨rfl, rfl⟩)) (by unfold NativeT; omega)
  have hq : TwosTile a (1, 1) :=
    tile_pt (by unfold NativeT; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
      (by unfold FreeSite FreeHSite FreeVSite; omega)
  rw [rhoTwos_tile_freeH_eta (-1) ha he2 hp (Or.inl ⟨rfl, rfl⟩), freeH_minus_one_zero,
    rho_bulk_eq_m ha he2 hq (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega),
    bulkTreeM_one_one ha]
  norm_num

/-- The bulk point `(0, a)` has sign `-1` rank `3`. -/
theorem bulkTreeM_zero_a {a : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) : bulkTreeM a 0 a = 3 := by
  unfold bulkTreeM
  split_ifs <;> omega

/-- The free V site `(0, y)` with `y` odd: its sign `-1` selected target is `(0, y+1)`, which has rank one less. -/
theorem free_V0_odd_minus {a y : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hy0 : 1 ≤ y) (hya : y < a) (hodd : y % 2 = 1) :
    rhoTwos a (-1) (0, y + 1) < rhoTwos a (-1) (0, y) := by
  have hp : TwosTile a (0, y) := free_tile (Or.inr (Or.inl ⟨rfl, by omega, by omega⟩)) (by unfold NativeT; omega)
  rw [rhoTwos_tile_freeV_eta (-1) ha he2 hp (by unfold FreeHSite; omega)
    (Or.inl ⟨rfl, by omega, by omega⟩), freeV_minus_eq]
  by_cases hTop : y + 1 = a
  · have hq : TwosTile a (0, a) :=
      tile_pt (by unfold NativeT; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
        (by unfold FreeSite FreeHSite FreeVSite; omega)
    rw [hTop]
    rw [rho_bulk_eq_m ha he2 hq (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega), bulkTreeM_zero_a ha he2]
    split_ifs <;> omega
  · have hq : TwosTile a (0, y + 1) :=
      free_tile (Or.inr (Or.inl ⟨rfl, by omega, by omega⟩)) (by unfold NativeT; omega)
    rw [rhoTwos_tile_freeV_eta (-1) ha he2 hq (by unfold FreeHSite; omega)
      (Or.inl ⟨rfl, by omega, by omega⟩), freeV_minus_eq]
    split_ifs <;> omega

/-- The free displacement at the alias `(-1, a)` of the special point, for sign `-1`: it is `(0, 1)`. -/
theorem freeDisp_minus_at_a {a : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) : freeDisp a (-1) (-1) a = (0, 1) := by
  unfold freeDisp
  rw [if_neg (by unfold FreeHSite; omega), if_neg (by omega), if_neg (by unfold EvenSite; dsimp only; omega)]
  norm_num

/-- The sign `-1` selected input of the special tile point `(a, 2a-1)` is `(a, 2a)`. -/
theorem twosSel_special_minus (k : ℕ) {i1 i2 : ℤ}
    (hl : laplacian (standardField (List.replicate (k + 1) Digit.two)) (2 * (k : ℤ) + 4, 2 * (2 * (k : ℤ) + 4) - 1) = 0)
    (ha : 4 ≤ 2 * (k : ℤ) + 4)
    (h : TwosSel (2 * (k : ℤ) + 4) (-1) (standardField (List.replicate (k + 1) Digit.two))
      (2 * (k : ℤ) + 4, 2 * (2 * (k : ℤ) + 4) - 1) (i1, i2)) :
    (i1, i2) = (2 * (k : ℤ) + 4, 2 * (2 * (k : ℤ) + 4)) := by
  have he2 : (2 * (k : ℤ) + 4) % 2 = 0 := by omega
  rcases h with ⟨hm, -⟩ | ⟨-, h2 | ⟨hnfc, -⟩⟩
  · rw [hl] at hm
    norm_num at hm
  · obtain ⟨⟨u1, u2⟩, hu, huF, hi⟩ := h2
    by_cases hN : NativeT (2 * (k : ℤ) + 4) u1 u2
    · exfalso
      have hut : TwosTile (2 * (k : ℤ) + 4) (u1, u2) := free_tile huF hN
      have hk : classKey (2 * (k : ℤ) + 4) (u1, u2) = classKey (2 * (k : ℤ) + 4)
          (2 * (k : ℤ) + 4, 2 * (2 * (k : ℤ) + 4) - 1) := alias_classKey hu
      have hp : TwosTile (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 4, 2 * (2 * (k : ℤ) + 4) - 1) := tile_a_2a1 ha
      obtain ⟨e1, e2⟩ := tile_unique ha he2 hut hp hk
      rw [e1, e2] at huF
      unfold FreeSite FreeHSite FreeVSite at huF
      omega
    · have hxy := free_nonnative_eq ha huF hN
      obtain ⟨hx, hy⟩ := hxy
      subst hx
      subst hy
      simp only at hi
      rw [freeDisp_minus_at_a ha he2] at hi
      simp only [Prod.mk.injEq] at hi
      obtain ⟨h1, h2⟩ := hi
      rw [h1, h2]
      exact Prod.ext (by ring) (by ring)
  · exfalso
    exact hnfc ⟨(-1, 2 * (k : ℤ) + 4), ⟨1, 0, Prod.ext (by dsimp only; ring) (by dsimp only; ring)⟩,
      Or.inr (Or.inr ⟨rfl, by omega, by omega⟩)⟩

/-- The special tile point `(a, 2a-1)` for sign `-1`: its selected input `(a, 2a)` has rank `1`, below its rank `2`. -/
theorem special_minus_rho_drop {a : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) :
    rhoTwos a (-1) (a, 2 * a) < rhoTwos a (-1) (a, 2 * a - 1) := by
  have hU := rhoTwos_add_U_eta (-1) a (-1) (a + 1)
  rw [show (-1 : ℤ) + (a + 1) = a by ring, show (a + 1 : ℤ) + (a - 1) = 2 * a by ring] at hU
  rw [hU]
  have hq : TwosTile a (-1, a + 1) := free_tile (Or.inr (Or.inr ⟨rfl, by omega, by omega⟩)) (by unfold NativeT; omega)
  rw [rhoTwos_tile_freeV_eta (-1) ha he2 hq (by unfold FreeHSite; omega) (Or.inr ⟨rfl, by omega, by omega⟩),
    freeV_minus_eq, rhoTwos_tile_eta (-1) ha he2 (tile_a_2a1 ha), deck_special_minus ha]
  split_ifs <;> omega

/-- The slip at `(a, a-3)` is `0`: it is the `V` translate of `(a-2, 3a-3)`, which lies in the upper band, where the slip is `2`. -/
theorem twosSlip_a_a3_zero (k : ℕ) :
    twosSlip k (2 * (k : ℤ) + 4, 2 * (k : ℤ) + 4 - 3) = 0 := by
  have hV := twosSlip_V k (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 4 - 3)
  have hK : TwosKey (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 4 + (-2)) (2 * (k : ℤ) + 4 - 3 + (4 * (k : ℤ) + 8)) := by
    unfold TwosKey
    omega
  have h2 : TwosSlipZ2 (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 4 + (-2)) (2 * (k : ℤ) + 4 - 3 + (4 * (k : ℤ) + 8)) := by
    unfold TwosSlipZ2
    omega
  have h0 : ¬ TwosSlipZ0 (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 4 + (-2)) (2 * (k : ℤ) + 4 - 3 + (4 * (k : ℤ) + 8)) := by
    unfold TwosSlipZ0
    omega
  have hs := twosSlip_eq_two_of k hK h2 h0
  linarith

/-- The slip at `(a, a-2)` is `0`: it lies in the lower band. -/
theorem twosSlip_a_a2_zero (k : ℕ) :
    twosSlip k (2 * (k : ℤ) + 4, 2 * (k : ℤ) + 4 - 2) = 0 := by
  have hK : TwosKey (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 4 - 2) := by
    unfold TwosKey
    omega
  exact twosSlip_eq_zero_of k hK (by unfold TwosSlipZ0; omega) (by unfold TwosSlipZ2; omega)

/-- The sign `-1` potential of `(a+1, a-1)` equals that of `(a+1, a-2)` (the free H site `H3`): both levels are `C - 2 - 1`. -/
theorem H3_phi_eq (k : ℕ) :
    twosPhi k (-1) (2 * (k : ℤ) + 4 + 1, 2 * (k : ℤ) + 4 - 1) = twosPhi k (-1) (2 * (k : ℤ) + 4 + 1, 2 * (k : ℤ) + 4 - 2) := by
  unfold twosPhi
  have hN1 : NativeT (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 4 + 1) (2 * (k : ℤ) + 4 - 1) := by
    unfold NativeT
    omega
  have hN2 : NativeT (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 4 + 1) (2 * (k : ℤ) + 4 - 2) := by
    unfold NativeT
    omega
  rw [chainM_native_level k hN1 (by omega), chainM_native_level k hN2 (by omega)]
  have d1 : TwosDelta k (2 * (k : ℤ) + 4 + 1 - 1) (2 * (k : ℤ) + 4 - 1 - 1) := by
    unfold TwosDelta
    omega
  have d2 : TwosDelta k (2 * (k : ℤ) + 4 + 1 - 1) (2 * (k : ℤ) + 4 - 2 - 1) := by
    unfold TwosDelta
    omega
  rw [if_pos d1, if_pos d2]
  have s1 : twosSlip k (2 * (k : ℤ) + 4 + 1 - 1, 2 * (k : ℤ) + 4 - 1 - 1) = 0 := by
    rw [show (2 * (k : ℤ) + 4 + 1 - 1 : ℤ) = 2 * (k : ℤ) + 4 by ring,
      show (2 * (k : ℤ) + 4 - 1 - 1 : ℤ) = 2 * (k : ℤ) + 4 - 2 by ring]
    exact twosSlip_a_a2_zero k
  have s2 : twosSlip k (2 * (k : ℤ) + 4 + 1 - 1, 2 * (k : ℤ) + 4 - 2 - 1) = 0 := by
    rw [show (2 * (k : ℤ) + 4 + 1 - 1 : ℤ) = 2 * (k : ℤ) + 4 by ring,
      show (2 * (k : ℤ) + 4 - 2 - 1 : ℤ) = 2 * (k : ℤ) + 4 - 3 by ring]
    exact twosSlip_a_a3_zero k
  rw [s1, s2]

/-- The sign `-1` rank of the free H site `H3 = (a+1, a-2)` is `6`. -/
theorem rank_H3_minus {a : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) : rhoTwos a (-1) (a + 1, a - 2) = 6 := by
  have hp : TwosTile a (a + 1, a - 2) := free_tile (Or.inl (Or.inr (Or.inr ⟨rfl, rfl⟩))) (by unfold NativeT; omega)
  rw [rhoTwos_tile_freeH_eta (-1) ha he2 hp (Or.inr (Or.inr ⟨rfl, rfl⟩))]
  have hη : ((-1 : ℤ) = 1) = False := by norm_num
  simp only [freeH, hη, if_false]
  split_ifs <;> omega

/-- The point `(a+1, a-1)` is the `U`-translate of the free V site `(0, 0)`, so its sign `-1` rank is `5`. -/
theorem rank_target_minus {a : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) : rhoTwos a (-1) (a + 1, a - 1) = 5 := by
  have hU := rhoTwos_add_U_eta (-1) a 0 0
  simp only [zero_add] at hU
  rw [hU]
  have hp : TwosTile a (0, 0) := free_tile (Or.inr (Or.inl ⟨rfl, by omega, by omega⟩)) (by unfold NativeT; omega)
  rw [rhoTwos_tile_freeV_eta (-1) ha he2 hp (by unfold FreeHSite; omega) (Or.inl ⟨rfl, by omega, by omega⟩),
    freeV_minus_eq]
  simp

/-- The free H site `H3 = (a+1, a-2)` for sign `-1`: its selected target `(a+1, a-1)` has rank `5`, below `6`. -/
theorem free_H3_minus {a : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) :
    rhoTwos a (-1) (a + 1, a - 1) < rhoTwos a (-1) (a + 1, a - 2) := by
  rw [rank_target_minus ha he2, rank_H3_minus ha he2]
  norm_num

/-- The sign `-1` rank of the target `(-2, y)` of the free V site `(-1, y)` (`y` odd, `a+1 ≤ y ≤ 2a-1`): it is the rank of
`(a-1, y+a-1)`, the `U` translate. -/
theorem rank_V1_target (a y : ℤ) :
    rhoTwos a (-1) (-2, y) = rhoTwos a (-1) (a - 1, y + a - 1) := by
  have hU := rhoTwos_add_U_eta (-1) a (-2) y
  rw [show (-2 : ℤ) + (a + 1) = a - 1 by ring, show y + (a - 1) = y + a - 1 by ring] at hU
  exact hU.symm

/-- The free V site `(-1, y)` for sign `-1`, `y` odd: its selected target `(-2, y)` has rank below its own. -/
theorem free_V1_odd_minus {a y : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hy1 : a + 1 ≤ y) (hy2 : y ≤ 2 * a - 1)
    (hodd : y % 2 = 1) :
    rhoTwos a (-1) (-2, y) < rhoTwos a (-1) (-1, y) := by
  rw [rank_V1_target a y]
  have hp : TwosTile a (-1, y) := free_tile (Or.inr (Or.inr ⟨rfl, by omega, by omega⟩)) (by unfold NativeT; omega)
  rw [rhoTwos_tile_freeV_eta (-1) ha he2 hp (by unfold FreeHSite; omega) (Or.inr ⟨rfl, by omega, by omega⟩),
    freeV_minus_eq]
  by_cases h1 : y = a + 1
  · -- the first odd row: the target is the bulk point (a-1, 2a) of rank 0
    subst h1
    have hq : TwosTile a (a - 1, 2 * a) :=
      tile_pt (by unfold NativeT; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
        (by unfold FreeSite FreeHSite FreeVSite; omega)
    rw [show a + 1 + a - 1 = 2 * a by ring]
    rw [rho_bulk_eq_m ha he2 hq (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega)]
    unfold bulkTreeM
    split_ifs <;> omega
  by_cases h2 : y = 2 * a - 1
  · -- the last odd row: the target is the V translate of the free H site H3 = (a+1, a-2), of rank 6
    subst h2
    have hV := rhoTwos_add_V_eta (-1) a (a + 1) (a - 2)
    rw [show (a + 1 : ℤ) + (-2) = a - 1 by ring, show (a - 2 : ℤ) + 2 * a = 3 * a - 2 by ring] at hV
    rw [show 2 * a - 1 + a - 1 = 3 * a - 2 by ring, hV, rank_H3_minus ha he2]
    split_ifs <;> omega
  · -- the middle odd rows: the target is the bulk point (a-1, y+a-1) of rank 2a+4-2r
    have hq : TwosTile a (a - 1, y + a - 1) :=
      tile_pt (by unfold NativeT; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
        (by unfold FreeSite FreeHSite FreeVSite; omega)
    rw [rho_bulk_eq_m ha he2 hq (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega)]
    unfold bulkTreeM
    split_ifs <;> omega

/-- The left Low family: at `x` with `3 ≤ x ≤ a-1`, the sign `-1` potential of `(x, a+1)` is one less than that of `(x, a)`. -/
theorem phi_low_up_family (k : ℕ) {x : ℤ} (hx3 : 3 ≤ x) (hx : x ≤ 2 * (k : ℤ) + 4 - 1) :
    twosPhi k (-1) (x, 2 * (k : ℤ) + 4 + 1) = twosPhi k (-1) (x, 2 * (k : ℤ) + 4) - 1 := by
  unfold twosPhi
  have hN1 : NativeT (2 * (k : ℤ) + 4) x (2 * (k : ℤ) + 4) := by
    unfold NativeT
    omega
  have hN2 : NativeT (2 * (k : ℤ) + 4) x (2 * (k : ℤ) + 4 + 1) := by
    unfold NativeT
    omega
  rw [chainM_native_level k hN2 (by omega), chainM_native_level k hN1 (by omega)]
  have dT : TwosDelta k (x - 1) (2 * (k : ℤ) + 4 + 1 - 1) := by
    unfold TwosDelta
    omega
  have dU : ¬ TwosDelta k (x - 1) (2 * (k : ℤ) + 4 - 1) := by
    unfold TwosDelta
    omega
  have sT : twosSlip k (x - 1, 2 * (k : ℤ) + 4 + 1 - 1) = 1 :=
    twosSlip_eq_one_of k (by unfold TwosKey; omega) (by unfold TwosSlipZ0; omega) (by unfold TwosSlipZ2; omega)
  have sU : twosSlip k (x - 1, 2 * (k : ℤ) + 4 - 1) = 1 :=
    twosSlip_eq_one_of k (by unfold TwosKey; omega) (by unfold TwosSlipZ0; omega) (by unfold TwosSlipZ2; omega)
  rw [if_pos dT, if_neg dU, sT, sU]
  ring

/-- The right High family: at `x` with `1 ≤ x ≤ a-1`, the sign `-1` potential of `(x, 2a+1)` is one less than that of `(x, 2a)`. -/
theorem phi_high_up_family (k : ℕ) {x : ℤ} (hx1 : 1 ≤ x) (hx : x ≤ 2 * (k : ℤ) + 4 - 1) :
    twosPhi k (-1) (x, 2 * (2 * (k : ℤ) + 4) + 1) = twosPhi k (-1) (x, 2 * (2 * (k : ℤ) + 4)) - 1 := by
  unfold twosPhi
  have hN1 : NativeT (2 * (k : ℤ) + 4) x (2 * (2 * (k : ℤ) + 4)) := by
    unfold NativeT
    omega
  have hN2 : NativeT (2 * (k : ℤ) + 4) x (2 * (2 * (k : ℤ) + 4) + 1) := by
    unfold NativeT
    omega
  rw [chainM_native_level k hN2 (by omega), chainM_native_level k hN1 (by omega)]
  have dT : TwosDelta k (x - 1) (2 * (2 * (k : ℤ) + 4) + 1 - 1) := by
    unfold TwosDelta
    omega
  have dU : ¬ TwosDelta k (x - 1) (2 * (2 * (k : ℤ) + 4) - 1) := by
    unfold TwosDelta
    omega
  have sT : twosSlip k (x - 1, 2 * (2 * (k : ℤ) + 4) + 1 - 1) = 2 :=
    twosSlip_eq_two_of k (by unfold TwosKey; omega) (by unfold TwosSlipZ2; omega) (by unfold TwosSlipZ0; omega)
  have sU : twosSlip k (x - 1, 2 * (2 * (k : ℤ) + 4) - 1) = 2 :=
    twosSlip_eq_two_of k (by unfold TwosKey; omega) (by unfold TwosSlipZ2; omega) (by unfold TwosSlipZ0; omega)
  rw [if_pos dT, if_neg dU, sT, sU]
  ring

/-- The free V site `(-1, y)` with `y` even, `a+2 ≤ y ≤ 2a-2` (the odd white V sites that are tiles): its target `(-1, y+1)` has rank one less. -/
theorem free_V1_even_row_minus {a y : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hy1 : a + 2 ≤ y) (hy2 : y ≤ 2 * a - 2)
    (hye : y % 2 = 0) :
    rhoTwos a (-1) (-1, y + 1) < rhoTwos a (-1) (-1, y) := by
  have hq : TwosTile a (-1, y + 1) :=
    free_tile (Or.inr (Or.inr ⟨rfl, by omega, by omega⟩)) (by unfold NativeT; omega)
  have hp : TwosTile a (-1, y) :=
    free_tile (Or.inr (Or.inr ⟨rfl, by omega, by omega⟩)) (by unfold NativeT; omega)
  rw [rhoTwos_tile_freeV_eta (-1) ha he2 hq (by unfold FreeHSite; omega) (Or.inr ⟨rfl, by omega, by omega⟩),
    rhoTwos_tile_freeV_eta (-1) ha he2 hp (by unfold FreeHSite; omega) (Or.inr ⟨rfl, by omega, by omega⟩),
    freeV_minus_eq, freeV_minus_eq]
  split_ifs <;> omega

/-- The Low band, down step: `y < a-1`, the target `(x, y-1)` has rank one less (sign `-1`). -/
theorem candLow_down_minus {a x y : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hp : TwosTile a (x, y))
    (hpF : ¬ FreeSite a x y) (hL : CandLow a x y) (hm : y < a - 1) (hyx : 1 ≤ y - x) :
    rhoTwos a (-1) (x, y + -1) < rhoTwos a (-1) (x, y) := by
  have hL' := hL
  unfold CandLow at hL'
  have hT : TwosTile a (x, y + -1) :=
    tile_pt (by unfold NativeT; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
      (by unfold FreeSite FreeHSite FreeVSite; omega)
  have hTF : ¬ FreeSite a x (y + -1) := by
    unfold FreeSite FreeHSite FreeVSite
    omega
  rw [rho_bulk_eq_m ha he2 hT hTF (by omega), rho_bulk_eq_m ha he2 hp hpF (by omega)]
  unfold bulkTreeM
  split_ifs <;> omega

/-- The Low band, up step from `y ≥ a+1`: the target `(x, y+1)` has rank one less (sign `-1`). -/
theorem candLow_up_gen_minus {a x y : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hp : TwosTile a (x, y))
    (hpF : ¬ FreeSite a x y) (hL : CandLow a x y) (hm : a + 1 ≤ y) :
    rhoTwos a (-1) (x, y + 1) < rhoTwos a (-1) (x, y) := by
  have hL' := hL
  unfold CandLow at hL'
  have hT : TwosTile a (x, y + 1) :=
    tile_pt (by unfold NativeT; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
      (by unfold FreeSite FreeHSite FreeVSite; omega)
  have hTF : ¬ FreeSite a x (y + 1) := by
    unfold FreeSite FreeHSite FreeVSite
    omega
  rw [rho_bulk_eq_m ha he2 hT hTF (by omega), rho_bulk_eq_m ha he2 hp hpF (by omega)]
  unfold bulkTreeM
  split_ifs <;> omega

/-- The High band, down step: `y < 2a-1`, the target `(x, y-1)` has rank one less (sign `-1`). -/
theorem candHigh_down_minus {a x y : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hp : TwosTile a (x, y))
    (hpF : ¬ FreeSite a x y) (hH : CandHigh a x y) (hm : y < 2 * a - 1) :
    rhoTwos a (-1) (x, y - 1) < rhoTwos a (-1) (x, y) := by
  have hH' := hH
  unfold CandHigh at hH'
  have hT : TwosTile a (x, y - 1) :=
    tile_pt (by unfold NativeT; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
      (by unfold FreeSite FreeHSite FreeVSite; omega)
  have hTF : ¬ FreeSite a x (y - 1) := by
    unfold FreeSite FreeHSite FreeVSite
    omega
  rw [rho_bulk_eq_m ha he2 hT hTF (by omega), rho_bulk_eq_m ha he2 hp hpF (by omega)]
  unfold bulkTreeM
  split_ifs <;> omega

/-- The High band, up step from `y ≥ 2a+1`: the target `(x, y+1)` has rank one less (sign `-1`). -/
theorem candHigh_up_gen_minus {a x y : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hp : TwosTile a (x, y))
    (hpF : ¬ FreeSite a x y) (hH : CandHigh a x y) (hm : 2 * a + 1 ≤ y) (hyx : y - x ≤ 2 * a - 2) :
    rhoTwos a (-1) (x, y + 1) < rhoTwos a (-1) (x, y) := by
  have hH' := hH
  unfold CandHigh at hH'
  have hT : TwosTile a (x, y + 1) :=
    tile_pt (by unfold NativeT; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
      (by unfold FreeSite FreeHSite FreeVSite; omega)
  have hTF : ¬ FreeSite a x (y + 1) := by
    unfold FreeSite FreeHSite FreeVSite
    omega
  rw [rho_bulk_eq_m ha he2 hT hTF (by omega), rho_bulk_eq_m ha he2 hp hpF (by omega)]
  unfold bulkTreeM
  split_ifs <;> omega

/-- The Low band at the row `y = a` (the potential family): the flatness hypothesis is false there. -/
theorem candLow_row_a_vacuous {a x : ℤ} {k : ℕ} (hk : a = 2 * (k : ℤ) + 4) (hL : CandLow a x a)
    (hΦ : twosPhi k (-1) (x, a + 1) = twosPhi k (-1) (x, a)) : False := by
  have hL' := hL
  unfold CandLow at hL'
  have e := phi_low_up_family k (x := x) (by omega) (by omega)
  rw [← hk] at e
  omega

/-- The High band at the row `y = 2a` (the potential family): the flatness hypothesis is false there. -/
theorem candHigh_row_2a_vacuous {a x : ℤ} {k : ℕ} (hk : a = 2 * (k : ℤ) + 4) (hH : CandHigh a x (2 * a))
    (hΦ : twosPhi k (-1) (x, 2 * a + 1) = twosPhi k (-1) (x, 2 * a)) : False := by
  have hH' := hH
  unfold CandHigh at hH'
  have e := phi_high_up_family k (x := x) (by omega) (by omega)
  rw [← hk] at e
  omega

/-- The Low band, down step to the free H2 site, at `y = x - 1` with `2 ≤ x ≤ a`: the target `(x, x-2)` has rank
`2a+7-2x` (or `1` at `x = 2`), below the rank `2a+8-2x` of `(x, x-1)`. -/
theorem candLow_down_m1 {a x y : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hp : TwosTile a (x, y))
    (hpF : ¬ FreeSite a x y) (hx2 : 2 ≤ x) (hxa : x ≤ a) (hy : y = x - 1) :
    rhoTwos a (-1) (x, y + -1) < rhoTwos a (-1) (x, y) := by
  have hT : TwosTile a (x, y + -1) :=
    free_tile (Or.inl (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))) (by unfold NativeT; omega)
  rw [rhoTwos_tile_freeH_eta (-1) ha he2 hT (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)),
    rho_bulk_eq_m ha he2 hp hpF (by omega)]
  have hη : ((-1 : ℤ) = 1) = False := by norm_num
  simp only [freeH, hη, if_false]
  unfold bulkTreeM
  split_ifs <;> omega

/-- The High band, up step along the edge `y - x = 2a-1` with `2 ≤ x ≤ a-2`: the target `(x, x+2a)` is the `V` translate of the
free H2 site `(x+2, x)`, of rank `2a+3-2x`, below the rank `2a+4-2x` of `(x, x+2a-1)`. -/
theorem candHigh_up_m1 {a x y : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hp : TwosTile a (x, y))
    (hpF : ¬ FreeSite a x y) (hx2 : 2 ≤ x) (hxa : x ≤ a - 2) (hy : y = x + 2 * a - 1) :
    rhoTwos a (-1) (x, y + 1) < rhoTwos a (-1) (x, y) := by
  have hV := rhoTwos_add_V_eta (-1) a (x + 2) x
  rw [show x + 2 + (-2 : ℤ) = x by ring, show x + 2 * a = y + 1 by omega] at hV
  have hT : TwosTile a (x + 2, x) :=
    free_tile (Or.inl (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))) (by unfold NativeT; omega)
  rw [hV, rhoTwos_tile_freeH_eta (-1) ha he2 hT (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)),
    rho_bulk_eq_m ha he2 hp hpF (by omega)]
  have hη : ((-1 : ℤ) = 1) = False := by norm_num
  simp only [freeH, hη, if_false]
  subst hy
  unfold bulkTreeM
  split_ifs <;> omega

/-- The odd white candidate centre `(x, y)` of sign `-1`: the rank of its candidate target drops, when the potentials agree.
The Low and High bands; the E and W diagonals have even parity and do not occur for an odd centre. -/
theorem candidate_flat_drop_odd_minus {a x y : ℤ} {k : ℕ} (hk : a = 2 * (k : ℤ) + 4) (hp : TwosTile a (x, y))
    (hpF : ¬ FreeSite a x y) (hodd : (x + y) % 2 = 1) (hG : CandGuard a x y)
    (hΦ : twosPhi k (-1) (x + (candDisp a x y).1, y + (candDisp a x y).2) = twosPhi k (-1) (x, y)) :
    rhoTwos a (-1) (x + (candDisp a x y).1, y + (candDisp a x y).2) < rhoTwos a (-1) (x, y) := by
  have ha : (4 : ℤ) ≤ a := by omega
  have he2 : a % 2 = 0 := by omega
  rcases hG with hL | hH | hE | hW
  · -- the Low band
    have hL' := hL
    unfold CandLow at hL'
    by_cases hd : y < a - 1
    · rw [candDisp_low_down hL hd] at hΦ ⊢
      dsimp only at hΦ ⊢
      rw [add_zero]
      by_cases h1 : y - x = -1
      · exact candLow_down_m1 ha he2 hp hpF (by omega) (by omega) (by omega)
      · exact candLow_down_minus ha he2 hp hpF hL hd (by omega)
    · rw [candDisp_low_up hL hd] at hΦ ⊢
      dsimp only at hΦ ⊢
      rw [add_zero] at hΦ ⊢
      by_cases hy : y = a
      · subst hy
        exact (candLow_row_a_vacuous hk hL hΦ).elim
      · exact candLow_up_gen_minus ha he2 hp hpF hL (by omega)
  · -- the High band
    have hH' := hH
    unfold CandHigh at hH'
    by_cases hd : y < 2 * a - 1
    · rw [candDisp_high_down hH hd] at hΦ ⊢
      dsimp only at hΦ ⊢
      rw [add_zero]
      exact candHigh_down_minus ha he2 hp hpF hH hd
    · rw [candDisp_high_up hH hd] at hΦ ⊢
      dsimp only at hΦ ⊢
      rw [add_zero] at hΦ ⊢
      by_cases hy : y = 2 * a
      · subst hy
        exact (candHigh_row_2a_vacuous hk hH hΦ).elim
      · by_cases hy2 : y - x = 2 * a - 1
        · exact candHigh_up_m1 ha he2 hp hpF (by omega) (by omega) (by omega)
        · exact candHigh_up_gen_minus ha he2 hp hpF hH (by omega) (by omega)
  · -- the E diagonal has even parity
    exfalso
    unfold CandE at hE
    omega
  · -- the W diagonal has even parity
    exfalso
    unfold CandW at hW
    omega

/-- The candidate selection for any sign: a non-free white tile centre with a selected input is a candidate, with the
displacement of its native copy. -/
theorem twosSel_cand_tile_eta {a : ℤ} {k : ℕ} (hk : a = 2 * (k : ℤ) + 4) {F : Field} {η p1 p2 i1 i2 : ℤ}
    (hp : TwosTile a (p1, p2)) (hpF : ¬ FreeSite a p1 p2) (hpS : ¬ (p1 = a ∧ p2 = 2 * a - 1))
    (hl : laplacian F (p1, p2) = 0) (h : TwosSel a η F (p1, p2) (i1, i2)) :
    CandGuard a p1 p2 ∧ (i1, i2) = (p1 + (candDisp a p1 p2).1, p2 + (candDisp a p1 p2).2) := by
  have ha : (4 : ℤ) ≤ a := by omega
  have he2 : a % 2 = 0 := by omega
  rcases h with ⟨hm, -⟩ | ⟨-, h2 | ⟨hnfc, ⟨⟨u1, u2⟩, hu, hN, hG, hi⟩⟩⟩
  · rw [hl] at hm
    norm_num at hm
  · obtain ⟨⟨u1, u2⟩, hu, huF, -⟩ := h2
    exact absurd huF (fun hf => nonfree_no_free_alias ha he2 hp hpF hpS hu hf)
  · obtain ⟨e1, e2⟩ := cand_native_alias ha he2 hp hpF hu hN
    subst e1
    subst e2
    exact ⟨hG, hi⟩

/-- The sign `-1` free displacement at the H site `(1, 0)` is `(0, 1)`. -/
theorem freeDisp_minus_H1 {a : ℤ} (ha : 4 ≤ a) : freeDisp a (-1) 1 0 = (0, 1) := by
  unfold freeDisp
  rw [if_pos (show FreeHSite a 1 0 by unfold FreeHSite; omega), if_pos (show (1 : ℤ) = 1 ∧ (0 : ℤ) = 0 by omega)]
  norm_num

/-- The sign `-1` free displacement at the H site `(a+1, a-2)` is `(0, 1)`. -/
theorem freeDisp_minus_H3 {a : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) : freeDisp a (-1) (a + 1) (a - 2) = (0, 1) := by
  unfold freeDisp
  rw [if_pos (show FreeHSite a (a + 1) (a - 2) by unfold FreeHSite; omega),
    if_neg (show ¬ ((a + 1 = 1) ∧ (a - 2 = 0)) by omega),
    if_neg (show ¬ EvenSite (a + 1, a - 2) by unfold EvenSite; dsimp only; omega)]

/-- The sign `-1` free displacement at the V site `(0, y)` with `y` odd is `(0, 1)`. -/
theorem freeDisp_minus_V0 {a y : ℤ} (ha : 4 ≤ a) (hy : y % 2 = 1) : freeDisp a (-1) 0 y = (0, 1) := by
  unfold freeDisp
  rw [if_neg (show ¬ FreeHSite a 0 y by unfold FreeHSite; omega), if_neg (show ¬ ((0 : ℤ) = 0 ∧ y = 0) by omega),
    if_neg (show ¬ EvenSite (0, y) by unfold EvenSite; dsimp only; omega)]
  all_goals norm_num

/-- The sign `-1` free displacement at the V site `(-1, y)` with `y` even is `(0, 1)`. -/
theorem freeDisp_minus_Vm1 {a y : ℤ} (ha : 4 ≤ a) (hy : y % 2 = 0) : freeDisp a (-1) (-1) y = (0, 1) := by
  unfold freeDisp
  rw [if_neg (show ¬ FreeHSite a (-1) y by unfold FreeHSite; omega), if_neg (show ¬ ((-1 : ℤ) = 0 ∧ y = 0) by omega),
    if_neg (show ¬ EvenSite (-1, y) by unfold EvenSite; dsimp only; omega)]
  all_goals norm_num

/-- The odd white centres of sign `-1`: a tile centre `p` of odd parity whose selected input `i` has rank below `p` when
the potentials agree. -/
theorem hTile_minus_odd_white (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    {p1 p2 i1 i2 : ℤ} (hp : TwosTile (2 * (k : ℤ) + 4) (p1, p2)) (hpar : (p1 + p2) % 2 = 1)
    (hB : ¬ LadderOddEvenBlack (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - p2, p1 + 1))
    (hsel : TwosSel (2 * (k : ℤ) + 4) (-1) (standardField (List.replicate (k + 1) Digit.two)) (p1, p2) (i1, i2))
    (hΦ : twosPhi k (-1) (i1, i2) = twosPhi k (-1) (p1, p2)) :
    rhoTwos (2 * (k : ℤ) + 4) (-1) (i1, i2) < rhoTwos (2 * (k : ℤ) + 4) (-1) (p1, p2) := by
  have hk : (2 * (k : ℤ) + 4) = 2 * (k : ℤ) + 4 := rfl
  have ha : (4 : ℤ) ≤ 2 * (k : ℤ) + 4 := by omega
  have he2 : (2 * (k : ℤ) + 4) % 2 = 0 := by omega
  have hN : NativeT (2 * (k : ℤ) + 4) p1 p2 := ((tile_iff_lin _ _ _).mp hp).1
  have hl : laplacian (standardField (List.replicate (k + 1) Digit.two)) (p1, p2) = 0 :=
    lap_odd_value k hagree hperiod hN hpar hB
  by_cases hsp : p1 = 2 * (k : ℤ) + 4 ∧ p2 = 2 * (2 * (k : ℤ) + 4) - 1
  · obtain ⟨hs1, hs2⟩ := hsp
    rw [hs1, hs2] at hsel hΦ hl ⊢
    have hlz := twosSel_special_minus k hl ha hsel
    obtain ⟨e1, e2⟩ := Prod.mk.inj hlz
    rw [e1, e2]
    exact special_minus_rho_drop ha he2
  · by_cases hf : FreeSite (2 * (k : ℤ) + 4) p1 p2
    · have hd := (twosSel_free_self (η := -1) ha he2 hl hp hf).mp hsel
      unfold FreeSite FreeHSite FreeVSite at hf
      rcases hf with (H1 | H2 | H3) | (V1 | V2)
      · obtain ⟨h1, h2⟩ := H1
        subst h1
        subst h2
        rw [hd, freeDisp_minus_H1 ha]
        simp only [add_zero]
        exact free_H1_minus ha he2
      · exfalso
        obtain ⟨h1, h2, h3⟩ := H2
        omega
      · obtain ⟨h1, h2⟩ := H3
        subst h1
        subst h2
        rw [hd, freeDisp_minus_H3 ha he2]
        simp only [add_zero]
        rw [show (2 * (k : ℤ) + 4 - 2 + 1 : ℤ) = 2 * (k : ℤ) + 4 - 1 by ring]
        exact free_H3_minus ha he2
      · obtain ⟨h1, h2, h3⟩ := V1
        subst h1
        rw [hd, freeDisp_minus_V0 ha (by omega)]
        simp only [add_zero]
        exact free_V0_odd_minus ha he2 (by omega) (by omega) (by omega)
      · obtain ⟨h1, h2, h3⟩ := V2
        subst h1
        unfold NativeT at hN
        have hpe : p2 % 2 = 0 := by omega
        rw [hd, freeDisp_minus_Vm1 ha hpe]
        simp only [add_zero]
        exact free_V1_even_row_minus ha he2 (by omega) (by omega) hpe
    · obtain ⟨hG, hd⟩ := twosSel_cand_tile_eta hk hp hf hsp hl hsel
      rw [hd] at hΦ ⊢
      exact candidate_flat_drop_odd_minus hk hp hf hpar hG hΦ

end FLatticePaper.TwosEPolicy
