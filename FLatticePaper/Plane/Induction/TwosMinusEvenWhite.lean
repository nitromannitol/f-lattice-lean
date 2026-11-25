import FLatticePaper.Plane.Induction.TwosMinusOddWhite
import FLatticePaper.Plane.Induction.TwosFreeAssembly

/-! Twos flatness, sign `-1`, the even white centres. The even white centres are the points of `EvenWhitePiece`. The
selected inputs are the free displacements of the free even sites (the H sites `(x, x-2)`, the V sites `(0, y)` with `y`
even, and the V sites `(-1, y)` with `y` odd) and the candidate displacements of the diagonals `y - x = a-2` and `y - x = a`.
Every rank drops, with no potential argument. -/

noncomputable section

namespace FLatticePaper.TwosEPolicy

open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey
open scoped Classical

/-- The sign `-1` rank of a free H site `(x, x-2)` with `3 ≤ x ≤ a-1`. -/
theorem freeH_minus_mid {a x : ℤ} (hx3 : 3 ≤ x) (hxa : x ≤ a - 1) :
    freeH a (-1) x (x - 2) = 2 * a + 7 - 2 * x := by
  have hη : ((-1 : ℤ) = 1) = False := by norm_num
  simp only [freeH, hη, if_false]
  split_ifs <;> omega

/-- The sign `-1` free displacement at the even H site `(x, x-2)` with `2 ≤ x ≤ a` is `(1, 0)`. -/
theorem freeDisp_minus_H2 {a x : ℤ} (hx2 : 2 ≤ x) (hxa : x ≤ a) :
    freeDisp a (-1) x (x - 2) = (1, 0) := by
  unfold freeDisp
  rw [if_pos (show FreeHSite a x (x - 2) by unfold FreeHSite; omega),
    if_neg (show ¬ (x = 1 ∧ x - 2 = 0) by omega),
    if_pos (show EvenSite (x, x - 2) by unfold EvenSite; dsimp only; omega)]

/-- The sign `-1` free displacement at the V site `(0, y)` with `y` even, `2 ≤ y`, is `(-1, 0)`. -/
theorem freeDisp_minus_V0_even {a y : ℤ} (ha : 4 ≤ a) (hy : y % 2 = 0) (hy1 : 2 ≤ y) :
    freeDisp a (-1) 0 y = (-1, 0) := by
  unfold freeDisp
  rw [if_neg (show ¬ FreeHSite a 0 y by unfold FreeHSite; omega),
    if_neg (show ¬ ((0 : ℤ) = 0 ∧ y = 0) by omega),
    if_pos (show EvenSite (0, y) by unfold EvenSite; dsimp only; omega)]

/-- The sign `-1` free displacement at the V site `(0, 0)` is `(1, 0)`. -/
theorem freeDisp_minus_V00 {a : ℤ} (ha : 4 ≤ a) : freeDisp a (-1) 0 0 = (1, 0) := by
  unfold freeDisp
  rw [if_neg (show ¬ FreeHSite a 0 0 by unfold FreeHSite; omega),
    if_pos (show (0 : ℤ) = 0 ∧ (0 : ℤ) = 0 from ⟨rfl, rfl⟩)]

/-- The sign `-1` free displacement at the V site `(-1, y)` with `y` odd is `(-1, 0)`. -/
theorem freeDisp_minus_Vm1_odd {a y : ℤ} (ha : 4 ≤ a) (hy : y % 2 = 1) :
    freeDisp a (-1) (-1) y = (-1, 0) := by
  unfold freeDisp
  rw [if_neg (show ¬ FreeHSite a (-1) y by unfold FreeHSite; omega),
    if_neg (show ¬ ((-1 : ℤ) = 0 ∧ y = 0) by omega),
    if_pos (show EvenSite (-1, y) by unfold EvenSite; dsimp only; omega)]

/-- The candidate displacement on the east diagonal `y - x = a-2` is `(1, 0)`. -/
theorem candDisp_E_minus {a x y : ℤ} (hy : y - x = a - 2) (hx2 : 2 ≤ x) (hxa : x ≤ a) :
    candDisp a x y = (1, 0) := by
  unfold candDisp
  rw [if_pos (show CandE a x y by unfold CandE; omega),
    if_neg (show ¬ (CandLow a x y ∨ CandHigh a x y) by unfold CandLow CandHigh; omega)]

/-- The candidate displacement on the west diagonal `y - x = a` is `(-1, 0)`. -/
theorem candDisp_W_minus {a x y : ℤ} (hy : y - x = a) (h0 : 0 ≤ x) (hxa : x ≤ a - 2) :
    candDisp a x y = (-1, 0) := by
  unfold candDisp
  rw [if_neg (show ¬ CandE a x y by unfold CandE; omega),
    if_pos (show CandW a x y by unfold CandW; omega),
    if_neg (show ¬ (CandLow a x y ∨ CandHigh a x y) by unfold CandLow CandHigh; omega)]

/-- The H site `(2, 0)` (rank `1`) has the target `(3, 0)`, of rank `0`, the `V` translate of `(1, 2a)`. -/
theorem even_H2_two_minus {a : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hp : TwosTile a (2, 0)) :
    rhoTwos a (-1) (3, 0) < rhoTwos a (-1) (2, 0) := by
  have hV := rhoTwos_add_V_eta (-1) a 3 0
  rw [show (3 : ℤ) + (-2) = 1 by ring, show (0 : ℤ) + 2 * a = 2 * a by ring] at hV
  rw [← hV]
  have hF : FreeHSite a 2 0 := Or.inr (Or.inl ⟨le_refl _, by omega, by omega⟩)
  rw [rhoTwos_tile_freeH_eta (-1) ha he2 hp hF, freeH_minus_two ha]
  have hq : TwosTile a (1, 2 * a) :=
    tile_pt (by unfold NativeT; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
      (by unfold FreeSite FreeHSite FreeVSite; omega)
  rw [rho_bulk_eq_m ha he2 hq (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega)]
  unfold bulkTreeM
  split_ifs <;> omega

/-- The H site `(x, x-2)` with `3 ≤ x ≤ a-1` has the target `(x+1, x-2)`, the `V` translate of `(x-1, x+2a-2)`, one less. -/
theorem even_H2_mid_minus {a x : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hx3 : 3 ≤ x) (hxa : x ≤ a - 1)
    (hp : TwosTile a (x, x - 2)) :
    rhoTwos a (-1) (x + 1, x - 2) < rhoTwos a (-1) (x, x - 2) := by
  have hV := rhoTwos_add_V_eta (-1) a (x + 1) (x - 2)
  rw [show x + 1 + (-2 : ℤ) = x - 1 by ring, show x - 2 + 2 * a = x + 2 * a - 2 by ring] at hV
  rw [← hV]
  have hF : FreeHSite a x (x - 2) := Or.inr (Or.inl ⟨by omega, by omega, rfl⟩)
  rw [rhoTwos_tile_freeH_eta (-1) ha he2 hp hF, freeH_minus_mid hx3 hxa]
  have hq : TwosTile a (x - 1, x + 2 * a - 2) :=
    tile_pt (by unfold NativeT; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
      (by unfold FreeSite FreeHSite FreeVSite; omega)
  rw [rho_bulk_eq_m ha he2 hq (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega)]
  unfold bulkTreeM
  split_ifs <;> omega

/-- The H site `(a, a-2)` (rank `7`) has the target `(a+1, a-2)`, the free H3 site of rank `6`. -/
theorem even_H2_last_minus {a : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hp : TwosTile a (a, a - 2)) :
    rhoTwos a (-1) (a + 1, a - 2) < rhoTwos a (-1) (a, a - 2) := by
  have hF : FreeHSite a a (a - 2) := Or.inr (Or.inl ⟨by omega, le_refl _, rfl⟩)
  rw [rhoTwos_tile_freeH_eta (-1) ha he2 hp hF, freeH_minus_last ha, rank_H3_minus ha he2]
  norm_num

/-- The free V site `(0, 0)` (rank `5`) has the target `(1, 0)`, the free H site of rank `4`. -/
theorem even_V0_zero_minus {a : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hp : TwosTile a (0, 0)) :
    rhoTwos a (-1) (1, 0) < rhoTwos a (-1) (0, 0) := by
  have hq : TwosTile a (1, 0) := free_tile (Or.inl (Or.inl ⟨rfl, rfl⟩)) (by unfold NativeT; omega)
  rw [rhoTwos_tile_freeH_eta (-1) ha he2 hq (Or.inl ⟨rfl, rfl⟩), freeH_minus_one_zero,
    rhoTwos_tile_freeV_eta (-1) ha he2 hp (by unfold FreeHSite; omega) (Or.inl ⟨rfl, by omega, by omega⟩),
    freeV_minus_eq]
  norm_num

/-- The free V site `(0, y)` with `y` even, `2 ≤ y ≤ a-2`: its target `(-1, y)` is the `U` translate of `(a, y+a-1)`, of
rank `2a+2-2y`, below the rank `2a+3-2y` of `(0, y)`. -/
theorem even_V0_mid_minus {a y : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hy2 : 2 ≤ y) (hya : y ≤ a - 2)
    (hye : y % 2 = 0) (hp : TwosTile a (0, y)) :
    rhoTwos a (-1) (-1, y) < rhoTwos a (-1) (0, y) := by
  have hU := rhoTwos_add_U_eta (-1) a (-1) y
  rw [show (-1 : ℤ) + (a + 1) = a by ring, show y + (a - 1) = y + a - 1 by ring] at hU
  rw [← hU]
  have hF : FreeVSite a 0 y := Or.inl ⟨rfl, by omega, by omega⟩
  rw [rhoTwos_tile_freeV_eta (-1) ha he2 hp (by unfold FreeHSite; omega) hF, freeV_minus_eq]
  have hq : TwosTile a (a, y + a - 1) :=
    tile_pt (by unfold NativeT; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
      (by unfold FreeSite FreeHSite FreeVSite; omega)
  rw [rho_bulk_eq_m ha he2 hq (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega)]
  unfold bulkTreeM
  split_ifs <;> omega

/-- The east diagonal at `x = 2`: the candidate `(2, a)` of rank `1` moves to `(3, a)` of rank `0`. -/
theorem even_E2_minus {a : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hp : TwosTile a (2, a)) :
    rhoTwos a (-1) (3, a) < rhoTwos a (-1) (2, a) := by
  have hq : TwosTile a (3, a) :=
    tile_pt (by unfold NativeT; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
      (by unfold FreeSite FreeHSite FreeVSite; omega)
  rw [rho_bulk_eq_m ha he2 hq (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega),
    rho_bulk_eq_m ha he2 hp (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega)]
  unfold bulkTreeM
  split_ifs <;> omega

/-- The east diagonal at `3 ≤ x ≤ a-1`: `(x, x+a-2)` moves to `(x+1, x+a-2)`, one less. -/
theorem even_E_mid_minus {a x : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hx3 : 3 ≤ x) (hxa : x ≤ a - 1)
    (hp : TwosTile a (x, x + a - 2)) :
    rhoTwos a (-1) (x + 1, x + a - 2) < rhoTwos a (-1) (x, x + a - 2) := by
  have hq : TwosTile a (x + 1, x + a - 2) :=
    tile_pt (by unfold NativeT; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
      (by unfold FreeSite FreeHSite FreeVSite; omega)
  rw [rho_bulk_eq_m ha he2 hq (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega),
    rho_bulk_eq_m ha he2 hp (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega)]
  unfold bulkTreeM
  split_ifs <;> omega

/-- The east diagonal at `x = a`: `(a, 2a-2)` of rank `5` moves to `(a+1, 2a-2)`, the `U` translate of the free V site
`(0, a-1)` of rank `4`. -/
theorem even_E_last_minus {a : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hp : TwosTile a (a, 2 * a - 2)) :
    rhoTwos a (-1) (a + 1, 2 * a - 2) < rhoTwos a (-1) (a, 2 * a - 2) := by
  have hU := rhoTwos_add_U_eta (-1) a 0 (a - 1)
  rw [show (0 : ℤ) + (a + 1) = a + 1 by ring, show (a - 1 : ℤ) + (a - 1) = 2 * a - 2 by ring] at hU
  rw [hU]
  have hp0 : TwosTile a (0, a - 1) :=
    free_tile (Or.inr (Or.inl ⟨rfl, by omega, by omega⟩)) (by unfold NativeT; omega)
  rw [rhoTwos_tile_freeV_eta (-1) ha he2 hp0 (by unfold FreeHSite; omega) (Or.inl ⟨rfl, by omega, by omega⟩),
    freeV_minus_eq]
  rw [rho_bulk_eq_m ha he2 hp (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega)]
  unfold bulkTreeM
  split_ifs <;> omega

/-- The west diagonal at `x = 0`: `(0, a)` of rank `3` moves to `(-1, a)`, the `U` translate of the special point of rank `2`. -/
theorem even_W0_minus {a : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hp : TwosTile a (0, a)) :
    rhoTwos a (-1) (-1, a) < rhoTwos a (-1) (0, a) := by
  have hU := rhoTwos_add_U_eta (-1) a (-1) a
  rw [show (-1 : ℤ) + (a + 1) = a by ring, show a + (a - 1) = 2 * a - 1 by ring] at hU
  rw [← hU, rhoTwos_tile_eta (-1) ha he2 (tile_a_2a1 ha), deck_special_minus ha]
  rw [rho_bulk_eq_m ha he2 hp (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega)]
  unfold bulkTreeM
  split_ifs <;> omega

/-- The west diagonal at `1 ≤ x ≤ a-2`: `(x, x+a)` of rank `2x+3` moves to `(x-1, x+a)`, of rank `2x+2`. -/
theorem even_W_mid_minus {a x : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hx1 : 1 ≤ x) (hxa : x ≤ a - 2)
    (hp : TwosTile a (x, x + a)) :
    rhoTwos a (-1) (x + -1, x + a) < rhoTwos a (-1) (x, x + a) := by
  have hq : TwosTile a (x + -1, x + a) :=
    tile_pt (by unfold NativeT; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
      (by unfold FreeSite FreeHSite FreeVSite; omega)
  rw [rho_bulk_eq_m ha he2 hq (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega),
    rho_bulk_eq_m ha he2 hp (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega)]
  unfold bulkTreeM
  split_ifs <;> omega

/-- The even white candidate centres of sign `-1`: the rank of the candidate target drops (no potential argument). -/
theorem candidate_even_minus {a x y : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hp : TwosTile a (x, y))
    (hpar : (x + y) % 2 = 0) (hG : CandGuard a x y) :
    rhoTwos a (-1) (x + (candDisp a x y).1, y + (candDisp a x y).2) < rhoTwos a (-1) (x, y) := by
  rcases hG with hL | hH | hE | hW
  · exfalso
    unfold CandLow at hL
    omega
  · exfalso
    unfold CandHigh at hH
    omega
  · -- the east diagonal
    unfold CandE at hE
    obtain ⟨hy, hx2, hxa⟩ := hE
    rw [candDisp_E_minus hy hx2 hxa]
    have hy' : y = x + a - 2 := by omega
    subst hy'
    simp only [add_zero]
    rcases (show x = 2 ∨ (3 ≤ x ∧ x ≤ a - 1) ∨ x = a by omega) with h | ⟨h1, h2⟩ | h
    · subst h
      rw [show (2 : ℤ) + a - 2 = a by ring] at hp ⊢
      exact even_E2_minus ha he2 hp
    · exact even_E_mid_minus ha he2 h1 h2 hp
    · rw [h] at hp ⊢
      rw [show a + a - 2 = 2 * a - 2 by ring] at hp ⊢
      exact even_E_last_minus ha he2 hp
  · -- the west diagonal
    unfold CandW at hW
    obtain ⟨hy, h0, hxa⟩ := hW
    rw [candDisp_W_minus hy h0 hxa]
    have hy' : y = x + a := by omega
    subst hy'
    simp only [add_zero]
    rcases (show x = 0 ∨ 1 ≤ x by omega) with h | h
    · subst h
      simp only [zero_add] at hp ⊢
      exact even_W0_minus ha he2 hp
    · exact even_W_mid_minus ha he2 h hxa hp

/-- The even white centres of sign `-1`: a tile centre of `EvenWhitePiece` with even parity has its selected input of
rank below its own (no potential argument is needed). -/
theorem hTile_minus_even_white (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    {p1 p2 i1 i2 : ℤ} (hp : TwosTile (2 * (k : ℤ) + 4) (p1, p2)) (hpar : (p1 + p2) % 2 = 0)
    (hX : EvenWhitePiece (2 * (k : ℤ) + 4) p1 p2)
    (hsel : TwosSel (2 * (k : ℤ) + 4) (-1) (standardField (List.replicate (k + 1) Digit.two)) (p1, p2) (i1, i2)) :
    rhoTwos (2 * (k : ℤ) + 4) (-1) (i1, i2) < rhoTwos (2 * (k : ℤ) + 4) (-1) (p1, p2) := by
  have ha : (4 : ℤ) ≤ 2 * (k : ℤ) + 4 := by omega
  have he2 : (2 * (k : ℤ) + 4) % 2 = 0 := by omega
  have hN : NativeT (2 * (k : ℤ) + 4) p1 p2 := ((tile_iff_lin _ _ _).mp hp).1
  have hl : laplacian (standardField (List.replicate (k + 1) Digit.two)) (p1, p2) = 0 :=
    lap_even_white k hagree hperiod hN hpar hX
  by_cases hf : FreeSite (2 * (k : ℤ) + 4) p1 p2
  · have hd := (twosSel_free_self (η := -1) ha he2 hl hp hf).mp hsel
    unfold FreeSite FreeHSite FreeVSite at hf
    rcases hf with (H1 | H2 | H3) | (V1 | V2)
    · exfalso
      obtain ⟨h1, h2⟩ := H1
      omega
    · -- the H sites (x, x-2)
      obtain ⟨h1, h2, h3⟩ := H2
      rw [h3] at hd hp ⊢
      rw [freeDisp_minus_H2 h1 h2] at hd
      rw [hd]
      simp only [add_zero]
      rcases (show p1 = 2 ∨ (3 ≤ p1 ∧ p1 ≤ 2 * (k : ℤ) + 4 - 1) ∨ p1 = 2 * (k : ℤ) + 4 by omega) with h | ⟨h4, h5⟩ | h
      · subst h
        exact even_H2_two_minus ha he2 hp
      · exact even_H2_mid_minus ha he2 h4 h5 hp
      · subst h
        exact even_H2_last_minus ha he2 hp
    · exfalso
      obtain ⟨h1, h2⟩ := H3
      omega
    · -- the V sites (0, y)
      obtain ⟨h1, h2, h3⟩ := V1
      subst h1
      rcases (show p2 = 0 ∨ 2 ≤ p2 by omega) with h | h
      · subst h
        rw [freeDisp_minus_V00 ha] at hd
        rw [hd]
        simp only [add_zero, zero_add]
        exact even_V0_zero_minus ha he2 hp
      · rw [freeDisp_minus_V0_even ha (by omega) h] at hd
        rw [hd]
        simp only [add_zero, zero_add]
        exact even_V0_mid_minus ha he2 h (by omega) (by omega) hp
    · -- the V sites (-1, y)
      obtain ⟨h1, h2, h3⟩ := V2
      subst h1
      rw [freeDisp_minus_Vm1_odd ha (by omega)] at hd
      rw [hd]
      simp only [add_zero]
      exact free_V1_odd_minus ha he2 (by omega) (by omega) (by omega)
  · have hpS : ¬ (p1 = 2 * (k : ℤ) + 4 ∧ p2 = 2 * (2 * (k : ℤ) + 4) - 1) := fun h => by
      obtain ⟨h1, h2⟩ := h
      omega
    obtain ⟨hG, hd⟩ := twosSel_cand_tile_eta rfl hp hf hpS hl hsel
    rw [hd]
    exact candidate_even_minus ha he2 hp hpar hG

end FLatticePaper.TwosEPolicy

