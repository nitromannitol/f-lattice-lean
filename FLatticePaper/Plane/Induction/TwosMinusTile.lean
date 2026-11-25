import FLatticePaper.Plane.Induction.TwosMinusOddWhite
import FLatticePaper.Plane.Induction.TwosMinusEvenWhite
import FLatticePaper.Plane.Induction.TwosMinusOddBlack
import FLatticePaper.Plane.Induction.TwosBlackOdd
import FLatticePaper.Plane.Induction.TwosBlackEvenNb
import FLatticePaper.Plane.Induction.TwosBlackEven
import FLatticePaper.Plane.Induction.TwosMinusEvenBlack

/-! Twos flatness, sign `-1`: the tile claims by centre type, assembled from the drops of each type. -/

noncomputable section

namespace FLatticePaper.TwosEPolicy

open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey
open scoped Classical

/-- The odd black centres of sign `-1`: the selected inputs are the vertical neighbours, each of rank one less when the
potentials agree (the upper neighbour without the potential). -/
theorem hTile_minus_odd_black (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    {p1 p2 i1 i2 : ℤ} (hp : TwosTile (2 * (k : ℤ) + 4) (p1, p2)) (hpar : (p1 + p2) % 2 = 1)
    (hB : LadderOddEvenBlack (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - p2, p1 + 1))
    (hsel : TwosSel (2 * (k : ℤ) + 4) (-1) (standardField (List.replicate (k + 1) Digit.two)) (p1, p2) (i1, i2))
    (hΦ : twosPhi k (-1) (i1, i2) = twosPhi k (-1) (p1, p2)) :
    rhoTwos (2 * (k : ℤ) + 4) (-1) (i1, i2) < rhoTwos (2 * (k : ℤ) + 4) (-1) (p1, p2) := by
  have hk : (2 * (k : ℤ) + 4) = 2 * (k : ℤ) + 4 := rfl
  have hN : NativeT (2 * (k : ℤ) + 4) p1 p2 := ((tile_iff_lin _ _ _).mp hp).1
  have hBexp := (odd_black_explicit (2 * (k : ℤ) + 4) p1 p2).mp hB
  have hlap := (lap_odd_black_iff k hagree hperiod hN hpar).mpr hB
  rcases hsel with ⟨hl0, hE⟩ | ⟨hl0, -⟩
  · have hodd : ¬ EvenSite (p1, p2) := by
      unfold EvenSite
      omega
    unfold Edge incomingNeg incomingPos at hE
    simp only [hodd, if_false] at hE
    rcases hE with hE | hE
    · obtain ⟨e1, e2⟩ := Prod.mk.inj hE
      rw [e1, e2] at hΦ ⊢
      exact odd_black_down_m hk hBexp hp hpar hΦ
    · obtain ⟨e1, e2⟩ := Prod.mk.inj hE
      rw [e1, e2]
      exact odd_black_up_m hk hBexp hp hpar
  · rw [hlap] at hl0
    norm_num at hl0

/-- The left neighbour of an even black native point is a tile. -/
theorem even_black_left_tile_m {a x y : ℤ} (ha : 4 ≤ a) (hN : NativeT a x y) (hB : ¬ EvenWhitePiece a x y)
    (he : (x + y) % 2 = 0) : TwosTile a (x - 1, y) := by
  have hNl := even_black_nat_left ha hN hB he
  have nc9 : ¬ (x = 0 ∧ y = 2 * a) := fun h => hB (ewp_9 h)
  have ne6 : ¬ (x = a ∧ 2 * a - 2 ≤ y ∧ y ≤ 3 * a - 2) := fun h => hB (ewp_6 h)
  have hNx := hN
  unfold NativeT at hNx
  exact tile_pt hNl (by unfold FreeSite FreeHSite FreeVSite; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)

/-- The right neighbour of an even black native point is a tile, off the two families whose neighbour is the `U` translate of
a free V site. -/
theorem even_black_right_tile_m {a x y : ℤ} (ha : 4 ≤ a) (hN : NativeT a x y) (hB : ¬ EvenWhitePiece a x y)
    (he : (x + y) % 2 = 0) (hR1 : ¬ (x = a - 1 ∧ 2 * a - 1 ≤ y ∧ y ≤ 3 * a - 2))
    (hR2 : ¬ (x = a ∧ a ≤ y ∧ y ≤ 2 * a - 2)) : TwosTile a (x + 1, y) := by
  have hNr := even_black_nat_right ha hN hB he
  have ne1 : ¬ (y - x = 2 * a ∧ 1 ≤ x ∧ x ≤ a - 2) := fun h => hB (ewp_1 h)
  have hNx := hN
  unfold NativeT at hNx
  exact tile_pt hNr (by unfold FreeSite FreeHSite FreeVSite; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)

/-- The even black centre `(a+1, 2a-1)`: its left neighbour is the special point `(a, 2a-1)`, of rank `2`, below the rank
`3` of `(a+1, 2a-1)` (which is the `U` translate of `(0, a)`). -/
theorem even_black_left_special {a : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) :
    rhoTwos a (-1) (a, 2 * a - 1) < rhoTwos a (-1) (a + 1, 2 * a - 1) := by
  have hU := rhoTwos_add_U_eta (-1) a 0 a
  rw [show (0 : ℤ) + (a + 1) = a + 1 by ring, show a + (a - 1) = 2 * a - 1 by ring] at hU
  rw [hU, rhoTwos_tile_eta (-1) ha he2 (tile_a_2a1 ha), deck_special_minus ha]
  have hp0 : TwosTile a (0, a) :=
    tile_pt (by unfold NativeT; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
      (by unfold FreeSite FreeHSite FreeVSite; omega)
  rw [rho_bulk_eq_m ha he2 hp0 (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega)]
  unfold bulkTreeM
  split_ifs <;> omega

/-- The even black centre `(a-1, 2a-1)`: its right neighbour is the special point `(a, 2a-1)`, of rank `2`, below the rank
of `(a-1, 2a-1)`. -/
theorem even_black_right_special {a : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) :
    rhoTwos a (-1) (a, 2 * a - 1) < rhoTwos a (-1) (a - 1, 2 * a - 1) := by
  rw [rhoTwos_tile_eta (-1) ha he2 (tile_a_2a1 ha), deck_special_minus ha]
  have hp0 : TwosTile a (a - 1, 2 * a - 1) :=
    tile_pt (by unfold NativeT; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
      (by unfold FreeSite FreeHSite FreeVSite; omega)
  rw [rho_bulk_eq_m ha he2 hp0 (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega)]
  unfold bulkTreeM
  split_ifs <;> omega

/-- The right family R1: `(a-1, y)`, `y` odd, `2a+1 ≤ y ≤ 3a-3`: the neighbour `(a, y)` is the `U` translate of the free V
site `(-1, y-a+1)`, of rank one less than `(a-1, y)`. -/
theorem even_black_right_R1 {a y : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hy1 : 2 * a + 1 ≤ y) (hy2 : y ≤ 3 * a - 3)
    (hodd : y % 2 = 1) : rhoTwos a (-1) (a, y) < rhoTwos a (-1) (a - 1, y) := by
  have hU := rhoTwos_add_U_eta (-1) a (-1) (y - a + 1)
  rw [show (-1 : ℤ) + (a + 1) = a by ring, show y - a + 1 + (a - 1) = y by ring] at hU
  rw [hU]
  have hq : TwosTile a (-1, y - a + 1) :=
    free_tile (Or.inr (Or.inr ⟨rfl, by omega, by omega⟩)) (by unfold NativeT; omega)
  rw [rhoTwos_tile_freeV_eta (-1) ha he2 hq (by unfold FreeHSite; omega) (Or.inr ⟨rfl, by omega, by omega⟩),
    freeV_minus_eq]
  have hp : TwosTile a (a - 1, y) :=
    tile_pt (by unfold NativeT; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
      (by unfold FreeSite FreeHSite FreeVSite; omega)
  rw [rho_bulk_eq_m ha he2 hp (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega)]
  unfold bulkTreeM
  split_ifs <;> omega

/-- The right family R2: `(a, y)`, `y` even, `a+2 ≤ y ≤ 2a-4`: the neighbour `(a+1, y)` is the `U` translate of the free V site
`(0, y-a+1)`, of rank `4a-2y`, below the rank `4a+1-2y` of `(a, y)`. -/
theorem even_black_right_R2 {a y : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hy1 : a + 2 ≤ y) (hy2 : y ≤ 2 * a - 4)
    (hye : y % 2 = 0) : rhoTwos a (-1) (a + 1, y) < rhoTwos a (-1) (a, y) := by
  have hU := rhoTwos_add_U_eta (-1) a 0 (y - a + 1)
  rw [show (0 : ℤ) + (a + 1) = a + 1 by ring, show y - a + 1 + (a - 1) = y by ring] at hU
  rw [hU]
  have hq : TwosTile a (0, y - a + 1) :=
    free_tile (Or.inr (Or.inl ⟨rfl, by omega, by omega⟩)) (by unfold NativeT; omega)
  rw [rhoTwos_tile_freeV_eta (-1) ha he2 hq (by unfold FreeHSite; omega) (Or.inl ⟨rfl, by omega, by omega⟩),
    freeV_minus_eq]
  have hp : TwosTile a (a, y) :=
    tile_pt (by unfold NativeT; omega) (by unfold FreeSite FreeHSite FreeVSite; omega)
      (by unfold FreeSite FreeHSite FreeVSite; omega)
  rw [rho_bulk_eq_m ha he2 hp (by unfold FreeSite FreeHSite FreeVSite; omega) (by omega)]
  unfold bulkTreeM
  split_ifs <;> omega

/-- The left drop of an even black centre, with the potential equality. -/
theorem even_black_left_case {a x y : ℤ} {k : ℕ} (hk : a = 2 * (k : ℤ) + 4) (ha : 4 ≤ a) (he2 : a % 2 = 0)
    (hp : TwosTile a (x, y)) (hB : ¬ EvenWhitePiece a x y) (he : (x + y) % 2 = 0)
    (hp2 : ¬ (x = a ∧ y = 2 * a - 1))
    (hΦ : twosPhi k (-1) (x - 1, y) = twosPhi k (-1) (x, y)) :
    rhoTwos a (-1) (x - 1, y) < rhoTwos a (-1) (x, y) := by
  have hN : NativeT a x y := ((tile_iff_lin _ _ _).mp hp).1
  have hF : ¬ (x = a ∧ y = a - 2) := fun h => hB (ewp_10 h)
  by_cases hs : x = a + 1 ∧ y = 2 * a - 1
  · obtain ⟨h1, h2⟩ := hs
    subst h1
    subst h2
    rw [show a + 1 - 1 = a by ring]
    exact even_black_left_special ha he2
  · exact even_left_m hk hp hp2 hF hB he (even_black_left_tile_m ha hN hB he)
      (fun h => hs ⟨by omega, h.2⟩) hΦ

/-- The right drop of an even black centre, with the potential equality. -/
theorem even_black_right_case {a x y : ℤ} {k : ℕ} (hk : a = 2 * (k : ℤ) + 4) (ha : 4 ≤ a) (he2 : a % 2 = 0)
    (hp : TwosTile a (x, y)) (hB : ¬ EvenWhitePiece a x y) (he : (x + y) % 2 = 0)
    (hp1 : ¬ (x = a ∧ y = 2 * a - 2)) (hp2 : ¬ (x = a ∧ y = 2 * a - 1)) (hp3 : ¬ (x = a + 1 ∧ y = a - 2))
    (hΦ : twosPhi k (-1) (x + 1, y) = twosPhi k (-1) (x, y)) :
    rhoTwos a (-1) (x + 1, y) < rhoTwos a (-1) (x, y) := by
  have hN : NativeT a x y := ((tile_iff_lin _ _ _).mp hp).1
  have hF : ¬ (x = a ∧ y = a - 2) := fun h => hB (ewp_10 h)
  by_cases hs : x = a - 1 ∧ y = 2 * a - 1
  · obtain ⟨h1, h2⟩ := hs
    subst h1
    subst h2
    rw [show a - 1 + 1 = a by ring]
    exact even_black_right_special ha he2
  by_cases hA : x = a ∧ y = a
  · obtain ⟨h1, h2⟩ := hA
    subst h1
    subst h2
    exact (even_right_ne_d k hk rfl hΦ).elim
  by_cases hR2 : x = a ∧ a + 2 ≤ y ∧ y ≤ 2 * a - 4
  · obtain ⟨h1, h2, h3⟩ := hR2
    subst h1
    have hye : y % 2 = 0 := by omega
    exact even_black_right_R2 ha he2 h2 h3 hye
  by_cases hR1 : x = a - 1 ∧ 2 * a + 1 ≤ y ∧ y ≤ 3 * a - 3
  · obtain ⟨h1, h2, h3⟩ := hR1
    subst h1
    have hodd : y % 2 = 1 := by omega
    rw [show a - 1 + 1 = a by ring]
    exact even_black_right_R1 ha he2 h2 h3 hodd
  have hi : TwosTile a (x + 1, y) :=
    even_black_right_tile_m ha hN hB he (fun h => by omega) (fun h => by omega)
  exact even_right_m hk hp hp1 hp2 hp3 hF hB he hi (fun h => hs ⟨by omega, h.2⟩) hΦ

/-- The even black centres of sign `-1`: the selected inputs are the horizontal neighbours; the left and right drops of every
even black tile centre hold under the potential equality of the flatness hypothesis. -/
theorem hTile_minus_even_black (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    {p1 p2 i1 i2 : ℤ} (hp : TwosTile (2 * (k : ℤ) + 4) (p1, p2)) (hpar : (p1 + p2) % 2 = 0)
    (hLOOW : ¬ LadderOddOddWhite (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - p2, p1 + 1))
    (hsel : TwosSel (2 * (k : ℤ) + 4) (-1) (standardField (List.replicate (k + 1) Digit.two)) (p1, p2) (i1, i2))
    (hΦ : twosPhi k (-1) (i1, i2) = twosPhi k (-1) (p1, p2)) :
    rhoTwos (2 * (k : ℤ) + 4) (-1) (i1, i2) < rhoTwos (2 * (k : ℤ) + 4) (-1) (p1, p2) := by
  have hk : (2 * (k : ℤ) + 4) = 2 * (k : ℤ) + 4 := rfl
  have ha : (4 : ℤ) ≤ 2 * (k : ℤ) + 4 := by omega
  have he2 : (2 * (k : ℤ) + 4) % 2 = 0 := by omega
  have hN : NativeT (2 * (k : ℤ) + 4) p1 p2 := ((tile_iff_lin _ _ _).mp hp).1
  have hB : ¬ EvenWhitePiece (2 * (k : ℤ) + 4) p1 p2 := fun hX =>
    ((even_black_explicit (2 * (k : ℤ) + 4) p1 p2).mp hLOOW) hX
  have hp1 : ¬ (p1 = 2 * (k : ℤ) + 4 ∧ p2 = 2 * (2 * (k : ℤ) + 4) - 2) := fun h =>
    hB (ewp_6 ⟨h.1, by omega, by omega⟩)
  have hp2 : ¬ (p1 = 2 * (k : ℤ) + 4 ∧ p2 = 2 * (2 * (k : ℤ) + 4) - 1) := fun h => by
    obtain ⟨h1, h2⟩ := h
    omega
  have hp3 : ¬ (p1 = 2 * (k : ℤ) + 4 + 1 ∧ p2 = 2 * (k : ℤ) + 4 - 2) := fun h => by
    obtain ⟨h1, h2⟩ := h
    omega
  rcases hsel with ⟨hl0, hE⟩ | ⟨hl0, -⟩
  · unfold Edge incomingNeg incomingPos at hE
    have heven : EvenSite (p1, p2) := by
      unfold EvenSite
      omega
    simp only [heven, if_true] at hE
    rcases hE with hE | hE
    · obtain ⟨e1, e2⟩ := Prod.mk.inj hE
      rw [e1, e2] at hΦ ⊢
      exact even_black_left_case hk ha he2 hp hB hpar hp2 hΦ
    · obtain ⟨e1, e2⟩ := Prod.mk.inj hE
      rw [e1, e2] at hΦ ⊢
      exact even_black_right_case hk ha he2 hp hB hpar hp1 hp2 hp3 hΦ
  · have hlap := (lap_even_black_iff k hagree hperiod hN (by omega)).mpr hLOOW
    rw [hlap] at hl0
    norm_num at hl0

/-- **The tile claim, sign `-1`.** Every tile centre, with each of its selected inputs of equal potential, has rank above
that input: the odd and even centres, black and white, dispatch to the claims above. -/
theorem twos_hTile_minus (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4))) :
    ∀ p : Site, TwosTile (2 * (k : ℤ) + 4) p → ∀ i : Site,
      TwosSel (2 * (k : ℤ) + 4) (-1) (standardField (List.replicate (k + 1) Digit.two)) p i →
      twosPhi k (-1) i = twosPhi k (-1) p → rhoTwos (2 * (k : ℤ) + 4) (-1) i < rhoTwos (2 * (k : ℤ) + 4) (-1) p := by
  rintro ⟨p1, p2⟩ hp ⟨i1, i2⟩ hsel hΦ
  by_cases hpar : (p1 + p2) % 2 = 1
  · by_cases hB : LadderOddEvenBlack (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - p2, p1 + 1)
    · exact hTile_minus_odd_black k hagree hperiod hp hpar hB hsel hΦ
    · exact hTile_minus_odd_white k hagree hperiod hp hpar hB hsel hΦ
  · have hpar0 : (p1 + p2) % 2 = 0 := by omega
    by_cases hLOOW : LadderOddOddWhite (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - p2, p1 + 1)
    · have hX : EvenWhitePiece (2 * (k : ℤ) + 4) p1 p2 := by
        by_contra hc
        exact ((even_black_explicit (2 * (k : ℤ) + 4) p1 p2).mpr hc) hLOOW
      exact hTile_minus_even_white k hagree hperiod hp hpar0 hX hsel
    · exact hTile_minus_even_black k hagree hperiod hp hpar0 hLOOW hsel hΦ

end FLatticePaper.TwosEPolicy
