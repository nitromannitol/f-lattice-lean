import FLatticePaper.Plane.Induction.TwosFreeAll
import FLatticePaper.Plane.Induction.TwosCandAll
import FLatticePaper.Plane.Induction.TwosSpecialCentres
import FLatticePaper.Plane.Induction.TwosBlackDrop
import FLatticePaper.Plane.Induction.TwosBlackEvenDrop
import FLatticePaper.Plane.Induction.TwosCandSel

/-! Twos flatness, the tile claim `hTile` for sign `+1`: on a tile centre `p` and a selected input `i` with equal chain
potential, the rank `rhoTwos` strictly drops. The cases are the odd black, the odd white (special and free and candidate),
the even white (free and candidate) and the even black centres. -/

noncomputable section

namespace FLatticePaper.TwosEPolicy

open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey
open scoped Classical

/-- The odd black centres: the inputs are the vertical neighbours. -/
theorem hTile_odd_black (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    {p1 p2 i1 i2 : ℤ} (hp : TwosTile (2 * (k : ℤ) + 4) (p1, p2))
    (hpar : (p1 + p2) % 2 = 1)
    (hB : LadderOddEvenBlack (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - p2, p1 + 1))
    (hsel : TwosSel (2 * (k : ℤ) + 4) 1 (standardField (List.replicate (k + 1) Digit.two)) (p1, p2) (i1, i2))
    (hΦ : twosPhi k 1 (i1, i2) = twosPhi k 1 (p1, p2)) :
    rhoTwos (2 * (k : ℤ) + 4) 1 (i1, i2) < rhoTwos (2 * (k : ℤ) + 4) 1 (p1, p2) := by
  have hk : (2 * (k : ℤ) + 4) = 2 * (k : ℤ) + 4 := rfl
  have hN : NativeT (2 * (k : ℤ) + 4) p1 p2 := ((tile_iff_lin _ _ _).mp hp).1
  have hBexp := (odd_black_explicit (2 * (k : ℤ) + 4) p1 p2).mp hB
  have hlap := (lap_odd_black_iff k hagree hperiod hN hpar).mpr hB
  rcases hsel with ⟨-, hE⟩ | ⟨hl0, -⟩
  · have hodd : ¬ EvenSite (p1, p2) := by
      unfold EvenSite
      omega
    unfold Edge incomingNeg incomingPos at hE
    simp only [hodd, if_false] at hE
    rcases hE with hE | hE
    · obtain ⟨e1, e2⟩ := Prod.mk.inj hE
      rw [e1, e2] at hΦ ⊢
      exact odd_black_drop_down hk hBexp hp hpar hΦ
    · obtain ⟨e1, e2⟩ := Prod.mk.inj hE
      rw [e1, e2]
      exact odd_black_drop_up hk hBexp hp hpar
  · rw [hlap] at hl0
    norm_num at hl0

/-- The odd white centres: the special point `(a, 2a-1)`, the free centres, and the candidate centres. -/
theorem hTile_odd_white (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    {p1 p2 i1 i2 : ℤ} (hp : TwosTile (2 * (k : ℤ) + 4) (p1, p2))
    (hpar : (p1 + p2) % 2 = 1)
    (hB : ¬ LadderOddEvenBlack (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - p2, p1 + 1))
    (hsel : TwosSel (2 * (k : ℤ) + 4) 1 (standardField (List.replicate (k + 1) Digit.two)) (p1, p2) (i1, i2))
    (hΦ : twosPhi k 1 (i1, i2) = twosPhi k 1 (p1, p2)) :
    rhoTwos (2 * (k : ℤ) + 4) 1 (i1, i2) < rhoTwos (2 * (k : ℤ) + 4) 1 (p1, p2) := by
  have hk : (2 * (k : ℤ) + 4) = 2 * (k : ℤ) + 4 := rfl
  have ha : (4 : ℤ) ≤ 2 * (k : ℤ) + 4 := by omega
  have he2 : (2 * (k : ℤ) + 4) % 2 = 0 := by omega
  have hN : NativeT (2 * (k : ℤ) + 4) p1 p2 := ((tile_iff_lin _ _ _).mp hp).1
  have hl : laplacian (standardField (List.replicate (k + 1) Digit.two)) (p1, p2) = 0 :=
    lap_odd_value k hagree hperiod hN hpar hB
  by_cases hsp : p1 = 2 * (k : ℤ) + 4 ∧ p2 = 2 * (2 * (k : ℤ) + 4) - 1
  · obtain ⟨hs1, hs2⟩ := hsp
    rw [hs1, hs2] at hsel hΦ hl ⊢
    have hlz := twosSel_special_1 k hl ha hsel
    obtain ⟨e1, e2⟩ := Prod.mk.inj hlz
    rw [e1, e2]
    exact special1_rho_drop ha he2
  · by_cases hf : FreeSite (2 * (k : ℤ) + 4) p1 p2
    · have hd := (twosSel_free_self (η := 1) ha he2 hl hp hf).mp hsel
      exact free_flat_drop hk hp hf hd hΦ
    · obtain ⟨hG, hd⟩ := twosSel_cand_tile hk hp hf hsp hl hsel
      rw [hd] at hΦ ⊢
      exact candidate_flat_drop hk hp hf hsp hG hΦ

/-- The even white centres: the free centres and the candidate centres. -/
theorem hTile_even_white (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    {p1 p2 i1 i2 : ℤ} (hp : TwosTile (2 * (k : ℤ) + 4) (p1, p2))
    (hpar : (p1 + p2) % 2 = 0)
    (hX : EvenWhitePiece (2 * (k : ℤ) + 4) p1 p2)
    (hsel : TwosSel (2 * (k : ℤ) + 4) 1 (standardField (List.replicate (k + 1) Digit.two)) (p1, p2) (i1, i2))
    (hΦ : twosPhi k 1 (i1, i2) = twosPhi k 1 (p1, p2)) :
    rhoTwos (2 * (k : ℤ) + 4) 1 (i1, i2) < rhoTwos (2 * (k : ℤ) + 4) 1 (p1, p2) := by
  have hk : (2 * (k : ℤ) + 4) = 2 * (k : ℤ) + 4 := rfl
  have ha : (4 : ℤ) ≤ 2 * (k : ℤ) + 4 := by omega
  have he2 : (2 * (k : ℤ) + 4) % 2 = 0 := by omega
  have hN : NativeT (2 * (k : ℤ) + 4) p1 p2 := ((tile_iff_lin _ _ _).mp hp).1
  have hl : laplacian (standardField (List.replicate (k + 1) Digit.two)) (p1, p2) = 0 :=
    lap_even_white k hagree hperiod hN hpar hX
  have hsp : ¬ (p1 = 2 * (k : ℤ) + 4 ∧ p2 = 2 * (2 * (k : ℤ) + 4) - 1) := fun h => by
    obtain ⟨h1, h2⟩ := h
    omega
  by_cases hf : FreeSite (2 * (k : ℤ) + 4) p1 p2
  · have hd := (twosSel_free_self (η := 1) ha he2 hl hp hf).mp hsel
    exact free_flat_drop hk hp hf hd hΦ
  · obtain ⟨hG, hd⟩ := twosSel_cand_tile hk hp hf hsp hl hsel
    rw [hd] at hΦ ⊢
    exact candidate_flat_drop hk hp hf hsp hG hΦ

/-- The even black centres: the inputs are the horizontal neighbours. -/
theorem hTile_even_black (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    {p1 p2 i1 i2 : ℤ} (hp : TwosTile (2 * (k : ℤ) + 4) (p1, p2))
    (hpar : (p1 + p2) % 2 = 0)
    (hLOOW : ¬ LadderOddOddWhite (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - p2, p1 + 1))
    (hsel : TwosSel (2 * (k : ℤ) + 4) 1 (standardField (List.replicate (k + 1) Digit.two)) (p1, p2) (i1, i2))
    (hΦ : twosPhi k 1 (i1, i2) = twosPhi k 1 (p1, p2)) :
    rhoTwos (2 * (k : ℤ) + 4) 1 (i1, i2) < rhoTwos (2 * (k : ℤ) + 4) 1 (p1, p2) := by
  have hk : (2 * (k : ℤ) + 4) = 2 * (k : ℤ) + 4 := rfl
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
      exact even_black_drop_left hk hp hp1 hp2 hp3 hB hpar hΦ
    · obtain ⟨e1, e2⟩ := Prod.mk.inj hE
      rw [e1, e2] at hΦ ⊢
      exact even_black_drop_right hk hp hp1 hp2 hp3 hB hpar hΦ
  · have hlap := (lap_even_black_iff k hagree hperiod hN (by omega)).mpr hLOOW
    rw [hlap] at hl0
    norm_num at hl0

set_option maxHeartbeats 400000 in
/-- **The tile claim, sign `+1`.** -/
theorem twos_hTile_plus (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4))) :
    ∀ p : Site, TwosTile (2 * (k : ℤ) + 4) p → ∀ i : Site,
      TwosSel (2 * (k : ℤ) + 4) 1 (standardField (List.replicate (k + 1) Digit.two)) p i →
      twosPhi k 1 i = twosPhi k 1 p → rhoTwos (2 * (k : ℤ) + 4) 1 i < rhoTwos (2 * (k : ℤ) + 4) 1 p := by
  rintro ⟨p1, p2⟩ hp ⟨i1, i2⟩ hsel hΦ
  by_cases hpar : (p1 + p2) % 2 = 1
  · by_cases hB : LadderOddEvenBlack (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - p2, p1 + 1)
    · exact hTile_odd_black k hagree hperiod hp hpar hB hsel hΦ
    · exact hTile_odd_white k hagree hperiod hp hpar hB hsel hΦ
  · have hpar0 : (p1 + p2) % 2 = 0 := by omega
    by_cases hLOOW : LadderOddOddWhite (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - p2, p1 + 1)
    · have hX : EvenWhitePiece (2 * (k : ℤ) + 4) p1 p2 := by
        by_contra hc
        exact ((even_black_explicit (2 * (k : ℤ) + 4) p1 p2).mpr hc) hLOOW
      exact hTile_even_white k hagree hperiod hp hpar0 hX hsel hΦ
    · exact hTile_even_black k hagree hperiod hp hpar0 hLOOW hsel hΦ

end FLatticePaper.TwosEPolicy
