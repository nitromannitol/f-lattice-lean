import FLatticePaper.Plane.Induction.TwosNearOne
import FLatticePaper.Plane.Induction.TwosPeriods
import FLatticePaper.Plane.Induction.TwosEPolicy
import FLatticePaper.Construction.LadderLaplacian

/-! The Laplacian of the twos field on the native box (task 72). The twos standard field is the rotated odd-ladder source
(`twos_standardField_eq_rotate`), and its Laplacian at `u` is the source Laplacian at the quarter turn `(2a - u.2, u.1 + 1)`
(`rotateLadderField_laplacian`). The native box `FLatticePaper.TwosEPolicy.NativeT` is exactly the set of `u` whose quarter
turn is a raw site of the odd-ladder mask, so the charge table `ladderOdd_laplacian_on_raw` applies at every native point. -/

namespace FLatticePaper.TwosEPolicy

open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey

/-- The odd-ladder source at the denominator `a = 2k+4` is valid. -/
theorem ladderOdd_valid_twos (k : ℕ) : BaseMask.ladderOdd.Valid (2 * (k : ℤ) + 4) :=
  ⟨by omega, by omega⟩

/-- The twos standard field's Laplacian at `u` is the source Laplacian at the quarter turn of `u`. -/
theorem laplacian_twos_eq_source (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    (u : Site) :
    laplacian (standardField (List.replicate (k + 1) Digit.two)) u =
      laplacian S (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) u) := by
  have hfun : standardField (List.replicate (k + 1) Digit.two) =
      rotateLadderField (2 * (k : ℤ) + 4) S :=
    funext fun z => twos_standardField_eq_rotate k hagree hperiod z
  rw [hfun, rotateLadderField_laplacian]

/-- The quarter turn of a native point is a raw site of the odd-ladder mask. -/
theorem nativeT_rot_raw {a : ℤ} (ha : 4 ≤ a) {u : Site} (hu : NativeT a u.1 u.2) :
    QuarterTurn.counterclockwise.mapSite (2 * a, 1) u ∈ (BaseMask.ladderOdd.raw a).sites := by
  rw [quarterTurn_offset_apply, BaseMask.mem_ladderOdd_raw_iff]
  obtain ⟨x, y⟩ := u
  simp only [NativeT, BaseMask.LadderOddCorner] at hu ⊢
  omega

/-- The charge of a native point of the twos field (the source charge table at its quarter turn). -/
theorem laplacian_twos_native (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    {u : Site} (hu : NativeT (2 * (k : ℤ) + 4) u.1 u.2) :
    laplacian (standardField (List.replicate (k + 1) Digit.two)) u =
      if EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) u) then
        (if LadderOddEvenBlack (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) u)
          then -1 else 0)
      else
        (if LadderOddOddWhite (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) u)
          then 0 else -1) := by
  rw [laplacian_twos_eq_source k hagree hperiod u]
  exact ladderOdd_laplacian_on_raw (ladderOdd_valid_twos k) hagree hperiod _
    (nativeT_rot_raw (by omega) hu)

set_option maxHeartbeats 400000 in
/-- The white cover on the odd-`t` branch, with `t = y - x ≤ a - 1`. -/
theorem cover_E_lo (a x y : ℤ) (ha2 : a % 2 = 0) (ha4 : 4 ≤ a) (hu : NativeT a x y)
    (he : EvenSite (2 * a - y, x + 1)) (hb : ¬ LadderOddEvenBlack a (2 * a - y, x + 1)) (ht : y - x ≤ a - 1) :
    CandGuard a x y ∨ FreeSite a x y ∨ FreeSite a (x + 2) (y - 2 * a) ∨
      FreeSite a (x - (a + 1)) (y - (a - 1)) := by
  simp only [EvenSite, LadderOddEvenBlack] at he hb
  simp only [NativeT] at hu
  rcases (by omega : y - x = -3 ∨ y - x = -1 ∨ (1 ≤ y - x ∧ y - x ≤ a - 3) ∨ y - x = a - 1) with h | h | h | h
  · exact Or.inr (Or.inl (by simp only [FreeSite, FreeHSite, FreeVSite]; omega))
  · rcases (by omega : x = 1 ∨ x = a + 1 ∨ (2 ≤ x ∧ x ≤ a)) with h' | h' | h'
    · exact Or.inr (Or.inl (by simp only [FreeSite, FreeHSite, FreeVSite]; omega))
    · exact Or.inr (Or.inr (Or.inr (by simp only [FreeSite, FreeHSite, FreeVSite]; omega)))
    · exact Or.inl (Or.inl (by simp only [CandLow]; omega))
  · rcases (by omega : x = 0 ∨ x = a + 1 ∨ (1 ≤ x ∧ x ≤ a)) with h' | h' | h'
    · exact Or.inr (Or.inl (by simp only [FreeSite, FreeHSite, FreeVSite]; omega))
    · exact Or.inr (Or.inr (Or.inr (by simp only [FreeSite, FreeHSite, FreeVSite]; omega)))
    · exact Or.inl (Or.inl (by simp only [CandLow]; omega))
  · rcases (by omega : x = 0 ∨ x = a ∨ (1 ≤ x ∧ x ≤ a - 1)) with h' | h' | h'
    · exact Or.inr (Or.inl (by simp only [FreeSite, FreeHSite, FreeVSite]; omega))
    · exact Or.inr (Or.inr (Or.inr (by simp only [FreeSite, FreeHSite, FreeVSite]; omega)))
    · exfalso
      omega

set_option maxHeartbeats 400000 in
/-- The white cover on the odd-`t` branch, with `t = y - x ≥ a`. -/
theorem cover_E_hi (a x y : ℤ) (ha2 : a % 2 = 0) (ha4 : 4 ≤ a) (hu : NativeT a x y)
    (he : EvenSite (2 * a - y, x + 1)) (hb : ¬ LadderOddEvenBlack a (2 * a - y, x + 1)) (ht : a ≤ y - x) :
    CandGuard a x y ∨ FreeSite a x y ∨ FreeSite a (x + 2) (y - 2 * a) ∨
      FreeSite a (x - (a + 1)) (y - (a - 1)) := by
  simp only [EvenSite, LadderOddEvenBlack] at he hb
  simp only [NativeT] at hu
  rcases (by omega : (a + 1 ≤ y - x ∧ y - x ≤ 2 * a - 3) ∨ y - x = 2 * a - 1 ∨ y - x = 2 * a + 1) with h | h | h
  · rcases (by omega : x = -1 ∨ x = a ∨ (0 ≤ x ∧ x ≤ a - 1)) with h' | h' | h'
    · exact Or.inr (Or.inl (by simp only [FreeSite, FreeHSite, FreeVSite]; omega))
    · exact Or.inr (Or.inr (Or.inr (by simp only [FreeSite, FreeHSite, FreeVSite]; omega)))
    · exact Or.inl (Or.inr (Or.inl (by simp only [CandHigh]; omega)))
  · rcases (by omega : x = -1 ∨ x = a - 1 ∨ x = 0 ∨ (1 ≤ x ∧ x ≤ a - 2)) with h' | h' | h' | h'
    · exact Or.inr (Or.inl (by simp only [FreeSite, FreeHSite, FreeVSite]; omega))
    · exact Or.inr (Or.inr (Or.inl (by simp only [FreeSite, FreeHSite, FreeVSite]; omega)))
    · exfalso
      omega
    · exact Or.inl (Or.inr (Or.inl (by simp only [CandHigh]; omega)))
  · exact Or.inr (Or.inr (Or.inl (by simp only [FreeSite, FreeHSite, FreeVSite]; omega)))

/-- The white cover on the odd-`t` branch (the quarter turn is even), by the two `t` ranges. -/
theorem cover_E (a x y : ℤ) (ha2 : a % 2 = 0) (ha4 : 4 ≤ a) (hu : NativeT a x y)
    (he : EvenSite (2 * a - y, x + 1)) (hb : ¬ LadderOddEvenBlack a (2 * a - y, x + 1)) :
    CandGuard a x y ∨ FreeSite a x y ∨ FreeSite a (x + 2) (y - 2 * a) ∨
      FreeSite a (x - (a + 1)) (y - (a - 1)) := by
  by_cases ht : y - x ≤ a - 1
  · exact cover_E_lo a x y ha2 ha4 hu he hb ht
  · exact cover_E_hi a x y ha2 ha4 hu he hb (by omega)

set_option maxHeartbeats 400000 in
/-- The white cover on the even-`t` branch (the quarter turn is odd): the ten charge pieces of `OddWhite`, one alternative each. -/
theorem cover_O (a x y : ℤ) (ha2 : a % 2 = 0) (ha4 : 4 ≤ a) (_hu : NativeT a x y)
    (_he : ¬ EvenSite (2 * a - y, x + 1)) (hb : LadderOddOddWhite a (2 * a - y, x + 1)) :
    CandGuard a x y ∨ FreeSite a x y ∨ FreeSite a (x + 2) (y - 2 * a) ∨
      FreeSite a (x - (a + 1)) (y - (a - 1)) := by
  simp only [LadderOddOddWhite, LadderOddLowerBoundary, reflectLadderOdd, Prod.fst_sub, Prod.snd_sub] at hb
  rcases hb with (h1 | h2 | h3) | (h4 | h5 | h6) | h7 | h8 | h9 | h10
  · exact Or.inr (Or.inr (Or.inl (by simp only [FreeSite, FreeHSite, FreeVSite]; omega)))
  · exact Or.inr (Or.inl (by simp only [FreeSite, FreeHSite, FreeVSite]; omega))
  · by_cases hy : y = a
    · exact Or.inl (Or.inr (Or.inr (Or.inr (by simp only [CandW]; omega))))
    · exact Or.inr (Or.inl (by simp only [FreeSite, FreeHSite, FreeVSite]; omega))
  · exact Or.inr (Or.inl (by simp only [FreeSite, FreeHSite, FreeVSite]; omega))
  · exact Or.inr (Or.inr (Or.inr (by simp only [FreeSite, FreeHSite, FreeVSite]; omega)))
  · by_cases ht : y - x = a - 2
    · exact Or.inl (Or.inr (Or.inr (Or.inl (by simp only [CandE]; omega))))
    · exact Or.inr (Or.inr (Or.inr (by simp only [FreeSite, FreeHSite, FreeVSite]; omega)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (by simp only [CandW]; omega))))
  · exact Or.inl (Or.inr (Or.inr (Or.inl (by simp only [CandE]; omega))))
  · exact Or.inr (Or.inr (Or.inl (by simp only [FreeSite, FreeHSite, FreeVSite]; omega)))
  · exact Or.inr (Or.inl (by simp only [FreeSite, FreeHSite, FreeVSite]; omega))

/-- Every native white is candidate-covered, an H/V site, or a translate of an H/V site by `-V` or `-U`. -/
theorem native_white_cover (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    {u : Site} (hu : NativeT (2 * (k : ℤ) + 4) u.1 u.2)
    (hw : laplacian (standardField (List.replicate (k + 1) Digit.two)) u = 0) :
    CandGuard (2 * (k : ℤ) + 4) u.1 u.2 ∨ FreeSite (2 * (k : ℤ) + 4) u.1 u.2 ∨
      FreeSite (2 * (k : ℤ) + 4) (u.1 + 2) (u.2 - 2 * (2 * (k : ℤ) + 4)) ∨
      FreeSite (2 * (k : ℤ) + 4) (u.1 - (2 * (k : ℤ) + 4 + 1)) (u.2 - (2 * (k : ℤ) + 4 - 1)) := by
  have hc := laplacian_twos_native k hagree hperiod hu
  rw [hw, quarterTurn_offset_apply] at hc
  obtain ⟨x, y⟩ := u
  dsimp only at hc hu ⊢
  have ha2 : (2 * (k : ℤ) + 4) % 2 = 0 := by omega
  have ha4 : 4 ≤ 2 * (k : ℤ) + 4 := by omega
  by_cases he : EvenSite (2 * (2 * (k : ℤ) + 4) - y, x + 1)
  · rw [if_pos he] at hc
    by_cases hb : LadderOddEvenBlack (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - y, x + 1)
    · rw [if_pos hb] at hc
      norm_num at hc
    · exact cover_E _ x y ha2 ha4 hu he hb
  · rw [if_neg he] at hc
    by_cases hb : LadderOddOddWhite (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - y, x + 1)
    · exact cover_O _ x y ha2 ha4 hu he hb
    · rw [if_neg hb] at hc
      norm_num at hc

end FLatticePaper.TwosEPolicy
