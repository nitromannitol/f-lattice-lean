import FLatticePaper.Plane.Induction.TwosBlackOdd

/-! Twos flatness, black centres on the even sites: the black set of the twos field at an even native site, in coordinates.

At an even native site `(x, y)` (so `x + y` even) the quarter turn `(2a - y, x + 1)` is odd, and the charge is `-1` exactly when
the odd-odd white predicate `LadderOddOddWhite` fails there. Written out, the white set is the union of ten explicit pieces
(two lines `x = -1`, `x = 0`, `x = a+1`, `x = a`, the diagonals `y - x ∈ {2a, -2, a, a-2}`, and the two points `(0, 2a)`, `(a, a-2)`). -/

noncomputable section

namespace FLatticePaper.TwosEPolicy

open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey
open scoped Classical

/-- At an even native site, the twos charge is `-1` exactly when `LadderOddOddWhite` fails at the turned point. -/
theorem lap_even_black_iff (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y) (hp : (x + y) % 2 = 0) :
    laplacian (standardField (List.replicate (k + 1) Digit.two)) (x, y) = -1 ↔
      ¬ LadderOddOddWhite (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - y, x + 1) := by
  rw [laplacian_twos_native k hagree hperiod hn]
  simp only [rot_twos_ccw]
  have he : ¬ EvenSite (2 * (2 * (k : ℤ) + 4) - y, x + 1) := by
    unfold EvenSite
    dsimp only
    omega
  rw [if_neg he]
  by_cases h : LadderOddOddWhite (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - y, x + 1)
  · simp [h]
  · simp [h]

/-- The even black set in coordinates: the complement of the ten explicit white pieces. -/
theorem even_black_explicit (a x y : ℤ) :
    ¬ LadderOddOddWhite a (2 * a - y, x + 1) ↔
      ¬ ((y - x = 2 * a ∧ 1 ≤ x ∧ x ≤ a - 2) ∨ (x = -1 ∧ a + 1 ≤ y ∧ y ≤ 2 * a - 1) ∨
        (x = 0 ∧ 0 ≤ y ∧ y ≤ a) ∨ (y - x = -2 ∧ 2 ≤ x ∧ x ≤ a - 1) ∨
        (x = a + 1 ∧ a - 1 ≤ y ∧ y ≤ 2 * a - 3) ∨ (x = a ∧ 2 * a - 2 ≤ y ∧ y ≤ 3 * a - 2) ∨
        (y - x = a ∧ 0 ≤ x ∧ x ≤ a - 2) ∨ (y - x = a - 2 ∧ 2 ≤ x ∧ x ≤ a) ∨
        (x = 0 ∧ y = 2 * a) ∨ (x = a ∧ y = a - 2)) := by
  simp only [LadderOddOddWhite, LadderOddLowerBoundary, reflectLadderOdd, Prod.mk_sub_mk]
  constructor <;> intro h <;> omega

/-- The black-even explicit set, as a hypothesis: the even site is not in any white piece. -/
abbrev EvenWhitePiece (a x y : ℤ) : Prop :=
  (y - x = 2 * a ∧ 1 ≤ x ∧ x ≤ a - 2) ∨ (x = -1 ∧ a + 1 ≤ y ∧ y ≤ 2 * a - 1) ∨
  (x = 0 ∧ 0 ≤ y ∧ y ≤ a) ∨ (y - x = -2 ∧ 2 ≤ x ∧ x ≤ a - 1) ∨
  (x = a + 1 ∧ a - 1 ≤ y ∧ y ≤ 2 * a - 3) ∨ (x = a ∧ 2 * a - 2 ≤ y ∧ y ≤ 3 * a - 2) ∨
  (y - x = a ∧ 0 ≤ x ∧ x ≤ a - 2) ∨ (y - x = a - 2 ∧ 2 ≤ x ∧ x ≤ a) ∨
  (x = 0 ∧ y = 2 * a) ∨ (x = a ∧ y = a - 2)

/-- The white piece 1 of `EvenWhitePiece`. -/
theorem ewp_1 {a x y : ℤ} (h : y - x = 2 * a ∧ 1 ≤ x ∧ x ≤ a - 2) : EvenWhitePiece a x y :=
  Or.inl h

/-- The white piece 2 of `EvenWhitePiece`. -/
theorem ewp_2 {a x y : ℤ} (h : x = -1 ∧ a + 1 ≤ y ∧ y ≤ 2 * a - 1) : EvenWhitePiece a x y :=
  Or.inr (Or.inl h)

/-- The white piece 3 of `EvenWhitePiece`. -/
theorem ewp_3 {a x y : ℤ} (h : x = 0 ∧ 0 ≤ y ∧ y ≤ a) : EvenWhitePiece a x y :=
  Or.inr (Or.inr (Or.inl h))

/-- The white piece 4 of `EvenWhitePiece`. -/
theorem ewp_4 {a x y : ℤ} (h : y - x = -2 ∧ 2 ≤ x ∧ x ≤ a - 1) : EvenWhitePiece a x y :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

/-- The white piece 5 of `EvenWhitePiece`. -/
theorem ewp_5 {a x y : ℤ} (h : x = a + 1 ∧ a - 1 ≤ y ∧ y ≤ 2 * a - 3) : EvenWhitePiece a x y :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

/-- The white piece 6 of `EvenWhitePiece`. -/
theorem ewp_6 {a x y : ℤ} (h : x = a ∧ 2 * a - 2 ≤ y ∧ y ≤ 3 * a - 2) : EvenWhitePiece a x y :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

/-- The white piece 7 of `EvenWhitePiece`. -/
theorem ewp_7 {a x y : ℤ} (h : y - x = a ∧ 0 ≤ x ∧ x ≤ a - 2) : EvenWhitePiece a x y :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))

/-- The white piece 8 of `EvenWhitePiece`. -/
theorem ewp_8 {a x y : ℤ} (h : y - x = a - 2 ∧ 2 ≤ x ∧ x ≤ a) : EvenWhitePiece a x y :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))

/-- The white piece 9 of `EvenWhitePiece`. -/
theorem ewp_9 {a x y : ℤ} (h : x = 0 ∧ y = 2 * a) : EvenWhitePiece a x y :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))

/-- The white piece 10 of `EvenWhitePiece`. -/
theorem ewp_10 {a x y : ℤ} (h : x = a ∧ y = a - 2) : EvenWhitePiece a x y :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h)))))))))


end FLatticePaper.TwosEPolicy
