import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Ring

namespace FLatticePaper.Farey

/-- Integer coordinates of a Farey fraction, before any rational normalization. -/
@[ext]
structure Fraction where
  num : ℤ
  den : ℤ
  deriving DecidableEq, Repr

def Fraction.InUnitInterval (fraction : Fraction) : Prop :=
  0 < fraction.den ∧ 0 ≤ fraction.num ∧ fraction.num ≤ fraction.den

def Fraction.Interior (fraction : Fraction) : Prop :=
  0 < fraction.num ∧ fraction.num < fraction.den

def Fraction.Reduced (fraction : Fraction) : Prop := IsCoprime fraction.num fraction.den

def Fraction.Odd (fraction : Fraction) : Prop := (fraction.num + fraction.den) % 2 = 1

def Fraction.Even (fraction : Fraction) : Prop := (fraction.num + fraction.den) % 2 = 0

def Fraction.det (first second : Fraction) : ℤ := first.num * second.den - second.num * first.den

theorem Fraction.det_swap (first second : Fraction) : second.det first = -first.det second := by
  unfold Fraction.det
  omega

theorem Fraction.reduced_of_det (first second : Fraction)
    (hdet : first.det second = 1 ∨ first.det second = -1) : first.Reduced := by
  rcases hdet with hdet | hdet
  · refine ⟨second.den, -second.num, ?_⟩
    rw [← hdet, Fraction.det]
    ring
  · refine ⟨-second.den, second.num, ?_⟩
    calc
      _ = -first.det second := by unfold Fraction.det; ring
      _ = 1 := by rw [hdet]; decide

inductive Digit
  | one | two | three
  deriving DecidableEq, Repr

abbrev Word := List Digit

/-- The named registers used for the two parities in one Farey pair. -/
inductive Parity
  | odd | even
  deriving DecidableEq, Repr

def Parity.flip : Parity → Parity
  | .odd => .even
  | .even => .odd

/-- The last two registers of a Farey quadruple determine its first two. -/
structure Parents where
  odd : Fraction
  even : Fraction
  deriving DecidableEq, Repr

def Parents.combine (parents : Parents) (oddCoeff evenCoeff : ℤ) : Fraction :=
  ⟨oddCoeff * parents.odd.num + evenCoeff * parents.even.num,
    oddCoeff * parents.odd.den + evenCoeff * parents.even.den⟩

def Parents.current (parents : Parents) : Parity → Fraction
  | .odd => parents.combine 1 1
  | .even => parents.combine 2 1

def Parents.retained (parents : Parents) : Parity → Fraction
  | .odd => parents.odd
  | .even => parents.even

def Parents.step (parents : Parents) : Digit → Parents
  | .one => ⟨parents.current .odd, parents.current .even⟩
  | .two => ⟨parents.current .odd, parents.even⟩
  | .three => ⟨parents.odd, parents.current .even⟩

def Parents.walk (parents : Parents) (word : Word) : Parents := word.foldl Parents.step parents

theorem Parents.walk_cons (parents : Parents) (digit : Digit) (tail : Word) :
    parents.walk (digit :: tail) = (parents.step digit).walk tail := rfl

theorem Parents.walk_append (parents : Parents) (first second : Word) :
    parents.walk (first ++ second) = (parents.walk first).walk second := List.foldl_append ..

def root : Parents := ⟨⟨0, 1⟩, ⟨1, 1⟩⟩

/-- Parent registers at a word, with current registers given by `Parents.current`. -/
def parentsAt (word : Word) : Parents := root.walk word

theorem parentsAt_append_singleton (word : Word) (digit : Digit) :
    parentsAt (word ++ [digit]) = (parentsAt word).step digit :=
  root.walk_append word [digit]

/-- The invariant of the generated frames: bounds, parities and a unit determinant. -/
structure Parents.ValidFrame (parents : Parents) : Prop where
  odd_bounds : parents.odd.InUnitInterval
  even_bounds : parents.even.InUnitInterval
  odd_parity : parents.odd.Odd
  even_parity : parents.even.Even
  unit_det : parents.odd.det parents.even = 1 ∨ parents.odd.det parents.even = -1

theorem Parents.ValidFrame.odd_reduced {parents : Parents} (valid : parents.ValidFrame) :
    parents.odd.Reduced := parents.odd.reduced_of_det parents.even valid.unit_det

theorem Parents.ValidFrame.even_reduced {parents : Parents} (valid : parents.ValidFrame) :
    parents.even.Reduced := by
  have hdet := valid.unit_det
  apply parents.even.reduced_of_det parents.odd
  rw [Fraction.det_swap]
  omega

theorem Parents.ValidFrame.current_interior {parents : Parents} (valid : parents.ValidFrame)
    (parity : Parity) : (parents.current parity).Interior := by
  obtain ⟨hoddDen, hoddNum, hoddLe⟩ := valid.odd_bounds
  obtain ⟨hevenDen, hevenNum, hevenLe⟩ := valid.even_bounds
  have hnum : 0 < parents.odd.num + parents.even.num := by
    by_contra! h
    have hoddZero : parents.odd.num = 0 := by omega
    have hevenZero : parents.even.num = 0 := by omega
    have hdet := valid.unit_det
    simp [Fraction.det, hoddZero, hevenZero] at hdet
  have hden : parents.odd.num + parents.even.num < parents.odd.den + parents.even.den := by
    by_contra! h
    have hoddEq : parents.odd.num = parents.odd.den := by omega
    have hevenEq : parents.even.num = parents.even.den := by omega
    have hdet := valid.unit_det
    simp [Fraction.det, hoddEq, hevenEq, mul_comm] at hdet
  cases parity <;> dsimp [Parents.current, Parents.combine, Fraction.Interior] <;> omega

theorem Parents.ValidFrame.current_odd_parity {parents : Parents} (valid : parents.ValidFrame) :
    (parents.current .odd).Odd := by
  have hodd := valid.odd_parity
  have heven := valid.even_parity
  dsimp [Parents.current, Parents.combine, Fraction.Odd, Fraction.Even] at *
  omega

theorem Parents.ValidFrame.current_even_parity {parents : Parents} (valid : parents.ValidFrame) :
    (parents.current .even).Even := by
  have hodd := valid.odd_parity
  have heven := valid.even_parity
  dsimp [Parents.current, Parents.combine, Fraction.Odd, Fraction.Even] at *
  omega

theorem Parents.det_step (parents : Parents) (digit : Digit) :
    (parents.step digit).odd.det (parents.step digit).even =
      (if digit = .one then -(parents.odd.det parents.even) else parents.odd.det parents.even) := by
  cases digit <;> simp [Parents.step, Parents.current, Parents.combine, Fraction.det] <;> ring

theorem Fraction.Interior.inUnitInterval {fraction : Fraction} (h : fraction.Interior) :
    fraction.InUnitInterval := by
  obtain ⟨hnum, hden⟩ := h
  exact ⟨by omega, by omega, by omega⟩

theorem Parents.ValidFrame.step {parents : Parents} (valid : parents.ValidFrame) (digit : Digit) :
    (parents.step digit).ValidFrame := by
  have hdet : (parents.step digit).odd.det (parents.step digit).even = 1 ∨
      (parents.step digit).odd.det (parents.step digit).even = -1 := by
    have hold := valid.unit_det
    rw [Parents.det_step]
    split <;> omega
  have hodd := (valid.current_interior .odd).inUnitInterval
  have heven := (valid.current_interior .even).inUnitInterval
  cases digit
  · exact ⟨hodd, heven, valid.current_odd_parity, valid.current_even_parity, hdet⟩
  · exact ⟨hodd, valid.even_bounds, valid.current_odd_parity, valid.even_parity, hdet⟩
  · exact ⟨valid.odd_bounds, heven, valid.odd_parity, valid.current_even_parity, hdet⟩

theorem Parents.ValidFrame.current_reduced {parents : Parents} (valid : parents.ValidFrame)
    (parity : Parity) : (parents.current parity).Reduced :=
  match parity with
  | .odd => (valid.step .two).odd_reduced
  | .even => (valid.step .three).even_reduced

theorem Parents.ValidFrame.walk {parents : Parents} (valid : parents.ValidFrame) (word : Word) :
    (parents.walk word).ValidFrame := by
  induction word generalizing parents with
  | nil => exact valid
  | cons digit tail ih =>
    rw [Parents.walk_cons]
    exact ih (valid.step digit)

theorem root_valid : root.ValidFrame :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩,
    rfl, rfl, Or.inr rfl⟩

theorem parentsAt_valid (word : Word) : (parentsAt word).ValidFrame := root_valid.walk word

/-- The phase used by the offset tables. -/
def phase (word : Word) : ℕ := word.count .one % 2

theorem Parents.det_walk (parents : Parents) (word : Word) :
    (parents.walk word).odd.det (parents.walk word).even =
      (-1) ^ word.count .one * parents.odd.det parents.even := by
  induction word generalizing parents with
  | nil => simp [Parents.walk]
  | cons digit tail ih =>
    rw [Parents.walk_cons, ih, Parents.det_step]
    cases digit <;> simp [pow_succ]

end FLatticePaper.Farey
