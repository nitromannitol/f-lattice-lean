import FLatticePaper.Farey.PeriodDeck
import FLatticePaper.Graph
import Mathlib.Tactic.LinearCombination

namespace FLatticePaper.Induction
open Farey

/-- A proper even child with its odd parent `N/D` and even sibling, as in supplement Part I. -/
structure ChildFrame where
  parents : Parents
  valid : parents.ValidFrame

namespace ChildFrame
variable (frame : ChildFrame)

/-- The child `n/d`. -/
def child : Fraction := frame.parents.current .even
/-- `ε = N d − D n`. -/
def eps : ℤ := frame.parents.odd.det frame.parents.even
/-- `σ = 2ε(D,N)`. -/
def shortShift : Site := (2 * frame.eps * frame.parents.odd.den, 2 * frame.eps * frame.parents.odd.num)
/-- `v = ε(N−D, N+D)`. -/
def parentShift : Site :=
  (frame.eps * (frame.parents.odd.num - frame.parents.odd.den),
    frame.eps * (frame.parents.odd.num + frame.parents.odd.den))
/-- `t(x,y) = n x − d y`. -/
def tGrade (x : Site) : ℤ := frame.child.num * x.1 - frame.child.den * x.2
/-- `s(x,y) = L x + (d − n) y`, `L = d + n`. -/
def sGrade (x : Site) : ℤ :=
  (frame.child.den + frame.child.num) * x.1 + (frame.child.den - frame.child.num) * x.2
/-- `s_p(x,y) = (D+N) x + (D−N) y`. -/
def parentSGrade (x : Site) : ℤ :=
  (frame.parents.odd.den + frame.parents.odd.num) * x.1 + (frame.parents.odd.den - frame.parents.odd.num) * x.2
/-- `c0 = (T_p − ε L_p)/2`. -/
def cutPrice : ℤ :=
  (frame.parents.odd.periodDenominator - frame.eps * (frame.parents.odd.den + frame.parents.odd.num)) / 2

end ChildFrame

/-- The harmonic grid field `h0(x,y) = (x² + 2xy − y² − 2y − par(x+y))/4`. -/
def harmonicGrid (x : Site) : ℤ :=
  (x.1 ^ 2 + 2 * x.1 * x.2 - x.2 ^ 2 - 2 * x.2 - (x.1 + x.2) % 2) / 4

/-- The numerator of `h0` is divisible by four. -/
private theorem numer_dvd (p q : ℤ) :
    ∃ k : ℤ, p ^ 2 + 2 * p * q - q ^ 2 - 2 * q - (p + q) % 2 = 4 * k := by
  obtain ⟨a, i, hi, hp⟩ : ∃ a i : ℤ, (i = 0 ∨ i = 1) ∧ p = 2 * a + i :=
    ⟨p / 2, p % 2, by omega, by omega⟩
  obtain ⟨b, j, hj, hq⟩ : ∃ b j : ℤ, (j = 0 ∨ j = 1) ∧ q = 2 * b + j :=
    ⟨q / 2, q % 2, by omega, by omega⟩
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · refine ⟨a ^ 2 + 2 * a * b - b ^ 2 - b, ?_⟩
    have hm : (p + q) % 2 = 0 := by omega
    rw [hm, hp, hq]; ring
  · refine ⟨a ^ 2 + 2 * a * b + a - b ^ 2 - 2 * b - 1, ?_⟩
    have hm : (p + q) % 2 = 1 := by omega
    rw [hm, hp, hq]; ring
  · refine ⟨a ^ 2 + a + 2 * a * b - b ^ 2, ?_⟩
    have hm : (p + q) % 2 = 1 := by omega
    rw [hm, hp, hq]; ring
  · refine ⟨a ^ 2 + 2 * a + 2 * a * b - b ^ 2 - b, ?_⟩
    have hm : (p + q) % 2 = 0 := by omega
    rw [hm, hp, hq]; ring

theorem harmonicGrid_exact (x : Site) :
    4 * harmonicGrid x = x.1 ^ 2 + 2 * x.1 * x.2 - x.2 ^ 2 - 2 * x.2 - (x.1 + x.2) % 2 := by
  obtain ⟨k, hk⟩ := numer_dvd x.1 x.2
  unfold harmonicGrid
  rw [hk]
  omega

theorem ChildFrame.eps_eq (frame : ChildFrame) :
    frame.eps = frame.parents.odd.num * frame.child.den - frame.parents.odd.den * frame.child.num := by
  simp only [ChildFrame.eps, ChildFrame.child, Parents.current, Parents.combine, Fraction.det]
  ring

theorem ChildFrame.eps_unit (frame : ChildFrame) : frame.eps = 1 ∨ frame.eps = -1 :=
  frame.valid.unit_det

theorem ChildFrame.child_even (frame : ChildFrame) : frame.child.Even :=
  frame.valid.current_even_parity

theorem ChildFrame.child_reduced (frame : ChildFrame) : frame.child.Reduced :=
  frame.valid.current_reduced .even

theorem ChildFrame.tGrade_kernel (frame : ChildFrame) :
    frame.tGrade frame.child.unmodifiedDeck.kernel = 0 := by
  show frame.child.num * frame.child.den - frame.child.den * frame.child.num = 0
  ring

theorem ChildFrame.tGrade_transverse (frame : ChildFrame) :
    frame.tGrade frame.child.unmodifiedDeck.transverse = -frame.child.periodDenominator := by
  show frame.child.num * (frame.child.num - frame.child.den) -
      frame.child.den * (frame.child.num + frame.child.den) = -frame.child.periodDenominator
  unfold Fraction.periodDenominator
  ring

theorem ChildFrame.tGrade_shortShift (frame : ChildFrame) : frame.tGrade frame.shortShift = -2 := by
  have key : frame.child.num * frame.parents.odd.den - frame.child.den * frame.parents.odd.num =
      -frame.eps := by
    rw [ChildFrame.eps_eq]
    ring
  have hsq : frame.eps ^ 2 = 1 := by
    rcases frame.eps_unit with h | h <;> rw [h] <;> norm_num
  show frame.child.num * (2 * frame.eps * frame.parents.odd.den) -
      frame.child.den * (2 * frame.eps * frame.parents.odd.num) = -2
  linear_combination (2 * frame.eps) * key - 2 * hsq

theorem ChildFrame.sGrade_kernel (frame : ChildFrame) :
    frame.sGrade frame.child.unmodifiedDeck.kernel = frame.child.periodDenominator := by
  show (frame.child.den + frame.child.num) * frame.child.den +
      (frame.child.den - frame.child.num) * frame.child.num = frame.child.periodDenominator
  unfold Fraction.periodDenominator
  ring

theorem ChildFrame.sGrade_transverse (frame : ChildFrame) :
    frame.sGrade frame.child.unmodifiedDeck.transverse = 0 := by
  show (frame.child.den + frame.child.num) * (frame.child.num - frame.child.den) +
      (frame.child.den - frame.child.num) * (frame.child.num + frame.child.den) = 0
  ring

theorem ChildFrame.parentSGrade_transverse (frame : ChildFrame) :
    frame.parentSGrade frame.child.unmodifiedDeck.transverse = -2 * frame.eps := by
  rw [ChildFrame.eps_eq]
  show (frame.parents.odd.den + frame.parents.odd.num) * (frame.child.num - frame.child.den) +
      (frame.parents.odd.den - frame.parents.odd.num) * (frame.child.num + frame.child.den) =
      -2 * (frame.parents.odd.num * frame.child.den - frame.parents.odd.den * frame.child.num)
  ring

theorem ChildFrame.shortShift_eq (frame : ChildFrame) :
    frame.shortShift = frame.eps • frame.parents.odd.modifiedDeck.kernel := by
  have hodd : (frame.parents.odd.num + frame.parents.odd.den) % 2 = 1 := frame.valid.odd_parity
  have hne : ¬ ((frame.parents.odd.num + frame.parents.odd.den) % 2 = 0) := by omega
  have hmu : frame.parents.odd.periodMultiplicity = 2 := by
    unfold Fraction.periodMultiplicity
    rw [if_neg hne]
  show (2 * frame.eps * frame.parents.odd.den, 2 * frame.eps * frame.parents.odd.num) =
    frame.eps • (frame.parents.odd.periodMultiplicity * frame.parents.odd.den,
      frame.parents.odd.periodMultiplicity * frame.parents.odd.num)
  rw [hmu]
  ext <;> simp <;> ring

theorem ChildFrame.parentShift_eq (frame : ChildFrame) :
    frame.parentShift = frame.eps • frame.parents.odd.unmodifiedDeck.transverse := by
  show (frame.eps * (frame.parents.odd.num - frame.parents.odd.den),
      frame.eps * (frame.parents.odd.num + frame.parents.odd.den)) =
    frame.eps • (frame.parents.odd.num - frame.parents.odd.den,
      frame.parents.odd.num + frame.parents.odd.den)
  ext <;> simp

theorem harmonicGrid_harmonic (x : Site) : laplacian harmonicGrid x = 0 := by
  unfold laplacian
  by_cases hE : EvenSite x
  · have hn : incomingNeg x = (x.1 - 1, x.2) := by simp [incomingNeg, hE]
    have hp : incomingPos x = (x.1 + 1, x.2) := by simp [incomingPos, hE]
    rw [hn, hp]
    have ha := harmonicGrid_exact (x.1 - 1, x.2)
    have hb := harmonicGrid_exact (x.1 + 1, x.2)
    have hx := harmonicGrid_exact x
    dsimp only at ha hb
    have m0 : (x.1 + x.2) % 2 = 0 := hE
    have m1 : (x.1 - 1 + x.2) % 2 = 1 := by omega
    have m2 : (x.1 + 1 + x.2) % 2 = 1 := by omega
    linarith
  · have hn : incomingNeg x = (x.1, x.2 - 1) := by simp [incomingNeg, hE]
    have hp : incomingPos x = (x.1, x.2 + 1) := by simp [incomingPos, hE]
    rw [hn, hp]
    have ha := harmonicGrid_exact (x.1, x.2 - 1)
    have hb := harmonicGrid_exact (x.1, x.2 + 1)
    have hx := harmonicGrid_exact x
    dsimp only at ha hb
    have hE' : ¬ ((x.1 + x.2) % 2 = 0) := hE
    have m0 : (x.1 + x.2) % 2 = 1 := by omega
    have m1 : (x.1 + (x.2 - 1)) % 2 = 0 := by omega
    have m2 : (x.1 + (x.2 + 1)) % 2 = 0 := by omega
    linarith

theorem ChildFrame.cutPrice_exact (frame : ChildFrame) :
    2 * frame.cutPrice = frame.parents.odd.periodDenominator -
      frame.eps * (frame.parents.odd.den + frame.parents.odd.num) := by
  have hodd : (frame.parents.odd.num + frame.parents.odd.den) % 2 = 1 := frame.valid.odd_parity
  have hpar : (frame.parents.odd.den - frame.parents.odd.num - frame.eps) % 2 = 0 := by
    rcases frame.eps_unit with h | h <;> rw [h] <;> omega
  have hdvd : (2 : ℤ) ∣ frame.parents.odd.periodDenominator -
      frame.eps * (frame.parents.odd.den + frame.parents.odd.num) := by
    have key : frame.parents.odd.periodDenominator -
        frame.eps * (frame.parents.odd.den + frame.parents.odd.num) =
        2 * (frame.parents.odd.den * frame.parents.odd.num) +
          (frame.parents.odd.den + frame.parents.odd.num) *
            (frame.parents.odd.den - frame.parents.odd.num - frame.eps) := by
      unfold Fraction.periodDenominator
      ring
    rw [key]
    exact dvd_add (dvd_mul_right 2 _) (Dvd.dvd.mul_left (Int.dvd_of_emod_eq_zero hpar) _)
  unfold ChildFrame.cutPrice
  exact Int.mul_ediv_cancel' hdvd

theorem ChildFrame.cutPrice_eq (frame : ChildFrame) :
    frame.cutPrice = -harmonicGrid (-frame.parentShift) := by
  have hA := frame.cutPrice_exact
  have hsq : frame.eps ^ 2 = 1 := by
    rcases frame.eps_unit with h | h <;> rw [h] <;> norm_num
  have hm : ((-frame.parentShift).1 + (-frame.parentShift).2) % 2 = 0 := by
    apply Int.emod_eq_zero_of_dvd
    exact ⟨-frame.eps * frame.parents.odd.num, by
      simp [ChildFrame.parentShift]
      ring⟩
  have hB : 4 * harmonicGrid (-frame.parentShift) =
      -2 * (frame.parents.odd.periodDenominator -
        frame.eps * (frame.parents.odd.den + frame.parents.odd.num)) := by
    rw [harmonicGrid_exact, hm]
    simp only [ChildFrame.parentShift, Prod.fst_neg, Prod.snd_neg]
    unfold Fraction.periodDenominator
    linear_combination (-2 * (frame.parents.odd.den ^ 2 + 2 * frame.parents.odd.den *
      frame.parents.odd.num - frame.parents.odd.num ^ 2)) * hsq
  linarith

end FLatticePaper.Induction
