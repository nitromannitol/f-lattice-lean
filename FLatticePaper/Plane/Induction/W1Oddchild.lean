import FLatticePaper.Plane.Induction.W1Hc

/-! Task 55: the Farey relation of the odd child. For an even child `w` with parents `P` (odd, the odd parent) and `Q` (even,
the even parent), the odd child `X = rotate(Q) + rotate(P)` (the sum of the rotated parents, as fractions) is the odd fraction
`((d − n)/2, (d + n)/2)` with `(d, n)` the child of `w` (`num`, `den` of `2P + Q`): so `rotate(X) = child(w)` and the
rotated parents are the parents of `X`, with `rotate(P)` the even parent of `X`. -/

namespace FLatticePaper.W1Oddchild

open Farey

/-- The rotation of an odd fraction. -/
theorem rotate_odd_num_den (P : Fraction) (hP : P.Odd) :
    P.rotate.num = P.den - P.num ∧ P.rotate.den = P.den + P.num := by
  rw [Fraction.rotate_of_odd hP]
  exact ⟨rfl, rfl⟩

/-- The rotation of an even fraction. -/
theorem rotate_even_num_den (Q : Fraction) (hQ : Q.Even) :
    Q.rotate.num = (Q.den - Q.num) / 2 ∧ Q.rotate.den = (Q.den + Q.num) / 2 := by
  have hne : ¬ ((Q.num + Q.den) % 2 = 1) := by
    have h : (Q.num + Q.den) % 2 = 0 := hQ
    omega
  unfold Fraction.rotate
  rw [if_neg hne]
  exact ⟨rfl, rfl⟩

/-- **The Farey relation of the odd child.** The sum of the rotated parents of `w` is `((d − n)/2, (d + n)/2)`, the odd
fraction whose rotation is the child `(n, d)` of `w`. -/
theorem odd_child_sum (P Q : Fraction) (hP : P.Odd) (hQ : Q.Even) :
    Q.rotate.num + P.rotate.num =
        ((2 * P.den + Q.den) - (2 * P.num + Q.num)) / 2 ∧
      Q.rotate.den + P.rotate.den = ((2 * P.den + Q.den) + (2 * P.num + Q.num)) / 2 := by
  obtain ⟨h1, h2⟩ := rotate_even_num_den Q hQ
  obtain ⟨h3, h4⟩ := rotate_odd_num_den P hP
  have hPp : (P.num + P.den) % 2 = 1 := hP
  have hQq : (Q.num + Q.den) % 2 = 0 := hQ
  rw [h1, h2, h3, h4]
  constructor <;> omega

end FLatticePaper.W1Oddchild
