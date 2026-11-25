import FLatticePaper.Plane.Induction.Q3VStar
import FLatticePaper.Plane.Induction.S3FreeBoundary
import FLatticePaper.Plane.Induction.NativeGrade

/-! Task w3, step 1(b), first part: the V window of the transport query.

For the word with odd parent `N/D` (`1 ≤ N < D`), the query `Z x = (−x₂, x₁ − 1)` lies on the conjugate's V grade line with
`sGrade' (Z x) = 2 t_p(x) − 2N`, `t_p(x) = N x₁ − D x₂` (`ChildFrame.sGrade` of the conjugate child `b/r = (D−N)/(D+N)`).
Its V spectrum holds exactly when `1 ≤ t_p(x) ≤ r − 1`, `r = D + N`. The H-form of the query is `t_p(x) = r` (`NativeGrade`). -/

namespace FLatticePaper.QueryGrade

open Farey FLatticePaper FLatticePaper.Induction

/-- The transport query `Z x = (−x₂, x₁ − 1)`. -/
def zq (x : ℤ × ℤ) : ℤ × ℤ := (-x.2, x.1 - 1)

/-- **The conjugate's sGrade at the query:** `s'(Z x) = 2 t_p(x) − 2N`. -/
theorem sGrade_zq_conj {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (x : ℤ × ℤ) :
    (frameAt (conjWord word)).sGrade (zq x) =
      2 * ((frameAt word).parents.odd.num * x.1 - (frameAt word).parents.odd.den * x.2) -
        2 * (frameAt word).parents.odd.num := by
  obtain ⟨hcn, hcd⟩ := frameAt_conj_num_den h
  unfold ChildFrame.sGrade zq
  rw [hcn, hcd]
  ring

/-- **The V window of the query:** `vSpectrum'(s'(Z x))` iff `1 ≤ t_p(x) ≤ r − 1`, for `1 ≤ N`. -/
theorem vSpectrum_zq_iff {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (x : ℤ × ℤ)
    (hN : 1 ≤ (frameAt word).parents.odd.num) :
    (frameAt (conjWord word)).vSpectrum ((frameAt (conjWord word)).sGrade (zq x)) ↔
      1 ≤ (frameAt word).parents.odd.num * x.1 - (frameAt word).parents.odd.den * x.2 ∧
        (frameAt word).parents.odd.num * x.1 - (frameAt word).parents.odd.den * x.2 ≤
          (frameAt word).parents.odd.den + (frameAt word).parents.odd.num - 1 := by
  obtain ⟨hcn, hcd⟩ := frameAt_conj_num_den h
  rw [sGrade_zq_conj h x]
  unfold ChildFrame.vSpectrum
  rw [hcn, hcd]
  omega

end FLatticePaper.QueryGrade
