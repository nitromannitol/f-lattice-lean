import FLatticePaper.Plane.Induction.PlusAdjacent
import FLatticePaper.Plane.Induction.StrongCoreDef

/-! # W4 (Q34): the sign `−1` slip at an `A`-root in the adjacent chart, as `−min(a, B)`

With `uq = ε U_q` and `v` a site with `v` and `v + uq` in the closed polygon, the sign `−1` slip is the adjacent difference
`D₋(v) = F v − F (v + uq)` (kernel periodicity, both signs of `ε`). When `Ψ v ≥ 0` (so `F v = A v`) and `F (v + uq) = min(A, C)`,

  `D₋(v) = − min(a v, B v)`,  with `a v = A(v + uq) − A v` and `B v = C(v + uq) − A v`,

which are the two sheet quantities of `RawB` (`a_unit_bound`, `hbmono_of_raw`). So the sign `−1` permit at an edge `c → i` with
both endpoints `A`-roots reduces to the comparison of `min(a, B)`: this file proves the identity only; the reduction and the
a-fall exclusion are separate. -/

namespace FLatticePaper.SignMinusAdjacent

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1MSheet FLatticePaper.W1Step

/-- **The sign `−1` slip is the adjacent difference:** `D₋(v) = F v − F (v + uq)`. -/
theorem slip_minus_one_eq_uq {word : Word} (hW : StrongCore word) (v : Site) :
    (frameAt word).slip (standardField word) (-1) v =
      standardField word v - standardField word (v + (frameAt word).uq) := by
  unfold ChildFrame.slip
  rw [neg_one_smul, Sec3Shift.shortShift_eq_eps_Upar word]
  have hK := Sec3Shift.child_kernel_eq word
  rcases ChildFrame.eps_unit (frameAt word) with he | he
  · rw [he, one_smul]
    unfold ChildFrame.uq
    rw [he, one_mul, one_mul]
    congr 1
    have e : v + -Upar word = (v + ((frameAt word).parents.even.den, (frameAt word).parents.even.num)) -
        (frameAt word).child.modifiedDeck.kernel := by
      rw [hK]
      unfold Fraction.unmodifiedDeck
      ext <;> simp <;> ring
    rw [e, PlusAdjacent.kernel_period_sub hW]
  · rw [he, neg_one_smul, neg_neg]
    unfold ChildFrame.uq
    rw [he, neg_one_mul, neg_one_mul]
    congr 1
    have e : v + Upar word = (v + (-(frameAt word).parents.even.den, -(frameAt word).parents.even.num)) +
        (frameAt word).child.modifiedDeck.kernel := by
      rw [hK]
      unfold Fraction.unmodifiedDeck
      ext <;> simp <;> ring
    rw [e, Sec3Shift.kernel_period hW]

/-- **The sign `−1` adjacent identity:** at an `A`-root `z` (`Ψ z ≥ 0`) with `z + uq` in the closed polygon,
`D₋(z) = − min(a z, B z)`, the two sheet quantities of `RawB`. -/
theorem slip_minus_adj_eq {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hW : StrongCore word)
    (hSE : StrongEstimates (conjWord word)) {z : Site}
    (hz : z ∈ (frameAt word).closedPolygon) (hzu : z + (frameAt word).uq ∈ (frameAt word).closedPolygon)
    (hΨ : 0 ≤ sheetPsi word z) :
    (frameAt word).slip (standardField word) (-1) z =
      -min ((frameAt word).sheetA (FqW word) (z + (frameAt word).uq) - (frameAt word).sheetA (FqW word) z)
        ((frameAt word).sheetC (FqW word) (z + (frameAt word).uq) - (frameAt word).sheetA (FqW word) z) := by
  rw [slip_minus_one_eq_uq hW z, PlusAdjacent.F_eq_sheetA_of_psi_nonneg h hSE hz hΨ,
    standardField_eq_sheetMin_of_strong h hSE hzu]
  unfold ChildFrame.sheetMin
  simp only [FqW] at *
  omega

end FLatticePaper.SignMinusAdjacent
