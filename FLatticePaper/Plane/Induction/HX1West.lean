import FLatticePaper.Plane.Induction.ShortPassages
import FLatticePaper.Plane.Induction.EvenVSquare

/-! # The west instances of the neighbour facts `hX1`, `hX2` of an even free V root, on the west band

For an even root `z` of the V arc, `hX1` (δ = −1) asks that `z + (−1, 0)` has laplacian `−1`, or is nonfree with laplacian `0`, and
`hX2` (δ = −1) asks the same of the diagonal `z + (−1, 1)`. The field is binary (`Packet.binary`), so a nonfree middle satisfies the
dichotomy outright. On the west band `2 ≤ s ≤ 2n − 2`, `2(n+d) − 1 − P < t < n` (`P` the period denominator), the middles are nonfree by
`ShortPassages.V_WNE_middle0_nonfree` and `V_WNE_middle1_nonfree`. The complementary even V roots are not covered here. -/

namespace FLatticePaper.HX1West

open FLatticePaper FLatticePaper.Induction FLatticePaper.Farey

/-- A binary field's neighbour satisfies the `hX1`-type dichotomy at a nonfree site. -/
theorem dichotomy_of_nonfree {frame : ChildFrame} {G : Field} (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0)
    {c : Site} (hnf : Nonfree frame c) : laplacian G c = -1 ∨ (laplacian G c = 0 ∧ Nonfree frame c) :=
  (hbin c).imp id (fun h => ⟨h, hnf⟩)

/-- The west instance of `hX1` on the west band: the west neighbour `(z.1 − 1, z.2)` of an even V root. -/
theorem hX1_west_band {frame : ChildFrame} {G : Field} (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0)
    {z : Site} (hev : EvenSite z)
    (hS1 : 2 ≤ frame.sGrade z) (hS2 : frame.sGrade z ≤ 2 * frame.child.num - 2)
    (ht1 : 2 * (frame.child.num + frame.child.den) - 1 - frame.child.periodDenominator < frame.tGrade z)
    (ht2 : frame.tGrade z < frame.child.num) :
    laplacian G (z.1 + -1, z.2) = -1 ∨ (laplacian G (z.1 + -1, z.2) = 0 ∧ Nonfree frame (z.1 + -1, z.2)) := by
  have hnf : Nonfree frame (z.1 + -1, z.2) := by
    have h := FLatticePaper.Induction.ShortPassages.V_WNE_middle0_nonfree frame z hev hS1 hS2 ht1 ht2
    have e : z + (-1, 0) = (z.1 + -1, z.2) := by
      ext <;> simp
    rwa [e] at h
  exact dichotomy_of_nonfree hbin hnf

/-- The west instance of `hX2` on the west band: the diagonal `(z.1 − 1, z.2 + 1)` of an even V root. -/
theorem hX2_west_band {frame : ChildFrame} {G : Field} (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0)
    {z : Site} (hev : EvenSite z)
    (hS1 : 2 ≤ frame.sGrade z) (hS2 : frame.sGrade z ≤ 2 * frame.child.num - 2)
    (ht1 : 2 * (frame.child.num + frame.child.den) - 1 - frame.child.periodDenominator < frame.tGrade z)
    (ht2 : frame.tGrade z < frame.child.num) :
    laplacian G (z.1 + -1, z.2 - -1) = -1 ∨ (laplacian G (z.1 + -1, z.2 - -1) = 0 ∧ Nonfree frame (z.1 + -1, z.2 - -1)) := by
  have hnf : Nonfree frame (z.1 + -1, z.2 - -1) := by
    have h := FLatticePaper.Induction.ShortPassages.V_WNE_middle1_nonfree frame z hev hS1 hS2 ht1 ht2
    have e : z + (-1, 1) = (z.1 + -1, z.2 - -1) := by
      ext <;> simp [sub_neg_eq_add]
    rwa [e] at h
  exact dichotomy_of_nonfree hbin hnf

end FLatticePaper.HX1West
