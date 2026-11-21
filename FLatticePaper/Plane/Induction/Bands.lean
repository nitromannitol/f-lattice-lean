import FLatticePaper.Plane.Induction.Sheets

/-! The two boundary bands of the closed polygon, its centre of symmetry, and the three height inputs of the
coherence step (supplement Part I; `canonical/stage1_audit/FOUR_MEMBERSHIPS_CLOSED.md`). -/

namespace FLatticePaper.Induction

open Farey

namespace ChildFrame

variable (frame : ChildFrame)

/-- The centre `R = U + V + I` of the reflection `z ↦ R − z`, with `I = (1, −1)`. -/
def centre : Site :=
  frame.child.modifiedDeck.kernel + frame.child.modifiedDeck.transverse + (1, -1)

/-- The reflection constant `κ = (L − T)/2`. -/
def symmetryConstant : ℤ :=
  (frame.child.den + frame.child.num - frame.child.periodDenominator) / 2

/-- The `H` band of `E`: the sites of `E` with `a_χ ≤ t ≤ b_χ`. -/
def hBand : Set Site :=
  {z | z ∈ frame.closedPolygon ∧
    if EvenSite z then 2 ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den + frame.child.num - 2
    else frame.child.num ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den}

/-- The `V` band of `E`: the sites of `E` with `c_χ ≤ s ≤ h_χ`. -/
def vBand : Set Site :=
  {z | z ∈ frame.closedPolygon ∧
    if EvenSite z then 0 ≤ frame.sGrade z ∧ frame.sGrade z ≤ 2 * frame.child.num
    else 2 - frame.child.den + frame.child.num ≤ frame.sGrade z ∧
      frame.sGrade z ≤ frame.child.den + frame.child.num - 2}

/-- The three height inputs of the coherence step: zero on the `H` band, the harmonic grid field on the `V`
band, and the central reflection `M(R − z) = M(z) − a·z + κ` on `E`, where `a·z = t(z)`. -/
structure HeightInputs (M : Site → ℤ) : Prop where
  zero_on_hBand : ∀ z ∈ frame.hBand, M z = 0
  harmonic_on_vBand : ∀ z ∈ frame.vBand, M z = harmonicGrid z
  reflection : ∀ z ∈ frame.closedPolygon,
    M (frame.centre - z) = M z - frame.tGrade z + frame.symmetryConstant

/-- The kernel constant `c_U = h₀(V + I) − a·(V + I) + κ` forced by the height inputs. -/
def coherentConstantU : ℤ :=
  harmonicGrid (frame.child.modifiedDeck.transverse + (1, -1)) -
    frame.tGrade (frame.child.modifiedDeck.transverse + (1, -1)) + frame.symmetryConstant

/-- The transverse constant `c_V = κ − a·R + a·V` forced by the height inputs. -/
def coherentConstantV : ℤ :=
  frame.symmetryConstant - frame.tGrade frame.centre + frame.tGrade frame.child.modifiedDeck.transverse

end ChildFrame

end FLatticePaper.Induction
