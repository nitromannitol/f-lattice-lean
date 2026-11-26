import FLatticePaper.Plane.Induction.Sec3PermitRep
import FLatticePaper.Plane.Induction.CanonicalSigned
import FLatticePaper.Plane.Induction.W1Strips
import FLatticePaper.Plane.Induction.StrongCoreDef

/-! The V slip permit for free V whites `w ≠ V_end` with the policy of the canonical signed games: the premise `PrescribedAt` is
the `prescribed` field of the canonical game, and the `I`-symmetry of the conjugate's standard field is `standardField_iRefl`. -/

namespace FLatticePaper.CanonicalPermit

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.Sec3Shift

/-- The retained relation of `oldPolicyData_of_canonical` satisfies the prescription at the free points: it is the `prescribed`
field of the canonical game of that sign. -/
theorem prescribed_of_canonical {frame : ChildFrame} {F : Field} (hF : ∀ z, F (reflectionI - z) = F z)
    (G : CanonicalSignedGames frame F) (η : ℤ) (hη : η = 1 ∨ η = -1) :
    PrescribedAt frame F η (oldPolicyData_of_canonical hF G η hη).retained :=
  (G.game η hη).prescribed

/-- The standard field of the conjugate is symmetric under the reflection `z ↦ I − z`, `I = (1, −1) = reflectionI`. -/
theorem standardField_reflect {u : Word} (hSE : StrongEstimates u) (z : Site) :
    standardField u (reflectionI - z) = standardField u z := by
  have := W1Strips.standardField_iRefl hSE z
  rw [W1Strips.iRefl_eq_sub] at this
  exact this

/-- `standardField_reflect` from the core of the strong estimates. -/
theorem standardField_reflect_core {u : Word} (hSE : StrongCore u) (z : Site) :
    standardField u (reflectionI - z) = standardField u z := by
  have := W1Strips.standardField_iRefl_core hSE z
  rw [W1Strips.iRefl_eq_sub] at this
  exact this

/-- **The V slip permit with the canonical policy.** For a free V white `w ≠ V_end`, `D₊(u) ≤ D₊(w)` with `u = w + prescribedV 1 w`, for
the `OldPolicyData` of the canonical signed games of the conjugate, at the sign of the word. -/
theorem slip_permit_freeV_canonical {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hW : StrongCore word)
    (hSE : StrongEstimates (conjWord word))
    (G : CanonicalSignedGames (frameAt (conjWord word)) (standardField (conjWord word)))
    {w : Site} (hw : w ∈ (frameAt word).freeV) (hne : w ≠ (frameAt word).vLast) :
    (frameAt word).slip (standardField word) 1 (w + (frameAt word).prescribedV 1 w) ≤
      (frameAt word).slip (standardField word) 1 w := by
  have hη : (frameAt word).eps = 1 ∨ (frameAt word).eps = -1 := ChildFrame.eps_unit (frameAt word)
  exact Sec3PermitRep.slip_permit_freeV_psi h hW hSE
    (oldPolicyData_of_canonical (standardField_reflect hSE) G (frameAt word).eps hη)
    (prescribed_of_canonical (standardField_reflect hSE) G (frameAt word).eps hη) hw hne

end FLatticePaper.CanonicalPermit
