import FLatticePaper.Endpoint
import FLatticePaper.Farey.Rotation
import FLatticePaper.Plane.RecurrenceRotation

namespace FLatticePaper.Checks

open Farey

private def evenBirth : Birth := ([Digit.three, .three, .one, .two], .even)

theorem rotate_mixed_birth : evenBirth.fraction.rotate = (⟨14, 19⟩ : Fraction) :=
  evenBirth.rotate_fraction.trans (by decide)

private def affineCorrection : Field := fun site => 3 * site.1 - site.2 + 4

private theorem affineCorrection_harmonic : Harmonic affineCorrection := by
  intro site
  by_cases heven : EvenSite site <;>
    simp [laplacian, affineCorrection, incomingNeg, incomingPos, heven]
  all_goals omega

private def rotatedEndpoint (direction : QuarterTurn) : Field :=
  fun site => zeroEndpoint (direction.mapSite (0, 1) site) + affineCorrection site

theorem rotatedEndpoint_rank (direction : QuarterTurn) :
    IsBurningRank (rotatedEndpoint direction)
      (fun site => checkerboardRank (direction.mapSite (0, 1) site)) := by
  have hoff : ¬ EvenSite (0, 1) := by decide
  exact zeroEndpoint_rank.quarterTurn direction (0, 1) hoff affineCorrection_harmonic

theorem rotatedEndpoint_recurrent (direction : QuarterTurn) : Recurrent (rotatedEndpoint direction) :=
  (zeroEndpoint_recurrent.quarterTurn zeroEndpoint_rank.superharmonic direction (0, 1)
    (by decide) affineCorrection_harmonic).2

theorem rotatedEndpoint_comparison {competitor : Field} (direction : QuarterTurn)
    (sites : Finset Site) (bound : ℤ) (hf : ∀ site ∈ sites, laplacian competitor site ≤ 0)
    (hb : ∀ site ∈ incomingBoundary sites,
      rotatedEndpoint direction site - competitor site ≤ bound) :
    ∀ site ∈ sites, rotatedEndpoint direction site - competitor site ≤ bound :=
  (rotatedEndpoint_rank direction).finiteComparison sites bound hf hb

#print axioms rotate_parentsAt
#print axioms Fraction.rotate_reduced
#print axioms Birth.rotate_rotate
#print axioms QuarterTurn.edge_mapSite_iff
#print axioms laplacian_quarterTurn_add_harmonic
#print axioms IsConstrainedBurningRank.quarterTurn
#print axioms exists_source_component
#print axioms recurrent_iff_allowed
#print axioms Recurrent.quarterTurn
#print axioms rotate_mixed_birth
#print axioms rotatedEndpoint_recurrent
#print axioms rotatedEndpoint_comparison
#print axioms laplacian_oneEndpoint
#print axioms oneEndpoint_recurrent

end FLatticePaper.Checks
