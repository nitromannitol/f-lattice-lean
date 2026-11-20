import FLatticePaper.Plane.AlternatePeriods

namespace FLatticePaper.Checks

/-- Consume the computed rank in finite comparison on the physical plane. -/
theorem alternateCompanion_finiteComparison {α : Type*} [LinearOrder α]
    {standard competitor : Field} {rank : Site → α} (num den parentNum parentDen : ℤ)
    (hstep : HasUnitSlip standard (alternateCompanion standard num den parentNum parentDen))
    (hnoSaddle : NoEvenSlipSaddle standard (alternateCompanion standard num den parentNum parentDen))
    (hr : IsConstrainedBurningRank standard rank
      (fun center input => slipIncrement standard
        (alternateCompanion standard num den parentNum parentDen) center input ≤ 0))
    (sites : Finset Site) (bound : ℤ)
    (hf : ∀ site ∈ sites, laplacian competitor site ≤ 0)
    (hb : ∀ site ∈ incomingBoundary sites, roundedMidpoint standard
      (alternateCompanion standard num den parentNum parentDen) site - competitor site ≤ bound) :
    ∀ site ∈ sites, roundedMidpoint standard
      (alternateCompanion standard num den parentNum parentDen) site - competitor site ≤ bound :=
  (isBurningRank_alternateCompanion_midpoint num den parentNum parentDen
    hstep hnoSaddle hr).finiteComparison sites bound hf hb

example : roundedMidpoint (fun _ => -3) (fun _ => -2) (0, 0) = -2 := by decide

#print axioms roundedMidpoint_eq_neg_floor
#print axioms laplacian_roundedMidpoint
#print axioms isBurningRank_roundedMidpoint
#print axioms isBurningRank_alternateCompanion_midpoint
#print axioms roundedMidpoint_eq_min_of_slip
#print axioms alternateCompanion_finiteComparison
#print axioms roundedMidpoint_sub_standard_add_transverse
#print axioms roundedMidpoint_sub_standard_add_kernel
#print axioms not_integerAffine_roundedMidpoint_sub_standard

end FLatticePaper.Checks
