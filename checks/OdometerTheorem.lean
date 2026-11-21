import FLatticePaper.Plane.OdometerTheorem

namespace FLatticePaper.Checks

open FLatticePaper Farey

example : OdometersTheoremAt ⟨1, 2⟩ := by
  have hrot : Fraction.rotate ⟨1, 3⟩ = ⟨1, 2⟩ := by decide
  have h := (odometersTheoremAt_base (d := 3) (by norm_num)).2
  rwa [hrot] at h

#print axioms satisfiesPeriodicity_of_generatorPeriods
#print axioms odometersTheoremAt_base

end FLatticePaper.Checks
