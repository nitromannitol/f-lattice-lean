import FLatticePaper.Plane.OdometerTheorem

/-! The statement of `theorem:odometers` for every reduced interior slope, kept apart from the consequences
in `FLatticePaper.MainTheorems` so that the induction files can refer to it without importing those consequences. -/

namespace FLatticePaper

open Farey

/-- `theorem:odometers` for every reduced fraction `0 < n/d < 1`. -/
def OdometersTheorem : Prop :=
  ∀ fraction : Fraction, fraction.Interior → fraction.Reduced → OdometersTheoremAt fraction

end FLatticePaper
