import FLatticePaper.FlatPlusHeadline
import FLatticePaper.FlatMinusHeadline
import FLatticePaper.TraceHeadline
import FLatticePaper.MainTheorems
import FLatticePaper.Plane.GlobalOdometersAll

/-! The axiom report of the headline declarations. CI compiles this file with `lake env lean` and requires the three standard
axioms `propext`, `Classical.choice` and `Quot.sound` (and no `sorryAx`) for each report. -/

#print axioms FLatticePaper.odometersTheorem_no_flatP
#print axioms FLatticePaper.odometersTheorem_no_flat
#print axioms FLatticePaper.odometersTheorem_no_hbd
#print axioms FLatticePaper.hyperbola_of_odometersTheorem
#print axioms FLatticePaper.circlePacking_of_odometersTheorem
#print axioms FLatticePaper.GlobalOdometers.global_odometers_all
