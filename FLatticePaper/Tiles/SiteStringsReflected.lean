import FLatticePaper.Tiles.SiteStrings

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings

/-! Task 51, step 1: the reflected consistency of the Q9 reading (`ReflectedOK`: the reversed horizontal string at the reflected origin is
the half-turn image of the forward horizontal string), decided for the standard tiles of the digit words of length at most two. -/

namespace FLatticePaper.Tiles.SiteStringsReflected

instance (w : Word) (par : Bool) : Decidable (StandardReflectedOK w par) := by
  unfold StandardReflectedOK
  infer_instance

open FLatticePaper.Tiles.SiteStrings

set_option maxHeartbeats 4000000 in
theorem refl_e_odd : StandardReflectedOK [] false := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem refl_e_even : StandardReflectedOK [] true := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem refl_1_odd : StandardReflectedOK [Digit.one] false := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem refl_1_even : StandardReflectedOK [Digit.one] true := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem refl_2_odd : StandardReflectedOK [Digit.two] false := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem refl_2_even : StandardReflectedOK [Digit.two] true := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem refl_3_odd : StandardReflectedOK [Digit.three] false := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem refl_3_even : StandardReflectedOK [Digit.three] true := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem refl_11_odd : StandardReflectedOK [Digit.one, Digit.one] false := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem refl_11_even : StandardReflectedOK [Digit.one, Digit.one] true := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem refl_12_odd : StandardReflectedOK [Digit.one, Digit.two] false := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem refl_12_even : StandardReflectedOK [Digit.one, Digit.two] true := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem refl_13_odd : StandardReflectedOK [Digit.one, Digit.three] false := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem refl_13_even : StandardReflectedOK [Digit.one, Digit.three] true := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem refl_21_odd : StandardReflectedOK [Digit.two, Digit.one] false := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem refl_21_even : StandardReflectedOK [Digit.two, Digit.one] true := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem refl_22_odd : StandardReflectedOK [Digit.two, Digit.two] false := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem refl_22_even : StandardReflectedOK [Digit.two, Digit.two] true := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem refl_23_odd : StandardReflectedOK [Digit.two, Digit.three] false := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem refl_23_even : StandardReflectedOK [Digit.two, Digit.three] true := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem refl_31_odd : StandardReflectedOK [Digit.three, Digit.one] false := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem refl_31_even : StandardReflectedOK [Digit.three, Digit.one] true := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem refl_32_odd : StandardReflectedOK [Digit.three, Digit.two] false := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem refl_32_even : StandardReflectedOK [Digit.three, Digit.two] true := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem refl_33_odd : StandardReflectedOK [Digit.three, Digit.three] false := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem refl_33_even : StandardReflectedOK [Digit.three, Digit.three] true := by decide +kernel

end FLatticePaper.Tiles.SiteStringsReflected
