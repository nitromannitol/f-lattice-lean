import FLatticePaper.Tiles.SiteStrings

/-! Task 51, step 1 (base cases): the Q9 four-string predicate decided for the standard tiles of all digit words of length at most two,
both parities (the pure words `2`, `3`, `22`, `33` and the empty word among them), by kernel evaluation of `decide +kernel` (each
theorem costs about 90 seconds of kernel time; the words of length three and four are not decided at this cost). -/


namespace FLatticePaper.Tiles.SiteStringsDecide

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Tiles.Standard

set_option maxHeartbeats 4000000 in
theorem fs_e_odd : StandardFourStrings [] false := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem fs_e_even : StandardFourStrings [] true := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem fs_1_odd : StandardFourStrings [Digit.one] false := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem fs_1_even : StandardFourStrings [Digit.one] true := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem fs_2_odd : StandardFourStrings [Digit.two] false := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem fs_2_even : StandardFourStrings [Digit.two] true := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem fs_3_odd : StandardFourStrings [Digit.three] false := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem fs_3_even : StandardFourStrings [Digit.three] true := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem fs_11_odd : StandardFourStrings [Digit.one, Digit.one] false := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem fs_11_even : StandardFourStrings [Digit.one, Digit.one] true := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem fs_12_odd : StandardFourStrings [Digit.one, Digit.two] false := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem fs_12_even : StandardFourStrings [Digit.one, Digit.two] true := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem fs_13_odd : StandardFourStrings [Digit.one, Digit.three] false := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem fs_13_even : StandardFourStrings [Digit.one, Digit.three] true := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem fs_21_odd : StandardFourStrings [Digit.two, Digit.one] false := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem fs_21_even : StandardFourStrings [Digit.two, Digit.one] true := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem fs_22_odd : StandardFourStrings [Digit.two, Digit.two] false := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem fs_22_even : StandardFourStrings [Digit.two, Digit.two] true := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem fs_23_odd : StandardFourStrings [Digit.two, Digit.three] false := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem fs_23_even : StandardFourStrings [Digit.two, Digit.three] true := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem fs_31_odd : StandardFourStrings [Digit.three, Digit.one] false := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem fs_31_even : StandardFourStrings [Digit.three, Digit.one] true := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem fs_32_odd : StandardFourStrings [Digit.three, Digit.two] false := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem fs_32_even : StandardFourStrings [Digit.three, Digit.two] true := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem fs_33_odd : StandardFourStrings [Digit.three, Digit.three] false := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem fs_33_even : StandardFourStrings [Digit.three, Digit.three] true := by decide +kernel

-- The predicate is not vacuous: the empty strings do not cover the inner boundary of the odd tile of the empty word.
set_option maxHeartbeats 4000000 in
theorem fs_nonvacuous : ¬ FourStrings (oddTile []) [] [] := by decide +kernel

end FLatticePaper.Tiles.SiteStringsDecide
