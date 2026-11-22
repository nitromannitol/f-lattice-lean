import FLatticePaper.Construction.AlternateIdentification

/-! Probe for task 46 (the odd-phase chart and the seventh restoration), for every odd-phase word of length at most three and
for every non-base even word w = p d whose seventh copy was checked (scripts/seventh_chart_check.py). Expected: the chart of
the odd-phase words are (1) (-4, 2), (1 3) (0, 0), (2 1) (-6, 2), (3 1) (-8, 4), (1 2 3) (-16, 2), (1 1 1) (-24, 10), (1 3 3)
(0, 0), (2 1 3) (0, 0), (2 2 1) (-8, 2), (2 3 1) (-12, 6), (3 1 3) (-16, 2), (3 2 1) (-16, 6), (3 3 1) (-12, 6); the seventh
restoration (odd parity) is (-8, 0) for (1 3 1) and (1 3 2), and zero for the others. -/

open FLatticePaper.Farey FLatticePaper FLatticePaper.Construction

#eval alternateOddChart [Digit.one, Digit.one, Digit.one]
#eval alternateOddChart [Digit.one, Digit.two, Digit.three]
#eval alternateOddChart [Digit.one, Digit.three, Digit.three]
#eval alternateOddChart [Digit.two, Digit.one, Digit.three]
#eval alternateOddChart [Digit.two, Digit.two, Digit.one]
#eval alternateOddChart [Digit.two, Digit.three, Digit.one]
#eval alternateOddChart [Digit.three, Digit.one, Digit.three]
#eval alternateOddChart [Digit.three, Digit.two, Digit.one]
#eval alternateOddChart [Digit.three, Digit.three, Digit.one]
#eval alternateRestoration [Digit.one, Digit.one, Digit.one] .odd
#eval alternateRestoration [Digit.one, Digit.two, Digit.one] .odd
#eval alternateRestoration [Digit.two, Digit.one, Digit.one] .odd
#eval alternateRestoration [Digit.three, Digit.two, Digit.one] .odd
