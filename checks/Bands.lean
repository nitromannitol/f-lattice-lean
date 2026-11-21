import FLatticePaper.Plane.Induction.Bands

namespace FLatticePaper.Checks

open FLatticePaper.Induction Farey

/-- At the empty word (child 1/3) the two coherent constants are those of the reciprocal staircase B1. -/
example : (⟨parentsAt [], parentsAt_valid []⟩ : ChildFrame).coherentConstantU = 0 := by decide
example : (⟨parentsAt [], parentsAt_valid []⟩ : ChildFrame).coherentConstantV = -9 := by decide

end FLatticePaper.Checks
