import FLatticePaper.Plane.Induction.Sheets

namespace FLatticePaper.Checks

open FLatticePaper.Induction Farey

#print axioms ChildFrame.closedPolygon_covers
#print axioms ChildFrame.sheetConstant_exact

example : (1, 1) ∈ (⟨parentsAt [], parentsAt_valid []⟩ : ChildFrame).closedPolygon := by
  decide

end FLatticePaper.Checks
