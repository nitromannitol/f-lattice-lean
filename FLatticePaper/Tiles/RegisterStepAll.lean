import FLatticePaper.Tiles.RegisterStep
import FLatticePaper.Tiles.StandardAll
import FLatticePaper.Tiles.ArcOKAll

/-! Task Q25, S2 for every word. `RegisterStep.S2_of_named` takes the standard boundary statement of the odd and even
tiles and the arc data `ArcOK` of the bottom and right words as named inputs; both are now proved for every word
(`StandardAll.standardBoundaryWord_all`, `ArcOKAll.arcOK_odd_all`, `ArcOKAll.arcOK_even_all`). -/

namespace FLatticePaper.Tiles.RegisterStepAll

open FLatticePaper FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.RegisterInduction
  FLatticePaper.Tiles.RegisterStep FLatticePaper.Tiles.StandardAll

/-- S2 at every word: the odd and even registers are the first arcs of the boundaries of the standard tiles. -/
theorem S2_every (w : Word) : S2 w :=
  S2_of_named (fun s => (standardBoundaryWord_all s).1) (fun s => (standardBoundaryWord_all s).2)
    ArcOKAll.arcOK_odd_all ArcOKAll.arcOK_even_all w

end FLatticePaper.Tiles.RegisterStepAll
