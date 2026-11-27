import FLatticePaper.Tiles.SurgicalWeakOdometers
import FLatticePaper.Tiles.HorizontalEnlargedCross
import FLatticePaper.Tiles.VerticalMoreoverProof

/-! # The Section 5 Moreover hypothesis of the weak standard odometers, discharged

`SectionFiveMoreoverHyp` (`Tiles/SurgicalWeakOdometers.lean`) is the statement that the horizontal and vertical halves of the
Moreover hold for every binary word. The stacked common extension is proved on main: `horizontalMoreover_proof` and
`verticalMoreover_proof`. -/

namespace FLatticePaper.Tiles.SurgicalWeak

/-- The Section 5 Moreover hypothesis holds: both halves are proved (`horizontalMoreover_proof`, `verticalMoreover_proof`). -/
theorem sectionFiveMoreover_discharged : SectionFiveMoreoverHyp :=
  fun w => ⟨FLatticePaper.Tiles.horizontalMoreover_proof w, FLatticePaper.Tiles.verticalMoreover_proof w⟩

end FLatticePaper.Tiles.SurgicalWeak
