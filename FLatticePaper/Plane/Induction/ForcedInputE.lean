import FLatticePaper.Plane.Induction.W4White
import FLatticePaper.Plane.Induction.SquareClauses

/-! # The forced input of a strict-interior white lies in the closed polygon

A forced edge `c → o` with the unseeded derivation has `o` an input of `c` (`ForcedEdge.unit`), and at a strict-interior centre both inputs
lie in the closed polygon (`W4White.strict_neighbours_mem`). The seed case is empty for the unseeded derivation. -/

namespace FLatticePaper.ForcedInputE

open FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses

/-- **The forced input of a strict centre is in the polygon.** -/
theorem forced_input_mem_E {F : Field} (frame : ChildFrame) {c o : Site}
    (hSI : FLatticePaper.W1.StrictInterior frame.child.num frame.child.den c)
    (hf : ForcedEdge F (fun _ _ => False) c o) : o ∈ frame.closedPolygon := by
  cases hf with
  | seed hs => exact hs.elim
  | unit inside hc hw ho hout hin hforced =>
    rcases ho with rfl | rfl
    · exact (FLatticePaper.W4White.strict_neighbours_mem frame hSI).1
    · exact (FLatticePaper.W4White.strict_neighbours_mem frame hSI).2

end FLatticePaper.ForcedInputE
