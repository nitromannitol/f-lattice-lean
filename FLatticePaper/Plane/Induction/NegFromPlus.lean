import FLatticePaper.Plane.Induction.ForcedCentre
import FLatticePaper.Plane.Induction.SecondarySeamEq
import FLatticePaper.Plane.Induction.NonfreeReflect

/-! # Sign `−1` of the raw-slip permit on forced edges, from sign `+1` by the centre reflection (Q34, the direct route)

For a forced edge `z → u` of the standard field, the reflection `ρ x = centre − x` carries it to a forced edge `ρ z → ρ u`
(`ForcedCentre.forced_reflect_centre`), and `D₋(x) = D₊(ρ x) − 2` (`SecondarySeamEq.slipPlus_centre_eq`). So the sign `−1` claim at
`(z, u)` is the sign `+1` claim at `(ρ z, ρ u)`. The class `N` (nonfree whites) is carried by `ρ` (premise `hNρ`; the proof is
`CollarTop.freeH_reflect` and `FreeVReflect.freeV_reflect_word`, to be supplied). -/

namespace FLatticePaper.NegFromPlus

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses

/-- **Sign `−1` from sign `+1` on the reflected edge.** -/
theorem slip_minus_of_plus {F : Field} (frame : ChildFrame) (hP : frame.Packet F)
    (N : Site → Prop) (hNρ : ∀ c, N c → N (frame.centre - c))
    (hplus : ∀ c o : Site, ForcedEdge F (fun _ _ => False) c o → N c → frame.slip F 1 o ≤ frame.slip F 1 c)
    {z u : Site} (hf : ForcedEdge F (fun _ _ => False) z u) (hz : N z) :
    frame.slip F (-1) u ≤ frame.slip F (-1) z := by
  have hf' := ForcedCentre.forced_reflect_centre frame hP hf
  have key := hplus (frame.centre - z) (frame.centre - u) hf' (hNρ z hz)
  have e1 := FLatticePaper.SecondarySeamEq.slipPlus_centre_eq frame hP u
  have e2 := FLatticePaper.SecondarySeamEq.slipPlus_centre_eq frame hP z
  linarith

/-- **Sign `−1` at a nonfree white, from sign `+1`.** The class of nonfree whites (`laplacian F c = 0` and `¬ freeClosure`) is carried
by `ρ`: the Laplacian by `ChildFrame.laplacian_reflect`, the nonfree condition by `NonfreeReflect.not_freeClosure_centre`. -/
theorem slip_minus_white_of_plus {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hP : (frameAt word).Packet (standardField word))
    (hplus : ∀ c o : Site, ForcedEdge (standardField word) (fun _ _ => False) c o →
      laplacian (standardField word) c = 0 → ¬ FLatticePaper.FreeClosure.freeClosure (frameAt word) c →
        (frameAt word).slip (standardField word) 1 o ≤ (frameAt word).slip (standardField word) 1 c)
    {z u : Site} (hf : ForcedEdge (standardField word) (fun _ _ => False) z u)
    (hz0 : laplacian (standardField word) z = 0) (hzN : ¬ FLatticePaper.FreeClosure.freeClosure (frameAt word) z) :
    (frameAt word).slip (standardField word) (-1) u ≤ (frameAt word).slip (standardField word) (-1) z := by
  refine slip_minus_of_plus (frameAt word) hP
    (fun c => laplacian (standardField word) c = 0 ∧ ¬ FLatticePaper.FreeClosure.freeClosure (frameAt word) c)
    ?_ (fun c o hf' hN => hplus c o hf' hN.1 hN.2) hf ⟨hz0, hzN⟩
  intro c hc
  refine ⟨?_, NonfreeReflect.not_freeClosure_centre h c hc.2⟩
  rw [(frameAt word).laplacian_reflect hP c]
  exact hc.1

end FLatticePaper.NegFromPlus
