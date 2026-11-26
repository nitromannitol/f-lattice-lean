import FLatticePaper.Plane.Induction.ProtectedWeb
import FLatticePaper.Plane.Induction.W1Strips
import FLatticePaper.Plane.Induction.EvenWindow
import FLatticePaper.Plane.Induction.StrongEstimates
import FLatticePaper.Plane.Induction.W1Seeds

/-! # `hFreeIn` from the strong estimates (Q39, the W1 and games steps)

At the field `standardField (conjWord w)` of a word `w` whose conjugate has strong estimates and seed fields, the protected web
hypotheses are the packet strips and periods, the extended even zero strip (`W1Strips.even_zero_full`) and the odd `h_0` band
(`EvenWindow.odd_band_conj`). A forced white `c` with a free input `o` forces `o`. -/

namespace FLatticePaper.FreeInStep

open FLatticePaper FLatticePaper.Induction FLatticePaper.ProtectedWeb FLatticePaper.SquareClauses

theorem webHyp_of_strong {w : Farey.Word} (hSE : StrongEstimates (conjWord w))
    (hpar : FLatticePaper.W1Seeds.SeedFields (conjWord w)) :
    WebHyp (frameAt (conjWord w)) (standardField (conjWord w)) where
  strips := hSE.packet.strips
  inv := fun z v hv => by
    obtain ⟨i, j, rfl⟩ := hv
    exact laplacian_add_combine hSE.packet.periods z i j
  evenExt := fun z hz hlo hhi =>
    FLatticePaper.W1Strips.even_zero_full (frameAt (conjWord w)) (FLatticePaper.W1Strips.hper_of_strong hSE)
      hSE.packet.strips (fun z hz => (hSE.slipRange z hz).1) hpar.even_zero
      (FLatticePaper.W1Strips.standardField_iRefl hSE) z hz hlo hhi
  oddExt := fun z hz hlo hhi => odd_band_conj hSE hpar z hz hlo hhi

/-- **`hFreeIn`**: a forced white whose input `o` is free forces `o`, at the field of a conjugate with strong estimates. -/
theorem hFreeIn_of_strong {w : Farey.Word} (hSE : StrongEstimates (conjWord w))
    (hpar : FLatticePaper.W1Seeds.SeedFields (conjWord w)) (c i o : Site)
    (h : ForcedEdge (standardField (conjWord w)) (fun _ _ => False) c i)
    (ho : o = incomingNeg c ∨ o = incomingPos c)
    (hfo : o ∈ (frameAt (conjWord w)).freeH ∪ (frameAt (conjWord w)).freeV) : o = i :=
  freeInput_eq (webHyp_of_strong hSE hpar) h ho hfo

end FLatticePaper.FreeInStep
