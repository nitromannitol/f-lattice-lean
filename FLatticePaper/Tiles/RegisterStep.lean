import FLatticePaper.Tiles.RegisterIdentity
import FLatticePaper.Tiles.RegisterTiles
import FLatticePaper.Tiles.StandardBoundary

/-! Task Q25 (c), the S2 step of the register-to-tile link.

`RegisterInduction.S2 w` says that the odd (even) register of `w` is the first arc of the boundary of the odd (even)
register tile of `w`, with the arc data `ArcOK`. The register tile is the standard tile of the source
(`RegisterTiles.tOdd_eq_oddTile`, `tEven_eq_evenTile`), and the register is the bottom edge of the source
(`RegisterIdentity.regsAfter_fst`, `regsAfter_snd`). So S2 at every word follows from the standard boundary statement of the
odd and even tiles at every word (`StandardBoundaryOdd`, `StandardBoundaryEven`) and the arc data of the bottom and right
words of every word. These four facts are the named inputs of this module; they are the seam of Q25 (d)-(f) and the arc
(sum and pattern) facts, which are not proved here. -/

namespace FLatticePaper.Tiles.RegisterStep

open FLatticePaper FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.RecursionIdentity
  FLatticePaper.Tiles.RegisterInduction FLatticePaper.Tiles.RegisterLink FLatticePaper.Tiles.RegisterIdentity
  FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.RegisterTiles

/-- The odd half of S2 from the named standard boundary and arc facts. -/
theorem S2odd_of_named (hO : ∀ s : Word, StandardBoundaryOdd s)
    (hA : ∀ s : Word, ArcOK (oddBottom s) (oddRight s)) (w : Word) : S2odd w := by
  intro h
  refine ⟨oddRight (srcOf w).1, ?_, ?_⟩
  · rw [regsAfter_fst w h]
    exact hA (srcOf w).1
  · rw [tOdd_eq_oddTile w h, regsAfter_fst w h]
    exact hO (srcOf w).1

/-- The even half of S2 from the named standard boundary and arc facts. -/
theorem S2even_of_named (hE : ∀ s : Word, StandardBoundaryEven s)
    (hA : ∀ s : Word, ArcOK (evenBottom s) (evenRight s)) (w : Word) : S2even w := by
  intro h
  refine ⟨evenRight (srcOf w).2, ?_, ?_⟩
  · rw [regsAfter_snd w h]
    exact hA (srcOf w).2
  · rw [tEven_eq_evenTile w h, regsAfter_snd w h]
    exact hE (srcOf w).2

/-- S2 at every word from the named standard boundary and arc facts. -/
theorem S2_of_named (hO : ∀ s : Word, StandardBoundaryOdd s) (hE : ∀ s : Word, StandardBoundaryEven s)
    (hAo : ∀ s : Word, ArcOK (oddBottom s) (oddRight s)) (hAe : ∀ s : Word, ArcOK (evenBottom s) (evenRight s))
    (w : Word) : S2 w :=
  ⟨S2odd_of_named hO hAo w, S2even_of_named hE hAe w⟩

/-- The child step `S2 pre → S2 (pre ++ [d])` of `RegisterInduction.S2_all`, from the named facts (the step holds
for every prefix, since S2 holds for every word). -/
theorem S2_step_of_named (hO : ∀ s : Word, StandardBoundaryOdd s) (hE : ∀ s : Word, StandardBoundaryEven s)
    (hAo : ∀ s : Word, ArcOK (oddBottom s) (oddRight s)) (hAe : ∀ s : Word, ArcOK (evenBottom s) (evenRight s))
    (pre : Word) (d : Digit) (_ : S2 pre) : S2 (pre ++ [d]) :=
  S2_of_named hO hE hAo hAe (pre ++ [d])

end FLatticePaper.Tiles.RegisterStep
