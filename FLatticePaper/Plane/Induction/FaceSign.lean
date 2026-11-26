import FLatticePaper.Plane.Induction.CollarChain
import FLatticePaper.Plane.Induction.FaceWitness

/-! # The face of a collar centre, the sign of `Ψ` per face, and the face-restricted row input

A strict collar centre `c` lies on one of four faces of the child rectangle, read off from its collar witnesses (`CollarFrame`):

* bottom: a free H point at Chebyshev distance `≤ 1` (the disjunct `v ∈ freeH`);
* top: a free H point translated by the transverse vector (`v − transverse ∈ freeH`);
* left vertical: a free V point (`v ∈ freeV`);
* right vertical: a free V point translated by the kernel (`v − kernel ∈ freeV`).

The aligned vertical face is the left one when `ε = 1` (`W = 1`) and the right one when `ε = −1` (`W = 0`); the opposite vertical face is the other.

The numerical sign check (words of length at most 5, 358 words, the sheet field `Ψ = C − A` at every white strict collar centre) gives
`Ψ ≥ 0` on the bottom and on the aligned face, `Ψ ≤ 0` on the top and on the opposite face, with zeros only in reflected pairs.
`PsiFaceSign` is this statement (a named premise, not yet proved). `RowFaceStrictHyp` is `RowStrictHyp` restricted to centres on the
bottom or the aligned face. -/

namespace FLatticePaper.FaceSign

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank
open FLatticePaper.W1NonfreeOut FLatticePaper.CollarSquare FLatticePaper.W1SheetSquare FLatticePaper.W1PrivateSquare
open FLatticePaper.W1NonfreeHsqNonneg FLatticePaper.W1Step FLatticePaper.W1MSheet FLatticePaper.W1CollarFrame
open FLatticePaper.W1NonfreeHsqC FLatticePaper.ChainWire FLatticePaper.CollarChain FLatticePaper.FaceWitness

-- `RowFaceStrictHyp` is defined in `CollarChain` (this module imports it).

end FLatticePaper.FaceSign
