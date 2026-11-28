import FLatticePaper.Tiles.CorrectedWordCoverage
import FLatticePaper.Tiles.MixedRegisterOddOneDirectLowEven
import FLatticePaper.Tiles.MixedRegisterEvenOneDirectLowEven
import FLatticePaper.Tiles.MixedRegisterOddOneDirectLowOdd
import FLatticePaper.Tiles.MixedRegisterEvenOneDirectLowOdd
import FLatticePaper.Tiles.MixedRegisterOddOneDirectMidEven
import FLatticePaper.Tiles.MixedRegisterEvenOneDirectMidEven
import FLatticePaper.Tiles.MixedRegisterOddOneDirectMidOdd
import FLatticePaper.Tiles.MixedRegisterEvenOneDirectMidOdd
import FLatticePaper.Tiles.MixedRegisterOddOneDirectHighEven
import FLatticePaper.Tiles.MixedRegisterEvenOneDirectHighEven
import FLatticePaper.Tiles.MixedRegisterOddOneDirectHighOdd
import FLatticePaper.Tiles.MixedRegisterEvenOneDirectHighOdd

/-! The two inclusions across all three sectors and both physical parities for a fixed register orientation. -/

namespace FLatticePaper.Tiles.MixedRegisterOneDirect

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles Standard
open CorrectedRegisterDiagram CorrectedDomainLattice CorrectedRegisterWords CorrectedWordCoverage

theorem bounded (r : Register) (sec : Fin 3) (par even : Bool) (hr : Regular r true sec)
    (div : r.M ∣ r.S) (run : r.S=r.M)
    (lat : ∀ i : ℕ, (CorrectedMixedDiagram.mixed r true (-1) even i).lattice r (1) par sec) :
    Covers (fun i => (CorrectedMixedDiagram.mixed r true (-1) even i).contains r par sec) true 8 := by
  fin_cases sec <;> cases par <;> cases even
  · exact MixedRegisterOddOneDirectLowEven.coverage r hr div run fun i => lat i.val
  · exact MixedRegisterEvenOneDirectLowEven.coverage r hr div run fun i => lat i.val
  · exact MixedRegisterOddOneDirectLowOdd.coverage r hr div run fun i => lat i.val
  · exact MixedRegisterEvenOneDirectLowOdd.coverage r hr div run fun i => lat i.val
  · exact MixedRegisterOddOneDirectMidEven.coverage r hr div run fun i => lat i.val
  · exact MixedRegisterEvenOneDirectMidEven.coverage r hr div run fun i => lat i.val
  · exact MixedRegisterOddOneDirectMidOdd.coverage r hr div run fun i => lat i.val
  · exact MixedRegisterEvenOneDirectMidOdd.coverage r hr div run fun i => lat i.val
  · exact MixedRegisterOddOneDirectHighEven.coverage r hr div run fun i => lat i.val
  · exact MixedRegisterEvenOneDirectHighEven.coverage r hr div run fun i => lat i.val
  · exact MixedRegisterOddOneDirectHighOdd.coverage r hr div run fun i => lat i.val
  · exact MixedRegisterEvenOneDirectHighOdd.coverage r hr div run fun i => lat i.val

/-- Both inclusions in unbounded determinant coordinates at every actual site of
every eligible preceding word in this orientation. -/
theorem word (x : Digit) (xs : Word) (hw : ¬ IsBase (x::xs)) (even : Bool) (z : Site)
    (sign : (parentsAt (x::xs)).odd.det (parentsAt (x::xs)).even=(1)) :
    let P := parentsAt (x::xs)
    let sec := firstSector x
    let par := CorrectedCellsBands.oddSite z
    let r := register P true 1 (chart (P.current .odd) (representative z))
    let shape := CorrectedMixedDiagram.mixed r true (-1) even
    Covers (fun i => CorrectedRegisterFaces.exact ((shape i).probe r par sec)) true 8 := by
  intro P sec par r shape
  have hp : -(parentsAt (x::xs)).odd.det (parentsAt (x::xs)).even=(-1) := by omega
  have goal := CorrectedWordCoverage.mixed x xs hw true even z
  dsimp only at goal
  rw [hp] at goal
  apply goal
  exact bounded r sec par even

end FLatticePaper.Tiles.MixedRegisterOneDirect
