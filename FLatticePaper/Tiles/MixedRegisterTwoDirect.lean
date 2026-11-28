import FLatticePaper.Tiles.CorrectedWordCoverage
import FLatticePaper.Tiles.MixedRegisterOddTwoDirectLowEven
import FLatticePaper.Tiles.MixedRegisterEvenTwoDirectLowEven
import FLatticePaper.Tiles.MixedRegisterOddTwoDirectLowOdd
import FLatticePaper.Tiles.MixedRegisterEvenTwoDirectLowOdd
import FLatticePaper.Tiles.MixedRegisterOddTwoDirectMidEven
import FLatticePaper.Tiles.MixedRegisterEvenTwoDirectMidEven
import FLatticePaper.Tiles.MixedRegisterOddTwoDirectMidOdd
import FLatticePaper.Tiles.MixedRegisterEvenTwoDirectMidOdd
import FLatticePaper.Tiles.MixedRegisterOddTwoDirectHighEven
import FLatticePaper.Tiles.MixedRegisterEvenTwoDirectHighEven
import FLatticePaper.Tiles.MixedRegisterOddTwoDirectHighOdd
import FLatticePaper.Tiles.MixedRegisterEvenTwoDirectHighOdd

/-! The two inclusions across all three sectors and both physical parities for a fixed register orientation. -/

namespace FLatticePaper.Tiles.MixedRegisterTwoDirect

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles Standard
open CorrectedRegisterDiagram CorrectedDomainLattice CorrectedRegisterWords CorrectedWordCoverage

theorem bounded (r : Register) (sec : Fin 3) (par even : Bool) (hr : Regular r false sec)
    (div : r.M ∣ r.S) (run : r.S=r.M)
    (lat : ∀ i : ℕ, (CorrectedMixedDiagram.mixed r false (-1) even i).lattice r (-1) par sec) :
    Covers (fun i => (CorrectedMixedDiagram.mixed r false (-1) even i).contains r par sec) true (if even then 8 else 6) := by
  fin_cases sec <;> cases par <;> cases even
  · exact MixedRegisterOddTwoDirectLowEven.coverage r hr div run fun i => lat i.val
  · exact MixedRegisterEvenTwoDirectLowEven.coverage r hr div run fun i => lat i.val
  · exact MixedRegisterOddTwoDirectLowOdd.coverage r hr div run fun i => lat i.val
  · exact MixedRegisterEvenTwoDirectLowOdd.coverage r hr div run fun i => lat i.val
  · exact MixedRegisterOddTwoDirectMidEven.coverage r hr div run fun i => lat i.val
  · exact MixedRegisterEvenTwoDirectMidEven.coverage r hr div run fun i => lat i.val
  · exact MixedRegisterOddTwoDirectMidOdd.coverage r hr div run fun i => lat i.val
  · exact MixedRegisterEvenTwoDirectMidOdd.coverage r hr div run fun i => lat i.val
  · exact MixedRegisterOddTwoDirectHighEven.coverage r hr div run fun i => lat i.val
  · exact MixedRegisterEvenTwoDirectHighEven.coverage r hr div run fun i => lat i.val
  · exact MixedRegisterOddTwoDirectHighOdd.coverage r hr div run fun i => lat i.val
  · exact MixedRegisterEvenTwoDirectHighOdd.coverage r hr div run fun i => lat i.val

/-- Both inclusions in unbounded determinant coordinates at every actual site of
every eligible preceding word in this orientation. -/
theorem word (x : Digit) (xs : Word) (hw : ¬ IsBase (x::xs)) (even : Bool) (z : Site)
    (sign : (parentsAt (x::xs)).odd.det (parentsAt (x::xs)).even=(1)) :
    let P := parentsAt (x::xs)
    let sec := firstSector x
    let par := CorrectedCellsBands.oddSite z
    let r := register P false 1 (chart (P.current .odd) (representative z))
    let shape := CorrectedMixedDiagram.mixed r false (-1) even
    Covers (fun i => CorrectedRegisterFaces.exact ((shape i).probe r par sec)) true (if even then 8 else 6) := by
  intro P sec par r shape
  have hp : -(parentsAt (x::xs)).odd.det (parentsAt (x::xs)).even=(-1) := by omega
  have goal := CorrectedWordCoverage.mixed x xs hw false even z
  dsimp only at goal
  rw [hp] at goal
  apply goal
  exact bounded r sec par even

end FLatticePaper.Tiles.MixedRegisterTwoDirect
