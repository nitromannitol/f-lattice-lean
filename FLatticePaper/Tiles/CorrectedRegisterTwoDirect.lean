import FLatticePaper.Tiles.CorrectedWordCoverage
import FLatticePaper.Tiles.CorrectedRegisterShortTwoDirectLowEven
import FLatticePaper.Tiles.CorrectedRegisterLongTwoDirectLowEven
import FLatticePaper.Tiles.CorrectedRegisterShortTwoDirectLowOdd
import FLatticePaper.Tiles.CorrectedRegisterLongTwoDirectLowOdd
import FLatticePaper.Tiles.CorrectedRegisterShortTwoDirectMidEven
import FLatticePaper.Tiles.CorrectedRegisterLongTwoDirectMidEven
import FLatticePaper.Tiles.CorrectedRegisterShortTwoDirectMidOdd
import FLatticePaper.Tiles.CorrectedRegisterLongTwoDirectMidOdd
import FLatticePaper.Tiles.CorrectedRegisterShortTwoDirectHighEven
import FLatticePaper.Tiles.CorrectedRegisterLongTwoDirectHighEven
import FLatticePaper.Tiles.CorrectedRegisterShortTwoDirectHighOdd
import FLatticePaper.Tiles.CorrectedRegisterLongTwoDirectHighOdd

/-! The two inclusions across all three sectors and both physical parities for a fixed register orientation. -/

namespace FLatticePaper.Tiles.CorrectedRegisterTwoDirect

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles Standard
open CorrectedRegisterDiagram CorrectedDomainLattice CorrectedRegisterWords CorrectedWordCoverage

theorem bounded (r : Register) (sec : Fin 3) (par long : Bool) (hr : Regular r false sec)
    (div : r.M ∣ r.S)
    (lat : ∀ i : ℕ, (CorrectedRegisterDiagram.corrected r false (-1) long i).lattice r (-1) par sec) :
    Covers (fun i => (CorrectedRegisterDiagram.corrected r false (-1) long i).contains r par sec) long 8 := by
  fin_cases sec <;> cases par <;> cases long
  · exact CorrectedRegisterShortTwoDirectLowEven.coverage r hr div fun i => lat i.val
  · exact CorrectedRegisterLongTwoDirectLowEven.coverage r hr div fun i => lat i.val
  · exact CorrectedRegisterShortTwoDirectLowOdd.coverage r hr div fun i => lat i.val
  · exact CorrectedRegisterLongTwoDirectLowOdd.coverage r hr div fun i => lat i.val
  · exact CorrectedRegisterShortTwoDirectMidEven.coverage r hr div fun i => lat i.val
  · exact CorrectedRegisterLongTwoDirectMidEven.coverage r hr div fun i => lat i.val
  · exact CorrectedRegisterShortTwoDirectMidOdd.coverage r hr div fun i => lat i.val
  · exact CorrectedRegisterLongTwoDirectMidOdd.coverage r hr div fun i => lat i.val
  · exact CorrectedRegisterShortTwoDirectHighEven.coverage r hr div fun i => lat i.val
  · exact CorrectedRegisterLongTwoDirectHighEven.coverage r hr div fun i => lat i.val
  · exact CorrectedRegisterShortTwoDirectHighOdd.coverage r hr div fun i => lat i.val
  · exact CorrectedRegisterLongTwoDirectHighOdd.coverage r hr div fun i => lat i.val

/-- Both inclusions in unbounded determinant coordinates at every actual site of
every eligible preceding word in this orientation. -/
theorem word (x : Digit) (xs : Word) (hw : ¬ IsBase (x::xs)) (long : Bool) (N : ℕ) (hN : 0<N) (z : Site)
    (sign : (parentsAt (x::xs)).odd.det (parentsAt (x::xs)).even=(1)) :
    let P := parentsAt (x::xs)
    let sec := firstSector x
    let par := CorrectedCellsBands.oddSite z
    let r := register P false N (chart (P.current .odd) (representative z))
    let shape := CorrectedRegisterDiagram.corrected r false (-1) long
    Covers (fun i => CorrectedRegisterFaces.exact ((shape i).probe r par sec)) long 8 := by
  intro P sec par r shape
  have hp : -(parentsAt (x::xs)).odd.det (parentsAt (x::xs)).even=(-1) := by omega
  have goal := CorrectedWordCoverage.corrected x xs hw false long N hN z
  dsimp only at goal
  rw [hp] at goal
  apply goal
  exact bounded r sec par long

end FLatticePaper.Tiles.CorrectedRegisterTwoDirect
