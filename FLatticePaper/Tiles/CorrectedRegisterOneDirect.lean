import FLatticePaper.Tiles.CorrectedWordCoverage
import FLatticePaper.Tiles.CorrectedRegisterShortOneDirectLowEven
import FLatticePaper.Tiles.CorrectedRegisterLongOneDirectLowEven
import FLatticePaper.Tiles.CorrectedRegisterShortOneDirectLowOdd
import FLatticePaper.Tiles.CorrectedRegisterLongOneDirectLowOdd
import FLatticePaper.Tiles.CorrectedRegisterShortOneDirectMidEven
import FLatticePaper.Tiles.CorrectedRegisterLongOneDirectMidEven
import FLatticePaper.Tiles.CorrectedRegisterShortOneDirectMidOdd
import FLatticePaper.Tiles.CorrectedRegisterLongOneDirectMidOdd
import FLatticePaper.Tiles.CorrectedRegisterShortOneDirectHighEven
import FLatticePaper.Tiles.CorrectedRegisterLongOneDirectHighEven
import FLatticePaper.Tiles.CorrectedRegisterShortOneDirectHighOdd
import FLatticePaper.Tiles.CorrectedRegisterLongOneDirectHighOdd

/-! The two inclusions across all three sectors and both physical parities for a fixed register orientation. -/

namespace FLatticePaper.Tiles.CorrectedRegisterOneDirect

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles Standard
open CorrectedRegisterDiagram CorrectedDomainLattice CorrectedRegisterWords CorrectedWordCoverage

theorem bounded (r : Register) (sec : Fin 3) (par long : Bool) (hr : Regular r true sec)
    (div : r.M ∣ r.S)
    (lat : ∀ i : ℕ, (CorrectedRegisterDiagram.corrected r true (-1) long i).lattice r (1) par sec) :
    Covers (fun i => (CorrectedRegisterDiagram.corrected r true (-1) long i).contains r par sec) long 8 := by
  fin_cases sec <;> cases par <;> cases long
  · exact CorrectedRegisterShortOneDirectLowEven.coverage r hr div fun i => lat i.val
  · exact CorrectedRegisterLongOneDirectLowEven.coverage r hr div fun i => lat i.val
  · exact CorrectedRegisterShortOneDirectLowOdd.coverage r hr div fun i => lat i.val
  · exact CorrectedRegisterLongOneDirectLowOdd.coverage r hr div fun i => lat i.val
  · exact CorrectedRegisterShortOneDirectMidEven.coverage r hr div fun i => lat i.val
  · exact CorrectedRegisterLongOneDirectMidEven.coverage r hr div fun i => lat i.val
  · exact CorrectedRegisterShortOneDirectMidOdd.coverage r hr div fun i => lat i.val
  · exact CorrectedRegisterLongOneDirectMidOdd.coverage r hr div fun i => lat i.val
  · exact CorrectedRegisterShortOneDirectHighEven.coverage r hr div fun i => lat i.val
  · exact CorrectedRegisterLongOneDirectHighEven.coverage r hr div fun i => lat i.val
  · exact CorrectedRegisterShortOneDirectHighOdd.coverage r hr div fun i => lat i.val
  · exact CorrectedRegisterLongOneDirectHighOdd.coverage r hr div fun i => lat i.val

/-- Both inclusions in unbounded determinant coordinates at every actual site of
every eligible preceding word in this orientation. -/
theorem word (x : Digit) (xs : Word) (hw : ¬ IsBase (x::xs)) (long : Bool) (N : ℕ) (hN : 0<N) (z : Site)
    (sign : (parentsAt (x::xs)).odd.det (parentsAt (x::xs)).even=(1)) :
    let P := parentsAt (x::xs)
    let sec := firstSector x
    let par := CorrectedCellsBands.oddSite z
    let r := register P true N (chart (P.current .odd) (representative z))
    let shape := CorrectedRegisterDiagram.corrected r true (-1) long
    Covers (fun i => CorrectedRegisterFaces.exact ((shape i).probe r par sec)) long 8 := by
  intro P sec par r shape
  have hp : -(parentsAt (x::xs)).odd.det (parentsAt (x::xs)).even=(-1) := by omega
  have goal := CorrectedWordCoverage.corrected x xs hw true long N hN z
  dsimp only at goal
  rw [hp] at goal
  apply goal
  exact bounded r sec par long

end FLatticePaper.Tiles.CorrectedRegisterOneDirect
