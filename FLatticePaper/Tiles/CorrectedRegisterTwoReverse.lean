import FLatticePaper.Tiles.CorrectedWordCoverage
import FLatticePaper.Tiles.CorrectedRegisterShortTwoReverseLowEven
import FLatticePaper.Tiles.CorrectedRegisterLongTwoReverseLowEven
import FLatticePaper.Tiles.CorrectedRegisterShortTwoReverseLowOdd
import FLatticePaper.Tiles.CorrectedRegisterLongTwoReverseLowOdd
import FLatticePaper.Tiles.CorrectedRegisterShortTwoReverseMidEven
import FLatticePaper.Tiles.CorrectedRegisterLongTwoReverseMidEven
import FLatticePaper.Tiles.CorrectedRegisterShortTwoReverseMidOdd
import FLatticePaper.Tiles.CorrectedRegisterLongTwoReverseMidOdd
import FLatticePaper.Tiles.CorrectedRegisterShortTwoReverseHighEven
import FLatticePaper.Tiles.CorrectedRegisterLongTwoReverseHighEven
import FLatticePaper.Tiles.CorrectedRegisterShortTwoReverseHighOdd
import FLatticePaper.Tiles.CorrectedRegisterLongTwoReverseHighOdd

/-! The two inclusions across all three sectors and both physical parities for a fixed register orientation. -/

namespace FLatticePaper.Tiles.CorrectedRegisterTwoReverse

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles Standard
open CorrectedRegisterDiagram CorrectedDomainLattice CorrectedRegisterWords CorrectedWordCoverage

theorem bounded (r : Register) (sec : Fin 3) (par long : Bool) (hr : Regular r false sec)
    (div : r.M ∣ r.S)
    (lat : ∀ i : ℕ, (CorrectedRegisterDiagram.corrected r false (1) long i).lattice r (1) par sec) :
    Covers (fun i => (CorrectedRegisterDiagram.corrected r false (1) long i).contains r par sec) long 8 := by
  fin_cases sec <;> cases par <;> cases long
  · exact CorrectedRegisterShortTwoReverseLowEven.coverage r hr div fun i => lat i.val
  · exact CorrectedRegisterLongTwoReverseLowEven.coverage r hr div fun i => lat i.val
  · exact CorrectedRegisterShortTwoReverseLowOdd.coverage r hr div fun i => lat i.val
  · exact CorrectedRegisterLongTwoReverseLowOdd.coverage r hr div fun i => lat i.val
  · exact CorrectedRegisterShortTwoReverseMidEven.coverage r hr div fun i => lat i.val
  · exact CorrectedRegisterLongTwoReverseMidEven.coverage r hr div fun i => lat i.val
  · exact CorrectedRegisterShortTwoReverseMidOdd.coverage r hr div fun i => lat i.val
  · exact CorrectedRegisterLongTwoReverseMidOdd.coverage r hr div fun i => lat i.val
  · exact CorrectedRegisterShortTwoReverseHighEven.coverage r hr div fun i => lat i.val
  · exact CorrectedRegisterLongTwoReverseHighEven.coverage r hr div fun i => lat i.val
  · exact CorrectedRegisterShortTwoReverseHighOdd.coverage r hr div fun i => lat i.val
  · exact CorrectedRegisterLongTwoReverseHighOdd.coverage r hr div fun i => lat i.val

/-- Both inclusions in unbounded determinant coordinates at every actual site of
every eligible preceding word in this orientation. -/
theorem word (x : Digit) (xs : Word) (hw : ¬ IsBase (x::xs)) (long : Bool) (N : ℕ) (hN : 0<N) (z : Site)
    (sign : (parentsAt (x::xs)).odd.det (parentsAt (x::xs)).even=(-1)) :
    let P := parentsAt (x::xs)
    let sec := firstSector x
    let par := CorrectedCellsBands.oddSite z
    let r := register P false N (chart (P.current .odd) (representative z))
    let shape := CorrectedRegisterDiagram.corrected r false (1) long
    Covers (fun i => CorrectedRegisterFaces.exact ((shape i).probe r par sec)) long 8 := by
  intro P sec par r shape
  have hp : -(parentsAt (x::xs)).odd.det (parentsAt (x::xs)).even=(1) := by omega
  have goal := CorrectedWordCoverage.corrected x xs hw false long N hN z
  dsimp only at goal
  rw [hp] at goal
  apply goal
  exact bounded r sec par long

end FLatticePaper.Tiles.CorrectedRegisterTwoReverse
