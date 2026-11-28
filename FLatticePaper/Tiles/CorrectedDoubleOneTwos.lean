import FLatticePaper.Tiles.CorrectedSwappedDomains
import FLatticePaper.Tiles.CorrectedDoubleOneFamily

/-! Both printed corrected domains on the two-ending rotation of the double-one family. -/

namespace FLatticePaper.Tiles.CorrectedDoubleOneTwos

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open Standard JointFamily JointRot LCorrecProps CorrectedEvenPlacement CorrectedPlacementFrames CorrectedChildColumns

/-- The original two corrected piece unions coincide with their printed children at two ones
followed by any positive number of twos. -/
theorem piece_unions (k : ℕ) :
    let w := [Digit.one,.one]++List.replicate (k+1) Digit.two
    pieceUnion (tileEvenPieces cellData (fun u => domOdo (oddTile u)) (fun u => domOdo (evenTile u))
      (fun u s e => domOdo (oddLCells u s e)) w)=evenTile w ∧
    pieceUnion (tileAltOddPieces cellData (fun u => domOdo (oddTile u)) (fun u => domOdo (evenTile u))
      (fun u => domOdo (altOddT u)) (fun u => domOdo (altEvenT u)) (fun u s e => domOdo (oddLCells u s e)) w)=altOddT w := by
  let v := [Digit.one,.one]++List.replicate k Digit.three
  have pre : stemPrefix v=[.one,.one] := by
    change stripTrailing .three ([.one,.one]++List.replicate k .three)=[.one,.one]
    induction k with
    | zero => rfl
    | succ k ih => rw [List.replicate_succ',←List.append_assoc,stripTrailing_snoc,if_pos rfl,ih]
  have hn : ¬IsBase (v++[.three]) := by
    have one : Digit.one∈v++[.three] := by simp [v]
    rintro (h|h|h)
    · rw [h] at one; cases one
    · exact Digit.noConfusion (h _ one)
    · exact Digit.noConfusion (h _ one)
  have h := CorrectedDoubleOneFamily.domains k
  have result := CorrectedSwappedDomains.at_exit v [.one] true pre hn (by rw [pre]; simp [IsBase]) h.1 h.2
  have sw : swapW v=[Digit.one,.one]++List.replicate k Digit.two := by
    dsimp only [v]
    rw [swapW_append,swapW_replicate]; rfl
  rw [sw] at result
  dsimp only
  rw [List.replicate_succ',←List.append_assoc]
  exact result

end FLatticePaper.Tiles.CorrectedDoubleOneTwos
