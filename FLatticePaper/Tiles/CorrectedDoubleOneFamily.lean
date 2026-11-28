import FLatticePaper.Tiles.CorrectedMixedSources
import FLatticePaper.Tiles.CorrectedPhysicalCoverage
import FLatticePaper.Tiles.CorrectedAlternateRotation
import FLatticePaper.Tiles.MixedRegisterOddTwoReverseMidEven
import FLatticePaper.Tiles.MixedRegisterOddTwoReverseMidOdd

/-! Both actual domains at every positive run of threes after two ones. -/

namespace FLatticePaper.Tiles.CorrectedDoubleOneFamily

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles Standard JointFamily LCorrecProps
open CorrectedEvenPlacement CorrectedPlacementFrames CorrectedWordCoverage CorrectedDomainLattice
open CorrectedRegisterWords CorrectedAlternatePolygons CorrectedPhysicalCoverage CorrectedChildColumns

private theorem nonbase (xs : Word) : ¬IsBase (.one::xs) := by
  rintro (h|h|h)
  · simp at h
  · exact Digit.noConfusion (h .one (List.mem_cons_self))
  · exact Digit.noConfusion (h .one (List.mem_cons_self))

/-- The odd alternate after a two has only six full parent copies. At these words its two
displayed polygons therefore follow without an alternate induction hypothesis. -/
theorem after_two (xs : Word) (sign : (parentsAt (.one::xs)).odd.det (parentsAt (.one::xs)).even= -1) :
    MixedAt ((.one::xs)++[.two]) false := by
  let w := Digit.one::xs
  have hn : ¬IsBase (w++[exit false]) := nonbase _
  apply CorrectedMixedSources.mixed_at w false false hn (by intro bad; cases bad)
  intro z
  apply (CorrectedMixedPlacement.physical .one xs (nonbase _) false false z).mp
  apply CorrectedWordCoverage.mixed .one xs (nonbase _) false false z
  intro reg multiple equal lattice
  have det : -(parentsAt (.one::xs)).odd.det (parentsAt (.one::xs)).even=1 := by omega
  simp only [det] at lattice ⊢
  cases p : CorrectedCellsBands.oddSite z
  · rw [p] at lattice
    exact MixedRegisterOddTwoReverseMidEven.coverage _ reg multiple equal (fun i => lattice i.val)
  · rw [p] at lattice
    exact MixedRegisterOddTwoReverseMidOdd.coverage _ reg multiple equal (fun i => lattice i.val)

private theorem phase_twos (k : ℕ) : W1Odd ([Digit.one,.one]++List.replicate k Digit.two)=false :=
  (JointRot.W1Odd_append_replicate _ k .two (by decide)).trans (by decide)

/-- The ordinary and elongated piece unions coincide with the printed odd standard and even
alternate children for the same positive run length. -/
theorem domains (k : ℕ) :
    let v := [Digit.one,.one]++List.replicate k Digit.three
    evenChild evenLCells v false=oddTile (v++[.three]) ∧ evenChild evenLCells v true=altEvenT (v++[.three]) := by
  intro v
  have pre : stemPrefix v=[.one,.one] := by
    change stripTrailing .three ([.one,.one]++List.replicate k .three)=[.one,.one]
    induction k with
    | zero => rfl
    | succ k ih => rw [List.replicate_succ',←List.append_assoc,JointRot.stripTrailing_snoc,if_pos rfl,ih]
  have pf : stemPrefix v=[Digit.one]++[exit true] := pre
  refine ⟨first_one_run v pre,elongated v [.one] true pf (nonbase []) (first_head v pre) ?_ ?_⟩
  · apply CorrectedAlternateRotation.after_three
    have sw : swapW v=[Digit.one,.one]++List.replicate k Digit.two := by
      change swapW ([Digit.one,.one]++List.replicate k .three)=_
      rw [JointRot.swapW_append,JointRot.swapW_replicate]; rfl
    rw [sw]
    apply after_two (.one::List.replicate k Digit.two)
    rw [SiteScope.det_parentsAt]
    have h := phase_twos k
    change (phase (.one::.one::List.replicate k .two)==1)=false at h
    have bound : phase (.one::.one::List.replicate k .two)<2 := Nat.mod_lt _ (by decide)
    have zero : phase (.one::.one::List.replicate k .two)=0 := by
      by_contra! ne
      have eq : phase (.one::.one::List.replicate k .two)=1 := by omega
      simp [eq] at h
    rw [zero]; decide
  · intro z
    apply CorrectedPhysicalCoverage.physical .one [] v (nonbase []) true true pf z
    exact CorrectedRegisterOneDirect.word .one [] (nonbase []) true (length v) (Nat.succ_pos _) z (by decide)

/-- The two corrected clauses, stated with the original piece lists of corrected cells. -/
theorem piece_unions (k : ℕ) :
    let w := [Digit.one,.one]++List.replicate (k+1) Digit.three
    pieceUnion (tileOddPieces cellData (fun u => domOdo (oddTile u)) (fun u => domOdo (evenTile u))
      (fun u s e => domOdo (evenLCells u s e)) w)=oddTile w ∧
    pieceUnion (tileAltEvenPieces cellData (fun u => domOdo (oddTile u)) (fun u => domOdo (evenTile u))
      (fun u => domOdo (altOddT u)) (fun u => domOdo (altEvenT u)) (fun u s e => domOdo (evenLCells u s e)) w)=altEvenT w := by
  dsimp only
  rw [List.replicate_succ',←List.append_assoc]
  exact domains k

end FLatticePaper.Tiles.CorrectedDoubleOneFamily
