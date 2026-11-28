import FLatticePaper.Tiles.CorrectedPlacedSectors
import FLatticePaper.Tiles.CorrectedPlacedSources
import FLatticePaper.Tiles.CorrectedRegisterOneDirect
import FLatticePaper.Tiles.CorrectedAlternatePolygons

/-! Physical domain equalities at corrected words with a two-polygon alternate head. -/

namespace FLatticePaper.Tiles.CorrectedPhysicalCoverage

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles Standard
open CorrectedRegisterDiagram CorrectedDomainLattice CorrectedRegisterWords CorrectedWordCoverage
open CorrectedPlacedDiagram CorrectedEvenPlacement CorrectedPlacementFrames CorrectedPlacedSources
open CorrectedChildColumns JointFamily LCorrecProps

/-- A register comparison at the site gives the same comparison between the physical bands. -/
theorem physical (x : Digit) (xs v : Word) (hw : ¬ IsBase (x::xs)) (one long : Bool)
    (pre : stemPrefix v=(x::xs)++[exit one]) (z : Site) :
    let P := parentsAt (x::xs)
    let p := P.current .odd
    let prev := -P.odd.det P.even
    let r := register P one (length v) (chart p (representative z))
    let shape := CorrectedRegisterDiagram.corrected r one prev long
    Covers (fun i => CorrectedRegisterFaces.exact ((shape i).probe r (CorrectedCellsBands.oddSite z) (firstSector x))) long 8 →
    Covers (fun i => (diagram (periods v) (length v) one prev long i).mem z) long 8 := by
  intro P p prev r shape h
  have N : 0 < length v := Nat.succ_pos _
  have reg := CorrectedRegisterWords.regular x xs hw one (length v) N (chart p (representative z))
  have hm : 0<scale p := lt_of_lt_of_le (by decide : (0:ℤ)<7) reg.scale
  have F := CorrectedPlacementFrames.word v (x::xs) one pre (chart p (representative z))
  refine (congr_cover long (by decide : 8≤8) fun i => ?_).mpr h
  have pr := projects one long prev F N (show r.S=(length v : ℤ)*r.M from rfl) i
  exact pr.band_iff z (firstSector x) (CorrectedPlacedSectors.word x xs v one long prev pre i) hm rfl

/-- The ordinary corrected pieces give the printed odd tile when their physical comparison holds. -/
theorem ordinary (v w : Word) (one : Bool) (pre : stemPrefix v=w++[exit one]) (hw : ¬ IsBase w) :
    let g := periods v
    let prev := -(parentsAt w).odd.det (parentsAt w).even
    HeadPair v one prev → (∀ z, Covers (fun i => (diagram g (length v) one prev false i).mem z) false 8) →
    evenChild evenLCells v false=oddTile (v++[.three]) := by
  intro g prev head proof
  have phase : decide (orientation one prev≠1)=W1Odd v := by
    rw [orientation_phase v w one pre]; cases W1Odd v <;> decide
  ext x
  let c := g.origin (W1Odd v) false
  have src := sources v w one false pre hw (x+c) head
  change x+c ∈ shift (evenChild evenLCells v false) c ↔ _ at src
  rw [mem_shift,add_sub_cancel_right] at src
  have covered := proof (x+c)
  change (diagram g (length v) one prev false 0).mem (x+c) ↔ _ at covered
  have target := target_band v x
  dsimp only at target
  rw [src,←covered,target]
  simp only [diagram,Block.mem,phase,Bool.false_eq_true,if_false,c,add_sub_cancel_right]
  rfl

/-- In the elongated diagram the second target and the topmost head are retained in the
comparison. Their union is the actual even alternate tile at this corrected child. -/
theorem elongated (v w : Word) (one : Bool) (pre : stemPrefix v=w++[exit one]) (hw : ¬ IsBase w) :
    let g := periods v
    let prev := -(parentsAt w).odd.det (parentsAt w).even
    HeadPair v one prev → CorrectedAlternatePolygons.MixedAt (v++[.three]) true →
    (∀ z, Covers (fun i => (diagram g (length v) one prev true i).mem z) true 8) →
    evenChild evenLCells v true=altEvenT (v++[.three]) := by
  intro g prev head alt proof
  ext x
  let c := g.origin (W1Odd v) true
  have src := sources v w one true pre hw (x+c) head
  change x+c ∈ shift (evenChild evenLCells v true) c ↔ _ at src
  rw [mem_shift,add_sub_cancel_right] at src
  have dst := CorrectedAlternatePolygons.target v w one pre alt (x+c)
  change x+c ∈ shift (altEvenT (v++[.three])) c ↔ _ at dst
  rw [mem_shift,add_sub_cancel_right] at dst
  exact src.trans ((proof (x+c)).symm.trans dst.symm)

/-- The initial non-base head is the actual odd alternate of the one-letter word. -/
theorem first_head (v : Word) (pre : stemPrefix v=[.one,.one]) : HeadPair v true (-1) := by
  exact CorrectedAlternatePolygons.head v [.one] true pre (CorrectedAlternatePolygons.first false)

/-- For any tail of threes following two ones, the actual ordinary corrected decomposition
has domain exactly the printed odd tile. -/
theorem first_one_run (v : Word) (pre : stemPrefix v=[.one,.one]) :
    evenChild evenLCells v false=oddTile (v++[.three]) := by
  have h : ¬ IsBase [Digit.one] := by simp [IsBase]
  have eq : stemPrefix v=[Digit.one]++[exit true] := pre
  apply ordinary v [.one] true eq h
  · exact first_head v pre
  · intro z
    apply physical .one [] v h true false eq z
    exact CorrectedRegisterOneDirect.word .one [] h false (length v) (Nat.succ_pos _) z (by decide)

/-- The odd standard clause of corrected cells, in its original piece-union form,
after two ones and any positive number of threes. -/
theorem odd_one_one_threes (k : ℕ) :
    let w := [Digit.one,.one]++List.replicate (k+1) Digit.three
    pieceUnion (tileOddPieces cellData (fun u => domOdo (oddTile u)) (fun u => domOdo (evenTile u))
      (fun u s e => domOdo (evenLCells u s e)) w)=oddTile w := by
  let v := [Digit.one,.one]++List.replicate k Digit.three
  have pre : stemPrefix v=[.one,.one] := by
    change stripTrailing .three ([.one,.one]++List.replicate k .three)=[.one,.one]
    induction k with
    | zero => rfl
    | succ k ih => rw [List.replicate_succ',←List.append_assoc,JointRot.stripTrailing_snoc,if_pos rfl,ih]
  dsimp only
  rw [List.replicate_succ',←List.append_assoc]
  exact first_one_run v pre

end FLatticePaper.Tiles.CorrectedPhysicalCoverage
