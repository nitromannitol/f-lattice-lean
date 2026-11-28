import FLatticePaper.Tiles.CorrectedBaseHeadPlacement
import FLatticePaper.Tiles.CorrectedBaseProjection
import FLatticePaper.Tiles.CorrectedAlternatePolygons
import FLatticePaper.Tiles.CorrectedPlacedSectors

/-! Transport from the arithmetic description at a first exit to its native corrected domain. -/

namespace FLatticePaper.Tiles.CorrectedBaseTransport

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles Standard
open CorrectedEvenPlacement CorrectedPlacementFrames CorrectedPlacedDiagram CorrectedRegisterDiagram
open CorrectedPhysicalFaces CorrectedRegisterWords CorrectedWordCoverage CorrectedDomainLattice
open JointFamily LCorrecProps CorrectedChildColumns

/-- The empty predecessor uses the middle sector at a one exit and the upper sector at a two exit. -/
theorem root_sector (v : Word) (one long : Bool) (pre : stemPrefix v=[exit one]) (i : Fin 10) :
    let B := diagram (periods v) (length v) one 1 long i.val
    Aligned B.a B.b (if one then 1 else 2) := by
  have K := CorrectedBaseHeadPlacement.two_axes v 0 one pre
  dsimp only at K
  obtain ⟨A,B,U,V⟩ := K
  have fu : (periods v).fullU=(periods v).u+(length v:ℤ) • (periods v).a := rfl
  have fv : (periods v).fullV=(periods v).v+(2*(length v:ℤ)) • (periods v).b := rfl
  fin_cases i <;> cases one <;> cases long
  all_goals norm_num [diagram,Aligned,fu,fv,A,B,U,V,Prod.smul_mk,Fin.ext_iff] <;> omega

/-- Each positioned physical polygon agrees with its register entry at a base site. -/
theorem polygon (v w : Word) (one long : Bool) (sec : Fin 3) (pre : stemPrefix v=w++[exit one])
    (prev : -(parentsAt w).odd.det (parentsAt w).even=1) (z : Site) (i : Fin 10)
    (oriented : let P := diagram (periods v) (length v) one 1 long i.val
      Aligned P.a P.b sec)
    (pos : 0<scale ((parentsAt w).current .odd)) :
    let P := parentsAt w
    let p := P.current .odd
    let r := register P one (length v) (chart p (representative z))
    (diagram (periods v) (length v) one 1 long i.val).mem z ↔
      CorrectedRegisterFaces.exact ((corrected r one 1 long i.val).probe r (CorrectedCellsBands.oddSite z) sec) := by
  intro P p r
  have F := CorrectedPlacementFrames.word v w one pre (chart p (representative z))
  change CorrectedPlacementFrames.Frame p r (orientation one (-(parentsAt w).odd.det (parentsAt w).even)) (periods v) (length v) at F
  rw [prev] at F
  have pr := projects one long 1 F (Nat.succ_pos _) (show r.S=(length v:ℤ)*r.M from rfl) i
  exact pr.band_iff z sec oriented pos rfl

def Shows (v : Word) (one long : Bool) (z : Site) : Prop :=
  let g := periods v
  let P := fun i => (diagram g (length v) one 1 long i).mem z
  z ∈ shift (evenChild evenLCells v long) (g.origin (W1Odd v) long) ↔ (if long then P 0 ∨ P 9 else P 0)

theorem ordinary (v : Word) (one : Bool) (phase : decide (orientation one 1≠1)=W1Odd v) (h : ∀ z, Shows v one false z) :
    evenChild evenLCells v false=oddTile (v++[.three]) := by
  ext x
  let g := periods v
  let c := g.origin (W1Odd v) false
  have H := h (x+c)
  change x+c∈shift _ c ↔ (diagram g (length v) one 1 false 0).mem (x+c) at H
  rw [mem_shift,add_sub_cancel_right] at H
  have T := CorrectedPlacedSources.target_band v x
  dsimp only at T
  rw [H,T]
  change CorrectedCellsBands.Band _ _ 0 0 ((x+c)-g.origin (decide (orientation one 1≠1)) false) ↔ _
  rw [phase]
  simp only [c,add_sub_cancel_right]
  rfl

theorem elongated (v w : Word) (one : Bool) (pre : stemPrefix v=w++[exit one])
    (prev : -(parentsAt w).odd.det (parentsAt w).even=1)
    (actual : CorrectedAlternatePolygons.MixedAt (v++[.three]) true) (h : ∀ z, Shows v one true z) :
    evenChild evenLCells v true=altEvenT (v++[.three]) := by
  ext x
  let c := (periods v).origin (W1Odd v) true
  have H := h (x+c)
  have T := CorrectedAlternatePolygons.target v w one pre actual (x+c)
  dsimp only at T
  rw [prev] at T
  change x+c∈shift _ c ↔ _ at T
  change x+c∈shift _ c ↔ _ at H
  rw [mem_shift,add_sub_cancel_right] at H T
  exact H.trans T.symm

end FLatticePaper.Tiles.CorrectedBaseTransport
