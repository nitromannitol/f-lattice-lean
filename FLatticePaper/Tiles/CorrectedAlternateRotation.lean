import FLatticePaper.Tiles.CorrectedAlternatePolygons

/-! Rotation of the two actual alternate polygons, including the change of their order. -/

namespace FLatticePaper.Tiles.CorrectedAlternateRotation

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open Standard JointFamily LCorrecProps CorrectedCellsBands CorrectedAlternatePolygons

private def horizontal (w : Word) := vP1 w+vQ1 w
private def vertical (w : Word) := vP2 w+vQ2 w
private def off (w : Word) (even : Bool) : Site :=
  let e := -(parentsAt w).odd.det (parentsAt w).even
  vP2 w+(if even then -e else e) • vQ1 w

private def arg (w : Word) (z : Site) := transverse z+vertical w+((1,0):Site)
private def tau (w : Word) (even : Bool) := if even then AltRotStep.tauE w else AltRotStep.tauO w

private theorem band (w : Word) (z : Site) :
    Band (horizontal (swapW w)) (vertical (swapW w)) 0 0 z ↔
    Band (horizontal w) (vertical w) 0 0 (arg w z) := by
  obtain ⟨p₁,p₂,q₁,q₂,_,_⟩ := JointRot.vecs_swapW w
  have A : transverse (vertical (swapW w))=horizontal w := by
    rw [vertical,p₂,q₂]; ext <;> dsimp [transverse,horizontal,vP1,vQ1,texV1Odd,texV1Even] <;> ring
  have B : mulI (horizontal (swapW w))=vertical w := by
    rw [horizontal,p₁,q₁]; ext <;> dsimp [mulI,vertical,vP2,vQ2,texV2] <;> ring
  have E : ((horizontal (swapW w)).1+(horizontal (swapW w)).2)%2=0 := by
    rw [horizontal,p₁,q₁]; dsimp; omega
  simpa only [A,B,Nat.cast_zero,zero_add,one_smul,arg] using clockwise (horizontal (swapW w)) (vertical (swapW w)) z 0 0 E

private theorem points (w : Word) (even : Bool) (z : Site) :
    let y := transverse (z-tau w even)
    let g := off w even
    let z' := z-off (swapW w) (!even)
    (y=arg w z ∧ y-g=arg w z') ∨ (y=arg w z' ∧ y-g=arg w z) := by
  obtain ⟨_,p₂,q₁,_,_,_⟩ := JointRot.vecs_swapW w
  have bound : phase w < 2 := Nat.mod_lt _ (by decide)
  dsimp only
  rcases (show phase w=0 ∨ phase w=1 by omega) with hp|hp <;> cases even
  · left
    simp only [arg,off,p₂,q₁]
    constructor <;> ext <;> simp [tau,AltRotStep.tauO,AltRotStep.tauOdd,AltRotStep.tauShort,
      vertical,SiteScope.det_parentsAt,phase_swapW,hp,
      transverse,vP2,vQ1,vQ2,texV2,texV1Even] <;> ring
  · right
    simp only [arg,off,p₂,q₁]
    constructor <;> ext <;> simp [tau,AltRotStep.tauE,AltRotStep.tauEven,AltRotStep.tauLong,
      vertical,SiteScope.det_parentsAt,phase_swapW,hp,
      transverse,vP2,vQ1,vQ2,texV2,texV1Even] <;> ring
  · right
    simp only [arg,off,p₂,q₁]
    constructor <;> ext <;> simp [tau,AltRotStep.tauO,AltRotStep.tauOdd,AltRotStep.tauLong,
      vertical,SiteScope.det_parentsAt,phase_swapW,hp,
      transverse,vP2,vQ1,vQ2,texV2,texV1Even] <;> ring
  · left
    simp only [arg,off,p₂,q₁]
    constructor <;> ext <;> simp [tau,AltRotStep.tauE,AltRotStep.tauEven,AltRotStep.tauShort,
      vertical,SiteScope.det_parentsAt,phase_swapW,hp,
      transverse,vP2,vQ1,vQ2,texV2,texV1Even] <;> ring

/-- The two-polygon description for one alternate child implies the description of
the other alternate child at the swapped word, with the corners in their printed positions. -/
theorem swap (w : Word) (even : Bool) (h : MixedAt w even) : MixedAt (swapW w) (!even) := by
  let tile (u : Word) (v : Bool) := if v then altEvenT u else altOddT u
  have rot : shift (Standard.rot (tile w even)) (tau w even)=tile (swapW w) (!even) := by
    cases even
    · exact (AltRotStep.altRot w).1
    · exact (AltRotStep.altRot w).2
  intro z
  let y := transverse (z-tau w even)
  change z ∈ tile (swapW w) (!even) ↔ Band (horizontal (swapW w)) (vertical (swapW w)) 0 0 z ∨
    Band (horizontal (swapW w)) (vertical (swapW w)) 0 0 (z-off (swapW w) (!even))
  rw [←rot,mem_shift,mem_rot,band,band]
  have source := h y
  change y ∈ tile w even ↔ Band (horizontal w) (vertical w) 0 0 y ∨
    Band (horizontal w) (vertical w) 0 0 (y-off w even) at source
  apply source.trans
  rcases points w even z with ⟨first,second⟩|⟨first,second⟩
  · rw [show y-off w even=_ from second,show y=_ from first]
  · rw [show y-off w even=_ from second,show y=_ from first,or_comm]

/-- Both alternate domains after a three follow from the opposite alternate after a two. -/
theorem after_three (u : Word) (even : Bool) (h : MixedAt (swapW u++[.two]) (!even)) :
    MixedAt (u++[.three]) even := by
  have eqn : swapW (swapW u++[.two])=u++[.three] := calc
    _ = swapW (swapW u)++swapW [.two] := JointRot.swapW_append _ _
    _ = _ := congrArg₂ List.append (JointRot.swapW_swapW' u) rfl
  have h' := swap (swapW u++[.two]) (!even) h
  rw [eqn,Bool.not_not] at h'
  exact h'

end FLatticePaper.Tiles.CorrectedAlternateRotation
