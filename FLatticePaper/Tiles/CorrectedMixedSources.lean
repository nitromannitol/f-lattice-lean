import FLatticePaper.Tiles.CorrectedMixedPlacement
import FLatticePaper.Tiles.CorrectedAlternatePolygons

/-! Identify the register comparison for each alternate polygon with its printed piece union. -/

namespace FLatticePaper.Tiles.CorrectedMixedSources

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles Standard
open CorrectedCellsBands JointFamily LCorrecProps SurgicalWeak
open SurgicalDict SurgicalAlt SurgicalAltTiles AltRotStep CorrectedEvenPlacement CorrectedPlacementFrames
open CorrectedRegisterDiagram CorrectedMixedPlacement CorrectedPlacedDiagram CorrectedAlternatePolygons
open CorrectedWordCoverage

abbrev six (P : ℕ → Prop) := P 1 ∨ P 2 ∨ P 3 ∨ P 4 ∨ P 5 ∨ P 6

private theorem regs (t : Word) (hn : ¬IsBase t) (z : Site) :
    (z ∈ (stateAt t).tOdd ↔ Band (vP1 t) (vP2 t) 0 0 z) ∧
    (z ∈ (stateAt t).tEven ↔ Band (vQ1 t) (vQ2 t) 0 0 z) := by
  obtain ⟨⟨x,hx⟩,⟨y,hy⟩⟩ := JointRot.regs_some t hn
  obtain ⟨O,_,E,_⟩ := WeakStepPaper.regsAt_tiles t
  obtain ⟨a,b⟩ := JointRot.parents_of_regs t
  rw [O x hx,E y hy,odd_band,even_band]
  simp only [vP1,vP2,vQ1,vQ2,SiteInduction.curO,SiteInduction.curE,a x hx,b y hy,and_self]

private theorem standard (p q : Fraction) (T Q : Tile) (o even one : Bool) (prev : ℤ)
    (phaseEq : orientation one prev=if o then -1 else 1)
    (Pmem : ∀ z, z∈T ↔ Band (texV1Odd p) (texV2 p) 0 0 z)
    (Qmem : ∀ z, z∈Q ↔ Band (texV1Even q) (texV2 q) 0 0 z) (z : Site) :
    z ∈ (if even then evenStd o T Q p q else oddStd o T Q p q) ↔
      six (fun i => (layout (texV1Odd p) (texV2 p) (texV1Even q) (texV2 q) one prev even i).mem z) := by
  obtain ⟨x,y⟩ := z
  cases o <;> cases even
  all_goals simp [evenStd,oddStd,doubled,mem_shift,Finset.mem_union,Pmem,Qmem,six,layout,Block.mem,
    phaseEq,offP0,offQ0,shP,shQ,altShifts,coeffOff,altP0Coeff,altQ0Coeff,texV1Odd,texV1Even,texV2,
    Prod.mk_add_mk,Prod.mk_sub_mk]
  all_goals ring_nf
  all_goals tauto

def rest (t : Word) (one even : Bool) : Tile :=
  let o := W1Odd t
  let p := (parentsAt t).odd
  let q := (parentsAt t).even
  let R := altRegs B t
  if even then altP1Part o (exit one) R.1 p q else altQ1Part o (exit one) R.2 p q

private def hasRest (P : ℕ → Prop) (one even : Bool) := if one || even then P 7 ∨ P 8 else False

private theorem oldAxes (w : Word) (one : Bool) :
    let t := w++[exit one]
    (if one then vQ1 t else vP1 t-vQ1 t)=vP1 w+vQ1 w ∧ vP2 t=vP2 w+vQ2 w ∧
    (if one then vP1 t-vQ1 t else vQ1 t)=vQ1 w ∧
    (if one then vQ2 t-vP2 t else vP2 t-vQ2 t)=vP2 w := by
  cases one <;> dsimp only <;> refine ⟨?_,?_,?_,?_⟩
  all_goals ext <;> simp [exit,vP1,vP2,vQ1,vQ2,parentsAt_append_singleton,Parents.step,Parents.current,
    Parents.combine,texV1Odd,texV1Even,texV2] <;> ring

/-- The given head polygons suffice exactly in the three cases that use an alternate register. -/
def input (w : Word) (one even : Bool) : Prop :=
  (one || even)=true → MixedAt w (!even)

private theorem parent (w : Word) (one even : Bool) (h : input w one even) (z : Site) :
    let t := w++[exit one]
    let prev := -(parentsAt w).odd.det (parentsAt w).even
    z∈rest t one even ↔ hasRest (fun i => (layout (vP1 t) (vP2 t) (vQ1 t) (vQ2 t) one prev even i).mem z) one even := by
  intro t prev
  have ph := CorrectedPlacementFrames.orientation_phase t w one (stem_at_exit w one)
  change orientation one prev=(if W1Odd t then -1 else 1) at ph
  obtain ⟨A,Bb,U,V⟩ := oldAxes w one
  have printP : (altRegs B t).1=altOddT w := by
    dsimp only [t]; rw [altRegs_snoc]; cases one <;> rfl
  have printQ (e : one=true) : (altRegs B t).2=altEvenT w := by subst one; rw [show t=w++[.one] from rfl,altRegs_snoc]; rfl
  have hh (used : (one || even)=true) (y : Site) :
      y∈(if even then altOddT w else altEvenT w) ↔
      Band (if one then vQ1 t else vP1 t-vQ1 t) (vP2 t) 0 0 y ∨
      Band (if one then vQ1 t else vP1 t-vQ1 t) (vP2 t) 0 0
        (y-((if one then vQ2 t-vP2 t else vP2 t-vQ2 t)+(if even then prev else -prev) • (if one then vP1 t-vQ1 t else vQ1 t))) := by
    rw [U,V,A,Bb]
    cases even <;> exact h used y
  cases one <;> cases even <;> cases o : W1Odd t
  all_goals simp only [o,Bool.false_eq_true,if_false,if_true] at ph
  all_goals try (solve | simp [rest,hasRest,altQ1Part,altQ1Coeff,exit])
  all_goals have mem := hh (by decide)
  all_goals simp only [Bool.false_eq_true,if_true,if_false] at mem
  all_goals obtain ⟨x,y⟩ := z
  all_goals simp [rest,hasRest,layout,Block.mem,o,ph,altQ1Part,altP1Part,exit,altQ1Coeff,altP1Coeff,
    coeffOff,mem_shift,printP,printQ,mem,vP1,vP2,vQ1,vQ2,texV1Odd,texV1Even,texV2,Prod.mk_sub_mk,
    Prod.mk_add_mk,Prod.smul_mk]
  all_goals ring_nf

private theorem union (P : ℕ → Prop) (one even : Bool) :
    (six P ∨ hasRest P one even) ↔ ∃ i : Fin (if one || even then 8 else 6), P (i.val+1) := by
  have short : (six P ∨ False) ↔ ∃ i : Fin 6, P (i.val+1) := by
    rw [or_false]
    constructor
    · rintro (p|p|p|p|p|p)
      exacts [⟨0,p⟩,⟨1,p⟩,⟨2,p⟩,⟨3,p⟩,⟨4,p⟩,⟨5,p⟩]
    · rintro ⟨i,hit⟩; unfold six; fin_cases i <;> tauto
  have full : (six P ∨ P 7 ∨ P 8) ↔ ∃ i : Fin 8, P (i.val+1) := by
    constructor
    · rintro ((p|p|p|p|p|p)|(p|p))
      exacts [⟨0,p⟩,⟨1,p⟩,⟨2,p⟩,⟨3,p⟩,⟨4,p⟩,⟨5,p⟩,⟨6,p⟩,⟨7,p⟩]
    · rintro ⟨i,hit⟩; unfold six; fin_cases i <;> tauto
  cases one <;> cases even <;> first | exact short | exact full

/-- Separate the six regular polygons from the actual alternate register, including when
the preceding word is pure and that register is given by a base tile. -/
theorem printed (w : Word) (one even : Bool) (hn : ¬IsBase (w++[exit one])) (z : Site) :
    let t := w++[exit one]
    let prev := -(parentsAt w).odd.det (parentsAt w).even
    z∈(if even then altEvenT t else altOddT t) ↔
      six (fun i => (layout (vP1 t) (vP2 t) (vQ1 t) (vQ2 t) one prev even i).mem z) ∨ z∈rest t one even := by
  intro t prev
  have st := standard (parentsAt t).odd (parentsAt t).even (stateAt t).tOdd (stateAt t).tEven
    (W1Odd t) even one prev (orientation_phase t w one (stem_at_exit w one)) (fun y => (regs t hn y).1) (fun y => (regs t hn y).2) z
  have pieces : (if even then altEvenT t else altOddT t)=
      (if even then evenStd (W1Odd t) (stateAt t).tOdd (stateAt t).tEven (parentsAt t).odd (parentsAt t).even
      else oddStd (W1Odd t) (stateAt t).tOdd (stateAt t).tEven (parentsAt t).odd (parentsAt t).even) ∪ rest t one even := by
    cases even
    · exact (altOddTile_of_not_base B hn).trans (altOddPieces_snoc w _ _)
    · exact (altEvenTile_of_not_base B hn).trans (altEvenPieces_snoc w _ _)
  rw [pieces,Finset.mem_union]
  exact or_congr st Iff.rfl

/-- Membership in the actual alternate tile is the union of its six or eight diagram entries.
An exit of type two in the odd family uses only the six standard copies. -/
theorem sources (w : Word) (one even : Bool) (hn : ¬IsBase (w++[exit one])) (h : input w one even) (z : Site) :
    let t := w++[exit one]
    let g := periods t
    let prev := -(parentsAt w).odd.det (parentsAt w).even
    z∈(if even then altEvenT t else altOddT t) ↔
      ∃ i : Fin (if one || even then 8 else 6), (layout g.a g.b g.u g.v one prev even (i.val+1)).mem z := by
  intro t g prev
  have hp := parent w one even h z
  let P := fun i => (layout (vP1 t) (vP2 t) (vQ1 t) (vQ2 t) one prev even i).mem z
  have cast : (layout g.a g.b g.u g.v one prev even)=layout (vP1 t) (vP2 t) (vQ1 t) (vQ2 t) one prev even := by
    dsimp only [g,periods]; rw [show stemPrefix t=t from stem_at_exit w one]
  rw [cast]
  refine Iff.trans ?_ (union P one even)
  exact (printed w one even hn z).trans (or_congr Iff.rfl hp)

/-- Transport a physical two-sided comparison to the alternate tile of the given word. -/
theorem mixed_at (w : Word) (one even : Bool) (hn : ¬IsBase (w++[exit one])) (h : input w one even) :
    let t := w++[exit one]
    let g := periods t
    let prev := -(parentsAt w).odd.det (parentsAt w).even
    (∀ z, Covers (fun i => (layout g.a g.b g.u g.v one prev even i).mem z) true (if one || even then 8 else 6)) →
    MixedAt t even := by
  intro t g prev cmp z
  have src := sources w one even hn h z
  apply src.trans
  have cc := (cmp z).symm
  apply cc.trans
  have dt : -(parentsAt t).odd.det (parentsAt t).even=orientation one prev := by
    dsimp only [t]; rw [parentsAt_append_singleton]; cases one
    · exact CorrectedRegisterLattice.next_sign (parentsAt w) false
    · exact CorrectedRegisterLattice.next_sign (parentsAt w) true
  have pre : stemPrefix t=t := stem_at_exit w one
  change (layout g.a g.b g.u g.v one prev even 0).mem z ∨ (layout g.a g.b g.u g.v one prev even 9).mem z ↔
    Band (vP1 t+vQ1 t) (vP2 t+vQ2 t) 0 0 z ∨
    Band (vP1 t+vQ1 t) (vP2 t+vQ2 t) 0 0 (z-(vP2 t+(if even then -(-(parentsAt t).odd.det (parentsAt t).even) else -(parentsAt t).odd.det (parentsAt t).even) • vQ1 t))
  rw [dt]
  simp [layout,g,periods,pre,Block.mem]

end FLatticePaper.Tiles.CorrectedMixedSources
