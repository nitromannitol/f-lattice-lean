import FLatticePaper.Tiles.CorrectedEvenPlacement
import FLatticePaper.Tiles.CorrectedPhysicalFaces

/-! The physical periods of a corrected word and their images in its Farey frame. -/

namespace FLatticePaper.Tiles.CorrectedPlacementFrames

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open JointFamily CorrectedDomainLattice CorrectedRegisterDiagram CorrectedRegisterWords
open CorrectedEvenPlacement CorrectedPhysicalFaces

/-- A physical site of the even checkerboard together with its register coordinates. -/
structure Image (p : Fraction) (v w : Site) : Prop where
  even : EvenPoint v
  eqn : chart p v=w

theorem Image.add {p : Fraction} {a b A B : Site} (h : Image p a A) (k : Image p b B) :
    Image p (a+b) (A+B) :=
  ⟨even_add h.even k.even,(chart_add p a b h.even k.even).trans (congrArg₂ (·+·) h.eqn k.eqn)⟩

theorem Image.sub {p : Fraction} {a b A B : Site} (h : Image p a A) (k : Image p b B) :
    Image p (a-b) (A-B) :=
  ⟨even_sub h.even k.even,(chart_sub p h.even k.even).trans (congrArg₂ (·-·) h.eqn k.eqn)⟩

theorem Image.smul {p : Fraction} {a A : Site} (h : Image p a A) (i : ℤ) :
    Image p (i • a) (i • A) :=
  ⟨even_smul i h.even,(chart_smul p i a h.even).trans (congrArg (i • ·) h.eqn)⟩

theorem Image.zero (p : Fraction) : Image p 0 0 := by
  constructor <;> simp [EvenPoint,chart]

theorem Image.neg {p : Fraction} {a A : Site} (h : Image p a A) : Image p (-a) (-A) := by
  simpa using (Image.zero p).sub h

/-- All four period vectors, both periods at the end of the run, and its two displacements. -/
structure Frame (p : Fraction) (r : Register) (e : ℤ) (g : Periods) (N : ℕ) : Prop where
  a : Image p g.a (r.M,0)
  b : Image p g.b (0,r.M)
  u : Image p g.u (r.T,e)
  v : Image p g.v (e,2*r.T)
  runA : Image p g.runA (r.S,0)
  runB : Image p ((N : ℤ) • g.b) (0,r.S)
  fullU : Image p g.fullU (r.S+r.T,e)
  fullV : Image p g.fullV (e,2*(r.S+r.T))

def exit (one : Bool) : Digit := if one then .one else .two

private theorem phase_run (v : Word) : W1Odd v=W1Odd (stemPrefix v) := by
  have H (u : Word) (k : ℕ) : W1Odd (u++List.replicate k .three)=W1Odd u := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [List.replicate_succ',←List.append_assoc]
      exact (JointRot.phase_snoc_three _).trans ih
  calc
    _ = W1Odd (stemPrefix v++List.replicate (trailingCount .three v) .three) :=
      congrArg W1Odd (JointRot.strip_append_replicate .three v).symm
    _ = _ := H _ _

/-- The two signs used in the numerical diagram are the checkerboard phases of the old
and current words. In particular the placement offsets use the same orientation. -/
theorem orientation_phase (v w : Word) (one : Bool) (pre : stemPrefix v=w++[exit one]) :
    orientation one (-(parentsAt w).odd.det (parentsAt w).even) = if W1Odd v then -1 else 1 := by
  let P := parentsAt w
  have e := CorrectedRegisterLattice.next_sign P one
  have ep : (parentsAt (stemPrefix v)).odd.det (parentsAt (stemPrefix v)).even =
      (P.current .odd).det (if one then P.current .even else P.even) := by
    rw [pre,parentsAt_append_singleton]
    cases one <;> rfl
  rw [←e,←ep,SiteScope.det_parentsAt,phase_run v]
  have h : phase (stemPrefix v) < 2 := Nat.mod_lt _ (by decide)
  rcases (show phase (stemPrefix v)=0 ∨ phase (stemPrefix v)=1 by omega) with q|q <;> simp [W1Odd,q]

/-- Both physical coordinate directions and the entire run project to the canonical
vectors for the word, with the corresponding Farey determinant as sign. -/
theorem word (v w : Word) (one : Bool) (pre : stemPrefix v=w++[exit one]) (Z : Site) :
    let P := parentsAt w
    let p := P.current .odd
    let e := orientation one (-P.odd.det P.even)
    let r := register P one (length v) Z
    Frame p r e (periods v) (length v) := by
  intro P p e r
  let q := if one then P.current .even else P.even
  have old : (parentsAt (stemPrefix v)).odd=p ∧ (parentsAt (stemPrefix v)).even=q := by
    rw [pre,parentsAt_append_singleton]
    cases one <;> exact ⟨rfl,rfl⟩
  have hq := (parentsAt_valid (stemPrefix v)).even_parity
  rw [old.2] at hq
  change (q.num+q.den)%2=0 at hq
  have sgn : -p.det q=e := CorrectedRegisterLattice.next_sign P one
  obtain ⟨ha,hb,hu,hv⟩ := CorrectedDomainLattice.periods p q hq
  rw [sgn] at hu hv
  have a : Image p (vP1 (stemPrefix v)) (r.M,0) := by
    unfold vP1; rw [old.1]; exact ⟨by dsimp [EvenPoint,texV1Odd]; omega,ha⟩
  have b : Image p (vP2 (stemPrefix v)) (0,r.M) := by
    unfold vP2; rw [old.1]; exact ⟨by dsimp [EvenPoint,texV2]; omega,hb⟩
  have u : Image p (vQ1 (stemPrefix v)) (r.T,e) := by
    unfold vQ1; rw [old.2]; exact ⟨by change (q.den+q.num)%2=0; omega,hu⟩
  have t : Image p (vQ2 (stemPrefix v)) (e,2*r.T) := by
    unfold vQ2; rw [old.2]; exact ⟨by dsimp [EvenPoint,texV2]; omega,hv⟩
  let k : ℤ := length v
  have S : k*r.M=r.S := rfl
  have ra := a.smul k
  have rb := b.smul k
  have twice := b.smul (2*k)
  simp only [Prod.smul_mk,smul_eq_mul,mul_zero,S,show 2*k*r.M=2*r.S by rw [←S]; ring] at ra rb twice
  refine ⟨a,b,u,t,ra,rb,?_,?_⟩
  · change Image p (vQ1 (stemPrefix v)+k • vP1 (stemPrefix v)) (r.S+r.T,e)
    simpa only [Prod.mk_add_mk,add_zero,add_comm r.T r.S] using u.add ra
  · change Image p (vQ2 (stemPrefix v)+(2*k) • vP2 (stemPrefix v)) (e,2*(r.S+r.T))
    simpa only [Prod.mk_add_mk,add_zero,show 2*r.T+2*r.S=2*(r.S+r.T) by ring] using t.add twice

end FLatticePaper.Tiles.CorrectedPlacementFrames
