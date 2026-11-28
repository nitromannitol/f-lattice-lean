import FLatticePaper.Tiles.CorrectedRegisterLattice
import FLatticePaper.Tiles.CorrectedPureCorners

/-! Lattice congruences of the exceptional strips and the finite pure-two corner boxes. -/

namespace FLatticePaper.Tiles.CorrectedBoundaryLattice

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open CorrectedRegisterWords CorrectedRegisterDiagram CorrectedDomainLattice CorrectedRegisterLattice

/-- The periods, the two run shifts and all even physical displacements in one subgroup. -/
structure Data (r : Register) (e : ℤ) : Prop where
  point : ((r.X,r.Y):Site) ∈ lattice r.M r.T e
  a : ((r.M,0):Site) ∈ lattice r.M r.T e
  b : ((0,r.M):Site) ∈ lattice r.M r.T e
  u : ((r.T,e):Site) ∈ lattice r.M r.T e
  v : ((e,2*r.T):Site) ∈ lattice r.M r.T e
  runA : ((r.S,0):Site) ∈ lattice r.M r.T e
  runB : ((0,r.S):Site) ∈ lattice r.M r.T e
  offset : ∀ t : Site, (t.1+t.2)%2=0 → displacement r t ∈ lattice r.M r.T e

theorem word (w : Word) (one : Bool) (N : ℕ) (z : Site) (hz : (z.1+z.2)%2=0) :
    let P := parentsAt w
    let p := P.current .odd
    let prev := -P.odd.det P.even
    let r := register P one N (chart p z)
    Data r (orientation one prev) := by
  intro P p prev r
  let q := if one then P.current .even else P.even
  let e := orientation one prev
  let L := lattice r.M r.T e
  have addends := parentsAt_valid w
  change P.ValidFrame at addends
  have qeven : q.Even := by cases one <;> first | exact addends.current_even_parity | exact addends.even_parity
  have det : p.det q = 1 ∨ p.det q = -1 := by
    cases one
    · exact (addends.step .two).unit_det
    · exact (addends.step .one).unit_det
  have sign : -p.det q=e := next_sign P one
  have site (u : Site) (h : (u.1+u.2)%2=0) : chart p u ∈ L := by
    have hyp := chart_multiples p q qeven u h det
    change scale p ∣ (chart p u).1-e*(chart p u).2*(chart p (texV1Even q)).1 ∧
      scale p ∣ (chart p u).2-2*e*(chart p u).1*(chart p (texV1Even q)).1
    rw [← sign]
    exact hyp
  have po := periods p q qeven
  change chart p (texV1Odd p) = (r.M,0) ∧ chart p (texV2 p) = (0,r.M) ∧
    chart p (texV1Even q) = (r.T,-p.det q) ∧ chart p (texV2 q) = (-p.det q,2*r.T) at po
  rw [sign] at po
  have a : ((r.M,0):Site) ∈ L := po.1 ▸ site _ (by dsimp [texV1Odd]; omega)
  have b : ((0,r.M):Site) ∈ L := po.2.1 ▸ site _ (by dsimp [texV2]; omega)
  have u : ((r.T,e):Site) ∈ L := po.2.2.1 ▸ site _ (by change (q.den+q.num)%2=0; change (q.num+q.den)%2=0 at qeven; omega)
  have v : ((e,2*r.T):Site) ∈ L := po.2.2.2 ▸ site _ (by dsimp [texV2]; omega)
  have Sx : ((r.S,0):Site) ∈ L := by change (((N:ℤ)*r.M,0):Site) ∈ L; simpa [Prod.smul_mk] using L.zsmul_mem a (N : ℤ)
  have Sy : ((0,r.S):Site) ∈ L := by change ((0,(N:ℤ)*r.M):Site) ∈ L; simpa [Prod.smul_mk] using L.zsmul_mem b (N : ℤ)
  refine ⟨site z hz,a,b,u,v,Sx,Sy,?_⟩
  intro t ht
  rw [displacement_eq r t ht]
  exact site t ht

/-- Points satisfying the pure-two congruence are physical points of the even checkerboard
in the pure-two chart. The short intervals follow uniformly at any translated lattice corner. -/
theorem corner (d x y : ℤ) (hd : 2≤d) (latticePoint : (2*d^2-1) ∣ x-d*y)
    (hx : |x|≤3*d) (hy : |y|≤3*d) :
    ∃ a b : ℤ, -4≤a ∧ a≤4 ∧ -2≤b ∧ b≤2 ∧ x=d*a+b ∧ y=2*d*b+a := by
  obtain ⟨t,h⟩ := latticePoint
  let a := y+2*d*t
  let b := -t
  let u : Site := (a,a+2*b)
  have eu : (u.1+u.2)%2=0 := by change (a+(a+2*b))%2=0; omega
  have xval : d*a+b=x := by dsimp [a,b]; linarith only [h]
  have yval : 2*d*b+a=y := by dsimp [a,b]; ring
  have C : chart ⟨d-1,d⟩ u=(x,y) := by
    obtain ⟨t',eq⟩ := CorrectedPureCorners.basis d u eu
    have val : t'=b := by
      have sec := congrArg Prod.snd eq
      change d*(a+2*b)-(d-1)*a=2*d*t'+a at sec
      have mul : 2*d*(b-t')=0 := by linarith only [sec]
      rcases mul_eq_zero.mp mul with e|e <;> omega
    rw [eq,val]
    exact Prod.ext xval yval
  have hX : |(chart ⟨d-1,d⟩ u).1|≤3*d := by rwa [C]
  have hY : |(chart ⟨d-1,d⟩ u).2|≤3*d := by rwa [C]
  obtain ⟨aa,bb,l,h,l',h',eq⟩ := CorrectedPureCorners.bounded d hd u eu hX hY
  rw [C] at eq
  exact ⟨aa,bb,l,h,l',h',congrArg Prod.fst eq,congrArg Prod.snd eq⟩

end FLatticePaper.Tiles.CorrectedBoundaryLattice
