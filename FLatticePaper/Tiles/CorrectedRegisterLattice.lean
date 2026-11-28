import FLatticePaper.Tiles.CorrectedRegisterWords

/-! Every corner and probe in the corrected diagram belongs to the physical checkerboard lattice. -/

namespace FLatticePaper.Tiles.CorrectedRegisterLattice

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open CorrectedRegisterDiagram CorrectedRegisterWords CorrectedDomainLattice

/-- The two register congruences at a projected site. -/
def lattice (M T e : ℤ) : AddSubgroup Site where
  carrier := {z | M ∣ z.1-e*z.2*T ∧ M ∣ z.2-2*e*z.1*T}
  zero_mem' := by simp
  add_mem' := by
    rintro a b ⟨ha,va⟩ ⟨hb,vb⟩
    change M ∣ (a.1+b.1)-e*(a.2+b.2)*T ∧ M ∣ (a.2+b.2)-2*e*(a.1+b.1)*T
    constructor
    · rw [show (a.1+b.1)-e*(a.2+b.2)*T=(a.1-e*a.2*T)+(b.1-e*b.2*T) by ring]
      exact dvd_add ha hb
    · rw [show (a.2+b.2)-2*e*(a.1+b.1)*T=(a.2-2*e*a.1*T)+(b.2-2*e*b.1*T) by ring]
      exact dvd_add va vb
  neg_mem' := by
    rintro a ⟨ha,va⟩
    change M ∣ -a.1-e*(-a.2)*T ∧ M ∣ -a.2-2*e*(-a.1)*T
    constructor
    · rw [show -a.1-e*(-a.2)*T=-(a.1-e*a.2*T) by ring]
      exact dvd_neg.mpr ha
    · rw [show -a.2-2*e*(-a.1)*T=-(a.2-2*e*a.1*T) by ring]
      exact dvd_neg.mpr va

/-- A polygon whose five defining vectors belong to the indicated subgroup. -/
structure Placed (L : AddSubgroup Site) (s : Shape) : Prop where
  corner : s.corner ∈ L
  a : s.a ∈ L
  b : s.b ∈ L
  extraA : s.extraA ∈ L
  extraB : s.extraB ∈ L

private theorem placed (L : AddSubgroup Site) (r : Register) (one long : Bool) (prev : ℤ)
    (ha : ((r.M,0) : Site) ∈ L) (hb : ((0,r.M) : Site) ∈ L)
    (hu : ((r.T,orientation one prev) : Site) ∈ L)
    (hv : ((orientation one prev,2*r.T) : Site) ∈ L)
    (hs : ((r.S,0) : Site) ∈ L) (ht : ((0,r.S) : Site) ∈ L) (i : ℕ) :
    Placed L (corrected r one prev long i) := by
  let e := orientation one prev
  have fu : ((r.S+r.T,e) : Site) ∈ L := by simpa [e] using L.add_mem hs hu
  have tv : ((0,2*r.S) : Site) ∈ L := by
    convert L.add_mem ht ht using 1
    apply Prod.ext <;> dsimp
    ring
  have fv : ((e,2*(r.S+r.T)) : Site) ∈ L := by
    convert L.add_mem hv tv using 1
    apply Prod.ext <;> dsimp [e] <;> ring
  have tb : ((0,2*r.S-r.M) : Site) ∈ L := by simpa using L.sub_mem tv hb
  have extra : ((0,if long then 2*r.S else 2*r.S-r.M) : Site) ∈ L := by
    cases long <;> assumption
  dsimp only [e] at fu fv
  unfold corrected
  split <;> (try split) <;> constructor
  all_goals dsimp only
  all_goals
    repeat' first
      | assumption
      | exact L.zero_mem
      | apply L.add_mem
      | apply L.sub_mem
      | apply L.neg_mem
      | apply L.zsmul_mem
      | split

theorem bias_even (par : Bool) (sec : Fin 3) (i : Fin 4) :
    ((bias par sec i).1+(bias par sec i).2)%2=0 := by
  cases par <;> fin_cases sec <;> fin_cases i <;> decide

private theorem probe_lattice {r : Register} {e : ℤ} {s : Shape} (par : Bool) (sec : Fin 3)
    (p : Placed (lattice r.M r.T e) s) (z : ((r.X,r.Y) : Site) ∈ lattice r.M r.T e)
    (b : ∀ i, displacement r (bias par sec i) ∈ lattice r.M r.T e) :
    s.lattice r e par sec := by
  let L := lattice r.M r.T e
  have h (i : Fin 4) := L.add_mem (L.sub_mem z p.corner) (b i)
  intro i
  fin_cases i
  · exact (h 0).1
  · exact (L.sub_mem (L.sub_mem (h 1) p.b) p.extraB).1
  · exact (h 2).2
  · exact (L.sub_mem (L.sub_mem (h 3) p.a) p.extraA).2

/-- The orientation of the revised frame, including the sign change when both parents change. -/
theorem next_sign (P : Parents) (one : Bool) :
    -(P.current .odd).det (if one then P.current .even else P.even) =
      orientation one (-P.odd.det P.even) := by
  cases one <;> simp [orientation,Parents.current,Parents.combine,Fraction.det] <;> ring

/-- A family of shapes made from the four periods and their two run displacements. -/
def FromPeriods (one : Bool) (shape : Register → ℤ → Shape) : Prop :=
  ∀ (L : AddSubgroup Site) (r : Register) (prev : ℤ),
    ((r.M,0) : Site) ∈ L → ((0,r.M) : Site) ∈ L →
    ((r.T,orientation one prev) : Site) ∈ L → ((orientation one prev,2*r.T) : Site) ∈ L →
    ((r.S,0) : Site) ∈ L → ((0,r.S) : Site) ∈ L → Placed L (shape r prev)

/-- Each probe of a shape built out of the periods has the two physical lattice congruences. -/
theorem from_periods (w : Word) (one par : Bool) (sec : Fin 3) (N : ℕ) (z : Site) (hz : (z.1+z.2)%2=0)
    (shape : Register → ℤ → Shape) (hs : FromPeriods one shape) :
    let P := parentsAt w
    let p := P.current .odd
    let prev := -P.odd.det P.even
    let r := register P one N (chart p z)
    (shape r prev).lattice r (orientation one prev) par sec := by
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
  apply probe_lattice par sec (hs L r prev a b u v Sx Sy)
  · exact site z hz
  · intro j
    rw [displacement_eq r _ (bias_even par sec j)]
    exact site _ (bias_even par sec j)

/-- The actual two lattice congruences for every probe of every entry of either
corrected diagram, at any word and any even reference displacement. -/
theorem word (w : Word) (one long par : Bool) (sec : Fin 3) (N : ℕ) (z : Site) (hz : (z.1+z.2)%2=0) (i : ℕ) :
    let P := parentsAt w
    let p := P.current .odd
    let prev := -P.odd.det P.even
    let r := register P one N (chart p z)
    (corrected r one prev long i).lattice r (orientation one prev) par sec :=
  from_periods w one par sec N z hz (fun r prev => corrected r one prev long i)
    (fun L r prev a b u v s t => placed L r one long prev a b u v s t i)

end FLatticePaper.Tiles.CorrectedRegisterLattice
