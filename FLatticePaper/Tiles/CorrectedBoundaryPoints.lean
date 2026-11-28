import FLatticePaper.Tiles.CorrectedBoundaryLattice
import Mathlib.Tactic.IntervalCases

/-! Register points for the two side strips, two square bridges, and nine pure-two corners. -/

namespace FLatticePaper.Tiles.CorrectedBoundaryPoints

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open CorrectedRegisterDiagram CorrectedRegisterLattice CorrectedBoundaryLattice

abbrev a (r : Register) : Site := (r.M,0)
abbrev b (r : Register) : Site := (0,r.M)
abbrev u (r : Register) (e : ℤ) : Site := (r.T,e)
abbrev v (r : Register) (e : ℤ) : Site := (e,2*r.T)
abbrev run (r : Register) : Site := (0,r.S)
def top (r : Register) (long : Bool) : Site := run r+run r+(if long then b r else 0)
def center (r : Register) (e : ℤ) (long : Bool) : Site :=
  a r+b r+(if long then b r else 0)+v r e+run r+run r
def stripStart (r : Register) (e : ℤ) (one upper : Bool) : Site :=
  (if one then b r+u r e else v r e)+(if upper then a r+displacement r (0,-2) else b r)
def gridStart (r : Register) (e : ℤ) (long upper : Bool) : Site := if upper then
  center r e long+displacement r (1,-1)-displacement r (2,2) else 0
def nearCorner (r : Register) (long : Bool) : ℕ → Site
  | 0 => 0
  | 1 => center r 1 long
  | 2 => v r 1+b r
  | 3 => v r 1+a r
  | 4 => v r 1+top r long-b r
  | 5 => v r 1+top r long
  | 6 => v r 1+top r long+b r
  | 7 => v r 1+a r+top r long
  | _ => v r 1+b r+b r

local macro "lattice_sum" h:ident : tactic => `(tactic| (
  repeat' first | exact ($h).point | exact ($h).a | exact ($h).b | exact ($h).u | exact ($h).v
                | exact ($h).runB | exact ($h).offset _ (by decide) | exact AddSubgroup.zero_mem _
                | apply AddSubgroup.add_mem | apply AddSubgroup.sub_mem | split))

theorem strip_point {r : Register} {e : ℤ} (h : Data r e) (one upper high long : Bool) :
    ((r.X,r.Y)-stripStart r e one upper-(if high then top r long else 0) : Site) ∈ lattice r.M r.T e := by
  unfold stripStart top
  lattice_sum h

theorem grid_point {r : Register} {e : ℤ} (h : Data r e) (long upper : Bool) (t : Site)
    (even : (t.1+t.2)%2=0) :
    ((r.X,r.Y)-gridStart r e long upper-displacement r t : Site) ∈ lattice r.M r.T e := by
  apply AddSubgroup.sub_mem _ _ (h.offset _ even)
  unfold gridStart center
  lattice_sum h

private theorem near_point {r : Register} (h : Data r 1) (long : Bool) (i : Fin 9) :
    ((r.X,r.Y)-nearCorner r long i.val : Site) ∈ lattice r.M r.T 1 := by
  fin_cases i <;> dsimp only [nearCorner,center,top]
  all_goals lattice_sum h

/-- A finite inequality description of the allowed sites around one corner. -/
def allowed (d x y : ℤ) : Prop :=
  (0 ≤ (-3*d-x-1) ∨
  0 ≤ (-3*d+x-1) ∨
  0 ≤ (-3*d-y-1) ∨
  0 ≤ (-3*d+y-1) ∨
  (0 ≤ (4*d+x+2) ∧ 0 ≤ (-4*d-x-2) ∧ 0 ≤ (4*d+y+4) ∧ 0 ≤ (-4*d-y-4)) ∨
  (0 ≤ (4*d+x+1) ∧ 0 ≤ (-4*d-x-1) ∧ 0 ≤ (2*d+y+4) ∧ 0 ≤ (-2*d-y-4)) ∨
  (0 ≤ (4*d+x) ∧ 0 ≤ (-4*d-x) ∧ 0 ≤ (y+4) ∧ 0 ≤ (-y-4)) ∨
  (0 ≤ (4*d+x-1) ∧ 0 ≤ (-4*d-x+1) ∧ 0 ≤ (-2*d+y+4) ∧ 0 ≤ (2*d-y-4)) ∨
  (0 ≤ (4*d+x-2) ∧ 0 ≤ (-4*d-x+2) ∧ 0 ≤ (-4*d+y+4) ∧ 0 ≤ (4*d-y-4)) ∨
  (0 ≤ (3*d+x+2) ∧ 0 ≤ (-3*d-x-2) ∧ 0 ≤ (4*d+y+3) ∧ 0 ≤ (-4*d-y-3)) ∨
  (0 ≤ (3*d+x+1) ∧ 0 ≤ (-3*d-x-1) ∧ 0 ≤ (2*d+y+3) ∧ 0 ≤ (-2*d-y-3)) ∨
  (0 ≤ (3*d+x) ∧ 0 ≤ (-3*d-x) ∧ 0 ≤ (y+3) ∧ 0 ≤ (-y-3)) ∨
  (0 ≤ (3*d+x-1) ∧ 0 ≤ (-3*d-x+1) ∧ 0 ≤ (-2*d+y+3) ∧ 0 ≤ (2*d-y-3)) ∨
  (0 ≤ (3*d+x-2) ∧ 0 ≤ (-3*d-x+2) ∧ 0 ≤ (-4*d+y+3) ∧ 0 ≤ (4*d-y-3)) ∨
  (0 ≤ (2*d+x+2) ∧ 0 ≤ (-2*d-x-2) ∧ 0 ≤ (4*d+y+2) ∧ 0 ≤ (-4*d-y-2)) ∨
  (0 ≤ (2*d+x+1) ∧ 0 ≤ (-2*d-x-1) ∧ 0 ≤ (2*d+y+2) ∧ 0 ≤ (-2*d-y-2)) ∨
  (0 ≤ (2*d+x) ∧ 0 ≤ (-2*d-x) ∧ 0 ≤ (y+2) ∧ 0 ≤ (-y-2)) ∨
  (0 ≤ (2*d+x-1) ∧ 0 ≤ (-2*d-x+1) ∧ 0 ≤ (-2*d+y+2) ∧ 0 ≤ (2*d-y-2)) ∨
  (0 ≤ (2*d+x-2) ∧ 0 ≤ (-2*d-x+2) ∧ 0 ≤ (-4*d+y+2) ∧ 0 ≤ (4*d-y-2)) ∨
  (0 ≤ (d+x+2) ∧ 0 ≤ (-d-x-2) ∧ 0 ≤ (4*d+y+1) ∧ 0 ≤ (-4*d-y-1)) ∨
  (0 ≤ (d+x+1) ∧ 0 ≤ (-d-x-1) ∧ 0 ≤ (2*d+y+1) ∧ 0 ≤ (-2*d-y-1)) ∨
  (0 ≤ (d+x) ∧ 0 ≤ (-d-x) ∧ 0 ≤ (y+1) ∧ 0 ≤ (-y-1)) ∨
  (0 ≤ (d+x-1) ∧ 0 ≤ (-d-x+1) ∧ 0 ≤ (-2*d+y+1) ∧ 0 ≤ (2*d-y-1)) ∨
  (0 ≤ (d+x-2) ∧ 0 ≤ (-d-x+2) ∧ 0 ≤ (-4*d+y+1) ∧ 0 ≤ (4*d-y-1)) ∨
  (0 ≤ (x+2) ∧ 0 ≤ (-x-2) ∧ 0 ≤ (4*d+y) ∧ 0 ≤ (-4*d-y)) ∨
  (0 ≤ (x+1) ∧ 0 ≤ (-x-1) ∧ 0 ≤ (2*d+y) ∧ 0 ≤ (-2*d-y)) ∨
  (0 ≤ (x) ∧ 0 ≤ (-x) ∧ 0 ≤ (y) ∧ 0 ≤ (-y)) ∨
  (0 ≤ (x-1) ∧ 0 ≤ (-x+1) ∧ 0 ≤ (-2*d+y) ∧ 0 ≤ (2*d-y)) ∨
  (0 ≤ (x-2) ∧ 0 ≤ (-x+2) ∧ 0 ≤ (-4*d+y) ∧ 0 ≤ (4*d-y)) ∨
  (0 ≤ (-d+x+2) ∧ 0 ≤ (d-x-2) ∧ 0 ≤ (4*d+y-1) ∧ 0 ≤ (-4*d-y+1)) ∨
  (0 ≤ (-d+x+1) ∧ 0 ≤ (d-x-1) ∧ 0 ≤ (2*d+y-1) ∧ 0 ≤ (-2*d-y+1)) ∨
  (0 ≤ (-d+x) ∧ 0 ≤ (d-x) ∧ 0 ≤ (y-1) ∧ 0 ≤ (-y+1)) ∨
  (0 ≤ (-d+x-1) ∧ 0 ≤ (d-x+1) ∧ 0 ≤ (-2*d+y-1) ∧ 0 ≤ (2*d-y+1)) ∨
  (0 ≤ (-d+x-2) ∧ 0 ≤ (d-x+2) ∧ 0 ≤ (-4*d+y-1) ∧ 0 ≤ (4*d-y+1)) ∨
  (0 ≤ (-2*d+x+2) ∧ 0 ≤ (2*d-x-2) ∧ 0 ≤ (4*d+y-2) ∧ 0 ≤ (-4*d-y+2)) ∨
  (0 ≤ (-2*d+x+1) ∧ 0 ≤ (2*d-x-1) ∧ 0 ≤ (2*d+y-2) ∧ 0 ≤ (-2*d-y+2)) ∨
  (0 ≤ (-2*d+x) ∧ 0 ≤ (2*d-x) ∧ 0 ≤ (y-2) ∧ 0 ≤ (-y+2)) ∨
  (0 ≤ (-2*d+x-1) ∧ 0 ≤ (2*d-x+1) ∧ 0 ≤ (-2*d+y-2) ∧ 0 ≤ (2*d-y+2)) ∨
  (0 ≤ (-2*d+x-2) ∧ 0 ≤ (2*d-x+2) ∧ 0 ≤ (-4*d+y-2) ∧ 0 ≤ (4*d-y+2)) ∨
  (0 ≤ (-3*d+x+2) ∧ 0 ≤ (3*d-x-2) ∧ 0 ≤ (4*d+y-3) ∧ 0 ≤ (-4*d-y+3)) ∨
  (0 ≤ (-3*d+x+1) ∧ 0 ≤ (3*d-x-1) ∧ 0 ≤ (2*d+y-3) ∧ 0 ≤ (-2*d-y+3)) ∨
  (0 ≤ (-3*d+x) ∧ 0 ≤ (3*d-x) ∧ 0 ≤ (y-3) ∧ 0 ≤ (-y+3)) ∨
  (0 ≤ (-3*d+x-1) ∧ 0 ≤ (3*d-x+1) ∧ 0 ≤ (-2*d+y-3) ∧ 0 ≤ (2*d-y+3)) ∨
  (0 ≤ (-3*d+x-2) ∧ 0 ≤ (3*d-x+2) ∧ 0 ≤ (-4*d+y-3) ∧ 0 ≤ (4*d-y+3)) ∨
  (0 ≤ (-4*d+x+2) ∧ 0 ≤ (4*d-x-2) ∧ 0 ≤ (4*d+y-4) ∧ 0 ≤ (-4*d-y+4)) ∨
  (0 ≤ (-4*d+x+1) ∧ 0 ≤ (4*d-x-1) ∧ 0 ≤ (2*d+y-4) ∧ 0 ≤ (-2*d-y+4)) ∨
  (0 ≤ (-4*d+x) ∧ 0 ≤ (4*d-x) ∧ 0 ≤ (y-4) ∧ 0 ≤ (-y+4)) ∨
  (0 ≤ (-4*d+x-1) ∧ 0 ≤ (4*d-x+1) ∧ 0 ≤ (-2*d+y-4) ∧ 0 ≤ (2*d-y+4)) ∨
  (0 ≤ (-4*d+x-2) ∧ 0 ≤ (4*d-x+2) ∧ 0 ≤ (-4*d+y-4) ∧ 0 ≤ (4*d-y+4)))

private theorem allowed_of_small {d x y : ℤ} (hd : 2≤d) (point : 2*d^2-1 ∣ x-d*y) : allowed d x y := by
  by_cases lx : x < -3*d
  · exact Or.inl (by omega)
  by_cases ux : 3*d < x
  · exact Or.inr (Or.inl (by omega))
  by_cases ly : y < -3*d
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  by_cases uy : 3*d < y
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
  obtain ⟨m,n,l,u,l',u',X,Y⟩ := corner d x y hd point (abs_le.mpr (by omega)) (abs_le.mpr (by omega))
  interval_cases m <;> interval_cases n
  · unfold allowed
    iterate 4 right
    left; omega
  · unfold allowed
    iterate 5 right
    left; omega
  · unfold allowed
    iterate 6 right
    left; omega
  · unfold allowed
    iterate 7 right
    left; omega
  · unfold allowed
    iterate 8 right
    left; omega
  · unfold allowed
    iterate 9 right
    left; omega
  · unfold allowed
    iterate 10 right
    left; omega
  · unfold allowed
    iterate 11 right
    left; omega
  · unfold allowed
    iterate 12 right
    left; omega
  · unfold allowed
    iterate 13 right
    left; omega
  · unfold allowed
    iterate 14 right
    left; omega
  · unfold allowed
    iterate 15 right
    left; omega
  · unfold allowed
    iterate 16 right
    left; omega
  · unfold allowed
    iterate 17 right
    left; omega
  · unfold allowed
    iterate 18 right
    left; omega
  · unfold allowed
    iterate 19 right
    left; omega
  · unfold allowed
    iterate 20 right
    left; omega
  · unfold allowed
    iterate 21 right
    left; omega
  · unfold allowed
    iterate 22 right
    left; omega
  · unfold allowed
    iterate 23 right
    left; omega
  · unfold allowed
    iterate 24 right
    left; omega
  · unfold allowed
    iterate 25 right
    left; omega
  · unfold allowed
    iterate 26 right
    left; omega
  · unfold allowed
    iterate 27 right
    left; omega
  · unfold allowed
    iterate 28 right
    left; omega
  · unfold allowed
    iterate 29 right
    left; omega
  · unfold allowed
    iterate 30 right
    left; omega
  · unfold allowed
    iterate 31 right
    left; omega
  · unfold allowed
    iterate 32 right
    left; omega
  · unfold allowed
    iterate 33 right
    left; omega
  · unfold allowed
    iterate 34 right
    left; omega
  · unfold allowed
    iterate 35 right
    left; omega
  · unfold allowed
    iterate 36 right
    left; omega
  · unfold allowed
    iterate 37 right
    left; omega
  · unfold allowed
    iterate 38 right
    left; omega
  · unfold allowed
    iterate 39 right
    left; omega
  · unfold allowed
    iterate 40 right
    left; omega
  · unfold allowed
    iterate 41 right
    left; omega
  · unfold allowed
    iterate 42 right
    left; omega
  · unfold allowed
    iterate 43 right
    left; omega
  · unfold allowed
    iterate 44 right
    left; omega
  · unfold allowed
    iterate 45 right
    left; omega
  · unfold allowed
    iterate 46 right
    left; omega
  · unfold allowed
    iterate 47 right
    left; omega
  · unfold allowed
    iterate 48 right
    omega

/-- Every corner tested at a pure-two exit admits just the listed short offsets in its box. -/
theorem local_points {r : Register} (h : Data r 1) (d : 2≤r.d) (scale : r.M=2*r.d^2-1) (turn : r.T=r.d)
    (long : Bool) (i : Fin 9) :
    let z : Site := (r.X,r.Y)-nearCorner r long i.val
    allowed r.d z.1 z.2 := by
  intro z
  have hp := (near_point h long i).1
  change r.M ∣ z.1-1*z.2*r.T at hp
  rw [scale,turn,one_mul,mul_comm z.2 r.d] at hp
  exact allowed_of_small d hp

end FLatticePaper.Tiles.CorrectedBoundaryPoints
