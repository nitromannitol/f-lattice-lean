import FLatticePaper.Tiles.CorrectedFiniteFaces
import FLatticePaper.Tiles.CorrectedRegisterDiagram
import Mathlib.Tactic.ClearExcept

/-! Both inclusions of the elongated corrected diagram for base family 3 and exit 1 on even sites. -/

namespace FLatticePaper.Tiles.BaseCorrectedThreeOneLongEvenSites

open CorrectedFiniteFaces CorrectedLevelTests Lean

abbrev Register := CorrectedRegisterDiagram.Register

structure Frame (r : Register) : Prop where
  f0 : 0 ≤ (r.d-4)
  f1 : r.d%2=0
  f2 : 0 ≤ (r.n-1)
  f3 : 0 ≤ (-r.n+1)
  f4 : 0 ≤ (-r.d+r.f-1)
  f5 : 0 ≤ (r.d-r.f+1)
  f6 : 0 ≤ (r.g-1)
  f7 : 0 ≤ (-r.g+1)
  f8 : 0 ≤ (-r.M+2*r.T-r.d-1)
  f9 : 0 ≤ (r.M-2*r.T+r.d+1)
  f10 : 0 ≤ (r.M-5*r.d-3)
  f11 : 0 ≤ (-r.M+r.S)
  f12 : r.M%2=1
  site0 : (0 ≤ (r.S+r.X-1) ∨ 0 ≤ (-r.S-r.X-1) ∨ 0 ≤ (-r.M-r.Y) ∨ 0 ≤ (r.Y))
  site1 : (0 ≤ (r.S+r.X-1) ∨ 0 ≤ (-r.S-r.X-1) ∨ 0 ≤ (-r.Y) ∨ 0 ≤ (-r.M+r.Y))
  site2 : (0 ≤ (-r.M-2*r.T-r.S-r.n+r.X) ∨ 0 ≤ (r.M+2*r.T+r.S+r.n-r.X-2) ∨ 0 ≤ (r.M+2*r.T+2*r.S-r.d-r.n-r.Y-2) ∨ 0 ≤ (-2*r.M-2*r.T-2*r.S+r.d+r.n+r.Y+2))
  site3 : (0 ≤ (-r.M-2*r.T-r.S-r.n+r.X) ∨ 0 ≤ (r.M+2*r.T+r.S+r.n-r.X-2) ∨ 0 ≤ (2*r.M+2*r.T+2*r.S-r.d-r.n-r.Y-2) ∨ 0 ≤ (-3*r.M-2*r.T-2*r.S+r.d+r.n+r.Y+2))

/-- The four levels of each polygon and the explicit boundary conditions on each component of the alternate parent. -/
def test (r : Register) : ℕ → ℕ → Test
  | 0, 0 => .line 4 (.sloped (r.d-r.n+r.Y) (r.M+r.T+r.S) (-r.S-r.d-r.X))
  | 0, 1 => .line 4 (.sloped (r.M+2*r.T+2*r.S-2*r.n-r.Y) (r.M+r.T+r.S) (r.S-r.d-r.n+r.X+1))
  | 0, 2 => .line 4 (.sloped (r.S+r.X) (r.M+2*r.T+2*r.S) (-r.Y))
  | 0, 3 => .line 4 (.sloped (r.M+r.T+r.n-r.X) (r.M+2*r.T+2*r.S) (r.d+r.n+r.Y+1))
  | 1, 0 => .line 4 (.sloped (-r.M+r.d-r.n+r.Y) (r.T+r.S) (-r.S-r.d-r.X))
  | 1, 1 => .line 4 (.sloped (r.M+2*r.T+2*r.S-2*r.n-r.Y) (r.T+r.S) (r.S-r.d-r.n+r.X+1))
  | 1, 2 => .line 4 (.sloped (r.S+r.X) (2*r.T+2*r.S) (r.M-r.Y))
  | 1, 3 => .line 4 (.sloped (r.T+r.n-r.X) (2*r.T+2*r.S) (-r.M+r.d+r.n+r.Y+1))
  | 2, 0 => .line 4 (.sloped (-r.M+r.d-r.n+r.Y+1) (r.T+r.S) (r.M+r.T-r.d-r.X))
  | 2, 1 => .line 4 (.sloped (r.M+2*r.T+2*r.S-2*r.n-r.Y-1) (r.T+r.S) (-r.M-r.T-r.d-r.n+r.X+1))
  | 2, 2 => .line 4 (.sloped (-r.M-r.T+r.X) (2*r.T+2*r.S) (r.M-r.Y-1))
  | 2, 3 => .line 4 (.sloped (r.M+2*r.T+r.S+r.n-r.X) (2*r.T+2*r.S) (-r.M+r.d+r.n+r.Y+2))
  | 3, 0 => .line 4 (.flat (r.d-r.n+r.Y))
  | 3, 1 => .line 4 (.flat (r.M-2*r.n-r.Y))
  | 3, 2 => .line 4 (.flat (r.S+r.X))
  | 3, 3 => .line 4 (.flat (r.M+r.n-r.X))
  | 4, 0 => .line 4 (.flat (-r.M-2*r.T-2*r.S+r.d-r.n+r.Y+2))
  | 4, 1 => .line 4 (.flat (2*r.M+2*r.T+2*r.S-2*r.n-r.Y-2))
  | 4, 2 => .line 4 (.flat (-2*r.T+r.X+1))
  | 4, 3 => .line 4 (.flat (r.M+2*r.T+r.S+r.n-r.X-1))
  | 5, 0 => .line 4 (.sloped (r.d-r.n+r.Y) (r.T) (r.M-r.d-r.X))
  | 5, 1 => .line 4 (.sloped (2*r.T-2*r.n-r.Y) (r.T) (-r.M-r.d-r.n+r.X+1))
  | 5, 2 => .line 4 (.sloped (-r.M+r.X) (2*r.T) (-r.Y))
  | 5, 3 => .line 4 (.sloped (r.M+r.T+r.n-r.X) (2*r.T) (r.d+r.n+r.Y+1))
  | 6, 0 => .line 4 (.sloped (-2*r.M-2*r.S+r.d-r.n+r.Y+1) (r.T) (r.T-r.d-r.X))
  | 6, 1 => .line 4 (.sloped (2*r.M+2*r.T+2*r.S-2*r.n-r.Y-1) (r.T) (-r.T-r.d-r.n+r.X+1))
  | 6, 2 => .line 4 (.sloped (-r.T+r.X) (2*r.T) (2*r.M+2*r.S-r.Y-1))
  | 6, 3 => .line 4 (.sloped (2*r.T+r.n-r.X) (2*r.T) (-2*r.M-2*r.S+r.d+r.n+r.Y+2))
  | 7, 0 => .line 4 (.sloped (-r.M+r.d-r.n+r.Y+1) (r.T) (r.T-r.d-r.X))
  | 7, 1 => .line 4 (.sloped (2*r.M+2*r.S-2*r.n-r.Y-1) (r.T) (-r.T-r.d-r.n+r.X))
  | 7, 2 => .line 4 (.flat (-r.T+r.X))
  | 7, 3 => .line 4 (.flat (2*r.T+r.n-r.X))
  | 7, 4 => .boundary ((0 ≤ (4*r.T-r.d+r.n-2*r.X-1) ∨ 0 ≤ (-4*r.T+r.d-r.n+2*r.X-1) ∨ 0 ≤ (r.M-r.d-r.Y-3) ∨ 0 ≤ (-r.M+r.d+r.Y+1)))
  | 7, 5 => .boundary ((0 ≤ (2*r.T-r.X-1) ∨ 0 ≤ (-2*r.T+r.X-1) ∨ 0 ≤ (r.M-r.Y-3) ∨ 0 ≤ (-r.M+r.Y+1)))
  | 7, 6 => .boundary ((0 ≤ (2*r.T-r.d-r.n-r.X-1) ∨ 0 ≤ (-2*r.T+r.d+r.n+r.X-1) ∨ 0 ≤ (2*r.M+2*r.S+2*r.n-r.Y-3) ∨ 0 ≤ (-2*r.M-2*r.S-2*r.n+r.Y+1)))
  | 7, 7 => .boundary ((0 ≤ (4*r.T-r.d-3*r.n-2*r.X-1) ∨ 0 ≤ (-4*r.T+r.d+3*r.n+2*r.X-1) ∨ 0 ≤ (2*r.M+2*r.S+r.d+2*r.n-r.Y-3) ∨ 0 ≤ (-2*r.M-2*r.S-r.d-2*r.n+r.Y+1)))
  | 8, 0 => .line 4 (.sloped (-2*r.T+r.d-r.n+r.Y) (r.T) (r.M-r.d-r.X-1))
  | 8, 1 => .line 4 (.sloped (r.M+2*r.T+2*r.S-2*r.n-r.Y) (r.T) (-r.M-r.d-r.n+r.X+1))
  | 8, 2 => .line 4 (.flat (-r.M+r.X+1))
  | 8, 3 => .line 4 (.flat (r.M+r.T+r.n-r.X-1))
  | 8, 4 => .boundary ((0 ≤ (4*r.T-r.d+r.n-2*r.X-1) ∨ 0 ≤ (-4*r.T+r.d-r.n+2*r.X-1) ∨ 0 ≤ (r.M-r.d-r.Y-3) ∨ 0 ≤ (-r.M+r.d+r.Y+1)))
  | 8, 5 => .boundary ((0 ≤ (2*r.T-r.X-1) ∨ 0 ≤ (-2*r.T+r.X-1) ∨ 0 ≤ (r.M-r.Y-3) ∨ 0 ≤ (-r.M+r.Y+1)))
  | 8, 6 => .boundary ((0 ≤ (2*r.T-r.d-r.n-r.X-1) ∨ 0 ≤ (-2*r.T+r.d+r.n+r.X-1) ∨ 0 ≤ (2*r.M+2*r.S+2*r.n-r.Y-3) ∨ 0 ≤ (-2*r.M-2*r.S-2*r.n+r.Y+1)))
  | 8, 7 => .boundary ((0 ≤ (4*r.T-r.d-3*r.n-2*r.X-1) ∨ 0 ≤ (-4*r.T+r.d+3*r.n+2*r.X-1) ∨ 0 ≤ (2*r.M+2*r.S+r.d+2*r.n-r.Y-3) ∨ 0 ≤ (-2*r.M-2*r.S-r.d-2*r.n+r.Y+1)))
  | 9, 0 => .line 4 (.sloped (-r.M+r.d-r.n+r.Y+1) (r.M+r.T+r.S) (r.T-r.d-r.X))
  | 9, 1 => .line 4 (.sloped (2*r.M+2*r.T+2*r.S-2*r.n-r.Y-1) (r.M+r.T+r.S) (-r.T-r.d-r.n+r.X+1))
  | 9, 2 => .line 4 (.sloped (-r.T+r.X) (r.M+2*r.T+2*r.S) (r.M-r.Y-1))
  | 9, 3 => .line 4 (.sloped (r.M+2*r.T+r.S+r.n-r.X) (r.M+2*r.T+2*r.S) (-r.M+r.d+r.n+r.Y+2))
  | _, _ => .boundary True

def arity : ℕ → ℕ
  | 0 => 4
  | 1 => 4
  | 2 => 4
  | 3 => 4
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | 7 => 8
  | 8 => 8
  | 9 => 4
  | _ => 0

def contains (r : Register) (i : ℕ) : Prop := ∀ j : Fin (arity i), (test r i j.val).holds

private abbrev Pos (r : Register) (i : ℕ) := ∀ j : Fin (arity i), ∀ k : Fin 10, (test r i j.val).bound true k.val
private abbrev Neg (r : Register) (i j : ℕ) := ∀ k : Fin 10, (test r i j).bound false k.val

local macro "lin_close" "[" xs:term,* "]" : tactic => do
  let vs := xs.getElems
  let ns := vs.mapIdx fun i _ => mkIdent (Name.mkSimple s!"bound{i}")
  let hs ← (ns.zip vs).mapM fun (n,v) => `(tactic| have $n := $v)
  `(tactic| ($[$hs:tactic]*; clear * - $ns:ident*; norm_num [test,Test.bound,fact] at $ns:ident*; all_goals omega))

private theorem valid0 (r : Register) (h : Frame r) (j : Fin 12) (k : Fin 10) :
    (test r 0 j.val).valid k.val := by
  have bound := k.isLt
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,_,_,_,_⟩ := h
  fin_cases j <;> norm_num [test,Test.valid,Line.valid] <;> omega

private theorem valid1 (r : Register) (h : Frame r) (j : Fin 12) (k : Fin 10) :
    (test r 1 j.val).valid k.val := by
  have bound := k.isLt
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,_,_,_,_⟩ := h
  fin_cases j <;> norm_num [test,Test.valid,Line.valid] <;> omega

private theorem valid2 (r : Register) (h : Frame r) (j : Fin 12) (k : Fin 10) :
    (test r 2 j.val).valid k.val := by
  have bound := k.isLt
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,_,_,_,_⟩ := h
  fin_cases j <;> norm_num [test,Test.valid,Line.valid] <;> omega

private theorem valid3 (r : Register) (h : Frame r) (j : Fin 12) (k : Fin 10) :
    (test r 3 j.val).valid k.val := by
  have bound := k.isLt
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,_,_,_,_⟩ := h
  fin_cases j <;> norm_num [test,Test.valid,Line.valid] <;> omega

private theorem valid4 (r : Register) (h : Frame r) (j : Fin 12) (k : Fin 10) :
    (test r 4 j.val).valid k.val := by
  have bound := k.isLt
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,_,_,_,_⟩ := h
  fin_cases j <;> norm_num [test,Test.valid,Line.valid] <;> omega

private theorem valid5 (r : Register) (h : Frame r) (j : Fin 12) (k : Fin 10) :
    (test r 5 j.val).valid k.val := by
  have bound := k.isLt
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,_,_,_,_⟩ := h
  fin_cases j <;> norm_num [test,Test.valid,Line.valid] <;> omega

private theorem valid6 (r : Register) (h : Frame r) (j : Fin 12) (k : Fin 10) :
    (test r 6 j.val).valid k.val := by
  have bound := k.isLt
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,_,_,_,_⟩ := h
  fin_cases j <;> norm_num [test,Test.valid,Line.valid] <;> omega

private theorem valid7 (r : Register) (h : Frame r) (j : Fin 12) (k : Fin 10) :
    (test r 7 j.val).valid k.val := by
  have bound := k.isLt
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,_,_,_,_⟩ := h
  fin_cases j <;> norm_num [test,Test.valid,Line.valid] <;> omega

private theorem valid8 (r : Register) (h : Frame r) (j : Fin 12) (k : Fin 10) :
    (test r 8 j.val).valid k.val := by
  have bound := k.isLt
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,_,_,_,_⟩ := h
  fin_cases j <;> norm_num [test,Test.valid,Line.valid] <;> omega

private theorem valid9 (r : Register) (h : Frame r) (j : Fin 12) (k : Fin 10) :
    (test r 9 j.val).valid k.val := by
  have bound := k.isLt
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,_,_,_,_⟩ := h
  fin_cases j <;> norm_num [test,Test.valid,Line.valid] <;> omega

private theorem ok (r : Register) (h : Frame r) (i : Fin 10) (j : Fin 12) (k : Fin 10) :
    (test r i.val j.val).valid k.val := by
  fin_cases i
  · exact valid0 r h j k
  · exact valid1 r h j k
  · exact valid2 r h j k
  · exact valid3 r h j k
  · exact valid4 r h j k
  · exact valid5 r h j k
  · exact valid6 r h j k
  · exact valid7 r h j k
  · exact valid8 r h j k
  · exact valid9 r h j k

private theorem positive (r : Register) (h : Frame r) (i : Fin 10) (hit : contains r i.val) : Pos r i.val := by
  intro j k
  have bound : arity i.val≤12 := by fin_cases i <;> decide
  exact Test.bounds _ true _ (ok r h i ⟨j.val,by have := j.isLt; omega⟩ k) (hit j)

private abbrev Outside0 (r : Register) := Neg r 0 0 ∨ Neg r 0 1 ∨ Neg r 0 2 ∨ Neg r 0 3
private theorem outside0 {r : Register} (h : Frame r) (miss : ¬contains r 0) : Outside0 r := by
  unfold contains at miss
  push Not at miss
  obtain ⟨j,hj⟩ := miss
  have N : Neg r 0 j.val := fun k =>
    Test.bounds _ false _ (ok r h 0 ⟨j.val,by have hh := j.isLt; change j.val < 4 at hh; omega⟩ k) hj
  change Fin 4 at j
  fin_cases j <;> unfold Outside0 <;> tauto

private abbrev Outside9 (r : Register) := Neg r 9 0 ∨ Neg r 9 1 ∨ Neg r 9 2 ∨ Neg r 9 3
private theorem outside9 {r : Register} (h : Frame r) (miss : ¬contains r 9) : Outside9 r := by
  unfold contains at miss
  push Not at miss
  obtain ⟨j,hj⟩ := miss
  have N : Neg r 9 j.val := fun k =>
    Test.bounds _ false _ (ok r h 9 ⟨j.val,by have hh := j.isLt; change j.val < 4 at hh; omega⟩ k) hj
  change Fin 4 at j
  fin_cases j <;> unfold Outside9 <;> tauto

private abbrev Outside1 (r : Register) := Neg r 1 0 ∨ Neg r 1 1 ∨ Neg r 1 2 ∨ Neg r 1 3
private theorem outside1 {r : Register} (h : Frame r) (miss : ¬contains r 1) : Outside1 r := by
  unfold contains at miss
  push Not at miss
  obtain ⟨j,hj⟩ := miss
  have N : Neg r 1 j.val := fun k =>
    Test.bounds _ false _ (ok r h 1 ⟨j.val,by have hh := j.isLt; change j.val < 4 at hh; omega⟩ k) hj
  change Fin 4 at j
  fin_cases j <;> unfold Outside1 <;> tauto

private abbrev Outside2 (r : Register) := Neg r 2 0 ∨ Neg r 2 1 ∨ Neg r 2 2 ∨ Neg r 2 3
private theorem outside2 {r : Register} (h : Frame r) (miss : ¬contains r 2) : Outside2 r := by
  unfold contains at miss
  push Not at miss
  obtain ⟨j,hj⟩ := miss
  have N : Neg r 2 j.val := fun k =>
    Test.bounds _ false _ (ok r h 2 ⟨j.val,by have hh := j.isLt; change j.val < 4 at hh; omega⟩ k) hj
  change Fin 4 at j
  fin_cases j <;> unfold Outside2 <;> tauto

private abbrev Outside3 (r : Register) := Neg r 3 0 ∨ Neg r 3 1 ∨ Neg r 3 2 ∨ Neg r 3 3
private theorem outside3 {r : Register} (h : Frame r) (miss : ¬contains r 3) : Outside3 r := by
  unfold contains at miss
  push Not at miss
  obtain ⟨j,hj⟩ := miss
  have N : Neg r 3 j.val := fun k =>
    Test.bounds _ false _ (ok r h 3 ⟨j.val,by have hh := j.isLt; change j.val < 4 at hh; omega⟩ k) hj
  change Fin 4 at j
  fin_cases j <;> unfold Outside3 <;> tauto

private abbrev Outside4 (r : Register) := Neg r 4 0 ∨ Neg r 4 1 ∨ Neg r 4 2 ∨ Neg r 4 3
private theorem outside4 {r : Register} (h : Frame r) (miss : ¬contains r 4) : Outside4 r := by
  unfold contains at miss
  push Not at miss
  obtain ⟨j,hj⟩ := miss
  have N : Neg r 4 j.val := fun k =>
    Test.bounds _ false _ (ok r h 4 ⟨j.val,by have hh := j.isLt; change j.val < 4 at hh; omega⟩ k) hj
  change Fin 4 at j
  fin_cases j <;> unfold Outside4 <;> tauto

private abbrev Outside5 (r : Register) := Neg r 5 0 ∨ Neg r 5 1 ∨ Neg r 5 2 ∨ Neg r 5 3
private theorem outside5 {r : Register} (h : Frame r) (miss : ¬contains r 5) : Outside5 r := by
  unfold contains at miss
  push Not at miss
  obtain ⟨j,hj⟩ := miss
  have N : Neg r 5 j.val := fun k =>
    Test.bounds _ false _ (ok r h 5 ⟨j.val,by have hh := j.isLt; change j.val < 4 at hh; omega⟩ k) hj
  change Fin 4 at j
  fin_cases j <;> unfold Outside5 <;> tauto

private abbrev Outside6 (r : Register) := Neg r 6 0 ∨ Neg r 6 1 ∨ Neg r 6 2 ∨ Neg r 6 3
private theorem outside6 {r : Register} (h : Frame r) (miss : ¬contains r 6) : Outside6 r := by
  unfold contains at miss
  push Not at miss
  obtain ⟨j,hj⟩ := miss
  have N : Neg r 6 j.val := fun k =>
    Test.bounds _ false _ (ok r h 6 ⟨j.val,by have hh := j.isLt; change j.val < 4 at hh; omega⟩ k) hj
  change Fin 4 at j
  fin_cases j <;> unfold Outside6 <;> tauto

private abbrev Outside7 (r : Register) := Neg r 7 0 ∨ Neg r 7 1 ∨ Neg r 7 2 ∨ Neg r 7 3 ∨ Neg r 7 4 ∨ Neg r 7 5 ∨ Neg r 7 6 ∨ Neg r 7 7
private theorem outside7 {r : Register} (h : Frame r) (miss : ¬contains r 7) : Outside7 r := by
  unfold contains at miss
  push Not at miss
  obtain ⟨j,hj⟩ := miss
  have N : Neg r 7 j.val := fun k =>
    Test.bounds _ false _ (ok r h 7 ⟨j.val,by have hh := j.isLt; change j.val < 8 at hh; omega⟩ k) hj
  change Fin 8 at j
  fin_cases j <;> unfold Outside7 <;> tauto

private abbrev Outside8 (r : Register) := Neg r 8 0 ∨ Neg r 8 1 ∨ Neg r 8 2 ∨ Neg r 8 3 ∨ Neg r 8 4 ∨ Neg r 8 5 ∨ Neg r 8 6 ∨ Neg r 8 7
private theorem outside8 {r : Register} (h : Frame r) (miss : ¬contains r 8) : Outside8 r := by
  unfold contains at miss
  push Not at miss
  obtain ⟨j,hj⟩ := miss
  have N : Neg r 8 j.val := fun k =>
    Test.bounds _ false _ (ok r h 8 ⟨j.val,by have hh := j.isLt; change j.val < 8 at hh; omega⟩ k) hj
  change Fin 8 at j
  fin_cases j <;> unfold Outside8 <;> tauto

private theorem cell0 {r : Register} (h : Frame r) (n_3_0 : Neg r 3 0) (n_5_0 : Neg r 5 0) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, h.f8, h.f10, h.f11, n_3_0 0, n_5_0 4, p ⟨0,by decide⟩ 0, p ⟨0,by decide⟩ 1, p ⟨0,by decide⟩ 2, p ⟨0,by decide⟩ 3, p ⟨0,by decide⟩ 4, p ⟨1,by decide⟩ 0, p ⟨3,by decide⟩ 0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f12]

private theorem cell1 {r : Register} (h : Frame r) (n_3_0 : Neg r 3 0) (n_5_1 : Neg r 5 1) : False := by
  lin_close [h.f0, h.f3, h.f8, h.f10, n_3_0 0, n_5_1 0, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f9, h.f11, h.f12]

private theorem cell2 {r : Register} (h : Frame r) (n_3_0 : Neg r 3 0) (n_5_2 : Neg r 5 2) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f8, h.f10, n_3_0 0, n_5_2 0, p ⟨0,by decide⟩ 4, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f11, h.f12]

private theorem cell3 {r : Register} (h : Frame r) (n_2_0 : Neg r 2 0) (n_3_0 : Neg r 3 0) (n_5_3 : Neg r 5 3) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, h.f3, h.f8, h.f10, h.f11, n_2_0 0, n_3_0 0, n_5_3 6, p ⟨0,by decide⟩ 0, p ⟨0,by decide⟩ 1, p ⟨0,by decide⟩ 2, p ⟨0,by decide⟩ 3, p ⟨1,by decide⟩ 0, p ⟨3,by decide⟩ 0, p ⟨3,by decide⟩ 5, h.f1, h.f4, h.f5, h.f6, h.f7, h.f9, h.f12]

private theorem cell4 {r : Register} (h : Frame r) (n_2_0 : Neg r 2 0) (n_3_1 : Neg r 3 1) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f3, h.f8, h.f10, h.f11, n_2_0 0, n_2_0 6, n_2_0 7, n_3_1 0, p ⟨1,by decide⟩ 0, p ⟨2,by decide⟩ 4, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f9, h.f12]

private theorem cell5 {r : Register} (h : Frame r) (n_2_0 : Neg r 2 0) (n_3_2 : Neg r 3 2) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f8, h.f10, h.f11, n_2_0 0, n_3_2 0, p ⟨1,by decide⟩ 0, p ⟨2,by decide⟩ 4, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f12]

private theorem cell6 {r : Register} (h : Frame r) (n_3_3 : Neg r 3 3) (n_5_0 : Neg r 5 0) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, h.f10, h.f11, n_3_3 0, n_5_0 4, n_5_0 5, p ⟨0,by decide⟩ 0, p ⟨0,by decide⟩ 1, p ⟨0,by decide⟩ 2, p ⟨0,by decide⟩ 3, p ⟨0,by decide⟩ 4, p ⟨1,by decide⟩ 0, p ⟨3,by decide⟩ 0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f12]

private theorem cell7 {r : Register} (h : Frame r) (n_2_0 : Neg r 2 0) (n_3_3 : Neg r 3 3) (n_5_1 : Neg r 5 1) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, h.f3, h.f8, h.f9, h.f10, h.f11, h.f12, n_2_0 6, n_3_3 0, n_5_1 0, p ⟨0,by decide⟩ 0, p ⟨3,by decide⟩ 0, p ⟨3,by decide⟩ 1, p ⟨3,by decide⟩ 2, p ⟨3,by decide⟩ 3, p ⟨3,by decide⟩ 4, p ⟨3,by decide⟩ 5, h.f1, h.f4, h.f5, h.f6, h.f7]

private theorem cell8 {r : Register} (h : Frame r) (n_2_0 : Neg r 2 0) (n_3_3 : Neg r 3 3) (n_5_2 : Neg r 5 2) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, h.f8, h.f10, h.f11, n_2_0 0, n_2_0 6, n_3_3 0, n_5_2 0, n_5_2 6, p ⟨0,by decide⟩ 1, p ⟨0,by decide⟩ 4, p ⟨3,by decide⟩ 0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f12]

private theorem cell9 {r : Register} (h : Frame r) (n_2_0 : Neg r 2 0) (n_3_3 : Neg r 3 3) (n_5_3 : Neg r 5 3) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, h.f3, h.f8, h.f10, h.f11, n_2_0 5, n_3_3 0, n_5_3 0, n_5_3 6, p ⟨0,by decide⟩ 0, p ⟨0,by decide⟩ 1, p ⟨0,by decide⟩ 2, p ⟨0,by decide⟩ 3, p ⟨1,by decide⟩ 0, p ⟨3,by decide⟩ 0, p ⟨3,by decide⟩ 5, h.f1, h.f4, h.f5, h.f6, h.f7, h.f9, h.f12]

private theorem cell10 {r : Register} (h : Frame r) (n_2_1 : Neg r 2 1) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, h.f3, h.f8, h.f10, h.f11, n_2_1 0, n_2_1 4, n_2_1 5, p ⟨0,by decide⟩ 0, p ⟨1,by decide⟩ 0, p ⟨1,by decide⟩ 2, p ⟨1,by decide⟩ 3, p ⟨1,by decide⟩ 4, p ⟨1,by decide⟩ 5, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 4, p ⟨3,by decide⟩ 5, h.f1, h.f4, h.f5, h.f6, h.f7, h.f9, h.f12]

private theorem cell11 {r : Register} (h : Frame r) (n_2_2 : Neg r 2 2) (n_3_0 : Neg r 3 0) (n_4_0 : Neg r 4 0) (n_5_0 : Neg r 5 0) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f10, n_2_2 0, n_3_0 0, n_4_0 0, n_5_0 4, p ⟨0,by decide⟩ 0, p ⟨0,by decide⟩ 1, p ⟨0,by decide⟩ 2, p ⟨0,by decide⟩ 3, p ⟨0,by decide⟩ 4, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f11, h.f12]

private theorem cell12 {r : Register} (h : Frame r) (n_2_2 : Neg r 2 2) (n_3_0 : Neg r 3 0) (n_4_0 : Neg r 4 0) (n_5_3 : Neg r 5 3) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, h.f8, h.f10, n_2_2 0, n_3_0 0, n_4_0 0, n_5_3 0, n_5_3 6, p ⟨0,by decide⟩ 0, p ⟨0,by decide⟩ 1, p ⟨0,by decide⟩ 2, p ⟨0,by decide⟩ 3, p ⟨3,by decide⟩ 5, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f11, h.f12]

private theorem cell13 {r : Register} (h : Frame r) (n_1_0 : Neg r 1 0) (n_3_1 : Neg r 3 1) (n_4_0 : Neg r 4 0) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f3, n_1_0 5, n_3_1 0, n_4_0 0, p ⟨1,by decide⟩ 0, p ⟨2,by decide⟩ 4, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f10, h.f11, h.f12]

private theorem cell14 {r : Register} (h : Frame r) (n_3_2 : Neg r 3 2) (n_4_0 : Neg r 4 0) (p : Pos r 0) : False := by
  lin_close [h.f0, n_3_2 0, n_4_0 0, p ⟨1,by decide⟩ 0, p ⟨2,by decide⟩ 4, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f10, h.f11, h.f12]

private theorem cell15 {r : Register} (h : Frame r) (n_2_2 : Neg r 2 2) (n_3_3 : Neg r 3 3) (n_4_0 : Neg r 4 0) (n_5_0 : Neg r 5 0) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, h.f10, n_2_2 0, n_3_3 0, n_4_0 0, n_5_0 4, n_5_0 5, p ⟨0,by decide⟩ 0, p ⟨0,by decide⟩ 1, p ⟨0,by decide⟩ 2, p ⟨0,by decide⟩ 3, p ⟨0,by decide⟩ 4, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f11, h.f12]

private theorem cell16 {r : Register} (h : Frame r) (n_1_0 : Neg r 1 0) (n_2_2 : Neg r 2 2) (n_3_3 : Neg r 3 3) (n_5_1 : Neg r 5 1) : False := by
  lin_close [h.f0, h.f3, h.f8, n_1_0 0, n_1_0 4, n_2_2 5, n_3_3 0, n_5_1 0, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f9, h.f10, h.f11, h.f12]

private theorem cell17 {r : Register} (h : Frame r) (n_3_3 : Neg r 3 3) (n_5_2 : Neg r 5 2) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, h.f8, h.f10, n_3_3 0, n_5_2 6, p ⟨0,by decide⟩ 0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f11, h.f12]

private theorem cell18 {r : Register} (h : Frame r) (n_1_0 : Neg r 1 0) (n_2_2 : Neg r 2 2) (n_3_3 : Neg r 3 3) (n_4_0 : Neg r 4 0) (n_5_3 : Neg r 5 3) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, h.f3, h.f8, h.f9, h.f10, n_1_0 4, n_2_2 0, n_3_3 0, n_4_0 0, n_5_3 6, p ⟨0,by decide⟩ 0, p ⟨0,by decide⟩ 1, p ⟨0,by decide⟩ 2, p ⟨0,by decide⟩ 3, p ⟨3,by decide⟩ 5, h.f1, h.f4, h.f5, h.f6, h.f7, h.f11, h.f12]

private theorem cell19 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_4_0 : Neg r 4 0) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f3, h.f8, h.f10, h.f11, h.f12, n_1_1 0, n_1_1 6, n_1_1 7, n_4_0 0, p ⟨0,by decide⟩ 0, p ⟨1,by decide⟩ 0, p ⟨2,by decide⟩ 4, p ⟨3,by decide⟩ 4, p ⟨3,by decide⟩ 5, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f9]

private theorem cell20 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_3_0 : Neg r 3 0) (n_4_0 : Neg r 4 0) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f10, n_1_2 0, n_3_0 0, n_4_0 0, p ⟨0,by decide⟩ 0, p ⟨0,by decide⟩ 1, p ⟨0,by decide⟩ 2, p ⟨0,by decide⟩ 3, p ⟨0,by decide⟩ 4, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f11, h.f12]

private theorem cell21 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_3_1 : Neg r 3 1) (n_4_0 : Neg r 4 0) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f8, h.f9, h.f10, h.f11, h.f12, h.site1, n_1_2 5, n_1_2 6, n_3_1 0, n_4_0 0, p ⟨0,by decide⟩ 0, p ⟨1,by decide⟩ 0, p ⟨2,by decide⟩ 4, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7]

private theorem cell22 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_3_3 : Neg r 3 3) : False := by
  lin_close [h.f0, h.f2, h.f10, h.f11, n_1_2 0, n_3_3 0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f12]

private theorem cell23 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_3_1 : Neg r 3 1) (n_4_0 : Neg r 4 0) (n_7_0 : Neg r 7 0) : False := by
  lin_close [h.f0, h.f3, n_1_3 6, n_3_1 0, n_4_0 0, n_7_0 0, n_7_0 5, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f10, h.f11, h.f12]

private theorem cell24 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_2_2 : Neg r 2 2) (n_3_1 : Neg r 3 1) (n_4_0 : Neg r 4 0) (n_6_0 : Neg r 6 0) (n_7_1 : Neg r 7 1) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f3, n_1_3 6, n_2_2 5, n_3_1 0, n_4_0 0, n_6_0 0, n_6_0 5, n_7_1 0, n_7_1 7, p ⟨1,by decide⟩ 0, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f10, h.f11, h.f12]

private theorem cell25 {r : Register} (h : Frame r) (n_6_1 : Neg r 6 1) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f10, n_6_1 0, p ⟨1,by decide⟩ 0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f11, h.f12]

private theorem cell26 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_2_2 : Neg r 2 2) (n_4_0 : Neg r 4 0) (n_6_2 : Neg r 6 2) (n_7_1 : Neg r 7 1) : False := by
  lin_close [h.f0, h.f2, h.f3, h.f9, n_1_3 6, n_2_2 0, n_4_0 0, n_6_2 0, n_6_2 5, n_6_2 6, n_7_1 5, h.f1, h.f4, h.f5, h.f6, h.f7, h.f8, h.f10, h.f11, h.f12]

private theorem cell27 {r : Register} (h : Frame r) (n_2_2 : Neg r 2 2) (n_6_3 : Neg r 6 3) (n_7_1 : Neg r 7 1) (n_8_0 : Neg r 8 0) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f10, h.f11, n_2_2 0, n_6_3 0, n_7_1 0, n_8_0 0, p ⟨1,by decide⟩ 0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f12]

private theorem cell28 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_3_1 : Neg r 3 1) (n_4_0 : Neg r 4 0) (n_8_1 : Neg r 8 1) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f3, h.f10, h.f12, n_1_3 0, n_3_1 0, n_4_0 0, n_8_1 6, p ⟨0,by decide⟩ 0, p ⟨3,by decide⟩ 2, p ⟨3,by decide⟩ 3, p ⟨3,by decide⟩ 4, p ⟨3,by decide⟩ 5, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f11]

private theorem cell29 {r : Register} (h : Frame r) (n_4_0 : Neg r 4 0) (n_6_3 : Neg r 6 3) (n_7_1 : Neg r 7 1) (n_8_2 : Neg r 8 2) : False := by
  lin_close [h.f0, h.f8, n_4_0 0, n_6_3 0, n_7_1 0, n_8_2 0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f10, h.f11, h.f12]

private theorem cell30 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_2_2 : Neg r 2 2) (n_3_1 : Neg r 3 1) (n_4_0 : Neg r 4 0) (n_8_3 : Neg r 8 3) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f3, h.f10, h.f12, n_1_3 0, n_2_2 0, n_3_1 0, n_4_0 0, n_8_3 0, p ⟨0,by decide⟩ 0, p ⟨3,by decide⟩ 2, p ⟨3,by decide⟩ 3, p ⟨3,by decide⟩ 4, p ⟨3,by decide⟩ 5, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f11]

private theorem cell31 {r : Register} (h : Frame r) (n_8_4 : Neg r 8 4) : False := by
  lin_close [h.f1, h.f2, h.f3, n_8_4 0, n_8_4 1, h.f0, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f10, h.f11, h.f12]

private theorem cell32 {r : Register} (h : Frame r) (n_3_1 : Neg r 3 1) (n_8_5 : Neg r 8 5) : False := by
  lin_close [h.f3, n_3_1 0, n_8_5 3, h.f0, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f10, h.f11, h.f12]

private theorem cell33 {r : Register} (h : Frame r) (n_6_3 : Neg r 6 3) (n_8_6 : Neg r 8 6) : False := by
  lin_close [h.f0, h.f2, n_6_3 0, n_8_6 1, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f10, h.f11, h.f12]

private theorem cell34 {r : Register} (h : Frame r) (n_6_3 : Neg r 6 3) (n_8_7 : Neg r 8 7) : False := by
  lin_close [h.f0, h.f2, n_6_3 0, n_8_7 1, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f10, h.f11, h.f12]

private theorem cell35 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_4_0 : Neg r 4 0) (n_7_2 : Neg r 7 2) : False := by
  lin_close [h.f2, h.f3, n_1_3 6, n_4_0 0, n_7_2 0, h.f0, h.f1, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f10, h.f11, h.f12]

private theorem cell36 {r : Register} (h : Frame r) (n_3_1 : Neg r 3 1) (n_5_0 : Neg r 5 0) : False := by
  lin_close [h.f0, h.f3, h.f10, n_3_1 0, n_5_0 0, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f11, h.f12]

private theorem cell37 {r : Register} (h : Frame r) (n_2_2 : Neg r 2 2) (n_3_1 : Neg r 3 1) (n_4_0 : Neg r 4 0) (n_5_1 : Neg r 5 1) (n_7_3 : Neg r 7 3) (n_8_0 : Neg r 8 0) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f3, h.f12, n_2_2 0, n_3_1 0, n_4_0 0, n_5_1 6, n_7_3 0, n_8_0 0, n_8_0 5, p ⟨0,by decide⟩ 0, p ⟨3,by decide⟩ 2, p ⟨3,by decide⟩ 3, p ⟨3,by decide⟩ 4, p ⟨3,by decide⟩ 5, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f10, h.f11]

private theorem cell38 {r : Register} (h : Frame r) (n_3_1 : Neg r 3 1) (n_5_2 : Neg r 5 2) (n_7_3 : Neg r 7 3) (n_8_0 : Neg r 8 0) : False := by
  lin_close [h.f0, h.f8, n_3_1 0, n_5_2 0, n_7_3 0, n_8_0 0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f10, h.f11, h.f12]

private theorem cell39 {r : Register} (h : Frame r) (n_2_2 : Neg r 2 2) (n_3_1 : Neg r 3 1) (n_4_0 : Neg r 4 0) (n_5_3 : Neg r 5 3) (n_7_3 : Neg r 7 3) (n_8_0 : Neg r 8 0) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, h.f3, h.f12, n_2_2 0, n_2_2 5, n_3_1 0, n_4_0 0, n_5_3 0, n_5_3 6, n_5_3 7, n_7_3 0, n_8_0 0, n_8_0 4, p ⟨0,by decide⟩ 0, p ⟨3,by decide⟩ 2, p ⟨3,by decide⟩ 3, p ⟨3,by decide⟩ 4, p ⟨3,by decide⟩ 5, h.f1, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f10, h.f11]

private theorem cell40 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_2_2 : Neg r 2 2) (n_3_1 : Neg r 3 1) (n_4_0 : Neg r 4 0) (n_8_1 : Neg r 8 1) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f3, h.f10, h.f12, n_1_3 0, n_2_2 0, n_3_1 0, n_4_0 0, n_8_1 6, p ⟨0,by decide⟩ 0, p ⟨1,by decide⟩ 0, p ⟨3,by decide⟩ 2, p ⟨3,by decide⟩ 3, p ⟨3,by decide⟩ 4, p ⟨3,by decide⟩ 5, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f11]

private theorem cell41 {r : Register} (h : Frame r) (n_7_3 : Neg r 7 3) (n_8_2 : Neg r 8 2) : False := by
  lin_close [h.f0, h.f2, h.f8, n_7_3 0, n_8_2 0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f10, h.f11, h.f12]

private theorem cell42 {r : Register} (h : Frame r) (n_3_1 : Neg r 3 1) (n_7_3 : Neg r 7 3) (n_8_4 : Neg r 8 4) : False := by
  lin_close [h.f0, n_3_1 0, n_7_3 0, n_8_4 1, n_8_4 3, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f10, h.f11, h.f12]

private theorem cell43 {r : Register} (h : Frame r) (n_3_1 : Neg r 3 1) (n_7_3 : Neg r 7 3) (n_8_5 : Neg r 8 5) : False := by
  lin_close [n_3_1 0, n_7_3 0, n_8_5 1, n_8_5 3, h.f0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f10, h.f11, h.f12]

private theorem cell44 {r : Register} (h : Frame r) (n_7_3 : Neg r 7 3) (n_8_6 : Neg r 8 6) : False := by
  lin_close [h.f0, h.f2, n_7_3 0, n_8_6 1, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f10, h.f11, h.f12]

private theorem cell45 {r : Register} (h : Frame r) (n_7_3 : Neg r 7 3) (n_8_7 : Neg r 8 7) : False := by
  lin_close [h.f0, h.f2, n_7_3 0, n_8_7 1, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f10, h.f11, h.f12]

private theorem cell46 {r : Register} (h : Frame r) (n_7_4 : Neg r 7 4) : False := by
  lin_close [h.f1, h.f2, h.f3, n_7_4 0, n_7_4 1, h.f0, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f10, h.f11, h.f12]

private theorem cell47 {r : Register} (h : Frame r) (n_3_1 : Neg r 3 1) (n_7_5 : Neg r 7 5) : False := by
  lin_close [h.f3, n_3_1 0, n_7_5 3, h.f0, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f10, h.f11, h.f12]

private theorem cell48 {r : Register} (h : Frame r) (n_4_0 : Neg r 4 0) (n_7_6 : Neg r 7 6) : False := by
  lin_close [h.f2, h.f9, n_4_0 0, n_7_6 2, h.f0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f10, h.f11, h.f12]

private theorem cell49 {r : Register} (h : Frame r) (n_7_7 : Neg r 7 7) : False := by
  lin_close [h.f1, h.f2, h.f3, n_7_7 0, n_7_7 1, h.f0, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f10, h.f11, h.f12]

private theorem cell50 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_3_2 : Neg r 3 2) : False := by
  lin_close [h.f0, h.f2, h.f8, h.f10, h.f11, n_1_3 0, n_3_2 0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f12]

private theorem cell51 {r : Register} (h : Frame r) (n_2_2 : Neg r 2 2) (n_3_3 : Neg r 3 3) (n_4_0 : Neg r 4 0) (n_5_1 : Neg r 5 1) (n_8_0 : Neg r 8 0) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f3, h.f10, h.f11, h.f12, n_2_2 0, n_3_3 0, n_4_0 0, n_5_1 0, n_5_1 6, n_8_0 0, n_8_0 5, p ⟨0,by decide⟩ 0, p ⟨3,by decide⟩ 2, p ⟨3,by decide⟩ 3, p ⟨3,by decide⟩ 4, p ⟨3,by decide⟩ 5, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9]

private theorem cell52 {r : Register} (h : Frame r) (n_2_2 : Neg r 2 2) (n_3_3 : Neg r 3 3) (n_4_0 : Neg r 4 0) (n_8_1 : Neg r 8 1) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f3, h.f9, h.f10, h.f11, h.f12, n_2_2 0, n_3_3 0, n_4_0 0, n_8_1 0, n_8_1 6, p ⟨0,by decide⟩ 0, p ⟨3,by decide⟩ 2, p ⟨3,by decide⟩ 3, p ⟨3,by decide⟩ 4, p ⟨3,by decide⟩ 5, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f8]

private theorem cell53 {r : Register} (h : Frame r) (n_3_3 : Neg r 3 3) (n_8_2 : Neg r 8 2) : False := by
  lin_close [h.f2, n_3_3 0, n_8_2 0, h.f0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f10, h.f11, h.f12]

private theorem cell54 {r : Register} (h : Frame r) (n_2_2 : Neg r 2 2) (n_3_3 : Neg r 3 3) (n_4_0 : Neg r 4 0) (n_5_1 : Neg r 5 1) (n_8_3 : Neg r 8 3) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f3, h.f10, h.f11, h.f12, n_2_2 0, n_3_3 0, n_4_0 0, n_5_1 0, n_8_3 0, p ⟨0,by decide⟩ 0, p ⟨3,by decide⟩ 2, p ⟨3,by decide⟩ 3, p ⟨3,by decide⟩ 4, p ⟨3,by decide⟩ 5, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9]

private theorem cell55 {r : Register} (h : Frame r) (n_5_1 : Neg r 5 1) (n_8_5 : Neg r 8 5) : False := by
  lin_close [h.f0, h.f3, h.f8, n_5_1 0, n_8_5 3, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f9, h.f10, h.f11, h.f12]

private theorem cell56 {r : Register} (h : Frame r) (n_3_3 : Neg r 3 3) (n_8_6 : Neg r 8 6) : False := by
  lin_close [h.f2, h.f9, n_3_3 0, n_8_6 1, h.f0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f10, h.f11, h.f12]

private theorem cell57 {r : Register} (h : Frame r) (n_8_7 : Neg r 8 7) : False := by
  lin_close [h.f1, h.f2, h.f3, n_8_7 0, n_8_7 1, h.f0, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f10, h.f11, h.f12]

private theorem cell58 {r : Register} (h : Frame r) (n_2_2 : Neg r 2 2) (n_4_0 : Neg r 4 0) (n_5_3 : Neg r 5 3) (n_8_0 : Neg r 8 0) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, h.f3, h.f8, h.f10, n_2_2 0, n_2_2 5, n_4_0 0, n_5_3 0, n_5_3 6, n_5_3 7, n_8_0 0, n_8_0 4, p ⟨0,by decide⟩ 0, p ⟨0,by decide⟩ 1, p ⟨0,by decide⟩ 2, p ⟨0,by decide⟩ 3, p ⟨3,by decide⟩ 5, h.f1, h.f4, h.f5, h.f6, h.f7, h.f9, h.f11, h.f12]

private theorem cell59 {r : Register} (h : Frame r) (n_2_2 : Neg r 2 2) (n_4_0 : Neg r 4 0) (n_8_3 : Neg r 8 3) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, h.f10, n_2_2 0, n_4_0 0, n_8_3 0, p ⟨0,by decide⟩ 0, p ⟨0,by decide⟩ 1, p ⟨0,by decide⟩ 2, p ⟨0,by decide⟩ 3, p ⟨3,by decide⟩ 5, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f11, h.f12]

private theorem cell60 {r : Register} (h : Frame r) (n_3_3 : Neg r 3 3) (n_5_3 : Neg r 5 3) (n_8_5 : Neg r 8 5) : False := by
  lin_close [h.f2, h.f9, h.f10, h.f12, n_3_3 0, n_5_3 0, n_8_5 1, h.f0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f11]

private theorem cell61 {r : Register} (h : Frame r) (n_4_1 : Neg r 4 1) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f10, n_4_1 0, p ⟨1,by decide⟩ 0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f11, h.f12]

private theorem cell62 {r : Register} (h : Frame r) (n_3_0 : Neg r 3 0) (n_4_2 : Neg r 4 2) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f9, h.f10, n_3_0 0, n_4_2 0, p ⟨0,by decide⟩ 4, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f11, h.f12]

private theorem cell63 {r : Register} (h : Frame r) (n_1_0 : Neg r 1 0) (n_4_2 : Neg r 4 2) (n_5_1 : Neg r 5 1) : False := by
  lin_close [h.f0, h.f2, h.f3, h.f8, h.f9, n_1_0 0, n_4_2 0, n_5_1 5, h.f1, h.f4, h.f5, h.f6, h.f7, h.f10, h.f11, h.f12]

private theorem cell64 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_4_2 : Neg r 4 2) (n_6_0 : Neg r 6 0) : False := by
  lin_close [h.f0, h.f3, h.f8, h.f11, n_1_1 0, n_1_1 6, n_1_1 7, n_4_2 0, n_6_0 0, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f9, h.f10, h.f12]

private theorem cell65 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_6_2 : Neg r 6 2) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, h.f10, n_1_1 5, n_1_1 6, n_6_2 0, p ⟨0,by decide⟩ 0, p ⟨1,by decide⟩ 0, p ⟨1,by decide⟩ 1, p ⟨1,by decide⟩ 4, p ⟨1,by decide⟩ 5, p ⟨2,by decide⟩ 0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f11, h.f12]

private theorem cell66 {r : Register} (h : Frame r) (n_3_1 : Neg r 3 1) (n_4_2 : Neg r 4 2) (n_5_1 : Neg r 5 1) (n_6_3 : Neg r 6 3) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, h.f8, h.f10, n_3_1 0, n_4_2 0, n_5_1 0, n_6_3 0, n_6_3 6, p ⟨0,by decide⟩ 0, p ⟨1,by decide⟩ 0, p ⟨1,by decide⟩ 1, p ⟨1,by decide⟩ 2, p ⟨1,by decide⟩ 3, p ⟨1,by decide⟩ 4, p ⟨1,by decide⟩ 5, p ⟨2,by decide⟩ 0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f11, h.f12]

private theorem cell67 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_3_1 : Neg r 3 1) (n_5_1 : Neg r 5 1) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, h.f3, h.f8, h.f9, h.f10, h.f11, n_1_2 0, n_1_2 5, n_3_1 0, n_5_1 2, p ⟨0,by decide⟩ 0, p ⟨1,by decide⟩ 0, p ⟨1,by decide⟩ 1, p ⟨1,by decide⟩ 2, p ⟨1,by decide⟩ 3, p ⟨1,by decide⟩ 4, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 4, h.f1, h.f4, h.f5, h.f6, h.f7, h.f12]

private theorem cell68 {r : Register} (h : Frame r) (n_4_2 : Neg r 4 2) (n_5_1 : Neg r 5 1) (n_7_0 : Neg r 7 0) : False := by
  lin_close [h.f0, h.f3, h.f8, n_4_2 0, n_5_1 0, n_5_1 5, n_7_0 0, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f9, h.f10, h.f11, h.f12]

private theorem cell69 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_4_2 : Neg r 4 2) (n_6_0 : Neg r 6 0) (n_7_1 : Neg r 7 1) : False := by
  lin_close [h.f0, h.f3, h.f10, h.f11, n_1_3 0, n_1_3 7, n_4_2 0, n_6_0 0, n_6_0 5, n_7_1 0, n_7_1 6, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f12]

private theorem cell70 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_6_0 : Neg r 6 0) (n_7_2 : Neg r 7 2) : False := by
  lin_close [h.f0, h.f2, h.f8, h.f10, h.f11, n_1_3 0, n_1_3 7, n_6_0 0, n_7_2 0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f12]

private theorem cell71 {r : Register} (h : Frame r) (n_4_2 : Neg r 4 2) (n_7_3 : Neg r 7 3) : False := by
  lin_close [h.f2, n_4_2 0, n_7_3 0, h.f0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f10, h.f11, h.f12]

private theorem cell72 {r : Register} (h : Frame r) (n_4_2 : Neg r 4 2) (n_5_1 : Neg r 5 1) (n_7_4 : Neg r 7 4) : False := by
  lin_close [h.f8, n_4_2 0, n_5_1 0, n_7_4 0, n_7_4 3, h.f0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f10, h.f11, h.f12]

private theorem cell73 {r : Register} (h : Frame r) (n_4_2 : Neg r 4 2) (n_7_5 : Neg r 7 5) : False := by
  lin_close [n_4_2 0, n_7_5 0, h.f0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f10, h.f11, h.f12]

private theorem cell74 {r : Register} (h : Frame r) (n_4_2 : Neg r 4 2) (n_6_0 : Neg r 6 0) (n_7_6 : Neg r 7 6) (p : Pos r 0) : False := by
  lin_close [h.f9, h.f10, n_4_2 0, n_6_0 5, n_7_6 0, n_7_6 2, p ⟨1,by decide⟩ 0, h.f0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f11, h.f12]

private theorem cell75 {r : Register} (h : Frame r) (n_4_2 : Neg r 4 2) (n_6_0 : Neg r 6 0) (n_7_7 : Neg r 7 7) (p : Pos r 0) : False := by
  lin_close [h.f8, h.f9, h.f12, n_4_2 0, n_6_0 0, n_7_7 0, n_7_7 1, n_7_7 2, p ⟨1,by decide⟩ 0, h.f0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f10, h.f11]

private theorem cell76 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_3_1 : Neg r 3 1) (n_5_1 : Neg r 5 1) (n_6_2 : Neg r 6 2) (n_7_1 : Neg r 7 1) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, h.f8, h.f10, h.f11, n_1_3 0, n_1_3 6, n_1_3 7, n_3_1 0, n_5_1 0, n_6_2 0, n_6_2 5, n_6_2 6, n_7_1 0, n_7_1 5, p ⟨1,by decide⟩ 1, p ⟨1,by decide⟩ 4, p ⟨1,by decide⟩ 5, p ⟨2,by decide⟩ 0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f12]

private theorem cell77 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_7_2 : Neg r 7 2) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, h.f8, h.f10, h.f11, n_1_3 7, n_7_2 0, p ⟨1,by decide⟩ 0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f12]

private theorem cell78 {r : Register} (h : Frame r) (n_4_2 : Neg r 4 2) (n_6_2 : Neg r 6 2) (n_7_6 : Neg r 7 6) : False := by
  lin_close [h.f3, h.f8, h.f9, h.f10, h.f12, n_4_2 0, n_6_2 0, n_7_6 0, h.f0, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f11]

private theorem cell79 {r : Register} (h : Frame r) (n_4_2 : Neg r 4 2) (n_6_2 : Neg r 6 2) (n_7_7 : Neg r 7 7) (p : Pos r 0) : False := by
  lin_close [h.f8, h.f9, h.f10, h.f12, n_4_2 0, n_6_2 0, n_7_7 0, n_7_7 2, p ⟨1,by decide⟩ 0, h.f0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f11]

private theorem cell80 {r : Register} (h : Frame r) (n_4_2 : Neg r 4 2) (n_6_3 : Neg r 6 3) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, h.f10, n_4_2 0, n_6_3 6, p ⟨1,by decide⟩ 0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f11, h.f12]

private theorem cell81 {r : Register} (h : Frame r) (n_1_0 : Neg r 1 0) (n_3_1 : Neg r 3 1) (n_4_2 : Neg r 4 2) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f3, h.f10, h.f11, n_1_0 0, n_1_0 5, n_3_1 0, n_4_2 0, p ⟨1,by decide⟩ 0, p ⟨2,by decide⟩ 1, p ⟨2,by decide⟩ 4, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f12]

private theorem cell82 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_6_0 : Neg r 6 0) : False := by
  lin_close [h.f0, h.f2, h.f3, h.f8, n_1_1 0, n_1_1 6, n_6_0 0, n_6_0 5, h.f1, h.f4, h.f5, h.f6, h.f7, h.f9, h.f10, h.f11, h.f12]

private theorem cell83 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_3_1 : Neg r 3 1) (n_6_0 : Neg r 6 0) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, h.f8, h.f10, h.f11, h.site1, n_1_2 5, n_1_2 6, n_3_1 0, n_6_0 0, p ⟨0,by decide⟩ 0, p ⟨1,by decide⟩ 0, p ⟨2,by decide⟩ 4, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f12]

private theorem cell84 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_3_1 : Neg r 3 1) (n_7_0 : Neg r 7 0) : False := by
  lin_close [h.f0, h.f3, n_1_3 0, n_3_1 0, n_7_0 0, n_7_0 5, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f10, h.f11, h.f12]

private theorem cell85 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_4_2 : Neg r 4 2) (n_6_0 : Neg r 6 0) (n_7_1 : Neg r 7 1) : False := by
  lin_close [h.f0, h.f2, h.f3, n_1_3 0, n_4_2 0, n_6_0 0, n_6_0 5, n_7_1 0, n_7_1 6, h.f1, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f10, h.f11, h.f12]

private theorem cell86 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_6_0 : Neg r 6 0) (n_7_2 : Neg r 7 2) : False := by
  lin_close [h.f0, h.f2, h.f8, n_1_3 0, n_1_3 6, n_6_0 5, n_7_2 0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f10, h.f11, h.f12]

private theorem cell87 {r : Register} (h : Frame r) (n_3_1 : Neg r 3 1) (n_4_2 : Neg r 4 2) (n_5_2 : Neg r 5 2) (n_7_4 : Neg r 7 4) : False := by
  lin_close [h.f8, n_3_1 0, n_4_2 0, n_5_2 0, n_7_4 0, n_7_4 3, h.f0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f10, h.f11, h.f12]

private theorem cell88 {r : Register} (h : Frame r) (n_4_2 : Neg r 4 2) (n_5_2 : Neg r 5 2) (n_6_0 : Neg r 6 0) (n_7_6 : Neg r 7 6) (p : Pos r 0) : False := by
  lin_close [h.f8, h.f9, h.f10, h.f11, n_4_2 0, n_5_2 2, n_6_0 0, n_7_6 0, n_7_6 2, p ⟨1,by decide⟩ 0, h.f0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f12]

private theorem cell89 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_6_2 : Neg r 6 2) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, h.f3, h.f8, h.f10, n_1_1 0, n_1_1 5, n_1_1 6, n_6_2 0, n_6_2 5, p ⟨0,by decide⟩ 0, p ⟨1,by decide⟩ 0, p ⟨1,by decide⟩ 1, p ⟨1,by decide⟩ 2, p ⟨1,by decide⟩ 3, p ⟨1,by decide⟩ 4, p ⟨1,by decide⟩ 5, p ⟨2,by decide⟩ 0, h.f1, h.f4, h.f5, h.f6, h.f7, h.f9, h.f11, h.f12]

private theorem cell90 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_3_1 : Neg r 3 1) (n_6_2 : Neg r 6 2) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, h.f8, h.f10, h.f11, h.site1, n_1_2 5, n_1_2 6, n_3_1 0, n_6_2 0, p ⟨0,by decide⟩ 0, p ⟨1,by decide⟩ 0, p ⟨1,by decide⟩ 1, p ⟨1,by decide⟩ 2, p ⟨1,by decide⟩ 3, p ⟨1,by decide⟩ 4, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 4, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f12]

private theorem cell91 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_3_1 : Neg r 3 1) (n_4_2 : Neg r 4 2) (n_7_0 : Neg r 7 0) : False := by
  lin_close [h.f0, h.f3, h.f10, h.f11, n_1_3 0, n_1_3 6, n_3_1 0, n_4_2 0, n_7_0 0, n_7_0 5, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f12]

private theorem cell92 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_3_1 : Neg r 3 1) (n_6_2 : Neg r 6 2) (n_7_1 : Neg r 7 1) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, h.f8, h.f10, h.f11, n_1_3 0, n_1_3 6, n_1_3 7, n_3_1 0, n_6_2 0, n_6_2 5, n_6_2 6, n_7_1 0, p ⟨0,by decide⟩ 0, p ⟨1,by decide⟩ 0, p ⟨1,by decide⟩ 4, p ⟨1,by decide⟩ 5, p ⟨2,by decide⟩ 0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f12]

private theorem cell93 {r : Register} (h : Frame r) (n_3_1 : Neg r 3 1) (n_4_2 : Neg r 4 2) (n_5_2 : Neg r 5 2) (n_6_3 : Neg r 6 3) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, h.f8, h.f9, h.f10, h.f12, n_3_1 0, n_4_2 0, n_5_2 4, n_5_2 5, n_6_3 0, p ⟨0,by decide⟩ 0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f11]

private theorem cell94 {r : Register} (h : Frame r) (n_4_2 : Neg r 4 2) (n_5_3 : Neg r 5 3) : False := by
  lin_close [h.f0, h.f2, h.f9, h.f10, n_4_2 0, n_5_3 0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f11, h.f12]

private theorem cell95 {r : Register} (h : Frame r) (n_3_2 : Neg r 3 2) (n_4_2 : Neg r 4 2) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, h.f9, h.f10, h.f11, n_3_2 0, n_4_2 0, p ⟨0,by decide⟩ 1, p ⟨0,by decide⟩ 4, p ⟨1,by decide⟩ 0, p ⟨1,by decide⟩ 1, p ⟨1,by decide⟩ 4, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 4, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f12]

private theorem cell96 {r : Register} (h : Frame r) (n_3_3 : Neg r 3 3) (n_4_2 : Neg r 4 2) (n_5_0 : Neg r 5 0) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, h.f9, h.f10, n_3_3 0, n_4_2 0, n_5_0 5, p ⟨0,by decide⟩ 4, p ⟨3,by decide⟩ 0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f11, h.f12]

private theorem cell97 {r : Register} (h : Frame r) (n_3_3 : Neg r 3 3) (n_4_2 : Neg r 4 2) (n_5_1 : Neg r 5 1) (n_8_0 : Neg r 8 0) : False := by
  lin_close [h.f0, h.f2, h.f3, h.f9, n_3_3 0, n_4_2 0, n_5_1 5, n_8_0 0, n_8_0 5, h.f1, h.f4, h.f5, h.f6, h.f7, h.f8, h.f10, h.f11, h.f12]

private theorem cell98 {r : Register} (h : Frame r) (n_3_3 : Neg r 3 3) (n_4_2 : Neg r 4 2) (n_5_1 : Neg r 5 1) (n_8_1 : Neg r 8 1) (p : Pos r 0) : False := by
  lin_close [h.f2, h.f9, h.f10, n_3_3 0, n_4_2 0, n_5_1 0, n_8_1 5, p ⟨1,by decide⟩ 1, p ⟨1,by decide⟩ 2, p ⟨1,by decide⟩ 3, p ⟨1,by decide⟩ 4, p ⟨1,by decide⟩ 5, p ⟨2,by decide⟩ 0, h.f0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f11, h.f12]

private theorem cell99 {r : Register} (h : Frame r) (n_3_3 : Neg r 3 3) (n_4_2 : Neg r 4 2) (n_8_3 : Neg r 8 3) : False := by
  lin_close [h.f2, h.f9, h.f10, n_3_3 0, n_4_2 0, n_8_3 0, h.f0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f11, h.f12]

private theorem cell100 {r : Register} (h : Frame r) (n_3_3 : Neg r 3 3) (n_4_2 : Neg r 4 2) (n_5_1 : Neg r 5 1) (n_8_4 : Neg r 8 4) : False := by
  lin_close [n_3_3 0, n_4_2 0, n_5_1 0, n_8_4 0, n_8_4 3, h.f0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f10, h.f11, h.f12]

private theorem cell101 {r : Register} (h : Frame r) (n_4_2 : Neg r 4 2) (n_8_5 : Neg r 8 5) : False := by
  lin_close [n_4_2 0, n_8_5 0, h.f0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f10, h.f11, h.f12]

private theorem cell102 {r : Register} (h : Frame r) (n_3_3 : Neg r 3 3) (n_4_2 : Neg r 4 2) (n_5_3 : Neg r 5 3) : False := by
  lin_close [h.f2, h.f9, h.f10, n_3_3 0, n_4_2 0, n_5_3 0, h.f0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f11, h.f12]

private theorem cell103 {r : Register} (h : Frame r) (n_4_3 : Neg r 4 3) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f8, h.f10, h.f11, n_4_3 0, p ⟨3,by decide⟩ 0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f12]

private theorem cell104 {r : Register} (h : Frame r) (n_2_3 : Neg r 2 3) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f8, h.f10, h.f11, n_2_3 0, p ⟨3,by decide⟩ 0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f12]

private theorem cell105 {r : Register} (h : Frame r) (n_1_0 : Neg r 1 0) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, h.f3, h.f8, h.f10, h.f11, n_1_0 0, n_1_0 3, n_1_0 4, p ⟨0,by decide⟩ 0, p ⟨0,by decide⟩ 1, p ⟨0,by decide⟩ 2, p ⟨0,by decide⟩ 3, p ⟨0,by decide⟩ 4, p ⟨1,by decide⟩ 0, p ⟨2,by decide⟩ 4, p ⟨3,by decide⟩ 0, p ⟨3,by decide⟩ 5, h.f1, h.f4, h.f5, h.f6, h.f7, h.f9, h.f12]

private theorem cell106 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_4_0 : Neg r 4 0) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f3, h.f8, h.f10, h.f11, n_1_1 0, n_1_1 7, n_1_1 8, n_4_0 0, p ⟨0,by decide⟩ 0, p ⟨1,by decide⟩ 0, p ⟨2,by decide⟩ 4, p ⟨3,by decide⟩ 4, p ⟨3,by decide⟩ 5, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f9, h.f12]

private theorem cell107 {r : Register} (h : Frame r) (n_4_1 : Neg r 4 1) (n_6_0 : Neg r 6 0) : False := by
  lin_close [h.f0, h.f3, h.f8, h.f10, n_4_1 0, n_6_0 0, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f9, h.f11, h.f12]

private theorem cell108 {r : Register} (h : Frame r) (n_4_1 : Neg r 4 1) (n_6_1 : Neg r 6 1) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f8, h.f10, h.f11, n_4_1 0, n_6_1 5, p ⟨0,by decide⟩ 0, p ⟨1,by decide⟩ 0, p ⟨1,by decide⟩ 4, p ⟨1,by decide⟩ 5, p ⟨2,by decide⟩ 0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f12]

private theorem cell109 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_6_2 : Neg r 6 2) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, h.f3, h.f8, h.f10, h.f11, n_1_1 0, n_6_2 5, p ⟨0,by decide⟩ 0, p ⟨1,by decide⟩ 0, p ⟨1,by decide⟩ 4, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 4, h.f1, h.f4, h.f5, h.f6, h.f7, h.f9, h.f12]

private theorem cell110 {r : Register} (h : Frame r) (n_4_1 : Neg r 4 1) (n_6_3 : Neg r 6 3) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f8, h.f10, n_4_1 0, n_6_3 0, p ⟨1,by decide⟩ 5, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f11, h.f12]

private theorem cell111 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_4_2 : Neg r 4 2) (n_6_0 : Neg r 6 0) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, h.f3, h.f8, h.f9, h.f10, h.f11, h.f12, n_1_1 7, n_4_2 0, n_6_0 0, p ⟨1,by decide⟩ 0, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 1, p ⟨2,by decide⟩ 2, p ⟨2,by decide⟩ 3, p ⟨2,by decide⟩ 4, h.f1, h.f4, h.f5, h.f6, h.f7]

private theorem cell112 {r : Register} (h : Frame r) (n_4_2 : Neg r 4 2) (n_6_1 : Neg r 6 1) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, h.f10, h.f11, n_4_2 0, n_6_1 5, n_6_1 6, p ⟨0,by decide⟩ 0, p ⟨1,by decide⟩ 0, p ⟨1,by decide⟩ 1, p ⟨1,by decide⟩ 2, p ⟨1,by decide⟩ 3, p ⟨1,by decide⟩ 4, p ⟨1,by decide⟩ 5, p ⟨2,by decide⟩ 0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f12]

private theorem cell113 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_4_2 : Neg r 4 2) (n_6_2 : Neg r 6 2) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, h.f3, h.f8, h.f10, h.f11, n_1_1 6, n_4_2 0, n_6_2 0, n_6_2 5, p ⟨0,by decide⟩ 0, p ⟨1,by decide⟩ 0, p ⟨1,by decide⟩ 1, p ⟨1,by decide⟩ 2, p ⟨1,by decide⟩ 3, p ⟨1,by decide⟩ 4, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 4, h.f1, h.f4, h.f5, h.f6, h.f7, h.f9, h.f12]

private theorem cell114 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_4_2 : Neg r 4 2) (n_6_3 : Neg r 6 3) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, h.f8, h.f10, h.f11, n_1_1 0, n_1_1 7, n_4_2 0, n_6_3 0, n_6_3 7, p ⟨1,by decide⟩ 1, p ⟨1,by decide⟩ 5, p ⟨2,by decide⟩ 0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f12]

private theorem cell115 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_4_3 : Neg r 4 3) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, h.f8, h.f9, h.f10, h.f11, h.f12, n_1_1 0, n_4_3 0, p ⟨0,by decide⟩ 0, p ⟨1,by decide⟩ 0, p ⟨1,by decide⟩ 1, p ⟨1,by decide⟩ 2, p ⟨1,by decide⟩ 3, p ⟨1,by decide⟩ 4, p ⟨1,by decide⟩ 5, p ⟨2,by decide⟩ 0, p ⟨3,by decide⟩ 5, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7]

private theorem cell116 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f8, h.f10, h.f11, n_1_2 0, p ⟨2,by decide⟩ 0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f12]

private theorem cell117 {r : Register} (h : Frame r) (n_3_0 : Neg r 3 0) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f10, n_3_0 0, p ⟨0,by decide⟩ 0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f11, h.f12]

private theorem cell118 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_2_0 : Neg r 2 0) (n_3_1 : Neg r 3 1) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f3, h.f8, h.f11, n_1_3 0, n_2_0 6, n_3_1 0, p ⟨2,by decide⟩ 0, p ⟨3,by decide⟩ 0, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f9, h.f10, h.f12]

private theorem cell119 {r : Register} (h : Frame r) (n_2_1 : Neg r 2 1) (n_3_1 : Neg r 3 1) (n_4_0 : Neg r 4 0) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f3, n_2_1 6, n_3_1 0, n_4_0 0, p ⟨3,by decide⟩ 5, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f10, h.f11, h.f12]

private theorem cell120 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_3_1 : Neg r 3 1) (n_4_1 : Neg r 4 1) (n_6_1 : Neg r 6 1) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f10, n_1_3 0, n_3_1 0, n_4_1 0, n_6_1 5, p ⟨1,by decide⟩ 0, p ⟨1,by decide⟩ 1, p ⟨1,by decide⟩ 2, p ⟨1,by decide⟩ 3, p ⟨1,by decide⟩ 4, p ⟨1,by decide⟩ 5, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f11, h.f12]

private theorem cell121 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_3_1 : Neg r 3 1) (n_4_1 : Neg r 4 1) (n_6_2 : Neg r 6 2) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, h.f8, h.f10, n_1_3 0, n_3_1 0, n_4_1 0, n_6_2 0, n_6_2 5, p ⟨1,by decide⟩ 0, p ⟨1,by decide⟩ 1, p ⟨1,by decide⟩ 2, p ⟨1,by decide⟩ 3, p ⟨1,by decide⟩ 4, p ⟨2,by decide⟩ 4, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f11, h.f12]

private theorem cell122 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_2_1 : Neg r 2 1) (n_3_1 : Neg r 3 1) (n_4_2 : Neg r 4 2) (n_6_0 : Neg r 6 0) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, h.f3, h.f8, h.f9, h.f10, h.f11, h.f12, n_1_3 0, n_2_1 0, n_2_1 5, n_3_1 0, n_4_2 0, n_6_0 0, p ⟨1,by decide⟩ 0, p ⟨2,by decide⟩ 2, p ⟨2,by decide⟩ 3, p ⟨2,by decide⟩ 4, h.f1, h.f4, h.f5, h.f6, h.f7]

private theorem cell123 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_3_1 : Neg r 3 1) (n_4_2 : Neg r 4 2) (n_6_1 : Neg r 6 1) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, h.f10, n_1_3 0, n_3_1 0, n_4_2 0, n_6_1 5, n_6_1 6, p ⟨1,by decide⟩ 0, p ⟨1,by decide⟩ 1, p ⟨1,by decide⟩ 2, p ⟨1,by decide⟩ 3, p ⟨1,by decide⟩ 4, p ⟨1,by decide⟩ 5, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f11, h.f12]

private theorem cell124 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_2_1 : Neg r 2 1) (n_3_1 : Neg r 3 1) (n_4_2 : Neg r 4 2) (n_6_2 : Neg r 6 2) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, h.f3, h.f8, h.f9, h.f10, n_1_3 0, n_2_1 5, n_3_1 0, n_4_2 0, n_6_2 5, p ⟨1,by decide⟩ 0, p ⟨1,by decide⟩ 1, p ⟨1,by decide⟩ 2, p ⟨1,by decide⟩ 3, p ⟨1,by decide⟩ 4, p ⟨2,by decide⟩ 4, h.f1, h.f4, h.f5, h.f6, h.f7, h.f11, h.f12]

private theorem cell125 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_2_1 : Neg r 2 1) (n_4_2 : Neg r 4 2) (n_6_3 : Neg r 6 3) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, h.f8, h.f9, h.f10, n_1_3 0, n_2_1 5, n_4_2 0, n_6_3 0, n_6_3 7, p ⟨1,by decide⟩ 5, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f11, h.f12]

private theorem cell126 {r : Register} (h : Frame r) (n_3_1 : Neg r 3 1) (n_4_3 : Neg r 4 3) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f3, n_3_1 0, n_4_3 0, p ⟨3,by decide⟩ 5, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f10, h.f11, h.f12]

private theorem cell127 {r : Register} (h : Frame r) (n_3_1 : Neg r 3 1) (n_4_0 : Neg r 4 0) (n_7_0 : Neg r 7 0) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f3, h.f10, n_3_1 0, n_4_0 0, n_7_0 5, p ⟨1,by decide⟩ 0, p ⟨2,by decide⟩ 4, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f11, h.f12]

private theorem cell128 {r : Register} (h : Frame r) (n_2_2 : Neg r 2 2) (n_3_1 : Neg r 3 1) (n_4_0 : Neg r 4 0) (n_6_0 : Neg r 6 0) (n_7_1 : Neg r 7 1) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f3, h.f10, n_2_2 5, n_3_1 0, n_4_0 0, n_6_0 5, n_7_1 0, n_7_1 7, p ⟨1,by decide⟩ 0, p ⟨2,by decide⟩ 4, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f11, h.f12]

private theorem cell129 {r : Register} (h : Frame r) (n_4_0 : Neg r 4 0) (n_6_1 : Neg r 6 1) : False := by
  lin_close [h.f0, h.f3, h.f10, n_4_0 0, n_6_1 0, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f11, h.f12]

private theorem cell130 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_2_2 : Neg r 2 2) (n_4_0 : Neg r 4 0) (n_6_2 : Neg r 6 2) (n_7_1 : Neg r 7 1) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, h.f3, h.f10, n_1_3 0, n_1_3 6, n_2_2 0, n_4_0 0, n_6_2 0, n_6_2 5, n_6_2 6, n_7_1 5, p ⟨2,by decide⟩ 4, h.f1, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f11, h.f12]

private theorem cell131 {r : Register} (h : Frame r) (n_2_2 : Neg r 2 2) (n_6_3 : Neg r 6 3) (n_7_1 : Neg r 7 1) (n_8_0 : Neg r 8 0) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f10, h.f11, n_2_2 0, n_6_3 0, n_7_1 0, n_8_0 0, p ⟨0,by decide⟩ 0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f12]

private theorem cell132 {r : Register} (h : Frame r) (n_2_2 : Neg r 2 2) (n_3_1 : Neg r 3 1) (n_4_0 : Neg r 4 0) (n_8_1 : Neg r 8 1) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f3, h.f8, h.f9, h.f10, h.f11, h.f12, n_2_2 5, n_3_1 0, n_4_0 0, n_8_1 0, n_8_1 6, p ⟨0,by decide⟩ 0, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7]

private theorem cell133 {r : Register} (h : Frame r) (n_2_2 : Neg r 2 2) (n_3_1 : Neg r 3 1) (n_8_3 : Neg r 8 3) : False := by
  lin_close [h.f2, h.f3, n_2_2 5, n_3_1 0, n_8_3 0, h.f0, h.f1, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f10, h.f11, h.f12]

private theorem cell134 {r : Register} (h : Frame r) (n_3_1 : Neg r 3 1) (n_8_4 : Neg r 8 4) (p : Pos r 9) : False := by
  lin_close [h.f0, n_3_1 0, n_8_4 3, p ⟨0,by decide⟩ 0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f10, h.f11, h.f12]

private theorem cell135 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_4_0 : Neg r 4 0) (n_7_2 : Neg r 7 2) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f10, n_1_3 0, n_4_0 0, n_7_2 0, p ⟨2,by decide⟩ 4, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f11, h.f12]

private theorem cell136 {r : Register} (h : Frame r) (n_5_0 : Neg r 5 0) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f10, n_5_0 0, p ⟨0,by decide⟩ 0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f11, h.f12]

private theorem cell137 {r : Register} (h : Frame r) (n_2_2 : Neg r 2 2) (n_3_1 : Neg r 3 1) (n_5_1 : Neg r 5 1) (n_7_3 : Neg r 7 3) (n_8_0 : Neg r 8 0) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f3, n_2_2 5, n_3_1 0, n_5_1 0, n_5_1 6, n_7_3 0, n_8_0 0, n_8_0 5, p ⟨0,by decide⟩ 0, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f10, h.f11, h.f12]

private theorem cell138 {r : Register} (h : Frame r) (n_2_2 : Neg r 2 2) (n_3_1 : Neg r 3 1) (n_5_3 : Neg r 5 3) (n_7_3 : Neg r 7 3) (n_8_0 : Neg r 8 0) : False := by
  lin_close [h.f0, h.f2, h.f3, h.f9, n_2_2 5, n_3_1 0, n_5_3 0, n_5_3 6, n_5_3 7, n_7_3 0, n_8_0 4, h.f1, h.f4, h.f5, h.f6, h.f7, h.f8, h.f10, h.f11, h.f12]

private theorem cell139 {r : Register} (h : Frame r) (n_3_1 : Neg r 3 1) (n_7_4 : Neg r 7 4) (p : Pos r 9) : False := by
  lin_close [h.f0, n_3_1 0, n_7_4 3, p ⟨0,by decide⟩ 0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f10, h.f11, h.f12]

private theorem cell140 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_4_2 : Neg r 4 2) (n_6_0 : Neg r 6 0) (n_7_1 : Neg r 7 1) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, h.f3, h.f9, h.f10, h.f11, h.f12, n_1_3 0, n_4_2 0, n_6_0 0, n_6_0 5, n_7_1 0, n_7_1 6, p ⟨1,by decide⟩ 0, p ⟨2,by decide⟩ 2, p ⟨2,by decide⟩ 3, p ⟨2,by decide⟩ 4, h.f1, h.f4, h.f5, h.f6, h.f7, h.f8]

private theorem cell141 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_3_1 : Neg r 3 1) (n_4_2 : Neg r 4 2) (n_6_0 : Neg r 6 0) (n_7_2 : Neg r 7 2) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, h.f3, h.f9, h.f10, h.f11, h.f12, n_1_3 0, n_3_1 0, n_4_2 0, n_6_0 0, n_7_2 0, p ⟨1,by decide⟩ 0, p ⟨2,by decide⟩ 2, p ⟨2,by decide⟩ 3, p ⟨2,by decide⟩ 4, h.f1, h.f4, h.f5, h.f6, h.f7, h.f8]

private theorem cell142 {r : Register} (h : Frame r) (n_3_1 : Neg r 3 1) (n_4_2 : Neg r 4 2) (n_7_4 : Neg r 7 4) (p : Pos r 9) : False := by
  lin_close [n_3_1 0, n_4_2 0, n_7_4 0, n_7_4 3, p ⟨0,by decide⟩ 0, h.f0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f10, h.f11, h.f12]

private theorem cell143 {r : Register} (h : Frame r) (n_4_2 : Neg r 4 2) (n_6_0 : Neg r 6 0) (n_7_6 : Neg r 7 6) (p : Pos r 9) : False := by
  lin_close [h.f8, h.f10, n_4_2 0, n_6_0 5, n_7_6 0, n_7_6 2, p ⟨1,by decide⟩ 0, h.f0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f11, h.f12]

private theorem cell144 {r : Register} (h : Frame r) (n_4_2 : Neg r 4 2) (n_6_0 : Neg r 6 0) (n_7_7 : Neg r 7 7) : False := by
  lin_close [h.f0, n_4_2 0, n_6_0 0, n_7_7 0, n_7_7 2, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f10, h.f11, h.f12]

private theorem cell145 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_3_1 : Neg r 3 1) (n_4_2 : Neg r 4 2) (n_6_1 : Neg r 6 1) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, h.f10, n_1_3 0, n_3_1 0, n_4_2 0, n_6_1 5, n_6_1 6, p ⟨1,by decide⟩ 0, p ⟨1,by decide⟩ 4, p ⟨1,by decide⟩ 5, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f11, h.f12]

private theorem cell146 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_3_1 : Neg r 3 1) (n_6_2 : Neg r 6 2) (n_7_1 : Neg r 7 1) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, h.f3, h.f8, h.f10, n_1_3 0, n_1_3 6, n_3_1 0, n_6_2 0, n_6_2 5, n_6_2 6, n_7_1 0, n_7_1 5, p ⟨1,by decide⟩ 0, p ⟨1,by decide⟩ 4, p ⟨2,by decide⟩ 4, h.f1, h.f4, h.f5, h.f6, h.f7, h.f9, h.f11, h.f12]

private theorem cell147 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_3_1 : Neg r 3 1) (n_7_2 : Neg r 7 2) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, h.f10, n_1_3 0, n_3_1 0, n_7_2 0, p ⟨1,by decide⟩ 0, p ⟨1,by decide⟩ 4, p ⟨2,by decide⟩ 4, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f11, h.f12]

private theorem cell148 {r : Register} (h : Frame r) (n_4_2 : Neg r 4 2) (n_6_3 : Neg r 6 3) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, h.f8, h.f10, n_4_2 0, n_6_3 7, p ⟨1,by decide⟩ 0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f11, h.f12]

private theorem cell149 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_3_1 : Neg r 3 1) (n_4_2 : Neg r 4 2) (n_7_0 : Neg r 7 0) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, h.f3, h.f9, h.f10, h.f11, h.f12, n_1_3 0, n_3_1 0, n_4_2 0, n_7_0 0, n_7_0 5, p ⟨1,by decide⟩ 0, p ⟨2,by decide⟩ 2, p ⟨2,by decide⟩ 3, p ⟨2,by decide⟩ 4, h.f1, h.f4, h.f5, h.f6, h.f7, h.f8]

private theorem cell150 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_3_1 : Neg r 3 1) (n_6_2 : Neg r 6 2) (n_7_1 : Neg r 7 1) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, h.f3, h.f8, h.f10, n_1_3 0, n_1_3 6, n_3_1 0, n_6_2 0, n_6_2 5, n_6_2 6, n_7_1 5, p ⟨1,by decide⟩ 0, p ⟨1,by decide⟩ 4, p ⟨2,by decide⟩ 4, h.f1, h.f4, h.f5, h.f6, h.f7, h.f9, h.f11, h.f12]

private theorem cell151 {r : Register} (h : Frame r) (n_5_2 : Neg r 5 2) (n_6_3 : Neg r 6 3) (n_7_1 : Neg r 7 1) : False := by
  lin_close [h.f0, h.f2, h.f3, h.f8, h.f9, h.f10, h.f11, n_5_2 2, n_6_3 0, n_7_1 0, h.f1, h.f4, h.f5, h.f6, h.f7, h.f12]

private theorem cell152 {r : Register} (h : Frame r) (n_4_2 : Neg r 4 2) (n_5_2 : Neg r 5 2) (n_7_6 : Neg r 7 6) : False := by
  lin_close [h.f3, h.f8, h.f9, h.f10, h.f11, n_4_2 0, n_5_2 2, n_7_6 0, n_7_6 2, h.f0, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f12]

private theorem cell153 {r : Register} (h : Frame r) (n_2_2 : Neg r 2 2) (n_4_3 : Neg r 4 3) : False := by
  lin_close [h.f0, h.f2, h.f8, h.f10, h.f11, n_2_2 0, n_4_3 0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f12]

private theorem cell154 {r : Register} (h : Frame r) (n_2_3 : Neg r 2 3) (n_3_1 : Neg r 3 1) (n_4_0 : Neg r 4 0) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f3, h.f10, h.site2, n_2_3 6, n_2_3 7, n_3_1 0, n_4_0 0, p ⟨0,by decide⟩ 0, p ⟨1,by decide⟩ 0, p ⟨3,by decide⟩ 5, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f11, h.f12]

private theorem cell155 {r : Register} (h : Frame r) (n_2_3 : Neg r 2 3) (n_3_1 : Neg r 3 1) (n_4_1 : Neg r 4 1) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f10, n_2_3 0, n_3_1 0, n_4_1 0, p ⟨1,by decide⟩ 0, p ⟨1,by decide⟩ 1, p ⟨1,by decide⟩ 2, p ⟨1,by decide⟩ 3, p ⟨1,by decide⟩ 4, p ⟨1,by decide⟩ 5, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f11, h.f12]

private theorem cell156 {r : Register} (h : Frame r) (n_2_3 : Neg r 2 3) (n_4_2 : Neg r 4 2) : False := by
  lin_close [h.f0, h.f2, h.f10, h.f11, n_2_3 0, n_4_2 0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f12]

private theorem cell157 {r : Register} (h : Frame r) (n_3_2 : Neg r 3 2) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f8, h.f10, h.f11, n_3_2 0, p ⟨2,by decide⟩ 0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f12]

private theorem cell158 {r : Register} (h : Frame r) (n_2_0 : Neg r 2 0) (n_5_1 : Neg r 5 1) : False := by
  lin_close [h.f0, h.f2, h.f3, h.f8, n_2_0 0, n_2_0 5, n_5_1 0, n_5_1 6, h.f1, h.f4, h.f5, h.f6, h.f7, h.f9, h.f10, h.f11, h.f12]

private theorem cell159 {r : Register} (h : Frame r) (n_2_1 : Neg r 2 1) (n_3_3 : Neg r 3 3) (n_4_0 : Neg r 4 0) (n_5_1 : Neg r 5 1) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f3, h.f10, h.f11, n_2_1 0, n_2_1 6, n_3_3 0, n_4_0 0, n_5_1 0, p ⟨0,by decide⟩ 0, p ⟨3,by decide⟩ 3, p ⟨3,by decide⟩ 4, p ⟨3,by decide⟩ 5, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f12]

private theorem cell160 {r : Register} (h : Frame r) (n_2_2 : Neg r 2 2) (n_3_3 : Neg r 3 3) (n_5_1 : Neg r 5 1) (n_8_0 : Neg r 8 0) : False := by
  lin_close [h.f0, h.f2, h.f3, n_2_2 0, n_3_3 0, n_5_1 6, n_8_0 0, n_8_0 5, h.f1, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f10, h.f11, h.f12]

private theorem cell161 {r : Register} (h : Frame r) (n_2_2 : Neg r 2 2) (n_4_0 : Neg r 4 0) (n_8_1 : Neg r 8 1) : False := by
  lin_close [h.f0, h.f3, n_2_2 0, n_4_0 0, n_8_1 0, n_8_1 6, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f10, h.f11, h.f12]

private theorem cell162 {r : Register} (h : Frame r) (n_2_2 : Neg r 2 2) (n_5_1 : Neg r 5 1) (n_8_3 : Neg r 8 3) : False := by
  lin_close [h.f0, h.f2, h.f3, h.f8, n_2_2 0, n_2_2 5, n_5_1 6, n_8_3 0, h.f1, h.f4, h.f5, h.f6, h.f7, h.f9, h.f10, h.f11, h.f12]

private theorem cell163 {r : Register} (h : Frame r) (n_3_3 : Neg r 3 3) (n_5_1 : Neg r 5 1) (n_8_4 : Neg r 8 4) (p : Pos r 9) : False := by
  lin_close [h.f0, n_3_3 0, n_5_1 0, n_8_4 1, n_8_4 3, p ⟨0,by decide⟩ 0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f10, h.f11, h.f12]

private theorem cell164 {r : Register} (h : Frame r) (n_4_0 : Neg r 4 0) (n_8_6 : Neg r 8 6) : False := by
  lin_close [h.f2, h.f9, n_4_0 0, n_8_6 2, h.f0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f10, h.f11, h.f12]

private theorem cell165 {r : Register} (h : Frame r) (n_2_3 : Neg r 2 3) (n_3_3 : Neg r 3 3) (n_4_0 : Neg r 4 0) (n_5_1 : Neg r 5 1) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f8, h.f10, h.f11, h.site2, n_2_3 6, n_2_3 7, n_3_3 0, n_4_0 0, n_5_1 0, p ⟨0,by decide⟩ 0, p ⟨1,by decide⟩ 0, p ⟨3,by decide⟩ 5, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f12]

private theorem cell166 {r : Register} (h : Frame r) (n_3_3 : Neg r 3 3) (n_5_2 : Neg r 5 2) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, h.f10, n_3_3 0, n_5_2 5, p ⟨0,by decide⟩ 0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f11, h.f12]

private theorem cell167 {r : Register} (h : Frame r) (n_2_0 : Neg r 2 0) (n_5_3 : Neg r 5 3) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, h.f3, h.f8, h.f10, n_2_0 0, n_2_0 4, n_2_0 5, n_5_3 0, n_5_3 7, p ⟨0,by decide⟩ 0, p ⟨0,by decide⟩ 1, p ⟨0,by decide⟩ 2, p ⟨0,by decide⟩ 3, p ⟨0,by decide⟩ 4, p ⟨1,by decide⟩ 0, p ⟨3,by decide⟩ 0, h.f1, h.f4, h.f5, h.f6, h.f7, h.f9, h.f11, h.f12]

private theorem cell168 {r : Register} (h : Frame r) (n_2_1 : Neg r 2 1) (n_3_3 : Neg r 3 3) (n_4_0 : Neg r 4 0) (n_5_3 : Neg r 5 3) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f3, h.f10, h.f11, n_2_1 0, n_2_1 6, n_3_3 0, n_4_0 0, n_5_3 0, p ⟨0,by decide⟩ 0, p ⟨3,by decide⟩ 1, p ⟨3,by decide⟩ 2, p ⟨3,by decide⟩ 3, p ⟨3,by decide⟩ 4, p ⟨3,by decide⟩ 5, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f12]

private theorem cell169 {r : Register} (h : Frame r) (n_2_2 : Neg r 2 2) (n_5_3 : Neg r 5 3) (n_8_0 : Neg r 8 0) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, h.f8, h.f10, h.f11, n_2_2 0, n_2_2 5, n_2_2 6, n_5_3 0, n_5_3 6, n_5_3 7, n_8_0 0, p ⟨0,by decide⟩ 0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f12]

private theorem cell170 {r : Register} (h : Frame r) (n_2_2 : Neg r 2 2) (n_3_3 : Neg r 3 3) (n_4_0 : Neg r 4 0) (n_8_1 : Neg r 8 1) : False := by
  lin_close [h.f0, h.f3, h.f10, h.f11, n_2_2 0, n_2_2 5, n_3_3 0, n_4_0 0, n_8_1 0, n_8_1 6, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f12]

private theorem cell171 {r : Register} (h : Frame r) (n_2_2 : Neg r 2 2) (n_8_3 : Neg r 8 3) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, h.f8, h.f10, h.f11, n_2_2 6, n_8_3 0, p ⟨0,by decide⟩ 0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f12]

private theorem cell172 {r : Register} (h : Frame r) (n_2_3 : Neg r 2 3) (n_4_0 : Neg r 4 0) (n_5_3 : Neg r 5 3) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, h.f8, h.f10, h.f11, h.site2, n_2_3 6, n_2_3 7, n_4_0 0, n_5_3 0, p ⟨0,by decide⟩ 0, p ⟨0,by decide⟩ 1, p ⟨0,by decide⟩ 2, p ⟨0,by decide⟩ 3, p ⟨1,by decide⟩ 0, p ⟨3,by decide⟩ 0, p ⟨3,by decide⟩ 5, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f12]

private theorem cell173 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_3_3 : Neg r 3 3) (n_4_1 : Neg r 4 1) (p : Pos r 9) : False := by
  lin_close [h.f9, h.f10, h.f12, n_1_3 0, n_3_3 0, n_4_1 0, p ⟨1,by decide⟩ 5, h.f0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f11]

private theorem cell174 {r : Register} (h : Frame r) (n_3_3 : Neg r 3 3) (n_4_2 : Neg r 4 2) (n_5_1 : Neg r 5 1) (n_7_0 : Neg r 7 0) : False := by
  lin_close [h.f0, h.f3, n_3_3 0, n_4_2 0, n_5_1 0, n_5_1 5, n_7_0 0, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f10, h.f11, h.f12]

private theorem cell175 {r : Register} (h : Frame r) (n_3_3 : Neg r 3 3) (n_4_2 : Neg r 4 2) (n_6_0 : Neg r 6 0) (n_7_1 : Neg r 7 1) : False := by
  lin_close [h.f0, h.f2, h.f3, h.f9, n_3_3 0, n_4_2 0, n_6_0 4, n_7_1 0, n_7_1 6, h.f1, h.f4, h.f5, h.f6, h.f7, h.f8, h.f10, h.f11, h.f12]

private theorem cell176 {r : Register} (h : Frame r) (n_3_3 : Neg r 3 3) (n_4_2 : Neg r 4 2) (n_7_2 : Neg r 7 2) : False := by
  lin_close [h.f2, h.f9, h.f10, n_3_3 0, n_4_2 0, n_7_2 0, h.f0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f11, h.f12]

private theorem cell177 {r : Register} (h : Frame r) (n_3_3 : Neg r 3 3) (n_4_2 : Neg r 4 2) (n_5_1 : Neg r 5 1) (n_7_4 : Neg r 7 4) : False := by
  lin_close [n_3_3 0, n_4_2 0, n_5_1 0, n_7_4 0, n_7_4 3, h.f0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f10, h.f11, h.f12]

private theorem cell178 {r : Register} (h : Frame r) (n_3_3 : Neg r 3 3) (n_7_6 : Neg r 7 6) : False := by
  lin_close [h.f2, h.f9, n_3_3 0, n_7_6 1, h.f0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f10, h.f11, h.f12]

private theorem cell179 {r : Register} (h : Frame r) (n_3_3 : Neg r 3 3) (n_4_2 : Neg r 4 2) (n_6_0 : Neg r 6 0) (n_7_7 : Neg r 7 7) : False := by
  lin_close [h.f9, n_3_3 0, n_4_2 0, n_6_0 0, n_7_7 0, n_7_7 2, h.f0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f10, h.f11, h.f12]

private theorem cell180 {r : Register} (h : Frame r) (n_3_3 : Neg r 3 3) (n_4_2 : Neg r 4 2) (n_6_1 : Neg r 6 1) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, h.f9, h.f10, n_3_3 0, n_4_2 0, n_6_1 6, p ⟨1,by decide⟩ 5, p ⟨2,by decide⟩ 0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f11, h.f12]

private theorem cell181 {r : Register} (h : Frame r) (n_3_3 : Neg r 3 3) (n_4_2 : Neg r 4 2) (n_6_2 : Neg r 6 2) : False := by
  lin_close [h.f2, h.f9, h.f10, n_3_3 0, n_4_2 0, n_6_2 0, h.f0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f11, h.f12]

private theorem cell182 {r : Register} (h : Frame r) (n_3_3 : Neg r 3 3) (n_4_3 : Neg r 4 3) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, h.f10, h.f11, n_3_3 0, n_4_3 0, p ⟨0,by decide⟩ 0, p ⟨0,by decide⟩ 1, p ⟨0,by decide⟩ 2, p ⟨0,by decide⟩ 3, p ⟨1,by decide⟩ 0, p ⟨3,by decide⟩ 0, p ⟨3,by decide⟩ 5, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f12]

private theorem cell183 {r : Register} (h : Frame r) (n_0_0 : Neg r 0 0) (p : Pos r 1) : False := by
  lin_close [h.f0, h.f10, n_0_0 0, p ⟨0,by decide⟩ 0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f11, h.f12]

private theorem cell184 {r : Register} (h : Frame r) (n_0_1 : Neg r 0 1) (p : Pos r 1) : False := by
  lin_close [h.f0, h.f8, h.f10, h.f11, n_0_1 0, n_0_1 5, n_0_1 6, p ⟨0,by decide⟩ 0, p ⟨1,by decide⟩ 0, p ⟨1,by decide⟩ 2, p ⟨1,by decide⟩ 3, p ⟨1,by decide⟩ 4, p ⟨1,by decide⟩ 5, p ⟨2,by decide⟩ 0, p ⟨3,by decide⟩ 5, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f12]

private theorem cell185 {r : Register} (h : Frame r) (n_0_2 : Neg r 0 2) (p : Pos r 1) : False := by
  lin_close [h.f0, h.f2, h.f8, h.f10, h.f11, n_0_2 5, p ⟨0,by decide⟩ 0, p ⟨1,by decide⟩ 0, p ⟨1,by decide⟩ 4, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 4, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f12]

private theorem cell186 {r : Register} (h : Frame r) (n_0_3 : Neg r 0 3) (p : Pos r 1) : False := by
  lin_close [h.f0, h.f10, n_0_3 0, p ⟨3,by decide⟩ 0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f11, h.f12]

private theorem cell187 {r : Register} (h : Frame r) (n_9_0 : Neg r 9 0) (p : Pos r 2) : False := by
  lin_close [h.f0, h.f8, h.f10, h.f11, n_9_0 0, n_9_0 4, n_9_0 5, p ⟨0,by decide⟩ 0, p ⟨0,by decide⟩ 1, p ⟨0,by decide⟩ 2, p ⟨0,by decide⟩ 3, p ⟨0,by decide⟩ 4, p ⟨1,by decide⟩ 0, p ⟨2,by decide⟩ 4, p ⟨3,by decide⟩ 0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f12]

private theorem cell188 {r : Register} (h : Frame r) (n_9_1 : Neg r 9 1) (p : Pos r 2) : False := by
  lin_close [h.f0, h.f10, n_9_1 0, p ⟨1,by decide⟩ 0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f11, h.f12]

private theorem cell189 {r : Register} (h : Frame r) (n_9_2 : Neg r 9 2) (p : Pos r 2) : False := by
  lin_close [h.f0, h.f10, n_9_2 0, p ⟨2,by decide⟩ 0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f11, h.f12]

private theorem cell190 {r : Register} (h : Frame r) (n_9_3 : Neg r 9 3) (p : Pos r 2) : False := by
  lin_close [h.f0, h.f2, h.f8, h.f10, h.f11, n_9_3 6, p ⟨0,by decide⟩ 0, p ⟨0,by decide⟩ 1, p ⟨0,by decide⟩ 2, p ⟨0,by decide⟩ 3, p ⟨1,by decide⟩ 0, p ⟨3,by decide⟩ 0, p ⟨3,by decide⟩ 5, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f12]

private theorem cell191 {r : Register} (h : Frame r) (n_0_0 : Neg r 0 0) (p : Pos r 3) : False := by
  lin_close [h.f0, n_0_0 5, p ⟨0,by decide⟩ 0, p ⟨2,by decide⟩ 0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f10, h.f11, h.f12]

private theorem cell192 {r : Register} (h : Frame r) (n_0_1 : Neg r 0 1) (p : Pos r 3) : False := by
  lin_close [h.f2, h.f8, h.f10, h.f11, n_0_1 0, p ⟨0,by decide⟩ 0, p ⟨1,by decide⟩ 0, h.f0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f12]

private theorem cell193 {r : Register} (h : Frame r) (n_0_2 : Neg r 0 2) (p : Pos r 3) : False := by
  lin_close [h.f2, h.f8, h.f10, h.f11, h.site0, n_0_2 5, n_0_2 6, p ⟨0,by decide⟩ 0, p ⟨1,by decide⟩ 0, p ⟨2,by decide⟩ 0, p ⟨3,by decide⟩ 0, h.f0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f12]

private theorem cell194 {r : Register} (h : Frame r) (n_0_3 : Neg r 0 3) (p : Pos r 3) : False := by
  lin_close [h.f0, h.f8, h.f10, n_0_3 0, p ⟨3,by decide⟩ 0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f11, h.f12]

private theorem cell195 {r : Register} (h : Frame r) (n_9_0 : Neg r 9 0) (p : Pos r 4) : False := by
  lin_close [h.f2, h.f8, h.f10, h.f11, n_9_0 0, p ⟨0,by decide⟩ 0, p ⟨1,by decide⟩ 0, h.f0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f12]

private theorem cell196 {r : Register} (h : Frame r) (n_9_1 : Neg r 9 1) (p : Pos r 4) : False := by
  lin_close [h.f0, n_9_1 6, p ⟨1,by decide⟩ 0, p ⟨3,by decide⟩ 0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f10, h.f11, h.f12]

private theorem cell197 {r : Register} (h : Frame r) (n_9_2 : Neg r 9 2) (p : Pos r 4) : False := by
  lin_close [h.f0, h.f8, h.f10, n_9_2 0, p ⟨2,by decide⟩ 0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f11, h.f12]

private theorem cell198 {r : Register} (h : Frame r) (n_9_3 : Neg r 9 3) (p : Pos r 4) : False := by
  lin_close [h.f2, h.f8, h.f10, h.f11, h.site3, n_9_3 6, n_9_3 7, p ⟨0,by decide⟩ 0, p ⟨1,by decide⟩ 0, p ⟨2,by decide⟩ 0, p ⟨3,by decide⟩ 0, h.f0, h.f1, h.f3, h.f4, h.f5, h.f6, h.f7, h.f9, h.f12]

private theorem cell199 {r : Register} (h : Frame r) (n_0_0 : Neg r 0 0) (p : Pos r 5) : False := by
  lin_close [h.f0, h.f2, h.f3, h.f8, h.f9, h.f10, h.f11, h.f12, n_0_0 0, n_0_0 4, n_0_0 5, p ⟨0,by decide⟩ 3, p ⟨0,by decide⟩ 4, p ⟨1,by decide⟩ 0, p ⟨2,by decide⟩ 4, p ⟨3,by decide⟩ 0, p ⟨3,by decide⟩ 5, h.f1, h.f4, h.f5, h.f6, h.f7]

private theorem cell200 {r : Register} (h : Frame r) (n_0_1 : Neg r 0 1) (p : Pos r 5) : False := by
  lin_close [h.f0, h.f10, h.f11, n_0_1 0, p ⟨1,by decide⟩ 0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f12]

private theorem cell201 {r : Register} (h : Frame r) (n_0_2 : Neg r 0 2) (p : Pos r 5) : False := by
  lin_close [h.f0, h.f10, h.f11, n_0_2 0, p ⟨2,by decide⟩ 0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f12]

private theorem cell202 {r : Register} (h : Frame r) (n_0_3 : Neg r 0 3) (p : Pos r 5) : False := by
  lin_close [h.f0, h.f2, h.f3, h.f8, h.f10, h.f11, n_0_3 6, p ⟨0,by decide⟩ 3, p ⟨1,by decide⟩ 0, p ⟨3,by decide⟩ 0, p ⟨3,by decide⟩ 5, h.f1, h.f4, h.f5, h.f6, h.f7, h.f9, h.f12]

private theorem cell203 {r : Register} (h : Frame r) (n_9_0 : Neg r 9 0) (p : Pos r 6) : False := by
  lin_close [h.f0, h.f10, h.f11, n_9_0 0, p ⟨0,by decide⟩ 0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f12]

private theorem cell204 {r : Register} (h : Frame r) (n_9_1 : Neg r 9 1) (p : Pos r 6) : False := by
  lin_close [h.f0, h.f2, h.f3, h.f8, h.f9, h.f10, h.f11, h.f12, n_9_1 0, n_9_1 5, n_9_1 6, p ⟨0,by decide⟩ 0, p ⟨1,by decide⟩ 4, p ⟨1,by decide⟩ 5, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 4, p ⟨3,by decide⟩ 5, h.f1, h.f4, h.f5, h.f6, h.f7]

private theorem cell205 {r : Register} (h : Frame r) (n_9_2 : Neg r 9 2) (p : Pos r 6) : False := by
  lin_close [h.f0, h.f2, h.f3, h.f8, h.f10, h.f11, n_9_2 5, p ⟨0,by decide⟩ 0, p ⟨1,by decide⟩ 4, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 4, h.f1, h.f4, h.f5, h.f6, h.f7, h.f9, h.f12]

private theorem cell206 {r : Register} (h : Frame r) (n_9_3 : Neg r 9 3) (p : Pos r 6) : False := by
  lin_close [h.f0, h.f10, h.f11, n_9_3 0, p ⟨3,by decide⟩ 0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f12]

private theorem cell207 {r : Register} (h : Frame r) (n_0_0 : Neg r 0 0) (p : Pos r 7) : False := by
  lin_close [h.f0, h.f10, n_0_0 0, p ⟨0,by decide⟩ 0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f11, h.f12]

private theorem cell208 {r : Register} (h : Frame r) (n_0_1 : Neg r 0 1) (p : Pos r 7) : False := by
  lin_close [h.f0, h.f3, h.f8, h.f10, n_0_1 0, p ⟨1,by decide⟩ 3, p ⟨2,by decide⟩ 0, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f9, h.f11, h.f12]

private theorem cell209 {r : Register} (h : Frame r) (n_0_2 : Neg r 0 2) (p : Pos r 7) : False := by
  lin_close [h.f0, h.f3, h.f10, h.f11, n_0_2 0, p ⟨2,by decide⟩ 0, p ⟨3,by decide⟩ 0, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f12]

private theorem cell210 {r : Register} (h : Frame r) (n_0_3 : Neg r 0 3) (p : Pos r 7) : False := by
  lin_close [h.f0, h.f9, h.f10, n_0_3 0, p ⟨3,by decide⟩ 0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f11, h.f12]

private theorem cell211 {r : Register} (h : Frame r) (n_9_0 : Neg r 9 0) (p : Pos r 8) : False := by
  lin_close [h.f0, h.f3, h.f8, h.f10, n_9_0 0, p ⟨0,by decide⟩ 3, p ⟨3,by decide⟩ 0, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f9, h.f11, h.f12]

private theorem cell212 {r : Register} (h : Frame r) (n_9_1 : Neg r 9 1) (p : Pos r 8) : False := by
  lin_close [h.f0, h.f10, n_9_1 0, p ⟨1,by decide⟩ 0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f11, h.f12]

private theorem cell213 {r : Register} (h : Frame r) (n_9_2 : Neg r 9 2) (p : Pos r 8) : False := by
  lin_close [h.f0, h.f9, h.f10, n_9_2 0, p ⟨2,by decide⟩ 0, h.f1, h.f2, h.f3, h.f4, h.f5, h.f6, h.f7, h.f8, h.f11, h.f12]

private theorem cell214 {r : Register} (h : Frame r) (n_9_3 : Neg r 9 3) (p : Pos r 8) : False := by
  lin_close [h.f0, h.f3, h.f10, h.f11, n_9_3 0, p ⟨2,by decide⟩ 0, p ⟨3,by decide⟩ 0, h.f1, h.f2, h.f4, h.f5, h.f6, h.f7, h.f8, h.f9, h.f12]

private theorem cover0 {r : Register} (h : Frame r) (n_2_0 : Neg r 2 0) (n_3_0 : Neg r 3 0) (o_5 : Outside5 r) (p : Pos r 0) : False := by
  rcases o_5 with n_5_0 | n_5_1 | n_5_2 | n_5_3
  · exact cell0 h n_3_0 n_5_0 p
  · exact cell1 h n_3_0 n_5_1
  · exact cell2 h n_3_0 n_5_2 p
  · exact cell3 h n_2_0 n_3_0 n_5_3 p

private theorem cover1 {r : Register} (h : Frame r) (n_2_0 : Neg r 2 0) (n_3_3 : Neg r 3 3) (o_5 : Outside5 r) (p : Pos r 0) : False := by
  rcases o_5 with n_5_0 | n_5_1 | n_5_2 | n_5_3
  · exact cell6 h n_3_3 n_5_0 p
  · exact cell7 h n_2_0 n_3_3 n_5_1 p
  · exact cell8 h n_2_0 n_3_3 n_5_2 p
  · exact cell9 h n_2_0 n_3_3 n_5_3 p

private theorem cover2 {r : Register} (h : Frame r) (n_2_0 : Neg r 2 0) (o_3 : Outside3 r) (o_5 : Outside5 r) (p : Pos r 0) : False := by
  rcases o_3 with n_3_0 | n_3_1 | n_3_2 | n_3_3
  · exact cover0 h n_2_0 n_3_0 o_5 p
  · exact cell4 h n_2_0 n_3_1 p
  · exact cell5 h n_2_0 n_3_2 p
  · exact cover1 h n_2_0 n_3_3 o_5 p

private theorem cover3 {r : Register} (h : Frame r) (n_2_2 : Neg r 2 2) (n_3_0 : Neg r 3 0) (n_4_0 : Neg r 4 0) (o_5 : Outside5 r) (p : Pos r 0) : False := by
  rcases o_5 with n_5_0 | n_5_1 | n_5_2 | n_5_3
  · exact cell11 h n_2_2 n_3_0 n_4_0 n_5_0 p
  · exact cell1 h n_3_0 n_5_1
  · exact cell2 h n_3_0 n_5_2 p
  · exact cell12 h n_2_2 n_3_0 n_4_0 n_5_3 p

private theorem cover4 {r : Register} (h : Frame r) (n_1_0 : Neg r 1 0) (n_2_2 : Neg r 2 2) (n_3_3 : Neg r 3 3) (n_4_0 : Neg r 4 0) (o_5 : Outside5 r) (p : Pos r 0) : False := by
  rcases o_5 with n_5_0 | n_5_1 | n_5_2 | n_5_3
  · exact cell15 h n_2_2 n_3_3 n_4_0 n_5_0 p
  · exact cell16 h n_1_0 n_2_2 n_3_3 n_5_1
  · exact cell17 h n_3_3 n_5_2 p
  · exact cell18 h n_1_0 n_2_2 n_3_3 n_4_0 n_5_3 p

private theorem cover5 {r : Register} (h : Frame r) (n_1_0 : Neg r 1 0) (n_2_2 : Neg r 2 2) (n_4_0 : Neg r 4 0) (o_3 : Outside3 r) (o_5 : Outside5 r) (p : Pos r 0) : False := by
  rcases o_3 with n_3_0 | n_3_1 | n_3_2 | n_3_3
  · exact cover3 h n_2_2 n_3_0 n_4_0 o_5 p
  · exact cell13 h n_1_0 n_3_1 n_4_0 p
  · exact cell14 h n_3_2 n_4_0 p
  · exact cover4 h n_1_0 n_2_2 n_3_3 n_4_0 o_5 p

private theorem cover6 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_4_0 : Neg r 4 0) (o_3 : Outside3 r) (p : Pos r 0) : False := by
  rcases o_3 with n_3_0 | n_3_1 | n_3_2 | n_3_3
  · exact cell20 h n_1_2 n_3_0 n_4_0 p
  · exact cell21 h n_1_2 n_3_1 n_4_0 p
  · exact cell14 h n_3_2 n_4_0 p
  · exact cell22 h n_1_2 n_3_3

private theorem cover7 {r : Register} (h : Frame r) (n_2_2 : Neg r 2 2) (n_3_0 : Neg r 3 0) (n_4_0 : Neg r 4 0) (o_5 : Outside5 r) (p : Pos r 0) : False := by
  rcases o_5 with n_5_0 | n_5_1 | n_5_2 | n_5_3
  · exact cell11 h n_2_2 n_3_0 n_4_0 n_5_0 p
  · exact cell1 h n_3_0 n_5_1
  · exact cell2 h n_3_0 n_5_2 p
  · exact cell12 h n_2_2 n_3_0 n_4_0 n_5_3 p

private theorem cover8 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_2_2 : Neg r 2 2) (n_3_1 : Neg r 3 1) (n_4_0 : Neg r 4 0) (n_6_3 : Neg r 6 3) (n_7_1 : Neg r 7 1) (o_8 : Outside8 r) (p : Pos r 0) : False := by
  rcases o_8 with n_8_0 | n_8_1 | n_8_2 | n_8_3 | n_8_4 | n_8_5 | n_8_6 | n_8_7
  · exact cell27 h n_2_2 n_6_3 n_7_1 n_8_0 p
  · exact cell28 h n_1_3 n_3_1 n_4_0 n_8_1 p
  · exact cell29 h n_4_0 n_6_3 n_7_1 n_8_2
  · exact cell30 h n_1_3 n_2_2 n_3_1 n_4_0 n_8_3 p
  · exact cell31 h n_8_4
  · exact cell32 h n_3_1 n_8_5
  · exact cell33 h n_6_3 n_8_6
  · exact cell34 h n_6_3 n_8_7

private theorem cover9 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_2_2 : Neg r 2 2) (n_3_1 : Neg r 3 1) (n_4_0 : Neg r 4 0) (n_7_1 : Neg r 7 1) (o_6 : Outside6 r) (o_8 : Outside8 r) (p : Pos r 0) : False := by
  rcases o_6 with n_6_0 | n_6_1 | n_6_2 | n_6_3
  · exact cell24 h n_1_3 n_2_2 n_3_1 n_4_0 n_6_0 n_7_1 p
  · exact cell25 h n_6_1 p
  · exact cell26 h n_1_3 n_2_2 n_4_0 n_6_2 n_7_1
  · exact cover8 h n_1_3 n_2_2 n_3_1 n_4_0 n_6_3 n_7_1 o_8 p

private theorem cover10 {r : Register} (h : Frame r) (n_2_2 : Neg r 2 2) (n_3_1 : Neg r 3 1) (n_4_0 : Neg r 4 0) (n_7_3 : Neg r 7 3) (n_8_0 : Neg r 8 0) (o_5 : Outside5 r) (p : Pos r 0) : False := by
  rcases o_5 with n_5_0 | n_5_1 | n_5_2 | n_5_3
  · exact cell36 h n_3_1 n_5_0
  · exact cell37 h n_2_2 n_3_1 n_4_0 n_5_1 n_7_3 n_8_0 p
  · exact cell38 h n_3_1 n_5_2 n_7_3 n_8_0
  · exact cell39 h n_2_2 n_3_1 n_4_0 n_5_3 n_7_3 n_8_0 p

private theorem cover11 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_2_2 : Neg r 2 2) (n_3_1 : Neg r 3 1) (n_4_0 : Neg r 4 0) (n_7_3 : Neg r 7 3) (o_5 : Outside5 r) (o_8 : Outside8 r) (p : Pos r 0) : False := by
  rcases o_8 with n_8_0 | n_8_1 | n_8_2 | n_8_3 | n_8_4 | n_8_5 | n_8_6 | n_8_7
  · exact cover10 h n_2_2 n_3_1 n_4_0 n_7_3 n_8_0 o_5 p
  · exact cell40 h n_1_3 n_2_2 n_3_1 n_4_0 n_8_1 p
  · exact cell41 h n_7_3 n_8_2
  · exact cell30 h n_1_3 n_2_2 n_3_1 n_4_0 n_8_3 p
  · exact cell42 h n_3_1 n_7_3 n_8_4
  · exact cell43 h n_3_1 n_7_3 n_8_5
  · exact cell44 h n_7_3 n_8_6
  · exact cell45 h n_7_3 n_8_7

private theorem cover12 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_2_2 : Neg r 2 2) (n_3_1 : Neg r 3 1) (n_4_0 : Neg r 4 0) (o_5 : Outside5 r) (o_6 : Outside6 r) (o_7 : Outside7 r) (o_8 : Outside8 r) (p : Pos r 0) : False := by
  rcases o_7 with n_7_0 | n_7_1 | n_7_2 | n_7_3 | n_7_4 | n_7_5 | n_7_6 | n_7_7
  · exact cell23 h n_1_3 n_3_1 n_4_0 n_7_0
  · exact cover9 h n_1_3 n_2_2 n_3_1 n_4_0 n_7_1 o_6 o_8 p
  · exact cell35 h n_1_3 n_4_0 n_7_2
  · exact cover11 h n_1_3 n_2_2 n_3_1 n_4_0 n_7_3 o_5 o_8 p
  · exact cell46 h n_7_4
  · exact cell47 h n_3_1 n_7_5
  · exact cell48 h n_4_0 n_7_6
  · exact cell49 h n_7_7

private theorem cover13 {r : Register} (h : Frame r) (n_2_2 : Neg r 2 2) (n_3_3 : Neg r 3 3) (n_4_0 : Neg r 4 0) (n_5_1 : Neg r 5 1) (o_8 : Outside8 r) (p : Pos r 0) : False := by
  rcases o_8 with n_8_0 | n_8_1 | n_8_2 | n_8_3 | n_8_4 | n_8_5 | n_8_6 | n_8_7
  · exact cell51 h n_2_2 n_3_3 n_4_0 n_5_1 n_8_0 p
  · exact cell52 h n_2_2 n_3_3 n_4_0 n_8_1 p
  · exact cell53 h n_3_3 n_8_2
  · exact cell54 h n_2_2 n_3_3 n_4_0 n_5_1 n_8_3 p
  · exact cell31 h n_8_4
  · exact cell55 h n_5_1 n_8_5
  · exact cell56 h n_3_3 n_8_6
  · exact cell57 h n_8_7

private theorem cover14 {r : Register} (h : Frame r) (n_2_2 : Neg r 2 2) (n_3_3 : Neg r 3 3) (n_4_0 : Neg r 4 0) (n_5_3 : Neg r 5 3) (o_8 : Outside8 r) (p : Pos r 0) : False := by
  rcases o_8 with n_8_0 | n_8_1 | n_8_2 | n_8_3 | n_8_4 | n_8_5 | n_8_6 | n_8_7
  · exact cell58 h n_2_2 n_4_0 n_5_3 n_8_0 p
  · exact cell52 h n_2_2 n_3_3 n_4_0 n_8_1 p
  · exact cell53 h n_3_3 n_8_2
  · exact cell59 h n_2_2 n_4_0 n_8_3 p
  · exact cell31 h n_8_4
  · exact cell60 h n_3_3 n_5_3 n_8_5
  · exact cell56 h n_3_3 n_8_6
  · exact cell57 h n_8_7

private theorem cover15 {r : Register} (h : Frame r) (n_2_2 : Neg r 2 2) (n_3_3 : Neg r 3 3) (n_4_0 : Neg r 4 0) (o_5 : Outside5 r) (o_8 : Outside8 r) (p : Pos r 0) : False := by
  rcases o_5 with n_5_0 | n_5_1 | n_5_2 | n_5_3
  · exact cell15 h n_2_2 n_3_3 n_4_0 n_5_0 p
  · exact cover13 h n_2_2 n_3_3 n_4_0 n_5_1 o_8 p
  · exact cell17 h n_3_3 n_5_2 p
  · exact cover14 h n_2_2 n_3_3 n_4_0 n_5_3 o_8 p

private theorem cover16 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_2_2 : Neg r 2 2) (n_4_0 : Neg r 4 0) (o_3 : Outside3 r) (o_5 : Outside5 r) (o_6 : Outside6 r) (o_7 : Outside7 r) (o_8 : Outside8 r) (p : Pos r 0) : False := by
  rcases o_3 with n_3_0 | n_3_1 | n_3_2 | n_3_3
  · exact cover7 h n_2_2 n_3_0 n_4_0 o_5 p
  · exact cover12 h n_1_3 n_2_2 n_3_1 n_4_0 o_5 o_6 o_7 o_8 p
  · exact cell50 h n_1_3 n_3_2
  · exact cover15 h n_2_2 n_3_3 n_4_0 o_5 o_8 p

private theorem cover17 {r : Register} (h : Frame r) (n_2_2 : Neg r 2 2) (n_4_0 : Neg r 4 0) (o_1 : Outside1 r) (o_3 : Outside3 r) (o_5 : Outside5 r) (o_6 : Outside6 r) (o_7 : Outside7 r) (o_8 : Outside8 r) (p : Pos r 0) : False := by
  rcases o_1 with n_1_0 | n_1_1 | n_1_2 | n_1_3
  · exact cover5 h n_1_0 n_2_2 n_4_0 o_3 o_5 p
  · exact cell19 h n_1_1 n_4_0 p
  · exact cover6 h n_1_2 n_4_0 o_3 p
  · exact cover16 h n_1_3 n_2_2 n_4_0 o_3 o_5 o_6 o_7 o_8 p

private theorem cover18 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_3_1 : Neg r 3 1) (n_4_2 : Neg r 4 2) (n_5_1 : Neg r 5 1) (o_6 : Outside6 r) (p : Pos r 0) : False := by
  rcases o_6 with n_6_0 | n_6_1 | n_6_2 | n_6_3
  · exact cell64 h n_1_1 n_4_2 n_6_0
  · exact cell25 h n_6_1 p
  · exact cell65 h n_1_1 n_6_2 p
  · exact cell66 h n_3_1 n_4_2 n_5_1 n_6_3 p

private theorem cover19 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_4_2 : Neg r 4 2) (n_5_1 : Neg r 5 1) (n_6_0 : Neg r 6 0) (o_7 : Outside7 r) (p : Pos r 0) : False := by
  rcases o_7 with n_7_0 | n_7_1 | n_7_2 | n_7_3 | n_7_4 | n_7_5 | n_7_6 | n_7_7
  · exact cell68 h n_4_2 n_5_1 n_7_0
  · exact cell69 h n_1_3 n_4_2 n_6_0 n_7_1
  · exact cell70 h n_1_3 n_6_0 n_7_2
  · exact cell71 h n_4_2 n_7_3
  · exact cell72 h n_4_2 n_5_1 n_7_4
  · exact cell73 h n_4_2 n_7_5
  · exact cell74 h n_4_2 n_6_0 n_7_6 p
  · exact cell75 h n_4_2 n_6_0 n_7_7 p

private theorem cover20 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_3_1 : Neg r 3 1) (n_4_2 : Neg r 4 2) (n_5_1 : Neg r 5 1) (n_6_2 : Neg r 6 2) (o_7 : Outside7 r) (p : Pos r 0) : False := by
  rcases o_7 with n_7_0 | n_7_1 | n_7_2 | n_7_3 | n_7_4 | n_7_5 | n_7_6 | n_7_7
  · exact cell68 h n_4_2 n_5_1 n_7_0
  · exact cell76 h n_1_3 n_3_1 n_5_1 n_6_2 n_7_1 p
  · exact cell77 h n_1_3 n_7_2 p
  · exact cell71 h n_4_2 n_7_3
  · exact cell72 h n_4_2 n_5_1 n_7_4
  · exact cell73 h n_4_2 n_7_5
  · exact cell78 h n_4_2 n_6_2 n_7_6
  · exact cell79 h n_4_2 n_6_2 n_7_7 p

private theorem cover21 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_3_1 : Neg r 3 1) (n_4_2 : Neg r 4 2) (n_5_1 : Neg r 5 1) (o_6 : Outside6 r) (o_7 : Outside7 r) (p : Pos r 0) : False := by
  rcases o_6 with n_6_0 | n_6_1 | n_6_2 | n_6_3
  · exact cover19 h n_1_3 n_4_2 n_5_1 n_6_0 o_7 p
  · exact cell25 h n_6_1 p
  · exact cover20 h n_1_3 n_3_1 n_4_2 n_5_1 n_6_2 o_7 p
  · exact cell80 h n_4_2 n_6_3 p

private theorem cover22 {r : Register} (h : Frame r) (n_3_1 : Neg r 3 1) (n_4_2 : Neg r 4 2) (n_5_1 : Neg r 5 1) (o_1 : Outside1 r) (o_6 : Outside6 r) (o_7 : Outside7 r) (p : Pos r 0) : False := by
  rcases o_1 with n_1_0 | n_1_1 | n_1_2 | n_1_3
  · exact cell63 h n_1_0 n_4_2 n_5_1
  · exact cover18 h n_1_1 n_3_1 n_4_2 n_5_1 o_6 p
  · exact cell67 h n_1_2 n_3_1 n_5_1 p
  · exact cover21 h n_1_3 n_3_1 n_4_2 n_5_1 o_6 o_7 p

private theorem cover23 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_3_1 : Neg r 3 1) (n_4_2 : Neg r 4 2) (n_5_2 : Neg r 5 2) (n_6_0 : Neg r 6 0) (o_7 : Outside7 r) (p : Pos r 0) : False := by
  rcases o_7 with n_7_0 | n_7_1 | n_7_2 | n_7_3 | n_7_4 | n_7_5 | n_7_6 | n_7_7
  · exact cell84 h n_1_3 n_3_1 n_7_0
  · exact cell85 h n_1_3 n_4_2 n_6_0 n_7_1
  · exact cell86 h n_1_3 n_6_0 n_7_2
  · exact cell71 h n_4_2 n_7_3
  · exact cell87 h n_3_1 n_4_2 n_5_2 n_7_4
  · exact cell73 h n_4_2 n_7_5
  · exact cell88 h n_4_2 n_5_2 n_6_0 n_7_6 p
  · exact cell75 h n_4_2 n_6_0 n_7_7 p

private theorem cover24 {r : Register} (h : Frame r) (n_3_1 : Neg r 3 1) (n_4_2 : Neg r 4 2) (n_5_2 : Neg r 5 2) (n_6_0 : Neg r 6 0) (o_1 : Outside1 r) (o_7 : Outside7 r) (p : Pos r 0) : False := by
  rcases o_1 with n_1_0 | n_1_1 | n_1_2 | n_1_3
  · exact cell81 h n_1_0 n_3_1 n_4_2 p
  · exact cell82 h n_1_1 n_6_0
  · exact cell83 h n_1_2 n_3_1 n_6_0 p
  · exact cover23 h n_1_3 n_3_1 n_4_2 n_5_2 n_6_0 o_7 p

private theorem cover25 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_3_1 : Neg r 3 1) (n_4_2 : Neg r 4 2) (n_5_2 : Neg r 5 2) (n_6_2 : Neg r 6 2) (o_7 : Outside7 r) (p : Pos r 0) : False := by
  rcases o_7 with n_7_0 | n_7_1 | n_7_2 | n_7_3 | n_7_4 | n_7_5 | n_7_6 | n_7_7
  · exact cell91 h n_1_3 n_3_1 n_4_2 n_7_0
  · exact cell92 h n_1_3 n_3_1 n_6_2 n_7_1 p
  · exact cell77 h n_1_3 n_7_2 p
  · exact cell71 h n_4_2 n_7_3
  · exact cell87 h n_3_1 n_4_2 n_5_2 n_7_4
  · exact cell73 h n_4_2 n_7_5
  · exact cell78 h n_4_2 n_6_2 n_7_6
  · exact cell79 h n_4_2 n_6_2 n_7_7 p

private theorem cover26 {r : Register} (h : Frame r) (n_3_1 : Neg r 3 1) (n_4_2 : Neg r 4 2) (n_5_2 : Neg r 5 2) (n_6_2 : Neg r 6 2) (o_1 : Outside1 r) (o_7 : Outside7 r) (p : Pos r 0) : False := by
  rcases o_1 with n_1_0 | n_1_1 | n_1_2 | n_1_3
  · exact cell81 h n_1_0 n_3_1 n_4_2 p
  · exact cell89 h n_1_1 n_6_2 p
  · exact cell90 h n_1_2 n_3_1 n_6_2 p
  · exact cover25 h n_1_3 n_3_1 n_4_2 n_5_2 n_6_2 o_7 p

private theorem cover27 {r : Register} (h : Frame r) (n_3_1 : Neg r 3 1) (n_4_2 : Neg r 4 2) (n_5_2 : Neg r 5 2) (o_1 : Outside1 r) (o_6 : Outside6 r) (o_7 : Outside7 r) (p : Pos r 0) : False := by
  rcases o_6 with n_6_0 | n_6_1 | n_6_2 | n_6_3
  · exact cover24 h n_3_1 n_4_2 n_5_2 n_6_0 o_1 o_7 p
  · exact cell25 h n_6_1 p
  · exact cover26 h n_3_1 n_4_2 n_5_2 n_6_2 o_1 o_7 p
  · exact cell93 h n_3_1 n_4_2 n_5_2 n_6_3 p

private theorem cover28 {r : Register} (h : Frame r) (n_3_1 : Neg r 3 1) (n_4_2 : Neg r 4 2) (o_1 : Outside1 r) (o_5 : Outside5 r) (o_6 : Outside6 r) (o_7 : Outside7 r) (p : Pos r 0) : False := by
  rcases o_5 with n_5_0 | n_5_1 | n_5_2 | n_5_3
  · exact cell36 h n_3_1 n_5_0
  · exact cover22 h n_3_1 n_4_2 n_5_1 o_1 o_6 o_7 p
  · exact cover27 h n_3_1 n_4_2 n_5_2 o_1 o_6 o_7 p
  · exact cell94 h n_4_2 n_5_3

private theorem cover29 {r : Register} (h : Frame r) (n_3_3 : Neg r 3 3) (n_4_2 : Neg r 4 2) (n_5_1 : Neg r 5 1) (o_8 : Outside8 r) (p : Pos r 0) : False := by
  rcases o_8 with n_8_0 | n_8_1 | n_8_2 | n_8_3 | n_8_4 | n_8_5 | n_8_6 | n_8_7
  · exact cell97 h n_3_3 n_4_2 n_5_1 n_8_0
  · exact cell98 h n_3_3 n_4_2 n_5_1 n_8_1 p
  · exact cell53 h n_3_3 n_8_2
  · exact cell99 h n_3_3 n_4_2 n_8_3
  · exact cell100 h n_3_3 n_4_2 n_5_1 n_8_4
  · exact cell101 h n_4_2 n_8_5
  · exact cell56 h n_3_3 n_8_6
  · exact cell57 h n_8_7

private theorem cover30 {r : Register} (h : Frame r) (n_3_3 : Neg r 3 3) (n_4_2 : Neg r 4 2) (o_5 : Outside5 r) (o_8 : Outside8 r) (p : Pos r 0) : False := by
  rcases o_5 with n_5_0 | n_5_1 | n_5_2 | n_5_3
  · exact cell96 h n_3_3 n_4_2 n_5_0 p
  · exact cover29 h n_3_3 n_4_2 n_5_1 o_8 p
  · exact cell17 h n_3_3 n_5_2 p
  · exact cell102 h n_3_3 n_4_2 n_5_3

private theorem cover31 {r : Register} (h : Frame r) (n_4_2 : Neg r 4 2) (o_1 : Outside1 r) (o_3 : Outside3 r) (o_5 : Outside5 r) (o_6 : Outside6 r) (o_7 : Outside7 r) (o_8 : Outside8 r) (p : Pos r 0) : False := by
  rcases o_3 with n_3_0 | n_3_1 | n_3_2 | n_3_3
  · exact cell62 h n_3_0 n_4_2 p
  · exact cover28 h n_3_1 n_4_2 o_1 o_5 o_6 o_7 p
  · exact cell95 h n_3_2 n_4_2 p
  · exact cover30 h n_3_3 n_4_2 o_5 o_8 p

private theorem cover32 {r : Register} (h : Frame r) (n_2_2 : Neg r 2 2) (o_1 : Outside1 r) (o_3 : Outside3 r) (o_4 : Outside4 r) (o_5 : Outside5 r) (o_6 : Outside6 r) (o_7 : Outside7 r) (o_8 : Outside8 r) (p : Pos r 0) : False := by
  rcases o_4 with n_4_0 | n_4_1 | n_4_2 | n_4_3
  · exact cover17 h n_2_2 n_4_0 o_1 o_3 o_5 o_6 o_7 o_8 p
  · exact cell61 h n_4_1 p
  · exact cover31 h n_4_2 o_1 o_3 o_5 o_6 o_7 o_8 p
  · exact cell103 h n_4_3 p

private theorem cover33 {r : Register} (h : Frame r) (o_1 : Outside1 r) (o_2 : Outside2 r) (o_3 : Outside3 r) (o_4 : Outside4 r) (o_5 : Outside5 r) (o_6 : Outside6 r) (o_7 : Outside7 r) (o_8 : Outside8 r) (p : Pos r 0) : False := by
  rcases o_2 with n_2_0 | n_2_1 | n_2_2 | n_2_3
  · exact cover2 h n_2_0 o_3 o_5 p
  · exact cell10 h n_2_1 p
  · exact cover32 h n_2_2 o_1 o_3 o_4 o_5 o_6 o_7 o_8 p
  · exact cell104 h n_2_3 p

private theorem cover34 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_4_1 : Neg r 4 1) (o_6 : Outside6 r) (p : Pos r 9) : False := by
  rcases o_6 with n_6_0 | n_6_1 | n_6_2 | n_6_3
  · exact cell107 h n_4_1 n_6_0
  · exact cell108 h n_4_1 n_6_1 p
  · exact cell109 h n_1_1 n_6_2 p
  · exact cell110 h n_4_1 n_6_3 p

private theorem cover35 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_4_2 : Neg r 4 2) (o_6 : Outside6 r) (p : Pos r 9) : False := by
  rcases o_6 with n_6_0 | n_6_1 | n_6_2 | n_6_3
  · exact cell111 h n_1_1 n_4_2 n_6_0 p
  · exact cell112 h n_4_2 n_6_1 p
  · exact cell113 h n_1_1 n_4_2 n_6_2 p
  · exact cell114 h n_1_1 n_4_2 n_6_3 p

private theorem cover36 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (o_4 : Outside4 r) (o_6 : Outside6 r) (p : Pos r 9) : False := by
  rcases o_4 with n_4_0 | n_4_1 | n_4_2 | n_4_3
  · exact cell106 h n_1_1 n_4_0 p
  · exact cover34 h n_1_1 n_4_1 o_6 p
  · exact cover35 h n_1_1 n_4_2 o_6 p
  · exact cell115 h n_1_1 n_4_3 p

private theorem cover37 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_3_1 : Neg r 3 1) (n_4_1 : Neg r 4 1) (o_6 : Outside6 r) (p : Pos r 9) : False := by
  rcases o_6 with n_6_0 | n_6_1 | n_6_2 | n_6_3
  · exact cell107 h n_4_1 n_6_0
  · exact cell120 h n_1_3 n_3_1 n_4_1 n_6_1 p
  · exact cell121 h n_1_3 n_3_1 n_4_1 n_6_2 p
  · exact cell110 h n_4_1 n_6_3 p

private theorem cover38 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_2_1 : Neg r 2 1) (n_3_1 : Neg r 3 1) (n_4_2 : Neg r 4 2) (o_6 : Outside6 r) (p : Pos r 9) : False := by
  rcases o_6 with n_6_0 | n_6_1 | n_6_2 | n_6_3
  · exact cell122 h n_1_3 n_2_1 n_3_1 n_4_2 n_6_0 p
  · exact cell123 h n_1_3 n_3_1 n_4_2 n_6_1 p
  · exact cell124 h n_1_3 n_2_1 n_3_1 n_4_2 n_6_2 p
  · exact cell125 h n_1_3 n_2_1 n_4_2 n_6_3 p

private theorem cover39 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_2_1 : Neg r 2 1) (n_3_1 : Neg r 3 1) (o_4 : Outside4 r) (o_6 : Outside6 r) (p : Pos r 9) : False := by
  rcases o_4 with n_4_0 | n_4_1 | n_4_2 | n_4_3
  · exact cell119 h n_2_1 n_3_1 n_4_0 p
  · exact cover37 h n_1_3 n_3_1 n_4_1 o_6 p
  · exact cover38 h n_1_3 n_2_1 n_3_1 n_4_2 o_6 p
  · exact cell126 h n_3_1 n_4_3 p

private theorem cover40 {r : Register} (h : Frame r) (n_2_2 : Neg r 2 2) (n_3_1 : Neg r 3 1) (n_4_0 : Neg r 4 0) (n_6_3 : Neg r 6 3) (n_7_1 : Neg r 7 1) (o_8 : Outside8 r) (p : Pos r 9) : False := by
  rcases o_8 with n_8_0 | n_8_1 | n_8_2 | n_8_3 | n_8_4 | n_8_5 | n_8_6 | n_8_7
  · exact cell131 h n_2_2 n_6_3 n_7_1 n_8_0 p
  · exact cell132 h n_2_2 n_3_1 n_4_0 n_8_1 p
  · exact cell29 h n_4_0 n_6_3 n_7_1 n_8_2
  · exact cell133 h n_2_2 n_3_1 n_8_3
  · exact cell134 h n_3_1 n_8_4 p
  · exact cell32 h n_3_1 n_8_5
  · exact cell33 h n_6_3 n_8_6
  · exact cell34 h n_6_3 n_8_7

private theorem cover41 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_2_2 : Neg r 2 2) (n_3_1 : Neg r 3 1) (n_4_0 : Neg r 4 0) (n_7_1 : Neg r 7 1) (o_6 : Outside6 r) (o_8 : Outside8 r) (p : Pos r 9) : False := by
  rcases o_6 with n_6_0 | n_6_1 | n_6_2 | n_6_3
  · exact cell128 h n_2_2 n_3_1 n_4_0 n_6_0 n_7_1 p
  · exact cell129 h n_4_0 n_6_1
  · exact cell130 h n_1_3 n_2_2 n_4_0 n_6_2 n_7_1 p
  · exact cover40 h n_2_2 n_3_1 n_4_0 n_6_3 n_7_1 o_8 p

private theorem cover42 {r : Register} (h : Frame r) (n_2_2 : Neg r 2 2) (n_3_1 : Neg r 3 1) (n_7_3 : Neg r 7 3) (n_8_0 : Neg r 8 0) (o_5 : Outside5 r) (p : Pos r 9) : False := by
  rcases o_5 with n_5_0 | n_5_1 | n_5_2 | n_5_3
  · exact cell136 h n_5_0 p
  · exact cell137 h n_2_2 n_3_1 n_5_1 n_7_3 n_8_0 p
  · exact cell38 h n_3_1 n_5_2 n_7_3 n_8_0
  · exact cell138 h n_2_2 n_3_1 n_5_3 n_7_3 n_8_0

private theorem cover43 {r : Register} (h : Frame r) (n_2_2 : Neg r 2 2) (n_3_1 : Neg r 3 1) (n_4_0 : Neg r 4 0) (n_7_3 : Neg r 7 3) (o_5 : Outside5 r) (o_8 : Outside8 r) (p : Pos r 9) : False := by
  rcases o_8 with n_8_0 | n_8_1 | n_8_2 | n_8_3 | n_8_4 | n_8_5 | n_8_6 | n_8_7
  · exact cover42 h n_2_2 n_3_1 n_7_3 n_8_0 o_5 p
  · exact cell132 h n_2_2 n_3_1 n_4_0 n_8_1 p
  · exact cell41 h n_7_3 n_8_2
  · exact cell133 h n_2_2 n_3_1 n_8_3
  · exact cell42 h n_3_1 n_7_3 n_8_4
  · exact cell43 h n_3_1 n_7_3 n_8_5
  · exact cell44 h n_7_3 n_8_6
  · exact cell45 h n_7_3 n_8_7

private theorem cover44 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_2_2 : Neg r 2 2) (n_3_1 : Neg r 3 1) (n_4_0 : Neg r 4 0) (o_5 : Outside5 r) (o_6 : Outside6 r) (o_7 : Outside7 r) (o_8 : Outside8 r) (p : Pos r 9) : False := by
  rcases o_7 with n_7_0 | n_7_1 | n_7_2 | n_7_3 | n_7_4 | n_7_5 | n_7_6 | n_7_7
  · exact cell127 h n_3_1 n_4_0 n_7_0 p
  · exact cover41 h n_1_3 n_2_2 n_3_1 n_4_0 n_7_1 o_6 o_8 p
  · exact cell135 h n_1_3 n_4_0 n_7_2 p
  · exact cover43 h n_2_2 n_3_1 n_4_0 n_7_3 o_5 o_8 p
  · exact cell139 h n_3_1 n_7_4 p
  · exact cell47 h n_3_1 n_7_5
  · exact cell48 h n_4_0 n_7_6
  · exact cell49 h n_7_7

private theorem cover45 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_3_1 : Neg r 3 1) (n_4_1 : Neg r 4 1) (o_6 : Outside6 r) (p : Pos r 9) : False := by
  rcases o_6 with n_6_0 | n_6_1 | n_6_2 | n_6_3
  · exact cell107 h n_4_1 n_6_0
  · exact cell120 h n_1_3 n_3_1 n_4_1 n_6_1 p
  · exact cell121 h n_1_3 n_3_1 n_4_1 n_6_2 p
  · exact cell110 h n_4_1 n_6_3 p

private theorem cover46 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_3_1 : Neg r 3 1) (n_4_2 : Neg r 4 2) (n_5_1 : Neg r 5 1) (n_6_0 : Neg r 6 0) (o_7 : Outside7 r) (p : Pos r 9) : False := by
  rcases o_7 with n_7_0 | n_7_1 | n_7_2 | n_7_3 | n_7_4 | n_7_5 | n_7_6 | n_7_7
  · exact cell68 h n_4_2 n_5_1 n_7_0
  · exact cell140 h n_1_3 n_4_2 n_6_0 n_7_1 p
  · exact cell141 h n_1_3 n_3_1 n_4_2 n_6_0 n_7_2 p
  · exact cell71 h n_4_2 n_7_3
  · exact cell142 h n_3_1 n_4_2 n_7_4 p
  · exact cell73 h n_4_2 n_7_5
  · exact cell143 h n_4_2 n_6_0 n_7_6 p
  · exact cell144 h n_4_2 n_6_0 n_7_7

private theorem cover47 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_3_1 : Neg r 3 1) (n_4_2 : Neg r 4 2) (n_5_1 : Neg r 5 1) (n_6_2 : Neg r 6 2) (o_7 : Outside7 r) (p : Pos r 9) : False := by
  rcases o_7 with n_7_0 | n_7_1 | n_7_2 | n_7_3 | n_7_4 | n_7_5 | n_7_6 | n_7_7
  · exact cell68 h n_4_2 n_5_1 n_7_0
  · exact cell146 h n_1_3 n_3_1 n_6_2 n_7_1 p
  · exact cell147 h n_1_3 n_3_1 n_7_2 p
  · exact cell71 h n_4_2 n_7_3
  · exact cell142 h n_3_1 n_4_2 n_7_4 p
  · exact cell73 h n_4_2 n_7_5
  · exact cell78 h n_4_2 n_6_2 n_7_6
  · exact cell49 h n_7_7

private theorem cover48 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_3_1 : Neg r 3 1) (n_4_2 : Neg r 4 2) (n_5_1 : Neg r 5 1) (o_6 : Outside6 r) (o_7 : Outside7 r) (p : Pos r 9) : False := by
  rcases o_6 with n_6_0 | n_6_1 | n_6_2 | n_6_3
  · exact cover46 h n_1_3 n_3_1 n_4_2 n_5_1 n_6_0 o_7 p
  · exact cell145 h n_1_3 n_3_1 n_4_2 n_6_1 p
  · exact cover47 h n_1_3 n_3_1 n_4_2 n_5_1 n_6_2 o_7 p
  · exact cell148 h n_4_2 n_6_3 p

private theorem cover49 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_3_1 : Neg r 3 1) (n_4_2 : Neg r 4 2) (n_5_2 : Neg r 5 2) (n_7_1 : Neg r 7 1) (o_6 : Outside6 r) (p : Pos r 9) : False := by
  rcases o_6 with n_6_0 | n_6_1 | n_6_2 | n_6_3
  · exact cell140 h n_1_3 n_4_2 n_6_0 n_7_1 p
  · exact cell145 h n_1_3 n_3_1 n_4_2 n_6_1 p
  · exact cell150 h n_1_3 n_3_1 n_6_2 n_7_1 p
  · exact cell151 h n_5_2 n_6_3 n_7_1

private theorem cover50 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_3_1 : Neg r 3 1) (n_4_2 : Neg r 4 2) (n_5_2 : Neg r 5 2) (o_6 : Outside6 r) (o_7 : Outside7 r) (p : Pos r 9) : False := by
  rcases o_7 with n_7_0 | n_7_1 | n_7_2 | n_7_3 | n_7_4 | n_7_5 | n_7_6 | n_7_7
  · exact cell149 h n_1_3 n_3_1 n_4_2 n_7_0 p
  · exact cover49 h n_1_3 n_3_1 n_4_2 n_5_2 n_7_1 o_6 p
  · exact cell147 h n_1_3 n_3_1 n_7_2 p
  · exact cell71 h n_4_2 n_7_3
  · exact cell142 h n_3_1 n_4_2 n_7_4 p
  · exact cell73 h n_4_2 n_7_5
  · exact cell152 h n_4_2 n_5_2 n_7_6
  · exact cell49 h n_7_7

private theorem cover51 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_3_1 : Neg r 3 1) (n_4_2 : Neg r 4 2) (o_5 : Outside5 r) (o_6 : Outside6 r) (o_7 : Outside7 r) (p : Pos r 9) : False := by
  rcases o_5 with n_5_0 | n_5_1 | n_5_2 | n_5_3
  · exact cell136 h n_5_0 p
  · exact cover48 h n_1_3 n_3_1 n_4_2 n_5_1 o_6 o_7 p
  · exact cover50 h n_1_3 n_3_1 n_4_2 n_5_2 o_6 o_7 p
  · exact cell94 h n_4_2 n_5_3

private theorem cover52 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_2_2 : Neg r 2 2) (n_3_1 : Neg r 3 1) (o_4 : Outside4 r) (o_5 : Outside5 r) (o_6 : Outside6 r) (o_7 : Outside7 r) (o_8 : Outside8 r) (p : Pos r 9) : False := by
  rcases o_4 with n_4_0 | n_4_1 | n_4_2 | n_4_3
  · exact cover44 h n_1_3 n_2_2 n_3_1 n_4_0 o_5 o_6 o_7 o_8 p
  · exact cover45 h n_1_3 n_3_1 n_4_1 o_6 p
  · exact cover51 h n_1_3 n_3_1 n_4_2 o_5 o_6 o_7 p
  · exact cell153 h n_2_2 n_4_3

private theorem cover53 {r : Register} (h : Frame r) (n_2_3 : Neg r 2 3) (n_3_1 : Neg r 3 1) (o_4 : Outside4 r) (p : Pos r 9) : False := by
  rcases o_4 with n_4_0 | n_4_1 | n_4_2 | n_4_3
  · exact cell154 h n_2_3 n_3_1 n_4_0 p
  · exact cell155 h n_2_3 n_3_1 n_4_1 p
  · exact cell156 h n_2_3 n_4_2
  · exact cell126 h n_3_1 n_4_3 p

private theorem cover54 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_3_1 : Neg r 3 1) (o_2 : Outside2 r) (o_4 : Outside4 r) (o_5 : Outside5 r) (o_6 : Outside6 r) (o_7 : Outside7 r) (o_8 : Outside8 r) (p : Pos r 9) : False := by
  rcases o_2 with n_2_0 | n_2_1 | n_2_2 | n_2_3
  · exact cell118 h n_1_3 n_2_0 n_3_1 p
  · exact cover39 h n_1_3 n_2_1 n_3_1 o_4 o_6 p
  · exact cover52 h n_1_3 n_2_2 n_3_1 o_4 o_5 o_6 o_7 o_8 p
  · exact cover53 h n_2_3 n_3_1 o_4 p

private theorem cover55 {r : Register} (h : Frame r) (n_2_2 : Neg r 2 2) (n_3_3 : Neg r 3 3) (n_4_0 : Neg r 4 0) (n_5_1 : Neg r 5 1) (o_8 : Outside8 r) (p : Pos r 9) : False := by
  rcases o_8 with n_8_0 | n_8_1 | n_8_2 | n_8_3 | n_8_4 | n_8_5 | n_8_6 | n_8_7
  · exact cell160 h n_2_2 n_3_3 n_5_1 n_8_0
  · exact cell161 h n_2_2 n_4_0 n_8_1
  · exact cell53 h n_3_3 n_8_2
  · exact cell162 h n_2_2 n_5_1 n_8_3
  · exact cell163 h n_3_3 n_5_1 n_8_4 p
  · exact cell55 h n_5_1 n_8_5
  · exact cell164 h n_4_0 n_8_6
  · exact cell57 h n_8_7

private theorem cover56 {r : Register} (h : Frame r) (n_3_3 : Neg r 3 3) (n_4_0 : Neg r 4 0) (n_5_1 : Neg r 5 1) (o_2 : Outside2 r) (o_8 : Outside8 r) (p : Pos r 9) : False := by
  rcases o_2 with n_2_0 | n_2_1 | n_2_2 | n_2_3
  · exact cell158 h n_2_0 n_5_1
  · exact cell159 h n_2_1 n_3_3 n_4_0 n_5_1 p
  · exact cover55 h n_2_2 n_3_3 n_4_0 n_5_1 o_8 p
  · exact cell165 h n_2_3 n_3_3 n_4_0 n_5_1 p

private theorem cover57 {r : Register} (h : Frame r) (n_2_2 : Neg r 2 2) (n_3_3 : Neg r 3 3) (n_4_0 : Neg r 4 0) (n_5_3 : Neg r 5 3) (o_8 : Outside8 r) (p : Pos r 9) : False := by
  rcases o_8 with n_8_0 | n_8_1 | n_8_2 | n_8_3 | n_8_4 | n_8_5 | n_8_6 | n_8_7
  · exact cell169 h n_2_2 n_5_3 n_8_0 p
  · exact cell170 h n_2_2 n_3_3 n_4_0 n_8_1
  · exact cell53 h n_3_3 n_8_2
  · exact cell171 h n_2_2 n_8_3 p
  · exact cell31 h n_8_4
  · exact cell60 h n_3_3 n_5_3 n_8_5
  · exact cell164 h n_4_0 n_8_6
  · exact cell57 h n_8_7

private theorem cover58 {r : Register} (h : Frame r) (n_3_3 : Neg r 3 3) (n_4_0 : Neg r 4 0) (n_5_3 : Neg r 5 3) (o_2 : Outside2 r) (o_8 : Outside8 r) (p : Pos r 9) : False := by
  rcases o_2 with n_2_0 | n_2_1 | n_2_2 | n_2_3
  · exact cell167 h n_2_0 n_5_3 p
  · exact cell168 h n_2_1 n_3_3 n_4_0 n_5_3 p
  · exact cover57 h n_2_2 n_3_3 n_4_0 n_5_3 o_8 p
  · exact cell172 h n_2_3 n_4_0 n_5_3 p

private theorem cover59 {r : Register} (h : Frame r) (n_3_3 : Neg r 3 3) (n_4_0 : Neg r 4 0) (o_2 : Outside2 r) (o_5 : Outside5 r) (o_8 : Outside8 r) (p : Pos r 9) : False := by
  rcases o_5 with n_5_0 | n_5_1 | n_5_2 | n_5_3
  · exact cell136 h n_5_0 p
  · exact cover56 h n_3_3 n_4_0 n_5_1 o_2 o_8 p
  · exact cell166 h n_3_3 n_5_2 p
  · exact cover58 h n_3_3 n_4_0 n_5_3 o_2 o_8 p

private theorem cover60 {r : Register} (h : Frame r) (n_3_3 : Neg r 3 3) (n_4_2 : Neg r 4 2) (n_5_1 : Neg r 5 1) (n_6_0 : Neg r 6 0) (o_7 : Outside7 r) : False := by
  rcases o_7 with n_7_0 | n_7_1 | n_7_2 | n_7_3 | n_7_4 | n_7_5 | n_7_6 | n_7_7
  · exact cell174 h n_3_3 n_4_2 n_5_1 n_7_0
  · exact cell175 h n_3_3 n_4_2 n_6_0 n_7_1
  · exact cell176 h n_3_3 n_4_2 n_7_2
  · exact cell71 h n_4_2 n_7_3
  · exact cell177 h n_3_3 n_4_2 n_5_1 n_7_4
  · exact cell73 h n_4_2 n_7_5
  · exact cell178 h n_3_3 n_7_6
  · exact cell179 h n_3_3 n_4_2 n_6_0 n_7_7

private theorem cover61 {r : Register} (h : Frame r) (n_3_3 : Neg r 3 3) (n_4_2 : Neg r 4 2) (n_5_1 : Neg r 5 1) (o_6 : Outside6 r) (o_7 : Outside7 r) (p : Pos r 9) : False := by
  rcases o_6 with n_6_0 | n_6_1 | n_6_2 | n_6_3
  · exact cover60 h n_3_3 n_4_2 n_5_1 n_6_0 o_7
  · exact cell180 h n_3_3 n_4_2 n_6_1 p
  · exact cell181 h n_3_3 n_4_2 n_6_2
  · exact cell148 h n_4_2 n_6_3 p

private theorem cover62 {r : Register} (h : Frame r) (n_3_3 : Neg r 3 3) (n_4_2 : Neg r 4 2) (o_5 : Outside5 r) (o_6 : Outside6 r) (o_7 : Outside7 r) (p : Pos r 9) : False := by
  rcases o_5 with n_5_0 | n_5_1 | n_5_2 | n_5_3
  · exact cell136 h n_5_0 p
  · exact cover61 h n_3_3 n_4_2 n_5_1 o_6 o_7 p
  · exact cell166 h n_3_3 n_5_2 p
  · exact cell102 h n_3_3 n_4_2 n_5_3

private theorem cover63 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_3_3 : Neg r 3 3) (o_2 : Outside2 r) (o_4 : Outside4 r) (o_5 : Outside5 r) (o_6 : Outside6 r) (o_7 : Outside7 r) (o_8 : Outside8 r) (p : Pos r 9) : False := by
  rcases o_4 with n_4_0 | n_4_1 | n_4_2 | n_4_3
  · exact cover59 h n_3_3 n_4_0 o_2 o_5 o_8 p
  · exact cell173 h n_1_3 n_3_3 n_4_1 p
  · exact cover62 h n_3_3 n_4_2 o_5 o_6 o_7 p
  · exact cell182 h n_3_3 n_4_3 p

private theorem cover64 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (o_2 : Outside2 r) (o_3 : Outside3 r) (o_4 : Outside4 r) (o_5 : Outside5 r) (o_6 : Outside6 r) (o_7 : Outside7 r) (o_8 : Outside8 r) (p : Pos r 9) : False := by
  rcases o_3 with n_3_0 | n_3_1 | n_3_2 | n_3_3
  · exact cell117 h n_3_0 p
  · exact cover54 h n_1_3 n_3_1 o_2 o_4 o_5 o_6 o_7 o_8 p
  · exact cell157 h n_3_2 p
  · exact cover63 h n_1_3 n_3_3 o_2 o_4 o_5 o_6 o_7 o_8 p

private theorem cover65 {r : Register} (h : Frame r) (o_1 : Outside1 r) (o_2 : Outside2 r) (o_3 : Outside3 r) (o_4 : Outside4 r) (o_5 : Outside5 r) (o_6 : Outside6 r) (o_7 : Outside7 r) (o_8 : Outside8 r) (p : Pos r 9) : False := by
  rcases o_1 with n_1_0 | n_1_1 | n_1_2 | n_1_3
  · exact cell105 h n_1_0 p
  · exact cover36 h n_1_1 o_4 o_6 p
  · exact cell116 h n_1_2 p
  · exact cover64 h n_1_3 o_2 o_3 o_4 o_5 o_6 o_7 o_8 p

private theorem cover66 {r : Register} (h : Frame r) (o_0 : Outside0 r) (p : Pos r 1) : False := by
  rcases o_0 with n_0_0 | n_0_1 | n_0_2 | n_0_3
  · exact cell183 h n_0_0 p
  · exact cell184 h n_0_1 p
  · exact cell185 h n_0_2 p
  · exact cell186 h n_0_3 p

private theorem cover67 {r : Register} (h : Frame r) (o_9 : Outside9 r) (p : Pos r 2) : False := by
  rcases o_9 with n_9_0 | n_9_1 | n_9_2 | n_9_3
  · exact cell187 h n_9_0 p
  · exact cell188 h n_9_1 p
  · exact cell189 h n_9_2 p
  · exact cell190 h n_9_3 p

private theorem cover68 {r : Register} (h : Frame r) (o_0 : Outside0 r) (p : Pos r 3) : False := by
  rcases o_0 with n_0_0 | n_0_1 | n_0_2 | n_0_3
  · exact cell191 h n_0_0 p
  · exact cell192 h n_0_1 p
  · exact cell193 h n_0_2 p
  · exact cell194 h n_0_3 p

private theorem cover69 {r : Register} (h : Frame r) (o_9 : Outside9 r) (p : Pos r 4) : False := by
  rcases o_9 with n_9_0 | n_9_1 | n_9_2 | n_9_3
  · exact cell195 h n_9_0 p
  · exact cell196 h n_9_1 p
  · exact cell197 h n_9_2 p
  · exact cell198 h n_9_3 p

private theorem cover70 {r : Register} (h : Frame r) (o_0 : Outside0 r) (p : Pos r 5) : False := by
  rcases o_0 with n_0_0 | n_0_1 | n_0_2 | n_0_3
  · exact cell199 h n_0_0 p
  · exact cell200 h n_0_1 p
  · exact cell201 h n_0_2 p
  · exact cell202 h n_0_3 p

private theorem cover71 {r : Register} (h : Frame r) (o_9 : Outside9 r) (p : Pos r 6) : False := by
  rcases o_9 with n_9_0 | n_9_1 | n_9_2 | n_9_3
  · exact cell203 h n_9_0 p
  · exact cell204 h n_9_1 p
  · exact cell205 h n_9_2 p
  · exact cell206 h n_9_3 p

private theorem cover72 {r : Register} (h : Frame r) (o_0 : Outside0 r) (p : Pos r 7) : False := by
  rcases o_0 with n_0_0 | n_0_1 | n_0_2 | n_0_3
  · exact cell207 h n_0_0 p
  · exact cell208 h n_0_1 p
  · exact cell209 h n_0_2 p
  · exact cell210 h n_0_3 p

private theorem cover73 {r : Register} (h : Frame r) (o_9 : Outside9 r) (p : Pos r 8) : False := by
  rcases o_9 with n_9_0 | n_9_1 | n_9_2 | n_9_3
  · exact cell211 h n_9_0 p
  · exact cell212 h n_9_1 p
  · exact cell213 h n_9_2 p
  · exact cell214 h n_9_3 p

private theorem included0 {r : Register} (h : Frame r) (yes : contains r 0) : contains r 1 ∨ contains r 2 ∨ contains r 3 ∨ contains r 4 ∨ contains r 5 ∨ contains r 6 ∨ contains r 7 ∨ contains r 8 := by
  by_contra miss
  have p := positive r h 0 yes
  exact cover33 h (outside1 h (by tauto)) (outside2 h (by tauto)) (outside3 h (by tauto)) (outside4 h (by tauto)) (outside5 h (by tauto)) (outside6 h (by tauto)) (outside7 h (by tauto)) (outside8 h (by tauto)) p

private theorem included9 {r : Register} (h : Frame r) (yes : contains r 9) : contains r 1 ∨ contains r 2 ∨ contains r 3 ∨ contains r 4 ∨ contains r 5 ∨ contains r 6 ∨ contains r 7 ∨ contains r 8 := by
  by_contra miss
  have p := positive r h 9 yes
  exact cover65 h (outside1 h (by tauto)) (outside2 h (by tauto)) (outside3 h (by tauto)) (outside4 h (by tauto)) (outside5 h (by tauto)) (outside6 h (by tauto)) (outside7 h (by tauto)) (outside8 h (by tauto)) p

private theorem included1 {r : Register} (h : Frame r) (yes : contains r 1) : contains r 0 ∨ contains r 9 := by
  by_contra miss
  have p := positive r h 1 yes
  exact cover66 h (outside0 h (by tauto)) p

private theorem included2 {r : Register} (h : Frame r) (yes : contains r 2) : contains r 0 ∨ contains r 9 := by
  by_contra miss
  have p := positive r h 2 yes
  exact cover67 h (outside9 h (by tauto)) p

private theorem included3 {r : Register} (h : Frame r) (yes : contains r 3) : contains r 0 ∨ contains r 9 := by
  by_contra miss
  have p := positive r h 3 yes
  exact cover68 h (outside0 h (by tauto)) p

private theorem included4 {r : Register} (h : Frame r) (yes : contains r 4) : contains r 0 ∨ contains r 9 := by
  by_contra miss
  have p := positive r h 4 yes
  exact cover69 h (outside9 h (by tauto)) p

private theorem included5 {r : Register} (h : Frame r) (yes : contains r 5) : contains r 0 ∨ contains r 9 := by
  by_contra miss
  have p := positive r h 5 yes
  exact cover70 h (outside0 h (by tauto)) p

private theorem included6 {r : Register} (h : Frame r) (yes : contains r 6) : contains r 0 ∨ contains r 9 := by
  by_contra miss
  have p := positive r h 6 yes
  exact cover71 h (outside9 h (by tauto)) p

private theorem included7 {r : Register} (h : Frame r) (yes : contains r 7) : contains r 0 ∨ contains r 9 := by
  by_contra miss
  have p := positive r h 7 yes
  exact cover72 h (outside0 h (by tauto)) p

private theorem included8 {r : Register} (h : Frame r) (yes : contains r 8) : contains r 0 ∨ contains r 9 := by
  by_contra miss
  have p := positive r h 8 yes
  exact cover73 h (outside9 h (by tauto)) p

/-- Both inclusions, for all admissible denominators and every site of the specified checkerboard. -/
theorem coverage (r : Register) (h : Frame r) : (contains r 0 ∨ contains r 9) ↔ contains r 1 ∨ contains r 2 ∨ contains r 3 ∨ contains r 4 ∨ contains r 5 ∨ contains r 6 ∨ contains r 7 ∨ contains r 8 := by
  constructor
  · exact fun t => t.elim (included0 h) (included9 h)
  · rintro (t|t|t|t|t|t|t|t)
    · exact included1 h t
    · exact included2 h t
    · exact included3 h t
    · exact included4 h t
    · exact included5 h t
    · exact included6 h t
    · exact included7 h t
    · exact included8 h t

end FLatticePaper.Tiles.BaseCorrectedThreeOneLongEvenSites
