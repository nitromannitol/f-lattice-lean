import FLatticePaper.Tiles.CorrectedFiniteFaces
import Mathlib.Tactic.ClearExcept

/-! Both inclusions of the odd alternate diagram for base family 3 and exit 1 on even sites. -/

namespace FLatticePaper.Tiles.BaseMixedThreeOneOddEvenSites

open CorrectedFiniteFaces CorrectedLevelTests Lean

structure Register where
  d : ℤ
  X : ℤ
  Y : ℤ

structure Frame (r : Register) : Prop where
  f0 : 0 ≤ (r.d-4)
  f1 : r.d%2=0
  f2 : r.X%2=0

/-- The four levels of each polygon and the explicit boundary conditions on each component of the alternate parent. -/
def test (r : Register) : ℕ → ℕ → Test
  | 0, 0 => .line 12 (.sloped (r.Y+1) (3*r.d+4) (3*r.X+6))
  | 0, 1 => .line 12 (.sloped (2*r.d-r.Y+3) (3*r.d+4) (-3*r.X+18))
  | 0, 2 => .line 12 (.sloped (r.X) (2*r.d+3) (4*r.Y))
  | 0, 3 => .line 12 (.sloped (3*r.d-r.X+4) (2*r.d+3) (-4*r.Y+8))
  | 1, 0 => .line 12 (.sloped (r.Y-1) (r.d+2) (-2*r.d+r.X))
  | 1, 1 => .line 12 (.sloped (r.d-r.Y+4) (r.d+2) (2*r.d-r.X+6))
  | 1, 2 => .line 12 (.sloped (-2*r.d+r.X-2) (r.d+2) (2*r.Y-4))
  | 1, 3 => .line 12 (.sloped (3*r.d-r.X+4) (r.d+2) (-2*r.Y+4))
  | 2, 0 => .line 12 (.sloped (-2*r.d+r.Y) (r.d+2) (r.d+r.X))
  | 2, 1 => .line 12 (.sloped (3*r.d-r.Y+3) (r.d+2) (-r.d-r.X+6))
  | 2, 2 => .line 12 (.sloped (r.d+r.X-2) (r.d+2) (-4*r.d+2*r.Y-2))
  | 2, 3 => .line 12 (.sloped (-r.X+4) (r.d+2) (4*r.d-2*r.Y+2))
  | 3, 0 => .line 12 (.sloped (r.Y+1) (2*r.d+2) (2*r.X+4))
  | 3, 1 => .line 12 (.sloped (r.d-r.Y+1) (2*r.d+2) (-2*r.X+8))
  | 3, 2 => .line 12 (.sloped (r.X) (r.d+1) (2*r.Y))
  | 3, 3 => .line 12 (.sloped (2*r.d-r.X+2) (r.d+1) (-2*r.Y+2))
  | 4, 0 => .line 12 (.sloped (-r.d+r.Y+1) (2*r.d+2) (2*r.d+2*r.X+4))
  | 4, 1 => .line 12 (.sloped (2*r.d-r.Y+1) (2*r.d+2) (-2*r.d-2*r.X+8))
  | 4, 2 => .line 12 (.sloped (r.d+r.X) (r.d+1) (-2*r.d+2*r.Y))
  | 4, 3 => .line 12 (.sloped (r.d-r.X+2) (r.d+1) (2*r.d-2*r.Y+2))
  | 5, 0 => .line 12 (.sloped (-r.d+r.Y-2) (2*r.d+2) (-2*r.d+2*r.X-4))
  | 5, 1 => .line 12 (.sloped (2*r.d-r.Y+4) (2*r.d+2) (2*r.d-2*r.X+16))
  | 5, 2 => .line 12 (.sloped (-r.d+r.X-4) (r.d+1) (-2*r.d+2*r.Y-6))
  | 5, 3 => .line 12 (.sloped (3*r.d-r.X+6) (r.d+1) (2*r.d-2*r.Y+8))
  | 6, 0 => .line 12 (.sloped (-2*r.d+r.Y-2) (2*r.d+2) (2*r.X-4))
  | 6, 1 => .line 12 (.sloped (3*r.d-r.Y+4) (2*r.d+2) (-2*r.X+16))
  | 6, 2 => .line 12 (.sloped (r.X-4) (r.d+1) (-4*r.d+2*r.Y-6))
  | 6, 3 => .line 12 (.sloped (2*r.d-r.X+6) (r.d+1) (4*r.d-2*r.Y+8))
  | 9, 0 => .line 12 (.sloped (-r.d+r.Y+1) (3*r.d+4) (3*r.d+3*r.X+6))
  | 9, 1 => .line 12 (.sloped (3*r.d-r.Y+3) (3*r.d+4) (-3*r.d-3*r.X+18))
  | 9, 2 => .line 12 (.sloped (r.d+r.X) (2*r.d+3) (-4*r.d+4*r.Y))
  | 9, 3 => .line 12 (.sloped (2*r.d-r.X+4) (2*r.d+3) (4*r.d-4*r.Y+8))
  | 10, 0 => .boundary (0 ≤ (r.d+r.X-r.Y))
  | 10, 1 => .boundary (0 ≤ (-r.d-r.X+r.Y))
  | 10, 2 => .boundary (0 ≤ (-r.d+r.Y-1))
  | 10, 3 => .boundary (0 ≤ (r.d-r.Y+2))
  | 11, 0 => .boundary (0 ≤ (r.X-r.Y-3))
  | 11, 1 => .boundary (0 ≤ (-r.X+r.Y+3))
  | 11, 2 => .boundary (0 ≤ (-2*r.d+r.Y-3))
  | 11, 3 => .boundary (0 ≤ (2*r.d-r.Y+4))
  | 12, 0 => .boundary (0 ≤ (-r.d+r.X-4))
  | 12, 1 => .boundary (0 ≤ (r.d-r.X+4))
  | 12, 2 => .boundary (0 ≤ (-r.d+r.Y-3))
  | 12, 3 => .boundary (0 ≤ (2*r.d-r.Y+2))
  | 13, 0 => .boundary (0 ≤ (-r.d+r.Y-1))
  | 13, 1 => .boundary (0 ≤ (r.d-r.Y+1))
  | 13, 2 => .boundary (0 ≤ (r.d+r.X-r.Y))
  | 13, 3 => .boundary (0 ≤ (-r.X+r.Y))
  | 14, 0 => .boundary (0 ≤ (-2*r.d+r.Y-4))
  | 14, 1 => .boundary (0 ≤ (2*r.d-r.Y+4))
  | 14, 2 => .boundary (0 ≤ (r.d+r.X-r.Y-3))
  | 14, 3 => .boundary (0 ≤ (-r.X+r.Y+3))
  | 15, 0 => .boundary (0 ≤ (2*r.d+r.X-r.Y-2))
  | 15, 1 => .boundary (0 ≤ (r.d-r.X+r.Y+1))
  | 15, 2 => .boundary (0 ≤ (-r.d+r.Y-2))
  | 15, 3 => .boundary (0 ≤ (2*r.d-r.Y+3))
  | 15, 4 => .boundary (0 ≤ (r.X-3))
  | 15, 5 => .boundary (0 ≤ (2*r.d-r.X+5))
  | _, _ => .boundary True

def arity : ℕ → ℕ
  | 0 => 4
  | 1 => 4
  | 2 => 4
  | 3 => 4
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | 9 => 4
  | 10 => 4
  | 11 => 4
  | 12 => 4
  | 13 => 4
  | 14 => 4
  | 15 => 6
  | _ => 0

def contains (r : Register) (i : ℕ) : Prop := ∀ j : Fin (arity i), (test r i j.val).holds

private abbrev Pos (r : Register) (i : ℕ) := ∀ j : Fin (arity i), ∀ k : Fin 26, (test r i j.val).bound true k.val
private abbrev Neg (r : Register) (i j : ℕ) := ∀ k : Fin 26, (test r i j).bound false k.val

local macro "lin_close" "[" xs:term,* "]" : tactic => do
  let vs := xs.getElems
  let ns := vs.mapIdx fun i _ => mkIdent (Name.mkSimple s!"bound{i}")
  let hs ← (ns.zip vs).mapM fun (n,v) => `(tactic| have $n := $v)
  `(tactic| ($[$hs:tactic]*; clear * - $ns:ident*; norm_num [test,Test.bound,fact] at $ns:ident*; all_goals omega))

private theorem valid0 (r : Register) (h : Frame r) (j : Fin 12) (k : Fin 26) :
    (test r 0 j.val).valid k.val := by
  have bound := k.isLt
  obtain ⟨h0,h1,h2⟩ := h
  fin_cases j <;> norm_num [test,Test.valid,Line.valid] <;> omega

private theorem valid1 (r : Register) (h : Frame r) (j : Fin 12) (k : Fin 26) :
    (test r 1 j.val).valid k.val := by
  have bound := k.isLt
  obtain ⟨h0,h1,h2⟩ := h
  fin_cases j <;> norm_num [test,Test.valid,Line.valid] <;> omega

private theorem valid2 (r : Register) (h : Frame r) (j : Fin 12) (k : Fin 26) :
    (test r 2 j.val).valid k.val := by
  have bound := k.isLt
  obtain ⟨h0,h1,h2⟩ := h
  fin_cases j <;> norm_num [test,Test.valid,Line.valid] <;> omega

private theorem valid3 (r : Register) (h : Frame r) (j : Fin 12) (k : Fin 26) :
    (test r 3 j.val).valid k.val := by
  have bound := k.isLt
  obtain ⟨h0,h1,h2⟩ := h
  fin_cases j <;> norm_num [test,Test.valid,Line.valid] <;> omega

private theorem valid4 (r : Register) (h : Frame r) (j : Fin 12) (k : Fin 26) :
    (test r 4 j.val).valid k.val := by
  have bound := k.isLt
  obtain ⟨h0,h1,h2⟩ := h
  fin_cases j <;> norm_num [test,Test.valid,Line.valid] <;> omega

private theorem valid5 (r : Register) (h : Frame r) (j : Fin 12) (k : Fin 26) :
    (test r 5 j.val).valid k.val := by
  have bound := k.isLt
  obtain ⟨h0,h1,h2⟩ := h
  fin_cases j <;> norm_num [test,Test.valid,Line.valid] <;> omega

private theorem valid6 (r : Register) (h : Frame r) (j : Fin 12) (k : Fin 26) :
    (test r 6 j.val).valid k.val := by
  have bound := k.isLt
  obtain ⟨h0,h1,h2⟩ := h
  fin_cases j <;> norm_num [test,Test.valid,Line.valid] <;> omega

private theorem valid7 (r : Register) (h : Frame r) (j : Fin 12) (k : Fin 26) :
    (test r 7 j.val).valid k.val := by
  have bound := k.isLt
  obtain ⟨h0,h1,h2⟩ := h
  fin_cases j <;> norm_num [test,Test.valid,Line.valid]

private theorem valid8 (r : Register) (h : Frame r) (j : Fin 12) (k : Fin 26) :
    (test r 8 j.val).valid k.val := by
  have bound := k.isLt
  obtain ⟨h0,h1,h2⟩ := h
  fin_cases j <;> norm_num [test,Test.valid,Line.valid]

private theorem valid9 (r : Register) (h : Frame r) (j : Fin 12) (k : Fin 26) :
    (test r 9 j.val).valid k.val := by
  have bound := k.isLt
  obtain ⟨h0,h1,h2⟩ := h
  fin_cases j <;> norm_num [test,Test.valid,Line.valid] <;> omega

private theorem valid10 (r : Register) (h : Frame r) (j : Fin 12) (k : Fin 26) :
    (test r 10 j.val).valid k.val := by
  have bound := k.isLt
  obtain ⟨h0,h1,h2⟩ := h
  fin_cases j <;> norm_num [test,Test.valid,Line.valid]

private theorem valid11 (r : Register) (h : Frame r) (j : Fin 12) (k : Fin 26) :
    (test r 11 j.val).valid k.val := by
  have bound := k.isLt
  obtain ⟨h0,h1,h2⟩ := h
  fin_cases j <;> norm_num [test,Test.valid,Line.valid]

private theorem valid12 (r : Register) (h : Frame r) (j : Fin 12) (k : Fin 26) :
    (test r 12 j.val).valid k.val := by
  have bound := k.isLt
  obtain ⟨h0,h1,h2⟩ := h
  fin_cases j <;> norm_num [test,Test.valid,Line.valid]

private theorem valid13 (r : Register) (h : Frame r) (j : Fin 12) (k : Fin 26) :
    (test r 13 j.val).valid k.val := by
  have bound := k.isLt
  obtain ⟨h0,h1,h2⟩ := h
  fin_cases j <;> norm_num [test,Test.valid,Line.valid]

private theorem valid14 (r : Register) (h : Frame r) (j : Fin 12) (k : Fin 26) :
    (test r 14 j.val).valid k.val := by
  have bound := k.isLt
  obtain ⟨h0,h1,h2⟩ := h
  fin_cases j <;> norm_num [test,Test.valid,Line.valid]

private theorem valid15 (r : Register) (h : Frame r) (j : Fin 12) (k : Fin 26) :
    (test r 15 j.val).valid k.val := by
  have bound := k.isLt
  obtain ⟨h0,h1,h2⟩ := h
  fin_cases j <;> norm_num [test,Test.valid,Line.valid]

private theorem ok (r : Register) (h : Frame r) (i : Fin 16) (j : Fin 12) (k : Fin 26) :
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
  · exact valid10 r h j k
  · exact valid11 r h j k
  · exact valid12 r h j k
  · exact valid13 r h j k
  · exact valid14 r h j k
  · exact valid15 r h j k

private theorem positive (r : Register) (h : Frame r) (i : Fin 16) (hit : contains r i.val) : Pos r i.val := by
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

private abbrev Outside10 (r : Register) := Neg r 10 0 ∨ Neg r 10 1 ∨ Neg r 10 2 ∨ Neg r 10 3
private theorem outside10 {r : Register} (h : Frame r) (miss : ¬contains r 10) : Outside10 r := by
  unfold contains at miss
  push Not at miss
  obtain ⟨j,hj⟩ := miss
  have N : Neg r 10 j.val := fun k =>
    Test.bounds _ false _ (ok r h 10 ⟨j.val,by have hh := j.isLt; change j.val < 4 at hh; omega⟩ k) hj
  change Fin 4 at j
  fin_cases j <;> unfold Outside10 <;> tauto

private abbrev Outside11 (r : Register) := Neg r 11 0 ∨ Neg r 11 1 ∨ Neg r 11 2 ∨ Neg r 11 3
private theorem outside11 {r : Register} (h : Frame r) (miss : ¬contains r 11) : Outside11 r := by
  unfold contains at miss
  push Not at miss
  obtain ⟨j,hj⟩ := miss
  have N : Neg r 11 j.val := fun k =>
    Test.bounds _ false _ (ok r h 11 ⟨j.val,by have hh := j.isLt; change j.val < 4 at hh; omega⟩ k) hj
  change Fin 4 at j
  fin_cases j <;> unfold Outside11 <;> tauto

private abbrev Outside12 (r : Register) := Neg r 12 0 ∨ Neg r 12 1 ∨ Neg r 12 2 ∨ Neg r 12 3
private theorem outside12 {r : Register} (h : Frame r) (miss : ¬contains r 12) : Outside12 r := by
  unfold contains at miss
  push Not at miss
  obtain ⟨j,hj⟩ := miss
  have N : Neg r 12 j.val := fun k =>
    Test.bounds _ false _ (ok r h 12 ⟨j.val,by have hh := j.isLt; change j.val < 4 at hh; omega⟩ k) hj
  change Fin 4 at j
  fin_cases j <;> unfold Outside12 <;> tauto

private abbrev Outside13 (r : Register) := Neg r 13 0 ∨ Neg r 13 1 ∨ Neg r 13 2 ∨ Neg r 13 3
private theorem outside13 {r : Register} (h : Frame r) (miss : ¬contains r 13) : Outside13 r := by
  unfold contains at miss
  push Not at miss
  obtain ⟨j,hj⟩ := miss
  have N : Neg r 13 j.val := fun k =>
    Test.bounds _ false _ (ok r h 13 ⟨j.val,by have hh := j.isLt; change j.val < 4 at hh; omega⟩ k) hj
  change Fin 4 at j
  fin_cases j <;> unfold Outside13 <;> tauto

private abbrev Outside14 (r : Register) := Neg r 14 0 ∨ Neg r 14 1 ∨ Neg r 14 2 ∨ Neg r 14 3
private theorem outside14 {r : Register} (h : Frame r) (miss : ¬contains r 14) : Outside14 r := by
  unfold contains at miss
  push Not at miss
  obtain ⟨j,hj⟩ := miss
  have N : Neg r 14 j.val := fun k =>
    Test.bounds _ false _ (ok r h 14 ⟨j.val,by have hh := j.isLt; change j.val < 4 at hh; omega⟩ k) hj
  change Fin 4 at j
  fin_cases j <;> unfold Outside14 <;> tauto

private abbrev Outside15 (r : Register) := Neg r 15 0 ∨ Neg r 15 1 ∨ Neg r 15 2 ∨ Neg r 15 3 ∨ Neg r 15 4 ∨ Neg r 15 5
private theorem outside15 {r : Register} (h : Frame r) (miss : ¬contains r 15) : Outside15 r := by
  unfold contains at miss
  push Not at miss
  obtain ⟨j,hj⟩ := miss
  have N : Neg r 15 j.val := fun k =>
    Test.bounds _ false _ (ok r h 15 ⟨j.val,by have hh := j.isLt; change j.val < 6 at hh; omega⟩ k) hj
  change Fin 6 at j
  fin_cases j <;> unfold Outside15 <;> tauto

private theorem cell0 {r : Register} (h : Frame r) (n_1_0 : Neg r 1 0) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f1, h.f2, n_1_0 0, n_1_0 12, n_1_0 13, n_1_0 14, n_1_0 15, p ⟨0,by decide⟩ 11, p ⟨0,by decide⟩ 13, p ⟨0,by decide⟩ 14, p ⟨0,by decide⟩ 15, p ⟨0,by decide⟩ 16, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 11, p ⟨3,by decide⟩ 7]

private theorem cell1 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_2_0 : Neg r 2 0) (n_4_0 : Neg r 4 0) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f1, h.f2, n_1_1 13, n_1_1 14, n_1_1 16, n_2_0 17, n_4_0 0, n_4_0 16, n_4_0 17, n_4_0 19, p ⟨0,by decide⟩ 11, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 11, p ⟨3,by decide⟩ 7]

private theorem cell2 {r : Register} (h : Frame r) (n_2_0 : Neg r 2 0) (n_4_1 : Neg r 4 1) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f1, h.f2, n_2_0 15, n_2_0 17, n_4_1 0, n_4_1 11, n_4_1 13, p ⟨1,by decide⟩ 8, p ⟨2,by decide⟩ 11, p ⟨3,by decide⟩ 0, p ⟨3,by decide⟩ 7]

private theorem cell3 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_2_0 : Neg r 2 0) (n_4_2 : Neg r 4 2) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f1, h.f2, n_1_1 16, n_2_0 15, n_4_2 0, n_4_2 15, p ⟨0,by decide⟩ 11, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 11]

private theorem cell4 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_2_0 : Neg r 2 0) (n_4_3 : Neg r 4 3) (n_5_0 : Neg r 5 0) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f1, h.f2, n_1_1 0, n_1_1 13, n_1_1 14, n_1_1 16, n_2_0 17, n_4_3 13, n_5_0 0, n_5_0 15, n_5_0 16, p ⟨2,by decide⟩ 11, p ⟨3,by decide⟩ 7]

private theorem cell5 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_2_0 : Neg r 2 0) (n_4_3 : Neg r 4 3) (n_5_1 : Neg r 5 1) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f1, h.f2, n_1_1 0, n_1_1 16, n_2_0 17, n_4_3 13, n_5_1 14, p ⟨1,by decide⟩ 8, p ⟨2,by decide⟩ 11, p ⟨3,by decide⟩ 0, p ⟨3,by decide⟩ 7]

private theorem cell6 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_2_0 : Neg r 2 0) (n_4_3 : Neg r 4 3) (n_12_0 : Neg r 12 0) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f1, h.f2, n_1_1 16, n_2_0 15, n_4_3 0, n_4_3 13, n_12_0 0, p ⟨0,by decide⟩ 10, p ⟨0,by decide⟩ 12, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 11]

private theorem cell7 {r : Register} (h : Frame r) (n_2_0 : Neg r 2 0) (n_5_2 : Neg r 5 2) (n_12_1 : Neg r 12 1) : False := by
  lin_close [h.f0, h.f1, h.f2, n_2_0 17, n_5_2 0, n_5_2 15, n_12_1 0]

private theorem cell8 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_4_3 : Neg r 4 3) (n_12_2 : Neg r 12 2) (p : Pos r 0) : False := by
  lin_close [h.f0, n_1_1 15, n_1_1 16, n_4_3 0, n_4_3 13, n_12_2 0, p ⟨0,by decide⟩ 12, p ⟨2,by decide⟩ 11, p ⟨3,by decide⟩ 11, h.f1, h.f2]

private theorem cell9 {r : Register} (h : Frame r) (n_2_0 : Neg r 2 0) (n_5_2 : Neg r 5 2) (n_12_3 : Neg r 12 3) (p : Pos r 0) : False := by
  lin_close [h.f0, n_2_0 16, n_2_0 17, n_5_2 0, n_5_2 15, n_12_3 0, p ⟨1,by decide⟩ 13, h.f1, h.f2]

private theorem cell10 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_2_0 : Neg r 2 0) (n_5_3 : Neg r 5 3) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f1, h.f2, n_1_1 13, n_1_1 15, n_2_0 17, n_5_3 0, n_5_3 13, n_5_3 14, p ⟨1,by decide⟩ 8, p ⟨3,by decide⟩ 0, p ⟨3,by decide⟩ 7, p ⟨3,by decide⟩ 9, p ⟨3,by decide⟩ 11]

private theorem cell11 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_3_0 : Neg r 3 0) (p : Pos r 0) : False := by
  lin_close [h.f0, n_1_2 16, n_3_0 0, n_3_0 14, n_3_0 15, n_3_0 16, p ⟨0,by decide⟩ 11, p ⟨0,by decide⟩ 13, p ⟨0,by decide⟩ 14, p ⟨0,by decide⟩ 15, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 11, h.f1, h.f2]

private theorem cell12 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_2_0 : Neg r 2 0) (n_3_1 : Neg r 3 1) (n_4_0 : Neg r 4 0) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f1, h.f2, n_1_2 17, n_2_0 17, n_3_1 12, n_3_1 13, n_3_1 14, n_4_0 0, n_4_0 15, n_4_0 16, n_4_0 17, p ⟨0,by decide⟩ 11, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 11, p ⟨3,by decide⟩ 7]

private theorem cell13 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_2_0 : Neg r 2 0) (n_4_1 : Neg r 4 1) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f1, h.f2, n_1_2 0, n_2_0 15, n_2_0 17, n_4_1 0, n_4_1 11, n_4_1 13, p ⟨1,by decide⟩ 9, p ⟨2,by decide⟩ 11, p ⟨3,by decide⟩ 7]

private theorem cell14 {r : Register} (h : Frame r) (n_2_0 : Neg r 2 0) (n_4_2 : Neg r 4 2) (p : Pos r 0) : False := by
  lin_close [h.f0, n_2_0 15, n_4_2 0, n_4_2 15, p ⟨0,by decide⟩ 10, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 11, h.f1, h.f2]

private theorem cell15 {r : Register} (h : Frame r) (n_4_3 : Neg r 4 3) (n_15_0 : Neg r 15 0) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, n_4_3 0, n_15_0 0, p ⟨1,by decide⟩ 6, p ⟨1,by decide⟩ 12, p ⟨1,by decide⟩ 13, p ⟨2,by decide⟩ 13, p ⟨2,by decide⟩ 15, p ⟨3,by decide⟩ 0, h.f1]

private theorem cell16 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_2_0 : Neg r 2 0) (n_3_1 : Neg r 3 1) (n_15_1 : Neg r 15 1) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f1, h.f2, n_1_2 0, n_1_2 17, n_2_0 17, n_3_1 12, n_3_1 13, n_15_1 0, p ⟨0,by decide⟩ 7, p ⟨0,by decide⟩ 13, p ⟨0,by decide⟩ 14, p ⟨1,by decide⟩ 9, p ⟨2,by decide⟩ 0, p ⟨3,by decide⟩ 7]

private theorem cell17 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_3_1 : Neg r 3 1) (n_4_3 : Neg r 4 3) (n_15_2 : Neg r 15 2) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, n_1_2 15, n_3_1 13, n_3_1 14, n_4_3 0, n_4_3 13, n_15_2 0, p ⟨0,by decide⟩ 12, p ⟨2,by decide⟩ 11, h.f1]

private theorem cell18 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_2_0 : Neg r 2 0) (n_15_3 : Neg r 15 3) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f1, h.f2, n_1_2 0, n_2_0 17, n_15_3 0, p ⟨1,by decide⟩ 9, p ⟨3,by decide⟩ 7]

private theorem cell19 {r : Register} (h : Frame r) (n_3_1 : Neg r 3 1) (n_4_3 : Neg r 4 3) (n_15_4 : Neg r 15 4) (p : Pos r 0) : False := by
  lin_close [h.f0, n_3_1 14, n_4_3 13, n_15_4 0, p ⟨0,by decide⟩ 9, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 11, h.f1, h.f2]

private theorem cell20 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_2_0 : Neg r 2 0) (n_15_5 : Neg r 15 5) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f1, h.f2, n_1_2 0, n_1_2 17, n_2_0 17, n_15_5 0, p ⟨1,by decide⟩ 9, p ⟨3,by decide⟩ 7]

private theorem cell21 {r : Register} (h : Frame r) (n_2_0 : Neg r 2 0) (n_3_2 : Neg r 3 2) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, n_2_0 16, n_3_2 0, n_3_2 13, n_3_2 15, n_3_2 17, p ⟨0,by decide⟩ 11, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 11, p ⟨2,by decide⟩ 13, p ⟨2,by decide⟩ 15, h.f1]

private theorem cell22 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_2_0 : Neg r 2 0) (n_3_3 : Neg r 3 3) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f1, h.f2, n_1_2 0, n_1_2 13, n_1_2 15, n_1_2 17, n_2_0 17, n_3_3 0, n_3_3 11, n_3_3 13, n_3_3 14, p ⟨0,by decide⟩ 12, p ⟨1,by decide⟩ 9, p ⟨3,by decide⟩ 7]

private theorem cell23 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_2_0 : Neg r 2 0) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f1, h.f2, n_1_3 0, n_1_3 11, n_1_3 13, n_1_3 14, n_2_0 17, p ⟨0,by decide⟩ 14, p ⟨0,by decide⟩ 16, p ⟨1,by decide⟩ 8, p ⟨3,by decide⟩ 0, p ⟨3,by decide⟩ 7, p ⟨3,by decide⟩ 9, p ⟨3,by decide⟩ 11]

private theorem cell24 {r : Register} (h : Frame r) (n_2_1 : Neg r 2 1) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, n_2_1 0, n_2_1 13, p ⟨1,by decide⟩ 8, p ⟨2,by decide⟩ 13, p ⟨3,by decide⟩ 0, h.f1]

private theorem cell25 {r : Register} (h : Frame r) (n_2_2 : Neg r 2 2) (p : Pos r 0) : False := by
  lin_close [h.f0, n_2_2 0, n_2_2 14, p ⟨0,by decide⟩ 10, p ⟨1,by decide⟩ 12, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 11, h.f1, h.f2]

private theorem cell26 {r : Register} (h : Frame r) (n_1_0 : Neg r 1 0) (n_2_3 : Neg r 2 3) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f1, h.f2, n_1_0 0, n_1_0 12, n_1_0 13, n_1_0 14, n_1_0 15, n_2_3 0, n_2_3 17, p ⟨0,by decide⟩ 11, p ⟨0,by decide⟩ 13, p ⟨0,by decide⟩ 14, p ⟨0,by decide⟩ 15, p ⟨0,by decide⟩ 16, p ⟨3,by decide⟩ 7]

private theorem cell27 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_2_3 : Neg r 2 3) (n_5_0 : Neg r 5 0) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, n_1_1 13, n_1_1 14, n_1_1 15, n_2_3 17, n_5_0 0, n_5_0 14, n_5_0 15, n_5_0 16, p ⟨0,by decide⟩ 11, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 15, p ⟨3,by decide⟩ 7, h.f1]

private theorem cell28 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_2_3 : Neg r 2 3) (n_3_0 : Neg r 3 0) (n_5_0 : Neg r 5 0) (p : Pos r 0) : False := by
  lin_close [h.f0, n_1_2 15, n_2_3 0, n_2_3 17, n_3_0 0, n_3_0 14, n_3_0 15, n_3_0 16, n_5_0 16, p ⟨0,by decide⟩ 11, p ⟨0,by decide⟩ 13, p ⟨0,by decide⟩ 14, p ⟨0,by decide⟩ 15, p ⟨3,by decide⟩ 9, h.f1, h.f2]

private theorem cell29 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_3_1 : Neg r 3 1) (n_15_0 : Neg r 15 0) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, n_1_2 0, n_3_1 0, n_15_0 0, p ⟨1,by decide⟩ 6, p ⟨1,by decide⟩ 12, p ⟨1,by decide⟩ 13, p ⟨2,by decide⟩ 9, p ⟨2,by decide⟩ 11, p ⟨2,by decide⟩ 13, p ⟨2,by decide⟩ 15, h.f1]

private theorem cell30 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_3_1 : Neg r 3 1) (n_5_0 : Neg r 5 0) (n_15_1 : Neg r 15 1) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, n_1_2 15, n_3_1 13, n_5_0 0, n_5_0 16, n_15_1 0, p ⟨0,by decide⟩ 7, p ⟨0,by decide⟩ 13, p ⟨0,by decide⟩ 14, p ⟨2,by decide⟩ 0, p ⟨3,by decide⟩ 7, h.f1]

private theorem cell31 {r : Register} (h : Frame r) (n_2_3 : Neg r 2 3) (n_3_1 : Neg r 3 1) (n_15_2 : Neg r 15 2) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, n_2_3 0, n_2_3 15, n_2_3 17, n_3_1 13, n_3_1 14, n_15_2 0, p ⟨0,by decide⟩ 11, h.f1]

private theorem cell32 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_5_0 : Neg r 5 0) (n_15_3 : Neg r 15 3) (p : Pos r 0) : False := by
  lin_close [h.f0, n_1_2 0, n_5_0 16, n_15_3 0, p ⟨1,by decide⟩ 9, p ⟨3,by decide⟩ 7, h.f1, h.f2]

private theorem cell33 {r : Register} (h : Frame r) (n_2_3 : Neg r 2 3) (n_3_1 : Neg r 3 1) (n_15_4 : Neg r 15 4) (p : Pos r 0) : False := by
  lin_close [h.f0, n_2_3 0, n_2_3 15, n_2_3 17, n_3_1 14, n_15_4 0, p ⟨0,by decide⟩ 11, h.f1, h.f2]

private theorem cell34 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_5_0 : Neg r 5 0) (n_15_5 : Neg r 15 5) (p : Pos r 0) : False := by
  lin_close [h.f0, n_1_2 15, n_5_0 0, n_5_0 16, n_15_5 0, p ⟨3,by decide⟩ 7, h.f1, h.f2]

private theorem cell35 {r : Register} (h : Frame r) (n_2_3 : Neg r 2 3) (n_3_2 : Neg r 3 2) (n_5_0 : Neg r 5 0) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, n_2_3 0, n_2_3 17, n_3_2 0, n_3_2 15, n_3_2 16, n_5_0 15, p ⟨0,by decide⟩ 11, p ⟨2,by decide⟩ 15, h.f1]

private theorem cell36 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_2_3 : Neg r 2 3) (n_3_3 : Neg r 3 3) (n_5_0 : Neg r 5 0) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, n_1_2 15, n_2_3 17, n_3_3 0, n_3_3 12, n_3_3 13, n_3_3 14, n_5_0 0, n_5_0 16, p ⟨0,by decide⟩ 12, p ⟨0,by decide⟩ 13, p ⟨0,by decide⟩ 14, p ⟨3,by decide⟩ 7, h.f1]

private theorem cell37 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (n_5_0 : Neg r 5 0) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f1, h.f2, n_1_3 0, n_1_3 11, n_1_3 13, n_1_3 14, n_5_0 0, n_5_0 16, p ⟨0,by decide⟩ 14, p ⟨0,by decide⟩ 16, p ⟨3,by decide⟩ 7, p ⟨3,by decide⟩ 9, p ⟨3,by decide⟩ 11]

private theorem cell38 {r : Register} (h : Frame r) (n_2_3 : Neg r 2 3) (n_5_1 : Neg r 5 1) (n_6_0 : Neg r 6 0) (p : Pos r 0) : False := by
  lin_close [h.f0, n_2_3 16, n_5_1 0, n_5_1 12, n_5_1 13, n_5_1 14, n_5_1 15, n_6_0 14, n_6_0 17, p ⟨1,by decide⟩ 8, p ⟨1,by decide⟩ 11, p ⟨1,by decide⟩ 12, p ⟨3,by decide⟩ 0, p ⟨3,by decide⟩ 7, h.f1, h.f2]

private theorem cell39 {r : Register} (h : Frame r) (n_2_3 : Neg r 2 3) (n_3_0 : Neg r 3 0) (n_5_2 : Neg r 5 2) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, n_2_3 0, n_2_3 17, n_3_0 0, n_3_0 14, n_3_0 15, n_5_2 15, p ⟨0,by decide⟩ 11, p ⟨0,by decide⟩ 13, p ⟨0,by decide⟩ 14, h.f1]

private theorem cell40 {r : Register} (h : Frame r) (n_2_3 : Neg r 2 3) (n_15_0 : Neg r 15 0) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, n_2_3 0, n_15_0 0, p ⟨1,by decide⟩ 5, p ⟨1,by decide⟩ 12, p ⟨1,by decide⟩ 13, p ⟨2,by decide⟩ 11, p ⟨2,by decide⟩ 13, p ⟨2,by decide⟩ 15, p ⟨3,by decide⟩ 0, h.f1]

private theorem cell41 {r : Register} (h : Frame r) (n_5_2 : Neg r 5 2) (n_15_1 : Neg r 15 1) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f1, n_5_2 0, n_5_2 11, n_5_2 13, n_5_2 15, n_5_2 16, n_15_1 0, p ⟨0,by decide⟩ 7, p ⟨0,by decide⟩ 13, p ⟨0,by decide⟩ 14, p ⟨1,by decide⟩ 10, p ⟨2,by decide⟩ 0, h.f2]

private theorem cell42 {r : Register} (h : Frame r) (n_5_2 : Neg r 5 2) (n_15_3 : Neg r 15 3) (p : Pos r 0) : False := by
  lin_close [h.f0, n_5_2 0, n_5_2 16, n_15_3 0, p ⟨1,by decide⟩ 10, p ⟨1,by decide⟩ 12, h.f1, h.f2]

private theorem cell43 {r : Register} (h : Frame r) (n_5_2 : Neg r 5 2) (n_15_5 : Neg r 15 5) (p : Pos r 0) : False := by
  lin_close [h.f0, n_5_2 0, n_5_2 16, n_15_5 0, p ⟨1,by decide⟩ 10, h.f1, h.f2]

private theorem cell44 {r : Register} (h : Frame r) (n_2_3 : Neg r 2 3) (n_3_2 : Neg r 3 2) (n_6_0 : Neg r 6 0) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, n_2_3 0, n_2_3 13, n_2_3 17, n_3_2 0, n_3_2 15, n_3_2 17, n_3_2 18, n_6_0 15, p ⟨0,by decide⟩ 11, p ⟨2,by decide⟩ 15, h.f1]

private theorem cell45 {r : Register} (h : Frame r) (n_2_3 : Neg r 2 3) (n_3_3 : Neg r 3 3) (n_5_2 : Neg r 5 2) (p : Pos r 0) : False := by
  lin_close [h.f0, n_2_3 17, n_3_3 0, n_3_3 12, n_3_3 13, n_3_3 14, n_5_2 0, n_5_2 16, p ⟨0,by decide⟩ 12, p ⟨0,by decide⟩ 13, p ⟨0,by decide⟩ 14, p ⟨1,by decide⟩ 10, h.f1, h.f2]

private theorem cell46 {r : Register} (h : Frame r) (n_5_3 : Neg r 5 3) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f1, h.f2, n_5_3 0, n_5_3 11, n_5_3 13, n_5_3 15, n_5_3 16, p ⟨0,by decide⟩ 14, p ⟨0,by decide⟩ 16, p ⟨1,by decide⟩ 8, p ⟨3,by decide⟩ 0, p ⟨3,by decide⟩ 7, p ⟨3,by decide⟩ 9, p ⟨3,by decide⟩ 11]

private theorem cell47 {r : Register} (h : Frame r) (n_2_3 : Neg r 2 3) (n_6_1 : Neg r 6 1) (p : Pos r 0) : False := by
  lin_close [h.f0, n_2_3 15, n_6_1 0, n_6_1 14, p ⟨1,by decide⟩ 8, p ⟨3,by decide⟩ 0, h.f1, h.f2]

private theorem cell48 {r : Register} (h : Frame r) (n_2_3 : Neg r 2 3) (n_6_2 : Neg r 6 2) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, n_2_3 0, n_2_3 13, n_2_3 17, n_6_2 0, n_6_2 11, n_6_2 13, n_6_2 14, p ⟨0,by decide⟩ 11, p ⟨1,by decide⟩ 11, p ⟨2,by decide⟩ 15, h.f1]

private theorem cell49 {r : Register} (h : Frame r) (n_1_0 : Neg r 1 0) (n_6_3 : Neg r 6 3) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, n_1_0 0, n_1_0 14, n_1_0 15, n_6_3 0, n_6_3 18, p ⟨0,by decide⟩ 13, p ⟨0,by decide⟩ 15, p ⟨0,by decide⟩ 16, p ⟨3,by decide⟩ 7, h.f1]

private theorem cell50 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_5_0 : Neg r 5 0) (n_6_3 : Neg r 6 3) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, n_1_1 13, n_1_1 14, n_5_0 0, n_5_0 16, n_6_3 0, n_6_3 15, n_6_3 18, p ⟨0,by decide⟩ 13, p ⟨3,by decide⟩ 7, h.f1]

private theorem cell51 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_5_0 : Neg r 5 0) (n_6_3 : Neg r 6 3) (p : Pos r 0) : False := by
  lin_close [h.f0, h.f2, n_1_2 13, n_1_2 15, n_5_0 0, n_5_0 16, n_6_3 0, n_6_3 17, n_6_3 18, p ⟨0,by decide⟩ 13, p ⟨3,by decide⟩ 7, h.f1]

private theorem cell52 {r : Register} (h : Frame r) (n_5_1 : Neg r 5 1) (n_6_3 : Neg r 6 3) (p : Pos r 0) : False := by
  lin_close [h.f0, n_5_1 0, n_5_1 12, n_5_1 13, n_5_1 14, n_6_3 18, p ⟨1,by decide⟩ 8, p ⟨1,by decide⟩ 10, p ⟨1,by decide⟩ 11, p ⟨1,by decide⟩ 12, p ⟨3,by decide⟩ 0, p ⟨3,by decide⟩ 7, h.f1, h.f2]

private theorem cell53 {r : Register} (h : Frame r) (n_5_2 : Neg r 5 2) (n_6_3 : Neg r 6 3) (p : Pos r 0) : False := by
  lin_close [h.f0, n_5_2 0, n_5_2 14, n_5_2 15, n_5_2 16, n_6_3 0, n_6_3 18, p ⟨0,by decide⟩ 13, p ⟨1,by decide⟩ 10, p ⟨1,by decide⟩ 11, h.f1, h.f2]

private theorem cell54 {r : Register} (h : Frame r) (n_1_0 : Neg r 1 0) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, n_1_0 0, n_1_0 14, p ⟨0,by decide⟩ 11, p ⟨2,by decide⟩ 0, p ⟨3,by decide⟩ 9, h.f1]

private theorem cell55 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_4_0 : Neg r 4 0) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f1, h.f2, n_1_1 14, n_1_1 16, n_4_0 0, n_4_0 16, n_4_0 17, p ⟨0,by decide⟩ 11, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 11, p ⟨3,by decide⟩ 9]

private theorem cell56 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_2_0 : Neg r 2 0) (n_4_1 : Neg r 4 1) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f1, h.f2, n_1_1 16, n_2_0 0, n_2_0 14, n_2_0 15, n_2_0 17, n_4_1 11, n_4_1 13, n_4_1 14, p ⟨0,by decide⟩ 11, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 11, p ⟨3,by decide⟩ 7]

private theorem cell57 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_2_0 : Neg r 2 0) (n_4_2 : Neg r 4 2) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f1, h.f2, n_1_1 16, n_2_0 15, n_4_2 0, n_4_2 15, p ⟨0,by decide⟩ 11, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 11, p ⟨2,by decide⟩ 13]

private theorem cell58 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_2_0 : Neg r 2 0) (n_4_3 : Neg r 4 3) (n_15_0 : Neg r 15 0) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f1, h.f2, n_1_1 16, n_2_0 15, n_4_3 0, n_4_3 12, n_4_3 13, n_15_0 0, p ⟨0,by decide⟩ 12, p ⟨1,by decide⟩ 8, p ⟨1,by decide⟩ 9, p ⟨1,by decide⟩ 10, p ⟨1,by decide⟩ 11, p ⟨2,by decide⟩ 11, p ⟨3,by decide⟩ 0]

private theorem cell59 {r : Register} (h : Frame r) (n_2_0 : Neg r 2 0) (n_15_1 : Neg r 15 1) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, n_2_0 0, n_15_1 0, p ⟨0,by decide⟩ 9, p ⟨0,by decide⟩ 15, p ⟨0,by decide⟩ 16, p ⟨2,by decide⟩ 0, p ⟨3,by decide⟩ 7, p ⟨3,by decide⟩ 9, p ⟨3,by decide⟩ 11, h.f1]

private theorem cell60 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_4_3 : Neg r 4 3) (n_15_2 : Neg r 15 2) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f1, h.f2, n_1_1 16, n_4_3 0, n_15_2 0, p ⟨0,by decide⟩ 12, p ⟨2,by decide⟩ 11]

private theorem cell61 {r : Register} (h : Frame r) (n_2_0 : Neg r 2 0) (n_15_3 : Neg r 15 3) (p : Pos r 9) : False := by
  lin_close [h.f0, n_2_0 0, n_2_0 17, n_15_3 0, p ⟨3,by decide⟩ 7, h.f1, h.f2]

private theorem cell62 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_4_3 : Neg r 4 3) (n_15_4 : Neg r 15 4) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f1, h.f2, n_1_1 16, n_4_3 0, n_4_3 13, n_15_4 0, p ⟨0,by decide⟩ 12, p ⟨2,by decide⟩ 11]

private theorem cell63 {r : Register} (h : Frame r) (n_2_0 : Neg r 2 0) (n_15_5 : Neg r 15 5) (p : Pos r 9) : False := by
  lin_close [h.f0, n_2_0 0, n_2_0 17, n_15_5 0, p ⟨3,by decide⟩ 7, p ⟨3,by decide⟩ 11, h.f1, h.f2]

private theorem cell64 {r : Register} (h : Frame r) (n_2_1 : Neg r 2 1) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f1, h.f2, n_2_1 0, n_2_1 11, n_2_1 12, n_2_1 13, n_2_1 14, p ⟨1,by decide⟩ 8, p ⟨1,by decide⟩ 10, p ⟨1,by decide⟩ 11, p ⟨1,by decide⟩ 12, p ⟨1,by decide⟩ 13, p ⟨2,by decide⟩ 11, p ⟨3,by decide⟩ 0, p ⟨3,by decide⟩ 7]

private theorem cell65 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_2_2 : Neg r 2 2) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f1, h.f2, n_1_1 16, n_2_2 0, n_2_2 13, n_2_2 15, n_2_2 16, p ⟨0,by decide⟩ 11, p ⟨1,by decide⟩ 11, p ⟨1,by decide⟩ 13, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 11, p ⟨2,by decide⟩ 13, p ⟨2,by decide⟩ 15]

private theorem cell66 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_2_3 : Neg r 2 3) (n_5_0 : Neg r 5 0) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f1, h.f2, n_1_1 14, n_1_1 16, n_2_3 0, n_5_0 0, n_5_0 13, n_5_0 15, p ⟨0,by decide⟩ 12, p ⟨2,by decide⟩ 11, p ⟨3,by decide⟩ 7]

private theorem cell67 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_2_3 : Neg r 2 3) (n_5_1 : Neg r 5 1) (n_6_0 : Neg r 6 0) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f1, h.f2, n_1_1 16, n_2_3 0, n_2_3 15, n_5_1 13, n_5_1 14, n_5_1 15, n_6_0 0, n_6_0 14, n_6_0 15, n_6_0 16, p ⟨0,by decide⟩ 12, p ⟨2,by decide⟩ 11, p ⟨3,by decide⟩ 7]

private theorem cell68 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_2_3 : Neg r 2 3) (n_5_2 : Neg r 5 2) (n_6_0 : Neg r 6 0) (n_15_0 : Neg r 15 0) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f1, h.f2, n_1_1 16, n_2_3 0, n_2_3 15, n_5_2 0, n_6_0 14, n_6_0 15, n_15_0 0, p ⟨0,by decide⟩ 12, p ⟨1,by decide⟩ 9, p ⟨1,by decide⟩ 10, p ⟨1,by decide⟩ 11, p ⟨2,by decide⟩ 11]

private theorem cell69 {r : Register} (h : Frame r) (n_5_2 : Neg r 5 2) (n_15_1 : Neg r 15 1) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, n_5_2 0, n_15_1 0, p ⟨0,by decide⟩ 8, p ⟨0,by decide⟩ 15, p ⟨0,by decide⟩ 16, p ⟨2,by decide⟩ 0, p ⟨3,by decide⟩ 9, p ⟨3,by decide⟩ 11, h.f1]

private theorem cell70 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_2_3 : Neg r 2 3) (n_15_2 : Neg r 15 2) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f1, h.f2, n_1_1 0, n_1_1 16, n_2_3 0, n_15_2 0, p ⟨0,by decide⟩ 12, p ⟨0,by decide⟩ 15, p ⟨2,by decide⟩ 9, p ⟨2,by decide⟩ 11]

private theorem cell71 {r : Register} (h : Frame r) (n_2_3 : Neg r 2 3) (n_5_2 : Neg r 5 2) (n_6_0 : Neg r 6 0) (n_15_3 : Neg r 15 3) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, n_2_3 13, n_5_2 15, n_6_0 0, n_6_0 15, n_6_0 16, n_15_3 0, p ⟨3,by decide⟩ 7, h.f1]

private theorem cell72 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_2_3 : Neg r 2 3) (n_15_4 : Neg r 15 4) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f1, h.f2, n_1_1 16, n_2_3 0, n_2_3 15, n_15_4 0, p ⟨0,by decide⟩ 12, p ⟨2,by decide⟩ 11]

private theorem cell73 {r : Register} (h : Frame r) (n_5_2 : Neg r 5 2) (n_6_0 : Neg r 6 0) (n_15_5 : Neg r 15 5) (p : Pos r 9) : False := by
  lin_close [h.f0, n_5_2 15, n_6_0 0, n_6_0 16, n_15_5 0, p ⟨3,by decide⟩ 7, h.f1, h.f2]

private theorem cell74 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_5_3 : Neg r 5 3) (n_6_0 : Neg r 6 0) (p : Pos r 9) : False := by
  lin_close [h.f0, n_1_1 15, n_5_3 0, n_5_3 14, n_6_0 0, p ⟨3,by decide⟩ 7, h.f1, h.f2]

private theorem cell75 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_2_3 : Neg r 2 3) (n_6_1 : Neg r 6 1) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f1, h.f2, n_1_1 16, n_2_3 14, n_6_1 0, n_6_1 12, n_6_1 13, n_6_1 14, p ⟨1,by decide⟩ 8, p ⟨1,by decide⟩ 10, p ⟨1,by decide⟩ 11, p ⟨1,by decide⟩ 12, p ⟨2,by decide⟩ 11, p ⟨3,by decide⟩ 0, p ⟨3,by decide⟩ 7]

private theorem cell76 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_2_3 : Neg r 2 3) (n_6_2 : Neg r 6 2) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f1, h.f2, n_1_1 16, n_2_3 11, n_2_3 13, n_2_3 15, n_6_2 0, n_6_2 13, n_6_2 15, n_6_2 16, p ⟨0,by decide⟩ 9, p ⟨1,by decide⟩ 10, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 11]

private theorem cell77 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_6_3 : Neg r 6 3) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, n_1_1 15, n_6_3 0, n_6_3 11, n_6_3 13, n_6_3 15, p ⟨1,by decide⟩ 8, p ⟨3,by decide⟩ 0, p ⟨3,by decide⟩ 7, p ⟨3,by decide⟩ 9, p ⟨3,by decide⟩ 11, h.f1]

private theorem cell78 {r : Register} (h : Frame r) (n_3_0 : Neg r 3 0) (p : Pos r 9) : False := by
  lin_close [h.f0, n_3_0 0, n_3_0 16, p ⟨0,by decide⟩ 11, p ⟨2,by decide⟩ 0, p ⟨3,by decide⟩ 11, h.f1, h.f2]

private theorem cell79 {r : Register} (h : Frame r) (n_3_1 : Neg r 3 1) (n_4_0 : Neg r 4 0) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, n_3_1 12, n_3_1 15, n_4_0 0, n_4_0 14, n_4_0 15, n_4_0 16, n_4_0 17, p ⟨0,by decide⟩ 11, p ⟨0,by decide⟩ 14, p ⟨0,by decide⟩ 15, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 11, p ⟨3,by decide⟩ 9, h.f1]

private theorem cell80 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_2_0 : Neg r 2 0) (n_4_1 : Neg r 4 1) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, n_1_2 0, n_1_2 19, n_2_0 14, n_2_0 15, n_2_0 16, n_4_1 12, n_4_1 13, n_4_1 14, p ⟨0,by decide⟩ 11, p ⟨1,by decide⟩ 9, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 11, p ⟨3,by decide⟩ 11, h.f1]

private theorem cell81 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_2_1 : Neg r 2 1) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f1, h.f2, n_1_2 0, n_1_2 19, n_2_1 0, n_2_1 11, n_2_1 12, n_2_1 13, n_2_1 14, p ⟨1,by decide⟩ 9, p ⟨1,by decide⟩ 10, p ⟨1,by decide⟩ 11, p ⟨1,by decide⟩ 12, p ⟨1,by decide⟩ 13, p ⟨2,by decide⟩ 11]

private theorem cell82 {r : Register} (h : Frame r) (n_2_2 : Neg r 2 2) (n_4_1 : Neg r 4 1) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f1, h.f2, n_2_2 0, n_2_2 13, n_2_2 15, n_2_2 16, n_4_1 14, p ⟨0,by decide⟩ 11, p ⟨1,by decide⟩ 11, p ⟨1,by decide⟩ 13, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 11, p ⟨2,by decide⟩ 13, p ⟨2,by decide⟩ 15]

private theorem cell83 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_2_3 : Neg r 2 3) (n_4_1 : Neg r 4 1) (n_6_0 : Neg r 6 0) (n_15_0 : Neg r 15 0) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f1, h.f2, n_1_2 0, n_2_3 0, n_2_3 13, n_4_1 14, n_6_0 15, n_15_0 0, p ⟨0,by decide⟩ 12, p ⟨1,by decide⟩ 9, p ⟨1,by decide⟩ 10, p ⟨1,by decide⟩ 11, p ⟨2,by decide⟩ 11]

private theorem cell84 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_15_1 : Neg r 15 1) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, n_1_2 0, n_15_1 0, p ⟨0,by decide⟩ 8, p ⟨0,by decide⟩ 15, p ⟨0,by decide⟩ 16, p ⟨2,by decide⟩ 0, p ⟨3,by decide⟩ 9, p ⟨3,by decide⟩ 11, h.f1]

private theorem cell85 {r : Register} (h : Frame r) (n_2_3 : Neg r 2 3) (n_4_1 : Neg r 4 1) (n_15_2 : Neg r 15 2) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f1, n_2_3 0, n_4_1 0, n_4_1 14, n_15_2 0, p ⟨0,by decide⟩ 12, p ⟨0,by decide⟩ 15, p ⟨2,by decide⟩ 9, p ⟨2,by decide⟩ 11, h.f2]

private theorem cell86 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_6_0 : Neg r 6 0) (n_15_3 : Neg r 15 3) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, n_1_2 0, n_1_2 17, n_1_2 19, n_6_0 15, n_6_0 16, n_15_3 0, p ⟨1,by decide⟩ 9, h.f1]

private theorem cell87 {r : Register} (h : Frame r) (n_2_3 : Neg r 2 3) (n_4_1 : Neg r 4 1) (n_15_4 : Neg r 15 4) (p : Pos r 9) : False := by
  lin_close [h.f0, n_2_3 0, n_2_3 13, n_4_1 14, n_15_4 0, p ⟨0,by decide⟩ 12, p ⟨2,by decide⟩ 11, h.f1, h.f2]

private theorem cell88 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_6_0 : Neg r 6 0) (n_15_5 : Neg r 15 5) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, n_1_2 0, n_1_2 17, n_1_2 19, n_6_0 16, n_15_5 0, p ⟨1,by decide⟩ 9, h.f1]

private theorem cell89 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_2_3 : Neg r 2 3) (n_4_1 : Neg r 4 1) (n_6_1 : Neg r 6 1) (p : Pos r 9) : False := by
  lin_close [h.f0, n_1_2 0, n_1_2 19, n_2_3 13, n_4_1 14, n_6_1 0, n_6_1 12, n_6_1 13, n_6_1 14, p ⟨1,by decide⟩ 9, p ⟨1,by decide⟩ 10, p ⟨1,by decide⟩ 11, p ⟨1,by decide⟩ 12, p ⟨2,by decide⟩ 11, h.f1, h.f2]

private theorem cell90 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_2_3 : Neg r 2 3) (n_4_1 : Neg r 4 1) (n_6_2 : Neg r 6 2) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, n_1_2 19, n_2_3 13, n_4_1 14, n_6_2 0, n_6_2 15, n_6_2 16, p ⟨0,by decide⟩ 8, p ⟨1,by decide⟩ 10, p ⟨1,by decide⟩ 11, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 11, h.f1]

private theorem cell91 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_4_1 : Neg r 4 1) (n_6_3 : Neg r 6 3) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, n_1_2 0, n_1_2 19, n_4_1 13, n_6_3 0, n_6_3 13, n_6_3 14, p ⟨1,by decide⟩ 9, p ⟨3,by decide⟩ 11, h.f1]

private theorem cell92 {r : Register} (h : Frame r) (n_4_2 : Neg r 4 2) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f1, h.f2, n_4_2 0, n_4_2 13, n_4_2 15, n_4_2 17, n_4_2 18, p ⟨0,by decide⟩ 9, p ⟨1,by decide⟩ 11, p ⟨1,by decide⟩ 13, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 11, p ⟨2,by decide⟩ 13, p ⟨2,by decide⟩ 15]

private theorem cell93 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_3_1 : Neg r 3 1) (n_4_3 : Neg r 4 3) (n_15_0 : Neg r 15 0) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f1, n_1_2 0, n_3_1 15, n_4_3 0, n_4_3 9, n_4_3 11, n_4_3 13, n_4_3 14, n_15_0 0, p ⟨0,by decide⟩ 12, p ⟨1,by decide⟩ 9, p ⟨1,by decide⟩ 10, p ⟨1,by decide⟩ 11, h.f2]

private theorem cell94 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_15_1 : Neg r 15 1) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, n_1_2 0, n_15_1 0, p ⟨0,by decide⟩ 4, p ⟨0,by decide⟩ 14, p ⟨0,by decide⟩ 15, p ⟨0,by decide⟩ 16, p ⟨2,by decide⟩ 0, p ⟨3,by decide⟩ 9, p ⟨3,by decide⟩ 11, h.f1]

private theorem cell95 {r : Register} (h : Frame r) (n_3_1 : Neg r 3 1) (n_4_3 : Neg r 4 3) (n_15_2 : Neg r 15 2) (p : Pos r 9) : False := by
  lin_close [h.f0, n_3_1 15, n_4_3 0, n_4_3 14, n_15_2 0, p ⟨0,by decide⟩ 15, h.f1, h.f2]

private theorem cell96 {r : Register} (h : Frame r) (n_3_1 : Neg r 3 1) (n_4_3 : Neg r 4 3) (n_15_4 : Neg r 15 4) : False := by
  lin_close [h.f0, n_3_1 15, n_4_3 0, n_4_3 14, n_15_4 0, h.f1, h.f2]

private theorem cell97 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_4_3 : Neg r 4 3) (n_6_1 : Neg r 6 1) (p : Pos r 9) : False := by
  lin_close [h.f0, n_1_2 0, n_1_2 19, n_4_3 14, n_6_1 0, n_6_1 12, n_6_1 13, n_6_1 14, p ⟨1,by decide⟩ 9, p ⟨1,by decide⟩ 10, p ⟨1,by decide⟩ 11, p ⟨1,by decide⟩ 12, h.f1, h.f2]

private theorem cell98 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_3_1 : Neg r 3 1) (n_4_3 : Neg r 4 3) (n_6_2 : Neg r 6 2) (p : Pos r 9) : False := by
  lin_close [h.f0, n_1_2 19, n_3_1 15, n_4_3 0, n_4_3 14, n_6_2 0, n_6_2 15, n_6_2 16, p ⟨1,by decide⟩ 10, p ⟨1,by decide⟩ 11, h.f1, h.f2]

private theorem cell99 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_6_3 : Neg r 6 3) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, n_1_2 0, n_1_2 15, n_1_2 19, n_6_3 0, n_6_3 13, n_6_3 15, n_6_3 16, p ⟨0,by decide⟩ 14, p ⟨1,by decide⟩ 9, p ⟨3,by decide⟩ 11, h.f1]

private theorem cell100 {r : Register} (h : Frame r) (n_3_2 : Neg r 3 2) (n_4_0 : Neg r 4 0) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, n_3_2 19, n_4_0 0, n_4_0 14, n_4_0 15, p ⟨0,by decide⟩ 11, p ⟨0,by decide⟩ 13, p ⟨0,by decide⟩ 14, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 11, h.f1]

private theorem cell101 {r : Register} (h : Frame r) (n_2_0 : Neg r 2 0) (n_3_2 : Neg r 3 2) (n_4_1 : Neg r 4 1) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, n_2_0 14, n_2_0 15, n_3_2 0, n_3_2 17, n_3_2 20, n_4_1 14, p ⟨0,by decide⟩ 11, p ⟨1,by decide⟩ 11, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 11, h.f1]

private theorem cell102 {r : Register} (h : Frame r) (n_2_1 : Neg r 2 1) (n_3_2 : Neg r 3 2) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, n_2_1 0, n_2_1 13, n_2_1 14, n_3_2 0, n_3_2 20, p ⟨1,by decide⟩ 11, p ⟨1,by decide⟩ 12, p ⟨1,by decide⟩ 13, p ⟨2,by decide⟩ 11, h.f1]

private theorem cell103 {r : Register} (h : Frame r) (n_2_3 : Neg r 2 3) (n_3_2 : Neg r 3 2) (n_4_1 : Neg r 4 1) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, n_2_3 11, n_2_3 13, n_3_2 0, n_3_2 19, n_3_2 20, n_4_1 14, p ⟨0,by decide⟩ 9, p ⟨1,by decide⟩ 11, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 11, h.f1]

private theorem cell104 {r : Register} (h : Frame r) (n_4_2 : Neg r 4 2) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f1, h.f2, n_4_2 0, n_4_2 13, n_4_2 15, n_4_2 17, n_4_2 18, p ⟨0,by decide⟩ 8, p ⟨1,by decide⟩ 11, p ⟨1,by decide⟩ 13, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 11, p ⟨2,by decide⟩ 13, p ⟨2,by decide⟩ 15]

private theorem cell105 {r : Register} (h : Frame r) (n_3_2 : Neg r 3 2) (n_4_3 : Neg r 4 3) (p : Pos r 9) : False := by
  lin_close [h.f0, n_3_2 0, n_3_2 20, n_4_3 0, n_4_3 12, n_4_3 13, n_4_3 14, p ⟨0,by decide⟩ 12, p ⟨0,by decide⟩ 13, p ⟨0,by decide⟩ 14, p ⟨1,by decide⟩ 11, p ⟨2,by decide⟩ 11, h.f1, h.f2]

private theorem cell106 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_3_3 : Neg r 3 3) (p : Pos r 9) : False := by
  lin_close [h.f0, h.f2, n_1_2 0, n_1_2 15, n_1_2 19, n_3_3 0, n_3_3 9, n_3_3 11, n_3_3 12, p ⟨0,by decide⟩ 13, p ⟨1,by decide⟩ 9, p ⟨3,by decide⟩ 11, h.f1]

private theorem cell107 {r : Register} (h : Frame r) (n_1_3 : Neg r 1 3) (p : Pos r 9) : False := by
  lin_close [h.f0, n_1_3 0, n_1_3 12, p ⟨0,by decide⟩ 14, p ⟨1,by decide⟩ 8, p ⟨3,by decide⟩ 0, p ⟨3,by decide⟩ 7, h.f1, h.f2]

private theorem cell108 {r : Register} (h : Frame r) (n_0_0 : Neg r 0 0) (p : Pos r 1) : False := by
  lin_close [h.f0, n_0_0 0, n_0_0 16, n_0_0 17, p ⟨0,by decide⟩ 11, p ⟨0,by decide⟩ 13, p ⟨0,by decide⟩ 14, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 11, p ⟨3,by decide⟩ 9, h.f1, h.f2]

private theorem cell109 {r : Register} (h : Frame r) (n_0_1 : Neg r 0 1) (p : Pos r 1) : False := by
  lin_close [h.f0, n_0_1 13, p ⟨0,by decide⟩ 11, p ⟨1,by decide⟩ 10, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 11, p ⟨3,by decide⟩ 0, h.f1, h.f2]

private theorem cell110 {r : Register} (h : Frame r) (n_0_2 : Neg r 0 2) (p : Pos r 1) : False := by
  lin_close [h.f0, n_0_2 0, n_0_2 16, p ⟨0,by decide⟩ 10, p ⟨1,by decide⟩ 13, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 11, h.f1, h.f2]

private theorem cell111 {r : Register} (h : Frame r) (n_0_3 : Neg r 0 3) (p : Pos r 1) : False := by
  lin_close [h.f0, h.f1, h.f2, n_0_3 0, n_0_3 11, n_0_3 13, n_0_3 14, p ⟨0,by decide⟩ 11, p ⟨0,by decide⟩ 14, p ⟨1,by decide⟩ 10, p ⟨3,by decide⟩ 0, p ⟨3,by decide⟩ 9, p ⟨3,by decide⟩ 11]

private theorem cell112 {r : Register} (h : Frame r) (n_9_0 : Neg r 9 0) (p : Pos r 2) : False := by
  lin_close [h.f0, n_9_0 0, n_9_0 16, p ⟨0,by decide⟩ 11, p ⟨2,by decide⟩ 0, p ⟨3,by decide⟩ 9, h.f1, h.f2]

private theorem cell113 {r : Register} (h : Frame r) (n_9_1 : Neg r 9 1) (p : Pos r 2) : False := by
  lin_close [h.f0, n_9_1 13, n_9_1 14, p ⟨0,by decide⟩ 11, p ⟨1,by decide⟩ 10, p ⟨1,by decide⟩ 12, p ⟨1,by decide⟩ 13, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 11, p ⟨3,by decide⟩ 0, p ⟨3,by decide⟩ 9, h.f1, h.f2]

private theorem cell114 {r : Register} (h : Frame r) (n_9_2 : Neg r 9 2) (p : Pos r 2) : False := by
  lin_close [h.f0, h.f1, h.f2, n_9_2 0, n_9_2 15, n_9_2 17, n_9_2 18, p ⟨0,by decide⟩ 9, p ⟨1,by decide⟩ 11, p ⟨1,by decide⟩ 13, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 11, p ⟨2,by decide⟩ 13]

private theorem cell115 {r : Register} (h : Frame r) (n_9_3 : Neg r 9 3) (p : Pos r 2) : False := by
  lin_close [h.f0, n_9_3 0, n_9_3 12, p ⟨0,by decide⟩ 13, p ⟨1,by decide⟩ 10, p ⟨3,by decide⟩ 0, p ⟨3,by decide⟩ 9, h.f1, h.f2]

private theorem cell116 {r : Register} (h : Frame r) (n_0_0 : Neg r 0 0) (p : Pos r 3) : False := by
  lin_close [h.f0, n_0_0 14, n_0_0 15, n_0_0 16, p ⟨0,by decide⟩ 10, p ⟨0,by decide⟩ 13, p ⟨0,by decide⟩ 14, p ⟨0,by decide⟩ 15, p ⟨1,by decide⟩ 9, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 11, p ⟨3,by decide⟩ 0, p ⟨3,by decide⟩ 9, h.f1, h.f2]

private theorem cell117 {r : Register} (h : Frame r) (n_0_1 : Neg r 0 1) (p : Pos r 3) : False := by
  lin_close [h.f0, n_0_1 0, n_0_1 15, p ⟨1,by decide⟩ 9, p ⟨2,by decide⟩ 11, p ⟨3,by decide⟩ 0, h.f1, h.f2]

private theorem cell118 {r : Register} (h : Frame r) (n_0_2 : Neg r 0 2) (p : Pos r 3) : False := by
  lin_close [h.f0, h.f1, h.f2, n_0_2 0, n_0_2 13, n_0_2 15, n_0_2 16, p ⟨0,by decide⟩ 9, p ⟨1,by decide⟩ 11, p ⟨1,by decide⟩ 13, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 11, p ⟨2,by decide⟩ 13]

private theorem cell119 {r : Register} (h : Frame r) (n_0_3 : Neg r 0 3) (p : Pos r 3) : False := by
  lin_close [h.f0, n_0_3 0, n_0_3 14, p ⟨0,by decide⟩ 14, p ⟨1,by decide⟩ 9, p ⟨3,by decide⟩ 0, p ⟨3,by decide⟩ 9, h.f1, h.f2]

private theorem cell120 {r : Register} (h : Frame r) (n_9_0 : Neg r 9 0) (p : Pos r 4) : False := by
  lin_close [h.f0, n_9_0 14, n_9_0 15, n_9_0 16, p ⟨0,by decide⟩ 10, p ⟨0,by decide⟩ 13, p ⟨0,by decide⟩ 14, p ⟨0,by decide⟩ 15, p ⟨1,by decide⟩ 9, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 11, p ⟨3,by decide⟩ 0, p ⟨3,by decide⟩ 9, h.f1, h.f2]

private theorem cell121 {r : Register} (h : Frame r) (n_9_1 : Neg r 9 1) (p : Pos r 4) : False := by
  lin_close [h.f0, n_9_1 0, n_9_1 15, p ⟨1,by decide⟩ 9, p ⟨2,by decide⟩ 11, p ⟨3,by decide⟩ 0, h.f1, h.f2]

private theorem cell122 {r : Register} (h : Frame r) (n_9_2 : Neg r 9 2) (p : Pos r 4) : False := by
  lin_close [h.f0, h.f1, h.f2, n_9_2 0, n_9_2 13, n_9_2 15, n_9_2 16, p ⟨0,by decide⟩ 9, p ⟨1,by decide⟩ 11, p ⟨1,by decide⟩ 13, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 11, p ⟨2,by decide⟩ 13]

private theorem cell123 {r : Register} (h : Frame r) (n_9_3 : Neg r 9 3) (p : Pos r 4) : False := by
  lin_close [h.f0, n_9_3 0, n_9_3 14, p ⟨0,by decide⟩ 14, p ⟨1,by decide⟩ 9, p ⟨3,by decide⟩ 0, p ⟨3,by decide⟩ 9, h.f1, h.f2]

private theorem cell124 {r : Register} (h : Frame r) (n_0_0 : Neg r 0 0) (p : Pos r 5) : False := by
  lin_close [h.f0, n_0_0 0, n_0_0 17, p ⟨0,by decide⟩ 10, p ⟨2,by decide⟩ 0, p ⟨3,by decide⟩ 11, h.f1, h.f2]

private theorem cell125 {r : Register} (h : Frame r) (n_0_1 : Neg r 0 1) (p : Pos r 5) : False := by
  lin_close [h.f0, n_0_1 11, n_0_1 12, n_0_1 13, p ⟨0,by decide⟩ 10, p ⟨1,by decide⟩ 9, p ⟨1,by decide⟩ 11, p ⟨1,by decide⟩ 12, p ⟨1,by decide⟩ 13, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 11, p ⟨3,by decide⟩ 0, p ⟨3,by decide⟩ 9, h.f1, h.f2]

private theorem cell126 {r : Register} (h : Frame r) (n_0_2 : Neg r 0 2) (p : Pos r 5) : False := by
  lin_close [h.f0, n_0_2 0, n_0_2 18, p ⟨0,by decide⟩ 9, p ⟨1,by decide⟩ 12, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 11, h.f1, h.f2]

private theorem cell127 {r : Register} (h : Frame r) (n_0_3 : Neg r 0 3) (p : Pos r 5) : False := by
  lin_close [h.f0, h.f1, h.f2, n_0_3 0, n_0_3 9, n_0_3 11, n_0_3 12, p ⟨0,by decide⟩ 12, p ⟨0,by decide⟩ 15, p ⟨1,by decide⟩ 9, p ⟨3,by decide⟩ 0, p ⟨3,by decide⟩ 9, p ⟨3,by decide⟩ 11]

private theorem cell128 {r : Register} (h : Frame r) (n_9_0 : Neg r 9 0) (p : Pos r 6) : False := by
  lin_close [h.f0, n_9_0 0, n_9_0 17, p ⟨0,by decide⟩ 10, p ⟨2,by decide⟩ 0, p ⟨3,by decide⟩ 11, h.f1, h.f2]

private theorem cell129 {r : Register} (h : Frame r) (n_9_1 : Neg r 9 1) (p : Pos r 6) : False := by
  lin_close [h.f0, n_9_1 11, n_9_1 12, n_9_1 13, p ⟨0,by decide⟩ 10, p ⟨1,by decide⟩ 9, p ⟨1,by decide⟩ 11, p ⟨1,by decide⟩ 12, p ⟨1,by decide⟩ 13, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 11, p ⟨3,by decide⟩ 0, p ⟨3,by decide⟩ 9, h.f1, h.f2]

private theorem cell130 {r : Register} (h : Frame r) (n_9_2 : Neg r 9 2) (p : Pos r 6) : False := by
  lin_close [h.f0, n_9_2 0, n_9_2 18, p ⟨0,by decide⟩ 9, p ⟨1,by decide⟩ 12, p ⟨2,by decide⟩ 0, p ⟨2,by decide⟩ 11, h.f1, h.f2]

private theorem cell131 {r : Register} (h : Frame r) (n_9_3 : Neg r 9 3) (p : Pos r 6) : False := by
  lin_close [h.f0, h.f2, n_9_3 0, n_9_3 9, n_9_3 11, n_9_3 12, p ⟨0,by decide⟩ 12, p ⟨0,by decide⟩ 15, p ⟨1,by decide⟩ 9, p ⟨3,by decide⟩ 0, p ⟨3,by decide⟩ 9, p ⟨3,by decide⟩ 11, h.f1]

private theorem cell132 {r : Register} (h : Frame r) (n_9_0 : Neg r 9 0) (p : Pos r 10) : False := by
  lin_close [h.f0, n_9_0 15, p ⟨1,by decide⟩ 0, p ⟨2,by decide⟩ 0, p ⟨3,by decide⟩ 0, h.f1, h.f2]

private theorem cell133 {r : Register} (h : Frame r) (n_9_1 : Neg r 9 1) (p : Pos r 10) : False := by
  lin_close [h.f0, h.f2, n_9_1 13, p ⟨0,by decide⟩ 0, p ⟨2,by decide⟩ 0, p ⟨3,by decide⟩ 0, h.f1]

private theorem cell134 {r : Register} (h : Frame r) (n_9_2 : Neg r 9 2) (p : Pos r 10) : False := by
  lin_close [h.f0, n_9_2 14, p ⟨0,by decide⟩ 0, p ⟨2,by decide⟩ 0, p ⟨3,by decide⟩ 0, h.f1, h.f2]

private theorem cell135 {r : Register} (h : Frame r) (n_9_3 : Neg r 9 3) (p : Pos r 10) : False := by
  lin_close [h.f0, h.f2, n_9_3 13, p ⟨0,by decide⟩ 0, p ⟨1,by decide⟩ 0, p ⟨2,by decide⟩ 0, p ⟨3,by decide⟩ 0, h.f1]

private theorem cell136 {r : Register} (h : Frame r) (n_0_0 : Neg r 0 0) (p : Pos r 11) : False := by
  lin_close [h.f0, n_0_0 0, n_0_0 16, p ⟨1,by decide⟩ 0, p ⟨2,by decide⟩ 0, h.f1, h.f2]

private theorem cell137 {r : Register} (h : Frame r) (n_0_1 : Neg r 0 1) (p : Pos r 11) : False := by
  lin_close [h.f0, n_0_1 12, p ⟨0,by decide⟩ 0, p ⟨2,by decide⟩ 0, p ⟨3,by decide⟩ 0, h.f1, h.f2]

private theorem cell138 {r : Register} (h : Frame r) (n_0_2 : Neg r 0 2) (p : Pos r 11) : False := by
  lin_close [h.f0, n_0_2 0, p ⟨0,by decide⟩ 0, p ⟨2,by decide⟩ 0, h.f1, h.f2]

private theorem cell139 {r : Register} (h : Frame r) (n_0_3 : Neg r 0 3) (p : Pos r 11) : False := by
  lin_close [h.f0, n_0_3 10, p ⟨1,by decide⟩ 0, p ⟨2,by decide⟩ 0, p ⟨3,by decide⟩ 0, h.f1, h.f2]

private theorem cell140 {r : Register} (h : Frame r) (n_0_0 : Neg r 0 0) (p : Pos r 12) : False := by
  lin_close [h.f0, n_0_0 15, p ⟨1,by decide⟩ 0, p ⟨2,by decide⟩ 0, p ⟨3,by decide⟩ 0, h.f1, h.f2]

private theorem cell141 {r : Register} (h : Frame r) (n_0_1 : Neg r 0 1) (p : Pos r 12) : False := by
  lin_close [h.f0, n_0_1 13, p ⟨0,by decide⟩ 0, p ⟨3,by decide⟩ 0, h.f1, h.f2]

private theorem cell142 {r : Register} (h : Frame r) (n_0_2 : Neg r 0 2) (p : Pos r 12) : False := by
  lin_close [h.f0, n_0_2 17, p ⟨0,by decide⟩ 0, p ⟨3,by decide⟩ 0, h.f1, h.f2]

private theorem cell143 {r : Register} (h : Frame r) (n_0_3 : Neg r 0 3) (p : Pos r 12) : False := by
  lin_close [h.f0, n_0_3 12, p ⟨1,by decide⟩ 0, p ⟨2,by decide⟩ 0, p ⟨3,by decide⟩ 0, h.f1, h.f2]

private theorem cell144 {r : Register} (h : Frame r) (n_0_0 : Neg r 0 0) (p : Pos r 13) : False := by
  lin_close [h.f0, h.f2, n_0_0 15, p ⟨0,by decide⟩ 0, p ⟨1,by decide⟩ 0, p ⟨2,by decide⟩ 0, p ⟨3,by decide⟩ 0, h.f1]

private theorem cell145 {r : Register} (h : Frame r) (n_0_1 : Neg r 0 1) (p : Pos r 13) : False := by
  lin_close [h.f0, n_0_1 14, p ⟨0,by decide⟩ 0, p ⟨1,by decide⟩ 0, p ⟨2,by decide⟩ 0, p ⟨3,by decide⟩ 0, h.f1, h.f2]

private theorem cell146 {r : Register} (h : Frame r) (n_0_2 : Neg r 0 2) (p : Pos r 13) : False := by
  lin_close [h.f2, n_0_2 15, p ⟨0,by decide⟩ 0, p ⟨1,by decide⟩ 0, p ⟨2,by decide⟩ 0, h.f0, h.f1]

private theorem cell147 {r : Register} (h : Frame r) (n_0_3 : Neg r 0 3) (p : Pos r 13) : False := by
  lin_close [h.f0, n_0_3 12, p ⟨0,by decide⟩ 0, p ⟨1,by decide⟩ 0, p ⟨2,by decide⟩ 0, p ⟨3,by decide⟩ 0, h.f1, h.f2]

private theorem cell148 {r : Register} (h : Frame r) (n_0_0 : Neg r 0 0) (p : Pos r 14) : False := by
  lin_close [h.f0, n_0_0 0, p ⟨0,by decide⟩ 0, h.f1, h.f2]

private theorem cell149 {r : Register} (h : Frame r) (n_0_1 : Neg r 0 1) (p : Pos r 14) : False := by
  lin_close [h.f1, h.f2, n_0_1 12, p ⟨0,by decide⟩ 0, p ⟨1,by decide⟩ 0, p ⟨2,by decide⟩ 0, h.f0]

private theorem cell150 {r : Register} (h : Frame r) (n_0_2 : Neg r 0 2) (p : Pos r 14) : False := by
  lin_close [h.f2, n_0_2 18, p ⟨0,by decide⟩ 0, p ⟨1,by decide⟩ 0, p ⟨2,by decide⟩ 0, p ⟨3,by decide⟩ 0, h.f0, h.f1]

private theorem cell151 {r : Register} (h : Frame r) (n_0_3 : Neg r 0 3) (p : Pos r 14) : False := by
  lin_close [h.f0, n_0_3 10, p ⟨0,by decide⟩ 0, p ⟨1,by decide⟩ 0, p ⟨2,by decide⟩ 0, p ⟨3,by decide⟩ 0, h.f1, h.f2]

private theorem cell152 {r : Register} (h : Frame r) (n_0_0 : Neg r 0 0) (p : Pos r 15) : False := by
  lin_close [h.f0, n_0_0 16, p ⟨0,by decide⟩ 0, p ⟨1,by decide⟩ 0, p ⟨2,by decide⟩ 0, p ⟨5,by decide⟩ 0, h.f1, h.f2]

private theorem cell153 {r : Register} (h : Frame r) (n_0_1 : Neg r 0 1) (p : Pos r 15) : False := by
  lin_close [h.f0, h.f2, n_0_1 13, n_0_1 14, p ⟨0,by decide⟩ 0, p ⟨3,by decide⟩ 0, p ⟨4,by decide⟩ 0, h.f1]

private theorem cell154 {r : Register} (h : Frame r) (n_0_2 : Neg r 0 2) (p : Pos r 15) : False := by
  lin_close [h.f2, n_0_2 17, p ⟨3,by decide⟩ 0, p ⟨4,by decide⟩ 0, h.f0, h.f1]

private theorem cell155 {r : Register} (h : Frame r) (n_0_3 : Neg r 0 3) (p : Pos r 15) : False := by
  lin_close [h.f1, n_0_3 12, p ⟨0,by decide⟩ 0, p ⟨1,by decide⟩ 0, p ⟨2,by decide⟩ 0, p ⟨3,by decide⟩ 0, h.f0, h.f2]

private theorem cover0 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_2_0 : Neg r 2 0) (n_4_3 : Neg r 4 3) (n_5_2 : Neg r 5 2) (o_12 : Outside12 r) (p : Pos r 0) : False := by
  rcases o_12 with n_12_0 | n_12_1 | n_12_2 | n_12_3
  · exact cell6 h n_1_1 n_2_0 n_4_3 n_12_0 p
  · exact cell7 h n_2_0 n_5_2 n_12_1
  · exact cell8 h n_1_1 n_4_3 n_12_2 p
  · exact cell9 h n_2_0 n_5_2 n_12_3 p

private theorem cover1 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_2_0 : Neg r 2 0) (n_4_3 : Neg r 4 3) (o_5 : Outside5 r) (o_12 : Outside12 r) (p : Pos r 0) : False := by
  rcases o_5 with n_5_0 | n_5_1 | n_5_2 | n_5_3
  · exact cell4 h n_1_1 n_2_0 n_4_3 n_5_0 p
  · exact cell5 h n_1_1 n_2_0 n_4_3 n_5_1 p
  · exact cover0 h n_1_1 n_2_0 n_4_3 n_5_2 o_12 p
  · exact cell10 h n_1_1 n_2_0 n_5_3 p

private theorem cover2 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_2_0 : Neg r 2 0) (o_4 : Outside4 r) (o_5 : Outside5 r) (o_12 : Outside12 r) (p : Pos r 0) : False := by
  rcases o_4 with n_4_0 | n_4_1 | n_4_2 | n_4_3
  · exact cell1 h n_1_1 n_2_0 n_4_0 p
  · exact cell2 h n_2_0 n_4_1 p
  · exact cell3 h n_1_1 n_2_0 n_4_2 p
  · exact cover1 h n_1_1 n_2_0 n_4_3 o_5 o_12 p

private theorem cover3 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_2_0 : Neg r 2 0) (n_3_1 : Neg r 3 1) (n_4_3 : Neg r 4 3) (o_15 : Outside15 r) (p : Pos r 0) : False := by
  rcases o_15 with n_15_0 | n_15_1 | n_15_2 | n_15_3 | n_15_4 | n_15_5
  · exact cell15 h n_4_3 n_15_0 p
  · exact cell16 h n_1_2 n_2_0 n_3_1 n_15_1 p
  · exact cell17 h n_1_2 n_3_1 n_4_3 n_15_2 p
  · exact cell18 h n_1_2 n_2_0 n_15_3 p
  · exact cell19 h n_3_1 n_4_3 n_15_4 p
  · exact cell20 h n_1_2 n_2_0 n_15_5 p

private theorem cover4 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_2_0 : Neg r 2 0) (n_3_1 : Neg r 3 1) (o_4 : Outside4 r) (o_15 : Outside15 r) (p : Pos r 0) : False := by
  rcases o_4 with n_4_0 | n_4_1 | n_4_2 | n_4_3
  · exact cell12 h n_1_2 n_2_0 n_3_1 n_4_0 p
  · exact cell13 h n_1_2 n_2_0 n_4_1 p
  · exact cell14 h n_2_0 n_4_2 p
  · exact cover3 h n_1_2 n_2_0 n_3_1 n_4_3 o_15 p

private theorem cover5 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_2_0 : Neg r 2 0) (o_3 : Outside3 r) (o_4 : Outside4 r) (o_15 : Outside15 r) (p : Pos r 0) : False := by
  rcases o_3 with n_3_0 | n_3_1 | n_3_2 | n_3_3
  · exact cell11 h n_1_2 n_3_0 p
  · exact cover4 h n_1_2 n_2_0 n_3_1 o_4 o_15 p
  · exact cell21 h n_2_0 n_3_2 p
  · exact cell22 h n_1_2 n_2_0 n_3_3 p

private theorem cover6 {r : Register} (h : Frame r) (n_2_0 : Neg r 2 0) (o_1 : Outside1 r) (o_3 : Outside3 r) (o_4 : Outside4 r) (o_5 : Outside5 r) (o_12 : Outside12 r) (o_15 : Outside15 r) (p : Pos r 0) : False := by
  rcases o_1 with n_1_0 | n_1_1 | n_1_2 | n_1_3
  · exact cell0 h n_1_0 p
  · exact cover2 h n_1_1 n_2_0 o_4 o_5 o_12 p
  · exact cover5 h n_1_2 n_2_0 o_3 o_4 o_15 p
  · exact cell23 h n_1_3 n_2_0 p

private theorem cover7 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_2_3 : Neg r 2 3) (n_3_1 : Neg r 3 1) (n_5_0 : Neg r 5 0) (o_15 : Outside15 r) (p : Pos r 0) : False := by
  rcases o_15 with n_15_0 | n_15_1 | n_15_2 | n_15_3 | n_15_4 | n_15_5
  · exact cell29 h n_1_2 n_3_1 n_15_0 p
  · exact cell30 h n_1_2 n_3_1 n_5_0 n_15_1 p
  · exact cell31 h n_2_3 n_3_1 n_15_2 p
  · exact cell32 h n_1_2 n_5_0 n_15_3 p
  · exact cell33 h n_2_3 n_3_1 n_15_4 p
  · exact cell34 h n_1_2 n_5_0 n_15_5 p

private theorem cover8 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_2_3 : Neg r 2 3) (n_5_0 : Neg r 5 0) (o_3 : Outside3 r) (o_15 : Outside15 r) (p : Pos r 0) : False := by
  rcases o_3 with n_3_0 | n_3_1 | n_3_2 | n_3_3
  · exact cell28 h n_1_2 n_2_3 n_3_0 n_5_0 p
  · exact cover7 h n_1_2 n_2_3 n_3_1 n_5_0 o_15 p
  · exact cell35 h n_2_3 n_3_2 n_5_0 p
  · exact cell36 h n_1_2 n_2_3 n_3_3 n_5_0 p

private theorem cover9 {r : Register} (h : Frame r) (n_2_3 : Neg r 2 3) (n_5_0 : Neg r 5 0) (o_1 : Outside1 r) (o_3 : Outside3 r) (o_15 : Outside15 r) (p : Pos r 0) : False := by
  rcases o_1 with n_1_0 | n_1_1 | n_1_2 | n_1_3
  · exact cell26 h n_1_0 n_2_3 p
  · exact cell27 h n_1_1 n_2_3 n_5_0 p
  · exact cover8 h n_1_2 n_2_3 n_5_0 o_3 o_15 p
  · exact cell37 h n_1_3 n_5_0 p

private theorem cover10 {r : Register} (h : Frame r) (n_2_3 : Neg r 2 3) (n_3_1 : Neg r 3 1) (n_5_2 : Neg r 5 2) (o_15 : Outside15 r) (p : Pos r 0) : False := by
  rcases o_15 with n_15_0 | n_15_1 | n_15_2 | n_15_3 | n_15_4 | n_15_5
  · exact cell40 h n_2_3 n_15_0 p
  · exact cell41 h n_5_2 n_15_1 p
  · exact cell31 h n_2_3 n_3_1 n_15_2 p
  · exact cell42 h n_5_2 n_15_3 p
  · exact cell33 h n_2_3 n_3_1 n_15_4 p
  · exact cell43 h n_5_2 n_15_5 p

private theorem cover11 {r : Register} (h : Frame r) (n_2_3 : Neg r 2 3) (n_5_2 : Neg r 5 2) (n_6_0 : Neg r 6 0) (o_3 : Outside3 r) (o_15 : Outside15 r) (p : Pos r 0) : False := by
  rcases o_3 with n_3_0 | n_3_1 | n_3_2 | n_3_3
  · exact cell39 h n_2_3 n_3_0 n_5_2 p
  · exact cover10 h n_2_3 n_3_1 n_5_2 o_15 p
  · exact cell44 h n_2_3 n_3_2 n_6_0 p
  · exact cell45 h n_2_3 n_3_3 n_5_2 p

private theorem cover12 {r : Register} (h : Frame r) (n_2_3 : Neg r 2 3) (n_6_0 : Neg r 6 0) (o_1 : Outside1 r) (o_3 : Outside3 r) (o_5 : Outside5 r) (o_15 : Outside15 r) (p : Pos r 0) : False := by
  rcases o_5 with n_5_0 | n_5_1 | n_5_2 | n_5_3
  · exact cover9 h n_2_3 n_5_0 o_1 o_3 o_15 p
  · exact cell38 h n_2_3 n_5_1 n_6_0 p
  · exact cover11 h n_2_3 n_5_2 n_6_0 o_3 o_15 p
  · exact cell46 h n_5_3 p

private theorem cover13 {r : Register} (h : Frame r) (n_5_0 : Neg r 5 0) (n_6_3 : Neg r 6 3) (o_1 : Outside1 r) (p : Pos r 0) : False := by
  rcases o_1 with n_1_0 | n_1_1 | n_1_2 | n_1_3
  · exact cell49 h n_1_0 n_6_3 p
  · exact cell50 h n_1_1 n_5_0 n_6_3 p
  · exact cell51 h n_1_2 n_5_0 n_6_3 p
  · exact cell37 h n_1_3 n_5_0 p

private theorem cover14 {r : Register} (h : Frame r) (n_6_3 : Neg r 6 3) (o_1 : Outside1 r) (o_5 : Outside5 r) (p : Pos r 0) : False := by
  rcases o_5 with n_5_0 | n_5_1 | n_5_2 | n_5_3
  · exact cover13 h n_5_0 n_6_3 o_1 p
  · exact cell52 h n_5_1 n_6_3 p
  · exact cell53 h n_5_2 n_6_3 p
  · exact cell46 h n_5_3 p

private theorem cover15 {r : Register} (h : Frame r) (n_2_3 : Neg r 2 3) (o_1 : Outside1 r) (o_3 : Outside3 r) (o_5 : Outside5 r) (o_6 : Outside6 r) (o_15 : Outside15 r) (p : Pos r 0) : False := by
  rcases o_6 with n_6_0 | n_6_1 | n_6_2 | n_6_3
  · exact cover12 h n_2_3 n_6_0 o_1 o_3 o_5 o_15 p
  · exact cell47 h n_2_3 n_6_1 p
  · exact cell48 h n_2_3 n_6_2 p
  · exact cover14 h n_6_3 o_1 o_5 p

private theorem cover16 {r : Register} (h : Frame r) (o_1 : Outside1 r) (o_2 : Outside2 r) (o_3 : Outside3 r) (o_4 : Outside4 r) (o_5 : Outside5 r) (o_6 : Outside6 r) (o_12 : Outside12 r) (o_15 : Outside15 r) (p : Pos r 0) : False := by
  rcases o_2 with n_2_0 | n_2_1 | n_2_2 | n_2_3
  · exact cover6 h n_2_0 o_1 o_3 o_4 o_5 o_12 o_15 p
  · exact cell24 h n_2_1 p
  · exact cell25 h n_2_2 p
  · exact cover15 h n_2_3 o_1 o_3 o_5 o_6 o_15 p

private theorem cover17 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_2_0 : Neg r 2 0) (n_4_3 : Neg r 4 3) (o_15 : Outside15 r) (p : Pos r 9) : False := by
  rcases o_15 with n_15_0 | n_15_1 | n_15_2 | n_15_3 | n_15_4 | n_15_5
  · exact cell58 h n_1_1 n_2_0 n_4_3 n_15_0 p
  · exact cell59 h n_2_0 n_15_1 p
  · exact cell60 h n_1_1 n_4_3 n_15_2 p
  · exact cell61 h n_2_0 n_15_3 p
  · exact cell62 h n_1_1 n_4_3 n_15_4 p
  · exact cell63 h n_2_0 n_15_5 p

private theorem cover18 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_2_0 : Neg r 2 0) (o_4 : Outside4 r) (o_15 : Outside15 r) (p : Pos r 9) : False := by
  rcases o_4 with n_4_0 | n_4_1 | n_4_2 | n_4_3
  · exact cell55 h n_1_1 n_4_0 p
  · exact cell56 h n_1_1 n_2_0 n_4_1 p
  · exact cell57 h n_1_1 n_2_0 n_4_2 p
  · exact cover17 h n_1_1 n_2_0 n_4_3 o_15 p

private theorem cover19 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_2_3 : Neg r 2 3) (n_5_2 : Neg r 5 2) (n_6_0 : Neg r 6 0) (o_15 : Outside15 r) (p : Pos r 9) : False := by
  rcases o_15 with n_15_0 | n_15_1 | n_15_2 | n_15_3 | n_15_4 | n_15_5
  · exact cell68 h n_1_1 n_2_3 n_5_2 n_6_0 n_15_0 p
  · exact cell69 h n_5_2 n_15_1 p
  · exact cell70 h n_1_1 n_2_3 n_15_2 p
  · exact cell71 h n_2_3 n_5_2 n_6_0 n_15_3 p
  · exact cell72 h n_1_1 n_2_3 n_15_4 p
  · exact cell73 h n_5_2 n_6_0 n_15_5 p

private theorem cover20 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_2_3 : Neg r 2 3) (n_6_0 : Neg r 6 0) (o_5 : Outside5 r) (o_15 : Outside15 r) (p : Pos r 9) : False := by
  rcases o_5 with n_5_0 | n_5_1 | n_5_2 | n_5_3
  · exact cell66 h n_1_1 n_2_3 n_5_0 p
  · exact cell67 h n_1_1 n_2_3 n_5_1 n_6_0 p
  · exact cover19 h n_1_1 n_2_3 n_5_2 n_6_0 o_15 p
  · exact cell74 h n_1_1 n_5_3 n_6_0 p

private theorem cover21 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (n_2_3 : Neg r 2 3) (o_5 : Outside5 r) (o_6 : Outside6 r) (o_15 : Outside15 r) (p : Pos r 9) : False := by
  rcases o_6 with n_6_0 | n_6_1 | n_6_2 | n_6_3
  · exact cover20 h n_1_1 n_2_3 n_6_0 o_5 o_15 p
  · exact cell75 h n_1_1 n_2_3 n_6_1 p
  · exact cell76 h n_1_1 n_2_3 n_6_2 p
  · exact cell77 h n_1_1 n_6_3 p

private theorem cover22 {r : Register} (h : Frame r) (n_1_1 : Neg r 1 1) (o_2 : Outside2 r) (o_4 : Outside4 r) (o_5 : Outside5 r) (o_6 : Outside6 r) (o_15 : Outside15 r) (p : Pos r 9) : False := by
  rcases o_2 with n_2_0 | n_2_1 | n_2_2 | n_2_3
  · exact cover18 h n_1_1 n_2_0 o_4 o_15 p
  · exact cell64 h n_2_1 p
  · exact cell65 h n_1_1 n_2_2 p
  · exact cover21 h n_1_1 n_2_3 o_5 o_6 o_15 p

private theorem cover23 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_2_3 : Neg r 2 3) (n_4_1 : Neg r 4 1) (n_6_0 : Neg r 6 0) (o_15 : Outside15 r) (p : Pos r 9) : False := by
  rcases o_15 with n_15_0 | n_15_1 | n_15_2 | n_15_3 | n_15_4 | n_15_5
  · exact cell83 h n_1_2 n_2_3 n_4_1 n_6_0 n_15_0 p
  · exact cell84 h n_1_2 n_15_1 p
  · exact cell85 h n_2_3 n_4_1 n_15_2 p
  · exact cell86 h n_1_2 n_6_0 n_15_3 p
  · exact cell87 h n_2_3 n_4_1 n_15_4 p
  · exact cell88 h n_1_2 n_6_0 n_15_5 p

private theorem cover24 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_2_3 : Neg r 2 3) (n_4_1 : Neg r 4 1) (o_6 : Outside6 r) (o_15 : Outside15 r) (p : Pos r 9) : False := by
  rcases o_6 with n_6_0 | n_6_1 | n_6_2 | n_6_3
  · exact cover23 h n_1_2 n_2_3 n_4_1 n_6_0 o_15 p
  · exact cell89 h n_1_2 n_2_3 n_4_1 n_6_1 p
  · exact cell90 h n_1_2 n_2_3 n_4_1 n_6_2 p
  · exact cell91 h n_1_2 n_4_1 n_6_3 p

private theorem cover25 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_4_1 : Neg r 4 1) (o_2 : Outside2 r) (o_6 : Outside6 r) (o_15 : Outside15 r) (p : Pos r 9) : False := by
  rcases o_2 with n_2_0 | n_2_1 | n_2_2 | n_2_3
  · exact cell80 h n_1_2 n_2_0 n_4_1 p
  · exact cell81 h n_1_2 n_2_1 p
  · exact cell82 h n_2_2 n_4_1 p
  · exact cover24 h n_1_2 n_2_3 n_4_1 o_6 o_15 p

private theorem cover26 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_3_1 : Neg r 3 1) (n_4_3 : Neg r 4 3) (n_6_0 : Neg r 6 0) (o_15 : Outside15 r) (p : Pos r 9) : False := by
  rcases o_15 with n_15_0 | n_15_1 | n_15_2 | n_15_3 | n_15_4 | n_15_5
  · exact cell93 h n_1_2 n_3_1 n_4_3 n_15_0 p
  · exact cell94 h n_1_2 n_15_1 p
  · exact cell95 h n_3_1 n_4_3 n_15_2 p
  · exact cell86 h n_1_2 n_6_0 n_15_3 p
  · exact cell96 h n_3_1 n_4_3 n_15_4
  · exact cell88 h n_1_2 n_6_0 n_15_5 p

private theorem cover27 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_3_1 : Neg r 3 1) (n_4_3 : Neg r 4 3) (o_6 : Outside6 r) (o_15 : Outside15 r) (p : Pos r 9) : False := by
  rcases o_6 with n_6_0 | n_6_1 | n_6_2 | n_6_3
  · exact cover26 h n_1_2 n_3_1 n_4_3 n_6_0 o_15 p
  · exact cell97 h n_1_2 n_4_3 n_6_1 p
  · exact cell98 h n_1_2 n_3_1 n_4_3 n_6_2 p
  · exact cell99 h n_1_2 n_6_3 p

private theorem cover28 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (n_3_1 : Neg r 3 1) (o_2 : Outside2 r) (o_4 : Outside4 r) (o_6 : Outside6 r) (o_15 : Outside15 r) (p : Pos r 9) : False := by
  rcases o_4 with n_4_0 | n_4_1 | n_4_2 | n_4_3
  · exact cell79 h n_3_1 n_4_0 p
  · exact cover25 h n_1_2 n_4_1 o_2 o_6 o_15 p
  · exact cell92 h n_4_2 p
  · exact cover27 h n_1_2 n_3_1 n_4_3 o_6 o_15 p

private theorem cover29 {r : Register} (h : Frame r) (n_3_2 : Neg r 3 2) (n_4_1 : Neg r 4 1) (o_2 : Outside2 r) (p : Pos r 9) : False := by
  rcases o_2 with n_2_0 | n_2_1 | n_2_2 | n_2_3
  · exact cell101 h n_2_0 n_3_2 n_4_1 p
  · exact cell102 h n_2_1 n_3_2 p
  · exact cell82 h n_2_2 n_4_1 p
  · exact cell103 h n_2_3 n_3_2 n_4_1 p

private theorem cover30 {r : Register} (h : Frame r) (n_3_2 : Neg r 3 2) (o_2 : Outside2 r) (o_4 : Outside4 r) (p : Pos r 9) : False := by
  rcases o_4 with n_4_0 | n_4_1 | n_4_2 | n_4_3
  · exact cell100 h n_3_2 n_4_0 p
  · exact cover29 h n_3_2 n_4_1 o_2 p
  · exact cell104 h n_4_2 p
  · exact cell105 h n_3_2 n_4_3 p

private theorem cover31 {r : Register} (h : Frame r) (n_1_2 : Neg r 1 2) (o_2 : Outside2 r) (o_3 : Outside3 r) (o_4 : Outside4 r) (o_6 : Outside6 r) (o_15 : Outside15 r) (p : Pos r 9) : False := by
  rcases o_3 with n_3_0 | n_3_1 | n_3_2 | n_3_3
  · exact cell78 h n_3_0 p
  · exact cover28 h n_1_2 n_3_1 o_2 o_4 o_6 o_15 p
  · exact cover30 h n_3_2 o_2 o_4 p
  · exact cell106 h n_1_2 n_3_3 p

private theorem cover32 {r : Register} (h : Frame r) (o_1 : Outside1 r) (o_2 : Outside2 r) (o_3 : Outside3 r) (o_4 : Outside4 r) (o_5 : Outside5 r) (o_6 : Outside6 r) (o_15 : Outside15 r) (p : Pos r 9) : False := by
  rcases o_1 with n_1_0 | n_1_1 | n_1_2 | n_1_3
  · exact cell54 h n_1_0 p
  · exact cover22 h n_1_1 o_2 o_4 o_5 o_6 o_15 p
  · exact cover31 h n_1_2 o_2 o_3 o_4 o_6 o_15 p
  · exact cell107 h n_1_3 p

private theorem cover33 {r : Register} (h : Frame r) (o_0 : Outside0 r) (p : Pos r 1) : False := by
  rcases o_0 with n_0_0 | n_0_1 | n_0_2 | n_0_3
  · exact cell108 h n_0_0 p
  · exact cell109 h n_0_1 p
  · exact cell110 h n_0_2 p
  · exact cell111 h n_0_3 p

private theorem cover34 {r : Register} (h : Frame r) (o_9 : Outside9 r) (p : Pos r 2) : False := by
  rcases o_9 with n_9_0 | n_9_1 | n_9_2 | n_9_3
  · exact cell112 h n_9_0 p
  · exact cell113 h n_9_1 p
  · exact cell114 h n_9_2 p
  · exact cell115 h n_9_3 p

private theorem cover35 {r : Register} (h : Frame r) (o_0 : Outside0 r) (p : Pos r 3) : False := by
  rcases o_0 with n_0_0 | n_0_1 | n_0_2 | n_0_3
  · exact cell116 h n_0_0 p
  · exact cell117 h n_0_1 p
  · exact cell118 h n_0_2 p
  · exact cell119 h n_0_3 p

private theorem cover36 {r : Register} (h : Frame r) (o_9 : Outside9 r) (p : Pos r 4) : False := by
  rcases o_9 with n_9_0 | n_9_1 | n_9_2 | n_9_3
  · exact cell120 h n_9_0 p
  · exact cell121 h n_9_1 p
  · exact cell122 h n_9_2 p
  · exact cell123 h n_9_3 p

private theorem cover37 {r : Register} (h : Frame r) (o_0 : Outside0 r) (p : Pos r 5) : False := by
  rcases o_0 with n_0_0 | n_0_1 | n_0_2 | n_0_3
  · exact cell124 h n_0_0 p
  · exact cell125 h n_0_1 p
  · exact cell126 h n_0_2 p
  · exact cell127 h n_0_3 p

private theorem cover38 {r : Register} (h : Frame r) (o_9 : Outside9 r) (p : Pos r 6) : False := by
  rcases o_9 with n_9_0 | n_9_1 | n_9_2 | n_9_3
  · exact cell128 h n_9_0 p
  · exact cell129 h n_9_1 p
  · exact cell130 h n_9_2 p
  · exact cell131 h n_9_3 p

private theorem cover39 {r : Register} (h : Frame r) (o_9 : Outside9 r) (p : Pos r 10) : False := by
  rcases o_9 with n_9_0 | n_9_1 | n_9_2 | n_9_3
  · exact cell132 h n_9_0 p
  · exact cell133 h n_9_1 p
  · exact cell134 h n_9_2 p
  · exact cell135 h n_9_3 p

private theorem cover40 {r : Register} (h : Frame r) (o_0 : Outside0 r) (p : Pos r 11) : False := by
  rcases o_0 with n_0_0 | n_0_1 | n_0_2 | n_0_3
  · exact cell136 h n_0_0 p
  · exact cell137 h n_0_1 p
  · exact cell138 h n_0_2 p
  · exact cell139 h n_0_3 p

private theorem cover41 {r : Register} (h : Frame r) (o_0 : Outside0 r) (p : Pos r 12) : False := by
  rcases o_0 with n_0_0 | n_0_1 | n_0_2 | n_0_3
  · exact cell140 h n_0_0 p
  · exact cell141 h n_0_1 p
  · exact cell142 h n_0_2 p
  · exact cell143 h n_0_3 p

private theorem cover42 {r : Register} (h : Frame r) (o_0 : Outside0 r) (p : Pos r 13) : False := by
  rcases o_0 with n_0_0 | n_0_1 | n_0_2 | n_0_3
  · exact cell144 h n_0_0 p
  · exact cell145 h n_0_1 p
  · exact cell146 h n_0_2 p
  · exact cell147 h n_0_3 p

private theorem cover43 {r : Register} (h : Frame r) (o_0 : Outside0 r) (p : Pos r 14) : False := by
  rcases o_0 with n_0_0 | n_0_1 | n_0_2 | n_0_3
  · exact cell148 h n_0_0 p
  · exact cell149 h n_0_1 p
  · exact cell150 h n_0_2 p
  · exact cell151 h n_0_3 p

private theorem cover44 {r : Register} (h : Frame r) (o_0 : Outside0 r) (p : Pos r 15) : False := by
  rcases o_0 with n_0_0 | n_0_1 | n_0_2 | n_0_3
  · exact cell152 h n_0_0 p
  · exact cell153 h n_0_1 p
  · exact cell154 h n_0_2 p
  · exact cell155 h n_0_3 p

private theorem included0 {r : Register} (h : Frame r) (yes : contains r 0) : contains r 1 ∨ contains r 2 ∨ contains r 3 ∨ contains r 4 ∨ contains r 5 ∨ contains r 6 ∨ contains r 10 ∨ contains r 11 ∨ contains r 12 ∨ contains r 13 ∨ contains r 14 ∨ contains r 15 := by
  by_contra miss
  have p := positive r h 0 yes
  exact cover16 h (outside1 h (by tauto)) (outside2 h (by tauto)) (outside3 h (by tauto)) (outside4 h (by tauto)) (outside5 h (by tauto)) (outside6 h (by tauto)) (outside12 h (by tauto)) (outside15 h (by tauto)) p

private theorem included9 {r : Register} (h : Frame r) (yes : contains r 9) : contains r 1 ∨ contains r 2 ∨ contains r 3 ∨ contains r 4 ∨ contains r 5 ∨ contains r 6 ∨ contains r 10 ∨ contains r 11 ∨ contains r 12 ∨ contains r 13 ∨ contains r 14 ∨ contains r 15 := by
  by_contra miss
  have p := positive r h 9 yes
  exact cover32 h (outside1 h (by tauto)) (outside2 h (by tauto)) (outside3 h (by tauto)) (outside4 h (by tauto)) (outside5 h (by tauto)) (outside6 h (by tauto)) (outside15 h (by tauto)) p

private theorem included1 {r : Register} (h : Frame r) (yes : contains r 1) : contains r 0 ∨ contains r 9 := by
  by_contra miss
  have p := positive r h 1 yes
  exact cover33 h (outside0 h (by tauto)) p

private theorem included2 {r : Register} (h : Frame r) (yes : contains r 2) : contains r 0 ∨ contains r 9 := by
  by_contra miss
  have p := positive r h 2 yes
  exact cover34 h (outside9 h (by tauto)) p

private theorem included3 {r : Register} (h : Frame r) (yes : contains r 3) : contains r 0 ∨ contains r 9 := by
  by_contra miss
  have p := positive r h 3 yes
  exact cover35 h (outside0 h (by tauto)) p

private theorem included4 {r : Register} (h : Frame r) (yes : contains r 4) : contains r 0 ∨ contains r 9 := by
  by_contra miss
  have p := positive r h 4 yes
  exact cover36 h (outside9 h (by tauto)) p

private theorem included5 {r : Register} (h : Frame r) (yes : contains r 5) : contains r 0 ∨ contains r 9 := by
  by_contra miss
  have p := positive r h 5 yes
  exact cover37 h (outside0 h (by tauto)) p

private theorem included6 {r : Register} (h : Frame r) (yes : contains r 6) : contains r 0 ∨ contains r 9 := by
  by_contra miss
  have p := positive r h 6 yes
  exact cover38 h (outside9 h (by tauto)) p

private theorem included10 {r : Register} (h : Frame r) (yes : contains r 10) : contains r 0 ∨ contains r 9 := by
  by_contra miss
  have p := positive r h 10 yes
  exact cover39 h (outside9 h (by tauto)) p

private theorem included11 {r : Register} (h : Frame r) (yes : contains r 11) : contains r 0 ∨ contains r 9 := by
  by_contra miss
  have p := positive r h 11 yes
  exact cover40 h (outside0 h (by tauto)) p

private theorem included12 {r : Register} (h : Frame r) (yes : contains r 12) : contains r 0 ∨ contains r 9 := by
  by_contra miss
  have p := positive r h 12 yes
  exact cover41 h (outside0 h (by tauto)) p

private theorem included13 {r : Register} (h : Frame r) (yes : contains r 13) : contains r 0 ∨ contains r 9 := by
  by_contra miss
  have p := positive r h 13 yes
  exact cover42 h (outside0 h (by tauto)) p

private theorem included14 {r : Register} (h : Frame r) (yes : contains r 14) : contains r 0 ∨ contains r 9 := by
  by_contra miss
  have p := positive r h 14 yes
  exact cover43 h (outside0 h (by tauto)) p

private theorem included15 {r : Register} (h : Frame r) (yes : contains r 15) : contains r 0 ∨ contains r 9 := by
  by_contra miss
  have p := positive r h 15 yes
  exact cover44 h (outside0 h (by tauto)) p

/-- Both inclusions, for all admissible denominators and every site of the specified checkerboard. -/
theorem coverage (r : Register) (h : Frame r) : (contains r 0 ∨ contains r 9) ↔ contains r 1 ∨ contains r 2 ∨ contains r 3 ∨ contains r 4 ∨ contains r 5 ∨ contains r 6 ∨ contains r 10 ∨ contains r 11 ∨ contains r 12 ∨ contains r 13 ∨ contains r 14 ∨ contains r 15 := by
  constructor
  · exact fun t => t.elim (included0 h) (included9 h)
  · rintro (t|t|t|t|t|t|t|t|t|t|t|t)
    · exact included1 h t
    · exact included2 h t
    · exact included3 h t
    · exact included4 h t
    · exact included5 h t
    · exact included6 h t
    · exact included10 h t
    · exact included11 h t
    · exact included12 h t
    · exact included13 h t
    · exact included14 h t
    · exact included15 h t

end FLatticePaper.Tiles.BaseMixedThreeOneOddEvenSites
