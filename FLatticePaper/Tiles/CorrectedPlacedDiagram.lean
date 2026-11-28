import FLatticePaper.Tiles.CorrectedPlacementFrames

/-! The ordinary and elongated polygons of the corrected decomposition in physical coordinates. -/

namespace FLatticePaper.Tiles.CorrectedPlacedDiagram

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open CorrectedCellsBands CorrectedRegisterDiagram CorrectedEvenPlacement
open CorrectedPhysicalFaces CorrectedPlacementFrames

/-- A translated physical polygon with a specified number of extra periods at each outer edge. -/
structure Block where
  c : Site
  a : Site
  b : Site
  h : ℕ := 0
  v : ℕ := 0

def Block.mem (s : Block) (z : Site) : Prop := Band s.a s.b s.h s.v (z-s.c)

def diagram (g : Periods) (N : ℕ) (one : Bool) (prev : ℤ) (long : Bool) (i : ℕ) : Block :=
  let e := orientation one prev
  let odd := decide (e≠1)
  let x := g.origin odd long
  let B := g.b
  let h := g.head odd (!one)
  let u := if one then g.a-g.u else g.u
  let b := if one then g.v-B else B-g.v
  let sib := if one then g.u else g.a-g.u
  let m := 2*N-if long then 0 else 1
  match i with
  | 0 => if long then ⟨x,g.a+g.fullU,B+g.fullV,0,0⟩ else ⟨x,g.a+g.fullU+g.fullU,B+g.fullV,0,0⟩
  | 1 => ⟨g.full odd false long,g.fullU,g.fullV,0,0⟩
  | 2 => ⟨g.full odd true long,g.fullU,g.fullV,0,0⟩
  | 3 => ⟨g.row odd true long,g.a,B,N,0⟩
  | 4 => ⟨g.row odd false long,g.a,B,N,0⟩
  | 5 => ⟨g.bridge odd true long,g.u,g.v,0,0⟩
  | 6 => ⟨g.bridge odd false long,g.u,g.v,0,0⟩
  | 7 => ⟨h,sib,B,0,m⟩
  | 8 => ⟨h+b+prev • u,sib,B,0,m⟩
  | _ => ⟨g.origin odd true+B-e • g.fullU,g.a+g.fullU,B+g.fullV,0,0⟩

/-- The corner and all four side vectors have their displayed integral projections. -/
structure Projects (p : Fraction) (s : Block) (t : Shape) : Prop where
  corner : Image p s.c t.corner
  horizontal : Image p s.a t.a
  vertical : Image p s.b t.b
  extraH : Image p ((s.h : ℤ) • s.a) t.extraA
  extraV : Image p ((s.v : ℤ) • s.b) t.extraB

theorem Projects.band_iff {r : Register} {s : Block} {t : Shape} (z : Site) (sec : Fin 3)
    (h : Projects ⟨r.n,r.d⟩ s t) (aligned : Aligned s.a s.b sec) :
    let p : Fraction := ⟨r.n,r.d⟩
    let par := oddSite z
    let ref : Site := if par then (1,0) else 0
    0 < CorrectedDomainLattice.scale p → (r.X,r.Y)=CorrectedDomainLattice.chart p (z-ref) →
    (s.mem z ↔ CorrectedRegisterFaces.exact (t.probe r par sec)) := by
  intro p par ref hm base
  have pr : projectedShape p s.a s.b s.c s.h s.v=t := by
    dsimp only [p,projectedShape]
    rw [h.corner.eqn,h.horizontal.eqn,h.vertical.eqn,h.extraH.eqn,h.extraV.eqn]
  rw [←pr]
  exact CorrectedPhysicalFaces.band_iff r s.a s.b s.c z s.h s.v sec h.horizontal.even h.vertical.even h.corner.even aligned hm base

private def vectorShape (s : Block) : Shape :=
  ⟨s.c,s.a,s.b,(s.h : ℤ) • s.a,(s.v : ℤ) • s.b⟩

private def coordinates (r : Register) (e : ℤ) : Periods :=
  ⟨(r.M,0),(0,r.M),(r.T,e),(e,2*r.T),(r.S,0),(r.S+r.T,e),(e,2*(r.S+r.T))⟩

private structure Pair (p : Fraction) (g G : Periods) : Prop where
  a : Image p g.a G.a
  b : Image p g.b G.b
  u : Image p g.u G.u
  v : Image p g.v G.v
  run : Image p g.runA G.runA
  fullU : Image p g.fullU G.fullU
  fullV : Image p g.fullV G.fullV

local macro "place" : tactic => `(tactic| (
  repeat' first | assumption | exact Image.zero _ | apply Image.add | apply Image.sub
                | apply Image.smul | apply Image.neg))

private theorem same (p : Fraction) (g G : Periods) (h : Pair p g G)
    (N : ℕ) (one long : Bool) (prev : ℤ) (i : Fin 10) :
    Projects p (diagram g N one prev long i.val) (vectorShape (diagram G N one prev long i.val)) := by
  obtain ⟨a,b,u,v,run,fu,fv⟩ := h
  have origin (o l : Bool) : Image p (g.origin o l) (G.origin o l) := by
    cases o <;> cases l <;> simp only [Periods.origin,Bool.false_eq_true,if_false,if_true] <;> place
  have center (o l : Bool) : Image p (g.center o l) (G.center o l) := by
    cases o <;> cases l <;> simp only [Periods.center,Bool.false_eq_true,if_false,if_true] <;> place
  have full (o s l : Bool) : Image p (g.full o s l) (G.full o s l) := by
    cases o <;> cases s <;> cases l <;> simp only [Periods.full,Bool.false_eq_true,if_false,if_true] <;> place
  have row (o s l : Bool) : Image p (g.row o s l) (G.row o s l) := by
    have := center o l
    cases o <;> cases s <;> simp only [Periods.row,Bool.false_eq_true,if_false,if_true] <;> place
  have bridge (o s l : Bool) : Image p (g.bridge o s l) (G.bridge o s l) := by
    have := center o l
    cases o <;> cases s <;> simp only [Periods.bridge,Bool.false_eq_true,if_false,if_true] <;> place
  have head (o t : Bool) : Image p (g.head o t) (G.head o t) := by
    cases o <;> cases t <;> simp only [Periods.head,Bool.false_eq_true,if_false,if_true] <;> place
  let o := decide (orientation one prev ≠ 1)
  have xl := origin o true
  have x := origin o long
  have h := head o (!one)
  have f := full o false long
  have f' := full o true long
  have s := row o false long
  have s' := row o true long
  have t := bridge o false long
  have t' := bridge o true long
  have oldU : Image p (if one then g.a-g.u else g.u) (if one then G.a-G.u else G.u) := by cases one <;> dsimp <;> place
  have oldB : Image p (if one then g.v-g.b else g.b-g.v) (if one then G.v-G.b else G.b-G.v) := by cases one <;> dsimp <;> place
  have sib : Image p (if one then g.u else g.a-g.u) (if one then G.u else G.a-G.u) := by cases one <;> dsimp <;> place
  dsimp only [o] at x xl h f f' s s' t t'
  fin_cases i
  all_goals simp only [diagram,vectorShape]
  all_goals try split
  all_goals constructor <;> place

private theorem table (r : Register) (one long : Bool) (prev : ℤ) (N : ℕ) (pos : 0<N)
    (S : r.S = (N : ℤ)*r.M) (i : Fin 10) :
    vectorShape (diagram (coordinates r (orientation one prev)) N one prev long i.val) =
      corrected r one prev long i.val := by
  have last : ((2*N-1 : ℕ) : ℤ)=2*(N : ℤ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2*N)]; push_cast; ring
  cases one <;> cases long
  all_goals fin_cases i
  all_goals
    simp [vectorShape,diagram,coordinates,corrected,Periods.full,Periods.origin,Periods.center,
      Periods.bridge,Periods.head,Periods.row,Prod.smul_mk,last,S]
  all_goals first | rfl | (apply Prod.ext <;> simp <;> ring) | ring

/-- Every physical row and column in the corrected diagram projects to its
named register entry, including the extra head in the elongated case. -/
theorem projects {p : Fraction} {r : Register} {g : Periods} {N : ℕ}
    (one long : Bool) (prev : ℤ) (F : Frame p r (orientation one prev) g N)
    (pos : 0 < N) (S : r.S=(N : ℤ)*r.M) (i : Fin 10) :
    Projects p (diagram g N one prev long i.val) (corrected r one prev long i.val) := by
  rw [←table r one long prev N pos S i]
  exact same p g _ ⟨F.a,F.b,F.u,F.v,F.runA,F.fullU,F.fullV⟩ N one long prev i

end FLatticePaper.Tiles.CorrectedPlacedDiagram
