import FLatticePaper.Tiles.CorrectedLevelTests
import FLatticePaper.Tiles.CorrectedDomainLattice

/-! The polygons of the corrected decomposition in the coordinates of its odd register. -/

namespace FLatticePaper.Tiles.CorrectedRegisterDiagram

open FLatticePaper.Farey FLatticePaper.Construction CorrectedLevelTests

/-- The period scale, the mixed period, the run length in scaled units, the two
fractions, and the coordinates of the reference site. -/
structure Register where
  M : ℤ
  T : ℤ
  S : ℤ
  d : ℤ
  n : ℤ
  f : ℤ
  g : ℤ
  X : ℤ
  Y : ℤ

/-- An ordinary or lengthened polygon, described by its initial corner, the two
primitive sides, and the two displacements of its outer edges. -/
structure Shape where
  corner : Site
  a : Site
  b : Site
  extraA : Site := 0
  extraB : Site := 0

/-- A reference probe before giving the upper and right faces their inward orientation. -/
structure Probe where
  w : ℤ
  v : ℤ
  width : ℤ
  slope : ℤ

def Probe.line (q : Probe) (reverse : Bool) : Line :=
  let w := if reverse then -q.w else q.w
  let v := if reverse then -q.v else q.v
  if q.slope=0 then .flat w else .sloped w q.width (q.slope*v)

/-- Projection of a fixed displacement of even checkerboard parity. -/
def displacement (r : Register) (p : Site) : Site :=
  (((p.1+p.2)/2)*r.d+((p.1-p.2)/2)*r.n, p.2*r.d-p.1*r.n)

theorem displacement_eq (r : Register) (p : Site) (hp : (p.1+p.2)%2=0) :
    displacement r p = CorrectedDomainLattice.chart ⟨r.n,r.d⟩ p := by
  have h := CorrectedDomainLattice.twice_first ⟨r.n,r.d⟩ p hp
  have a : 2*((p.1+p.2)/2)=p.1+p.2 := by omega
  have b : 2*((p.1-p.2)/2)=p.1-p.2 := by omega
  apply Prod.ext
  · change ((p.1+p.2)/2)*r.d+((p.1-p.2)/2)*r.n=_
    dsimp only at h
    linarith only [h,congrArg (·*r.d) a,congrArg (·*r.n) b]
  · dsimp [displacement,CorrectedDomainLattice.chart]; ring

/-- The four fixed displacements from the checkerboard reference point in a sector. -/
def bias (par : Bool) (sector : Fin 3) (i : Fin 4) : Site :=
  let ref : Site := if par then (1,0) else 0
  let h : Site := if par then (0,1) else if sector=0 then (1,1) else (-2,0)
  let v : Site := if !par then (0,1) else if sector=2 then (1,1) else (-2,0)
  match i.val with
  | 0 => ref+h
  | 1 => ref+((-1,1):Site)-h
  | 2 => ref-((1,0):Site)-mulI v
  | _ => ref+((0,1):Site)+mulI v

/-- The signed distances and transverse coordinates of the bottom, top, left and right lines. -/
def Shape.probe (s : Shape) (r : Register) (par : Bool) (sector : Fin 3) (i : Fin 4) : Probe :=
  let z : Site := (r.X,r.Y)-s.corner+displacement r (bias par sector i)
  match i.val with
  | 0 => ⟨z.2,z.1,s.a.1,s.a.2⟩
  | 1 =>
    let u := z-s.b-s.extraB
    ⟨u.2,u.1,s.a.1,s.a.2⟩
  | 2 => ⟨z.1,z.2,s.b.2,s.b.1⟩
  | _ =>
    let u := z-s.a-s.extraA
    ⟨u.1,u.2,s.b.2,s.b.1⟩

def Shape.line (s : Shape) (r : Register) (par : Bool) (sector : Fin 3) (i : Fin 4) : Line :=
  (s.probe r par sector i).line (decide (i.val%2=1))

/-- The four finite tests on a point of the register. -/
def Shape.contains (s : Shape) (r : Register) (par : Bool) (sector : Fin 3) : Prop :=
  ∀ i, (s.line r par sector i).holds

/-- A probe comes from an even physical displacement. The register covolume divides the
indicated combination in its horizontal or vertical reading. -/
def Shape.lattice (s : Shape) (r : Register) (e : ℤ) (par : Bool) (sector : Fin 3) : Prop :=
  ∀ i, let q := s.probe r par sector i
       r.M ∣ q.v-(if i.val<2 then e else 2*e)*q.w*r.T

/-- No such probe can lie strictly between two adjacent multiples of the period scale. -/
theorem probe_gap (M S T e w v : ℤ) (hm : 0 ≤ M) (hs : M ∣ S) (hv : M ∣ v-e*w*T)
    (l j k : ℤ) :
    l < w ∨ w < l ∨ v-e*l*T ≤ k*S+j*M ∨ k*S+(j+1)*M ≤ v-e*l*T := by
  rcases lt_trichotomy l w with h|rfl|h
  · exact Or.inl h
  · right; right
    obtain ⟨s,hs⟩ := hs
    obtain ⟨t,ht⟩ := hv
    by_cases h : t ≤ k*s+j
    · left
      have a := mul_le_mul_of_nonneg_left h hm
      rw [ht,hs]
      linarith only [a]
    · right
      have a := mul_le_mul_of_nonneg_left (show k*s+j+1 ≤ t by omega) hm
      rw [ht,hs]
      linarith only [a]
  · exact Or.inr (Or.inl h)

theorem Shape.gap {s : Shape} {r : Register} {e : ℤ} {par : Bool} {sector : Fin 3}
    (h : s.lattice r e par sector) (hm : 0 ≤ r.M) (hs : r.M ∣ r.S) (i : Fin 4) (l j k : ℤ) :
    let q := s.probe r par sector i
    let t := q.v-(if i.val<2 then e else 2*e)*l*r.T
    l < q.w ∨ q.w < l ∨ t ≤ k*r.S+j*r.M ∨ k*r.S+(j+1)*r.M ≤ t :=
  probe_gap _ _ _ _ _ _ hm hs (h i) l j k

theorem period_gap {r : Register} (hm : 0 ≤ r.M) (hs : r.M ∣ r.S) (j k : ℤ) :
    r.S ≤ k*r.S+j*r.M ∨ k*r.S+(j+1)*r.M ≤ r.S := by
  simpa using probe_gap r.M r.S 0 0 0 r.S hm hs (by simpa using hs) 0 j k

def orientation (one : Bool) (previous : ℤ) : ℤ := if one then -previous else previous

/-- The two previous horizontal periods in physical coordinates. -/
def oldOdd (r : Register) (one : Bool) : Site :=
  if one then (2*r.f-2*r.d,2*r.g-2*r.n) else (2*r.d-2*r.f,2*r.n-2*r.g)

def oldEven (r : Register) (one : Bool) : Site :=
  if one then (2*r.d-r.f,2*r.n-r.g) else (r.f,r.g)

/-- The common closed sector occupied by both old periods. -/
def inSector (s : Fin 3) (z : Site) : Prop :=
  (if s=0 then 3*z.2 ≤ z.1 else if s=1 then z.1 ≤ 3*z.2 else True) ∧
  (if s=1 then 2*z.2 ≤ z.1 else if s=2 then z.1 ≤ 2*z.2 else True)

/-- Bounds in a general register, before specializing its sign, sector or physical parity. -/
structure Regular (r : Register) (one : Bool) (sector : Fin 3) : Prop where
  num : 1 ≤ r.n
  den : 1 ≤ r.d-r.n
  scale : 7 ≤ r.M
  run : r.M ≤ r.S
  oddX : 4 ≤ (oldOdd r one).1
  oddY : 2 ≤ (oldOdd r one).2
  oddDiff : 2 ≤ (oldOdd r one).1-(oldOdd r one).2
  evenX : 3 ≤ (oldEven r one).1
  evenY : 1 ≤ (oldEven r one).2
  evenDiff : 2 ≤ (oldEven r one).1-(oldEven r one).2
  oddSize : 4*(r.d+r.n)+2*(r.d-r.n) ≤ 2*(if one then 2*r.T-r.M else r.M-2*r.T)
  evenSize : 3*(r.d+r.n)+(r.d-r.n) ≤ 2*(if one then r.M-r.T else r.T)
  oddSector : inSector sector (oldOdd r one)
  evenSector : inSector sector (oldEven r one)
  oddParity : (r.d+r.n)%2=1
  evenDenParity : r.f%2=1
  evenNumParity : r.g%2=1
  scaleParity : r.M%2=1

/-- The finite inequalities supplied by an inward or outward reading of a face. -/
def Shape.bounds (s : Shape) (r : Register) (par : Bool) (sec : Fin 3) (i : Fin 4) (inside : Bool) : Prop :=
  ∀ j : Fin 10, (s.line r par sec i).fact inside j.val

theorem Shape.inside_bounds (s : Shape) (r : Register) (par : Bool) (sec : Fin 3)
    (ok : ∀ i, (s.line r par sec i).valid) (h : s.contains r par sec) :
    ∀ i, s.bounds r par sec i true := by
  intro i j
  exact Line.facts _ (ok i) true (h i) j.val (by omega)

theorem Shape.outside_bounds (s : Shape) (r : Register) (par : Bool) (sec : Fin 3)
    (ok : ∀ i, (s.line r par sec i).valid) (h : ¬s.contains r par sec) :
    s.bounds r par sec 0 false ∨ s.bounds r par sec 1 false ∨
    s.bounds r par sec 2 false ∨ s.bounds r par sec 3 false := by
  change ¬ ∀ i, _ at h
  obtain ⟨i,hi⟩ := Classical.not_forall.mp h
  have b : s.bounds r par sec i false :=
    fun j => Line.facts _ (ok i) false hi j.val (by omega)
  fin_cases i <;> tauto

/-- The target or a named piece of the corrected diagram.
Indices one and two are the full tiles, three and four are the complete stem rows,
five and six are the bridges, and seven and eight are the two head polygons.
Index zero is the target, with index nine the second target in the elongated case. -/
def corrected (r : Register) (one : Bool) (previous : ℤ) (long : Bool) (i : ℕ) : Shape :=
  let e := orientation one previous
  let a : Site := (r.M,0)
  let b : Site := (0,r.M)
  let u : Site := (r.T,e)
  let v : Site := (e,2*r.T)
  let fullU : Site := (r.S+r.T,e)
  let fullV : Site := (e,2*(r.S+r.T))
  let run : Site := (r.S,0)
  let ext := if long then b else 0
  let center := a+b+fullV+(if e=1 then 0 else u+u)
  let start := if e=1 then u else -run
  let bridge := if e=1 then 0 else a
  let head := if e=1 then (if one then a+b-u else v) else (if one then b+u else u+u+v)
  let sib := if one then u else a-u
  let oldU := if one then a-u else u
  let oldB := if one then v-b else b-v
  let extra : Site := (0,if long then 2*r.S else 2*r.S-r.M)
  let origin := if e=1 then 0 else -run
  match i with
  | 0 => if long then ⟨origin,a+fullU,b+fullV,0,0⟩
         else ⟨if e=1 then -fullU else -run,a+fullU+fullU,b+fullV,0,0⟩
  | 1 => ⟨if e=1 then a+b else b-run,fullU,fullV,0,0⟩
  | 2 => ⟨(if e=1 then -fullU else a+u)+ext,fullU,fullV,0,0⟩
  | 3 => ⟨start,a,b,run,0⟩
  | 4 => ⟨center-a-b-start-run+ext,a,b,run,0⟩
  | 5 => ⟨bridge,u,v,0,0⟩
  | 6 => ⟨center-u-v-bridge+ext,u,v,0,0⟩
  | 7 => ⟨head,sib,b,0,extra⟩
  | 8 => ⟨head+oldB+previous • oldU,sib,b,0,extra⟩
  | _ => ⟨origin+b-e • fullU,a+fullU,b+fullV,0,0⟩

end FLatticePaper.Tiles.CorrectedRegisterDiagram
