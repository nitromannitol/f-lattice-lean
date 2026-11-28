import FLatticePaper.Tiles.CorrectedPlacedSectors
import FLatticePaper.Tiles.CorrectedWordCoverage

/-! Physical corners and lattice projections for the alternate polygons needed at a corrected head. -/

namespace FLatticePaper.Tiles.CorrectedMixedPlacement

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles Standard
open CorrectedEvenPlacement CorrectedPlacementFrames CorrectedPlacedDiagram CorrectedPhysicalFaces
open CorrectedRegisterDiagram CorrectedRegisterWords CorrectedWordCoverage CorrectedDomainLattice

/-- The two alternate targets and all standard and alternate parent polygons in their original tile coordinates. -/
def layout (a b u v : Site) (one : Bool) (prev : ℤ) (even : Bool) (i : ℕ) : Block :=
  let e := orientation one prev
  let oldU := if one then a-u else u
  let oldB := if one then v-b else b-v
  let full (c : Site) := Block.mk c (a+u) (b+v) 0 0
  if i=0 then full 0 else if i=9 then full (b+(if even then -e else e) • u) else
  if even then
    let p₀ := if e=1 then u else 0
    let p₁ := if e=1 then b+v-u else b+v+u+u
    let q₀ := if e=1 then 0 else a
    let q₁ := if e=1 then a+b else b
    let gap := if e=1 then b-u else b+u
    let h := if e=1 then (if one then a+b-u else v) else (if one then b+u else u+u+v)
    let sib := if one then u else a-u
    match i with
    | 1 => ⟨p₀,a,b,0,0⟩
    | 2 => ⟨p₁,a,b,0,0⟩
    | 3 => ⟨q₀,u,v,0,0⟩
    | 4 => ⟨q₀+gap,u,v,0,0⟩
    | 5 => ⟨q₁,u,v,0,0⟩
    | 6 => ⟨q₁+gap,u,v,0,0⟩
    | 7 => ⟨h,sib,b,0,0⟩
    | _ => ⟨h+oldB+prev • oldU,sib,b,0,0⟩
  else
    let q₀ := if e=1 then 0 else a
    let q₁ := if e=1 then a+b+b+u else b+b-u
    let p₀ := if e=1 then u else 0
    let p₁ := if e=1 then v else u+v
    let gap := if e=1 then b+u else b-u
    let h := if e=1 then b+u else b+a-u
    match i with
    | 1 => ⟨q₀,u,v,0,0⟩
    | 2 => ⟨q₁,u,v,0,0⟩
    | 3 => ⟨p₀,a,b,0,0⟩
    | 4 => ⟨p₀+gap,a,b,0,0⟩
    | 5 => ⟨p₁,a,b,0,0⟩
    | 6 => ⟨p₁+gap,a,b,0,0⟩
    | 7 => ⟨h,u,b,0,0⟩
    | _ => ⟨h+oldB-prev • oldU,u,b,0,0⟩

theorem stem_at_exit (w : Word) (one : Bool) : stemPrefix (w++[exit one])=w++[exit one] := by
  cases one <;> rw [stemPrefix,JointRot.stripTrailing_snoc] <;> rfl

theorem run (w : Word) (one : Bool) : length (w++[exit one])=1 := by
  cases one <;> rw [length,JointRot.trailingCount_snoc] <;> rfl

local macro "place" : tactic => `(tactic| (
  repeat' first | assumption | exact Image.zero _ | apply Image.add | apply Image.sub
                | apply Image.smul | apply Image.neg | split))

private def shapeOf (b : Block) : Shape := ⟨b.c,b.a,b.b,0,0⟩

private theorem images (p : Fraction) (a b u v A B U V : Site)
    (a' : Image p a A) (b' : Image p b B) (u' : Image p u U) (v' : Image p v V)
    (one even : Bool) (prev : ℤ) (i : Fin 10) :
    Projects p (layout a b u v one prev even i.val) (shapeOf (layout A B U V one prev even i.val)) := by
  fin_cases i <;> cases even
  all_goals constructor <;> dsimp [layout,shapeOf] <;> try simp only [Nat.cast_zero,zero_smul]
  all_goals place

/-- Each physical polygon has exactly the projected corner and sides of its register entry. -/
theorem projects (p : Fraction) (r : Register) (g : Periods) (one even : Bool) (prev : ℤ)
    (F : Frame p r (orientation one prev) g 1) (i : Fin 10) :
    Projects p (layout g.a g.b g.u g.v one prev even i.val) (CorrectedMixedDiagram.mixed r one prev even i.val) := by
  have h := images p _ _ _ _ _ _ _ _ F.a F.b F.u F.v one even prev i
  convert h using 1
  fin_cases i <;> cases even <;> rfl

private theorem aligned_add {s : Fin 3} {a b u v : Site} (P : Aligned a b s) (Q : Aligned u v s) :
    Aligned (a+u) (b+v) s := by
  obtain ⟨A,B⟩ := P
  obtain ⟨U,V⟩ := Q
  constructor
  · split_ifs at A U ⊢ <;> dsimp <;> omega
  · split_ifs at B V ⊢ <;> dsimp <;> omega

private theorem sector (s : Fin 3) (a b u v : Site) (one even : Bool) (prev : ℤ) (i : Fin 10)
    (A : Aligned a b s) (U : Aligned u v s) (S : Aligned (if one then u else a-u) b s) :
    Aligned (layout a b u v one prev even i.val).a (layout a b u v one prev even i.val).b s := by
  have K := aligned_add A U
  have J : Aligned u b s := ⟨U.1,A.2⟩
  fin_cases i <;> cases even <;> dsimp [layout] <;> assumption

/-- Every edge of an alternate source uses the sector of the first letter of the preceding word. -/
theorem aligned (x : Digit) (xs : Word) (one even : Bool) (prev : ℤ) (i : Fin 10) :
    let g := periods ((x::xs)++[exit one])
    let q := layout g.a g.b g.u g.v one prev even i.val
    Aligned q.a q.b (firstSector x) := by
  let w := x::xs
  let t := w++[exit one]
  let g := periods t
  let s := firstSector x
  have pre := stem_at_exit w one
  have A : Aligned g.a g.b s := CorrectedPlacedSectors.word x xs t one false prev pre 3
  have U : Aligned g.u g.v s := CorrectedPlacedSectors.word x xs t one false prev pre 5
  have S : Aligned (if one then g.u else g.a-g.u) g.b s := CorrectedPlacedSectors.word x xs t one false prev pre 7
  exact sector s g.a g.b g.u g.v one even prev i A U S

/-- The word comparison in register coordinates is equivalent to the physical comparison at the given site. -/
theorem physical (x : Digit) (xs : Word) (hw : ¬ IsBase (x::xs)) (one even : Bool) (z : Site) :
    let P := parentsAt (x::xs)
    let p := P.current .odd
    let prev := -P.odd.det P.even
    let r := register P one 1 (chart p (representative z))
    let shape := CorrectedMixedDiagram.mixed r one prev even
    let g := periods ((x::xs)++[exit one])
    let count := if one || even then 8 else 6
    Covers (fun i => CorrectedRegisterFaces.exact ((shape i).probe r (CorrectedCellsBands.oddSite z) (firstSector x))) true count ↔
    Covers (fun i => (layout g.a g.b g.u g.v one prev even i).mem z) true count := by
  intro P p prev r shape g count
  have reg := regular x xs hw one 1 (by decide) (chart p (representative z))
  have hm : 0<scale p := lt_of_lt_of_le (by decide : (0:ℤ)<7) reg.scale
  let t := (x::xs)++[exit one]
  have F := CorrectedPlacementFrames.word t (x::xs) one (stem_at_exit _ one) (chart p (representative z))
  dsimp only at F
  rw [show length t=1 from run _ _] at F
  refine (congr_cover true (show count≤8 by dsimp [count]; split <;> decide) fun i => ?_).symm
  exact (projects p r g one even prev F i).band_iff z (firstSector x) (aligned x xs one even prev i) hm rfl

end FLatticePaper.Tiles.CorrectedMixedPlacement
