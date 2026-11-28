import FLatticePaper.Tiles.CorrectedRegisterLattice

/-! The mixed alternate parents in the two head polygons of a corrected column. -/

namespace FLatticePaper.Tiles.CorrectedMixedDiagram

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open CorrectedRegisterDiagram CorrectedRegisterWords CorrectedRegisterLattice CorrectedDomainLattice

/-- The two target polygons (indices zero and nine) and the six or eight source
polygons in the decomposition of a mixed alternate child. -/
def mixed (r : Register) (one : Bool) (prev : ℤ) (even : Bool) (i : ℕ) : Shape :=
  let e := orientation one prev
  let a : Site := (r.M,0)
  let b : Site := (0,r.M)
  let u : Site := (r.T,e)
  let v : Site := (e,2*r.T)
  let oldU := if one then a-u else u
  let oldB := if one then v-b else b-v
  let full (c : Site) := Shape.mk c (a+u) (b+v) 0 0
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

theorem from_periods (one even : Bool) (i : ℕ) : FromPeriods one (fun r prev => mixed r one prev even i) := by
  intro L r prev ha hb hu hv _ _
  change Placed L (mixed r one prev even i)
  by_cases h₀ : i=0
  · simp only [mixed,h₀,if_true]
    exact ⟨L.zero_mem,L.add_mem ha hu,L.add_mem hb hv,L.zero_mem,L.zero_mem⟩
  by_cases h₉ : i=9
  · simp only [mixed,h₉,if_true]
    exact ⟨L.add_mem hb (L.zsmul_mem hu _),L.add_mem ha hu,L.add_mem hb hv,L.zero_mem,L.zero_mem⟩
  cases even <;> simp only [mixed,h₀,h₉,if_false,if_true,Bool.false_eq_true]
  all_goals split <;> constructor
  all_goals dsimp only
  all_goals
    repeat' first
      | assumption
      | exact L.zero_mem
      | apply L.add_mem
      | apply L.sub_mem
      | apply L.zsmul_mem
      | split

/-- Every physical probe of either mixed alternate polygon and its pieces is a register-lattice site. -/
theorem word (w : Word) (one even par : Bool) (sec : Fin 3) (z : Site) (hz : (z.1+z.2)%2=0) (i : ℕ) :
    let P := parentsAt w
    let prev := -P.odd.det P.even
    let r := register P one 1 (chart (P.current .odd) z)
    (mixed r one prev even i).lattice r (orientation one prev) par sec :=
  CorrectedRegisterLattice.from_periods w one par sec 1 z hz (fun r prev => mixed r one prev even i) (from_periods one even i)

end FLatticePaper.Tiles.CorrectedMixedDiagram
