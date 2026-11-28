import FLatticePaper.Tiles.CorrectedBaseEnds
import FLatticePaper.Tiles.CorrectedPlacedDiagram
import FLatticePaper.Tiles.CorrectedWordCoverage

/-! Twice the first register coordinate and the second coordinate on arbitrary physical sites. -/

namespace FLatticePaper.Tiles.CorrectedBaseProjection

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open CorrectedBaseEnds CorrectedRegisterDiagram CorrectedRegisterWords CorrectedEvenPlacement
open CorrectedPlacementFrames CorrectedWordCoverage CorrectedDomainLattice

def project (p : Fraction) : Site →+ Site where
  toFun := coords p
  map_zero' := by simp [coords]
  map_add' := coords_add p

def twice (z : Site) : Site := (2*z.1,z.2)
def ref (par : Bool) : Site := if par then (1,0) else 0

theorem faithful {p : Fraction} (pos : 0<scale p) : Function.Injective (project p) :=
  coords_injective _ (ne_of_gt pos)

theorem of_image {p : Fraction} {u v : Site} (h : Image p u v) : project p u=twice v := by
  change coords p u=_
  rw [coords_chart _ _ h.even,h.eqn]; rfl

/-- The chart of the representative, the four primitive displacements and the final column. -/
structure Reading (r : Register) (g : Periods) (e : ℤ) (N : ℕ) (z : Site) (par : Bool) : Prop where
  site : project ⟨r.n,r.d⟩ z=twice (r.X,r.Y)+project ⟨r.n,r.d⟩ (ref par)
  a : project ⟨r.n,r.d⟩ g.a=twice (r.M,0)
  b : project ⟨r.n,r.d⟩ g.b=twice (0,r.M)
  u : project ⟨r.n,r.d⟩ g.u=twice (r.T,e)
  v : project ⟨r.n,r.d⟩ g.v=twice (e,2*r.T)
  fullV : project ⟨r.n,r.d⟩ g.fullV=twice (e,2*(r.S+r.T))
  run : r.S=(N:ℤ)*r.M

theorem word (v w : Word) (one : Bool) (pre : stemPrefix v=w++[exit one]) (z : Site) :
    let P := parentsAt w
    let p := P.current .odd
    let r := register P one (length v) (chart p (representative z))
    Reading r (periods v) (orientation one (-P.odd.det P.even)) (length v) z (CorrectedCellsBands.oddSite z) := by
  intro P p r
  have F := CorrectedPlacementFrames.word v w one pre (chart p (representative z))
  refine ⟨?_,of_image F.a,of_image F.b,of_image F.u,of_image F.v,of_image F.fullV,rfl⟩
  have e := coords_chart p (representative z) (representative_even z)
  have eq : project p (representative z)=twice (r.X,r.Y) := e
  rw [←eq]
  change project p z=project p (z-ref (CorrectedCellsBands.oddSite z))+project p (ref (CorrectedCellsBands.oddSite z))
  rw [←map_add,sub_add_cancel]

theorem projected_end {r : Register} {g : Periods} {e : ℤ} {N : ℕ} {z : Site} {par : Bool}
    (h : Reading r g e N z par) (hn : 0<N) (long : Bool) :
    let m := 2*N-if long then 0 else 1
    project ⟨r.n,r.d⟩ ((m:ℤ) • g.b)=twice (0,2*r.S-(if long then 0 else r.M)) ∧
      ((m:ℤ)+1)*r.M=2*r.S+(if long then r.M else 0) := by
  intro m
  have k : (m:ℤ)=2*(N:ℤ)-(if long then 0 else 1) := by
    cases long <;> dsimp [m] <;> omega
  rw [map_zsmul,h.b,k,h.run]
  cases long <;> constructor
  all_goals first | (ext <;> dsimp [twice] <;> ring) | (dsimp; ring)

end FLatticePaper.Tiles.CorrectedBaseProjection
