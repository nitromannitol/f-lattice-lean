import FLatticePaper.Tiles.CorrectedBaseProjection
import FLatticePaper.Tiles.CorrectedBaseHeadPlacement
import FLatticePaper.Tiles.CorrectedPureBridges

/-! The exceptional end tests in the same integral coordinates as the corrected polygons. -/

namespace FLatticePaper.Tiles.BaseCorrectedThreeOneShortEvenSitesBoundary

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles Standard
open CorrectedRegisterDiagram CorrectedEvenPlacement CorrectedBaseProjection CorrectedBaseHeadPlacement

theorem ends (r : Register) (g : Periods) (N : ℕ) (hn : 0<N) (z : Site) (h : Reading r g (-1) N z false) (pos : 0<CorrectedDomainLattice.scale ⟨r.n,r.d⟩) :
    holes g true (copies N false) z ↔ (0 ≤ (4*r.T-r.d+r.n-2*r.X-1) ∨ 0 ≤ (-4*r.T+r.d-r.n+2*r.X-1) ∨ 0 ≤ (r.M-r.d-r.Y-3) ∨ 0 ≤ (-r.M+r.d+r.Y+1)) ∧ (0 ≤ (2*r.T-r.X-1) ∨ 0 ≤ (-2*r.T+r.X-1) ∨ 0 ≤ (r.M-r.Y-3) ∨ 0 ≤ (-r.M+r.Y+1)) ∧ (0 ≤ (2*r.T-r.d-r.n-r.X-1) ∨ 0 ≤ (-2*r.T+r.d+r.n+r.X-1) ∨ 0 ≤ (r.M+2*r.S+2*r.n-r.Y-3) ∨ 0 ≤ (-r.M-2*r.S-2*r.n+r.Y+1)) ∧ (0 ≤ (4*r.T-r.d-3*r.n-2*r.X-1) ∨ 0 ≤ (-4*r.T+r.d+3*r.n+2*r.X-1) ∨ 0 ≤ (r.M+2*r.S+r.d+2*r.n-r.Y-3) ∨ 0 ≤ (-r.M-2*r.S-r.d-2*r.n+r.Y+1)) := by
  have different (u : Site) : z≠u ↔ project ⟨r.n,r.d⟩ z≠project ⟨r.n,r.d⟩ u := not_congr (faithful pos).eq_iff.symm
  have last := (projected_end h hn false).1
  change project ⟨r.n,r.d⟩ (((copies N false):ℤ) • g.b)=_ at last
  unfold holes
  simp only [different]
  simp only [lower,upper,start,Bool.false_eq_true,if_false,if_true,map_add,last,h.site,h.b,h.u]
  norm_num [ref,twice,project,CorrectedBaseEnds.coords,Prod.ext_iff]
  omega

end FLatticePaper.Tiles.BaseCorrectedThreeOneShortEvenSitesBoundary
