import FLatticePaper.Tiles.BaseCorrectedThreeOneShortEvenSites
import FLatticePaper.Tiles.CorrectedBaseArithmetic
import FLatticePaper.Tiles.CorrectedBoundaryPoints

/-! Realization of every scale, lattice-gap and corner hypothesis of the base comparison. -/

namespace FLatticePaper.Tiles.BaseCorrectedThreeOneShortEvenSitesFrame

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open CorrectedRegisterDiagram CorrectedDomainLattice CorrectedRegisterWords CorrectedBaseArithmetic
open CorrectedBoundaryLattice CorrectedBoundaryPoints
private abbrev Hypotheses := FLatticePaper.Tiles.BaseCorrectedThreeOneShortEvenSites.Frame

private theorem frame (r : Register) (base : Three r true)
    (div : r.M ∣ r.S)
    (lat : ∀ i : ℕ, (corrected r true 1 false i).lattice r (-1) false 0) : Hypotheses r := by
  obtain ⟨size,denEven,num,nextDen,nextNum,turn,width,period,odd⟩ := base
  change r.f=r.d+1 at nextDen
  change 2*r.T=r.M+1*(r.d+1) at turn
  have hm : 0≤r.M := by omega
  constructor
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · have H := Shape.gap (lat 0) hm div 2 (0) (-1) (0)
    norm_num [corrected,Shape.probe,bias,displacement,FLatticePaper.Farey.mulI,orientation,Prod.smul_mk,Fin.ext_iff] at H
    omega
  · have H := Shape.gap (lat 0) hm div 2 (0) (0) (0)
    norm_num [corrected,Shape.probe,bias,displacement,FLatticePaper.Farey.mulI,orientation,Prod.smul_mk,Fin.ext_iff] at H
    omega
  · have H := Shape.gap (lat 2) hm div 0 (0) (-1) (0)
    norm_num [corrected,Shape.probe,bias,displacement,FLatticePaper.Farey.mulI,orientation,Prod.smul_mk,Fin.ext_iff] at H
    omega
  · have H := Shape.gap (lat 4) hm div 3 (0) (0) (0)
    norm_num [corrected,Shape.probe,bias,displacement,FLatticePaper.Farey.mulI,orientation,Prod.smul_mk,Fin.ext_iff] at H
    omega
  · have H := Shape.gap (lat 4) hm div 3 (0) (1) (0)
    norm_num [corrected,Shape.probe,bias,displacement,FLatticePaper.Farey.mulI,orientation,Prod.smul_mk,Fin.ext_iff] at H
    omega
  · have H := Shape.gap (lat 6) hm div 1 (0) (0) (0)
    norm_num [corrected,Shape.probe,bias,displacement,FLatticePaper.Farey.mulI,orientation,Prod.smul_mk,Fin.ext_iff] at H
    omega

/-- All the stated arithmetic hypotheses hold at every physical even representative of this run. -/
theorem at_word (j N : ℕ) (hn : 0<N) (z : Site) (hz : (z.1+z.2)%2=0) :
    let w := List.replicate (j+1) Digit.three
    let P := parentsAt w
    Hypotheses (register P true N (chart (P.current .odd) z)) := by
  intro w P
  let Z := chart (P.current .odd) z
  let r := register P true N Z
  have prev : -P.odd.det P.even=1 := by
    simp [P,w,BaseTileProps.parents_three,Fraction.det]
  have L (i : ℕ) := CorrectedRegisterLattice.word w true false false 0 N z hz i
  change ∀ i, (corrected r true (-P.odd.det P.even) false i).lattice r (orientation true (-P.odd.det P.even)) false 0 at L
  rw [prev] at L
  have div : r.M ∣ r.S := dvd_mul_left _ _

  exact frame r (three j N hn true Z) div L

end FLatticePaper.Tiles.BaseCorrectedThreeOneShortEvenSitesFrame
