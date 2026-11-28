import FLatticePaper.Tiles.BaseMixedThreeOneEvenEvenSitesPolygons
import FLatticePaper.Tiles.CorrectedMixedBasePlacement

/-! The alternate child at actual sites of its first exit from a positive pure run. -/

namespace FLatticePaper.Tiles.BaseMixedThreeOneEvenEvenSitesChild

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open Standard LCorrecProps PaperAltBase CorrectedFiniteFaces
open CorrectedMixedBasePlacement CorrectedMixedSources CorrectedCellsBands
open FLatticePaper.Tiles.BaseMixedThreeOneEvenEvenSites (Register Frame test contains)
open FLatticePaper.Tiles.BaseMixedThreeOneEvenEvenSitesPolygons (shape physicalSite)

private theorem placed_fin (d : ℤ) (i : Fin 10) (used : i.val≠7 ∧ i.val≠8) :
    entry true true true d i.val=shape d i.val := by
  fin_cases i
  all_goals first | (exfalso; exact used.1 rfl) | (exfalso; exact used.2 rfl) | skip
  all_goals simp [entry,CorrectedMixedPlacement.layout,CorrectedRegisterDiagram.orientation,axisA,axisB,axisU,axisV,shape]
  all_goals norm_num [Prod.ext_iff]; omega

private theorem placed (d : ℤ) (i : ℕ) (valid : i<10 ∧ i≠7 ∧ i≠8) :
    entry true true true d i=shape d i := placed_fin d ⟨i,valid.1⟩ valid.2

private theorem component10 (r : Register) : contains r 10 ↔ 0 ≤ (r.X-r.Y-2) ∧ 0 ≤ (-r.X+r.Y+2) ∧ 0 ≤ (-r.d+r.Y-2) ∧ 0 ≤ (r.d-r.Y+2) ∧ (0 ≤ (r.d-r.X+r.Y+2) ∨ 0 ≤ (-r.d+r.Y-4)) ∧ (0 ≤ (r.X-r.Y-3) ∨ 0 ≤ (2*r.d-r.Y+3)) := by
  constructor
  · intro h
    change ∀ j : Fin 6, (test r 10 j.val).holds at h
    have c0 := h 0
    change 0 ≤ (r.X-r.Y-2) at c0
    have c1 := h 1
    change 0 ≤ (-r.X+r.Y+2) at c1
    have c2 := h 2
    change 0 ≤ (-r.d+r.Y-2) at c2
    have c3 := h 3
    change 0 ≤ (r.d-r.Y+2) at c3
    have c4 := h 4
    change (0 ≤ (r.d-r.X+r.Y+2) ∨ 0 ≤ (-r.d+r.Y-4)) at c4
    have c5 := h 5
    change (0 ≤ (r.X-r.Y-3) ∨ 0 ≤ (2*r.d-r.Y+3)) at c5
    exact ⟨c0, c1, c2, c3, c4, c5⟩
  · intro h j
    change Fin 6 at j
    fin_cases j
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2.1
    · exact h.2.2.2.2.1
    · exact h.2.2.2.2.2

private theorem component11 (r : Register) : contains r 11 ↔ 0 ≤ (-r.d+r.X-r.Y-3) ∧ 0 ≤ (r.d-r.X+r.Y+3) ∧ 0 ≤ (-2*r.d+r.Y-5) ∧ 0 ≤ (2*r.d-r.Y+5) ∧ (0 ≤ (r.d-r.X+r.Y+2) ∨ 0 ≤ (-r.d+r.Y-4)) ∧ (0 ≤ (r.X-r.Y-3) ∨ 0 ≤ (2*r.d-r.Y+3)) := by
  constructor
  · intro h
    change ∀ j : Fin 6, (test r 11 j.val).holds at h
    have c0 := h 0
    change 0 ≤ (-r.d+r.X-r.Y-3) at c0
    have c1 := h 1
    change 0 ≤ (r.d-r.X+r.Y+3) at c1
    have c2 := h 2
    change 0 ≤ (-2*r.d+r.Y-5) at c2
    have c3 := h 3
    change 0 ≤ (2*r.d-r.Y+5) at c3
    have c4 := h 4
    change (0 ≤ (r.d-r.X+r.Y+2) ∨ 0 ≤ (-r.d+r.Y-4)) at c4
    have c5 := h 5
    change (0 ≤ (r.X-r.Y-3) ∨ 0 ≤ (2*r.d-r.Y+3)) at c5
    exact ⟨c0, c1, c2, c3, c4, c5⟩
  · intro h j
    change Fin 6 at j
    fin_cases j
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2.1
    · exact h.2.2.2.2.1
    · exact h.2.2.2.2.2

private theorem component12 (r : Register) : contains r 12 ↔ 0 ≤ (r.X-r.Y-4) ∧ 0 ≤ (r.d-r.X+r.Y+1) ∧ 0 ≤ (-2*r.d+r.X-6) ∧ 0 ≤ (2*r.d-r.X+6) ∧ (0 ≤ (r.d-r.X+r.Y+2) ∨ 0 ≤ (-r.d+r.Y-4)) ∧ (0 ≤ (r.X-r.Y-3) ∨ 0 ≤ (2*r.d-r.Y+3)) := by
  constructor
  · intro h
    change ∀ j : Fin 6, (test r 12 j.val).holds at h
    have c0 := h 0
    change 0 ≤ (r.X-r.Y-4) at c0
    have c1 := h 1
    change 0 ≤ (r.d-r.X+r.Y+1) at c1
    have c2 := h 2
    change 0 ≤ (-2*r.d+r.X-6) at c2
    have c3 := h 3
    change 0 ≤ (2*r.d-r.X+6) at c3
    have c4 := h 4
    change (0 ≤ (r.d-r.X+r.Y+2) ∨ 0 ≤ (-r.d+r.Y-4)) at c4
    have c5 := h 5
    change (0 ≤ (r.X-r.Y-3) ∨ 0 ≤ (2*r.d-r.Y+3)) at c5
    exact ⟨c0, c1, c2, c3, c4, c5⟩
  · intro h j
    change Fin 6 at j
    fin_cases j
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2.1
    · exact h.2.2.2.2.1
    · exact h.2.2.2.2.2

private theorem component13 (r : Register) : contains r 13 ↔ 0 ≤ (r.d+r.X-r.Y-4) ∧ 0 ≤ (2*r.d-r.X+r.Y+1) ∧ 0 ≤ (-r.d+r.Y-2) ∧ 0 ≤ (2*r.d-r.Y+5) ∧ 0 ≤ (-r.d+r.X-5) ∧ 0 ≤ (3*r.d-r.X+7) ∧ (0 ≤ (r.d-r.X+r.Y+2) ∨ 0 ≤ (-r.d+r.Y-4)) ∧ (0 ≤ (r.X-r.Y-3) ∨ 0 ≤ (2*r.d-r.Y+3)) := by
  constructor
  · intro h
    change ∀ j : Fin 8, (test r 13 j.val).holds at h
    have c0 := h 0
    change 0 ≤ (r.d+r.X-r.Y-4) at c0
    have c1 := h 1
    change 0 ≤ (2*r.d-r.X+r.Y+1) at c1
    have c2 := h 2
    change 0 ≤ (-r.d+r.Y-2) at c2
    have c3 := h 3
    change 0 ≤ (2*r.d-r.Y+5) at c3
    have c4 := h 4
    change 0 ≤ (-r.d+r.X-5) at c4
    have c5 := h 5
    change 0 ≤ (3*r.d-r.X+7) at c5
    have c6 := h 6
    change (0 ≤ (r.d-r.X+r.Y+2) ∨ 0 ≤ (-r.d+r.Y-4)) at c6
    have c7 := h 7
    change (0 ≤ (r.X-r.Y-3) ∨ 0 ≤ (2*r.d-r.Y+3)) at c7
    exact ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩
  · intro h j
    change Fin 8 at j
    fin_cases j
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2.1
    · exact h.2.2.2.2.1
    · exact h.2.2.2.2.2.1
    · exact h.2.2.2.2.2.2.1
    · exact h.2.2.2.2.2.2.2

set_option maxHeartbeats 400000 in
private theorem boundary (r : Register) (h : Frame r) :
    physicalSite r∈extra true true true r.d ↔ contains r 10 ∨ contains r 11 ∨ contains r 12 ∨ contains r 13 := by
  have d := h.f0
  rw [component10,component11,component12,component13]
  simp only [extra,axisA,axisB,axisU,axisV,physicalSite,if_true,mem_shift,
    stairAltF,nearStairAltF,ladderAltF,nearLadderAltF,boxF,Finset.mem_filter,Finset.mem_product,Finset.mem_Icc,
    Prod.ext_iff,Prod.fst_sub,Prod.snd_sub,Prod.fst_add,Prod.snd_add]
  all_goals omega

private theorem comparison (r : Register) (h : Frame r) :
    (six (fun i => (entry true true true r.d i).mem (physicalSite r)) ∨ physicalSite r∈extra true true true r.d) ↔
      (entry true true true r.d 0).mem (physicalSite r) ∨ (entry true true true r.d 9).mem (physicalSite r) := by
  unfold six
  dsimp only
  rw [placed r.d 1 (by decide), BaseMixedThreeOneEvenEvenSitesPolygons.polygon1 r h, placed r.d 2 (by decide), BaseMixedThreeOneEvenEvenSitesPolygons.polygon2 r h, placed r.d 3 (by decide), BaseMixedThreeOneEvenEvenSitesPolygons.polygon3 r h, placed r.d 4 (by decide), BaseMixedThreeOneEvenEvenSitesPolygons.polygon4 r h, placed r.d 5 (by decide), BaseMixedThreeOneEvenEvenSitesPolygons.polygon5 r h, placed r.d 6 (by decide), BaseMixedThreeOneEvenEvenSitesPolygons.polygon6 r h, placed r.d 0 (by decide), BaseMixedThreeOneEvenEvenSitesPolygons.polygon0 r h, placed r.d 9 (by decide), BaseMixedThreeOneEvenEvenSitesPolygons.polygon9 r h, boundary r h]
  have eq := (BaseMixedThreeOneEvenEvenSites.coverage r h).symm
  tauto

/-- The actual two-polygon membership equivalence on this parity of physical sites. -/
theorem at_word (k : ℕ) (z : Site) (p : oddSite z=false) :
    let t := child true true k
    let e := -(parentsAt t).odd.det (parentsAt t).even
    let A := JointFamily.vP1 t+JointFamily.vQ1 t
    let B := JointFamily.vP2 t+JointFamily.vQ2 t
    z∈(if true then altEvenT t else altOddT t) ↔ Band A B 0 0 z ∨
      Band A B 0 0 (z-(JointFamily.vP2 t+(if true then -e else e) • JointFamily.vQ1 t)) := by
  let r : Register := ⟨size true k,z.1+z.2,z.2⟩
  have F : Frame r := by
    have pp := p
    simp [oddSite] at pp
    constructor <;> dsimp [r,size] <;> omega
  have site : physicalSite r=z := by ext <;> dsimp [physicalSite,r]; ring
  apply CorrectedMixedBasePlacement.at_site true true true k (by decide) z
  have C := comparison r F
  simpa only [site] using C

end FLatticePaper.Tiles.BaseMixedThreeOneEvenEvenSitesChild
