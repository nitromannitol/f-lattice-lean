import FLatticePaper.Tiles.BaseMixedThreeOneOddEvenSitesPolygons
import FLatticePaper.Tiles.CorrectedMixedBasePlacement

/-! The alternate child at actual sites of its first exit from a positive pure run. -/

namespace FLatticePaper.Tiles.BaseMixedThreeOneOddEvenSitesChild

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open Standard LCorrecProps PaperAltBase CorrectedFiniteFaces
open CorrectedMixedBasePlacement CorrectedMixedSources CorrectedCellsBands
open FLatticePaper.Tiles.BaseMixedThreeOneOddEvenSites (Register Frame test contains)
open FLatticePaper.Tiles.BaseMixedThreeOneOddEvenSitesPolygons (shape physicalSite)

private theorem placed_fin (d : ℤ) (i : Fin 10) (used : i.val≠7 ∧ i.val≠8) :
    entry true true false d i.val=shape d i.val := by
  fin_cases i
  all_goals first | (exfalso; exact used.1 rfl) | (exfalso; exact used.2 rfl) | skip
  all_goals simp [entry,CorrectedMixedPlacement.layout,CorrectedRegisterDiagram.orientation,axisA,axisB,axisU,axisV,shape]
  all_goals norm_num [Prod.ext_iff]; omega

private theorem placed (d : ℤ) (i : ℕ) (valid : i<10 ∧ i≠7 ∧ i≠8) :
    entry true true false d i=shape d i := placed_fin d ⟨i,valid.1⟩ valid.2

private theorem component10 (r : Register) : contains r 10 ↔ 0 ≤ (r.d+r.X-r.Y) ∧ 0 ≤ (-r.d-r.X+r.Y) ∧ 0 ≤ (-r.d+r.Y-1) ∧ 0 ≤ (r.d-r.Y+2) := by
  constructor
  · intro h
    change ∀ j : Fin 4, (test r 10 j.val).holds at h
    have c0 := h 0
    change 0 ≤ (r.d+r.X-r.Y) at c0
    have c1 := h 1
    change 0 ≤ (-r.d-r.X+r.Y) at c1
    have c2 := h 2
    change 0 ≤ (-r.d+r.Y-1) at c2
    have c3 := h 3
    change 0 ≤ (r.d-r.Y+2) at c3
    exact ⟨c0, c1, c2, c3⟩
  · intro h j
    change Fin 4 at j
    fin_cases j
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2

private theorem component11 (r : Register) : contains r 11 ↔ 0 ≤ (r.X-r.Y-3) ∧ 0 ≤ (-r.X+r.Y+3) ∧ 0 ≤ (-2*r.d+r.Y-3) ∧ 0 ≤ (2*r.d-r.Y+4) := by
  constructor
  · intro h
    change ∀ j : Fin 4, (test r 11 j.val).holds at h
    have c0 := h 0
    change 0 ≤ (r.X-r.Y-3) at c0
    have c1 := h 1
    change 0 ≤ (-r.X+r.Y+3) at c1
    have c2 := h 2
    change 0 ≤ (-2*r.d+r.Y-3) at c2
    have c3 := h 3
    change 0 ≤ (2*r.d-r.Y+4) at c3
    exact ⟨c0, c1, c2, c3⟩
  · intro h j
    change Fin 4 at j
    fin_cases j
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2

private theorem component12 (r : Register) : contains r 12 ↔ 0 ≤ (-r.d+r.X-4) ∧ 0 ≤ (r.d-r.X+4) ∧ 0 ≤ (-r.d+r.Y-3) ∧ 0 ≤ (2*r.d-r.Y+2) := by
  constructor
  · intro h
    change ∀ j : Fin 4, (test r 12 j.val).holds at h
    have c0 := h 0
    change 0 ≤ (-r.d+r.X-4) at c0
    have c1 := h 1
    change 0 ≤ (r.d-r.X+4) at c1
    have c2 := h 2
    change 0 ≤ (-r.d+r.Y-3) at c2
    have c3 := h 3
    change 0 ≤ (2*r.d-r.Y+2) at c3
    exact ⟨c0, c1, c2, c3⟩
  · intro h j
    change Fin 4 at j
    fin_cases j
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2

private theorem component13 (r : Register) : contains r 13 ↔ 0 ≤ (-r.d+r.Y-1) ∧ 0 ≤ (r.d-r.Y+1) ∧ 0 ≤ (r.d+r.X-r.Y) ∧ 0 ≤ (-r.X+r.Y) := by
  constructor
  · intro h
    change ∀ j : Fin 4, (test r 13 j.val).holds at h
    have c0 := h 0
    change 0 ≤ (-r.d+r.Y-1) at c0
    have c1 := h 1
    change 0 ≤ (r.d-r.Y+1) at c1
    have c2 := h 2
    change 0 ≤ (r.d+r.X-r.Y) at c2
    have c3 := h 3
    change 0 ≤ (-r.X+r.Y) at c3
    exact ⟨c0, c1, c2, c3⟩
  · intro h j
    change Fin 4 at j
    fin_cases j
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2

private theorem component14 (r : Register) : contains r 14 ↔ 0 ≤ (-2*r.d+r.Y-4) ∧ 0 ≤ (2*r.d-r.Y+4) ∧ 0 ≤ (r.d+r.X-r.Y-3) ∧ 0 ≤ (-r.X+r.Y+3) := by
  constructor
  · intro h
    change ∀ j : Fin 4, (test r 14 j.val).holds at h
    have c0 := h 0
    change 0 ≤ (-2*r.d+r.Y-4) at c0
    have c1 := h 1
    change 0 ≤ (2*r.d-r.Y+4) at c1
    have c2 := h 2
    change 0 ≤ (r.d+r.X-r.Y-3) at c2
    have c3 := h 3
    change 0 ≤ (-r.X+r.Y+3) at c3
    exact ⟨c0, c1, c2, c3⟩
  · intro h j
    change Fin 4 at j
    fin_cases j
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2

private theorem component15 (r : Register) : contains r 15 ↔ 0 ≤ (2*r.d+r.X-r.Y-2) ∧ 0 ≤ (r.d-r.X+r.Y+1) ∧ 0 ≤ (-r.d+r.Y-2) ∧ 0 ≤ (2*r.d-r.Y+3) ∧ 0 ≤ (r.X-3) ∧ 0 ≤ (2*r.d-r.X+5) := by
  constructor
  · intro h
    change ∀ j : Fin 6, (test r 15 j.val).holds at h
    have c0 := h 0
    change 0 ≤ (2*r.d+r.X-r.Y-2) at c0
    have c1 := h 1
    change 0 ≤ (r.d-r.X+r.Y+1) at c1
    have c2 := h 2
    change 0 ≤ (-r.d+r.Y-2) at c2
    have c3 := h 3
    change 0 ≤ (2*r.d-r.Y+3) at c3
    have c4 := h 4
    change 0 ≤ (r.X-3) at c4
    have c5 := h 5
    change 0 ≤ (2*r.d-r.X+5) at c5
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

set_option maxHeartbeats 400000 in
private theorem boundary (r : Register) (h : Frame r) :
    physicalSite r∈extra true true false r.d ↔ contains r 10 ∨ contains r 11 ∨ contains r 12 ∨ contains r 13 ∨ contains r 14 ∨ contains r 15 := by
  have d := h.f0
  rw [component10,component11,component12,component13,component14,component15]
  simp only [extra,axisA,axisB,axisU,axisV,physicalSite,Bool.false_eq_true,if_false,if_true,mem_shift,
    stairAltF,nearStairAltF,ladderAltF,nearLadderAltF,boxF,Finset.mem_filter,Finset.mem_product,Finset.mem_Icc,
    Prod.ext_iff,Prod.fst_sub,Prod.snd_sub,Prod.fst_add,Prod.snd_add]
  all_goals omega

private theorem comparison (r : Register) (h : Frame r) :
    (six (fun i => (entry true true false r.d i).mem (physicalSite r)) ∨ physicalSite r∈extra true true false r.d) ↔
      (entry true true false r.d 0).mem (physicalSite r) ∨ (entry true true false r.d 9).mem (physicalSite r) := by
  have agree (i : ℕ) (used : i<10 ∧ i≠7 ∧ i≠8)
      (poly : (shape r.d i).mem (physicalSite r) ↔ contains r i) :
      (entry true true false r.d i).mem (physicalSite r) ↔ contains r i := by
    rw [placed r.d i used]; exact poly
  have e0 := agree 0 (by decide) (BaseMixedThreeOneOddEvenSitesPolygons.polygon0 r h)
  have e9 := agree 9 (by decide) (BaseMixedThreeOneOddEvenSitesPolygons.polygon9 r h)
  have e1 := agree 1 (by decide) (BaseMixedThreeOneOddEvenSitesPolygons.polygon1 r h)
  have e2 := agree 2 (by decide) (BaseMixedThreeOneOddEvenSitesPolygons.polygon2 r h)
  have e3 := agree 3 (by decide) (BaseMixedThreeOneOddEvenSitesPolygons.polygon3 r h)
  have e4 := agree 4 (by decide) (BaseMixedThreeOneOddEvenSitesPolygons.polygon4 r h)
  have e5 := agree 5 (by decide) (BaseMixedThreeOneOddEvenSitesPolygons.polygon5 r h)
  have e6 := agree 6 (by decide) (BaseMixedThreeOneOddEvenSitesPolygons.polygon6 r h)
  have rows := or_congr e1 (or_congr e2 (or_congr e3 (or_congr e4 (or_congr e5 e6))))
  refine (or_congr rows (boundary r h)).trans ((Iff.trans ?_ (or_congr e0.symm e9.symm)))
  simpa only [or_assoc] using (BaseMixedThreeOneOddEvenSites.coverage r h).symm

/-- The actual two-polygon membership equivalence on this parity of physical sites. -/
theorem at_word (k : ℕ) (z : Site) (p : oddSite z=false) :
    let t := child true true k
    let e := -(parentsAt t).odd.det (parentsAt t).even
    let A := JointFamily.vP1 t+JointFamily.vQ1 t
    let B := JointFamily.vP2 t+JointFamily.vQ2 t
    z∈(if false then altEvenT t else altOddT t) ↔ Band A B 0 0 z ∨
      Band A B 0 0 (z-(JointFamily.vP2 t+(if false then -e else e) • JointFamily.vQ1 t)) := by
  let r : Register := ⟨size true k,z.1+z.2,z.2⟩
  have F : Frame r := by
    have pp := p
    simp [oddSite] at pp
    constructor <;> dsimp [r,size] <;> omega
  have site : physicalSite r=z := by ext <;> dsimp [physicalSite,r]; ring
  apply CorrectedMixedBasePlacement.at_site true true false k (by decide) z
  have C := comparison r F
  simpa only [site] using C

end FLatticePaper.Tiles.BaseMixedThreeOneOddEvenSitesChild
