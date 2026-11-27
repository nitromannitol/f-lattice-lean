import FLatticePaper.Plane.Induction.BulkForced
import FLatticePaper.Plane.Induction.PassageRank
import FLatticePaper.Plane.Induction.W1Step

/-! # A rank of the passage on strict representatives (Q36 with representatives)

`RepStep F z o`: a black step (lap `−1`, `o` an input of `z`) or a forced white step (lap `0`, `o` the unseeded forced input).
The rank of a nonfree site is the burning rank `R` of the sheet minimum at its strict representative `z + repShift z`.
Black steps lift with the same representative shift (`o + repShift z` is an input of the representative, where `R` decreases);
white steps lift through the forced-output uniqueness `forced_bulk`, whose value is the burning selection at the
representative. No start in the closed polygon is needed. -/

namespace FLatticePaper.RepRank

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.FreeClosure FLatticePaper.SquareClauses
  FLatticePaper.AndOrRank FLatticePaper.PassageRank FLatticePaper.BulkForced

/-- A passage step on nonfree sites: a black step to an input, or an unseeded forced white step. -/
def RepStep (F : Field) (z o : Site) : Prop :=
  (laplacian F z = -1 ∧ (o = incomingNeg z ∨ o = incomingPos z)) ∨
    (laplacian F z = 0 ∧ SquareClauses.ForcedEdge F (fun _ _ => False) z o)

/-- The forced input of an unseeded forced white is an input of it. -/
theorem input_of_forced {F : Field} {z o : Site} (hf : SquareClauses.ForcedEdge F (fun _ _ => False) z o) :
    o = incomingNeg z ∨ o = incomingPos z := by
  cases hf with
  | seed hs => exact False.elim hs
  | @unit a b c o' inside hc hw ho hout hin hforced => exact ho

/-- **The representative decrease.** Along a passage step between nonfree sites, the burning rank of the strict
representative decreases. -/
theorem rep_decrease (frame : ChildFrame) {F M : Field} (hW : ProtectedWeb.WebHyp frame F)
    (hFM : ∀ z ∈ frame.closedPolygon, F z = M z) {R : Site → ℤ ×ₗ ℤ} (hR : IsBurningRank M R) :
    ∀ z o : Site, Nonfree frame z → Nonfree frame o → RepStep F z o →
      R (o + repShift frame o) < R (z + repShift frame z) := by
  obtain ⟨sel, hsel, hsq⟩ := burning_sel hR
  have hselM : ∀ c, laplacian M c = 0 → sel c = incomingNeg c ∨ sel c = incomingPos c :=
    fun c h => (hsel c h).1
  intro z o hz ho hG
  obtain ⟨hvz, hsw⟩ := repShift_spec frame hz
  have hstar := lap_agree_star frame hFM (TransferW1.strictInterior_star frame hsw)
  have hlapw : laplacian F (z + repShift frame z) = laplacian F z := hW.inv z _ hvz
  rcases hG with ⟨hl, hadj⟩ | ⟨hl0, hf⟩
  · -- black step: `o + repShift z` is an input of the representative, which is black for `M`
    have hrep : repShift frame o = repShift frame z := (repShift_of_input frame hz ho hadj).symm
    have hlw : laplacian M (z + repShift frame z) = -1 := by
      rw [← hstar, hlapw]
      exact hl
    rw [hrep]
    rcases hR (z + repShift frame z) with ⟨-, hn, hp⟩ | ⟨hl0', -⟩
    · rcases hadj with h | h
      · rw [h, ← incomingNeg_add z _ (ProtectedWeb.span_even frame hvz)]
        exact hn
      · rw [h, ← incomingPos_add z _ (ProtectedWeb.span_even frame hvz)]
        exact hp
    · rw [hlw] at hl0'
      norm_num at hl0'
  · -- forced white step: the forced input is the burning selection at the representative
    have hlw0 : laplacian M (z + repShift frame z) = 0 := by
      rw [← hstar, hlapw]
      exact hl0
    obtain ⟨-, hm⟩ := forced_bulk frame hW hFM sel hselM hsq z o hf
    have hadj := input_of_forced hf
    have hrep : repShift frame o = repShift frame z := (repShift_of_input frame hz ho hadj).symm
    have hmo : o + repShift frame z = sel (z + repShift frame z) := by
      rw [hm]
      unfold bulkSel
      rw [sub_add_cancel]
    rw [hrep, hmo]
    exact (hsel (z + repShift frame z) hlw0).2

/-- The rank of the passage on nonfree sites, with values in `ℕ`. -/
theorem rep_rank (frame : ChildFrame) {F M : Field} (hW : ProtectedWeb.WebHyp frame F)
    (hFM : ∀ z ∈ frame.closedPolygon, F z = M z) {R : Site → ℤ ×ₗ ℤ} (hR : IsBurningRank M R) :
    ∃ ρ : Site → ℕ, ∀ z o : Site, Nonfree frame z → Nonfree frame o → RepStep F z o → ρ o < ρ z :=
  nat_rank_of_key {c : Site | FLatticePaper.W1.StrictInterior frame.child.num frame.child.den c}
    (W1Step.strictInterior_child_finite frame) R (fun z => z + repShift frame z)
    (fun z => Nonfree frame z) (RepStep F)
    (fun _ hz => (repShift_spec frame hz).2)
    (fun z o hz ho hG => rep_decrease frame hW hFM hR z o hz ho hG)

end FLatticePaper.RepRank
