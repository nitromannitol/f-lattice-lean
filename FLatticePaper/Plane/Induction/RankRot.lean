import FLatticePaper.Plane.Induction.Rank4Fort
import FLatticePaper.Plane.Induction.FanPropagation
import FLatticePaper.Plane.Induction.ContactCone

/-! # The rotated rank-4 fan exclusion (native fort, rotated comparison, region `P` of the cone)

The fort `S` stays in its own coordinates; only the comparison is the parabola `parabolaField b.2` (ordinate parabola), which has
laplacian `-1` on odd and `0` on every even site. The fan runs on a general region `P` (the rotated cone), so the exit lemma is
`fan_exit_region` (G2, proved): a fan from a contact in `P` leaves `P` at an input `w` of some `P`-site. The three explicit inputs are
G1 (`hPN`: cone sites are nonfree), G3 (`hG`: inputs of cone sites outside `P` are translates `e + t` of earlier entries `e`), and the
window `hwin` (from `cone_window_NL`, with the rotated cap of `rotated_ray_cap_mono`), plus the shift `hshift` of the fort by `t`. -/

namespace FLatticePaper.RankRot

open FLatticePaper FLatticePaper.Induction FLatticePaper.FanPropagation FLatticePaper.ContactCone FLatticePaper.Rank4Fort

/-- **G2: the first exit of a fan from a contact in a finite region.** -/
theorem fan_exit_region {F m : Field} {S : Set Site} {P : Site → Prop}
    (next : FanT F m S → FanT F m S) (hr : ∀ v : FanT F m S, P v.1 → FanRules next v)
    (hfin : {c | P c}.Finite) (v0 : Site) (hv0S : v0 ∈ S) (hv0c : F v0 = m v0) (hv0 : P v0) :
    ∃ x : Site, P x ∧ ∃ w : Site, (w = incomingNeg x ∨ w = incomingPos x) ∧ ¬ P w ∧ w ∈ S ∧ F w = m w := by
  obtain ⟨k, hk, hj⟩ := fan_first_exit_of next hr hfin ⟨v0, hv0S, hv0c⟩
  cases k with
  | zero => exact absurd hv0 (by simpa using hk)
  | succ k' =>
    have hpred := hj k' (Nat.lt_succ_self k')
    have hsucc : next^[k' + 1] ⟨v0, hv0S, hv0c⟩ = next (next^[k'] ⟨v0, hv0S, hv0c⟩) :=
      Function.iterate_succ_apply' next k' _
    rw [hsucc] at hk
    have hrk := hr _ hpred
    exact ⟨(next^[k'] ⟨v0, hv0S, hv0c⟩).1, hpred, (next (next^[k'] ⟨v0, hv0S, hv0c⟩)).1, hrk.2, hk,
      (next (next^[k'] ⟨v0, hv0S, hv0c⟩)).2.1, (next (next^[k'] ⟨v0, hv0S, hv0c⟩)).2.2⟩

/-- **The rotated rank-4 exclusion.** A fan of the fort `S` (translated by `t`) from a cone contact `start` cannot start with
`start − t ∈ S`: its first exit is an input `w` of a cone site, outside the cone; by G3 `w = e + t` with `e` an earlier entry, so
`e ∈ S`, contradicting `hE`. -/
theorem rank4_rot {N : Site → Prop} {F : Field} {P : Site → Prop} {S : Set Site} (t b start : Site) (Eset : Set Site)
    (hfort : FortAt N F S)
    (hshift : ∀ T : Set Site, FortAt N F T → FortAt N F (shiftSet t T))
    (hPN : ∀ x, P x → N x)
    (hfin : {c | P c}.Finite)
    (hwin : WindowOn P F (parabolaField b.2))
    (hE : ∀ e ∈ Eset, e ∉ S)
    (hG : ∀ x i : Site, P x → (i = incomingNeg x ∨ i = incomingPos x) → ¬ P i → ∃ e ∈ Eset, i = e + t)
    (hstart : P start) (hstartc : F start = parabolaField b.2 start) :
    start - t ∉ S := by
  intro h
  have hT : start ∈ shiftSet t S := h
  have hFT : FortAt N F (shiftSet t S) := hshift S hfort
  obtain ⟨next, hr⟩ := fan_path_exists_fortAt (P := P) hFT hPN (parabola_binary b.2)
    (fun w hw => parabola_lap_even b.2 w hw) hwin
  obtain ⟨x, hPx, w, hwx, hnotP, hwS, hwc⟩ :=
    fan_exit_region next hr hfin start hT hstartc hstart
  obtain ⟨e, he, hwe⟩ := hG x w hPx hwx hnotP
  have hwS' : w - t ∈ S := hwS
  rw [hwe, add_sub_cancel_right] at hwS'
  exact hE e he hwS'

end FLatticePaper.RankRot

