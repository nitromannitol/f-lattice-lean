import FLatticePaper.Plane.Induction.ShortPassages
import FLatticePaper.Plane.Induction.S3FreeBoundary

/-! Task 72 (FIXED_FREE §5 and §6): the canonical first directions, and the nonfree middles of the two cut-tip routes.

§5 (`FIXED_FREE_GAME_AUDIT` §5): the first edges of the canonical free table, read from `ChildFrame.prescribedH` and
`ChildFrame.prescribedV` (`S3FreeBoundary`): internal H east if even, north if odd; internal V `η` east if even, `−η` north if odd;
`H_0`: `−η` north; `V_0`: east; `H_last − U = (0, −1)`: north; `V_last − V = (1, −1)`: `η` east. For `η = −1` the ascending V
start is north at odd sites and west at even sites.

§6 (`TIP_THEOREM` and FIXED_FREE §6): with `t(v) = −B` and `s(v) = 2ε`, the W0 middle `v + (1, 1)` (`ε = −1`) and the W1 middle
`v + (−1, 0)` (`ε = +1`) are nonfree, under `0 ≤ B` and `5L ≤ T − B` (the licensed bounds of the note; `2L ≤ B` is not needed). -/

namespace FLatticePaper.Induction

namespace CanonicalDirections

open ShortPassages

theorem prescribedH_internal_even (frame : ChildFrame) (η : ℤ) {z : Site} (h1 : z ≠ hFirst) (h2 : z ≠ frame.hLast)
    (he : EvenSite z) : frame.prescribedH η z = (1, 0) := by
  unfold ChildFrame.prescribedH
  rw [if_neg h1, if_neg h2, if_pos he]

theorem prescribedH_internal_odd (frame : ChildFrame) (η : ℤ) {z : Site} (h1 : z ≠ hFirst) (h2 : z ≠ frame.hLast)
    (ho : ¬ EvenSite z) : frame.prescribedH η z = (0, 1) := by
  unfold ChildFrame.prescribedH
  rw [if_neg h1, if_neg h2, if_neg ho]

theorem prescribedV_internal_even (frame : ChildFrame) (η : ℤ) {z : Site} (h1 : z ≠ vFirst) (h2 : z ≠ frame.vLast)
    (he : EvenSite z) : frame.prescribedV η z = (η, 0) := by
  unfold ChildFrame.prescribedV
  rw [if_neg h1, if_neg h2, if_pos he]

theorem prescribedV_internal_odd (frame : ChildFrame) (η : ℤ) {z : Site} (h1 : z ≠ vFirst) (h2 : z ≠ frame.vLast)
    (ho : ¬ EvenSite z) : frame.prescribedV η z = (0, -η) := by
  unfold ChildFrame.prescribedV
  rw [if_neg h1, if_neg h2, if_neg ho]

/-- `H_0`: `−η` north. -/
theorem prescribedH_H0 (frame : ChildFrame) (η : ℤ) : frame.prescribedH η hFirst = (0, -η) :=
  frame.prescribedH_hFirst η

/-- `V_0`: east. -/
theorem prescribedV_V0 (frame : ChildFrame) (η : ℤ) : frame.prescribedV η vFirst = (1, 0) :=
  frame.prescribedV_vFirst η

/-- `H_last − U = (0, −1)` with `U = (d, n)`. -/
theorem hLast_sub_U (frame : ChildFrame) : frame.hLast - Kdeck frame = (0, -1) := by
  unfold ChildFrame.hLast Kdeck
  ext <;> simp

/-- The canonical direction at `H_last − U` is north. -/
theorem prescribedH_hLast_sub_U (frame : ChildFrame) (η : ℤ) :
    frame.prescribedH η (frame.hLast - Kdeck frame) = (0, 1) := by
  have hn := (period_facts frame).2.1
  rw [hLast_sub_U]
  apply prescribedH_internal_odd
  · intro h
    have := congrArg Prod.fst h
    simp [hFirst] at this
  · intro h
    have := congrArg Prod.snd h
    simp [ChildFrame.hLast] at this
    omega
  · unfold EvenSite
    simp

/-- `V_last − V = (1, −1)`. -/
theorem vLast_sub_V (frame : ChildFrame) : frame.vLast - Vdeck frame = (1, -1) := by
  unfold ChildFrame.vLast Vdeck
  ext <;> simp

/-- The canonical direction at `V_last − V` is `η` east. -/
theorem prescribedV_vLast_sub_V (frame : ChildFrame) (η : ℤ) :
    frame.prescribedV η (frame.vLast - Vdeck frame) = (η, 0) := by
  rw [vLast_sub_V]
  apply prescribedV_internal_even
  · intro h
    have := congrArg Prod.fst h
    simp [vFirst] at this
  · intro h
    have := congrArg Prod.fst h
    have hn := (period_facts frame).2.1
    have hd := (period_facts frame).2.2.1
    simp [ChildFrame.vLast] at this
    omega
  · unfold EvenSite
    simp

/-- The ascending V route from an odd internal V site starts north when `η = −1`. -/
theorem prescribedV_odd_minus_one (frame : ChildFrame) {z : Site} (h1 : z ≠ vFirst) (h2 : z ≠ frame.vLast)
    (ho : ¬ EvenSite z) : frame.prescribedV (-1) z = (0, 1) := by
  rw [prescribedV_internal_odd frame (-1) h1 h2 ho]
  norm_num

/-- The ascending V route from an even internal V site starts west when `η = −1`. -/
theorem prescribedV_even_minus_one (frame : ChildFrame) {z : Site} (h1 : z ≠ vFirst) (h2 : z ≠ frame.vLast)
    (he : EvenSite z) : frame.prescribedV (-1) z = (-1, 0) :=
  prescribedV_internal_even frame (-1) h1 h2 he

/-! ### §6: the two cut-tip middles. -/

/-- **Tip W0 (FIXED_FREE §6).** The middle `v + (1, 1)` of the W0 tip (`ε = −1`, `t(v) = −B`, `s(v) = 2ε`) is nonfree, under
`0 ≤ B` and `5L ≤ T − B`. -/
theorem tip_W0_middle_nonfree (frame : ChildFrame) (v : Site) (ε B : ℤ) (hv : EvenSite v) (hε : ε = -1)
    (ht : frame.tGrade v = -B) (hs : frame.sGrade v = 2 * ε)
    (hB0 : 0 ≤ B)
    (hB2 : 5 * (frame.child.den + frame.child.num) ≤ frame.child.periodDenominator - B) :
    Nonfree frame (v + (1, 1)) := by
  obtain ⟨-, hn, hnd, -⟩ := period_facts frame
  have hev : EvenSite (v + (1, 1)) := by
    rw [evenSite_add_pair_iff v 1 1 (by norm_num)]
    exact hv
  subst hε
  apply nonfree_V_even_left frame _ hev
  · rw [tGrade_add_pair, ht]
    linarith
  · rw [tGrade_add_pair, ht]
    linarith
  · rw [sGrade_add_pair, hs]
    linarith
  · rw [sGrade_add_pair, hs]
    linarith

/-- **Tip W1 (FIXED_FREE §6).** The middle `v + (−1, 0)` of the W1 tip (`ε = +1`, `t(v) = −B`, `s(v) = 2ε`) is nonfree, under
`0 ≤ B` and `5L ≤ T − B`. -/
theorem tip_W1_middle_nonfree (frame : ChildFrame) (v : Site) (ε B : ℤ) (hv : EvenSite v) (hε : ε = 1)
    (ht : frame.tGrade v = -B) (hs : frame.sGrade v = 2 * ε)
    (hB0 : 0 ≤ B)
    (hB2 : 5 * (frame.child.den + frame.child.num) ≤ frame.child.periodDenominator - B) :
    Nonfree frame (v + (-1, 0)) := by
  obtain ⟨-, hn, hnd, -⟩ := period_facts frame
  have hodd : ¬ EvenSite (v + (-1, 0)) := by
    unfold EvenSite at hv ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  subst hε
  apply nonfree_of_avoid
  · apply avoid_H_odd_low frame _ hodd
    · rw [tGrade_add_pair, ht]
      linarith
    · rw [tGrade_add_pair, ht]
      linarith
  · apply avoid_V_low frame
    · rw [sGrade_add_pair, hs]
      linarith
    · rw [sGrade_add_pair, hs]
      linarith

end CanonicalDirections

end FLatticePaper.Induction
