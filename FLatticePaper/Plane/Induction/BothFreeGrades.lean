import FLatticePaper.Plane.Induction.Q3Shift
import FLatticePaper.Plane.Induction.StrongPriceValues
import FLatticePaper.Plane.Induction.ArcRanges
import FLatticePaper.Plane.Induction.ChildGap

/-! Task 72 / Q20 (chain monotonicity), the both-free exclusion, grade lemmas (BOTH_FREE_RAW_PHI_EXCLUSION.md §§1–3).

Notation as in the note: `t = n x − d y`, `s = L x + (d − n) y` with `L = d + n`, `σ = shortShift` (`t σ = −2`), `z' = z + ησ`.
The prescribed directions are those of `S3FreeBoundary` (`prescribedH η`, `prescribedV η`).

* §2 (H/H): if `z` and `z' = z + ησ` are both free H representatives, their prescribed directions agree
  (`prescribedH_shift_agree`). The only non-north odd choice is `H_0` (grade `n`), and the shift moves grade `n` to `n − 2η`,
  which is outside the odd H band unless `η = −1`; the `H_{d−1}` case is the same by grade `d`.
* §3 (V/H endpoints): the grades of the V endpoints (`t(V_0) = 0`, `t(V_{L−1}) = L − T`) and their shifts, and the choices
  `prescribedV η V_0 = east`, `prescribedV η V_{L−1} = η east`. The even H choice is east (`prescribedH_even_east`).
* §1 (V star): the price is the constant `cutPrice` where the field is harmonic at the site and its parent shift
  (`price_eq_cutPrice_of_harmonic`, StrongPriceValues); the harmonic values on the star are a named input.

Named external inputs of the note, see the inventory in `checks/Q3_INVENTORY.md`: the two-rank reduction (TWO_RANK audit), the
V-arc order of the free V cut (§3, odd V grades), and the harmonic strip on the V star (§1). -/

namespace FLatticePaper.BothFreeGrades

open Farey FLatticePaper FLatticePaper.Induction

/-- The shift `η σ` as a site. -/
abbrev shiftσ (frame : ChildFrame) (η : ℤ) : Site :=
  (η * frame.shortShift.1, η * frame.shortShift.2)

theorem evenSite_shiftσ (frame : ChildFrame) (η : ℤ) (hη : η = 1 ∨ η = -1) (z : Site) :
    EvenSite (z + shiftσ frame η) ↔ EvenSite z := by
  have hs : (frame.shortShift.1 + frame.shortShift.2) % 2 = 0 := by
    unfold ChildFrame.shortShift
    simp only
    rw [show 2 * frame.eps * frame.parents.odd.den + 2 * frame.eps * frame.parents.odd.num =
        2 * (frame.eps * frame.parents.odd.den + frame.eps * frame.parents.odd.num) by ring]
    omega
  unfold EvenSite at hs ⊢
  simp only [Prod.fst_add, Prod.snd_add, shiftσ]
  rcases hη with rfl | rfl <;> omega

/-- `t(z + ησ) = t z − 2η` (the grade of the shift). -/
theorem tGrade_shiftσ (frame : ChildFrame) (η : ℤ) (z : Site) :
    frame.tGrade (z + shiftσ frame η) = frame.tGrade z - 2 * η :=
  frame.tGrade_add_shift z η

/-- The grade of `H_0 = (1, 0)` is `n`. -/
theorem tGrade_hFirst (frame : ChildFrame) : frame.tGrade hFirst = frame.child.num := by
  unfold ChildFrame.tGrade hFirst
  ring

/-- The grade of `H_{d−1} = (d, n−1)` is `d`. -/
theorem tGrade_hLast (frame : ChildFrame) : frame.tGrade frame.hLast = frame.child.den := by
  unfold ChildFrame.tGrade ChildFrame.hLast
  ring

/-- The grades of the V endpoints: `t(V_0) = 0`, `t(V_{L−1}) = L − T`. -/
theorem tGrade_vFirst (frame : ChildFrame) : frame.tGrade vFirst = 0 := by
  unfold ChildFrame.tGrade vFirst
  ring

theorem tGrade_vLast (frame : ChildFrame) :
    frame.tGrade frame.vLast =
      (frame.child.den + frame.child.num) - frame.child.periodDenominator := by
  obtain ⟨-, -, -, -, hT⟩ := frame.child_facts
  rw [hT]
  unfold ChildFrame.tGrade ChildFrame.vLast
  ring

/-- The even H choice is east (the special H sites are odd). -/
theorem prescribedH_even_east (frame : ChildFrame) (η : ℤ) (z : Site) (hz : EvenSite z) :
    frame.prescribedH η z = (1, 0) := by
  have hne1 : z ≠ hFirst := by
    rintro rfl
    unfold EvenSite hFirst at hz
    omega
  have hne2 : z ≠ frame.hLast := by
    rintro rfl
    unfold EvenSite ChildFrame.hLast at hz
    obtain ⟨hnodd, hdodd⟩ := frame.child_odd
    simp only at hz
    omega
  unfold ChildFrame.prescribedH
  rw [if_neg hne1, if_neg hne2, if_pos hz]

/-- The V endpoint choices: `V_0` east, `V_{L−1}` is `η` east. -/
theorem prescribedV_vFirst (frame : ChildFrame) (η : ℤ) : frame.prescribedV η vFirst = (1, 0) := by
  unfold ChildFrame.prescribedV
  simp

theorem prescribedV_vLast (frame : ChildFrame) (η : ℤ) (hne : vFirst ≠ frame.vLast) :
    frame.prescribedV η frame.vLast = (η, 0) := by
  unfold ChildFrame.prescribedV
  rw [if_neg (Ne.symm hne), if_pos rfl]

theorem tGrade_of_hFirst (frame : ChildFrame) {w : Site} (h : w = hFirst) :
    frame.tGrade w = frame.child.num := by
  rw [h]
  exact tGrade_hFirst frame

theorem tGrade_of_hLast (frame : ChildFrame) {w : Site} (h : w = frame.hLast) :
    frame.tGrade w = frame.child.den := by
  rw [h]
  exact tGrade_hLast frame

theorem not_even_hFirst : ¬ EvenSite hFirst := by
  unfold EvenSite hFirst
  norm_num

theorem not_even_hLast (frame : ChildFrame) : ¬ EvenSite frame.hLast := by
  obtain ⟨hnodd, hdodd⟩ := frame.child_odd
  unfold EvenSite ChildFrame.hLast
  simp only
  omega

/-- **§2, the H/H pairs agree.** If `z` and `z + ησ` are both free H representatives, the prescribed directions agree:
the original sign `η` at `z` and the shifted sign `−η` at `z + ησ` give the same direction. -/
theorem prescribedH_shift_agree (frame : ChildFrame) {η : ℤ} (hη : η = 1 ∨ η = -1) {z : Site}
    (hz : z ∈ frame.freeH) (hw : z + shiftσ frame η ∈ frame.freeH) :
    frame.prescribedH η z = frame.prescribedH (-η) (z + shiftσ frame η) := by
  obtain ⟨-, -, hzs⟩ := hz
  obtain ⟨-, -, hws⟩ := hw
  obtain ⟨w, hwdef⟩ : ∃ w, w = z + shiftσ frame η := ⟨_, rfl⟩
  rw [← hwdef] at hws ⊢
  have hpar : EvenSite w ↔ EvenSite z := by
    rw [hwdef]
    exact evenSite_shiftσ frame η hη z
  have ht : frame.tGrade w = frame.tGrade z - 2 * η := by
    rw [hwdef]
    exact tGrade_shiftσ frame η z
  obtain ⟨hnodd, hdodd⟩ := frame.child_odd
  obtain ⟨hn0, hnd1, hd2, -, -⟩ := frame.child_facts
  have hnd : frame.child.num + 2 ≤ frame.child.den := by omega
  unfold ChildFrame.hSpectrum at hzs hws
  have hpz : EvenSite z ↔ (z.1 + z.2) % 2 = 0 := Iff.rfl
  have hpw : EvenSite w ↔ (w.1 + w.2) % 2 = 0 := Iff.rfl
  unfold ChildFrame.prescribedH
  by_cases h1 : z = hFirst
  · -- z = H_0: odd, grade n; the shifted site has grade n − 2η
    have ht1 := tGrade_of_hFirst frame h1
    have hodd1 : ¬ EvenSite z := by rw [h1]; exact not_even_hFirst
    rw [if_pos h1]
    by_cases h2 : w = hFirst
    · exfalso
      have := tGrade_of_hFirst frame h2
      rcases hη with rfl | rfl <;> omega
    by_cases h3 : w = frame.hLast
    · have := tGrade_of_hLast frame h3
      rw [if_neg h2, if_pos h3]
      rcases hη with rfl | rfl
      · exfalso
        omega
      · norm_num
    · rw [if_neg h2, if_neg h3]
      have hodd_w : ¬ EvenSite w := fun h => hodd1 (hpar.mp h)
      rw [if_neg hodd_w]
      rcases hη with rfl | rfl
      · exfalso
        unfold EvenSite at hodd1 hpw hpz
        omega
      · norm_num
  by_cases h2 : z = frame.hLast
  · -- z = H_{d−1}: odd, grade d; the shifted site has grade d − 2η
    have ht2 := tGrade_of_hLast frame h2
    have hodd2 : ¬ EvenSite z := by rw [h2]; exact not_even_hLast frame
    rw [if_neg h1, if_pos h2]
    by_cases h3 : w = hFirst
    · have := tGrade_of_hFirst frame h3
      rw [if_pos h3]
      rcases hη with rfl | rfl
      · norm_num
      · exfalso
        omega
    by_cases h4 : w = frame.hLast
    · exfalso
      have := tGrade_of_hLast frame h4
      rcases hη with rfl | rfl <;> omega
    · rw [if_neg h3, if_neg h4]
      have hodd_w : ¬ EvenSite w := fun h => hodd2 (hpar.mp h)
      rw [if_neg hodd_w]
  -- z is an internal H site
  rw [if_neg h1, if_neg h2]
  by_cases h3 : w = hFirst
  · have := tGrade_of_hFirst frame h3
    have hoddw : ¬ EvenSite z := by
      intro h
      apply not_even_hFirst
      rw [← h3]
      exact hpar.mpr h
    rw [if_pos h3]
    rw [if_neg hoddw]
    rcases hη with rfl | rfl
    · norm_num
    · exfalso
      unfold EvenSite at hpz hoddw
      omega
  by_cases h4 : w = frame.hLast
  · -- w = H_{d−1} is odd, so z is odd: both directions are north
    have hoddz : ¬ EvenSite z := by
      intro h
      apply not_even_hLast frame
      rw [← h4]
      exact hpar.mpr h
    rw [if_neg h3, if_pos h4, if_neg hoddz]
  · by_cases he : EvenSite z
    · rw [if_neg h3, if_pos he, if_pos (hpar.mpr he), if_neg h4]
    · rw [if_neg h3, if_neg he, if_neg (fun h => he (hpar.mp h)), if_neg h4]

/-- The grade of a deck translate `w − kV`: `t(w − kV) = t w + k T` (`t V = −T`). -/
theorem tGrade_sub_kV (frame : ChildFrame) (w : Site) (k : ℤ) :
    frame.tGrade (w - (k * frame.child.modifiedDeck.transverse.1, k * frame.child.modifiedDeck.transverse.2)) =
      frame.tGrade w + k * frame.child.periodDenominator := by
  obtain ⟨-, -, -, -, hT⟩ := frame.child_facts
  rw [hT, ChildFrame.child_modifiedDeck_transverse]
  unfold ChildFrame.tGrade
  simp only [Prod.fst_sub, Prod.snd_sub]
  ring

/-- **§3, odd V.** An odd V site with `t ∈ [−T+L+d, −d]` has no free H translate `w − kV` (`w = z + ησ`). -/
theorem no_H_class_of_odd_V (frame : ChildFrame) {η : ℤ} (hη : η = 1 ∨ η = -1) {z : Site}
    (hzt : -frame.child.periodDenominator + (frame.child.den + frame.child.num + frame.child.den) ≤
        frame.tGrade z ∧ frame.tGrade z ≤ -frame.child.den)
    (k : ℤ) (r : Site)
    (hr : r = (z + shiftσ frame η) - (k * frame.child.modifiedDeck.transverse.1, k * frame.child.modifiedDeck.transverse.2)) :
    r ∉ frame.freeH := by
  intro hfree
  obtain ⟨-, -, hs⟩ := hfree
  unfold ChildFrame.hSpectrum at hs
  have htr := tGrade_sub_kV frame (z + shiftσ frame η) k
  rw [← hr] at htr
  have htw := tGrade_shiftσ frame η z
  obtain ⟨hn0, hnd1, hd2, hd3, hT⟩ := frame.child_facts
  obtain ⟨hnodd, hdodd⟩ := frame.child_odd
  have hTpos : 0 < frame.child.periodDenominator := by rw [hT]; nlinarith
  rw [htr] at hs
  rw [htw] at hs
  obtain ⟨h1, h2⟩ := hzt
  rcases hη with rfl | rfl
  all_goals
    rcases (show k ≤ -1 ∨ k = 0 ∨ 1 ≤ k by omega) with hk | rfl | hk
    · have : k * frame.child.periodDenominator ≤ -frame.child.periodDenominator := by nlinarith
      omega
    · simp only [zero_mul, add_zero] at hs
      omega
    · have : frame.child.periodDenominator ≤ k * frame.child.periodDenominator := by nlinarith
      omega

/-- **§3, even V.** An even V site with `t ∈ [−T+2L, −L]` (not an endpoint) has no free H translate `w − kV`. -/
theorem no_H_class_of_even_V (frame : ChildFrame) {η : ℤ} (hη : η = 1 ∨ η = -1) {z : Site}
    (hzt : -frame.child.periodDenominator + 2 * (frame.child.den + frame.child.num) ≤ frame.tGrade z ∧
        frame.tGrade z ≤ -(frame.child.den + frame.child.num))
    (k : ℤ) (r : Site)
    (hr : r = (z + shiftσ frame η) - (k * frame.child.modifiedDeck.transverse.1, k * frame.child.modifiedDeck.transverse.2)) :
    r ∉ frame.freeH := by
  intro hfree
  obtain ⟨-, -, hs⟩ := hfree
  unfold ChildFrame.hSpectrum at hs
  have htr := tGrade_sub_kV frame (z + shiftσ frame η) k
  rw [← hr] at htr
  have htw := tGrade_shiftσ frame η z
  obtain ⟨hn0, hnd1, hd2, hd3, hT⟩ := frame.child_facts
  obtain ⟨hnodd, hdodd⟩ := frame.child_odd
  have hTpos : 0 < frame.child.periodDenominator := by rw [hT]; nlinarith
  rw [htr] at hs
  rw [htw] at hs
  obtain ⟨h1, h2⟩ := hzt
  rcases hη with rfl | rfl
  all_goals
    rcases (show k ≤ -1 ∨ k = 0 ∨ 1 ≤ k by omega) with hk | rfl | hk
    · have : k * frame.child.periodDenominator ≤ -frame.child.periodDenominator := by nlinarith
      omega
    · simp only [zero_mul, add_zero] at hs
      omega
    · have : frame.child.periodDenominator ≤ k * frame.child.periodDenominator := by nlinarith
      omega

/-- The shift `σ` has even coordinate sum (so does `ησ` for `η = ±1`). -/
theorem shortShift_even (frame : ChildFrame) : (frame.shortShift.1 + frame.shortShift.2) % 2 = 0 := by
  unfold ChildFrame.shortShift
  simp only
  rw [show 2 * frame.eps * frame.parents.odd.den + 2 * frame.eps * frame.parents.odd.num =
      2 * (frame.eps * frame.parents.odd.den + frame.eps * frame.parents.odd.num) by ring]
  omega

/-- **§3, the endpoint `V_0`.** A free H translate of `V_0 + ησ` forces `η = −1` and `k = 0`. -/
theorem vFirst_class (frame : ChildFrame) {η : ℤ} (hη : η = 1 ∨ η = -1) (k : ℤ) (r : Site)
    (hr : r = (vFirst + shiftσ frame η) - (k * frame.child.modifiedDeck.transverse.1, k * frame.child.modifiedDeck.transverse.2))
    (hfree : r ∈ frame.freeH) : η = -1 ∧ k = 0 := by
  obtain ⟨-, -, hs⟩ := hfree
  unfold ChildFrame.hSpectrum at hs
  have htr := tGrade_sub_kV frame (vFirst + shiftσ frame η) k
  rw [← hr] at htr
  have htw : frame.tGrade (vFirst + shiftσ frame η) = frame.tGrade vFirst - 2 * η :=
    tGrade_shiftσ frame η vFirst
  rw [tGrade_vFirst] at htw
  obtain ⟨hn0, hnd1, hd2, hd3, hT⟩ := frame.child_facts
  obtain ⟨hnodd, hdodd⟩ := frame.child_odd
  have hTL : frame.child.den + frame.child.num + 2 < frame.child.periodDenominator := by
    rw [hT]
    nlinarith
  rw [htr, htw] at hs
  rcases hη with rfl | rfl
  all_goals
    rcases (show k ≤ -1 ∨ k = 0 ∨ 1 ≤ k by omega) with hk | rfl | hk
    · have : k * frame.child.periodDenominator ≤ -frame.child.periodDenominator := by nlinarith
      omega
    · simp only [zero_mul, add_zero] at hs
      omega
    · have : frame.child.periodDenominator ≤ k * frame.child.periodDenominator := by nlinarith
      omega

/-- **§3, the endpoint `V_{L−1}`.** A free H translate of `V_{L−1} + ησ` forces `η = 1` and `k = 1`. -/
theorem vLast_class (frame : ChildFrame) {η : ℤ} (hη : η = 1 ∨ η = -1) (k : ℤ) (r : Site)
    (hr : r = (frame.vLast + shiftσ frame η) - (k * frame.child.modifiedDeck.transverse.1, k * frame.child.modifiedDeck.transverse.2))
    (hfree : r ∈ frame.freeH) : η = 1 ∧ k = 1 := by
  obtain ⟨-, -, hs⟩ := hfree
  unfold ChildFrame.hSpectrum at hs
  have htr := tGrade_sub_kV frame (frame.vLast + shiftσ frame η) k
  rw [← hr] at htr
  have htw : frame.tGrade (frame.vLast + shiftσ frame η) = frame.tGrade frame.vLast - 2 * η :=
    tGrade_shiftσ frame η frame.vLast
  rw [tGrade_vLast] at htw
  obtain ⟨hn0, hnd1, hd2, hd3, hT⟩ := frame.child_facts
  obtain ⟨hnodd, hdodd⟩ := frame.child_odd
  have hTL : frame.child.den + frame.child.num + 2 < frame.child.periodDenominator := by
    rw [hT]
    nlinarith
  rw [htr, htw] at hs
  rcases hη with rfl | rfl
  all_goals
    rcases (show k ≤ -1 ∨ k = 0 ∨ k = 1 ∨ 2 ≤ k by omega) with hk | rfl | rfl | hk
    · have : k * frame.child.periodDenominator ≤ -frame.child.periodDenominator := by nlinarith
      omega
    · simp only [zero_mul, add_zero] at hs
      omega
    · simp only [one_mul] at hs
      omega
    · have : 2 * frame.child.periodDenominator ≤ k * frame.child.periodDenominator := by nlinarith
      omega

/-- The H class of `V_0 + ησ` is even, so its prescribed direction is east. -/
theorem vFirst_H_agree (frame : ChildFrame) (η : ℤ) (r : Site) (hη : η = -1)
    (hr : r = (vFirst + shiftσ frame η) - (0 * frame.child.modifiedDeck.transverse.1, 0 * frame.child.modifiedDeck.transverse.2)) :
    frame.prescribedV η vFirst = frame.prescribedH (-η) r := by
  subst hη
  have hev : EvenSite r := by
    rw [hr]
    unfold EvenSite
    simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, zero_mul, sub_zero]
    have h1 : vFirst.1 = 0 := rfl
    have h2 : vFirst.2 = 0 := rfl
    have hσ := shortShift_even frame
    omega
  rw [prescribedV_vFirst, prescribedH_even_east frame _ r hev]

/-- The H class of `V_{L−1} + ησ` is even, so its prescribed direction is east. -/
theorem vLast_H_agree (frame : ChildFrame) (r : Site) (_hη : η = 1)
    (hr : r = (frame.vLast + shiftσ frame 1) - (1 * frame.child.modifiedDeck.transverse.1, 1 * frame.child.modifiedDeck.transverse.2)) :
    frame.prescribedV 1 frame.vLast = frame.prescribedH (-1) r := by
  have hev : EvenSite r := by
    rw [hr]
    unfold EvenSite
    simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, one_mul]
    unfold ChildFrame.vLast
    rw [ChildFrame.child_modifiedDeck_transverse]
    have hσ := shortShift_even frame
    omega
  have hne : vFirst ≠ frame.vLast := by
    obtain ⟨hnodd, hdodd⟩ := frame.child_odd
    unfold vFirst ChildFrame.vLast
    intro h
    simp only [Prod.mk.injEq] at h
    omega
  rw [prescribedV_vLast frame 1 hne, prescribedH_even_east frame _ r hev]

/-- **§1, the price on the V star.** If the field is harmonic at two sites and at their parent shifts, the primitive price
agrees there (both are `cutPrice`). The harmonic values on the star are a named input (the strips of the harmonic field). -/
theorem price_const_on_star (frame : ChildFrame) (F : Field) {z u : Site}
    (hz1 : F z = harmonicGrid z) (hz2 : F (z - frame.parentShift) = harmonicGrid (z - frame.parentShift))
    (hu1 : F u = harmonicGrid u) (hu2 : F (u - frame.parentShift) = harmonicGrid (u - frame.parentShift)) :
    frame.price F u = frame.price F z := by
  rw [FLatticePaper.StrongPriceValues.price_eq_cutPrice_of_harmonic frame F u hu1 hu2,
    FLatticePaper.StrongPriceValues.price_eq_cutPrice_of_harmonic frame F z hz1 hz2]

/-- **§3, the V/H choices agree.** For a free V root `z` whose shift has a free H translate `r = z + ησ − kV`, the prescribed
directions agree. Only the endpoints `V_0`, `V_{L−1}` have such a translate; the other V sites are excluded by the V-arc grades
(`hArc`, the named input: the odd and even non-endpoint V grades, from the order of the free V cut). -/
theorem V_H_choices_agree (frame : ChildFrame)
    (hArc : ∀ z, z ∈ frame.freeV → z ≠ vFirst → z ≠ frame.vLast →
      (EvenSite z ∧ -frame.child.periodDenominator + 2 * (frame.child.den + frame.child.num) ≤ frame.tGrade z ∧
          frame.tGrade z ≤ -(frame.child.den + frame.child.num)) ∨
        (¬ EvenSite z ∧ -frame.child.periodDenominator + (frame.child.den + frame.child.num + frame.child.den) ≤
          frame.tGrade z ∧ frame.tGrade z ≤ -frame.child.den))
    {η : ℤ} (hη : η = 1 ∨ η = -1) {z : Site} (hz : z ∈ frame.freeV) (k : ℤ) (r : Site)
    (hr : r = (z + shiftσ frame η) - (k * frame.child.modifiedDeck.transverse.1, k * frame.child.modifiedDeck.transverse.2))
    (hrH : r ∈ frame.freeH) :
    frame.prescribedV η z = frame.prescribedH (-η) r := by
  by_cases h0 : z = vFirst
  · subst h0
    obtain ⟨rfl, rfl⟩ := vFirst_class frame hη k r hr hrH
    exact vFirst_H_agree frame (-1) r rfl hr
  by_cases h1 : z = frame.vLast
  · subst h1
    obtain ⟨rfl, rfl⟩ := vLast_class frame hη k r hr hrH
    exact vLast_H_agree frame r rfl hr
  exfalso
  rcases hArc z hz h0 h1 with ⟨hev, hzt⟩ | ⟨hod, hzt⟩
  · exact no_H_class_of_even_V frame hη hzt k r hr hrH
  · exact no_H_class_of_odd_V frame hη hzt k r hr hrH

/-- The grade is additive in the second argument: `s(z − p) = s z − s p`. -/
theorem sGrade_sub (frame : ChildFrame) (z p : Site) : frame.sGrade (z - p) = frame.sGrade z - frame.sGrade p := by
  unfold ChildFrame.sGrade
  simp only [Prod.fst_sub, Prod.snd_sub]
  ring

/-- The parent shift `δ = ε V_p` has `s(δ) = 2`, from `t σ = −2`. -/
theorem sGrade_parentShift (frame : ChildFrame) : frame.sGrade frame.parentShift = 2 := by
  have h := frame.tGrade_shortShift
  unfold ChildFrame.tGrade ChildFrame.shortShift at h
  unfold ChildFrame.sGrade ChildFrame.parentShift
  simp only at h ⊢
  linarith

/-- The native V star's grade set (the note's §1): even `s ∈ [2 − 2c, 2d − 2]`, odd `s ∈ [−L, d + 3n]`. -/
def StarS (frame : ChildFrame) (s : ℤ) : Prop :=
  (s % 2 = 0 ∧ 2 - 2 * (frame.child.den - frame.child.num) ≤ s ∧ s ≤ 2 * frame.child.den - 2) ∨
    (s % 2 = 1 ∧ -(frame.child.den + frame.child.num) ≤ s ∧ s ≤ frame.child.den + 3 * frame.child.num)

/-- **§1, the star lies in the harmonic strip.** For a star grade `s` with `c = d − n ≥ 3`, both `s` and `s − 2` lie in
`[1 − 2d, 2L − 1]`, the window of `HasStrips` (the note's ordinary h0 strip). -/
theorem star_in_strip (frame : ChildFrame) (hc : 3 ≤ frame.child.den - frame.child.num) {s : ℤ}
    (hs : StarS frame s) :
    1 - 2 * frame.child.den ≤ s - 2 ∧ s ≤ 2 * (frame.child.den + frame.child.num) - 1 := by
  obtain ⟨hn0, -, -, -, -⟩ := frame.child_facts
  unfold StarS at hs
  omega

/-- **§1, the price on the V star from the harmonic strip.** If the sites `z`, `u` have star grades and the field satisfies
`HasStrips`, the primitive price is the same at `z` and `u` (`cutPrice`). No harmonic input is named: the strips supply it. -/
theorem price_const_on_star_of_strips (frame : ChildFrame) (F : Field) (hS : frame.HasStrips F)
    (hc : 3 ≤ frame.child.den - frame.child.num) {z u : Site} (hzs : StarS frame (frame.sGrade z))
    (hus : StarS frame (frame.sGrade u)) : frame.price F u = frame.price F z := by
  have hz1 : F z = harmonicGrid z := by
    have hb := star_in_strip frame hc hzs
    exact hS.2 z (by omega) (by omega)
  have hu1 : F u = harmonicGrid u := by
    have hb := star_in_strip frame hc hus
    exact hS.2 u (by omega) (by omega)
  have hz2 : F (z - frame.parentShift) = harmonicGrid (z - frame.parentShift) := by
    have hb := star_in_strip frame hc hzs
    have hsz := sGrade_sub frame z frame.parentShift
    rw [sGrade_parentShift] at hsz
    exact hS.2 _ (by omega) (by omega)
  have hu2 : F (u - frame.parentShift) = harmonicGrid (u - frame.parentShift) := by
    have hb := star_in_strip frame hc hus
    have hsu := sGrade_sub frame u frame.parentShift
    rw [sGrade_parentShift] at hsu
    exact hS.2 _ (by omega) (by omega)
  exact price_const_on_star frame F hz1 hz2 hu1 hu2

/-- **§3, the V/H choices agree, with the V-arc grades derived.** The arc hypothesis of `V_H_choices_agree` is now a theorem
(`ArcRanges.arc_even_range`, `ArcRanges.arc_odd_range`). -/
theorem V_H_choices_agree_derived (frame : ChildFrame) {η : ℤ} (hη : η = 1 ∨ η = -1) {z : Site}
    (hz : z ∈ frame.freeV) (k : ℤ) (r : Site)
    (hr : r = (z + shiftσ frame η) - (k * frame.child.modifiedDeck.transverse.1, k * frame.child.modifiedDeck.transverse.2))
    (hrH : r ∈ frame.freeH) :
    frame.prescribedV η z = frame.prescribedH (-η) r :=
  V_H_choices_agree frame
    (fun z hz h1 h2 => by
      by_cases he : EvenSite z
      · exact Or.inl ⟨he, FLatticePaper.ArcRanges.arc_even_range frame hz he h1 h2⟩
      · exact Or.inr ⟨he, FLatticePaper.ArcRanges.arc_odd_range frame hz he⟩)
    hη hz k r hr hrH

/-- **§1 from the word.** For a proper word that is not a two-power, the child gap is at least `4`, so the star price
lemma applies: the price is constant on the star with no hypothesis beyond the word and `HasStrips`. -/
theorem price_const_on_star_of_word (word : Word) (hprop : ∃ x ∈ word, x ≠ Digit.three) (hnot : ¬ IsTwoPow word)
    (F : Field) (hS : (frameAt word).HasStrips F) {z u : Site}
    (hzs : StarS (frameAt word) ((frameAt word).sGrade z)) (hus : StarS (frameAt word) ((frameAt word).sGrade u)) :
    (frameAt word).price F u = (frameAt word).price F z :=
  price_const_on_star_of_strips (frameAt word) F hS
    (by have := FLatticePaper.ChildGap.child_gap_ge_four word hprop hnot; omega) hzs hus

end FLatticePaper.BothFreeGrades
