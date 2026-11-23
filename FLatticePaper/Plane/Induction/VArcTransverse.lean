import FLatticePaper.Plane.Induction.BaseInputsProof

/-! Task 56 (Q2, the transverse exits of the V-arc range).

For `z ∈ E` with a horizontal neighbour outside `E` (Q2: `OnVArc`), write `D_−(z) = F z − F (z − σ)`. Q2 proves
`−2 ≤ D_− ≤ 0` there. The transverse part of the argument (this file) is:
* the east neighbour `y = z + (1,0)` can only fail the transverse bound from above; then `t(z) ∈ [1−d, n+2d−3]` and
  `D_−(z) = 0` (zero strip);
* the west neighbour `w = z − (1,0)` can only fail the transverse bound from below; then `z − V` has `t ∈ [1−d, n+2d−3]`,
  so `D_−(z − V) = 0`, and the transverse drift `D_−(z) = D_−(z − V) − 2` gives `D_−(z) = −2`.
The longitudinal exits (the `s`-bounds) are the core of Q2 and are not in this file.

Hypotheses used: the sewn strip data of the current word (`StripInputs`, agreement with the sheet minimum on `E`, the
periods with `cU = 0`), and the numerical facts `3 ≤ n`, `n ≤ 2d − 3`, `3 ≤ d` (checked on the proper words of length ≤ 4). -/

namespace FLatticePaper.Induction

open Farey

namespace ChildFrame

variable (frame : ChildFrame)

/-- The upper transverse bound of `E` at the parity of `z` (`b_χ` of Q2). -/
def vUpper (z : Site) : ℤ :=
  if EvenSite z then frame.child.den + frame.child.num - 2 else frame.child.den

/-- The lower transverse bound of `E` at the parity of `z` (`a_χ − T` of Q2). -/
def vLower (z : Site) : ℤ :=
  if EvenSite z then 2 - frame.child.periodDenominator else frame.child.num - frame.child.periodDenominator

/-- The transverse bounds of `E` at `z`. -/
def vTBounds (z : Site) : Prop := vLower frame z ≤ frame.tGrade z ∧ frame.tGrade z ≤ vUpper frame z

theorem vUpper_even {z : Site} (h : EvenSite z) : vUpper frame z = frame.child.den + frame.child.num - 2 := by
  unfold vUpper; rw [if_pos h]

theorem vUpper_odd {z : Site} (h : ¬ EvenSite z) : vUpper frame z = frame.child.den := by
  unfold vUpper; rw [if_neg h]

theorem vLower_even {z : Site} (h : EvenSite z) : vLower frame z = 2 - frame.child.periodDenominator := by
  unfold vLower; rw [if_pos h]

theorem vLower_odd {z : Site} (h : ¬ EvenSite z) :
    vLower frame z = frame.child.num - frame.child.periodDenominator := by
  unfold vLower; rw [if_neg h]

theorem vTBounds_iff_even {z : Site} (h : EvenSite z) :
    vTBounds frame z ↔ 2 - frame.child.periodDenominator ≤ frame.tGrade z ∧
      frame.tGrade z ≤ frame.child.den + frame.child.num - 2 := by
  unfold vTBounds; rw [vLower_even frame h, vUpper_even frame h]

theorem vTBounds_iff_odd {z : Site} (h : ¬ EvenSite z) :
    vTBounds frame z ↔ frame.child.num - frame.child.periodDenominator ≤ frame.tGrade z ∧
      frame.tGrade z ≤ frame.child.den := by
  unfold vTBounds; rw [vLower_odd frame h, vUpper_odd frame h]

theorem mem_closedPolygon_vTBounds {z : Site} (hz : z ∈ frame.closedPolygon) : vTBounds frame z := by
  unfold ChildFrame.closedPolygon at hz
  by_cases h : EvenSite z
  · rw [Set.mem_setOf_eq, if_pos h] at hz
    exact (vTBounds_iff_even frame h).2 ⟨hz.1, hz.2.1⟩
  · rw [Set.mem_setOf_eq, if_neg h] at hz
    exact (vTBounds_iff_odd frame h).2 ⟨hz.1, hz.2.1⟩

theorem fst_add_east (z : Site) : (z + (1, 0)).1 = z.1 + 1 := rfl
theorem snd_add_east (z : Site) : (z + (1, 0)).2 = z.2 := by simp
theorem fst_sub_east (z : Site) : (z - (1, 0)).1 = z.1 - 1 := rfl
theorem snd_sub_east (z : Site) : (z - (1, 0)).2 = z.2 := by simp

/-- The grade `t` changes by `n` under the east step and by `−n` under the west step. -/
theorem tGrade_add_east (z : Site) : frame.tGrade (z + (1, 0)) = frame.tGrade z + frame.child.num := by
  unfold ChildFrame.tGrade
  rw [fst_add_east, snd_add_east]
  ring

theorem tGrade_sub_east (z : Site) : frame.tGrade (z - (1, 0)) = frame.tGrade z - frame.child.num := by
  unfold ChildFrame.tGrade
  rw [fst_sub_east, snd_sub_east]
  ring

/-- The east step flips the parity; so does the west step. -/
theorem evenSite_add_east_iff (z : Site) : EvenSite (z + (1, 0)) ↔ ¬ EvenSite z := by
  unfold EvenSite
  rw [fst_add_east, snd_add_east]
  omega

theorem evenSite_sub_east_iff (z : Site) : EvenSite (z - (1, 0)) ↔ ¬ EvenSite z := by
  unfold EvenSite
  rw [fst_sub_east, snd_sub_east]
  omega

/-- An east neighbour outside `E` fails the transverse bound from above only (the lower bound cannot fail). -/
theorem east_fail_upper (hn : 3 ≤ frame.child.num) {z : Site} (hz : z ∈ frame.closedPolygon)
    (hy : ¬ vTBounds frame (z + (1, 0))) :
    vUpper frame (z + (1, 0)) < frame.tGrade (z + (1, 0)) := by
  have hzb := mem_closedPolygon_vTBounds frame hz
  have ht := tGrade_add_east frame z
  by_cases he : EvenSite z
  · have hyn : ¬ EvenSite (z + (1, 0)) := fun h => (evenSite_add_east_iff z).1 h he
    rw [vTBounds_iff_even frame he] at hzb
    rw [vUpper_odd frame hyn]
    rw [vTBounds_iff_odd frame hyn] at hy
    omega
  · have hyn : EvenSite (z + (1, 0)) := (evenSite_add_east_iff z).2 he
    rw [vTBounds_iff_odd frame he] at hzb
    rw [vUpper_even frame hyn]
    rw [vTBounds_iff_even frame hyn] at hy
    omega

/-- A west neighbour outside `E` fails the transverse bound from below only (the upper bound cannot fail). -/
theorem west_fail_lower (hn : 3 ≤ frame.child.num) {z : Site} (hz : z ∈ frame.closedPolygon)
    (hw : ¬ vTBounds frame (z - (1, 0))) :
    frame.tGrade (z - (1, 0)) < vLower frame (z - (1, 0)) := by
  have hzb := mem_closedPolygon_vTBounds frame hz
  have ht := tGrade_sub_east frame z
  by_cases he : EvenSite z
  · have hwn : ¬ EvenSite (z - (1, 0)) := fun h => (evenSite_sub_east_iff z).1 h he
    rw [vTBounds_iff_even frame he] at hzb
    rw [vLower_odd frame hwn]
    rw [vTBounds_iff_odd frame hwn] at hw
    omega
  · have hwn : EvenSite (z - (1, 0)) := (evenSite_sub_east_iff z).2 he
    rw [vTBounds_iff_odd frame he] at hzb
    rw [vLower_even frame hwn]
    rw [vTBounds_iff_even frame hwn] at hw
    omega

/-- The zero strip for `D_−`: if `t(z) ∈ [1−d, n+2d−3]` then `F z − F (z − σ) = 0`. -/
theorem dMinus_zero_of_tRange {F M : Field} (hS : frame.StripInputs M)
    (hagree : ∀ y ∈ frame.closedPolygon, F y = M y)
    (hper : HasGeneratorPeriods frame.child F 0 frame.coherentConstantV) (z : Site)
    (hlo : 1 - frame.child.den ≤ frame.tGrade z)
    (hhi : frame.tGrade z ≤ frame.child.num + 2 * frame.child.den - 3) :
    F z - F (z - frame.shortShift) = 0 := by
  have ht : frame.tGrade (z - frame.shortShift) = frame.tGrade z + 2 := by
    have h := frame.tGrade_add_shortShift (z - frame.shortShift)
    rw [sub_add_cancel] at h
    omega
  have h := starDiff_zero_of_zero_strip frame hS hagree hper (z - frame.shortShift)
    (by omega) (by omega)
  unfold starDiff at h
  rw [sub_add_cancel] at h
  linarith

/-- East exit (upper): `D_−(z) = 0`. -/
theorem dMinus_zero_of_eastUpper {F M : Field} (hS : frame.StripInputs M)
    (hagree : ∀ y ∈ frame.closedPolygon, F y = M y)
    (hper : HasGeneratorPeriods frame.child F 0 frame.coherentConstantV)
    (hn : 3 ≤ frame.child.num) (hnd : frame.child.num ≤ 2 * frame.child.den - 3)
    {z : Site} (hz : z ∈ frame.closedPolygon) (hy : ¬ vTBounds frame (z + (1, 0))) :
    F z - F (z - frame.shortShift) = 0 := by
  have hup := east_fail_upper frame hn hz hy
  have hzb := mem_closedPolygon_vTBounds frame hz
  have ht := tGrade_add_east frame z
  apply dMinus_zero_of_tRange frame hS hagree hper z
  · by_cases he : EvenSite z
    · have hyn : ¬ EvenSite (z + (1, 0)) := fun h => (evenSite_add_east_iff z).1 h he
      rw [vTBounds_iff_even frame he] at hzb
      rw [vUpper_odd frame hyn] at hup
      omega
    · have hyn : EvenSite (z + (1, 0)) := (evenSite_add_east_iff z).2 he
      rw [vTBounds_iff_odd frame he] at hzb
      rw [vUpper_even frame hyn] at hup
      omega
  · by_cases he : EvenSite z
    · have hyn : ¬ EvenSite (z + (1, 0)) := fun h => (evenSite_add_east_iff z).1 h he
      rw [vTBounds_iff_even frame he] at hzb
      rw [vUpper_odd frame hyn] at hup
      omega
    · have hyn : EvenSite (z + (1, 0)) := (evenSite_add_east_iff z).2 he
      rw [vTBounds_iff_odd frame he] at hzb
      rw [vUpper_even frame hyn] at hup
      omega

/-- West exit (lower): `D_−(z) = −2`. -/
theorem dMinus_neg_two_of_westLower {F M : Field} (hS : frame.StripInputs M)
    (hagree : ∀ y ∈ frame.closedPolygon, F y = M y)
    (hper : HasGeneratorPeriods frame.child F 0 frame.coherentConstantV)
    (hn : 3 ≤ frame.child.num) (hnd : frame.child.num ≤ 2 * frame.child.den - 3) (hd : 3 ≤ frame.child.den)
    {z : Site} (hz : z ∈ frame.closedPolygon) (hw : ¬ vTBounds frame (z - (1, 0))) :
    F z - F (z - frame.shortShift) = -2 := by
  have hlow := west_fail_lower frame hn hz hw
  have hzb := mem_closedPolygon_vTBounds frame hz
  have ht := tGrade_sub_east frame z
  have hV := frame.tGrade_sub_modTransverse z
  have hu : 1 - frame.child.den ≤ frame.tGrade (z - frame.child.modifiedDeck.transverse) ∧
      frame.tGrade (z - frame.child.modifiedDeck.transverse) ≤ frame.child.num + 2 * frame.child.den - 3 := by
    rw [hV]
    by_cases he : EvenSite z
    · have hwn : ¬ EvenSite (z - (1, 0)) := fun h => (evenSite_sub_east_iff z).1 h he
      rw [vTBounds_iff_even frame he] at hzb
      rw [vLower_odd frame hwn] at hlow
      omega
    · have hwn : EvenSite (z - (1, 0)) := (evenSite_sub_east_iff z).2 he
      rw [vTBounds_iff_odd frame he] at hzb
      rw [vLower_even frame hwn] at hlow
      omega
  have h0 := dMinus_zero_of_tRange frame hS hagree hper _ hu.1 hu.2
  have hdrift := frame.starDiff_add_transverse_two hper (z - frame.child.modifiedDeck.transverse - frame.shortShift)
  unfold starDiff at hdrift
  have e1 : z - frame.child.modifiedDeck.transverse - frame.shortShift + frame.child.modifiedDeck.transverse =
      z - frame.shortShift := by abel
  have e3 : z - frame.child.modifiedDeck.transverse - frame.shortShift + frame.shortShift =
      z - frame.child.modifiedDeck.transverse := by abel
  rw [e1, show z - frame.shortShift + frame.shortShift = z from sub_add_cancel _ _, e3] at hdrift
  linarith

end ChildFrame

end FLatticePaper.Induction
