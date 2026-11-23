import FLatticePaper.Plane.Induction.VArcTransverse
import FLatticePaper.Plane.Induction.VArcRange
import FLatticePaper.Plane.Induction.Strips
import FLatticePaper.Plane.Induction.PolygonGeometry
import FLatticePaper.Plane.Induction.ChildNumerator
import FLatticePaper.Plane.Induction.StandardField

/-! Task 56 (Q2, the longitudinal exits of the V-arc range).

Let `z ∈ E` have a horizontal neighbour outside `E` whose transverse bounds hold (so the neighbour fails its `s`-bound).
Let `U = (d, n)` be the child kernel, `T = d² + 2dn − n²` the period, and `X = U_p` (`W = 0`) or `U_q` (`W = 1`).
* east exit: `v = z − U`; west exit: `v = z`. Then `v ∈ E` and `2 − c ≤ s(v) ≤ L − 1` (`c = d − n`, `L = d + n`).
* `F z = F v`, `F v = h₀(v)` (harmonic strip), and `F (z − σ) = F (v + X)` (kernel period, `σ = ε U_p`).
* `F (v + X) = min(A(v + X), C(v + X))` (sewn data on `E`); the offers satisfy `A(v+X) ≥ h₀(v)` and `C(v+X) = h₀(v) + 2`.
Hence `D_−(z) = h₀(v) − min(A, C) ∈ [−2, 0]`.

The two offer facts are the named input `LongitudinalOffers` of Q2 (for all `v ∈ E` in the `s`-range): `mem` (`v + X ∈ E`),
`first` (`h₀(v) ≤ A(v+X)`, which Q2 derives from `ParentStepSign` and the old zero strip), and `second` (`C(v+X) = h₀(v) + 2`).
The sewn data are the strip inputs, the agreement with the sheet minimum on `E`, and the periods with `cU = 0`. -/

namespace FLatticePaper.Induction

open Farey

namespace ChildFrame

variable (frame : ChildFrame)

/-- `U_p = 2 (D, N)` for the odd parent `N/D`. -/
def uP : Site := (2 * frame.parents.odd.den, 2 * frame.parents.odd.num)

/-- `U_q = (d_q, n_q)`, the kernel of the even parent. -/
def uQ : Site := (frame.parents.even.den, frame.parents.even.num)

/-- The offset `X` of Q2: `U_p` at `W = 0`, `U_q` at `W = 1`. -/
def offsetX : Site := if frame.phaseW = 0 then frame.uP else frame.uQ

/-- The `s`-range of the longitudinal reduction: `2 − c ≤ s ≤ L − 1`. -/
def longRange (v : Site) : Prop :=
  2 - (frame.child.den - frame.child.num) ≤ frame.sGrade v ∧ frame.sGrade v ≤ frame.child.den + frame.child.num - 1

/-- The named offer input of Q2 (see the module comment). -/
structure LongitudinalOffers (Fp : Field) : Prop where
  mem : ∀ v, v ∈ frame.closedPolygon → frame.longRange v → v + frame.offsetX ∈ frame.closedPolygon
  first : ∀ v, v ∈ frame.closedPolygon → frame.longRange v →
    harmonicGrid v ≤ frame.sheetA Fp (v + frame.offsetX)
  second : ∀ v, v ∈ frame.closedPolygon → frame.longRange v →
    frame.sheetC Fp (v + frame.offsetX) = harmonicGrid v + 2

/-! ### Coordinates of the child kernel and of the parent pair -/

theorem kernel_coords : frame.child.modifiedDeck.kernel = (frame.child.den, frame.child.num) :=
  frame.child_modifiedDeck_kernel

theorem child_den_eq : frame.child.den = 2 * frame.parents.odd.den + frame.parents.even.den := by
  simp [ChildFrame.child, Parents.current, Parents.combine]

theorem child_num_eq : frame.child.num = 2 * frame.parents.odd.num + frame.parents.even.num := by
  simp [ChildFrame.child, Parents.current, Parents.combine]

theorem kernel_uP_uQ : frame.child.modifiedDeck.kernel = frame.uP + frame.uQ := by
  rw [kernel_coords, uP, uQ, Prod.mk_add_mk, child_den_eq, child_num_eq]

/-- The grades of `z + U`: `t` is unchanged, `s` grows by `T`. -/
theorem tGrade_add_kernel (z : Site) : frame.tGrade (z + frame.child.modifiedDeck.kernel) = frame.tGrade z := by
  rw [kernel_coords]
  unfold ChildFrame.tGrade
  show frame.child.num * (z.1 + frame.child.den) - frame.child.den * (z.2 + frame.child.num) = _
  ring

theorem sGrade_add_kernel (z : Site) :
    frame.sGrade (z + frame.child.modifiedDeck.kernel) = frame.sGrade z + frame.child.periodDenominator := by
  rw [kernel_coords, (frame.child_facts).2.2.2.2]
  unfold ChildFrame.sGrade
  show (frame.child.den + frame.child.num) * (z.1 + frame.child.den) +
      (frame.child.den - frame.child.num) * (z.2 + frame.child.num) = _
  ring

theorem evenSite_add_kernel_iff (z : Site) : EvenSite (z + frame.child.modifiedDeck.kernel) ↔ EvenSite z := by
  rw [kernel_coords]
  have h := frame.child_even
  unfold EvenSite
  show (z.1 + frame.child.den + (z.2 + frame.child.num)) % 2 = 0 ↔ (z.1 + z.2) % 2 = 0
  have hp : (frame.child.num + frame.child.den) % 2 = 0 := h
  omega

/-- `s` is even at every site, since `L` and `c` are even. -/
theorem sGrade_mod_two (z : Site) : frame.sGrade z % 2 = 0 := by
  have hp : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  unfold ChildFrame.sGrade
  obtain ⟨m, hm⟩ : ∃ m : ℤ, frame.child.den + frame.child.num = 2 * m := ⟨(frame.child.den + frame.child.num) / 2, by omega⟩
  have key : (frame.child.den + frame.child.num) * z.1 + (frame.child.den - frame.child.num) * z.2 =
      2 * (m * z.1 + (m - frame.child.num) * z.2) := by
    have hc : frame.child.den - frame.child.num = 2 * m - 2 * frame.child.num := by omega
    rw [hc, hm]
    ring
  rw [key]
  omega

/-! ### Membership in `E` by parity -/

/-- The `s`-bounds of `E` at the parity of `z`. -/
def vSBounds (z : Site) : Prop :=
  (if EvenSite z then 0 else 2 - frame.child.den + frame.child.num) ≤ frame.sGrade z ∧
    frame.sGrade z ≤ (if EvenSite z then frame.child.periodDenominator + 2 * frame.child.num
      else frame.child.periodDenominator + frame.child.den + frame.child.num - 2)

theorem mem_E_iff_bounds (z : Site) :
    z ∈ frame.closedPolygon ↔ vTBounds frame z ∧ vSBounds frame z := by
  unfold ChildFrame.closedPolygon vTBounds vSBounds
  by_cases h : EvenSite z
  · rw [Set.mem_setOf_eq, if_pos h, vUpper_even frame h, vLower_even frame h]
    simp only [if_pos h]
    tauto
  · rw [Set.mem_setOf_eq, if_neg h, vUpper_odd frame h, vLower_odd frame h]
    simp only [if_neg h]
    tauto

/-! ### Grades and shifts of the exit points -/

theorem sGrade_add_east (z : Site) :
    frame.sGrade (z + (1, 0)) = frame.sGrade z + (frame.child.den + frame.child.num) := by
  unfold ChildFrame.sGrade
  rw [fst_add_east, snd_add_east]
  ring

theorem sGrade_sub_east (z : Site) :
    frame.sGrade (z - (1, 0)) = frame.sGrade z - (frame.child.den + frame.child.num) := by
  unfold ChildFrame.sGrade
  rw [fst_sub_east, snd_sub_east]
  ring

theorem T_nonneg : 0 ≤ frame.child.periodDenominator := by
  have h := (frame.child_facts).2.2.2.2
  have h1 := (frame.child_facts).1
  have h2 := (frame.child_facts).2.1
  rw [h]
  nlinarith

theorem vSBounds_even {z : Site} (h : EvenSite z) :
    vSBounds frame z ↔ 0 ≤ frame.sGrade z ∧
      frame.sGrade z ≤ frame.child.periodDenominator + 2 * frame.child.num := by
  unfold vSBounds
  rw [if_pos h, if_pos h]

theorem vSBounds_odd {z : Site} (h : ¬ EvenSite z) :
    vSBounds frame z ↔ 2 - frame.child.den + frame.child.num ≤ frame.sGrade z ∧
      frame.sGrade z ≤ frame.child.periodDenominator + frame.child.den + frame.child.num - 2 := by
  unfold vSBounds
  rw [if_neg h, if_neg h]

/-- The east reduction: `v = z − U` lies in `E` and in the `s`-range, when `z` has an east neighbour outside `E`
that satisfies the transverse bounds. -/
theorem east_reduction {z : Site} (hz : z ∈ frame.closedPolygon)
    (hy : z + (1, 0) ∉ frame.closedPolygon) (hyT : vTBounds frame (z + (1, 0))) :
    z - frame.child.modifiedDeck.kernel ∈ frame.closedPolygon ∧
      frame.longRange (z - frame.child.modifiedDeck.kernel) := by
  have hsy : ¬ vSBounds frame (z + (1, 0)) := fun h => hy ((frame.mem_E_iff_bounds _).2 ⟨hyT, h⟩)
  obtain ⟨hzT, hzS⟩ := (frame.mem_E_iff_bounds z).1 hz
  have hK := frame.sGrade_add_kernel (z - frame.child.modifiedDeck.kernel)
  have hKt := frame.tGrade_add_kernel (z - frame.child.modifiedDeck.kernel)
  have hKe := frame.evenSite_add_kernel_iff (z - frame.child.modifiedDeck.kernel)
  rw [sub_add_cancel] at hK hKt hKe
  have hsyE := frame.sGrade_add_east z
  have hyE := evenSite_add_east_iff z
  have hp2 := frame.sGrade_mod_two z
  have hp2v := frame.sGrade_mod_two (z - frame.child.modifiedDeck.kernel)
  obtain ⟨hn0, hnd, hc2, hd3, -⟩ := frame.child_facts
  have hT0 := frame.T_nonneg
  have hL2 : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  by_cases he : EvenSite z
  · have hve : EvenSite (z - frame.child.modifiedDeck.kernel) := hKe.1 he
    have hyn : ¬ EvenSite (z + (1, 0)) := fun h => (hyE.1 h) he
    have hzT' := (vTBounds_iff_even frame he).1 hzT
    have hzS' := (vSBounds_even frame he).1 hzS
    have hsy' : ¬ (2 - frame.child.den + frame.child.num ≤ frame.sGrade (z + (1, 0)) ∧
        frame.sGrade (z + (1, 0)) ≤ frame.child.periodDenominator + frame.child.den + frame.child.num - 2) :=
      fun h => hsy ((vSBounds_odd frame hyn).2 h)
    constructor
    · rw [mem_E_iff_bounds]
      exact ⟨(vTBounds_iff_even frame hve).2 ⟨by rw [← hKt]; exact hzT'.1, by rw [← hKt]; exact hzT'.2⟩,
        (vSBounds_even frame hve).2 ⟨by omega, by omega⟩⟩
    · unfold ChildFrame.longRange
      omega
  · have hyn : EvenSite (z + (1, 0)) := hyE.2 he
    have hnve : ¬ EvenSite (z - frame.child.modifiedDeck.kernel) := fun h => he (hKe.2 h)
    have hzT' := (vTBounds_iff_odd frame he).1 hzT
    have hzS' := (vSBounds_odd frame he).1 hzS
    have hsy' : ¬ (0 ≤ frame.sGrade (z + (1, 0)) ∧
        frame.sGrade (z + (1, 0)) ≤ frame.child.periodDenominator + 2 * frame.child.num) :=
      fun h => hsy ((vSBounds_even frame hyn).2 h)
    constructor
    · rw [mem_E_iff_bounds]
      exact ⟨(vTBounds_iff_odd frame hnve).2 ⟨by rw [← hKt]; exact hzT'.1, by rw [← hKt]; exact hzT'.2⟩,
        (vSBounds_odd frame hnve).2 ⟨by omega, by omega⟩⟩
    · unfold ChildFrame.longRange
      omega

/-- The west reduction: `v = z` lies in the `s`-range, when `z` has a west neighbour outside `E` satisfying the
transverse bounds. -/
theorem west_reduction {z : Site} (hz : z ∈ frame.closedPolygon)
    (hw : z - (1, 0) ∉ frame.closedPolygon) (hwT : vTBounds frame (z - (1, 0))) :
    frame.longRange z := by
  have hsw : ¬ vSBounds frame (z - (1, 0)) := fun h => hw ((frame.mem_E_iff_bounds _).2 ⟨hwT, h⟩)
  obtain ⟨hzT, hzS⟩ := (frame.mem_E_iff_bounds z).1 hz
  have hswE := frame.sGrade_sub_east z
  have hwE := evenSite_sub_east_iff z
  have hp2 := frame.sGrade_mod_two z
  obtain ⟨hn0, hnd, hc2, hd3, -⟩ := frame.child_facts
  have hT0 := frame.T_nonneg
  have hL2 : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  unfold ChildFrame.longRange
  by_cases he : EvenSite z
  · have hwn : ¬ EvenSite (z - (1, 0)) := fun h => (hwE.1 h) he
    have hzS' := (vSBounds_even frame he).1 hzS
    have hsw' : ¬ (2 - frame.child.den + frame.child.num ≤ frame.sGrade (z - (1, 0)) ∧
        frame.sGrade (z - (1, 0)) ≤ frame.child.periodDenominator + frame.child.den + frame.child.num - 2) :=
      fun h => hsw ((vSBounds_odd frame hwn).2 h)
    omega
  · have hwn : EvenSite (z - (1, 0)) := (hwE.2 he)
    have hzS' := (vSBounds_odd frame he).1 hzS
    have hsw' : ¬ (0 ≤ frame.sGrade (z - (1, 0)) ∧
        frame.sGrade (z - (1, 0)) ≤ frame.child.periodDenominator + 2 * frame.child.num) :=
      fun h => hsw ((vSBounds_even frame hwn).2 h)
    omega

/-! ### The shifts `σ = ε U_p` and the offset `X` -/

theorem shortShift_of_eps_one (h : frame.eps = 1) : frame.shortShift = frame.uP := by
  unfold ChildFrame.shortShift ChildFrame.uP
  rw [h]
  ext <;> simp

theorem shortShift_of_eps_neg (h : frame.eps = -1) : frame.shortShift = -frame.uP := by
  unfold ChildFrame.shortShift ChildFrame.uP
  rw [h]
  ext <;> simp

theorem offsetX_of_W0 (h : frame.phaseW = 0) : frame.offsetX = frame.uP := by
  unfold ChildFrame.offsetX
  rw [if_pos h]

theorem offsetX_of_W1 (h : frame.phaseW = 1) : frame.offsetX = frame.uQ := by
  unfold ChildFrame.offsetX
  rw [if_neg (by rw [h]; norm_num)]

/-- `F` is periodic under the child kernel `U` (the first generator with `cU = 0`). -/
theorem F_kernel_add {F : Field} (hper : HasGeneratorPeriods frame.child F 0 frame.coherentConstantV) (w : Site) :
    F (w + frame.child.modifiedDeck.kernel) = F w := by
  rw [hper.1 w, add_zero]

theorem F_kernel_sub {F : Field} (hper : HasGeneratorPeriods frame.child F 0 frame.coherentConstantV) (w : Site) :
    F (w - frame.child.modifiedDeck.kernel) = F w := by
  have h := hper.1 (w - frame.child.modifiedDeck.kernel)
  rw [sub_add_cancel, add_zero] at h
  exact h.symm

/-! ### The core bound at the reduced point -/

/-- The core of the longitudinal case: `D_−(z) ∈ [−2, 0]` once `F z = F v`, `F (z − σ) = F (v + X)`, and the offers. -/
theorem dMinus_core {F Fp : Field} (hS : frame.StripInputs (frame.sheetMin Fp))
    (hagree : ∀ y ∈ frame.closedPolygon, F y = frame.sheetMin Fp y)
    (hper : HasGeneratorPeriods frame.child F 0 frame.coherentConstantV)
    (hoff : frame.LongitudinalOffers Fp) {z v : Site} (hvE : v ∈ frame.closedPolygon)
    (hvR : frame.longRange v) (hFz : F z = F v) (hsh : F (z - frame.shortShift) = F (v + frame.offsetX)) :
    -2 ≤ F z - F (z - frame.shortShift) ∧ F z - F (z - frame.shortShift) ≤ 0 := by
  have hvR' := hvR
  unfold ChildFrame.longRange at hvR'
  obtain ⟨hn0, hnd, hc2, hd3, -⟩ := frame.child_facts
  have hFv : F v = harmonicGrid v :=
    frame.harmonic_strip hS hagree hper v (by omega) (by omega)
  have hag : F (v + frame.offsetX) = min (frame.sheetA Fp (v + frame.offsetX))
      (frame.sheetC Fp (v + frame.offsetX)) :=
    hagree _ (hoff.mem v hvE hvR)
  have h1 := hoff.first v hvE hvR
  have h2 := hoff.second v hvE hvR
  rw [hFz, hFv, hsh, hag]
  constructor <;> omega

/-! ### The longitudinal exits of Q2 -/

/-- East exit (longitudinal): `−2 ≤ D_−(z) ≤ 0`. -/
theorem dMinus_long_east {F Fp : Field} (hS : frame.StripInputs (frame.sheetMin Fp))
    (hagree : ∀ y ∈ frame.closedPolygon, F y = frame.sheetMin Fp y)
    (hper : HasGeneratorPeriods frame.child F 0 frame.coherentConstantV)
    (hoff : frame.LongitudinalOffers Fp) {z : Site} (hz : z ∈ frame.closedPolygon)
    (hy : z + (1, 0) ∉ frame.closedPolygon) (hyT : vTBounds frame (z + (1, 0))) :
    -2 ≤ F z - F (z - frame.shortShift) ∧ F z - F (z - frame.shortShift) ≤ 0 := by
  obtain ⟨hvE, hvR⟩ := east_reduction frame hz hy hyT
  have hFz : F z = F (z - frame.child.modifiedDeck.kernel) := by
    exact (F_kernel_sub frame hper z).symm
  rcases frame.phaseW_cases with ⟨he, hw⟩ | ⟨he, hw⟩
  · -- W = 1, ε = 1: σ = U_p and X = U_q, and z − U_p = (z − U) + U_q
    have hsh : F (z - frame.shortShift) = F (z - frame.child.modifiedDeck.kernel + frame.offsetX) := by
      rw [shortShift_of_eps_one frame he, offsetX_of_W1 frame hw]
      congr 1
      rw [kernel_uP_uQ]
      abel
    exact dMinus_core frame hS hagree hper hoff hvE hvR hFz hsh
  · -- W = 0, ε = −1: σ = −U_p, X = U_p, and z + U_p = (z − U + U_p) + U
    have hsh : F (z - frame.shortShift) = F (z - frame.child.modifiedDeck.kernel + frame.offsetX) := by
      rw [shortShift_of_eps_neg frame he, offsetX_of_W0 frame hw]
      have e : z - -frame.uP = (z - frame.child.modifiedDeck.kernel + frame.uP) + frame.child.modifiedDeck.kernel := by
        rw [kernel_uP_uQ]
        abel
      rw [e, F_kernel_add frame hper]
    exact dMinus_core frame hS hagree hper hoff hvE hvR hFz hsh

/-- West exit (longitudinal): `−2 ≤ D_−(z) ≤ 0`. -/
theorem dMinus_long_west {F Fp : Field} (hS : frame.StripInputs (frame.sheetMin Fp))
    (hagree : ∀ y ∈ frame.closedPolygon, F y = frame.sheetMin Fp y)
    (hper : HasGeneratorPeriods frame.child F 0 frame.coherentConstantV)
    (hoff : frame.LongitudinalOffers Fp) {z : Site} (hz : z ∈ frame.closedPolygon)
    (hw : z - (1, 0) ∉ frame.closedPolygon) (hwT : vTBounds frame (z - (1, 0))) :
    -2 ≤ F z - F (z - frame.shortShift) ∧ F z - F (z - frame.shortShift) ≤ 0 := by
  have hvR := west_reduction frame hz hw hwT
  have hFz : F z = F z := rfl
  rcases frame.phaseW_cases with ⟨he, hw1⟩ | ⟨he, hw0⟩
  · -- W = 1, ε = 1: z − U_p = (z + U_q) − U
    have hsh : F (z - frame.shortShift) = F (z + frame.offsetX) := by
      rw [shortShift_of_eps_one frame he, offsetX_of_W1 frame hw1]
      have e : z - frame.uP = (z + frame.uQ) - frame.child.modifiedDeck.kernel := by
        rw [kernel_uP_uQ]
        abel
      rw [e, F_kernel_sub frame hper]
    exact dMinus_core frame hS hagree hper hoff hz hvR hFz hsh
  · -- W = 0, ε = −1: z + U_p = z + X
    have hsh : F (z - frame.shortShift) = F (z + frame.offsetX) := by
      rw [shortShift_of_eps_neg frame he, offsetX_of_W0 frame hw0]
      congr 1
      abel
    exact dMinus_core frame hS hagree hper hoff hz hvR hFz hsh

/-! ### The full range of `D_−` at the sites with a horizontal exit -/

theorem dMinus_range {F Fp : Field} (hS : frame.StripInputs (frame.sheetMin Fp))
    (hagree : ∀ y ∈ frame.closedPolygon, F y = frame.sheetMin Fp y)
    (hper : HasGeneratorPeriods frame.child F 0 frame.coherentConstantV)
    (hoff : frame.LongitudinalOffers Fp) (hn : 3 ≤ frame.child.num) {z : Site}
    (hz : z ∈ frame.closedPolygon)
    (hex : z + (1, 0) ∉ frame.closedPolygon ∨ z - (1, 0) ∉ frame.closedPolygon) :
    -2 ≤ F z - F (z - frame.shortShift) ∧ F z - F (z - frame.shortShift) ≤ 0 := by
  obtain ⟨hnd, hd⟩ : frame.child.num ≤ 2 * frame.child.den - 3 ∧ 3 ≤ frame.child.den := by
    obtain ⟨-, h1, -, h3, -⟩ := frame.child_facts
    omega
  rcases hex with hy | hw
  · by_cases hyT : vTBounds frame (z + (1, 0))
    · exact dMinus_long_east frame hS hagree hper hoff hz hy hyT
    · have h := dMinus_zero_of_eastUpper frame hS hagree hper hn hnd hz hyT
      constructor <;> linarith
  · by_cases hwT : vTBounds frame (z - (1, 0))
    · exact dMinus_long_west frame hS hagree hper hoff hz hw hwT
    · have h := dMinus_neg_two_of_westLower frame hS hagree hper hn hnd hd hz hwT
      constructor <;> linarith

/-! ### The reflection in the centre `R` -/

theorem sGrade_sub_gen (a b : Site) : frame.sGrade (a - b) = frame.sGrade a - frame.sGrade b := by
  unfold ChildFrame.sGrade
  simp only [Prod.fst_sub, Prod.snd_sub]
  ring

theorem tGrade_sub_gen (a b : Site) : frame.tGrade (a - b) = frame.tGrade a - frame.tGrade b := by
  unfold ChildFrame.tGrade
  simp only [Prod.fst_sub, Prod.snd_sub]
  ring

theorem centre_coords : frame.centre = (frame.child.num + 1, 2 * frame.child.num + frame.child.den - 1) := by
  unfold ChildFrame.centre
  rw [kernel_coords, frame.child_modifiedDeck_transverse]
  ext <;> simp
  all_goals ring

theorem centre_tGrade : frame.tGrade frame.centre = frame.child.den + frame.child.num - frame.child.periodDenominator := by
  rw [centre_coords, (frame.child_facts).2.2.2.2]
  unfold ChildFrame.tGrade
  ring

theorem centre_sGrade : frame.sGrade frame.centre = frame.child.periodDenominator + 2 * frame.child.num := by
  rw [centre_coords, (frame.child_facts).2.2.2.2]
  unfold ChildFrame.sGrade
  ring

theorem centre_even : EvenSite frame.centre := by
  rw [centre_coords]
  have hp : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  unfold EvenSite
  show ((frame.child.num + 1) + (2 * frame.child.num + frame.child.den - 1)) % 2 = 0
  omega

/-- The centre `R` maps `E` to itself: `z ∈ E ↔ R − z ∈ E`. -/
theorem centre_sub_mem_iff (z : Site) : frame.centre - z ∈ frame.closedPolygon ↔ z ∈ frame.closedPolygon := by
  rw [mem_E_iff_bounds, mem_E_iff_bounds]
  have hp : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hpar : EvenSite (frame.centre - z) ↔ EvenSite z := by
    have hc : (frame.centre.1 + frame.centre.2) % 2 = 0 := frame.centre_even
    unfold EvenSite
    show ((frame.centre - z).1 + (frame.centre - z).2) % 2 = 0 ↔ (z.1 + z.2) % 2 = 0
    rw [Prod.fst_sub, Prod.snd_sub]
    omega
  have ht := frame.tGrade_sub_gen frame.centre z
  have hs := frame.sGrade_sub_gen frame.centre z
  have hct := frame.centre_tGrade
  have hcs := frame.centre_sGrade
  have hT0 := frame.T_nonneg
  obtain ⟨hn0, hnd, hc2, hd3, -⟩ := frame.child_facts
  by_cases he : EvenSite z
  · have hze : EvenSite (frame.centre - z) := hpar.2 he
    rw [vTBounds_iff_even frame he, vSBounds_even frame he, vTBounds_iff_even frame hze,
      vSBounds_even frame hze]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      refine ⟨⟨by omega, by omega⟩, by omega, by omega⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      refine ⟨⟨by omega, by omega⟩, by omega, by omega⟩
  · have hze : ¬ EvenSite (frame.centre - z) := fun h => he (hpar.1 h)
    rw [vTBounds_iff_odd frame he, vSBounds_odd frame he, vTBounds_iff_odd frame hze,
      vSBounds_odd frame hze]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      refine ⟨⟨by omega, by omega⟩, by omega, by omega⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      refine ⟨⟨by omega, by omega⟩, by omega, by omega⟩

/-- The reflection of `F` in the centre, at every site. -/
theorem F_centre_sub {F M : Field} (hH : frame.HeightInputs M)
    (hagree : ∀ y ∈ frame.closedPolygon, F y = M y)
    (hper : HasGeneratorPeriods frame.child F 0 frame.coherentConstantV) (z : Site) :
    F (frame.centre - z) = F z - frame.tGrade z + frame.symmetryConstant := by
  have hper' : HasGeneratorPeriods frame.child F frame.coherentConstantU frame.coherentConstantV := by
    rw [frame.coherentConstantU_eq_zero]
    exact hper
  exact frame.reflection_of_heightInputs hH hagree hper' z

/-- Q2, the reflection: `D_+(z) = D_−(R − z) + 2` on the V arcs, so `D_+ ∈ [0, 2]` there. -/
theorem leftRange_of_dMinus {F Fp : Field} (hS : frame.StripInputs (frame.sheetMin Fp))
    (hH : frame.HeightInputs (frame.sheetMin Fp))
    (hagree : ∀ y ∈ frame.closedPolygon, F y = frame.sheetMin Fp y)
    (hper : HasGeneratorPeriods frame.child F 0 frame.coherentConstantV)
    (hoff : frame.LongitudinalOffers Fp) (hn : 3 ≤ frame.child.num) {z : Site}
    (hz : OnVArc frame.closedPolygon z) :
    starDiff F frame.shortShift z = 0 ∨ starDiff F frame.shortShift z = 1 ∨
      starDiff F frame.shortShift z = 2 := by
  obtain ⟨hzE, hex⟩ : z ∈ frame.closedPolygon ∧
      (z + (-1, 0) ∉ frame.closedPolygon ∨ z + (1, 0) ∉ frame.closedPolygon) := by
    rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1, Or.inl h2⟩
    · exact ⟨h1, Or.inr h2⟩
  have hu : frame.centre - z ∈ frame.closedPolygon := (frame.centre_sub_mem_iff z).2 hzE
  have hexu : (frame.centre - z) + (1, 0) ∉ frame.closedPolygon ∨
      (frame.centre - z) - (1, 0) ∉ frame.closedPolygon := by
    rcases hex with h | h
    · left
      intro hm
      apply h
      have := (frame.centre_sub_mem_iff (z + (-1, 0))).1
      apply this
      have e : frame.centre - (z + (-1, 0)) = frame.centre - z + (1, 0) := by
        ext <;> simp
        all_goals ring
      rw [e]
      exact hm
    · right
      intro hm
      apply h
      have := (frame.centre_sub_mem_iff (z + (1, 0))).1
      apply this
      have e : frame.centre - (z + (1, 0)) = frame.centre - z - (1, 0) := by
        ext <;> simp
        all_goals ring
      rw [e]
      exact hm
  have hD := dMinus_range frame hS hagree hper hoff hn hu hexu
  have hr1 := F_centre_sub frame hH hagree hper z
  have hr2 := F_centre_sub frame hH hagree hper (z + frame.shortShift)
  have hts := frame.tGrade_add_shortShift z
  have e2 : frame.centre - z - frame.shortShift = frame.centre - (z + frame.shortShift) := by abel
  unfold starDiff
  rw [e2] at hD
  rw [sub_add_eq_add_sub] at hr2
  have hsub : F (frame.centre - z) = F z - frame.tGrade z + frame.symmetryConstant := by
    rw [← hr1]
  unfold ChildFrame.shortShift at *
  omega

end ChildFrame

end FLatticePaper.Induction

namespace FLatticePaper.Induction

open Farey

/-- The V-arc range of Q2, from the named offers, the sewn data and the reflection: `VArcInputs.leftRange`. -/
theorem vArcInputs_of_longitudinal {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) {F Fp : Field}
    (hS : (frameAt word).StripInputs ((frameAt word).sheetMin Fp))
    (hH : (frameAt word).HeightInputs ((frameAt word).sheetMin Fp))
    (hagree : ∀ y ∈ (frameAt word).closedPolygon, F y = (frameAt word).sheetMin Fp y)
    (hper : HasGeneratorPeriods (frameAt word).child F 0 (frameAt word).coherentConstantV)
    (hoff : (frameAt word).LongitudinalOffers Fp) :
    VArcInputs (frameAt word) F :=
  ⟨fun _ hz => (frameAt word).leftRange_of_dMinus hS hH hagree hper hoff (child_num_ge_three h) hz⟩

end FLatticePaper.Induction

