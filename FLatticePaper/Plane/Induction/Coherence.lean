import FLatticePaper.Plane.Induction.Bands
import FLatticePaper.Plane.Induction.Periodization
import FLatticePaper.Plane.Induction.PolygonGeometry

namespace FLatticePaper.Induction
open Farey Construction

/-- The harmonic identity `h₀(c − y) + t(y) = h₀(y) + h₀(c)` for `c = (N − D + 1, N + D − 1)`, whose
coordinate sum is even, so that the parity terms of `h₀` cancel. -/
theorem harmonicGrid_shift (N D : ℤ) (y : Site) :
    harmonicGrid ((N - D + 1, N + D - 1) - y) + (N * y.1 - D * y.2) =
      harmonicGrid y + harmonicGrid (N - D + 1, N + D - 1) := by
  have e1 := harmonicGrid_exact ((N - D + 1, N + D - 1) - y)
  have e2 := harmonicGrid_exact y
  have e3 := harmonicGrid_exact (N - D + 1, N + D - 1)
  simp only [Prod.fst_sub, Prod.snd_sub] at e1
  dsimp only at e3
  have hp1 : (N - D + 1 - y.1 + (N + D - 1 - y.2)) % 2 = (y.1 + y.2) % 2 := by omega
  have hp2 : (N - D + 1 + (N + D - 1)) % 2 = 0 := by omega
  have key : 4 * (harmonicGrid ((N - D + 1, N + D - 1) - y) + (N * y.1 - D * y.2) - harmonicGrid y -
      harmonicGrid (N - D + 1, N + D - 1)) = 0 := by
    linear_combination e1 - e2 - e3 - hp1 + hp2
  linarith

namespace ChildFrame
variable (frame : ChildFrame)

/-! ### The centre, the deck vectors and their grades -/

theorem T_pos : 0 < frame.child.periodDenominator := by
  obtain ⟨hN, hND, hdiff, hD3, hTdef⟩ := frame.child_facts
  obtain ⟨-, hT2, -, -, -, -⟩ := T_bounds hN hdiff hD3
  linarith

theorem centre_eq :
    frame.centre = (frame.child.num + 1, 2 * frame.child.num + frame.child.den - 1) := by
  rw [ChildFrame.centre, frame.child_modifiedDeck_kernel, frame.child_modifiedDeck_transverse]
  ext <;> simp only [Prod.fst_add, Prod.snd_add]
  all_goals ring

theorem tGrade_sub (a b : Site) : frame.tGrade (a - b) = frame.tGrade a - frame.tGrade b := by
  unfold ChildFrame.tGrade
  simp only [Prod.fst_sub, Prod.snd_sub]
  ring

theorem sGrade_sub (a b : Site) : frame.sGrade (a - b) = frame.sGrade a - frame.sGrade b := by
  unfold ChildFrame.sGrade
  simp only [Prod.fst_sub, Prod.snd_sub]
  ring

theorem tGrade_centre :
    frame.tGrade frame.centre = frame.child.den + frame.child.num - frame.child.periodDenominator := by
  rw [centre_eq]
  unfold ChildFrame.tGrade Fraction.periodDenominator
  dsimp only
  ring

theorem sGrade_centre : frame.sGrade frame.centre = frame.child.periodDenominator + 2 * frame.child.num := by
  rw [centre_eq]
  unfold ChildFrame.sGrade Fraction.periodDenominator
  dsimp only
  ring

theorem evenSite_centre : EvenSite frame.centre := by
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  rw [centre_eq]
  unfold EvenSite
  dsimp only
  omega

theorem evenSite_centre_sub (z : Site) : EvenSite (frame.centre - z) ↔ EvenSite z := by
  have hR := frame.evenSite_centre
  unfold EvenSite at hR ⊢
  simp only [Prod.fst_sub, Prod.snd_sub]
  constructor <;> intro h <;> omega

theorem tGrade_modTransverse :
    frame.tGrade frame.child.modifiedDeck.transverse = -frame.child.periodDenominator := by
  rw [frame.child_modifiedDeck_transverse]
  unfold ChildFrame.tGrade Fraction.periodDenominator
  dsimp only
  ring

/-- The shifted transverse vector `V + I`. -/
theorem VI_eq : frame.child.modifiedDeck.transverse + (1, -1) =
    (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 1) := by
  rw [frame.child_modifiedDeck_transverse]
  ext <;> simp only [Prod.fst_add, Prod.snd_add]
  all_goals ring

theorem tGrade_VI : frame.tGrade (frame.child.modifiedDeck.transverse + (1, -1)) =
    frame.child.den + frame.child.num - frame.child.periodDenominator := by
  rw [VI_eq]
  unfold ChildFrame.tGrade Fraction.periodDenominator
  dsimp only
  ring

/-- `R − (y + U) = (V + I) − y`. -/
theorem centre_sub_U (y : Site) :
    frame.centre - (y + frame.child.modifiedDeck.combine 1 0) =
      (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 1) - y := by
  rw [centre_eq, frame.child_modifiedDeck_combine]
  ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
  all_goals ring

theorem site_add_combine_comb (y : Site) (i j i' j' : ℤ) :
    y + frame.child.modifiedDeck.combine i j + frame.child.modifiedDeck.combine i' j' =
      y + frame.child.modifiedDeck.combine (i + i') (j + j') := by
  rw [frame.child_modifiedDeck_combine, frame.child_modifiedDeck_combine,
    frame.child_modifiedDeck_combine]
  ext <;> simp only [Prod.fst_add, Prod.snd_add]
  all_goals ring

theorem periodIncrement_child (cU cV : ℤ) (y : Site) (i j : ℤ) :
    periodIncrement frame.child cU cV y i j =
      i * cU + j * (cV + frame.tGrade y) - frame.child.periodDenominator * chooseTwo j := by
  unfold periodIncrement ChildFrame.tGrade Fraction.transverseGrade
  ring

theorem mem_hBand_iff (z : Site) :
    z ∈ frame.hBand ↔ z ∈ frame.closedPolygon ∧
      (if EvenSite z then 2 ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den + frame.child.num - 2
        else frame.child.num ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den) :=
  Iff.rfl

theorem mem_vBand_iff (z : Site) :
    z ∈ frame.vBand ↔ z ∈ frame.closedPolygon ∧
      (if EvenSite z then 0 ≤ frame.sGrade z ∧ frame.sGrade z ≤ 2 * frame.child.num
        else 2 - frame.child.den + frame.child.num ≤ frame.sGrade z ∧
          frame.sGrade z ≤ frame.child.den + frame.child.num - 2) :=
  Iff.rfl

/-! ### The centre preserves `E` -/

/-- `E` is symmetric under `z ↦ R − z`. -/
theorem centre_sub_mem {z : Site} (hz : z ∈ frame.closedPolygon) :
    frame.centre - z ∈ frame.closedPolygon := by
  have hz' := (frame.mem_closedPolygon_iff z).mp hz
  rw [frame.mem_closedPolygon_iff, frame.tGrade_sub, frame.sGrade_sub, frame.tGrade_centre,
    frame.sGrade_centre]
  rcases hz' with ⟨hE, t1, t2, s1, s2⟩ | ⟨hO, t1, t2, s1, s2⟩
  · exact Or.inl ⟨(frame.evenSite_centre_sub z).mpr hE, by linarith, by linarith, by linarith, by linarith⟩
  · exact Or.inr ⟨fun h' => hO ((frame.evenSite_centre_sub z).mp h'), by linarith, by linarith, by linarith,
      by linarith⟩

/-! ### Single steps of the period law -/

section Steps

variable {M : Site → ℤ}

/-- The vertical step: `M(y + V) = M(y) + c_V + t(y)` for `y, y + V ∈ E`. -/
theorem stepV (h : frame.HeightInputs M) {y : Site} (hy : y ∈ frame.closedPolygon)
    (hyV : y + frame.child.modifiedDeck.combine 0 1 ∈ frame.closedPolygon) :
    M (y + frame.child.modifiedDeck.combine 0 1) = M y + frame.coherentConstantV + frame.tGrade y := by
  obtain ⟨-, -, hlow, -, -, -⟩ := frame.closedPolygon_pair hy hyV
  have hlow' := hlow rfl
  have hyH : y ∈ frame.hBand := by
    rw [frame.mem_hBand_iff]
    refine ⟨hy, ?_⟩
    rcases (frame.mem_closedPolygon_iff y).mp hy with ⟨hE, -, t2, -, -⟩ | ⟨hO, -, t2, -, -⟩
    · rw [if_pos hE] at hlow' ⊢
      exact ⟨hlow', t2⟩
    · rw [if_neg hO] at hlow' ⊢
      exact ⟨hlow', t2⟩
  have hM0 : M y = 0 := h.zero_on_hBand y hyH
  have hwH : frame.centre - (y + frame.child.modifiedDeck.combine 0 1) ∈ frame.hBand := by
    rw [frame.mem_hBand_iff]
    refine ⟨frame.centre_sub_mem hyV, ?_⟩
    have hpar : EvenSite (frame.centre - (y + frame.child.modifiedDeck.combine 0 1)) ↔ EvenSite y :=
      (frame.evenSite_centre_sub _).trans (frame.evenSite_add_combine y 0 1)
    have ht : frame.tGrade (frame.centre - (y + frame.child.modifiedDeck.combine 0 1)) =
        frame.child.den + frame.child.num - frame.tGrade y := by
      rw [frame.tGrade_sub, frame.tGrade_centre, frame.tGrade_add_combine]
      ring
    rw [ht]
    rcases (frame.mem_closedPolygon_iff y).mp hy with ⟨hE, -, t2, -, -⟩ | ⟨hO, -, t2, -, -⟩
    · rw [if_pos (hpar.mpr hE)]
      rw [if_pos hE] at hlow'
      constructor <;> linarith
    · rw [if_neg (fun h' => hO (hpar.mp h'))]
      rw [if_neg hO] at hlow'
      constructor <;> linarith
  have hMw := h.zero_on_hBand _ hwH
  have hrefl := h.reflection (frame.centre - (y + frame.child.modifiedDeck.combine 0 1))
    (frame.centre_sub_mem hyV)
  rw [sub_sub_cancel, hMw] at hrefl
  have ht : frame.tGrade (frame.centre - (y + frame.child.modifiedDeck.combine 0 1)) =
      frame.child.den + frame.child.num - frame.tGrade y := by
    rw [frame.tGrade_sub, frame.tGrade_centre, frame.tGrade_add_combine]
    ring
  rw [ht] at hrefl
  rw [hrefl, hM0]
  unfold ChildFrame.coherentConstantV ChildFrame.symmetryConstant
  rw [frame.tGrade_centre, frame.tGrade_modTransverse]
  ring

/-- The horizontal step: `M(y + U) = M(y) + c_U` for `y, y + U ∈ E`. -/
theorem stepU (h : frame.HeightInputs M) {y : Site} (hy : y ∈ frame.closedPolygon)
    (hyU : y + frame.child.modifiedDeck.combine 1 0 ∈ frame.closedPolygon) :
    M (y + frame.child.modifiedDeck.combine 1 0) = M y + frame.coherentConstantU := by
  obtain ⟨-, -, -, -, hup, -⟩ := frame.closedPolygon_pair hy hyU
  have hup' := hup rfl
  have hyV : y ∈ frame.vBand := by
    rw [frame.mem_vBand_iff]
    refine ⟨hy, ?_⟩
    rcases (frame.mem_closedPolygon_iff y).mp hy with ⟨hE, -, -, s1, -⟩ | ⟨hO, -, -, s1, -⟩
    · rw [if_pos hE] at hup' ⊢
      exact ⟨s1, hup'⟩
    · rw [if_neg hO] at hup' ⊢
      exact ⟨s1, hup'⟩
  have hMy : M y = harmonicGrid y := h.harmonic_on_vBand y hyV
  have hpar : EvenSite (frame.centre - (y + frame.child.modifiedDeck.combine 1 0)) ↔ EvenSite y :=
    (frame.evenSite_centre_sub _).trans (frame.evenSite_add_combine y 1 0)
  have hwV : frame.centre - (y + frame.child.modifiedDeck.combine 1 0) ∈ frame.vBand := by
    rw [frame.mem_vBand_iff]
    refine ⟨frame.centre_sub_mem hyU, ?_⟩
    have hs : frame.sGrade (frame.centre - (y + frame.child.modifiedDeck.combine 1 0)) =
        2 * frame.child.num - frame.sGrade y := by
      rw [frame.sGrade_sub, frame.sGrade_centre, frame.sGrade_add_combine]
      ring
    rw [hs]
    rcases (frame.mem_closedPolygon_iff y).mp hy with ⟨hE, -, -, s1, s2⟩ | ⟨hO, -, -, s1, s2⟩
    · rw [if_pos (hpar.mpr hE)]
      rw [if_pos hE] at hup'
      constructor <;> linarith
    · rw [if_neg (fun h' => hO (hpar.mp h'))]
      rw [if_neg hO] at hup'
      constructor <;> linarith
  have hMw := h.harmonic_on_vBand _ hwV
  have hrefl := h.reflection (frame.centre - (y + frame.child.modifiedDeck.combine 1 0))
    (frame.centre_sub_mem hyU)
  rw [sub_sub_cancel, hMw] at hrefl
  have ht : frame.tGrade (frame.centre - (y + frame.child.modifiedDeck.combine 1 0)) =
      frame.child.den + frame.child.num - frame.child.periodDenominator - frame.tGrade y := by
    rw [frame.tGrade_sub, frame.tGrade_centre, frame.tGrade_add_combine]
    ring
  rw [ht, frame.centre_sub_U] at hrefl
  have hsh := harmonicGrid_shift frame.child.num frame.child.den y
  rw [hrefl, hMy]
  unfold ChildFrame.coherentConstantU ChildFrame.symmetryConstant
  rw [tGrade_VI, VI_eq]
  have hty : frame.tGrade y = frame.child.num * y.1 - frame.child.den * y.2 := rfl
  linarith [hsh, hty]

end Steps

/-! ### Membership of the intermediate points -/

theorem combine_zero_zero (frame : ChildFrame) :
    frame.child.modifiedDeck.combine 0 0 = 0 := by
  rw [frame.child_modifiedDeck_combine]
  ext <;> simp

theorem mem_plusU {frame : ChildFrame} {y : Site} (hy : y ∈ frame.closedPolygon)
    (hs : frame.sGrade y ≤ if EvenSite y then 2 * frame.child.num else frame.child.den + frame.child.num - 2) :
    y + frame.child.modifiedDeck.combine 1 0 ∈ frame.closedPolygon := by
  have hT := frame.T_pos
  rcases (frame.mem_closedPolygon_iff y).mp hy with ⟨hE, t1, t2, s1, s2⟩ | ⟨hO, t1, t2, s1, s2⟩
  · rw [if_pos hE] at hs
    exact (frame.mem_translate_iff y 1 0).mpr (Or.inl ⟨hE, by linarith, by linarith, by linarith, by linarith⟩)
  · rw [if_neg hO] at hs
    exact (frame.mem_translate_iff y 1 0).mpr (Or.inr ⟨hO, by linarith, by linarith, by linarith, by linarith⟩)

theorem mem_plusV {frame : ChildFrame} {y : Site} (hy : y ∈ frame.closedPolygon)
    (ht : (if EvenSite y then 2 else frame.child.num) ≤ frame.tGrade y) :
    y + frame.child.modifiedDeck.combine 0 1 ∈ frame.closedPolygon := by
  have hT := frame.T_pos
  rcases (frame.mem_closedPolygon_iff y).mp hy with ⟨hE, t1, t2, s1, s2⟩ | ⟨hO, t1, t2, s1, s2⟩
  · rw [if_pos hE] at ht
    exact (frame.mem_translate_iff y 0 1).mpr (Or.inl ⟨hE, by linarith, by linarith, by linarith, by linarith⟩)
  · rw [if_neg hO] at ht
    exact (frame.mem_translate_iff y 0 1).mpr (Or.inr ⟨hO, by linarith, by linarith, by linarith, by linarith⟩)

theorem mem_minusV {frame : ChildFrame} {y : Site} (hy : y ∈ frame.closedPolygon)
    (ht : frame.tGrade y ≤ (if EvenSite y then frame.child.den + frame.child.num - 2 else frame.child.den) -
      frame.child.periodDenominator) :
    y + frame.child.modifiedDeck.combine 0 (-1) ∈ frame.closedPolygon := by
  have hT := frame.T_pos
  rcases (frame.mem_closedPolygon_iff y).mp hy with ⟨hE, t1, t2, s1, s2⟩ | ⟨hO, t1, t2, s1, s2⟩
  · rw [if_pos hE] at ht
    exact (frame.mem_translate_iff y 0 (-1)).mpr (Or.inl ⟨hE, by linarith, by linarith, by linarith, by linarith⟩)
  · rw [if_neg hO] at ht
    exact (frame.mem_translate_iff y 0 (-1)).mpr (Or.inr ⟨hO, by linarith, by linarith, by linarith, by linarith⟩)

theorem chooseTwo_zero : chooseTwo 0 = 0 := by decide
theorem chooseTwo_one : chooseTwo 1 = 0 := by decide
theorem chooseTwo_neg_one : chooseTwo (-1) = 1 := by decide

/-! ### Coherence -/

/-- Coherence: the three height inputs give the period law on `E` with the coherent constants. -/
theorem respectsPeriodsOn_of_heightInputs {M : Site → ℤ} (h : frame.HeightInputs M) :
    RespectsPeriodsOn frame.child frame.coherentConstantU frame.coherentConstantV frame.closedPolygon M := by
  unfold RespectsPeriodsOn
  intro y hy i j hy'
  obtain ⟨hi, hj, hjp, hjm, hip, him⟩ := frame.closedPolygon_pair hy hy'
  rw [frame.periodIncrement_child]
  have hT := frame.T_pos
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl
  · -- (i, j) = (-1, -1)
    have hzm := mem_minusV hy (hjm rfl)
    have ez : y + frame.child.modifiedDeck.combine 0 (-1) + frame.child.modifiedDeck.combine 0 1 = y := by
      rw [frame.site_add_combine_comb]
      norm_num [frame.combine_zero_zero]
    have key1 := frame.stepV h hzm (by rw [ez]; exact hy)
    rw [ez] at key1
    have hz0U : y + frame.child.modifiedDeck.combine (-1) (-1) + frame.child.modifiedDeck.combine 1 0 =
        y + frame.child.modifiedDeck.combine 0 (-1) := by
      rw [frame.site_add_combine_comb]
      norm_num
    have key2 := frame.stepU h hy' (by rw [hz0U]; exact hzm)
    rw [hz0U] at key2
    have ht0 : frame.tGrade (y + frame.child.modifiedDeck.combine 0 (-1)) =
        frame.tGrade y + frame.child.periodDenominator := by
      rw [frame.tGrade_add_combine]
      ring
    rw [chooseTwo_neg_one]
    linarith
  · -- (i, j) = (-1, 0)
    have hz : y + frame.child.modifiedDeck.combine (-1) 0 + frame.child.modifiedDeck.combine 1 0 = y := by
      rw [frame.site_add_combine_comb]
      norm_num [frame.combine_zero_zero]
    have key := frame.stepU h hy' (by rw [hz]; exact hy)
    rw [hz] at key
    rw [chooseTwo_zero]
    linarith
  · -- (i, j) = (-1, 1)
    have hz0 := mem_plusV hy (hjp rfl)
    have key1 := frame.stepV h hy hz0
    have hzU : y + frame.child.modifiedDeck.combine (-1) 1 + frame.child.modifiedDeck.combine 1 0 =
        y + frame.child.modifiedDeck.combine 0 1 := by
      rw [frame.site_add_combine_comb]
      norm_num
    have key2 := frame.stepU h hy' (by rw [hzU]; exact hz0)
    rw [hzU] at key2
    rw [chooseTwo_one]
    linarith
  · -- (i, j) = (0, -1)
    have hz : y + frame.child.modifiedDeck.combine 0 (-1) + frame.child.modifiedDeck.combine 0 1 = y := by
      rw [frame.site_add_combine_comb]
      norm_num [frame.combine_zero_zero]
    have key := frame.stepV h hy' (by rw [hz]; exact hy)
    rw [hz] at key
    have ht0 : frame.tGrade (y + frame.child.modifiedDeck.combine 0 (-1)) =
        frame.tGrade y + frame.child.periodDenominator := by
      rw [frame.tGrade_add_combine]
      ring
    rw [chooseTwo_neg_one]
    linarith
  · -- (i, j) = (0, 0)
    rw [frame.combine_zero_zero, add_zero, chooseTwo_zero]
    ring
  · -- (i, j) = (0, 1)
    have key := frame.stepV h hy hy'
    rw [chooseTwo_one]
    linarith
  · -- (i, j) = (1, -1)
    have hz0 := mem_plusU hy (hip rfl)
    have key1 := frame.stepU h hy hz0
    have hzV : y + frame.child.modifiedDeck.combine 1 (-1) + frame.child.modifiedDeck.combine 0 1 =
        y + frame.child.modifiedDeck.combine 1 0 := by
      rw [frame.site_add_combine_comb]
      norm_num
    have key2 := frame.stepV h hy' (by rw [hzV]; exact hz0)
    rw [hzV] at key2
    have ht1 : frame.tGrade (y + frame.child.modifiedDeck.combine 1 (-1)) =
        frame.tGrade y + frame.child.periodDenominator := by
      rw [frame.tGrade_add_combine]
      ring
    rw [chooseTwo_neg_one]
    linarith
  · -- (i, j) = (1, 0)
    have key := frame.stepU h hy hy'
    rw [chooseTwo_zero]
    linarith
  · -- (i, j) = (1, 1)
    have hz0 := mem_plusU hy (hip rfl)
    have key1 := frame.stepU h hy hz0
    have ez : y + frame.child.modifiedDeck.combine 1 0 + frame.child.modifiedDeck.combine 0 1 =
        y + frame.child.modifiedDeck.combine 1 1 := by
      rw [frame.site_add_combine_comb]
      norm_num
    have key2 := frame.stepV h hz0 (by rw [ez]; exact hy')
    rw [ez] at key2
    have ht0 : frame.tGrade (y + frame.child.modifiedDeck.combine 1 0) = frame.tGrade y := by
      rw [frame.tGrade_add_combine]
      ring
    rw [chooseTwo_one]
    linarith

/-- Hence the sewn standard exists and is unique. -/
theorem exists_unique_sewn_of_heightInputs {M : Site → ℤ} (h : frame.HeightInputs M) :
    ∃ F : Field, (∀ y ∈ frame.closedPolygon, F y = M y) ∧
      HasGeneratorPeriods frame.child F frame.coherentConstantU frame.coherentConstantV ∧
      ∀ G : Field, (∀ y ∈ frame.closedPolygon, G y = M y) →
        HasGeneratorPeriods frame.child G frame.coherentConstantU frame.coherentConstantV → G = F :=
  frame.exists_unique_periodization (frame.respectsPeriodsOn_of_heightInputs h)

end ChildFrame

end FLatticePaper.Induction
