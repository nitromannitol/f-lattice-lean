import FLatticePaper.Plane.Induction.TwosChainMinus
import FLatticePaper.Plane.Induction.FreeTraceBox
import FLatticePaper.Plane.Induction.CanonicalSigned

/-! The free H and V sets of the twos frame `2^(k+1)`, in closed form (the sets `freeH`, `freeV` of `ChildFrame`).

With `d = 2k+5` (the denominator), `n = d-2 = 2k+3` (the numerator) and `T = 2(d²-2)` (the period denominator), the free H trace
is the bottom boundary with `t = n z₁ - d z₂` in the H spectrum, and the free V cut is the left boundary with
`s = (2d-2) z₁ + 2 z₂` in the V spectrum. The arithmetic lemmas below decide both sets for every `d`; the bridges specialise them.
The result is the explicit classes `FreeHSite` and `FreeVSite` of `TwosEPolicy`. -/

namespace FLatticePaper.TwosEPolicy

open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey
open scoped Classical

/-- The V classes: the grades `t` and `s` of a closed-polygon point with `s` in `[0, 2d-4]` force `z₁ ∈ {-1, 0}`. -/
theorem twosFreeV_arith (d z1 z2 : ℤ) (hd : 5 ≤ d)
    (hC : (2 - 2 * (d * d - 2) ≤ (d - 2) * z1 - d * z2 ∧ (d - 2) * z1 - d * z2 ≤ 2 * d - 4) ∨
      (d - 2 - 2 * (d * d - 2) ≤ (d - 2) * z1 - d * z2 ∧ (d - 2) * z1 - d * z2 ≤ d))
    (hV0 : 0 ≤ (2 * d - 2) * z1 + 2 * z2) (hV1 : (2 * d - 2) * z1 + 2 * z2 ≤ 2 * d - 4) :
    (z1 = 0 ∧ 0 ≤ z2 ∧ z2 ≤ d - 2) ∨ (z1 = -1 ∧ d - 1 ≤ z2 ∧ z2 ≤ 2 * d - 3) := by
  have e2 : (2 * d - 2) * z1 + 2 * z2 = 2 * ((d - 1) * z1 + z2) := by ring
  have hu0 : 0 ≤ (d - 1) * z1 + z2 := by linarith
  have hu1 : (d - 1) * z1 + z2 ≤ d - 2 := by linarith
  have key : (d * d - 2) * z1 = ((d - 2) * z1 - d * z2) + d * ((d - 1) * z1 + z2) := by ring
  have hdu : d * ((d - 1) * z1 + z2) ≤ d * d - 2 * d := by
    have h := mul_le_mul_of_nonneg_left hu1 (by linarith : (0 : ℤ) ≤ d)
    nlinarith [h]
  have hdu0 : 0 ≤ d * ((d - 1) * z1 + z2) := mul_nonneg (by linarith) hu0
  have hT : 0 < d * d - 2 := by nlinarith
  have hz1a : z1 ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ z1 := by omega
    have hm := mul_le_mul_of_nonneg_left h2 hT.le
    rcases hC with ⟨_, h1⟩ | ⟨_, h1⟩ <;> nlinarith
  have hz1b : z1 ≠ 1 := by
    intro h1
    subst h1
    rcases hC with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> nlinarith
  have hz1c : -1 ≤ z1 := by
    by_contra h
    have h2 : z1 ≤ -2 := by omega
    have hm := mul_le_mul_of_nonneg_left h2 hT.le
    rcases hC with ⟨h3, _⟩ | ⟨h3, _⟩ <;> nlinarith
  have hz1 : z1 = 0 ∨ z1 = -1 := by omega
  rcases hz1 with rfl | rfl
  · left
    refine ⟨rfl, by linarith, by linarith⟩
  · right
    refine ⟨rfl, by linarith, by linarith⟩

/-- The H classes: the grade `t = n z₁ - d z₂` in the H spectrum, with the box `1 ≤ z₁ ≤ d`, decides the free H site. -/
theorem twosFreeH_arith (d z1 z2 t : ℤ) (hd : 5 ≤ d) (hodd : d % 2 = 1) (ht : t = (d - 2) * z1 - d * z2)
    (hb1 : 1 ≤ z1) (hb2 : z1 ≤ d)
    (hsp : (t % 2 = 0 ∧ 2 ≤ t ∧ t ≤ 2 * d - 4) ∨ (t % 2 = 1 ∧ d - 2 ≤ t ∧ t ≤ d)) :
    (z1 = 1 ∧ z2 = 0) ∨ (2 ≤ z1 ∧ z1 ≤ d - 1 ∧ z2 = z1 - 2) ∨ (z1 = d ∧ z2 = d - 3) := by
  obtain ⟨q, hq⟩ : ∃ q : ℤ, q = z1 - z2 - 2 := ⟨_, rfl⟩
  have htq : t = d * q + (2 * d - 2 * z1) := by rw [ht, hq]; ring
  have hlo : 2 ≤ t := by
    rcases hsp with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> omega
  have hhi : t ≤ 2 * d - 4 := by
    rcases hsp with ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> omega
  have hq2 : q ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ q := by omega
    have hm : d * 2 ≤ d * q := mul_le_mul_of_nonneg_left h2 (by omega)
    linarith
  have hq1 : -1 ≤ q := by
    by_contra h
    have h2 : q ≤ -2 := by omega
    have hm : d * q ≤ d * (-2) := mul_le_mul_of_nonneg_left h2 (by omega)
    linarith
  have hcases : q = -1 ∨ q = 0 ∨ q = 1 := by omega
  rcases hcases with rfl | rfl | rfl
  · rw [htq] at hsp
    rcases hsp with ⟨h1, -⟩ | ⟨h1, h2, h3⟩
    · exfalso
      omega
    · left
      constructor <;> omega
  · rw [htq] at hsp
    rcases hsp with ⟨h1, h2, h3⟩ | ⟨h1, -⟩
    · right
      left
      refine ⟨by omega, by omega, by omega⟩
    · exfalso
      omega
  · rw [htq] at hsp
    rcases hsp with ⟨h1, -⟩ | ⟨h1, h2, h3⟩
    · exfalso
      omega
    · right
      right
      constructor <;> omega

/-- The free H sites of the twos frame are the H classes `FreeHSite` (the bottom boundary with `t` in the H spectrum). -/
theorem freeH_twos_sub (k : ℕ) {z : Site}
    (hz : z ∈ (frameAt (List.replicate (k + 1) Digit.two)).freeH) :
    FreeHSite (2 * (k : ℤ) + 4) z.1 z.2 := by
  obtain ⟨hn, hden⟩ := twos_child_num_den k
  have hbox := FreeTraceBox.freeH_box _ hz
  have hz' := hz
  simp only [ChildFrame.freeH, Set.mem_setOf_eq] at hz'
  obtain ⟨-, -, hS⟩ := hz'
  rw [hn, hden] at hbox
  simp only [ChildFrame.hSpectrum, ChildFrame.tGrade, hn, hden] at hS
  have ht' : (2 * (k : ℤ) + 3) * z.1 - (2 * (k : ℤ) + 5) * z.2 = (2 * (k : ℤ) + 5 - 2) * z.1 - (2 * (k : ℤ) + 5) * z.2 := by
    ring
  rw [ht'] at hS
  generalize hT : (2 * (k : ℤ) + 5 - 2) * z.1 - (2 * (k : ℤ) + 5) * z.2 = t at hS
  have hsp : (t % 2 = 0 ∧ 2 ≤ t ∧ t ≤ 2 * (2 * (k : ℤ) + 5) - 4) ∨
      (t % 2 = 1 ∧ (2 * (k : ℤ) + 5) - 2 ≤ t ∧ t ≤ 2 * (k : ℤ) + 5) := by
    rcases hS with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl ⟨h1, h2, by omega⟩
    · exact Or.inr ⟨h1, by omega, by omega⟩
  have hres := twosFreeH_arith (2 * (k : ℤ) + 5) z.1 z.2 t (by omega) (by omega) hT.symm
    hbox.1 hbox.2.1 hsp
  unfold FreeHSite
  omega

/-- The free V sites of the twos frame are the V classes `FreeVSite` (the left boundary with `s` in the V spectrum). -/
theorem freeV_twos_sub (k : ℕ) {z : Site}
    (hz : z ∈ (frameAt (List.replicate (k + 1) Digit.two)).freeV) :
    FreeVSite (2 * (k : ℤ) + 4) z.1 z.2 := by
  obtain ⟨hn, hden⟩ := twos_child_num_den k
  have hz' := hz
  simp only [ChildFrame.freeV, Set.mem_setOf_eq] at hz'
  obtain ⟨hC, -, hV⟩ := hz'
  rw [ChildFrame.mem_closedPolygon_iff] at hC
  simp only [ChildFrame.tGrade, ChildFrame.sGrade, Fraction.periodDenominator, hn, hden] at hC
  simp only [ChildFrame.vSpectrum, ChildFrame.sGrade, hn, hden] at hV
  have hC' : (2 - 2 * ((2 * (k : ℤ) + 5) * (2 * (k : ℤ) + 5) - 2) ≤ (2 * (k : ℤ) + 5 - 2) * z.1 - (2 * (k : ℤ) + 5) * z.2 ∧
      (2 * (k : ℤ) + 5 - 2) * z.1 - (2 * (k : ℤ) + 5) * z.2 ≤ 2 * (2 * (k : ℤ) + 5) - 4) ∨
      ((2 * (k : ℤ) + 5) - 2 - 2 * ((2 * (k : ℤ) + 5) * (2 * (k : ℤ) + 5) - 2) ≤
        (2 * (k : ℤ) + 5 - 2) * z.1 - (2 * (k : ℤ) + 5) * z.2 ∧
        (2 * (k : ℤ) + 5 - 2) * z.1 - (2 * (k : ℤ) + 5) * z.2 ≤ 2 * (k : ℤ) + 5) := by
    rcases hC with ⟨-, h1, h2, -, -⟩ | ⟨-, h1, h2, -, -⟩
    · exact Or.inl ⟨by linarith, by linarith⟩
    · exact Or.inr ⟨by linarith, by linarith⟩
  have hV' : 0 ≤ (2 * (2 * (k : ℤ) + 5) - 2) * z.1 + 2 * z.2 ∧
      (2 * (2 * (k : ℤ) + 5) - 2) * z.1 + 2 * z.2 ≤ 2 * (2 * (k : ℤ) + 5) - 4 := by
    rcases hV with ⟨-, h | h⟩
    · exact ⟨by linarith [h.1], by linarith [h.2]⟩
    · exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hres := twosFreeV_arith (2 * (k : ℤ) + 5) z.1 z.2 (by omega) hC' hV'.1 hV'.2
  unfold FreeVSite
  omega

/-- The prescribed H direction of the twos frame at an H class is the free table `freeDisp`. -/
theorem twos_prescribedH_eq (k : ℕ) (η : ℤ) (x y : ℤ) (h : FreeHSite (2 * (k : ℤ) + 4) x y) :
    (frameAt (List.replicate (k + 1) Digit.two)).prescribedH η (x, y) = freeDisp (2 * (k : ℤ) + 4) η x y := by
  obtain ⟨hn, hden⟩ := twos_child_num_den k
  have hL : (frameAt (List.replicate (k + 1) Digit.two)).hLast = (2 * (k : ℤ) + 5, 2 * (k : ℤ) + 2) := by
    unfold ChildFrame.hLast
    rw [hn, hden]
    ext <;> simp
    all_goals (try ring)
  unfold ChildFrame.prescribedH
  rw [hL]
  unfold FLatticePaper.Induction.hFirst
  unfold freeDisp
  rw [if_pos h]
  unfold FreeHSite at h
  split_ifs <;> (try simp_all [EvenSite])
  all_goals (try omega)

/-- The prescribed V direction of the twos frame at a V class is the free table `freeDisp`. -/
theorem twos_prescribedV_eq (k : ℕ) (η : ℤ) (x y : ℤ) (h : FreeVSite (2 * (k : ℤ) + 4) x y) :
    (frameAt (List.replicate (k + 1) Digit.two)).prescribedV η (x, y) = freeDisp (2 * (k : ℤ) + 4) η x y := by
  obtain ⟨hn, hden⟩ := twos_child_num_den k
  have hL : (frameAt (List.replicate (k + 1) Digit.two)).vLast = (-1, 4 * (k : ℤ) + 7) := by
    unfold ChildFrame.vLast
    rw [hn, hden]
    ext <;> simp
    all_goals (try ring)
  have hnH : ¬ FreeHSite (2 * (k : ℤ) + 4) x y := by
    unfold FreeVSite at h
    unfold FreeHSite
    omega
  unfold ChildFrame.prescribedV
  rw [hL]
  unfold FLatticePaper.Induction.vFirst
  unfold freeDisp
  rw [if_neg hnH]
  unfold FreeVSite at h
  split_ifs <;> (try simp_all [EvenSite])
  all_goals (try omega)

/-- **The prescriptions of the twos policy (`PrescribedAt`).** At a free H or V white centre the twos policy `TwosSel` of sign `η`
keeps exactly the prescribed input. The selected input is the free table at the centre itself (`u = c`), and uniqueness of the
selected input at a white (`twos_white_quota`) gives the converse. -/
theorem twos_prescribedAt (k : ℕ) (η : ℤ)
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees
      (standardField (List.replicate (k + 1) Digit.two)) 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4))
      (standardField (List.replicate (k + 1) Digit.two)) 0 (stairEvenConstantV (2 * (k : ℤ) + 4))) :
    PrescribedAt (frameAt (List.replicate (k + 1) Digit.two)) (standardField (List.replicate (k + 1) Digit.two)) η
      (TwosSel (2 * (k : ℤ) + 4) η (standardField (List.replicate (k + 1) Digit.two))) := by
  refine ⟨fun c hcH hw j => ?_, fun c hcV hw j => ?_⟩
  · obtain ⟨x, y⟩ := c
    have hH : FreeHSite (2 * (k : ℤ) + 4) x y := freeH_twos_sub k hcH
    rw [twos_prescribedH_eq k η x y hH]
    have hwit : TwosSel (2 * (k : ℤ) + 4) η (standardField (List.replicate (k + 1) Digit.two)) (x, y)
        ((x, y) + freeDisp (2 * (k : ℤ) + 4) η x y) := by
      refine Or.inr ⟨hw, Or.inl ⟨(x, y), ⟨0, 0, by simp⟩, Or.inl hH, rfl⟩⟩
    constructor
    · intro hj
      exact (twos_white_quota k hagree hperiod η (x, y) hw).2 j _ hj hwit
    · intro hj
      rw [hj]
      exact hwit
  · obtain ⟨x, y⟩ := c
    have hV : FreeVSite (2 * (k : ℤ) + 4) x y := freeV_twos_sub k hcV
    rw [twos_prescribedV_eq k η x y hV]
    have hwit : TwosSel (2 * (k : ℤ) + 4) η (standardField (List.replicate (k + 1) Digit.two)) (x, y)
        ((x, y) + freeDisp (2 * (k : ℤ) + 4) η x y) := by
      refine Or.inr ⟨hw, Or.inl ⟨(x, y), ⟨0, 0, by simp⟩, Or.inr hV, rfl⟩⟩
    constructor
    · intro hj
      exact (twos_white_quota k hagree hperiod η (x, y) hw).2 j _ hj hwit
    · intro hj
      rw [hj]
      exact hwit

end FLatticePaper.TwosEPolicy
