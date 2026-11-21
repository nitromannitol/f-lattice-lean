import FLatticePaper.Plane.Induction.Sheets
import FLatticePaper.Plane.Induction.Bands
import FLatticePaper.Plane.Induction.OddStep
import FLatticePaper.Plane.Induction.Reflection

namespace FLatticePaper.Induction
open Farey

/-- The affine law of `h₀` under the reflection `y ↦ c − y`, for a centre `c` with even coordinate sum. -/
theorem harmonicGrid_reflect (c1 c2 s r y1 y2 : ℤ) (hs : c1 + c2 = 2 * s) (hr : c1 - c2 = 2 * r) :
    harmonicGrid (c1 - y1, c2 - y2) =
      harmonicGrid (y1, y2) + harmonicGrid (c1, c2) - s * y1 + (1 - r) * y2 := by
  have e1 := harmonicGrid_exact (c1 - y1, c2 - y2)
  have e2 := harmonicGrid_exact (y1, y2)
  have e3 := harmonicGrid_exact (c1, c2)
  dsimp only at e1 e2 e3
  have hp : (c1 - y1 + (c2 - y2)) % 2 = (y1 + y2) % 2 := by omega
  have hpc : (c1 + c2) % 2 = 0 := by omega
  have key : 4 * harmonicGrid (c1 - y1, c2 - y2) =
      4 * (harmonicGrid (y1, y2) + harmonicGrid (c1, c2) - s * y1 + (1 - r) * y2) := by
    linear_combination e1 - e2 - e3 - 2 * y1 * hs - 2 * y2 * hr - hp + hpc
  exact mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) key

/-- The harmonic quarter-turn of `G` reflects in the centre `c = (2N+1, 4N+2D−1)`, once `G` has the
reflection `G(R'' − w) = G w − t'(w) + κ'` with `R'' = (−4N−2D+1, 2N−1)`. -/
theorem quarterTurnField_reflect (N D : ℤ) {G : Field}
    (hG : ∀ w : Site, G ((-4 * N - 2 * D + 1, 2 * N - 1) - w) =
      G w - ((D - N) * w.1 - (D + N) * w.2) + (D - (D ^ 2 + 2 * D * N - N ^ 2)))
    (y : Site) :
    quarterTurnField G ((2 * N + 1, 4 * N + 2 * D - 1) - y) =
      quarterTurnField G y - ((D - N) * (-y.2) - (D + N) * (y.1 - 1)) +
        (D - (D ^ 2 + 2 * D * N - N ^ 2)) + harmonicGrid (2 * N + 1, 4 * N + 2 * D - 1) -
        (3 * N + D) * y.1 + (N + D) * y.2 := by
  have hsite : (2 * N + 1, 4 * N + 2 * D - 1) - y = (2 * N + 1 - y.1, 4 * N + 2 * D - 1 - y.2) := rfl
  have hZ : (-(4 * N + 2 * D - 1 - y.2), 2 * N + 1 - y.1 - 1) =
      (-4 * N - 2 * D + 1, 2 * N - 1) - (-y.2, y.1 - 1) :=
    Prod.ext (by simp only [Prod.fst_sub]; ring) (by simp only [Prod.snd_sub]; ring)
  have hh := harmonicGrid_reflect (2 * N + 1) (4 * N + 2 * D - 1) (3 * N + D) (-N - D + 1) y.1 y.2
    (by ring) (by ring)
  have hB := hG (-y.2, y.1 - 1)
  simp only [quarterTurnField_eq]
  rw [hsite]
  dsimp only
  rw [hZ, hB]
  linear_combination hh

/-- The reflection of the conjugate standard transfers to the centre `R'' = (−4N−2D+1, 2N−1)`, using the
kernel period `U' = (D+N, D−N)` of the conjugate and the three-fold shift `3U'`. -/
theorem pairing_of_reflection (frame conj : ChildFrame) (hconj : conj.child = frame.parents.odd.rotate)
    {G : Field}
    (hrefl : ∀ y, G (conj.centre - y) = G y - conj.tGrade y + conj.symmetryConstant)
    (hper : HasGeneratorPeriods conj.child G conj.coherentConstantU conj.coherentConstantV)
    (N D : ℤ) (hN : frame.parents.odd.num = N) (hD : frame.parents.odd.den = D) :
    ∀ w : Site, G ((-4 * N - 2 * D + 1, 2 * N - 1) - w) =
      G w - ((D - N) * w.1 - (D + N) * w.2) + (D - (D ^ 2 + 2 * D * N - N ^ 2)) := by
  have hodd : frame.parents.odd.Odd := frame.valid.odd_parity
  have hcnum : conj.child.num = D - N := by
    rw [hconj, Fraction.rotate_of_odd hodd, hN, hD]
  have hcden : conj.child.den = D + N := by
    rw [hconj, Fraction.rotate_of_odd hodd, hN, hD]
  unfold HasGeneratorPeriods at hper
  have hK : ∀ w : Site, G (w + (D + N, D - N)) = G w := by
    intro w
    have hk := hper.1 w
    rw [conj.child_modifiedDeck_kernel, hcden, hcnum, conj.coherentConstantU_eq_zero, add_zero] at hk
    exact hk
  have hcen : conj.centre = (D - N + 1, 3 * D - N - 1) := by
    unfold ChildFrame.centre
    rw [conj.child_modifiedDeck_kernel, conj.child_modifiedDeck_transverse, hcnum, hcden]
    exact Prod.ext (by simp only [Prod.fst_add]; ring)
      (by simp only [Prod.snd_add]; ring)
  have hκ : conj.symmetryConstant = D - (D ^ 2 + 2 * D * N - N ^ 2) := by
    unfold ChildFrame.symmetryConstant Fraction.periodDenominator
    rw [hcnum, hcden]
    have e : D + N + (D - N) - ((D + N) ^ 2 + 2 * (D + N) * (D - N) - (D - N) ^ 2) =
        2 * (D - (D ^ 2 + 2 * D * N - N ^ 2)) := by ring
    rw [e, Int.mul_ediv_cancel_left _ two_ne_zero]
  intro w
  have h3 : G (w + (D + N, D - N) + (D + N, D - N) + (D + N, D - N)) = G w := by
    rw [hK, hK, hK]
  have ht : conj.tGrade (w + (D + N, D - N) + (D + N, D - N) + (D + N, D - N)) =
      (D - N) * w.1 - (D + N) * w.2 := by
    unfold ChildFrame.tGrade
    rw [hcnum, hcden]
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  have hr := hrefl (w + (D + N, D - N) + (D + N, D - N) + (D + N, D - N))
  rw [hcen] at hr
  have eq1 : (D - N + 1, 3 * D - N - 1) - (w + (D + N, D - N) + (D + N, D - N) + (D + N, D - N)) =
      (-4 * N - 2 * D + 1, 2 * N - 1) - w :=
    Prod.ext (by simp only [Prod.fst_sub, Prod.fst_add]; ring)
      (by simp only [Prod.snd_sub, Prod.snd_add]; ring)
  rw [eq1, h3, ht, hκ] at hr
  exact hr

/-! ### The sheet data of a frame, in the parent coordinates -/

theorem harmonicGrid_centre_value (N D : ℤ) :
    harmonicGrid (2 * N + 1, 4 * N + 2 * D - 1) = N ^ 2 + 2 * N - 2 * N * D + D - D ^ 2 := by
  have e := harmonicGrid_exact (2 * N + 1, 4 * N + 2 * D - 1)
  dsimp only at e
  have hP : (2 * N + 1 + (4 * N + 2 * D - 1)) % 2 = 0 := by omega
  rw [hP] at e
  have h4 : 4 * harmonicGrid (2 * N + 1, 4 * N + 2 * D - 1) =
      4 * (N ^ 2 + 2 * N - 2 * N * D + D - D ^ 2) := by
    rw [e]
    ring
  exact mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) h4

theorem sheet_facts_alg (N D nq dq k : ℤ) (hk : nq + dq = 2 * k) :
    2 * D + dq + (2 * N + nq) - ((2 * D + dq) ^ 2 + 2 * (2 * D + dq) * (2 * N + nq) - (2 * N + nq) ^ 2) =
      2 * ((D + N + k) - 2 * (D + N + k) ^ 2 + (2 * N + nq) ^ 2) := by
  linear_combination (1 - 4 * (D + N + k) - (nq + dq - 2 * k)) * hk

/-- The constants of a frame in the parent coordinates: `k` with `n_q + d_q = 2k`, the parity constraint
`ε = N d_q − n_q D = 2W − 1`, the sheet constant, the reflection constant, the centre and the two sheet shifts. -/
theorem ChildFrame.sheet_facts (frame : ChildFrame) : ∃ k : ℤ,
    frame.parents.even.num + frame.parents.even.den = 2 * k ∧
    frame.eps = frame.parents.odd.num * frame.parents.even.den - frame.parents.even.num * frame.parents.odd.den ∧
    frame.eps = 2 * frame.phaseW - 1 ∧
    frame.phaseW * frame.phaseW = frame.phaseW ∧
    frame.sheetConstant = 2 * frame.phaseW + (2 * k ^ 2 - frame.parents.even.num ^ 2 - k) ∧
    frame.symmetryConstant = (frame.parents.odd.den + frame.parents.odd.num + k) -
      2 * (frame.parents.odd.den + frame.parents.odd.num + k) ^ 2 +
      (2 * frame.parents.odd.num + frame.parents.even.num) ^ 2 ∧
    frame.centre = (2 * frame.parents.odd.num + frame.parents.even.num + 1,
      4 * frame.parents.odd.num + 2 * frame.parents.even.num + 2 * frame.parents.odd.den +
        frame.parents.even.den - 1) ∧
    frame.sheetShift = ((1 - frame.phaseW) * frame.parents.even.den,
      (1 - frame.phaseW) * frame.parents.even.num) ∧
    frame.sheetOffset = (frame.parents.even.num - frame.parents.even.den +
        (2 * frame.phaseW - 1) * frame.parents.even.den,
      frame.parents.even.num + frame.parents.even.den + (2 * frame.phaseW - 1) * frame.parents.even.num) := by
  have hpar : (frame.parents.even.num + frame.parents.even.den) % 2 = 0 := frame.valid.even_parity
  obtain ⟨k, hk⟩ : ∃ k : ℤ, frame.parents.even.num + frame.parents.even.den = 2 * k :=
    ⟨(frame.parents.even.num + frame.parents.even.den) / 2, by omega⟩
  have hcn : frame.child.num = 2 * frame.parents.odd.num + frame.parents.even.num := by
    simp only [ChildFrame.child, Parents.current, Parents.combine]
    ring
  have hcd : frame.child.den = 2 * frame.parents.odd.den + frame.parents.even.den := by
    simp only [ChildFrame.child, Parents.current, Parents.combine]
    ring
  have heps : frame.eps = frame.parents.odd.num * frame.parents.even.den -
      frame.parents.even.num * frame.parents.odd.den := rfl
  have hW : frame.eps = 2 * frame.phaseW - 1 ∧ frame.phaseW * frame.phaseW = frame.phaseW := by
    rcases frame.phaseW_cases with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by rw [h1, h2]; norm_num, by rw [h2]; norm_num⟩
    · exact ⟨by rw [h1, h2]; norm_num, by rw [h2]; norm_num⟩
  have hsc : frame.sheetConstant = 2 * frame.phaseW + (2 * k ^ 2 - frame.parents.even.num ^ 2 - k) := by
    have h := frame.sheetConstant_exact
    unfold Fraction.periodDenominator at h
    have h2 : 2 * (frame.sheetConstant - (2 * frame.phaseW + (2 * k ^ 2 - frame.parents.even.num ^ 2 - k))) =
        0 := by
      linear_combination h + (frame.parents.even.num + frame.parents.even.den + 2 * k - 1) * hk
    have h3 := (mul_eq_zero.mp h2).resolve_left two_ne_zero
    linarith
  have hκ : frame.symmetryConstant = (frame.parents.odd.den + frame.parents.odd.num + k) -
      2 * (frame.parents.odd.den + frame.parents.odd.num + k) ^ 2 +
      (2 * frame.parents.odd.num + frame.parents.even.num) ^ 2 := by
    unfold ChildFrame.symmetryConstant Fraction.periodDenominator
    rw [hcn, hcd, sheet_facts_alg _ _ _ _ _ hk, Int.mul_ediv_cancel_left _ two_ne_zero]
  refine ⟨k, hk, heps, hW.1, hW.2, hsc, hκ, ?_, ?_, ?_⟩
  · rw [frame.centre_eq, hcn, hcd]
    congr 1
    ring
  · unfold ChildFrame.sheetShift
    rfl
  · unfold ChildFrame.sheetOffset
    rw [hW.1]
    rfl

/-- The first sheet at the reflected site is the second sheet at the site, shifted by the tGrade reflection. -/
theorem ChildFrame.sheet_swap_one (frame conj : ChildFrame) (hconj : conj.child = frame.parents.odd.rotate)
    {G : Field} (hrefl : ∀ y, G (conj.centre - y) = G y - conj.tGrade y + conj.symmetryConstant)
    (hper : HasGeneratorPeriods conj.child G conj.coherentConstantU conj.coherentConstantV) (z : Site) :
    frame.sheetA (quarterTurnField G) (frame.centre - z) =
      frame.sheetC (quarterTurnField G) z - frame.tGrade z + frame.symmetryConstant := by
  obtain ⟨k, hk, hεN, hεW, hWW, hsc, hκ, hR, hsh, hof⟩ := frame.sheet_facts
  have hcn : frame.child.num = 2 * frame.parents.odd.num + frame.parents.even.num := by
    simp only [ChildFrame.child, Parents.current, Parents.combine]
    ring
  have hcd : frame.child.den = 2 * frame.parents.odd.den + frame.parents.even.den := by
    simp only [ChildFrame.child, Parents.current, Parents.combine]
    ring
  have he := hεN.symm.trans hεW
  have hG := pairing_of_reflection frame conj hconj hrefl hper frame.parents.odd.num frame.parents.odd.den rfl rfl
  have hcore := quarterTurnField_reflect frame.parents.odd.num frame.parents.odd.den hG
    (z - frame.sheetShift - frame.sheetOffset)
  have hcy : frame.centre - z - frame.sheetShift =
      (2 * frame.parents.odd.num + 1, 4 * frame.parents.odd.num + 2 * frame.parents.odd.den - 1) -
        (z - frame.sheetShift - frame.sheetOffset) := by
    rw [hR, hsh, hof]
    exact Prod.ext (by simp only [Prod.fst_sub]; ring)
      (by simp only [Prod.snd_sub]; ring)
  set N := frame.parents.odd.num with hN
  set D := frame.parents.odd.den with hD
  set nq := frame.parents.even.num with hnq
  set dq := frame.parents.even.den with hdq
  set W := frame.phaseW with hWdef
  unfold ChildFrame.sheetA ChildFrame.sheetC
  rw [hcy, hcore]
  unfold ChildFrame.siblingSlope ChildFrame.tGrade
  rw [hκ, hsc, harmonicGrid_centre_value, hcn, hcd, hsh, hof]
  simp only [Prod.fst_sub, Prod.snd_sub]
  linear_combination (-2 * D - 2 * N) * hk + 2 * W * he + 4 * hWW

/-- The second sheet at the reflected site is the first sheet at the site. -/
theorem ChildFrame.sheet_swap_two (frame conj : ChildFrame) (hconj : conj.child = frame.parents.odd.rotate)
    {G : Field} (hrefl : ∀ y, G (conj.centre - y) = G y - conj.tGrade y + conj.symmetryConstant)
    (hper : HasGeneratorPeriods conj.child G conj.coherentConstantU conj.coherentConstantV) (z : Site) :
    frame.sheetC (quarterTurnField G) (frame.centre - z) =
      frame.sheetA (quarterTurnField G) z - frame.tGrade z + frame.symmetryConstant := by
  obtain ⟨k, hk, hεN, hεW, hWW, hsc, hκ, hR, hsh, hof⟩ := frame.sheet_facts
  have hcn : frame.child.num = 2 * frame.parents.odd.num + frame.parents.even.num := by
    simp only [ChildFrame.child, Parents.current, Parents.combine]
    ring
  have hcd : frame.child.den = 2 * frame.parents.odd.den + frame.parents.even.den := by
    simp only [ChildFrame.child, Parents.current, Parents.combine]
    ring
  have he := hεN.symm.trans hεW
  have hG := pairing_of_reflection frame conj hconj hrefl hper frame.parents.odd.num frame.parents.odd.den rfl rfl
  have hcore := quarterTurnField_reflect frame.parents.odd.num frame.parents.odd.den hG (z - frame.sheetShift)
  have hcy : frame.centre - z - frame.sheetShift - frame.sheetOffset =
      (2 * frame.parents.odd.num + 1, 4 * frame.parents.odd.num + 2 * frame.parents.odd.den - 1) -
        (z - frame.sheetShift) := by
    rw [hR, hsh, hof]
    exact Prod.ext (by simp only [Prod.fst_sub]; ring)
      (by simp only [Prod.snd_sub]; ring)
  set N := frame.parents.odd.num with hN
  set D := frame.parents.odd.den with hD
  set nq := frame.parents.even.num with hnq
  set dq := frame.parents.even.den with hdq
  set W := frame.phaseW with hWdef
  unfold ChildFrame.sheetA ChildFrame.sheetC
  rw [hcy, hcore]
  unfold ChildFrame.siblingSlope ChildFrame.tGrade
  rw [hκ, hsc, harmonicGrid_centre_value, hcn, hcd, hR, hsh]
  simp only [Prod.fst_sub, Prod.snd_sub]
  linear_combination (-2 * D - 2 * N - dq - 2 * k - nq + 1) * hk - 2 * W * he - 4 * hWW

/-- The sheet swap: the two sheets of the odd parent's quarter-turn are exchanged by the reflection of `E`. -/
theorem ChildFrame.sheet_swap (frame conj : ChildFrame) (hconj : conj.child = frame.parents.odd.rotate)
    {G : Field} (hrefl : ∀ y, G (conj.centre - y) = G y - conj.tGrade y + conj.symmetryConstant)
    (hper : HasGeneratorPeriods conj.child G conj.coherentConstantU conj.coherentConstantV) (z : Site) :
    frame.sheetA (quarterTurnField G) (frame.centre - z) =
        frame.sheetC (quarterTurnField G) z - frame.tGrade z + frame.symmetryConstant ∧
      frame.sheetC (quarterTurnField G) (frame.centre - z) =
        frame.sheetA (quarterTurnField G) z - frame.tGrade z + frame.symmetryConstant :=
  ⟨frame.sheet_swap_one conj hconj hrefl hper z, frame.sheet_swap_two conj hconj hrefl hper z⟩

/-- The sheet minimum has the central reflection, since the swap exchanges the two sheets. -/
theorem ChildFrame.sheetMin_reflection (frame conj : ChildFrame) (hconj : conj.child = frame.parents.odd.rotate)
    {G : Field} (hrefl : ∀ y, G (conj.centre - y) = G y - conj.tGrade y + conj.symmetryConstant)
    (hper : HasGeneratorPeriods conj.child G conj.coherentConstantU conj.coherentConstantV) (z : Site) :
    frame.sheetMin (quarterTurnField G) (frame.centre - z) =
      frame.sheetMin (quarterTurnField G) z - frame.tGrade z + frame.symmetryConstant := by
  rw [ChildFrame.sheetMin, (frame.sheet_swap conj hconj hrefl hper z).1,
    (frame.sheet_swap conj hconj hrefl hper z).2]
  unfold ChildFrame.sheetMin
  set A := frame.sheetA (quarterTurnField G) z
  set C := frame.sheetC (quarterTurnField G) z
  set t := frame.tGrade z
  set κ := frame.symmetryConstant
  have e1 : C - t + κ = (C + κ) - t := by ring
  have e2 : A - t + κ = (A + κ) - t := by ring
  rw [e1, e2, min_sub_sub_right, min_add_add_right, min_comm C A]
  ring

end FLatticePaper.Induction
