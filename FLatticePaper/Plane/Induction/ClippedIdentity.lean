import FLatticePaper.Plane.Induction.ClippedArith
import FLatticePaper.Plane.Induction.ParentStrip
import FLatticePaper.Plane.Induction.NativeShift
import FLatticePaper.Plane.Induction.SheetOffsets
import FLatticePaper.Plane.Induction.SheetPieces

/-! Task 72 / Q31 step 2: the clipped identity `D_−(z) = −min(g, 2)`, with `g = Fp(z + ε U_q) − Fp(z)`, `Fp = FqW word`.

`D_−(z) = F(z) − F(z − σ)` (`slip F (−1) z`) with `σ = ε U_p`. The shift gives `F(z + X)` (`X = U_p` in phase 0, `X = U_q` in
phase 1). `z + X` lies in the closed polygon (`NativeShift`), so `F(z + X) = min(sheetA, sheetC)` there. The two offers reduce to
`Fp(z + ε U_q)` and `h0(z) + 2`, using the parent strip (`ParentStrip`) and the harmonic translation (`ClippedCore`). The child
strip gives `F(z) = h0(z)`. -/

namespace FLatticePaper.ClippedIdentity

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1MSheet

/-- `T_q − d_q − n_q` is even, so `2 · ((T_q − d_q − n_q)/2) = T_q − d_q − n_q`. -/
theorem even_half (a b : ℤ) :
    2 * ((a ^ 2 + 2 * a * b - b ^ 2 - a - b) / 2) = a ^ 2 + 2 * a * b - b ^ 2 - a - b := by
  obtain ⟨r, hr⟩ := Int.even_mul_succ_self (a - 1)
  obtain ⟨s', hs⟩ := Int.even_mul_succ_self b
  have hE : a ^ 2 + 2 * a * b - b ^ 2 - a - b = 2 * (r - s' + a * b) := by
    linear_combination hr - hs
  rw [hE, Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)]

/-- `min(a, F + 2) − F = min(a − F, 2)`. -/
theorem min_shift (a F : ℤ) : F - min a (F + 2) = -min (a - F) 2 := by
  omega

/-- **Phase 0 (ε = −1).** -/
theorem phase0 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word)) {z : Site}
    (hε : (frameAt word).eps = -1)
    (hmem : z + (2 * (frameAt word).parents.odd.den, 2 * (frameAt word).parents.odd.num) ∈
      (frameAt word).closedPolygon)
    (hF0 : standardField word z = harmonicGrid z) (hS1 : FqW word z = harmonicGrid z)
    (hS2 : FqW word (z - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
          (frameAt word).parents.even.num + (frameAt word).parents.even.den)) =
        harmonicGrid (z - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
          (frameAt word).parents.even.num + (frameAt word).parents.even.den))) :
    standardField word z - standardField word (z - (frameAt word).shortShift) =
      -min (FqW word (z + ((frameAt word).eps * (frameAt word).parents.even.den,
          (frameAt word).eps * (frameAt word).parents.even.num)) - FqW word z) 2 := by
  rw [ClippedCore.sigma_shift_neg (frameAt word) (F := standardField word) z hε, standardField_eq_sheetMin_of_strong h hSE hmem, hF0]
  unfold ChildFrame.sheetMin
  rw [SheetOffsets.sheetA_neg h hSE hε z, SheetOffsets.sheetC_neg h hSE hε z, SheetOffsets.even_kernel, SheetOffsets.even_transverse]
  rw [hε, hS1, hS2]
  have hc0 : (frameAt word).sheetConstant =
      ((frameAt word).parents.even.den ^ 2 + 2 * (frameAt word).parents.even.den * (frameAt word).parents.even.num
        - (frameAt word).parents.even.num ^ 2 - (frameAt word).parents.even.den - (frameAt word).parents.even.num) / 2 := by
    unfold ChildFrame.sheetConstant Fraction.periodDenominator
    rw [SheetOffsets.phaseW_neg hε]
    ring
  rw [hc0]
  have hev := even_half (frameAt word).parents.even.den (frameAt word).parents.even.num
  have hT := ClippedCore.harmonic_translate_Vq (frameAt word).parents.even.num (frameAt word).parents.even.den z
    (-((((frameAt word).parents.even.den ^ 2 + 2 * (frameAt word).parents.even.den * (frameAt word).parents.even.num
        - (frameAt word).parents.even.num ^ 2 - (frameAt word).parents.even.den - (frameAt word).parents.even.num) / 2)))
    (by linarith)
  have hA : z + ((-1 : ℤ) * (frameAt word).parents.even.den, (-1 : ℤ) * (frameAt word).parents.even.num) =
      z - ((frameAt word).parents.even.den, (frameAt word).parents.even.num) := by
    ext <;> simp <;> ring
  rw [hA]
  simp only [ChildFrame.siblingSlope]
  generalize hs0 : ((frameAt word).parents.even.den ^ 2 + 2 * (frameAt word).parents.even.den * (frameAt word).parents.even.num
        - (frameAt word).parents.even.num ^ 2 - (frameAt word).parents.even.den - (frameAt word).parents.even.num) / 2 = s0 at hT ⊢
  have key : harmonicGrid (z - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
          (frameAt word).parents.even.num + (frameAt word).parents.even.den)) +
        ((frameAt word).parents.even.num * z.1 - (frameAt word).parents.even.den * z.2 + 2) + s0 =
      harmonicGrid z + 2 := by
    have e : z - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
          (frameAt word).parents.even.num + (frameAt word).parents.even.den) =
        (z.1 - ((frameAt word).parents.even.num - (frameAt word).parents.even.den),
          z.2 - ((frameAt word).parents.even.num + (frameAt word).parents.even.den)) := rfl
    rw [e]
    linarith [hT]
  rw [key]
  exact min_shift _ _

/-- **Phase 1 (ε = 1).** -/
theorem phase1 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hpk : (frameAt word).Packet (standardField word)) {z : Site}
    (hε : (frameAt word).eps = 1)
    (hmem : z + ((frameAt word).parents.even.den, (frameAt word).parents.even.num) ∈
      (frameAt word).closedPolygon)
    (hF0 : standardField word z = harmonicGrid z) (hS1 : FqW word z = harmonicGrid z)
    (hS2 : FqW word (z - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
          (frameAt word).parents.even.num + (frameAt word).parents.even.den)) =
        harmonicGrid (z - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
          (frameAt word).parents.even.num + (frameAt word).parents.even.den))) :
    standardField word z - standardField word (z - (frameAt word).shortShift) =
      -min (FqW word (z + ((frameAt word).eps * (frameAt word).parents.even.den,
          (frameAt word).eps * (frameAt word).parents.even.num)) - FqW word z) 2 := by
  rw [ClippedCore.sigma_shift_pos (frameAt word) hpk z hε, standardField_eq_sheetMin_of_strong h hSE hmem, hF0]
  unfold ChildFrame.sheetMin
  rw [← SheetOffsets.even_kernel, SheetOffsets.sheetA_pos hε, SheetOffsets.sheetC_pos hε z,
    SheetOffsets.even_transverse, hS1, hS2, hε]
  have hc1 : (frameAt word).sheetConstant =
      ((frameAt word).parents.even.den ^ 2 + 2 * (frameAt word).parents.even.den * (frameAt word).parents.even.num
        - (frameAt word).parents.even.num ^ 2 - (frameAt word).parents.even.den - (frameAt word).parents.even.num) / 2 + 2 := by
    unfold ChildFrame.sheetConstant Fraction.periodDenominator
    rw [SheetOffsets.phaseW_pos hε]
    ring
  rw [hc1]
  have hev := even_half (frameAt word).parents.even.den (frameAt word).parents.even.num
  have hT := ClippedCore.harmonic_translate_Vq (frameAt word).parents.even.num (frameAt word).parents.even.den z
    (-((((frameAt word).parents.even.den ^ 2 + 2 * (frameAt word).parents.even.den * (frameAt word).parents.even.num
        - (frameAt word).parents.even.num ^ 2 - (frameAt word).parents.even.den - (frameAt word).parents.even.num) / 2)))
    (by linarith)
  simp only [ChildFrame.siblingSlope, one_mul, SheetOffsets.even_kernel]
  generalize hs0 : ((frameAt word).parents.even.den ^ 2 + 2 * (frameAt word).parents.even.den * (frameAt word).parents.even.num
        - (frameAt word).parents.even.num ^ 2 - (frameAt word).parents.even.den - (frameAt word).parents.even.num) / 2 = s0 at hT ⊢
  have key : harmonicGrid (z - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
          (frameAt word).parents.even.num + (frameAt word).parents.even.den)) +
        ((frameAt word).parents.even.num * z.1 - (frameAt word).parents.even.den * z.2) + (s0 + 2) =
      harmonicGrid z + 2 := by
    have e : z - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
          (frameAt word).parents.even.num + (frameAt word).parents.even.den) =
        (z.1 - ((frameAt word).parents.even.num - (frameAt word).parents.even.den),
          z.2 - ((frameAt word).parents.even.num + (frameAt word).parents.even.den)) := rfl
    rw [e]
    linarith [hT]
  rw [key]
  exact min_shift _ _

/-- **The clipped identity (Q31 step 2):** `D_−(z) = F(z) − F(z − σ) = −min(g, 2)` with `g = Fp(z + ε U_q) − Fp(z)`, for a native
V point `z ∈ freeV` in the window `2 − c ≤ s ≤ L − 2` (and `0 ≤ s ≤ 2n` when `z` is even). -/
theorem clipped_identity {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hpk : (frameAt word).Packet (standardField word)) {z : Site}
    (hz : z ∈ (frameAt word).freeV)
    (hwin0 : 2 - ((frameAt word).child.den - (frameAt word).child.num) ≤ (frameAt word).sGrade z)
    (hwin1 : (frameAt word).sGrade z ≤ (frameAt word).child.den + (frameAt word).child.num - 2)
    (hj0 : 0 ≤ z.2)
    (hjL : z.2 ≤ (frameAt word).child.den + (frameAt word).child.num - 2)
    (hEv : EvenSite z → 0 ≤ (frameAt word).sGrade z ∧ (frameAt word).sGrade z ≤ 2 * (frameAt word).child.num) :
    standardField word z - standardField word (z - (frameAt word).shortShift) =
      -min (FqW word (z + ((frameAt word).eps * (frameAt word).parents.even.den,
          (frameAt word).eps * (frameAt word).parents.even.num)) - FqW word z) 2 := by
  have hstrip : FqW word z = harmonicGrid z ∧
      FqW word (z - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
          (frameAt word).parents.even.num + (frameAt word).parents.even.den)) =
        harmonicGrid (z - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
          (frameAt word).parents.even.num + (frameAt word).parents.even.den)) := by
    by_cases he : EvenSite z
    · obtain ⟨a, b⟩ := hEv he
      exact ParentStrip.even_strip h hSE z he hj0 hjL a b
    · exact ParentStrip.odd_strip h hSE z he hj0 hjL hwin0 hwin1
  have hF0 : standardField word z = harmonicGrid z :=
    ClippedArith.child_strip (frameAt word) hpk z (by omega) (by omega)
  have hsum := ClippedArith.sGrade_sum (frameAt word)
  have hUpar := ClippedArith.sGrade_Upar_ge (frameAt word)
  have hUq := ClippedArith.sGrade_Uq_ge (frameAt word)
  rcases (frameAt word).eps_unit with hε | hε
  · -- phase 1: X = U_q
    have hXt : (frameAt word).tGrade ((frameAt word).parents.even.den, (frameAt word).parents.even.num) = 2 := by
      rw [ClippedArith.tGrade_Uq, hε]
      norm_num
    have hXev : EvenSite ((frameAt word).parents.even.den, (frameAt word).parents.even.num) := by
      unfold EvenSite
      have := (frameAt word).valid.even_parity
      unfold Fraction.Even at this
      simpa [add_comm] using this
    have hXs1 : (frameAt word).sGrade ((frameAt word).parents.even.den, (frameAt word).parents.even.num) ≤
        (frameAt word).child.periodDenominator - ((frameAt word).child.den - (frameAt word).child.num) + 2 := by
      linarith
    have hmem := NativeShift.shift_mem_closedPolygon (frameAt word) hz hwin0 hwin1 hXt hXev hUq hXs1
    exact phase1 h hSE hpk hε hmem hF0 hstrip.1 hstrip.2
  · -- phase 0: X = U_p
    have hXt : (frameAt word).tGrade (2 * (frameAt word).parents.odd.den, 2 * (frameAt word).parents.odd.num) = 2 := by
      rw [ClippedArith.tGrade_Upar, hε]
      norm_num
    have hXev : EvenSite (2 * (frameAt word).parents.odd.den, 2 * (frameAt word).parents.odd.num) := by
      unfold EvenSite
      simp only
      omega
    have hXs1 : (frameAt word).sGrade (2 * (frameAt word).parents.odd.den, 2 * (frameAt word).parents.odd.num) ≤
        (frameAt word).child.periodDenominator - ((frameAt word).child.den - (frameAt word).child.num) + 2 := by
      linarith
    have hmem := NativeShift.shift_mem_closedPolygon (frameAt word) hz hwin0 hwin1 hXt hXev hUpar hXs1
    exact phase0 h hSE hε hmem hF0 hstrip.1 hstrip.2

end FLatticePaper.ClippedIdentity
