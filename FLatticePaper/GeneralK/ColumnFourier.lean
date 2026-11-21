import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace FLatticePaper.GeneralK

open scoped BigOperators

private theorem cos_gap_of_cyclic_mode {length index : ℕ} (hi : 0 < index) (hupper : index < length) :
    8 / (length : ℝ) ^ 2 ≤ 1 - Real.cos (2 * Real.pi * (index : ℝ) / (length : ℝ)) := by
  have hlen : (0 : ℝ) < (length : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hupper
  have hj : (1 : ℝ) ≤ (index : ℝ) := by exact_mod_cast hi
  have hj' : (index : ℝ) + 1 ≤ (length : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hupper
  let θ : ℝ := Real.pi * (index : ℝ) / (length : ℝ)
  let φ : ℝ := min θ (Real.pi - θ)
  have hθ₁ : Real.pi / (length : ℝ) ≤ θ := by
    apply div_le_div_of_nonneg_right _ hlen.le
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hj Real.pi_pos.le
  have hθ₂ : Real.pi / (length : ℝ) ≤ Real.pi - θ := by
    unfold θ
    have h := mul_le_mul_of_nonneg_left hj' Real.pi_pos.le
    apply (mul_le_mul_iff_left₀ hlen).mp
    rw [div_mul_cancel₀ _ hlen.ne', sub_mul, div_mul_cancel₀ _ hlen.ne']
    linarith only [h]
  have hφ : Real.pi / (length : ℝ) ≤ φ := le_min hθ₁ hθ₂
  have hφ₀ : 0 ≤ φ := (by positivity : 0 ≤ Real.pi / (length : ℝ)).trans hφ
  have hφ₁ : φ ≤ Real.pi / 2 := by
    unfold φ
    by_cases h : θ ≤ Real.pi - θ
    · rw [min_eq_left h]
      linarith only [h]
    · have h' := le_of_not_ge h
      rw [min_eq_right h']
      linarith only [h']
  have hsin : Real.sin φ = Real.sin θ := by
    unfold φ
    by_cases h : θ ≤ Real.pi - θ
    · rw [min_eq_left h]
    · rw [min_eq_right (le_of_not_ge h), Real.sin_pi_sub]
  have hs := (mul_le_mul_of_nonneg_left hφ (show 0 ≤ 2 / Real.pi by positivity)).trans (Real.mul_le_sin hφ₀ hφ₁)
  rw [hsin, show 2 / Real.pi * (Real.pi / (length : ℝ)) = 2 / (length : ℝ) by
    field_simp [Real.pi_ne_zero]] at hs
  have hsq := pow_le_pow_left₀ (show 0 ≤ 2 / (length : ℝ) by positivity) hs 2
  rw [show 2 * Real.pi * (index : ℝ) / (length : ℝ) = 2 * θ by unfold θ; ring,
    Real.cos_two_mul_eq_one_sub]
  have heq : 8 / (length : ℝ) ^ 2 = 2 * (2 / (length : ℝ)) ^ 2 := by field_simp; ring
  linarith only [hsq, heq]

private theorem norm_stdAddChar {length : ℕ} [NeZero length] (mode : ZMod length) :
    ‖ZMod.stdAddChar mode‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

private theorem re_stdAddChar {length : ℕ} [NeZero length] (mode : ZMod length) :
    (ZMod.stdAddChar mode).re = Real.cos (2 * Real.pi * (mode.val : ℝ) / (length : ℝ)) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_eq_circleExp, Circle.coe_exp]
  rw [Complex.exp_ofReal_mul_I_re]
  congr 1
  ring

/-- The exact contraction margin used in the column-shape bound. -/
theorem norm_add_stdAddChar_le {length : ℕ} [NeZero length] {k : ℝ} (hk : 2 ≤ k)
    (mode : ZMod length) (hmode : mode ≠ 0) :
    ‖((k - 1 : ℝ) : ℂ) + ZMod.stdAddChar mode‖ ≤
      k * (1 - 8 * (k - 1) / (k ^ 2 * (length : ℝ) ^ 2)) := by
  have hk' : 0 < k := by linarith
  have hm : 0 ≤ k - 1 := by linarith
  have hlen : (0 : ℝ) < (length : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne length)
  have hj : 0 < mode.val := Nat.pos_of_ne_zero (fun h => hmode ((ZMod.val_eq_zero _).mp h))
  let z := ZMod.stdAddChar mode
  let norm := ‖((k - 1 : ℝ) : ℂ) + z‖
  have hn : ‖z‖ = 1 := norm_stdAddChar mode
  have hnorm : norm ≤ k := by
    have h := norm_add_le ((k - 1 : ℝ) : ℂ) z
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hm, hn] at h
    dsimp only [norm]
    linarith only [h]
  have hsq : norm ^ 2 = k ^ 2 - 2 * (k - 1) * (1 - z.re) := by
    have hz : z.re ^ 2 + z.im ^ 2 = 1 := by
      have h := Complex.sq_norm z
      rw [hn, Complex.normSq_apply] at h
      nlinarith only [h]
    simp only [norm, Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_add]
    nlinarith only [hz]
  have hcos : 8 / (length : ℝ) ^ 2 ≤ 1 - z.re := by
    dsimp [z]
    rw [re_stdAddChar]
    exact cos_gap_of_cyclic_mode hj mode.val_lt
  have hgap := mul_le_mul_of_nonneg_left hcos (show 0 ≤ 2 * (k - 1) by positivity)
  have hlin : 2 * k * (k - norm) ≥ k ^ 2 - norm ^ 2 := by nlinarith only [sq_nonneg (k - norm)]
  have hbound : 2 * (k - 1) * (8 / (length : ℝ) ^ 2) ≤ 2 * k * (k - norm) := by linarith only [hgap, hlin, hsq]
  have hbound' : 8 * (k - 1) / (k * (length : ℝ) ^ 2) ≤ k - norm := by
    apply (div_le_iff₀ (by positivity)).mpr
    have h := (div_le_iff₀ (by positivity : 0 < (length : ℝ) ^ 2)).mp
      (show 2 * (k - 1) * 8 / (length : ℝ) ^ 2 ≤ 2 * k * (k - norm) by
        rw [mul_div_assoc]; exact hbound)
    nlinarith only [h]
  have heq : k * (1 - 8 * (k - 1) / (k ^ 2 * (length : ℝ) ^ 2)) =
      k - 8 * (k - 1) / (k * (length : ℝ) ^ 2) := by field_simp
  change norm ≤ _
  rw [heq]
  linarith only [hbound']

private theorem dft_translate {length : ℕ} [NeZero length] (field : ZMod length → ℂ) (step mode : ZMod length) :
    ZMod.dft (fun row => field (row + step)) mode = ZMod.stdAddChar (step * mode) * ZMod.dft field mode := by
  simp only [ZMod.dft_apply, smul_eq_mul, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addRight step) _ _ (fun row => ?_)
  change ZMod.stdAddChar (-(row * mode)) * field (row + step) =
    ZMod.stdAddChar (step * mode) * (ZMod.stdAddChar (-((row + step) * mode)) * field (row + step))
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, show step * mode + -((row + step) * mode) = -(row * mode) by ring]

private theorem norm_dft_le {length : ℕ} [NeZero length] (field : ZMod length → ℂ)
    (bound : ℝ) (hbound : ∀ row, ‖field row‖ ≤ bound) (mode : ZMod length) :
    ‖ZMod.dft field mode‖ ≤ (length : ℝ) * bound := by
  rw [ZMod.dft_apply]
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_smul, norm_stdAddChar, one_mul]
  exact (Finset.sum_le_sum (fun row _ => hbound row)).trans_eq (by simp)

private theorem dft_const_at_ne_zero {length : ℕ} [NeZero length] (constant : ℂ) {mode : ZMod length} (hne : mode ≠ 0) :
    ZMod.dft (fun _ => constant) mode = 0 := by
  simp only [ZMod.dft_apply, smul_eq_mul, ← Finset.sum_mul, ← neg_mul, mul_comm _ mode]
  have hsum : ∑ r : ZMod length, ZMod.stdAddChar (-mode * r) = 0 :=
    AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar length (neg_ne_zero.mpr hne))
  simpa only [neg_mul, zero_mul] using congrArg (· * constant) hsum

private theorem norm_le_of_neighbor_contraction {sequence : ℤ → ℂ} {source ratio : ℝ}
    (hratio : 0 ≤ ratio) (hstrict : ratio < 1)
    (hbounded : BddAbove (Set.range fun i => ‖sequence i‖))
    (hcontract : ∀ i, ‖sequence i‖ ≤ source + ratio * max ‖sequence (i - 1)‖ ‖sequence (i + 1)‖)
    (i : ℤ) : ‖sequence i‖ ≤ source / (1 - ratio) := by
  let upper := sSup (Set.range fun i => ‖sequence i‖)
  have hu (i : ℤ) : ‖sequence i‖ ≤ upper := le_csSup hbounded (Set.mem_range_self i)
  have hs : upper ≤ source + ratio * upper := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨i, rfl⟩
    exact (hcontract i).trans (add_le_add_right
      (mul_le_mul_of_nonneg_left (max_le (hu (i - 1)) (hu (i + 1))) hratio) source)
  apply (hu i).trans
  apply (le_div_iff₀ (sub_pos.mpr hstrict)).mpr
  linarith only [hs]

/-- The physical row operator in complex form on a cyclic column. -/
def complexColumnRow {length : ℕ} (k : ℝ) (field : ℤ → ZMod length → ℂ) (column : ℤ) (row : ZMod length) : ℂ :=
  ((k - 1 : ℝ) : ℂ) * field (column + 1) row + field (column + 1) (row + 1) +
    ((k - 1 : ℝ) : ℂ) * field (column - 1) row + field (column - 1) (row - 1) -
      (2 * (k : ℂ)) * field column row

private theorem dft_complexColumnRow {length : ℕ} [NeZero length] (k : ℝ) (field : ℤ → ZMod length → ℂ)
    (column : ℤ) (mode : ZMod length) :
    ZMod.dft (complexColumnRow k field column) mode =
      (((k - 1 : ℝ) : ℂ) + ZMod.stdAddChar mode) * ZMod.dft (field (column + 1)) mode +
      (((k - 1 : ℝ) : ℂ) + ZMod.stdAddChar (-mode)) * ZMod.dft (field (column - 1)) mode -
        (2 * (k : ℂ)) * ZMod.dft (field column) mode := by
  have heq : complexColumnRow k field column =
      ((k - 1 : ℝ) : ℂ) • field (column + 1) + (fun r => field (column + 1) (r + 1)) +
      ((k - 1 : ℝ) : ℂ) • field (column - 1) + (fun r => field (column - 1) (r + -1)) -
        (2 * (k : ℂ)) • field column := by
    funext row
    simp only [complexColumnRow, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_eq_add_neg]
  rw [heq]
  simp only [map_sub, map_add, map_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    dft_translate, one_mul, neg_one_mul]
  ring

/-- The uniform source width with the exact constant from the column
classification. The columnwise constant Fourier mode cancels. A bound on
the column differences suffices for the supremum form of the contraction. -/
theorem norm_sub_zero_le_column_width {length : ℕ} [NeZero length] {k bound : ℝ}
    (hk : 2 ≤ k) (field : ℤ → ZMod length → ℂ)
    (hoscillation : ∃ initial : ℝ, ∀ column row, ‖field column row - field column 0‖ ≤ initial)
    (hrow : ∀ column row, ‖complexColumnRow k field column row‖ ≤ bound) (column : ℤ) (row : ZMod length) :
    ‖field column row - field column 0‖ ≤ ((length : ℝ) - 1) * bound * k * (length : ℝ) ^ 2 / (8 * (k - 1)) := by
  let delta : ℝ := 8 * (k - 1) / (k ^ 2 * (length : ℝ) ^ 2)
  let ratio := 1 - delta
  let modeBound := (length : ℝ) * bound / (2 * k * delta)
  have hk' : 0 < k := by linarith
  have hlen : (0 : ℝ) < (length : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne length)
  have hdelta : 0 < delta := by dsimp [delta]; positivity [show 0 < k - 1 by linarith]
  have hmodeBound (mode : ZMod length) (hne : mode ≠ 0) (i : ℤ) : ‖ZMod.dft (field i) mode‖ ≤ modeBound := by
    let sequence (i : ℤ) := ZMod.dft (field i) mode
    have hcoeffPlus : ‖((k - 1 : ℝ) : ℂ) + ZMod.stdAddChar mode‖ ≤ k * ratio := norm_add_stdAddChar_le hk mode hne
    have hcoeffMinus : ‖((k - 1 : ℝ) : ℂ) + ZMod.stdAddChar (-mode)‖ ≤ k * ratio :=
      norm_add_stdAddChar_le hk (-mode) (neg_ne_zero.mpr hne)
    have hratio : 0 ≤ ratio := by
      by_contra! h
      exact (not_lt_of_ge ((norm_nonneg _).trans hcoeffPlus)) (mul_neg_of_pos_of_neg hk' h)
    have hstrict : ratio < 1 := by dsimp [ratio]; linarith
    obtain ⟨initial, hinitial⟩ := hoscillation
    have hbounded : BddAbove (Set.range fun i => ‖sequence i‖) := by
      refine ⟨(length : ℝ) * initial, ?_⟩
      rintro _ ⟨l, rfl⟩
      have heq : ZMod.dft (fun r => field l r - field l 0) mode = sequence l := by
        change ZMod.dft (field l - fun _ => field l 0) mode = _
        rw [map_sub, Pi.sub_apply, dft_const_at_ne_zero _ hne, sub_zero]
      change ‖sequence l‖ ≤ (length : ℝ) * initial
      rw [← heq]
      exact norm_dft_le _ _ (hinitial l) _
    have hcontract (l : ℤ) : ‖sequence l‖ ≤ (length : ℝ) * bound / (2 * k) +
        ratio * max ‖sequence (l - 1)‖ ‖sequence (l + 1)‖ := by
      let plus := ((k - 1 : ℝ) : ℂ) + ZMod.stdAddChar mode
      let minus := ((k - 1 : ℝ) : ℂ) + ZMod.stdAddChar (-mode)
      let residual := ZMod.dft (complexColumnRow k field l) mode
      have heq : 2 * (k : ℂ) * sequence l = plus * sequence (l + 1) + minus * sequence (l - 1) - residual := by
        have h := dft_complexColumnRow k field l mode
        dsimp only [sequence, plus, minus, residual]
        linear_combination h
      have hnorm := congrArg norm heq
      have hscale : ‖2 * (k : ℂ) * sequence l‖ = 2 * k * ‖sequence l‖ := by
        simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk']
      have hres : ‖residual‖ ≤ (length : ℝ) * bound := norm_dft_le _ _ (hrow l) _
      have habs : 2 * k * ‖sequence l‖ ≤ k * ratio * ‖sequence (l + 1)‖ + k * ratio * ‖sequence (l - 1)‖ +
          (length : ℝ) * bound := by
        rw [← hscale, hnorm]
        refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans ?_) hres)
        rw [norm_mul, norm_mul]
        exact add_le_add (mul_le_mul_of_nonneg_right hcoeffPlus (norm_nonneg _))
          (mul_le_mul_of_nonneg_right hcoeffMinus (norm_nonneg _))
      have h1 := mul_le_mul_of_nonneg_left (le_max_right ‖sequence (l - 1)‖ ‖sequence (l + 1)‖)
        (mul_nonneg hk'.le hratio)
      have h2 := mul_le_mul_of_nonneg_left (le_max_left ‖sequence (l - 1)‖ ‖sequence (l + 1)‖)
        (mul_nonneg hk'.le hratio)
      apply (mul_le_mul_iff_left₀ (show 0 < 2 * k by positivity)).mp
      rw [add_mul, div_mul_cancel₀ _ (by positivity)]
      nlinarith only [habs, h1, h2]
    have h := norm_le_of_neighbor_contraction hratio hstrict hbounded hcontract i
    change ‖sequence i‖ ≤ modeBound
    have heq : (length : ℝ) * bound / (2 * k) / (1 - ratio) = modeBound := by
      dsimp only [ratio, modeBound]
      rw [sub_sub_cancel, div_div]
    exact h.trans_eq heq
  have hinv (r : ZMod length) : field column r = (length : ℂ)⁻¹ *
      ∑ mode : ZMod length, ZMod.stdAddChar (mode * r) * ZMod.dft (field column) mode := by
    have h := congrFun (ZMod.dft.symm_apply_apply (field column)) r
    rw [ZMod.invDFT_apply] at h
    simpa only [smul_eq_mul] using h.symm
  let term (mode : ZMod length) := (ZMod.stdAddChar (mode * row) - 1) * ZMod.dft (field column) mode
  have hdiff : field column row - field column 0 = (length : ℂ)⁻¹ *
      ∑ mode ∈ (Finset.univ : Finset (ZMod length)).erase 0, term mode := by
    rw [hinv row, hinv 0, ← mul_sub, ← Finset.sum_sub_distrib]
    simp only [mul_zero, AddChar.map_zero_eq_one, one_mul, ← sub_one_mul]
    change (length : ℂ)⁻¹ * ∑ mode, term mode = _
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod length))]
    simp [term]
  have hterm (mode : ZMod length) (hne : mode ≠ 0) : ‖term mode‖ ≤ 2 * modeBound := by
    dsimp only [term]
    rw [norm_mul]
    have hchar := norm_sub_le (ZMod.stdAddChar (mode * row)) (1 : ℂ)
    norm_num [norm_stdAddChar] at hchar
    exact mul_le_mul hchar (hmodeBound mode hne column) (norm_nonneg _) (by norm_num)
  have hsum : ‖∑ mode ∈ (Finset.univ : Finset (ZMod length)).erase 0, term mode‖ ≤
      ((length : ℝ) - 1) * (2 * modeBound) := by
    calc
      _ ≤ ∑ mode ∈ (Finset.univ : Finset (ZMod length)).erase 0, ‖term mode‖ := norm_sum_le _ _
      _ ≤ ∑ _ ∈ (Finset.univ : Finset (ZMod length)).erase 0, 2 * modeBound :=
        Finset.sum_le_sum fun mode hmem => hterm mode (Finset.ne_of_mem_erase hmem)
      _ = _ := by
        have hcard : ((Finset.univ : Finset (ZMod length)).erase 0).card + 1 = length := by
          rw [Finset.card_erase_add_one (Finset.mem_univ _), Finset.card_univ, ZMod.card]
        rw [Finset.sum_const, nsmul_eq_mul]
        have hc : (((Finset.univ : Finset (ZMod length)).erase 0).card : ℝ) + 1 = length := by exact_mod_cast hcard
        have heq : (((Finset.univ : Finset (ZMod length)).erase 0).card : ℝ) = (length : ℝ) - 1 := by linarith
        rw [heq]
  rw [hdiff, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (length : ℝ)⁻¹ * (((length : ℝ) - 1) * (2 * modeBound)) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by dsimp [modeBound, delta]; field_simp

end FLatticePaper.GeneralK
