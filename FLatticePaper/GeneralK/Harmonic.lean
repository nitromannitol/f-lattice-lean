import FLatticePaper.GeneralK.Growth
import FLatticePaper.Construction.PeriodExtension

namespace FLatticePaper.GeneralK

open Construction

/-- The integer primitive with first difference `n / k` at `n`. -/
def phasePrimitive (k n : ℤ) : ℤ :=
  k * chooseTwo (n / k) + (n / k) * (n % k)

theorem phasePrimitive_succ {k : ℤ} (hk : 2 ≤ k) (n : ℤ) :
    phasePrimitive k (n + 1) = phasePrimitive k n + n / k := by
  have hkPos : 0 < k := by omega
  have hr₀ := Int.emod_nonneg n (ne_of_gt hkPos)
  have hrk := Int.emod_lt_of_pos n hkPos
  unfold phasePrimitive
  rw [Int.add_ediv_of_pos hkPos, Int.ediv_eq_zero_of_lt (by decide : (0 : ℤ) ≤ 1) (by omega : 1 < k),
    Int.emod_eq_of_lt (by decide : (0 : ℤ) ≤ 1) (by omega : 1 < k), add_zero,
    ← Int.emod_add_emod n k 1]
  by_cases h : n % k + 1 < k
  · rw [if_neg (not_le_of_gt h), add_zero, Int.emod_eq_of_lt (by omega) h]
    ring
  · have hcarry : n % k + 1 = k := by omega
    rw [hcarry, if_pos le_rfl, Int.emod_self, mul_zero, add_zero, chooseTwo_add]
    simp only [show chooseTwo (1 : ℤ) = 0 by decide, add_zero, mul_one]
    have hr : n % k = k - 1 := by omega
    rw [hr]
    ring

theorem phasePrimitive_secondDifference {k : ℤ} (hk : 2 ≤ k) (n : ℤ) :
    phasePrimitive k (n - 1) + phasePrimitive k (n + 1) - 2 * phasePrimitive k n =
      if n % k = 0 then 1 else 0 := by
  have hprev := phasePrimitive_succ hk (n - 1)
  rw [sub_add_cancel] at hprev
  rw [phasePrimitive_succ hk n]
  have hdiv := Int.emod_add_mul_ediv n k
  have hr₀ := Int.emod_nonneg n (by omega : k ≠ 0)
  have hrk := Int.emod_lt_of_pos n (by omega : 0 < k)
  split
  next hr =>
    have hq : (n - 1) / k = n / k - 1 := by
      apply (Int.ediv_eq_iff_of_pos (by omega : 0 < k)).mpr
      rw [hr, zero_add] at hdiv
      rw [sub_mul, one_mul, mul_comm (n / k) k]
      omega
    omega
  next hr =>
    have hq : (n - 1) / k = n / k := by
      apply (Int.ediv_eq_iff_of_pos (by omega : 0 < k)).mpr
      rw [mul_comm (n / k) k]
      omega
    omega

/-- The physical harmonic height at the first grid generator. -/
def harmonicGridField (k : ℤ) : Field := fun site => phasePrimitive k (site.1 + site.2) - chooseTwo site.1

theorem laplacian_harmonicGridField {k : ℤ} (hk : 2 ≤ k) (site : Site) :
    laplacian k (harmonicGridField k) site = 0 := by
  obtain ⟨x, y⟩ := site
  have hphase := phasePrimitive_secondDifference hk (x + y)
  by_cases h : Retained k (x, y)
  · have hmod : (x + y) % k = 0 := h
    rw [if_pos hmod] at hphase
    have hs : chooseTwo (x + 1) = chooseTwo x + x := by simpa [chooseTwo] using chooseTwo_add x 1
    have hp : chooseTwo (x - 1) = chooseTwo x + 1 - x := by
      simpa [sub_eq_add_neg, show chooseTwo (-1) = 1 by decide] using chooseTwo_add x (-1)
    simp only [laplacian, incomingNeg, incomingPos, if_pos h, harmonicGridField]
    rw [show x - 1 + y = x + y - 1 by omega, show x + 1 + y = x + y + 1 by omega, hs, hp]
    omega
  · have hmod : (x + y) % k ≠ 0 := h
    rw [if_neg hmod] at hphase
    simp only [laplacian, incomingNeg, incomingPos, if_neg h, harmonicGridField]
    rw [show x + (y - 1) = x + y - 1 by omega, show x + (y + 1) = x + y + 1 by omega]
    omega

private theorem cast_chooseTwo (n : ℤ) : (chooseTwo n : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  have h : (2 : ℝ) * (chooseTwo n : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
    exact_mod_cast two_mul_chooseTwo n
  linarith

theorem cast_phasePrimitive {k : ℤ} (hk : 0 < k) (n : ℤ) :
    (phasePrimitive k n : ℝ) = (n : ℝ) ^ 2 / (2 * (k : ℝ)) - (n : ℝ) / 2 +
      ((n % k : ℤ) : ℝ) * ((k : ℝ) - ((n % k : ℤ) : ℝ)) / (2 * (k : ℝ)) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hdiv : ((n % k : ℤ) : ℝ) + (k : ℝ) * ((n / k : ℤ) : ℝ) = n := by
    exact_mod_cast Int.emod_add_mul_ediv n k
  simp only [phasePrimitive, Int.cast_add, Int.cast_mul, cast_chooseTwo]
  rw [← hdiv]
  field_simp
  ring

/-- The symmetric physical matrix `H(s,t)` from the harmonic translations. -/
noncomputable def harmonicMatrix (k : ℤ) (s t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  symmetricMatrix (-((k : ℝ) - 1) * s) (s + t) s

private theorem harmonicGridField_error_bound {k : ℤ} (hk : 2 ≤ k) (site : Site) :
    |(harmonicGridField k site : ℝ) - matrixQuadratic (harmonicMatrix k (1 / (k : ℝ)) 0) site -
      (-1 / 2) * (site.2 : ℝ)| ≤ (k : ℝ) := by
  have hkPos : 0 < k := by omega
  have hkReal : 0 < (k : ℝ) := by exact_mod_cast hkPos
  obtain ⟨x, y⟩ := site
  let r : ℝ := (((x + y) % k : ℤ) : ℝ)
  have hr₀ : 0 ≤ r := by
    dsimp only [r]
    exact_mod_cast Int.emod_nonneg (x + y) (ne_of_gt hkPos)
  have hrk : r ≤ (k : ℝ) := by
    dsimp only [r]
    exact_mod_cast (Int.emod_lt_of_pos (x + y) hkPos).le
  have herror : (harmonicGridField k (x, y) : ℝ) -
      matrixQuadratic (harmonicMatrix k (1 / (k : ℝ)) 0) (x, y) -
      (-1 / 2) * (y : ℝ) = r * ((k : ℝ) - r) / (2 * (k : ℝ)) := by
    simp only [harmonicGridField, Int.cast_sub, cast_chooseTwo, cast_phasePrimitive hkPos, Int.cast_add,
      harmonicMatrix, matrixQuadratic_symmetricMatrix]
    dsimp only [r]
    simp
    field_simp
    ring
  change |_| ≤ (k : ℝ)
  rw [herror, abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ (by positivity : 0 < 2 * (k : ℝ))).mpr
  have hprod := mul_le_mul hrk (show (k : ℝ) - r ≤ k by linarith) (by linarith) hkReal.le
  nlinarith only [hprod, sq_nonneg (k : ℝ)]

theorem quadraticGrowth_harmonicGridField {k : ℤ} (hk : 2 ≤ k) :
    HasQuadraticGrowth (harmonicGridField k) (harmonicMatrix k (1 / (k : ℝ)) 0) := by
  have hk' : (0 : ℝ) ≤ k := by exact_mod_cast (show 0 ≤ k by omega)
  apply quadraticGrowth_of_bounded_linear_error 0 (-1 / 2) (k : ℝ) hk'
  intro site
  simpa only [zero_mul, zero_add] using harmonicGridField_error_bound hk site

/-- The integer harmonic height with parameters `s = m/k` and `t`. -/
def harmonicField (k m t : ℤ) : Field :=
  fun site => m * harmonicGridField k site + t * (site.1 * site.2)

theorem laplacian_harmonicField {k : ℤ} (hk : 2 ≤ k) (m t : ℤ) (site : Site) :
    laplacian k (harmonicField k m t) site = 0 := by
  have hgrid := laplacian_harmonicGridField hk site
  have hcross : laplacian k (fun point : Site => point.1 * point.2) site = 0 := by
    obtain ⟨x, y⟩ := site
    by_cases h : Retained k (x, y) <;> simp [laplacian, incomingNeg, incomingPos, h] <;> ring
  simp only [laplacian, harmonicField] at hgrid hcross ⊢
  linear_combination m * hgrid + t * hcross

theorem quadraticGrowth_harmonicField {k : ℤ} (hk : 2 ≤ k) (m t : ℤ) :
    HasQuadraticGrowth (harmonicField k m t) (harmonicMatrix k ((m : ℝ) / (k : ℝ)) t) := by
  have hk' : (0 : ℝ) ≤ k := by exact_mod_cast (show 0 ≤ k by omega)
  apply quadraticGrowth_of_bounded_linear_error 0 (-(m : ℝ) / 2) (|(m : ℝ)| * k) (by positivity)
  rintro ⟨x, y⟩
  have hquad : matrixQuadratic (harmonicMatrix k ((m : ℝ) / (k : ℝ)) t) (x, y) =
      (m : ℝ) * matrixQuadratic (harmonicMatrix k (1 / (k : ℝ)) 0) (x, y) + (t : ℝ) * x * y := by
    simp only [harmonicMatrix, matrixQuadratic_symmetricMatrix]
    ring
  have herror : (harmonicField k m t (x, y) : ℝ) -
      matrixQuadratic (harmonicMatrix k ((m : ℝ) / (k : ℝ)) t) (x, y) -
      (0 * (x : ℝ) + (-(m : ℝ) / 2) * (y : ℝ)) =
      (m : ℝ) * ((harmonicGridField k (x, y) : ℝ) -
        matrixQuadratic (harmonicMatrix k (1 / (k : ℝ)) 0) (x, y) - (-1 / 2) * (y : ℝ)) := by
    simp only [harmonicField, Int.cast_add, Int.cast_mul, hquad]
    ring
  rw [herror, abs_mul]
  exact mul_le_mul_of_nonneg_left (harmonicGridField_error_bound hk (x, y)) (abs_nonneg _)

theorem harmonicMatrix_mem_growthSet {k : ℤ} (hk : 2 ≤ k) (m t : ℤ) :
    harmonicMatrix k ((m : ℝ) / (k : ℝ)) t ∈ growthSet k := by
  apply (symmetricMatrix_mem_growthSet_iff ..).mpr
  exact ⟨harmonicField k m t, fun site => (laplacian_harmonicField hk m t site).le,
    quadraticGrowth_harmonicField hk m t⟩

/-- Translation by any integer-realizable harmonic Hessian preserves the physical growth set. -/
theorem add_harmonicMatrix_mem_growthSet_iff {k : ℤ} (hk : 2 ≤ k) (m t : ℤ)
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A + harmonicMatrix k ((m : ℝ) / (k : ℝ)) t ∈ growthSet k ↔ A ∈ growthSet k := by
  have hneg : harmonicMatrix k (((-m : ℤ) : ℝ) / (k : ℝ)) ((-t : ℤ) : ℝ) =
      -harmonicMatrix k ((m : ℝ) / (k : ℝ)) t := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [harmonicMatrix, symmetricMatrix] <;> ring
  constructor
  · intro h
    have hadd := add_mem_growthSet h (harmonicMatrix_mem_growthSet hk (-m) (-t))
    rw [hneg, add_neg_cancel_right] at hadd
    exact hadd
  · exact fun h => add_mem_growthSet h (harmonicMatrix_mem_growthSet hk m t)

end FLatticePaper.GeneralK
