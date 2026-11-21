import FLatticePaper.GeneralK.GrowthClosed

namespace FLatticePaper.GeneralK

open Filter Topology

private theorem symmetricMatrix_sub (a b c u v w : ℝ) :
    symmetricMatrix a b c - symmetricMatrix u v w = symmetricMatrix (a - u) (b - v) (c - w) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem posSemidef_parabolic (b c : ℝ) (hc : 0 < c) :
    (symmetricMatrix (b ^ 2 / c) b c).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.isHermitian_iff_isSymm.mpr (isSymm_symmetricMatrix ..))
  intro x
  have heq : dotProduct (star x) ((symmetricMatrix (b ^ 2 / c) b c).mulVec x) =
      (b * x 0 + c * x 1) ^ 2 / c := by
    simp [star_trivial, symmetricMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp
  rw [heq]
  exact div_nonneg (sq_nonneg _) hc.le

theorem posSemidef_topEntry {a : ℝ} (ha : 0 ≤ a) : (symmetricMatrix a 0 0).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.isHermitian_iff_isSymm.mpr (isSymm_symmetricMatrix ..))
  intro x
  simp [star_trivial, symmetricMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  calc
    _ = a * (x 0) ^ 2 := by ring
    _ ≥ 0 := mul_nonneg ha (sq_nonneg _)

theorem exists_mem_growthSet_slice {k : ℤ} (hk : 2 ≤ k) (b c : ℝ) :
    ∃ a, symmetricMatrix a b c ∈ growthSet k := by
  let m := ⌊(k : ℝ) * c⌋ + 1
  let s := (m : ℝ) / (k : ℝ)
  have hk' : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hcs : c < s := by
    apply (lt_div_iff₀ hk').mpr
    dsimp [m]
    push_cast
    rw [mul_comm]
    exact Int.lt_floor_add_one _
  let a := -((k : ℝ) - 1) * s - (s - b) ^ 2 / (s - c)
  refine ⟨a, ?_⟩
  have h := sub_mem_growthSet_of_posSemidef hk (harmonicMatrix_mem_growthSet hk m 0)
    (posSemidef_parabolic (s - b) (s - c) (sub_pos.mpr hcs))
  change symmetricMatrix (-((k : ℝ) - 1) * s) (s + (0 : ℤ)) s -
    symmetricMatrix ((s - b) ^ 2 / (s - c)) (s - b) (s - c) ∈ growthSet k at h
  simpa only [Int.cast_zero, add_zero, symmetricMatrix_sub, sub_sub_cancel] using h

private noncomputable def nearestRat (value : ℝ) (n : ℕ) : ℚ :=
  (⌊((n : ℝ) + 1) * value + 1 / 2⌋ : ℚ) / ((n : ℚ) + 1)

private noncomputable def lowerRat (value : ℝ) (n : ℕ) : ℚ :=
  ((⌊((n : ℝ) + 1) * value⌋ - 1 : ℤ) : ℚ) / ((n : ℚ) + 1)

private theorem abs_sub_nearestRat_le (value : ℝ) (n : ℕ) :
    |value - (nearestRat value n : ℝ)| ≤ 1 / (2 * ((n : ℝ) + 1)) := by
  let h : ℝ := (n : ℝ) + 1
  let rounded : ℤ := ⌊h * value + 1 / 2⌋
  have hpos : 0 < h := by dsimp [h]; positivity
  have heq : (nearestRat value n : ℝ) = (rounded : ℝ) / h := by simp [nearestRat, rounded, h]
  rw [heq]
  calc
    |value - (rounded : ℝ) / h| = |h * value - rounded| / h := by
      rw [show value - (rounded : ℝ) / h = (h * value - rounded) / h by field_simp,
        abs_div, abs_of_pos hpos]
    _ ≤ (1 / 2) / h := by
      apply div_le_div_of_nonneg_right ?_ hpos.le
      apply abs_le.mpr
      have hlo := Int.floor_le (h * value + 1 / 2)
      have hhi := Int.lt_floor_add_one (h * value + 1 / 2)
      change (rounded : ℝ) ≤ h * value + 1 / 2 at hlo
      change h * value + 1 / 2 < (rounded : ℝ) + 1 at hhi
      constructor <;> linarith only [hlo, hhi]
    _ = _ := by change (1 / 2) / h = 1 / (2 * h); rw [div_div]

private theorem sub_lowerRat_bounds (value : ℝ) (n : ℕ) :
    1 / ((n : ℝ) + 1) ≤ value - (lowerRat value n : ℝ) ∧
      value - (lowerRat value n : ℝ) ≤ 2 / ((n : ℝ) + 1) := by
  let h : ℝ := (n : ℝ) + 1
  let rounded : ℤ := ⌊h * value⌋
  have hpos : 0 < h := by dsimp [h]; positivity
  have heq : value - (lowerRat value n : ℝ) = (value * h - (rounded : ℝ) + 1) / h := by
    simp [lowerRat, rounded, h]
    field_simp
    ring
  rw [heq]
  change 1 / h ≤ _ ∧ _ ≤ 2 / h
  have hlo : (rounded : ℝ) ≤ h * value := Int.floor_le _
  have hhi : h * value < (rounded : ℝ) + 1 := Int.lt_floor_add_one _
  constructor <;> apply div_le_div_of_nonneg_right _ hpos.le <;> linarith only [hlo, hhi]

private theorem tendsto_rat_approximations (value : ℝ) :
    Tendsto (fun n => (nearestRat value n : ℝ)) atTop (𝓝 value) ∧
      Tendsto (fun n => (lowerRat value n : ℝ)) atTop (𝓝 value) := by
  have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hnear : Tendsto (fun n : ℕ => 1 / (2 * ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have heq (n : ℕ) : (1 / 2 : ℝ) * (1 / ((n : ℝ) + 1)) = 1 / (2 * ((n : ℝ) + 1)) := by
      rw [one_div_mul_one_div]
    simpa only [mul_zero] using (hinv.const_mul (1 / 2)).congr heq
  have hlow : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_one_div] using hinv.const_mul 2
  constructor <;> apply tendsto_iff_dist_tendsto_zero.mpr
  · refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) hnear
    simpa only [Real.dist_eq, abs_sub_comm] using abs_sub_nearestRat_le value n
  · refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) hlow
    have h := sub_lowerRat_bounds value n
    rw [dist_comm, Real.dist_eq, abs_of_nonneg ((by positivity : 0 ≤ 1 / ((n : ℝ) + 1)).trans h.1)]
    exact h.2

/-- The parabolic terms entering the real classification from the rational
first-entry endpoints. The denominator is strictly positive by definition. -/
def parabolicValues (endpoint : ℚ → ℚ → ℝ) (b c : ℝ) : Set ℝ :=
  {value | ∃ u v : ℚ, (v : ℝ) < c ∧ value = endpoint u v + (b - (u : ℝ)) ^ 2 / (c - (v : ℝ))}

/-- The downward cones under the rational first-entry endpoints. -/
def rationalConeUnion (endpoint : ℚ → ℚ → ℝ) : Set (Matrix (Fin 2) (Fin 2) ℝ) :=
  {matrix | matrix.IsSymm ∧ ∃ u v : ℚ, (symmetricMatrix (endpoint u v) u v - matrix).PosSemidef}

variable {k : ℤ} {endpoint : ℚ → ℚ → ℝ}

private theorem le_parabolic_of_mem_growthSet (hk : 2 ≤ k)
    (hslice : ∀ (u v : ℚ) (a : ℝ), symmetricMatrix a u v ∈ growthSet k ↔ a ≤ endpoint u v)
    {a b c : ℝ} (hm : symmetricMatrix a b c ∈ growthSet k) (u v : ℚ) (hv : (v : ℝ) < c) :
    a ≤ endpoint u v + (b - (u : ℝ)) ^ 2 / (c - (v : ℝ)) := by
  have h := sub_mem_growthSet_of_posSemidef hk hm
    (posSemidef_parabolic (b - (u : ℝ)) (c - (v : ℝ)) (sub_pos.mpr hv))
  rw [symmetricMatrix_sub, sub_sub_cancel b, sub_sub_cancel c] at h
  linarith only [(hslice _ _ _).mp h]

private theorem exists_tendsto_rationalCone {a b c : ℝ}
    (hparabola : ∀ u v : ℚ, (v : ℝ) < c → a ≤ endpoint u v + (b - (u : ℝ)) ^ 2 / (c - (v : ℝ))) :
    ∃ approximants : ℕ → Matrix (Fin 2) (Fin 2) ℝ, (∀ n, approximants n ∈ rationalConeUnion endpoint) ∧
      Tendsto approximants atTop (𝓝 (symmetricMatrix a b c)) := by
  let correction (n : ℕ) : ℝ := 1 / (4 * ((n : ℝ) + 1))
  let approximants (n : ℕ) := symmetricMatrix (a - correction n) (nearestRat b n) (lowerRat c n)
  refine ⟨approximants, fun n => ?_, ?_⟩
  · let h : ℝ := (n : ℝ) + 1
    have hpos : 0 < h := by dsimp [h]; positivity
    have hdiff := (sub_lowerRat_bounds c n).1
    have hv : 0 < c - (lowerRat c n : ℝ) := (by positivity : 0 < 1 / h).trans_le hdiff
    have hsq : (b - (nearestRat b n : ℝ)) ^ 2 ≤ (1 / (2 * h)) ^ 2 := by
      rw [← sq_abs (b - (nearestRat b n : ℝ))]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_sub_nearestRat_le b n) 2
    have hcorr : (b - (nearestRat b n : ℝ)) ^ 2 / (c - (lowerRat c n : ℝ)) ≤ correction n := by
      apply (div_le_iff₀ hv).mpr
      calc
        _ ≤ (1 / (2 * h)) ^ 2 := hsq
        _ = correction n * (1 / h) := by dsimp [correction, h]; field_simp; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hdiff (by dsimp [correction]; positivity)
    have hend : a - correction n ≤ endpoint (nearestRat b n) (lowerRat c n) := by
      linarith only [hparabola (nearestRat b n) (lowerRat c n) (sub_pos.mp hv), hcorr]
    refine ⟨isSymm_symmetricMatrix .., nearestRat b n, lowerRat c n, ?_⟩
    simp only [approximants, symmetricMatrix_sub, sub_self]
    exact posSemidef_topEntry (sub_nonneg.mpr hend)
  · have hu := (tendsto_rat_approximations b).1
    have hv := (tendsto_rat_approximations c).2
    have hcorr : Tendsto correction atTop (𝓝 0) := by
      have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have heq (n : ℕ) : (1 / 4 : ℝ) * (1 / ((n : ℝ) + 1)) = correction n := by
        rw [one_div_mul_one_div]
      simpa only [mul_zero] using (hinv.const_mul (1 / 4)).congr heq
    have ha : Tendsto (fun n => a - correction n) atTop (𝓝 a) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub hcorr
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    fin_cases i <;> fin_cases j
    · exact ha
    · exact hu
    · exact hu
    · exact hv

theorem closure_rationalCone_subset_growthSet (hk : 2 ≤ k)
    (hadmit : ∀ (u v : ℚ), symmetricMatrix (endpoint u v) u v ∈ growthSet k) :
    closure (rationalConeUnion endpoint) ⊆ growthSet k := by
  apply closure_minimal _ (isClosed_growthSet hk)
  rintro matrix ⟨_, u, v, hpos⟩
  have h := sub_mem_growthSet_of_posSemidef hk (hadmit u v) hpos
  rwa [sub_sub_cancel] at h

/-- Once the rational slice endpoint calculation is available, the
parabolic bound characterizes membership for every real matrix. -/
theorem mem_growthSet_iff_le_sInf_parabolicValues (hk : 2 ≤ k)
    (hslice : ∀ (u v : ℚ) (a : ℝ), symmetricMatrix a u v ∈ growthSet k ↔ a ≤ endpoint u v)
    (a b c : ℝ) : symmetricMatrix a b c ∈ growthSet k ↔ a ≤ sInf (parabolicValues endpoint b c) := by
  have hnonempty : (parabolicValues endpoint b c).Nonempty := by
    obtain ⟨v, hv⟩ := exists_rat_lt c
    exact ⟨_, 0, v, hv, rfl⟩
  have hbounded : BddBelow (parabolicValues endpoint b c) := by
    obtain ⟨seed, hseed⟩ := exists_mem_growthSet_slice hk b c
    exact ⟨seed, by rintro _ ⟨u, v, hv, rfl⟩; exact le_parabolic_of_mem_growthSet hk hslice hseed u v hv⟩
  constructor
  · intro hm
    apply le_csInf hnonempty
    rintro _ ⟨u, v, hv, rfl⟩
    exact le_parabolic_of_mem_growthSet hk hslice hm u v hv
  · intro hm
    have hparabola (u v : ℚ) (hv : (v : ℝ) < c) : a ≤ endpoint u v + (b - (u : ℝ)) ^ 2 / (c - (v : ℝ)) :=
      hm.trans (csInf_le hbounded ⟨u, v, hv, rfl⟩)
    obtain ⟨approximants, hmem, hlim⟩ := exists_tendsto_rationalCone hparabola
    exact closure_rationalCone_subset_growthSet hk (fun u v => (hslice u v _).mpr le_rfl)
      (mem_closure_of_tendsto hlim (Eventually.of_forall hmem))

/-- Both cone inclusions, including the passage to closure at irrational
entries, follow from the rational endpoint calculation. -/
theorem growthSet_eq_closure_rationalConeUnion (hk : 2 ≤ k)
    (hslice : ∀ (u v : ℚ) (a : ℝ), symmetricMatrix a u v ∈ growthSet k ↔ a ≤ endpoint u v) :
    growthSet k = closure (rationalConeUnion endpoint) := by
  apply le_antisymm _ (closure_rationalCone_subset_growthSet hk (fun u v => (hslice u v _).mpr le_rfl))
  intro matrix hmatrix
  have heq := symmetricMatrix_entries hmatrix.1
  rw [← heq] at hmatrix ⊢
  obtain ⟨approximants, hmem, hlim⟩ := exists_tendsto_rationalCone
    (le_parabolic_of_mem_growthSet hk hslice hmatrix)
  exact mem_closure_of_tendsto hlim (Eventually.of_forall hmem)

end FLatticePaper.GeneralK
