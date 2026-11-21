import FLatticePaper.GeneralK.ColumnGraph
import FLatticePaper.GeneralK.ColumnLift

namespace FLatticePaper.GeneralK

private theorem chain_nonneg_of_secondDifference_nonpos {k : ℤ} {f : ℤ → ℝ}
    (hfirst : f 0 = 0) (hlast : f k = 0)
    (hconcave : ∀ offset, 0 < offset → offset < k → f (offset - 1) + f (offset + 1) - 2 * f offset ≤ 0)
    (offset : ℤ) (hlo : 0 ≤ offset) (hhi : offset ≤ k) : 0 ≤ f offset := by
  classical
  by_contra! hnegative
  let chain := Finset.Icc 0 k
  obtain ⟨minimizer, hminimizer, hmin⟩ := chain.exists_min_image f ⟨offset, Finset.mem_Icc.mpr ⟨hlo, hhi⟩⟩
  let plateau := chain.filter fun i => f i = f minimizer
  obtain ⟨leftmost, hleftmost, hleftmostMin⟩ := plateau.exists_min_image id
    ⟨minimizer, Finset.mem_filter.mpr ⟨hminimizer, rfl⟩⟩
  obtain ⟨hleftmostChain, hleftmostValue⟩ := Finset.mem_filter.mp hleftmost
  obtain ⟨hleftmostLo, hleftmostHi⟩ := Finset.mem_Icc.mp hleftmostChain
  have hleftmostNeg := (hmin offset (Finset.mem_Icc.mpr ⟨hlo, hhi⟩)).trans_lt hnegative
  rw [← hleftmostValue] at hleftmostNeg
  have hleftmostPositive : 0 < leftmost := by
    by_contra! h
    have heq : leftmost = 0 := by omega
    rw [heq, hfirst] at hleftmostNeg
    exact (lt_irrefl (0 : ℝ)) hleftmostNeg
  have hleftmostBelow : leftmost < k := by
    by_contra! h
    have heq : leftmost = k := by omega
    rw [heq, hlast] at hleftmostNeg
    exact (lt_irrefl (0 : ℝ)) hleftmostNeg
  have hstep : leftmost - 1 ∈ chain := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hstep' : leftmost + 1 ∈ chain := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hl := hmin (leftmost - 1) hstep
  have hr := hmin (leftmost + 1) hstep'
  have hdiff := hconcave leftmost hleftmostPositive hleftmostBelow
  have hval : f (leftmost - 1) = f minimizer := by linarith only [hl, hr, hdiff, hleftmostValue]
  have h := hleftmostMin (leftmost - 1) (Finset.mem_filter.mpr ⟨hstep, hval⟩)
  change leftmost ≤ leftmost - 1 at h
  omega

/-- The linear interpolation through the two physical endpoints of a chain. -/
noncomputable def linearChainValue (k : ℤ) (field : Field) (column row offset : ℤ) : ℝ :=
  ((k : ℝ) - (offset : ℝ)) / (k : ℝ) * (field (columnSite k column row 0) : ℝ) +
    (offset : ℝ) / (k : ℝ) * (field (columnSite k column (row + 1) 0) : ℝ)

/-- Bounded integer charges give the exact parabolic error bound on the
actual vertical chains between retained sites. -/
theorem chain_sub_linearChainValue_bounds {k bound : ℤ} (hk : 2 ≤ k) {field : Field}
    (hcharge : ∀ site, 0 ≤ -laplacian k field site ∧ -laplacian k field site ≤ bound)
    (column row offset : ℤ) (hlo : 0 ≤ offset) (hhi : offset ≤ k) :
    0 ≤ (field (columnSite k column row offset) : ℝ) - linearChainValue k field column row offset ∧
    (field (columnSite k column row offset) : ℝ) - linearChainValue k field column row offset ≤
      (bound : ℝ) * (offset : ℝ) * ((k : ℝ) - (offset : ℝ)) / 2 := by
  let error (j : ℤ) := (field (columnSite k column row j) : ℝ) - linearChainValue k field column row j
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have htop : columnSite k column row k = columnSite k column (row + 1) 0 := by
    apply Prod.ext
    · rfl
    · simp only [columnSite]
      ring
  have hzero : error 0 = 0 := by simp [error, linearChainValue, hk']
  have hlast : error k = 0 := by simp [error, linearChainValue, hk', htop]
  have hstar (j : ℤ) (hj₀ : 0 < j) (hjk : j < k) :
      -(bound : ℝ) ≤ error (j - 1) + error (j + 1) - 2 * error j ∧
      error (j - 1) + error (j + 1) - 2 * error j ≤ 0 := by
    let site := columnSite k column row j
    have hphase : ¬ Retained k site := by
      change ¬ Retained k (columnSite k column row j)
      rw [Retained, columnSite_phase, Int.emod_eq_of_lt hj₀.le hjk]
      omega
    have hn : incomingNeg k site = columnSite k column row (j - 1) := by
      rw [incomingNeg, if_neg hphase]
      apply Prod.ext
      · rfl
      · dsimp [site, columnSite]
        ring
    have hp : incomingPos k site = columnSite k column row (j + 1) := by
      rw [incomingPos, if_neg hphase]
      apply Prod.ext
      · rfl
      · dsimp [site, columnSite]
        ring
    have heq : error (j - 1) + error (j + 1) - 2 * error j = (laplacian k field site : ℝ) := by
      simp only [error, laplacian, hn, hp, Int.cast_add, Int.cast_sub, linearChainValue, site]
      ring
    rw [heq]
    obtain ⟨hl, hu⟩ := hcharge site
    constructor
    · exact_mod_cast (show -bound ≤ laplacian k field site by omega)
    · exact_mod_cast (show laplacian k field site ≤ 0 by omega)
  let parabola (j : ℤ) := (bound : ℝ) * (j : ℝ) * ((k : ℝ) - (j : ℝ)) / 2
  have hupper (j : ℤ) (hj₀ : 0 < j) (hjk : j < k) :
      (parabola (j - 1) - error (j - 1)) + (parabola (j + 1) - error (j + 1)) -
        2 * (parabola j - error j) ≤ 0 := by
    have heq : parabola (j - 1) + parabola (j + 1) - 2 * parabola j = -(bound : ℝ) := by
      simp only [parabola, Int.cast_add, Int.cast_sub, Int.cast_one]
      ring
    linarith only [(hstar j hj₀ hjk).1, heq]
  have hparab : 0 ≤ parabola offset - error offset :=
    chain_nonneg_of_secondDifference_nonpos (f := fun j => parabola j - error j)
      (by simp [parabola, hzero]) (by simp [parabola, hlast]) hupper offset hlo hhi
  exact ⟨chain_nonneg_of_secondDifference_nonpos hzero hlast (fun j hj₀ hjk => (hstar j hj₀ hjk).2) offset hlo hhi,
    sub_nonneg.mp hparab⟩

/-- The restriction of a bounded-charge physical height to retained rows
has linear row deficit between zero and the exact bound `k² D`. -/
theorem linearColumnRow_restriction_bounds {k bound : ℤ} (hk : 2 ≤ k) {field : Field}
    (hcharge : ∀ site, 0 ≤ -laplacian k field site ∧ -laplacian k field site ≤ bound)
    (column row : ℤ) :
    let reduced : Field := fun point => field (columnSite k point.1 point.2 0)
    0 ≤ -linearColumnRow k reduced column row ∧ -linearColumnRow k reduced column row ≤ k ^ 2 * bound := by
  let center := columnSite k column row 0
  let negError : ℝ := (field (incomingNeg k center) : ℝ) - linearChainValue k field (column - 1) (row - 1) (k - 1)
  let posError : ℝ := (field (incomingPos k center) : ℝ) - linearChainValue k field (column + 1) row 1
  have hposK : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hen : 0 ≤ negError ∧ negError ≤ (bound : ℝ) * ((k : ℝ) - 1) / 2 := by
    obtain ⟨hlo, hhi⟩ := chain_sub_linearChainValue_bounds hk hcharge (column - 1) (row - 1) (k - 1) (by omega) (by omega)
    rw [show negError = (field (columnSite k (column - 1) (row - 1) (k - 1)) : ℝ) -
      linearChainValue k field (column - 1) (row - 1) (k - 1) by simp [negError, center, incomingNeg_columnSite]]
    refine ⟨hlo, ?_⟩
    convert hhi using 1
    push_cast
    ring
  have hep : 0 ≤ posError ∧ posError ≤ (bound : ℝ) * ((k : ℝ) - 1) / 2 := by
    obtain ⟨hlo, hhi⟩ := chain_sub_linearChainValue_bounds hk hcharge (column + 1) row 1 (by omega) (by omega)
    rw [show posError = (field (columnSite k (column + 1) row 1) : ℝ) - linearChainValue k field (column + 1) row 1 by
      simp [posError, center, incomingPos_columnSite]]
    exact ⟨hlo, by simpa only [Int.cast_one, mul_one] using hhi⟩
  let reduced : Field := fun point => field (columnSite k point.1 point.2 0)
  have heq : (linearColumnRow k reduced column row : ℝ) =
      (k : ℝ) * ((laplacian k field center : ℝ) - negError - posError) := by
    simp only [linearColumnRow, reduced, negError, posError, linearChainValue, laplacian, Int.cast_add,
      Int.cast_sub, Int.cast_mul, Int.cast_one, sub_add_cancel]
    field_simp
    ring
  have hlow : -(bound : ℝ) ≤ (laplacian k field center : ℝ) := by exact_mod_cast
    (show -bound ≤ laplacian k field center by have := (hcharge center).2; omega)
  have hhigh : (laplacian k field center : ℝ) ≤ 0 := by exact_mod_cast
    (show laplacian k field center ≤ 0 by have := (hcharge center).1; omega)
  have hb₀ := mul_nonneg hposK.le (show 0 ≤ negError + posError - (laplacian k field center : ℝ) by
    linarith only [hen.1, hep.1, hhigh])
  have hb₁ := mul_le_mul_of_nonneg_left (show negError + posError - (laplacian k field center : ℝ) ≤
    (bound : ℝ) * (k : ℝ) by nlinarith only [hen.2, hep.2, hlow]) hposK.le
  refine ⟨?_, ?_⟩
  · exact_mod_cast (show 0 ≤ -(linearColumnRow k reduced column row : ℝ) by rw [heq]; nlinarith only [hb₀])
  · exact_mod_cast (show -(linearColumnRow k reduced column row : ℝ) ≤ (k : ℝ) ^ 2 * (bound : ℝ) by
      rw [heq]
      nlinarith only [hb₁])

end FLatticePaper.GeneralK
