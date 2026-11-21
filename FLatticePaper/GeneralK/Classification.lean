import FLatticePaper.GeneralK.ColumnUpperObstacle
import FLatticePaper.GeneralK.Parabolic
import FLatticePaper.GeneralK.RationalReference

namespace FLatticePaper.GeneralK

open Farey

/-- The rational period realization obligation in the column-classification
source, for every permitted full-rank deck of physical shifts. -/
def RationalPeriodRealization (k : ℤ) : Prop :=
  ∀ (a b c : ℚ), symmetricMatrix (a : ℝ) (b : ℝ) (c : ℝ) ∈ growthSet k →
    ∀ deck : PeriodDeck, deck.det ≠ 0 → (∀ step ∈ deck.span, Retained k step) →
      HasIntegerAction a b c deck.kernel → HasIntegerAction a b c deck.transverse →
      ∃ (height : Field) (tiltX tiltY : ℚ) (remainder : Site → ℝ) (bound : ℝ),
        Superharmonic k height ∧
        (∀ site, (height site : ℝ) = matrixQuadratic (symmetricMatrix (a : ℝ) (b : ℝ) (c : ℝ)) site +
          ((tiltX : ℝ) * (site.1 : ℝ) + (tiltY : ℝ) * (site.2 : ℝ)) + remainder site) ∧
        (∀ site, |remainder site| ≤ bound) ∧
        ∀ step ∈ deck.span, Function.Periodic remainder step

/-- The explicit rational endpoints, viewed in the real matrix space. -/
noncomputable def cycleEndpoint (k : ℤ) (hk : 2 ≤ k) (b c : ℚ) : ℝ :=
  ((⟨k, hk, b, c⟩ : ColumnSlice).cyclePeak : ℝ)

private theorem rationalColumnUpper {k : ℤ} (hk : 2 ≤ k) (hrealize : RationalPeriodRealization k)
    (a b c : ℚ) (hadmit : symmetricMatrix (a : ℝ) (b : ℝ) (c : ℝ) ∈ growthSet k)
    (hfirst : (startingColumnEntry k b c hk : ℝ) ≤ (a : ℝ)) : (a : ℝ) ≤ cycleEndpoint k hk b c := by
  let slice : ColumnSlice := ⟨k, hk, b, c⟩
  let horizontal := k * (a.den : ℤ) * (b.den : ℤ)
  let vertical := k * (slice.length : ℤ)
  let deck : PeriodDeck := ⟨(horizontal, 0), (0, vertical)⟩
  have hk' : 0 < k := by omega
  have hh : 0 < horizontal := mul_pos (mul_pos hk' (by exact_mod_cast a.den_pos)) (by exact_mod_cast b.den_pos)
  have hv : 0 < vertical := mul_pos hk' (by exact_mod_cast slice.length_pos)
  have hdet : deck.det ≠ 0 := by
    have h : deck.det = horizontal * vertical := by simp [deck, PeriodDeck.det]
    exact h ▸ (mul_pos hh hv).ne'
  have hphase : ∀ step ∈ deck.span, Retained k step := by
    rintro _ ⟨i, j, rfl⟩
    change (i * horizontal + j * 0 + (i * 0 + j * vertical)) % k = 0
    apply Int.dvd_iff_emod_eq_zero.mp
    refine ⟨i * (a.den : ℤ) * (b.den : ℤ) + j * (slice.length : ℤ), ?_⟩
    dsimp [horizontal, vertical]
    ring
  have hkernel : HasIntegerAction a b c deck.kernel := by
    have hden (q : ℚ) : (q.den : ℚ) * q = q.num := by
      calc
        _ = (q.den : ℚ) * ((q.num : ℚ) / q.den) := congrArg ((q.den : ℚ) * ·) q.num_div_den.symm
        _ = _ := mul_div_cancel₀ _ (show (q.den : ℚ) ≠ 0 by exact_mod_cast q.den_pos.ne')
    refine ⟨k * (a.num : ℤ) * (b.den : ℤ), k * (a.den : ℤ) * b.num, ?_, ?_⟩
    · simp only [deck, horizontal, Int.cast_zero, mul_zero, add_zero, Int.cast_mul, Int.cast_natCast]
      linear_combination (k : ℚ) * (b.den : ℚ) * hden a
    · simp only [deck, horizontal, Int.cast_zero, mul_zero, add_zero, Int.cast_mul, Int.cast_natCast]
      linear_combination (k : ℚ) * (a.den : ℚ) * hden b
  have htrans : HasIntegerAction a b c deck.transverse := by
    obtain ⟨⟨bn, hb⟩, ⟨cn, hc⟩⟩ := columnLength_spec k b c
    refine ⟨bn, cn, ?_, ?_⟩
    · simp only [deck, vertical, Int.cast_zero, mul_zero, zero_add, Int.cast_mul, Int.cast_natCast]
      change (k : ℚ) * (slice.length : ℚ) * b = _ at hb
      linear_combination hb
    · simp only [deck, vertical, Int.cast_zero, mul_zero, zero_add, Int.cast_mul, Int.cast_natCast]
      change (k : ℚ) * (slice.length : ℚ) * c = _ at hc
      linear_combination hc
  obtain ⟨height, tiltX, tiltY, remainder, bound, hsuper, hheight, hbound, hperiod⟩ :=
    hrealize a b c hadmit deck hdet hphase hkernel htrans
  have hspan : (0, vertical) ∈ deck.span := ⟨0, 1, by simp [deck, PeriodDeck.combine]⟩
  have hrem : remainder (0, vertical) = remainder 0 := by
    simpa only [zero_add] using hperiod (0, vertical) hspan 0
  have hconstant : (c : ℝ) * ((k : ℝ) * (slice.length : ℝ)) ^ 2 / 2 +
      (tiltY : ℝ) * ((k : ℝ) * (slice.length : ℝ)) = ((height (0, vertical) - height 0 : ℤ) : ℝ) := by
    have h₁ := hheight (0, vertical)
    have h₀ := hheight (0, 0)
    change (height (0, 0) : ℝ) = _ at h₀
    have heq : (0, 0) = (0 : Site) := rfl
    rw [← heq] at hrem ⊢
    simp only [matrixQuadratic_symmetricMatrix, Int.cast_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
      mul_zero, zero_add, zero_div, add_zero, vertical, Int.cast_mul, Int.cast_natCast] at h₀ h₁ ⊢
    rw [Int.cast_sub]
    linarith only [h₀, h₁, hrem]
  have herror (site : Site) : |(height site : ℝ) - matrixQuadratic (symmetricMatrix (a : ℝ) (b : ℝ) (c : ℝ)) site -
      ((tiltX : ℝ) * (site.1 : ℝ) + (tiltY : ℝ) * (site.2 : ℝ))| ≤ bound := by
    rw [hheight]
    convert hbound site using 2
    ring
  exact slice.le_cyclePeak_of_transverse_representative hfirst hsuper _ hconstant herror

/-- Rational period realization supplies the exact rational column slice,
including arbitrary real first diagonal entries. -/
theorem rationalSlice_iff_le_cycleEndpoint {k : ℤ} (hk : 2 ≤ k) (hrealize : RationalPeriodRealization k)
    (b c : ℚ) (a : ℝ) : symmetricMatrix a (b : ℝ) (c : ℝ) ∈ growthSet k ↔ a ≤ cycleEndpoint k hk b c := by
  let slice : ColumnSlice := ⟨k, hk, b, c⟩
  constructor
  · intro h
    have hbase := startingColumnEntry_mem_growthSet hk b c
    have hlow : (slice.a₀ : ℝ) ≤ cycleEndpoint k hk b c := by
      have hcast : (((slice.a₀ : ℤ) : ℚ) : ℝ) = (slice.a₀ : ℝ) := Rat.cast_intCast _
      have hseed : symmetricMatrix (((slice.a₀ : ℤ) : ℚ) : ℝ) (b : ℝ) (c : ℝ) ∈ growthSet k := by
        rw [hcast]
        exact hbase
      have h := rationalColumnUpper hk hrealize (slice.a₀ : ℚ) b c hseed (by rw [hcast]; exact le_rfl)
      rwa [hcast] at h
    by_contra! hbad
    obtain ⟨q, hqlo, hqhi⟩ := exists_rat_btwn hbad
    have hqa : (slice.a₀ : ℝ) ≤ (q : ℝ) := hlow.trans hqlo.le
    have hsub := sub_mem_growthSet_of_posSemidef hk h (posSemidef_topEntry (sub_nonneg.mpr hqhi.le))
    have heq : symmetricMatrix a (b : ℝ) (c : ℝ) - symmetricMatrix (a - (q : ℝ)) 0 0 =
        symmetricMatrix (q : ℝ) (b : ℝ) (c : ℝ) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [symmetricMatrix]
    rw [heq] at hsub
    exact hqlo.not_ge (rationalColumnUpper hk hrealize q b c hsub hqa)
  · intro ha
    exact slice.mem_growthSet_of_le_cyclePeak ha

/-- The real parabolic classification, reduced to the rational period lemma. -/
theorem mem_growthSet_iff_le_cycleParabolic {k : ℤ} (hk : 2 ≤ k) (hrealize : RationalPeriodRealization k)
    (a b c : ℝ) : symmetricMatrix a b c ∈ growthSet k ↔ a ≤ sInf (parabolicValues (cycleEndpoint k hk) b c) :=
  mem_growthSet_iff_le_sInf_parabolicValues hk (rationalSlice_iff_le_cycleEndpoint hk hrealize) a b c

/-- The closure of the explicit downward cones classifies every real matrix
once rational period realization is available. -/
theorem growthSet_eq_closure_cycleCones {k : ℤ} (hk : 2 ≤ k) (hrealize : RationalPeriodRealization k) :
    growthSet k = closure (rationalConeUnion (cycleEndpoint k hk)) :=
  growthSet_eq_closure_rationalConeUnion hk (rationalSlice_iff_le_cycleEndpoint hk hrealize)

end FLatticePaper.GeneralK
