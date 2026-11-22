import FLatticePaper.MainTheorems
import FLatticePaper.Construction.PeriodExtension

/-! `lemma:global_odometers` for the standard odometers (global_recurrence.tex 56-101).

The finite standard tile odometer is a `HeightTile`. It extends to the plane standard field `standardField w` of its
birth word `w` (the even child `n/d`): the field agrees with the tile up to one constant, has the generator identities
of `eq:periodicity`, and `g - x^T M x / 2 - b^T x` is `L'(n,d)`-periodic. The extension is unique among the fields with
the same generator identities, by deck coverage of the tile (`PeriodDeck.Covers`). The Laplacians take values in
`{-1, 0}` and the field is recurrent. -/

namespace FLatticePaper

open Farey Construction Induction

/-! ### The integer period law -/

theorem combine_succ_kernel (fraction : Fraction) (i j : ℤ) :
    fraction.modifiedDeck.combine (i + 1) j = fraction.modifiedDeck.combine i j + fraction.modifiedDeck.kernel := by
  apply Prod.ext <;> simp [PeriodDeck.combine] <;> ring

theorem combine_succ_transverse (fraction : Fraction) (i j : ℤ) :
    fraction.modifiedDeck.combine i (j + 1) = fraction.modifiedDeck.combine i j + fraction.modifiedDeck.transverse := by
  apply Prod.ext <;> simp [PeriodDeck.combine] <;> ring

theorem combine_zero_zero (fraction : Fraction) : fraction.modifiedDeck.combine 0 0 = 0 := by
  apply Prod.ext <;> simp [PeriodDeck.combine]

theorem grade_add (fraction : Fraction) (s t : Site) :
    fraction.transverseGrade (s + t) = fraction.transverseGrade s + fraction.transverseGrade t := by
  simp only [Fraction.transverseGrade, Prod.fst_add, Prod.snd_add]
  ring

theorem grade_combine_kernel (fraction : Fraction) (i : ℤ) :
    fraction.transverseGrade (fraction.modifiedDeck.combine i 0) = 0 := by
  simp only [Fraction.transverseGrade, PeriodDeck.combine, Fraction.modifiedDeck, Fraction.unmodifiedDeck]
  ring

theorem grade_combine_transverse (fraction : Fraction) (j : ℤ) :
    fraction.transverseGrade (fraction.modifiedDeck.combine 0 j) = fraction.periodDenominator * j := by
  simp only [Fraction.transverseGrade, PeriodDeck.combine, Fraction.modifiedDeck, Fraction.unmodifiedDeck,
    Fraction.periodDenominator]
  ring

/-- The kernel identity iterated: `F (s + i·kernel) = F s + i·c_U`. -/
theorem kernel_law (fraction : Fraction) (F : Field) (cU : ℤ)
    (hK : ∀ s, F (s + fraction.modifiedDeck.kernel) = F s + cU) :
    ∀ (i : ℤ) (s : Site), F (s + fraction.modifiedDeck.combine i 0) = F s + i * cU := by
  intro i
  induction i using Int.induction_on with
  | zero =>
    intro s
    simp [combine_zero_zero]
  | succ n ih =>
    intro s
    rw [combine_succ_kernel, ← add_assoc, hK, ih]
    ring
  | pred n ih =>
    intro s
    have e : fraction.modifiedDeck.combine (-(n : ℤ)) 0 =
        fraction.modifiedDeck.combine (-(n : ℤ) - 1) 0 + fraction.modifiedDeck.kernel := by
      have := combine_succ_kernel fraction (-(n : ℤ) - 1) 0
      rw [show -(n : ℤ) - 1 + 1 = -(n : ℤ) by ring] at this
      exact this
    have e2 : s + fraction.modifiedDeck.combine (-(n : ℤ)) 0 =
        (s + fraction.modifiedDeck.combine (-(n : ℤ) - 1) 0) + fraction.modifiedDeck.kernel := by
      rw [e]
      abel
    have h1 := ih s
    rw [e2, hK] at h1
    linear_combination h1

/-- The transverse identity iterated, with the quadratic correction `pd * C(j)`. -/
theorem transverse_law (fraction : Fraction) (F : Field) (cV : ℤ)
    (hT : ∀ s, F (s + fraction.modifiedDeck.transverse) = F s - fraction.transverseGrade s + cV) :
    ∀ (j : ℤ) (s : Site), F (s + fraction.modifiedDeck.combine 0 j) =
      F s + j * (cV - fraction.transverseGrade s) - fraction.periodDenominator * chooseTwo j := by
  intro j
  induction j using Int.induction_on with
  | zero =>
    intro s
    simp [combine_zero_zero, chooseTwo]
  | succ n ih =>
    intro s
    have hc : chooseTwo ((n : ℤ) + 1) = chooseTwo (n : ℤ) + n := by
      rw [chooseTwo_add]
      simp [chooseTwo]
    rw [combine_succ_transverse, ← add_assoc, hT, ih s, grade_add, grade_combine_transverse, hc]
    ring
  | pred n ih =>
    intro s
    have e : fraction.modifiedDeck.combine 0 (-(n : ℤ)) =
        fraction.modifiedDeck.combine 0 (-(n : ℤ) - 1) + fraction.modifiedDeck.transverse := by
      have := combine_succ_transverse fraction 0 (-(n : ℤ) - 1)
      rw [show -(n : ℤ) - 1 + 1 = -(n : ℤ) by ring] at this
      exact this
    have e2 : s + fraction.modifiedDeck.combine 0 (-(n : ℤ)) =
        (s + fraction.modifiedDeck.combine 0 (-(n : ℤ) - 1)) + fraction.modifiedDeck.transverse := by
      rw [e]
      abel
    have hc : chooseTwo (-(n : ℤ)) = chooseTwo (-(n : ℤ) - 1) + (-(n : ℤ) - 1) := by
      have := chooseTwo_add (-(n : ℤ) - 1) 1
      rw [show -(n : ℤ) - 1 + 1 = -(n : ℤ) by ring] at this
      rw [this]
      simp [chooseTwo]
    have hg : fraction.transverseGrade (s + fraction.modifiedDeck.combine 0 (-(n : ℤ) - 1)) =
        fraction.transverseGrade s + fraction.periodDenominator * (-(n : ℤ) - 1) := by
      rw [grade_add, grade_combine_transverse]
    have h1 := ih s
    rw [e2, hT, hc] at h1
    rw [hg] at h1
    linear_combination h1

/-- The integer period law: `F (s + combine i j) = F s + periodIncrement`. -/
theorem periodIncrement_law (fraction : Fraction) (F : Field) (cU cV : ℤ)
    (hper : HasGeneratorPeriods fraction F cU cV) (s : Site) (i j : ℤ) :
    F (s + fraction.modifiedDeck.combine i j) = F s + periodIncrement fraction cU cV s i j := by
  obtain ⟨hK, hT⟩ := hper
  have hsplit : fraction.modifiedDeck.combine i j =
      fraction.modifiedDeck.combine i 0 + fraction.modifiedDeck.combine 0 j := by
    apply Prod.ext <;> simp [PeriodDeck.combine]
  rw [hsplit, ← add_assoc, transverse_law fraction F cV hT j, kernel_law fraction F cU hK i s,
    grade_add, grade_combine_kernel]
  unfold periodIncrement
  ring

/-- A tile that agrees with a field having the generator identities respects the periods. -/
theorem respects_of_agrees {fraction : Fraction} {F : Field} {cU cV : ℤ}
    (hper : HasGeneratorPeriods fraction F cU cV) {tile : HeightTile Site} {gauge : ℤ}
    (hag : tile.Agrees F gauge) : tile.RespectsPeriods fraction cU cV := by
  intro first second i j hsec
  rw [hag second, hag first, hsec, periodIncrement_law fraction F cU cV hper first.val i j]
  ring

/-! ### Uniqueness of the extension, by deck coverage -/

/-- Two fields with the same generator identities that agree with the tile differ by a constant: deck coverage
reaches every site from a site of the tile, and both fields shift by the same period increment. -/
theorem agrees_unique_of_covers {fraction : Fraction} (tile : HeightTile Site)
    (hcover : fraction.modifiedDeck.Covers tile.sites) {F H : Field} {cU cV : ℤ}
    (hF : HasGeneratorPeriods fraction F cU cV) (hH : HasGeneratorPeriods fraction H cU cV)
    {gF gH : ℤ} (hFt : tile.Agrees F gF) (hHt : tile.Agrees H gH) :
    ∀ x, H x = F x + (gF - gH) := by
  intro x
  obtain ⟨r, hr, hspan⟩ := hcover x
  obtain ⟨i, j, hij⟩ := hspan
  have hx : x = r + fraction.modifiedDeck.combine i j := by
    rw [← hij]
    abel
  have hF' : tile.height ⟨r, hr⟩ = F r + gF := hFt ⟨r, hr⟩
  have hH' : tile.height ⟨r, hr⟩ = H r + gH := hHt ⟨r, hr⟩
  rw [hx, periodIncrement_law fraction H cU cV hH r i j, periodIncrement_law fraction F cU cV hF r i j]
  linarith

/-! ### The tilt, the packets and the recurrence -/

/-- The real linear tilt of the generator constants, as the vector `b` of `g - xᵀMx/2 - bᵀx`. -/
noncomputable def tiltVector (fraction : Fraction) (cU cV : ℤ) : Fin 2 → ℝ :=
  ![periodicTilt fraction cU cV (1, 0), periodicTilt fraction cU cV (0, 1)]

theorem periodicTilt_linear (fraction : Fraction) (cU cV : ℤ) (x : Site) :
    periodicTilt fraction cU cV x =
      periodicTilt fraction cU cV (1, 0) * (x.1 : ℝ) + periodicTilt fraction cU cV (0, 1) * (x.2 : ℝ) := by
  unfold periodicTilt
  simp [PeriodDeck.kernelNumerator, PeriodDeck.transverseNumerator]
  ring

theorem tiltVector_dot (fraction : Fraction) (cU cV : ℤ) (x : Site) :
    dotProduct (tiltVector fraction cU cV) (siteVector x) = periodicTilt fraction cU cV x := by
  rw [periodicTilt_linear]
  simp [tiltVector, dotProduct, Fin.sum_univ_two, siteVector]

/-- The packet at every word: the reciprocal packet at the pure words, the proper packet otherwise. -/
theorem packet_of_word (w : Word) (hP : (∃ x ∈ w, x ≠ Digit.three) → (frameAt w).Packet (standardField w)) :
    (frameAt w).Packet (standardField w) := by
  by_cases hall : ∀ x ∈ w, x = Digit.three
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, w = List.replicate k Digit.three :=
      ⟨w.length, List.eq_replicate_iff.mpr ⟨rfl, hall⟩⟩
    exact reciprocal_packet k
  · have hex : ∃ x ∈ w, x ≠ Digit.three := by
      by_contra h
      push Not at h
      exact hall h
    exact hP hex

/-- The reciprocal staircase field of the pure words is recurrent (its burning rank). -/
theorem recurrent_reciprocal (k : ℕ) : Recurrent (reciprocalField k) := by
  obtain ⟨hagree, hper⟩ := reciprocalField_spec k
  obtain ⟨_, _, _, hrank⟩ := stairEven_exists_burningRank (stairEven_valid_reciprocal k) hagree hper
  exact hrank.recurrent

/-- The standard field is recurrent at every word: the reciprocal case by its burning rank, the proper case from the
star estimates (the constrained burning rank of `StarEstimates`). -/
theorem recurrent_of_word (w : Word) (hR : (∃ x ∈ w, x ≠ Digit.three) → StarEstimates w) :
    Recurrent (standardField w) := by
  by_cases hall : ∀ x ∈ w, x = Digit.three
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, w = List.replicate k Digit.three :=
      ⟨w.length, List.eq_replicate_iff.mpr ⟨rfl, hall⟩⟩
    rw [standardField_threes]
    exact recurrent_reciprocal k
  · have hex : ∃ x ∈ w, x ≠ Digit.three := by
      by_contra h
      push Not at h
      exact hall h
    obtain ⟨_, _, _, hrank⟩ := hR hex
    exact hrank.toIsBurningRank.recurrent

/-! ### `lemma:global_odometers`, for the standard odometer of the even child `n/d` -/

/-- `lemma:global_odometers` for the standard odometer at the birth word `w` of `n/d`. The finite standard tile odometer
(a height tile, identified with the plane standard field up to a constant) extends to `g = standardField w`, which has
the generator identities of `eq:periodicity` and the growth of `eq:periodicity_growth` with the real tilt `b`; the
Laplacians are binary and the field is recurrent; and the extension is unique given deck coverage of the tile.

The inputs that remain named are: the packet of the proper word (`hP`, the open inputs of the plane induction, via
`packet_standardField`), the star estimates of the proper word (`hR`, the rank of the step), the identification of the
finite tile with the plane standard field (`htile`, `ordinaryStandard_identifies_register`), and the deck coverage of
the tile (`hcover`, part III of the proof). -/
theorem global_odometers_standard {fraction : Fraction} (hint : fraction.Interior) (w : Word)
    (hw : (parentsAt w).current .even = fraction)
    (hP : (∃ x ∈ w, x ≠ Digit.three) → (frameAt w).Packet (standardField w))
    (hR : (∃ x ∈ w, x ≠ Digit.three) → StarEstimates w)
    (tile : HeightTile Site)
    (htile : ∃ gauge : ℤ, tile.Agrees (standardField w) gauge)
    (hcover : fraction.modifiedDeck.Covers tile.sites) :
    ∃ g : Field,
      (∃ c : ℤ, ∀ (x : Site) (hx : x ∈ tile.sites), g x = tile.height ⟨x, hx⟩ + c) ∧
      (∃ cU cV : ℤ, HasGeneratorPeriods fraction g cU cV) ∧
      SatisfiesPeriodicity fraction g ∧
      HasQuadraticGrowth g fraction.matrix ∧
      (∀ x, laplacian g x = -1 ∨ laplacian g x = 0) ∧
      (∃ b : Fin 2 → ℝ, ∀ v ∈ fraction.modifiedDeck.span,
        Function.Periodic (fun x : Site => ((g x : ℤ) : ℝ) - matrixQuadratic fraction.matrix x -
          dotProduct b (siteVector x)) v) ∧
      Recurrent g ∧
      (∀ H : Field, HasGeneratorPeriods fraction H (frameAt w).coherentConstantU (frameAt w).coherentConstantV →
        ∀ gH : ℤ, tile.Agrees H gH → ∃ c : ℤ, ∀ x, H x = g x + c) := by
  have hpk := packet_of_word w hP
  have hper : HasGeneratorPeriods fraction (standardField w) (frameAt w).coherentConstantU
      (frameAt w).coherentConstantV := by
    rw [← hw]
    exact hpk.periods
  have hinterval : fraction.InUnitInterval := hint.inUnitInterval
  obtain ⟨gauge, hag⟩ := htile
  refine ⟨standardField w, ⟨-gauge, fun x hx => ?_⟩, ⟨_, _, hper⟩,
    satisfiesPeriodicity_of_generatorPeriods hinterval hper, generator_periods_growth hinterval hper,
    hpk.binary, ⟨tiltVector fraction (frameAt w).coherentConstantU (frameAt w).coherentConstantV, fun v hv => ?_⟩,
    recurrent_of_word w hR, fun H hH gH hHt => ⟨gauge - gH, agrees_unique_of_covers tile hcover hper hH hag hHt⟩⟩
  · have := hag ⟨x, hx⟩
    linarith
  · have hPer := periodRemainder_periodic hinterval hper hv
    have hfun : (fun x : Site => ((standardField w x : ℤ) : ℝ) - matrixQuadratic fraction.matrix x -
        dotProduct (tiltVector fraction (frameAt w).coherentConstantU (frameAt w).coherentConstantV)
          (siteVector x)) =
        periodRemainder fraction (standardField w) (frameAt w).coherentConstantU
          (frameAt w).coherentConstantV := by
      funext x
      unfold periodRemainder
      rw [tiltVector_dot]
    rw [hfun]
    exact hPer

end FLatticePaper
