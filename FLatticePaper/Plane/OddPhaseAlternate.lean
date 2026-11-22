import FLatticePaper.Plane.GlobalOdometers
import FLatticePaper.Construction.AlternateIdentification
import FLatticePaper.Construction.NearOneBaseCases

/-! The alternate identification at every birth, with the odd alternate's target of w2 (`alternateOddTarget`).

At an odd birth the constructor's odd alternate is `alternateOddTarget w x = quarterTurnField (alternateTarget (swap w))
(x - alternateOddChart w) + (alternateOddSlope w).1 x₁ + (alternateOddSlope w).2 x₂`, which is the quarter-turned alternate
translated by the chart and with an integer affine term. Its properties follow from the alternate's (`planeAlternate`):

* the translation by the chart and the affine term keep the period structure up to integer constants (`T·M v` is integral on
  the span, since `M·kernel = 0` and `M·transverse = (n, -d)`);
* the Laplacian, superharmonicity and recurrence transfer when the chart is even (`EvenSite`, a named hypothesis at odd births);
* the growth is preserved (the translated remainder is `o(|y|²)`, the linear terms are `O(|y|)`);
* the difference from the standard field is not integer affine: its kernel increment is odd. -/

namespace FLatticePaper.OddPhaseAlternate

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Induction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard FLatticePaper.Tiles.DeckCoverage FLatticePaper.Tiles.StandardBoundary
open FLatticePaper.Tiles.StandardClause FLatticePaper.GlobalOdometers FLatticePaper.BaseAlternate

/-! ### Linear algebra of the chart translation -/

theorem siteVector_sub' (a b : Site) : siteVector (a - b) = siteVector a - siteVector b := by
  funext i
  fin_cases i <;> simp [siteVector]

theorem siteVector_zero' : siteVector (0 : Site) = 0 := by
  funext i
  fin_cases i <;> simp [siteVector]

theorem matrixQuadratic_sub (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hsym : ∀ x y : Site, dotProduct (siteVector x) (M.mulVec (siteVector y)) =
      dotProduct (siteVector y) (M.mulVec (siteVector x)))
    (y T : Site) :
    matrixQuadratic M (y - T) =
      matrixQuadratic M y - dotProduct (siteVector y) (M.mulVec (siteVector T)) + matrixQuadratic M T := by
  unfold matrixQuadratic
  rw [siteVector_sub', Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct, hsym T y]
  ring

theorem squaredSize_nonneg' (x : Site) : 0 ≤ squaredSize x := by
  unfold squaredSize
  positivity

/-! ### The deck of an odd fraction -/

theorem odd_kernel_eq (f : Fraction) (hodd : f.Odd) : f.modifiedDeck.kernel = (2 * f.den, 2 * f.num) := by
  rw [modifiedDeck_kernel_of_odd hodd]
  rfl

theorem transverse_eq (f : Fraction) : f.modifiedDeck.transverse = (f.num - f.den, f.num + f.den) := by
  rw [modifiedDeck_transverse]
  rfl

theorem combine_odd_eq (f : Fraction) (hodd : f.Odd) (i j : ℤ) :
    f.modifiedDeck.combine i j =
      (i * (2 * f.den) + j * (f.num - f.den), i * (2 * f.num) + j * (f.num + f.den)) := by
  simp only [PeriodDeck.combine, odd_kernel_eq f hodd, transverse_eq f]

theorem kernel_eq_combine (f : Fraction) : f.modifiedDeck.kernel = f.modifiedDeck.combine 1 0 := by
  ext <;> simp [PeriodDeck.combine]

/-- `T·M·(combine i j) = j (n T₁ - d T₂)`: `M·kernel = 0` and `M·transverse = (n, -d)`. -/
theorem dot_mulVec_combine (f : Fraction) (hodd : f.Odd) (hpos : 0 < f.periodDenominator) (T : Site) (i j : ℤ) :
    dotProduct (siteVector T) (f.matrix.mulVec (siteVector (f.modifiedDeck.combine i j))) =
      (j : ℝ) * ((f.num : ℝ) * (T.1 : ℝ) - (f.den : ℝ) * (T.2 : ℝ)) := by
  have hP : (f.den : ℝ) ^ 2 + 2 * (f.den : ℝ) * (f.num : ℝ) - (f.num : ℝ) ^ 2 ≠ 0 := by
    have hh : (0 : ℤ) < f.den ^ 2 + 2 * f.den * f.num - f.num ^ 2 := by
      unfold Fraction.periodDenominator at hpos
      exact hpos
    have h : (0 : ℝ) < ((f.den ^ 2 + 2 * f.den * f.num - f.num ^ 2 : ℤ) : ℝ) := by
      exact_mod_cast hh
    push_cast at h
    exact h.ne'
  rw [combine_odd_eq f hodd]
  have hPdef : (f.periodDenominator : ℝ) = (f.den : ℝ) ^ 2 + 2 * (f.den : ℝ) * (f.num : ℝ) - (f.num : ℝ) ^ 2 := by
    unfold Fraction.periodDenominator
    push_cast
    ring
  simp only [Fraction.matrix, Matrix.mulVec, dotProduct, siteVector, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hPdef]
  push_cast
  linear_combination ((j : ℝ) * ((f.num : ℝ) * (T.1 : ℝ) - (f.den : ℝ) * (T.2 : ℝ))) * mul_inv_cancel₀ hP

/-! ### Laplacians, superharmonicity and recurrence -/

theorem laplacian_affine' (a b : ℤ) (x : Site) : laplacian (fun y : Site => a * y.1 + b * y.2) x = 0 := by
  have h := incoming_add x
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [Prod.fst_add, Prod.snd_add] at h1 h2
  simp only [laplacian]
  linear_combination a * h1 + b * h2

theorem laplacian_affineShift (F : Field) {T : Site} (hT : EvenSite T) (a b : ℤ) (x : Site) :
    laplacian (fun y : Site => F (y - T) + (a * y.1 + b * y.2)) x = laplacian F (x - T) := by
  have hneg : EvenSite (-T) := by
    unfold EvenSite at hT ⊢
    simp only [Prod.fst_neg, Prod.snd_neg]
    omega
  have h1 := laplacian_translate_of_even F x (-T) hneg
  have hsplit : laplacian (fun y : Site => F (y - T) + (a * y.1 + b * y.2)) x =
      laplacian (fun y : Site => F (y + -T)) x + laplacian (fun y : Site => a * y.1 + b * y.2) x := by
    simp only [laplacian, sub_eq_add_neg]
    ring
  rw [hsplit, laplacian_affine', add_zero, h1, sub_eq_add_neg]

theorem superharmonic_affineShift {F : Field} (hF : Superharmonic F) {T : Site} (hT : EvenSite T) (a b : ℤ) :
    Superharmonic (fun y : Site => F (y - T) + (a * y.1 + b * y.2)) := by
  intro x
  rw [laplacian_affineShift F hT a b x]
  exact hF _

theorem binary_affineShift {F : Field} (hF : ∀ x, laplacian F x = -1 ∨ laplacian F x = 0) {T : Site}
    (hT : EvenSite T) (a b : ℤ) (x : Site) :
    laplacian (fun y : Site => F (y - T) + (a * y.1 + b * y.2)) x = -1 ∨
      laplacian (fun y : Site => F (y - T) + (a * y.1 + b * y.2)) x = 0 := by
  rw [laplacian_affineShift F hT a b x]
  exact hF _

/-- Adding a harmonic function preserves recurrence: the difference against a superharmonic competitor shifts. -/
theorem recurrent_add_harmonic {F L : Field} (hF : Recurrent F) (hL : ∀ x, laplacian L x = 0) :
    Recurrent (fun y => F y + L y) := by
  intro C hC sites h
  have hCL : Superharmonic (fun y => C y - L y) := by
    intro x
    have h1 := hC x
    have h2 := hL x
    simp only [laplacian] at h1 h2 ⊢
    linarith
  have key := hF (fun y => C y - L y) hCL sites h
  have e1 : maxDifference (fun y => F y + L y) C sites h.1 =
      maxDifference F (fun y => C y - L y) sites h.1 := by
    unfold maxDifference
    congr 2
    funext s
    ring
  have e2 : maxDifference (fun y => F y + L y) C (incomingBoundaryFinset sites)
      (incomingBoundaryFinset_nonempty h.1) =
      maxDifference F (fun y => C y - L y) (incomingBoundaryFinset sites)
        (incomingBoundaryFinset_nonempty h.1) := by
    unfold maxDifference
    congr 2
    funext s
    ring
  rw [e1, e2]
  exact key

theorem recurrent_affineShift {F : Field} (hF : Recurrent F) {T : Site} (hT : EvenSite T) (a b : ℤ) :
    Recurrent (fun y : Site => F (y - T) + (a * y.1 + b * y.2)) :=
  recurrent_add_harmonic (recurrent_translate_even hT hF) (laplacian_affine' a b)

/-! ### The growth of the translated affine field -/

/-- The linear error: `K m + |q| ≤ (ε/4) s` for large `s`, where `m² ≤ 2s`. -/
theorem linear_le_of_sq (K q m s ε : ℝ) (hK : 0 ≤ K) (hm : 0 ≤ m) (hm2 : m ^ 2 ≤ 2 * s) (hε : 0 < ε)
    (hS : 1 + (64 * K ^ 2 + 32 * q ^ 2) / ε ^ 2 ≤ s) (hs : 1 ≤ s) :
    K * m + |q| ≤ (ε / 4) * s := by
  have hs0 : 0 ≤ s := by linarith
  have hq2 : |q| ^ 2 = q ^ 2 := sq_abs q
  have hX : (K * m + |q|) ^ 2 ≤ 4 * K ^ 2 * s + 2 * q ^ 2 := by
    have h1 : (K * m + |q|) ^ 2 ≤ 2 * (K * m) ^ 2 + 2 * |q| ^ 2 := by
      nlinarith [sq_nonneg (K * m - |q|)]
    have h2 : (K * m) ^ 2 = K ^ 2 * m ^ 2 := by ring
    have h3 : K ^ 2 * m ^ 2 ≤ K ^ 2 * (2 * s) := mul_le_mul_of_nonneg_left hm2 (sq_nonneg K)
    rw [h2, hq2] at h1
    nlinarith
  have hε2 : 0 < ε ^ 2 := by positivity
  have hA : 64 * K ^ 2 + 32 * q ^ 2 ≤ (s - 1) * ε ^ 2 := by
    have hdiv : (64 * K ^ 2 + 32 * q ^ 2) / ε ^ 2 ≤ s - 1 := by linarith
    exact (div_le_iff₀ hε2).mp hdiv
  have hB : 4 * K ^ 2 + 2 * q ^ 2 ≤ (ε ^ 2 / 16) * s := by nlinarith
  have hkey : 4 * K ^ 2 * s + 2 * q ^ 2 ≤ ((ε / 4) * s) ^ 2 := by
    have hq0 : 0 ≤ q ^ 2 := sq_nonneg q
    have hB' := mul_le_mul_of_nonneg_right hB hs0
    have hq' := mul_nonneg hq0 (by linarith : (0 : ℝ) ≤ s - 1)
    nlinarith
  have hnonneg : 0 ≤ K * m + |q| := by
    have := abs_nonneg q
    positivity
  have hY : 0 ≤ (ε / 4) * s := by positivity
  nlinarith

/-- The translated remainder: `|F(y-T) - Q(y)|`-type bound for `s(y-T) ≥ r²`. -/
theorem squaredSize_sub_le (y T : Site) : squaredSize (y - T) ≤ 2 * squaredSize y + 2 * squaredSize T := by
  unfold squaredSize
  simp only [Prod.fst_sub, Prod.snd_sub]
  push_cast
  nlinarith [sq_nonneg ((y.1 : ℝ) + T.1), sq_nonneg ((y.2 : ℝ) + T.2)]

theorem squaredSize_le_sub (y T : Site) : squaredSize y ≤ 2 * squaredSize (y - T) + 2 * squaredSize T := by
  unfold squaredSize
  simp only [Prod.fst_sub, Prod.snd_sub]
  push_cast
  nlinarith [sq_nonneg ((y.1 : ℝ) - T.1 - T.1), sq_nonneg ((y.2 : ℝ) - T.2 - T.2)]

theorem abs_sum_sq_le (y : Site) : (|(y.1 : ℝ)| + |(y.2 : ℝ)|) ^ 2 ≤ 2 * squaredSize y := by
  unfold squaredSize
  have h1 := sq_abs (y.1 : ℝ)
  have h2 := sq_abs (y.2 : ℝ)
  nlinarith [sq_nonneg (|(y.1 : ℝ)| - |(y.2 : ℝ)|)]

/-- The affine part `p₁ y₁ + p₂ y₂ + q` is `≤ (ε/4) s(y)` for large `s(y)`. -/
theorem affine_part_le (p1 p2 q ε : ℝ) (hε : 0 < ε) (y : Site)
    (hS : 1 + (64 * (|p1| + |p2|) ^ 2 + 32 * q ^ 2) / ε ^ 2 ≤ squaredSize y) (hs : 1 ≤ squaredSize y) :
    |p1 * (y.1 : ℝ) + p2 * (y.2 : ℝ) + q| ≤ (ε / 4) * squaredSize y := by
  have hK : 0 ≤ |p1| + |p2| := by positivity
  have hm : 0 ≤ |(y.1 : ℝ)| + |(y.2 : ℝ)| := by positivity
  have hterm : |p1 * (y.1 : ℝ) + p2 * (y.2 : ℝ)| ≤ (|p1| + |p2|) * (|(y.1 : ℝ)| + |(y.2 : ℝ)|) := by
    calc |p1 * (y.1 : ℝ) + p2 * (y.2 : ℝ)| ≤ |p1 * (y.1 : ℝ)| + |p2 * (y.2 : ℝ)| := abs_add_le _ _
      _ = |p1| * |(y.1 : ℝ)| + |p2| * |(y.2 : ℝ)| := by rw [abs_mul, abs_mul]
      _ ≤ (|p1| + |p2|) * (|(y.1 : ℝ)| + |(y.2 : ℝ)|) := by
          have := abs_nonneg (y.1 : ℝ)
          have := abs_nonneg (y.2 : ℝ)
          have := abs_nonneg p1
          have := abs_nonneg p2
          nlinarith
  have hlin := linear_le_of_sq (|p1| + |p2|) q (|(y.1 : ℝ)| + |(y.2 : ℝ)|) (squaredSize y) ε hK hm
    (abs_sum_sq_le y) hε hS hs
  have htri : |p1 * (y.1 : ℝ) + p2 * (y.2 : ℝ) + q| ≤ |p1 * (y.1 : ℝ) + p2 * (y.2 : ℝ)| + |q| :=
    abs_add_le _ _
  linarith

theorem hasQuadraticGrowth_affineShift {F : Field} {M : Matrix (Fin 2) (Fin 2) ℝ}
    (hsym : ∀ x y : Site, dotProduct (siteVector x) (M.mulVec (siteVector y)) =
      dotProduct (siteVector y) (M.mulVec (siteVector x)))
    (hF : HasQuadraticGrowth F M) (T : Site) (a b : ℤ) :
    HasQuadraticGrowth (fun y : Site => F (y - T) + (a * y.1 + b * y.2)) M := by
  intro ε hε
  obtain ⟨r, hr, hbound⟩ := hF (ε / 4) (by linarith)
  obtain ⟨c1, hc1⟩ : ∃ c : ℝ, c = (M.mulVec (siteVector T)) 0 := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ c : ℝ, c = (M.mulVec (siteVector T)) 1 := ⟨_, rfl⟩
  obtain ⟨p1, hp1⟩ : ∃ p : ℝ, p = (a : ℝ) - c1 := ⟨_, rfl⟩
  obtain ⟨p2, hp2⟩ : ∃ p : ℝ, p = (b : ℝ) - c2 := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = matrixQuadratic M T := ⟨_, rfl⟩
  obtain ⟨sT, hsT⟩ : ∃ s : ℝ, s = squaredSize T := ⟨_, rfl⟩
  have hsT0 : 0 ≤ sT := by rw [hsT]; exact squaredSize_nonneg' T
  obtain ⟨S1, hS1⟩ : ∃ S : ℝ, S = 1 + (64 * (|p1| + |p2|) ^ 2 + 32 * q ^ 2) / ε ^ 2 := ⟨_, rfl⟩
  have hS1ge : 1 ≤ S1 := by
    rw [hS1]
    have : 0 ≤ (64 * (|p1| + |p2|) ^ 2 + 32 * q ^ 2) / ε ^ 2 := by positivity
    linarith
  refine ⟨1 + (2 * r ^ 2 + 4 * sT + S1), by positivity, fun y hy => ?_⟩
  have hy' : (1 + (2 * r ^ 2 + 4 * sT + S1)) ≤ (1 + (2 * r ^ 2 + 4 * sT + S1)) ^ 2 := by
    have : 0 ≤ 2 * r ^ 2 + 4 * sT + S1 := by positivity
    nlinarith
  have hs : 2 * r ^ 2 + 4 * sT + S1 ≤ squaredSize y := by linarith
  -- the translated point is large enough for the remainder
  have hzr : r ^ 2 ≤ squaredSize (y - T) := by
    have h1 := squaredSize_le_sub y T
    rw [← hsT] at h1
    nlinarith [sq_nonneg r]
  have hR := hbound (y - T) hzr
  -- the identity of the target and the affine part
  have hdot : dotProduct (siteVector y) (M.mulVec (siteVector T)) = (y.1 : ℝ) * c1 + (y.2 : ℝ) * c2 := by
    rw [hc1, hc2]
    simp only [dotProduct, Fin.sum_univ_two, siteVector, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hid : (((F (y - T) + (a * y.1 + b * y.2) : ℤ)) : ℝ) - matrixQuadratic M y =
      ((F (y - T) : ℤ) : ℝ) - matrixQuadratic M (y - T) + (p1 * (y.1 : ℝ) + p2 * (y.2 : ℝ) + q) := by
    rw [matrixQuadratic_sub M hsym y T, hdot, hp1, hp2, hq]
    push_cast
    ring
  have hsq0 : 0 ≤ r ^ 2 := sq_nonneg r
  have hterm := affine_part_le p1 p2 q ε hε y (by rw [← hS1]; linarith) (by linarith)
  -- the remainder at the translated point, with `4 s(T) ≤ s(y)`
  have hz1 := squaredSize_sub_le y T
  rw [← hsT] at hz1
  have h4 : 4 * sT ≤ squaredSize y := by linarith
  have hRz : |(F (y - T) : ℝ) - matrixQuadratic M (y - T)| ≤ (ε / 4) * squaredSize (y - T) := hR
  have hRb : |(F (y - T) : ℝ) - matrixQuadratic M (y - T)| ≤ (5 * ε / 8) * squaredSize y := by
    have hsz : (ε / 4) * squaredSize (y - T) ≤ (ε / 4) * (2 * squaredSize y + 2 * sT) :=
      mul_le_mul_of_nonneg_left hz1 (by linarith)
    have hsT' : (ε / 2) * sT ≤ (ε / 8) * squaredSize y := by nlinarith
    nlinarith
  rw [hid]
  calc |((F (y - T) : ℤ) : ℝ) - matrixQuadratic M (y - T) + (p1 * (y.1 : ℝ) + p2 * (y.2 : ℝ) + q)|
      ≤ |((F (y - T) : ℤ) : ℝ) - matrixQuadratic M (y - T)| + |p1 * (y.1 : ℝ) + p2 * (y.2 : ℝ) + q| :=
        abs_add_le _ _
    _ ≤ (5 * ε / 8) * squaredSize y + (ε / 4) * squaredSize y := by linarith
    _ ≤ ε * squaredSize y := by nlinarith [squaredSize_nonneg' y]

/-! ### The odd-phase target of w2, as the translated affine field -/

/-- The odd alternate target of w2 is the quarter-turned alternate translated by the chart and with the transverse slope. -/
noncomputable def oddAlternate (w : Word) (T : Site) (a b : ℤ) : Field :=
  fun y => planeAlternate w .odd (y - T) + (a * y.1 + b * y.2)

theorem alternateTarget_swap_eq (w : Word) :
    alternateTarget (w.map Digit.swapTwoThree) = (frameAt (swapW w)).alternate (standardField (swapW w)) := rfl

theorem alternateOddTarget_eq (w : Word) :
    alternateOddTarget w = oddAlternate w (alternateOddChart w) (alternateOddSlope w).1 (alternateOddSlope w).2 := by
  funext x
  rfl

/-- The periodicity of the translated affine field: the constant of `T·M·v` is an integer on the span. -/
theorem satisfiesPeriodicity_affineShift {fr : Fraction} {Q : Field} (hodd : fr.Odd)
    (hpos : 0 < fr.periodDenominator) (hQ : SatisfiesPeriodicity fr Q) (T : Site) (a b : ℤ) :
    SatisfiesPeriodicity fr (fun y : Site => Q (y - T) + (a * y.1 + b * y.2)) := by
  intro v hv
  obtain ⟨c, hc⟩ := hQ v hv
  obtain ⟨i, j, rfl⟩ := hv
  refine ⟨c + (a * (fr.modifiedDeck.combine i j).1 + b * (fr.modifiedDeck.combine i j).2) -
    j * (fr.num * T.1 - fr.den * T.2), fun x => ?_⟩
  have e : x + fr.modifiedDeck.combine i j - T = (x - T) + fr.modifiedDeck.combine i j := by abel
  have h1 := hc (x - T)
  have h2 : dotProduct (siteVector (x - T)) (fr.matrix.mulVec (siteVector (fr.modifiedDeck.combine i j))) =
      dotProduct (siteVector x) (fr.matrix.mulVec (siteVector (fr.modifiedDeck.combine i j))) -
        dotProduct (siteVector T) (fr.matrix.mulVec (siteVector (fr.modifiedDeck.combine i j))) := by
    rw [siteVector_sub', sub_dotProduct]
  have h3 := dot_mulVec_combine fr hodd hpos T i j
  simp only [e, Prod.fst_add, Prod.snd_add]
  push_cast
  rw [h1, h2, h3]
  ring

/-- The odd alternate target differs from the standard field by an increment `-1 + (slope · kernel)` on the kernel: the
translation cancels against the standard field's periodicity (`M·kernel = 0`), and the quarter-turn difference drops by `1`
(`odd_alt_increments`). -/
theorem oddAlternate_increment (w : Word) {fr : Fraction} (hfr : (parentsAt w).current .odd = fr)
    (hpk : (frameAt (swapW w)).Packet (standardField (swapW w))) (hA : AlternateFactsWord (swapW w))
    (hGSP : SatisfiesPeriodicity fr (planeTarget w .odd)) (hodd : fr.Odd) (hpos : 0 < fr.periodDenominator)
    (T : Site) (a b : ℤ) (x : Site) :
    (oddAlternate w T a b (x + fr.modifiedDeck.kernel) - planeTarget w .odd (x + fr.modifiedDeck.kernel)) -
        (oddAlternate w T a b x - planeTarget w .odd x) =
      -1 + (a * (fr.modifiedDeck.kernel).1 + b * (fr.modifiedDeck.kernel).2) := by
  have hz := odd_alt_increments w hfr hpk hA (x - T)
  obtain ⟨cG, hcG⟩ := hGSP fr.modifiedDeck.kernel ⟨1, 0, by ext <;> simp [PeriodDeck.combine]⟩
  have hkC : dotProduct (siteVector T) (fr.matrix.mulVec (siteVector fr.modifiedDeck.kernel)) = 0 := by
    rw [kernel_eq_combine fr, dot_mulVec_combine fr hodd hpos T 1 0]
    ring
  have h2 : dotProduct (siteVector (x - T)) (fr.matrix.mulVec (siteVector fr.modifiedDeck.kernel)) =
      dotProduct (siteVector x) (fr.matrix.mulVec (siteVector fr.modifiedDeck.kernel)) -
        dotProduct (siteVector T) (fr.matrix.mulVec (siteVector fr.modifiedDeck.kernel)) := by
    rw [siteVector_sub', sub_dotProduct]
  have hU1 := hcG (x - T)
  have hU2 := hcG x
  have e : x + fr.modifiedDeck.kernel - T = (x - T) + fr.modifiedDeck.kernel := by abel
  have hzR : ((planeAlternate w .odd ((x - T) + fr.modifiedDeck.kernel) : ℤ) : ℝ) -
      ((planeTarget w .odd ((x - T) + fr.modifiedDeck.kernel) : ℤ) : ℝ) =
      ((planeAlternate w .odd (x - T) : ℤ) : ℝ) - ((planeTarget w .odd (x - T) : ℤ) : ℝ) - 1 := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hz
    push_cast at this
    linarith
  apply Int.cast_injective (α := ℝ)
  simp only [oddAlternate, e, Prod.fst_add, Prod.snd_add]
  push_cast
  linarith [hzR, hU1, hU2, h2, hkC]

/-- An odd kernel increment: the difference of the odd target and the standard field has odd increment on the kernel, so it
is not integer affine (an integer affine function has even increment on `(2 e₁, 2 e₂)`). -/
theorem not_integerAffine_of_odd_increment (D : Field) (e1 e2 : ℤ)
    (h : ∀ x : Site, (D (x + (2 * e1, 2 * e2)) - D x) % 2 = 1) : ¬ IntegerAffine D := by
  rintro ⟨g, c, hg⟩
  have h0 := h 0
  have key : D (0 + (2 * e1, 2 * e2)) - D 0 = 2 * (g.1 * e1 + g.2 * e2) := by
    rw [hg (0 + (2 * e1, 2 * e2)), hg 0]
    simp only [zero_add, Prod.fst_zero, Prod.snd_zero]
    ring
  rw [key] at h0
  generalize g.1 * e1 + g.2 * e2 = X at h0
  omega

/-- The alternate target at every birth: the even `planeAlternate`, and the odd target of w2 (`alternateOddTarget`). -/
noncomputable def altTarget (w : Word) : Parity → Field
  | .even => planeAlternate w .even
  | .odd => alternateOddTarget w

/-- The facts of the odd target of w2 at an odd birth, from the facts of `planeAlternate`. -/
theorem odd_altTarget_facts (w : Word) {fr : Fraction} (hfr : (parentsAt w).current .odd = fr) (hint : fr.Interior)
    (hpk : ∀ u : Word, (frameAt u).Packet (standardField u)) (hAll : ∀ u : Word, AlternateFactsWord u)
    (hGSP : SatisfiesPeriodicity fr (planeTarget w .odd)) (hchart : EvenSite (alternateOddChart w)) :
    SatisfiesPeriodicity fr (alternateOddTarget w) ∧ HasQuadraticGrowth (alternateOddTarget w) fr.matrix ∧
      (∀ x, laplacian (alternateOddTarget w) x = -1 ∨ laplacian (alternateOddTarget w) x = 0) ∧
      Superharmonic (alternateOddTarget w) ∧ Recurrent (alternateOddTarget w) ∧
      ¬ IntegerAffine (fun x => alternateOddTarget w x - planeTarget w .odd x) ∧
      (∀ x, (alternateOddTarget w (x + fr.modifiedDeck.kernel) - planeTarget w .odd (x + fr.modifiedDeck.kernel)) -
          (alternateOddTarget w x - planeTarget w .odd x) =
        -1 + ((alternateOddSlope w).1 * (fr.modifiedDeck.kernel).1 + (alternateOddSlope w).2 * (fr.modifiedDeck.kernel).2)) := by
  obtain ⟨hQ1, hQ2, hQ3, hQ4, hQ5, -⟩ := alternate_facts_birth w .odd hfr hint hAll
  have hodd : fr.Odd := by
    rw [← hfr]
    exact (parentsAt_valid w).current_odd_parity
  have hpos : 0 < fr.periodDenominator := Fraction.periodDenominator_pos hint.inUnitInterval
  have hfun : alternateOddTarget w = oddAlternate w (alternateOddChart w) (alternateOddSlope w).1
      (alternateOddSlope w).2 := alternateOddTarget_eq w
  have hinc := fun x => oddAlternate_increment w hfr (hpk (swapW w)) (hAll (swapW w)) hGSP hodd hpos
    (alternateOddChart w) (alternateOddSlope w).1 (alternateOddSlope w).2 x
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfun]
    exact satisfiesPeriodicity_affineShift hodd hpos hQ1 _ _ _
  · rw [hfun]
    exact hasQuadraticGrowth_affineShift (matrix_dot_comm fr) hQ2 _ _ _
  · rw [hfun]
    exact fun x => binary_affineShift hQ3 hchart _ _ x
  · rw [hfun]
    exact superharmonic_affineShift hQ4 hchart _ _
  · rw [hfun]
    exact recurrent_affineShift hQ5 hchart _ _
  · have hD : (fun x => alternateOddTarget w x - planeTarget w .odd x) =
        (fun x => oddAlternate w (alternateOddChart w) (alternateOddSlope w).1 (alternateOddSlope w).2 x -
          planeTarget w .odd x) := by
      funext x
      rw [hfun]
    rw [hD]
    apply not_integerAffine_of_odd_increment _ fr.den fr.num
    intro x
    have hk := odd_kernel_eq fr hodd
    have h := hinc x
    rw [hk] at h
    dsimp only at h ⊢
    rw [h]
    have hY : (alternateOddSlope w).1 * (2 * fr.den) + (alternateOddSlope w).2 * (2 * fr.num) =
        2 * ((alternateOddSlope w).1 * fr.den + (alternateOddSlope w).2 * fr.num) := by ring
    rw [hY]
    generalize (alternateOddSlope w).1 * fr.den + (alternateOddSlope w).2 * fr.num = Z
    omega
  · intro x
    rw [hfun]
    exact hinc x

/-- The alternate facts of every word: the base words `3^k` from the explicit base alternate (`hbaseThree`), the powers of two
and the proper words from their star estimates. -/
theorem altFactsWord_all
    (hstar : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word → StarZoneInputs word)
    (hsheet : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word → SheetLocalInputs word)
    (harc : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word →
      VArcInputs (frameAt word) (standardField word))
    (hodd : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word →
      OddBlackNoRise (standardField word) (frameAt word).shortShift)
    (hbulk : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word →
      S3NoFortInputs (frameAt word) (standardField word))
    (hbaseTwoId : ∀ k : ℕ, ∃ S : Field, (BaseMask.ladderOddAlt.raw (2 * (k : ℤ) + 4)).Agrees S 0 ∧
      HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S (-1) (ladderOddAltConstantV (2 * (k : ℤ) + 4)) ∧
      ∃ c : ℤ, ∀ x, (frameAt (List.replicate (k + 1) Digit.two)).alternate
        (standardField (List.replicate (k + 1) Digit.two)) x = rotateLadderAltField (2 * (k : ℤ) + 4) S x + c)
    (hbaseThree : ∀ k : ℕ, ∃ c : ℤ, ∀ x, (frameAt (List.replicate k Digit.three)).alternate
        (standardField (List.replicate k Digit.three)) x =
      stairEvenAltField (2 * (k : ℤ) + 3) (standardField (List.replicate k Digit.three)) x + c) :
    ∀ u : Word, AlternateFactsWord u := by
  have hpk : ∀ u : Word, (frameAt u).Packet (standardField u) := packet_all hstar hsheet
  intro u
  by_cases hall : ∀ x ∈ u, x = Digit.three
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, u = List.replicate k Digit.three :=
      ⟨u.length, List.eq_replicate_iff.mpr ⟨rfl, hall⟩⟩
    exact reciprocal_alternateFactsWord k (hbaseThree k)
  · have hproper : ∃ x ∈ u, x ≠ Digit.three := by
      by_contra h
      push Not at h
      exact hall h
    by_cases htw : IsTwoPow u
    · obtain ⟨k, rfl⟩ := htw
      exact twos_alternateFactsWord k (hbaseTwoId k)
    · exact alternateFactsWord_of_star u (hpk u) (starEstimates_of_inputs u hproper (hpk (conjWord u)) (hpk u)
        (hstar u hproper htw) (hsheet u hproper htw) (harc u hproper htw) (hodd u hproper htw)
        (hbulk u hproper htw))

/-- `lemma:global_odometers` for both odometers at a birth `(w, p)` of `fraction = n/d`: the standard one (`global_odometers`),
and the alternate `ĝ = altTarget w p` with its identification of the constructor's alternate tile (`htileAlt`) and the
coverage of that tile (`hcovAlt`). The alternate is the even `planeAlternate` at even births and the odd target of w2
(`alternateOddTarget`) at odd births; the latter needs the chart `alternateOddChart` to be even (`hchart`), which the Laplacian
transfer uses. The distinctness in the fixed coordinates of `eq:periodicity`: the difference is not integer affine, the
Laplacians differ somewhere, and the explicit increments hold (the transverse increment `-1` at even births; at odd births the
kernel increment `-1 + slope·kernel`, whose affine term is the transverse slope of the odd parent).

The base words need no star estimates: at `3^k` the alternate is the explicit base alternate `stairEvenAltField` up to a
constant (`hbaseThree`), and at `2^k` the rotated explicit alternate `rotateLadderAltField` up to a constant (`hbaseTwoId`,
with its base field `S`). Both are plane identities between the midpoint and the explicit base fields, which the base-case
proposition of the paper states (the unique recurrent extension of the base alternate tile).
-/
theorem global_odometers_pair {fraction : Fraction} (hint : fraction.Interior) {w : Word} {p : Parity}
    (hbirth : (parentsAt w).current p = fraction)
    (hstar : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word → StarZoneInputs word)
    (hsheet : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word → SheetLocalInputs word)
    (harc : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word →
      VArcInputs (frameAt word) (standardField word))
    (hodd : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word →
      OddBlackNoRise (standardField word) (frameAt word).shortShift)
    (hbulk : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word →
      S3NoFortInputs (frameAt word) (standardField word))
    (hbaseTwoId : ∀ k : ℕ, ∃ S : Field, (BaseMask.ladderOddAlt.raw (2 * (k : ℤ) + 4)).Agrees S 0 ∧
      HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S (-1) (ladderOddAltConstantV (2 * (k : ℤ) + 4)) ∧
      ∃ c : ℤ, ∀ x, (frameAt (List.replicate (k + 1) Digit.two)).alternate
        (standardField (List.replicate (k + 1) Digit.two)) x = rotateLadderAltField (2 * (k : ℤ) + 4) S x + c)
    (hbaseThree : ∀ k : ℕ, ∃ c : ℤ, ∀ x, (frameAt (List.replicate k Digit.three)).alternate
        (standardField (List.replicate k Digit.three)) x =
      stairEvenAltField (2 * (k : ℤ) + 3) (standardField (List.replicate k Digit.three)) x + c)
    (bdOdd : ∀ v : Word, StandardBoundaryOdd v) (bdEven : ∀ v : Word, StandardBoundaryEven v)
    (simpleOdd : ∀ v : Word, IsSimpleTile (cellTileOf (oddTile v)))
    (simpleEven : ∀ v : Word, IsSimpleTile (cellTileOf (evenTile v)))
    (tile : HeightTile Site)
    (htile : ∃ gauge : ℤ, tile.Agrees (planeTarget w p) gauge)
    (hsites : (p = .even ∧ tile.sites = evenTile w) ∨ (p = .odd ∧ tile.sites = oddTile w) ∨
      fraction.modifiedDeck.Covers tile.sites)
    (hchart : p = .odd → EvenSite (alternateOddChart w))
    (altTile : HeightTile Site) (htileAlt : ∃ gauge : ℤ, altTile.Agrees (altTarget w p) gauge)
    (hcovAlt : fraction.modifiedDeck.Covers altTile.sites) :
    ((∃ c : ℤ, ∀ (x : Site) (hx : x ∈ tile.sites), planeTarget w p x = tile.height ⟨x, hx⟩ + c) ∧
      SatisfiesPeriodicity fraction (planeTarget w p) ∧
      HasQuadraticGrowth (planeTarget w p) fraction.matrix ∧
      (∃ b : Fin 2 → ℝ, ∀ v ∈ fraction.modifiedDeck.span,
        Function.Periodic (fun x : Site => ((planeTarget w p x : ℤ) : ℝ) - matrixQuadratic fraction.matrix x -
          dotProduct b (siteVector x)) v) ∧
      (∀ x, laplacian (planeTarget w p) x = -1 ∨ laplacian (planeTarget w p) x = 0) ∧
      Superharmonic (planeTarget w p) ∧ Recurrent (planeTarget w p) ∧
      (∀ H : Field, SatisfiesPeriodicity fraction H →
        (∀ v ∈ fraction.modifiedDeck.span, H v - H 0 = planeTarget w p v - planeTarget w p 0) →
        ∀ gH : ℤ, tile.Agrees H gH → ∃ c : ℤ, ∀ x, H x = planeTarget w p x + c)) ∧
    (∃ c : ℤ, ∀ (x : Site) (hx : x ∈ altTile.sites), altTarget w p x = altTile.height ⟨x, hx⟩ + c) ∧
    SatisfiesPeriodicity fraction (altTarget w p) ∧
    HasQuadraticGrowth (altTarget w p) fraction.matrix ∧
    (∃ b : Fin 2 → ℝ, ∀ v ∈ fraction.modifiedDeck.span,
      Function.Periodic (fun x : Site => ((altTarget w p x : ℤ) : ℝ) - matrixQuadratic fraction.matrix x -
        dotProduct b (siteVector x)) v) ∧
    (∀ x, laplacian (altTarget w p) x = -1 ∨ laplacian (altTarget w p) x = 0) ∧
    Superharmonic (altTarget w p) ∧ Recurrent (altTarget w p) ∧
    (∀ H : Field, SatisfiesPeriodicity fraction H →
      (∀ v ∈ fraction.modifiedDeck.span, H v - H 0 = altTarget w p v - altTarget w p 0) →
      ∀ gH : ℤ, altTile.Agrees H gH → ∃ c : ℤ, ∀ x, H x = altTarget w p x + c) ∧
    ¬ IntegerAffine (fun x => altTarget w p x - planeTarget w p x) ∧
    (∃ x, laplacian (altTarget w p) x ≠ laplacian (planeTarget w p) x) ∧
    ((p = .even →
        (∀ x : Site, altTarget w p (x + fraction.modifiedDeck.transverse) -
          planeTarget w p (x + fraction.modifiedDeck.transverse) =
          altTarget w p x - planeTarget w p x - 1) ∧
        (∀ x : Site, altTarget w p (x + fraction.modifiedDeck.kernel) -
          planeTarget w p (x + fraction.modifiedDeck.kernel) = altTarget w p x - planeTarget w p x)) ∧
      (p = .odd → ∀ x : Site, (altTarget w p (x + fraction.modifiedDeck.kernel) -
          planeTarget w p (x + fraction.modifiedDeck.kernel)) - (altTarget w p x - planeTarget w p x) =
          -1 + ((alternateOddSlope w).1 * (fraction.modifiedDeck.kernel).1 +
            (alternateOddSlope w).2 * (fraction.modifiedDeck.kernel).2))) := by
  have hpk : ∀ u : Word, (frameAt u).Packet (standardField u) := packet_all hstar hsheet
  have hAll : ∀ u : Word, AlternateFactsWord u :=
    altFactsWord_all hstar hsheet harc hodd hbulk hbaseTwoId hbaseThree
  have hstd := global_odometers hint hbirth hstar hsheet harc hodd hbulk bdOdd bdEven simpleOdd simpleEven
    tile htile hsites
  have hstdSP : SatisfiesPeriodicity fraction (planeTarget w p) := hstd.2.1
  obtain ⟨gauge, hag⟩ := htileAlt
  have hfacts : SatisfiesPeriodicity fraction (altTarget w p) ∧
      HasQuadraticGrowth (altTarget w p) fraction.matrix ∧
      (∀ x, laplacian (altTarget w p) x = -1 ∨ laplacian (altTarget w p) x = 0) ∧
      Superharmonic (altTarget w p) ∧ Recurrent (altTarget w p) ∧
      ¬ IntegerAffine (fun x => altTarget w p x - planeTarget w p x) ∧
      ((p = .even →
          (∀ x : Site, altTarget w p (x + fraction.modifiedDeck.transverse) -
            planeTarget w p (x + fraction.modifiedDeck.transverse) =
            altTarget w p x - planeTarget w p x - 1) ∧
          (∀ x : Site, altTarget w p (x + fraction.modifiedDeck.kernel) -
            planeTarget w p (x + fraction.modifiedDeck.kernel) = altTarget w p x - planeTarget w p x)) ∧
        (p = .odd → ∀ x : Site, (altTarget w p (x + fraction.modifiedDeck.kernel) -
            planeTarget w p (x + fraction.modifiedDeck.kernel)) - (altTarget w p x - planeTarget w p x) =
            -1 + ((alternateOddSlope w).1 * (fraction.modifiedDeck.kernel).1 +
              (alternateOddSlope w).2 * (fraction.modifiedDeck.kernel).2))) := by
    cases p with
    | even =>
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := alternate_facts_birth w .even hbirth hint hAll
      exact ⟨h1, h2, h3, h4, h5, h6, fun _ => even_alt_increments w hbirth (hpk w) (hAll w),
        fun h => Parity.noConfusion h⟩
    | odd =>
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
        odd_altTarget_facts w hbirth hint hpk hAll hstdSP (hchart rfl)
      exact ⟨h1, h2, h3, h4, h5, h6, fun h => Parity.noConfusion h, fun _ => h7⟩
  obtain ⟨hAS, hAGr, hAB, hAS2, hAR, hAN, hInc⟩ := hfacts
  refine ⟨hstd, ⟨-gauge, fun x hx => ?_⟩, hAS, hAGr, exists_tilt hint.inUnitInterval hAS, hAB, hAS2, hAR,
    fun H hH hcc gH hHt => ⟨gauge - gH, fun x => unique_of_covers altTile hcovAlt hAS hH hcc hag hHt x⟩,
    hAN, laplacian_differs hint.inUnitInterval hAS hstdSP hAN, hInc⟩
  have := hag ⟨x, hx⟩
  linarith


end FLatticePaper.OddPhaseAlternate
