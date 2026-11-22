import FLatticePaper.MainTheorems
import FLatticePaper.Construction.PeriodExtension
import FLatticePaper.Construction.PlaneIdentification
import FLatticePaper.Construction.LadderRank
import FLatticePaper.Construction.LadderRotation
import FLatticePaper.Construction.StaircaseRank
import FLatticePaper.Plane.Induction.OddStep
import FLatticePaper.Plane.Induction.TwosPeriods
import FLatticePaper.Plane.Induction.TwosInduction
import FLatticePaper.Plane.Induction.Packet
import FLatticePaper.Plane.Induction.StandardField
import FLatticePaper.Plane.Induction.OpenLocal
import FLatticePaper.Tiles.DeckCoverage
import FLatticePaper.Tiles.SeamSymm
import FLatticePaper.Plane.HarmonicConstant
import FLatticePaper.Plane.Induction.AlternateFacts

/-! `lemma:global_odometers` for the standard odometers (global_recurrence.tex 56-101), for every birth parity.

For a birth `(w, p)` of a reduced `0 < n/d < 1`, the standard tile odometer is the plane field `planeTarget w p`: the even
standard field `standardField w`, or the quarter turn `quarterTurnField (standardField (swapW w))` at odd births.

* The field agrees with the finite tile up to one constant (named: `htile`).
* It satisfies `eq:periodicity`, has quadratic growth, binary Laplacians and is recurrent.
* `g - xᵀMx/2 - bᵀx` is `L'(n,d)`-periodic for a real `b` (the tilt is fixed by the two deck generators).
* The extension is unique among fields with the same period constants on `L'(n,d)`, by deck coverage of the tile.

Deck coverage comes from `DeckCoverage` when the tile is the standard tile of `w`; the corrected outputs stay named.
At the powers of two the fields are unconditional (`twos_standardField_eq_rotate` with the ladder rotation); at the other
proper words the star estimates come from the open local inputs of the headline. -/

namespace FLatticePaper.GlobalOdometers

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Induction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.StandardClause
open FLatticePaper.Tiles.DeckCoverage FLatticePaper.Tiles.SeamSymm

/-! ### Shifts and the tilt from the two deck generators -/

theorem siteVector_add (x v : Site) : siteVector (x + v) = siteVector x + siteVector v := by
  funext i
  fin_cases i <;> simp [siteVector]

theorem siteVector_zero : siteVector (0 : Site) = 0 := by
  funext i
  fin_cases i <;> simp [siteVector]

/-- The matrix `M(n,d)` is symmetric as a bilinear form. -/
theorem matrix_dot_comm (fraction : Fraction) (x y : Site) :
    dotProduct (siteVector x) (fraction.matrix.mulVec (siteVector y)) =
      dotProduct (siteVector y) (fraction.matrix.mulVec (siteVector x)) := by
  simp [Fraction.matrix, Matrix.mulVec, dotProduct, siteVector, Fin.sum_univ_two]
  ring

theorem matrixQuadratic_add (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hsym : ∀ x y : Site, dotProduct (siteVector x) (M.mulVec (siteVector y)) = dotProduct (siteVector y) (M.mulVec (siteVector x)))
    (x v : Site) :
    matrixQuadratic M (x + v) =
      matrixQuadratic M x + dotProduct (siteVector x) (M.mulVec (siteVector v)) + matrixQuadratic M v := by
  unfold matrixQuadratic
  rw [siteVector_add, Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, hsym v x]
  ring

/-- The shift identity of `eq:periodicity`, with the constant read off at the origin. -/
theorem sat_shift (M : Matrix (Fin 2) (Fin 2) ℝ) (deck : PeriodDeck) {H : Field}
    (hH : ∀ v ∈ deck.span, ∃ c : ℤ, ∀ x : Site,
      ((H (x + v) : ℤ) : ℝ) = ((H x : ℤ) : ℝ) + dotProduct (siteVector x) (M.mulVec (siteVector v)) + (c : ℝ))
    {v : Site} (hv : v ∈ deck.span) (x : Site) :
    ((H (x + v) : ℤ) : ℝ) = ((H x : ℤ) : ℝ) + dotProduct (siteVector x) (M.mulVec (siteVector v)) +
      (((H v - H 0 : ℤ)) : ℝ) := by
  obtain ⟨c, hc⟩ := hH v hv
  have h0 := hc 0
  rw [zero_add, siteVector_zero, zero_dotProduct] at h0
  rw [hc x]
  push_cast at h0 ⊢
  linarith

/-- A function with the two generator periods is periodic on the whole span. -/
theorem periodic_span {ψ : Site → ℝ} {deck : PeriodDeck} (hK : Function.Periodic ψ deck.kernel)
    (hT : Function.Periodic ψ deck.transverse) : ∀ v ∈ deck.span, Function.Periodic ψ v := by
  have hmul : ∀ P : Site, Function.Periodic ψ P → ∀ n : ℤ, ∀ y : Site,
      ψ (y + (n * P.1, n * P.2)) = ψ y := by
    intro P hP n
    induction n using Int.induction_on with
    | zero => intro y; simp only [zero_mul, Prod.mk_zero_zero, add_zero]
    | succ n ih =>
      intro y
      have e : y + ((n + 1) * P.1, (n + 1) * P.2) = (y + (n * P.1, n * P.2)) + P := by
        ext <;> simp <;> ring
      rw [e, hP, ih]
    | pred n ih =>
      intro y
      have h := hP (y + ((-n - 1) * P.1, (-n - 1) * P.2))
      have e : y + ((-n - 1) * P.1, (-n - 1) * P.2) + P = y + (-n * P.1, -n * P.2) := by
        ext <;> simp <;> ring
      rw [e, ih] at h
      exact h.symm
  rintro v ⟨i, j, rfl⟩ x
  have e : x + deck.combine i j =
      (x + (i * deck.kernel.1, i * deck.kernel.2)) + (j * deck.transverse.1, j * deck.transverse.2) := by
    ext <;> simp [PeriodDeck.combine] <;> ring
  rw [e, hmul deck.transverse hT j, hmul deck.kernel hK i]

/-- The tilt `b` of a field with the shift identities: `b·K` and `b·T` are the periodic remainders of the generators. -/
theorem exists_tilt_of_deck (M : Matrix (Fin 2) (Fin 2) ℝ) (deck : PeriodDeck) (hdet : 0 < deck.det)
    (hsym : ∀ x y : Site, dotProduct (siteVector x) (M.mulVec (siteVector y)) = dotProduct (siteVector y) (M.mulVec (siteVector x)))
    {H : Field}
    (hH : ∀ v ∈ deck.span, ∃ c : ℤ, ∀ x : Site,
      ((H (x + v) : ℤ) : ℝ) = ((H x : ℤ) : ℝ) + dotProduct (siteVector x) (M.mulVec (siteVector v)) + (c : ℝ)) :
    ∃ b : Fin 2 → ℝ, ∀ v ∈ deck.span,
      Function.Periodic (fun x : Site => ((H x : ℤ) : ℝ) - matrixQuadratic M x - dotProduct b (siteVector x)) v := by
  have hK : deck.kernel ∈ deck.span := ⟨1, 0, by ext <;> simp [PeriodDeck.combine]⟩
  have hT : deck.transverse ∈ deck.span := ⟨0, 1, by ext <;> simp [PeriodDeck.combine]⟩
  obtain ⟨D, hDdef⟩ : ∃ r : ℝ, r = (deck.kernel.1 : ℝ) * (deck.transverse.2 : ℝ) -
      (deck.kernel.2 : ℝ) * (deck.transverse.1 : ℝ) := ⟨_, rfl⟩
  have hD : D ≠ 0 := by
    rw [hDdef]
    have h : (0 : ℤ) < deck.kernel.1 * deck.transverse.2 - deck.kernel.2 * deck.transverse.1 := hdet
    have h' : ((deck.kernel.1 * deck.transverse.2 - deck.kernel.2 * deck.transverse.1 : ℤ) : ℝ) ≠ 0 := by
      exact_mod_cast h.ne'
    push_cast at h'
    exact h'
  obtain ⟨φK, hφK⟩ : ∃ r : ℝ, r = ((H deck.kernel - H 0 : ℤ) : ℝ) - matrixQuadratic M deck.kernel := ⟨_, rfl⟩
  obtain ⟨φT, hφT⟩ : ∃ r : ℝ, r = ((H deck.transverse - H 0 : ℤ) : ℝ) - matrixQuadratic M deck.transverse :=
    ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin 2 → ℝ, b =
      ![(φK * (deck.transverse.2 : ℝ) - (deck.kernel.2 : ℝ) * φT) / D,
        ((deck.kernel.1 : ℝ) * φT - φK * (deck.transverse.1 : ℝ)) / D] := ⟨_, rfl⟩
  have hbK : dotProduct b (siteVector deck.kernel) = φK := by
    rw [hb]
    simp only [dotProduct, Fin.sum_univ_two, siteVector, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    rw [hDdef]
    ring
  have hbT : dotProduct b (siteVector deck.transverse) = φT := by
    rw [hb]
    simp only [dotProduct, Fin.sum_univ_two, siteVector, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    rw [hDdef]
    ring
  refine ⟨b, ?_⟩
  have hKper : Function.Periodic
      (fun x : Site => ((H x : ℤ) : ℝ) - matrixQuadratic M x - dotProduct b (siteVector x)) deck.kernel := by
    intro y
    dsimp only
    rw [sat_shift M deck hH hK y, matrixQuadratic_add M hsym y deck.kernel, siteVector_add, dotProduct_add,
      hbK, hφK]
    ring
  have hTper : Function.Periodic
      (fun x : Site => ((H x : ℤ) : ℝ) - matrixQuadratic M x - dotProduct b (siteVector x)) deck.transverse := by
    intro y
    dsimp only
    rw [sat_shift M deck hH hT y, matrixQuadratic_add M hsym y deck.transverse, siteVector_add, dotProduct_add,
      hbT, hφT]
    ring
  exact periodic_span hKper hTper

/-- The tilt of a field satisfying `eq:periodicity` on `L'(n,d)`. -/
theorem exists_tilt {fraction : Fraction} (hinterval : fraction.InUnitInterval) {H : Field}
    (hH : SatisfiesPeriodicity fraction H) :
    ∃ b : Fin 2 → ℝ, ∀ v ∈ fraction.modifiedDeck.span,
      Function.Periodic (fun x : Site => ((H x : ℤ) : ℝ) - matrixQuadratic fraction.matrix x - dotProduct b (siteVector x)) v :=
  exists_tilt_of_deck fraction.matrix fraction.modifiedDeck (Fraction.det_modifiedDeck_pos hinterval)
    (matrix_dot_comm fraction) hH

/-! ### Uniqueness of the extension, by deck coverage -/

/-- Two fields with `eq:periodicity` and the same period constants that agree with the tile differ by a constant. The
deck coverage of the tile reaches every site from a site of the tile. -/
theorem unique_of_covers {fraction : Fraction} (tile : HeightTile Site)
    (hcov : fraction.modifiedDeck.Covers tile.sites) {F H : Field}
    (hF : SatisfiesPeriodicity fraction F) (hH : SatisfiesPeriodicity fraction H)
    (hcc : ∀ v ∈ fraction.modifiedDeck.span, H v - H 0 = F v - F 0) {gF gH : ℤ}
    (hFt : tile.Agrees F gF) (hHt : tile.Agrees H gH) : ∀ x, H x = F x + (gF - gH) := by
  have step : ∀ r : Site, ∀ v ∈ fraction.modifiedDeck.span, H (r + v) - F (r + v) = H r - F r := by
    intro r v hv
    have h1 := sat_shift fraction.matrix fraction.modifiedDeck hH hv r
    have h2 := sat_shift fraction.matrix fraction.modifiedDeck hF hv r
    have hc' : ((H v : ℤ) : ℝ) - ((H 0 : ℤ) : ℝ) = ((F v : ℤ) : ℝ) - ((F 0 : ℤ) : ℝ) := by
      have := congrArg (fun z : ℤ => (z : ℝ)) (hcc v hv)
      push_cast at this
      exact this
    have key : ((H (r + v) - F (r + v) : ℤ) : ℝ) = ((H r - F r : ℤ) : ℝ) := by
      push_cast at h1 h2 ⊢
      linarith
    exact_mod_cast key
  intro x
  obtain ⟨r, hr, hv⟩ := hcov x
  have hD := step r (x - r) hv
  have hx : r + (x - r) = x := by abel
  rw [hx] at hD
  have hHr := hHt ⟨r, hr⟩
  have hFr := hFt ⟨r, hr⟩
  linarith

/-! ### Recurrence and the periodic field at each birth -/

theorem reciprocal_super_rec (k : ℕ) :
    Superharmonic (reciprocalField k) ∧ Recurrent (reciprocalField k) := by
  obtain ⟨hagree, hper⟩ := reciprocalField_spec k
  obtain ⟨_, _, _, hrank⟩ := stairEven_exists_burningRank (stairEven_valid_reciprocal k) hagree hper
  exact ⟨hrank.superharmonic, hrank.recurrent⟩

/-- The standard field of a power of two is recurrent: it is the ladder rotation of a recurrent ladder field. -/
theorem twos_super_rec (k : ℕ) :
    Superharmonic (standardField (List.replicate (k + 1) Digit.two)) ∧
      Recurrent (standardField (List.replicate (k + 1) Digit.two)) := by
  have hden : BaseMask.ladderOdd.Valid (2 * (k : ℤ) + 4) :=
    show 4 ≤ 2 * (k : ℤ) + 4 ∧ (2 * (k : ℤ) + 4) % 2 = 0 from ⟨by omega, by omega⟩
  obtain ⟨S, hagree, hper, _, hsup, hrec⟩ := ladderOdd_exists_recurrent_extension hden
  have hfun : standardField (List.replicate (k + 1) Digit.two) = rotateLadderField (2 * (k : ℤ) + 4) S :=
    funext (twos_standardField_eq_rotate k hagree hper)
  rw [hfun]
  exact rotateLadderField_recurrent hrec hsup

theorem proper_super_rec (u : Word) (hpk : ∀ v : Word, (frameAt v).Packet (standardField v))
    (hproper : ∃ x ∈ u, x ≠ Digit.three) (hstar : StarZoneInputs u) (hsheet : SheetLocalInputs u)
    (harc : VArcInputs (frameAt u) (standardField u))
    (hodd : OddBlackNoRise (standardField u) (frameAt u).shortShift)
    (hbulk : S3NoFortInputs (frameAt u) (standardField u)) :
    Superharmonic (standardField u) ∧ Recurrent (standardField u) := by
  obtain ⟨-, -, rank, hrank⟩ :=
    starEstimates_of_inputs u hproper (hpk (conjWord u)) (hpk u) hstar hsheet harc hodd hbulk
  exact ⟨hrank.toIsBurningRank.superharmonic, hrank.toIsBurningRank.recurrent⟩

/-- Superharmonicity and recurrence of the standard field at every word. -/
theorem super_rec_of_word (hpk : ∀ v : Word, (frameAt v).Packet (standardField v))
    (hstar : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word → StarZoneInputs word)
    (hsheet : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word → SheetLocalInputs word)
    (harc : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word →
      VArcInputs (frameAt word) (standardField word))
    (hodd : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word →
      OddBlackNoRise (standardField word) (frameAt word).shortShift)
    (hbulk : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word →
      S3NoFortInputs (frameAt word) (standardField word))
    (u : Word) : Superharmonic (standardField u) ∧ Recurrent (standardField u) := by
  by_cases hall : ∀ x ∈ u, x = Digit.three
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, u = List.replicate k Digit.three :=
      ⟨u.length, List.eq_replicate_iff.mpr ⟨rfl, hall⟩⟩
    rw [standardField_threes]
    exact reciprocal_super_rec k
  · have hproper : ∃ x ∈ u, x ≠ Digit.three := by
      by_contra h
      push Not at h
      exact hall h
    by_cases htw : IsTwoPow u
    · obtain ⟨k, rfl⟩ := htw
      exact twos_super_rec k
    · exact proper_super_rec u hpk hproper (hstar u hproper htw) (hsheet u hproper htw) (harc u hproper htw)
        (hodd u hproper htw) (hbulk u hproper htw)

/-! ### The plane field of each birth -/

theorem planeTarget_even (w : Word) : planeTarget w .even = standardField w := rfl

theorem planeTarget_odd (w : Word) :
    planeTarget w .odd = quarterTurnField (standardField (swapW w)) := by
  show quarterTurnField (standardField ((oddBirthPrefix (w ++ [Digit.one])).map Digit.swapTwoThree)) = _
  rw [conjWord_append_one]
  rfl

/-- The even birth: the standard field of `w` has the periods, growth, binary Laplacians and recurrence. -/
theorem facts_even {w : Word} {fr : Fraction} (hfr : (frameAt w).child = fr) (hint : fr.Interior)
    (hpk : (frameAt w).Packet (standardField w))
    (hsr : Superharmonic (standardField w) ∧ Recurrent (standardField w)) :
    SatisfiesPeriodicity fr (planeTarget w .even) ∧ HasQuadraticGrowth (planeTarget w .even) fr.matrix ∧
      (∀ x, laplacian (planeTarget w .even) x = -1 ∨ laplacian (planeTarget w .even) x = 0) ∧
      Superharmonic (planeTarget w .even) ∧ Recurrent (planeTarget w .even) := by
  rw [planeTarget_even]
  have hinterval : fr.InUnitInterval := hint.inUnitInterval
  have hper : HasGeneratorPeriods fr (standardField w) (frameAt w).coherentConstantU
      (frameAt w).coherentConstantV := by
    rw [← hfr]
    exact hpk.periods
  exact ⟨satisfiesPeriodicity_of_generatorPeriods hinterval hper, generator_periods_growth hinterval hper,
    hpk.binary, hsr.1, hsr.2⟩

/-- The odd birth: the quarter turn of the even standard field of the swapped word (`planeTarget w .odd`). -/
theorem facts_odd {w : Word} {fr : Fraction} (hfr : (frameAt (swapW w)).child = fr.rotate) (hodd : fr.Odd)
    (hint : fr.Interior) (hpk : (frameAt (swapW w)).Packet (standardField (swapW w)))
    (hsr : Superharmonic (standardField (swapW w)) ∧ Recurrent (standardField (swapW w))) :
    SatisfiesPeriodicity fr (planeTarget w .odd) ∧ HasQuadraticGrowth (planeTarget w .odd) fr.matrix ∧
      (∀ x, laplacian (planeTarget w .odd) x = -1 ∨ laplacian (planeTarget w .odd) x = 0) ∧
      Superharmonic (planeTarget w .odd) ∧ Recurrent (planeTarget w .odd) := by
  rw [planeTarget_odd]
  have hinterval : fr.InUnitInterval := hint.inUnitInterval
  have hT : (fr.periodDenominator : ℝ) ≠ 0 := by
    have := Fraction.periodDenominator_pos hinterval
    exact_mod_cast this.ne'
  have hrotInt : fr.rotate.Interior := by
    obtain ⟨hn, hnd⟩ := hint
    obtain ⟨h1, h2⟩ := rotate_num_den_of_odd hodd
    unfold Fraction.Interior
    rw [h1, h2]
    constructor <;> omega
  have hper : HasGeneratorPeriods fr.rotate (standardField (swapW w)) (frameAt (swapW w)).coherentConstantU
      (frameAt (swapW w)).coherentConstantV := by
    rw [← hfr]
    exact hpk.periods
  have hps := satisfiesPeriodicity_of_generatorPeriods hrotInt.inUnitInterval hper
  have hgr := generator_periods_growth hrotInt.inUnitInterval hper
  obtain ⟨hsup, hrec⟩ := hsr
  have hoff : ¬ EvenSite (0, -1) := by decide
  have hqS : Superharmonic (quarterTurnField (standardField (swapW w))) ∧
      Recurrent (quarterTurnField (standardField (swapW w))) :=
    Recurrent.quarterTurn (correction := harmonicGrid) hrec hsup QuarterTurn.counterclockwise (0, -1) hoff
      (fun x => harmonicGrid_harmonic x)
  refine ⟨satisfiesPeriodicity_quarterTurn hodd hT hps, ?_, fun x => quarterTurnField_binary hpk.binary x,
    hqS.1, hqS.2⟩
  rw [quarterTurnField_eq]
  exact growth_of_affine_remainder hgr harmonicGrid _ _ _ (growth_identity hodd hT)

/-! ### `lemma:global_odometers` -/

/-- `lemma:global_odometers` at a birth `(w, p)` of `fraction = n/d`, with the remaining inputs named in the signature.

Open local inputs (the headline's, at the proper words that are not powers of two): `hstar`, `hsheet`, `harc`, `hodd`,
`hbulk`. Standard tile facts for every word: `bdOdd`, `bdEven`, `simpleOdd`, `simpleEven`. Identification of the finite
tile with the plane field: `htile`. Coverage of the tile: `hsites`, which is either the standard tile of the birth (then
coverage follows from `DeckCoverage`) or the corrected-output case, named as `fraction.modifiedDeck.Covers tile.sites`. -/
theorem global_odometers {fraction : Fraction} (hint : fraction.Interior) {w : Word} {p : Parity}
    (hbirth : (parentsAt w).current p = fraction)
    (hstar : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word → StarZoneInputs word)
    (hsheet : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word → SheetLocalInputs word)
    (harc : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word →
      VArcInputs (frameAt word) (standardField word))
    (hodd : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word →
      OddBlackNoRise (standardField word) (frameAt word).shortShift)
    (hbulk : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word →
      S3NoFortInputs (frameAt word) (standardField word))
    (bdOdd : ∀ v : Word, StandardBoundaryOdd v) (bdEven : ∀ v : Word, StandardBoundaryEven v)
    (simpleOdd : ∀ v : Word, IsSimpleTile (cellTileOf (oddTile v)))
    (simpleEven : ∀ v : Word, IsSimpleTile (cellTileOf (evenTile v)))
    (tile : HeightTile Site)
    (htile : ∃ gauge : ℤ, tile.Agrees (planeTarget w p) gauge)
    (hsites : (p = .even ∧ tile.sites = evenTile w) ∨ (p = .odd ∧ tile.sites = oddTile w) ∨
      fraction.modifiedDeck.Covers tile.sites) :
    (∃ c : ℤ, ∀ (x : Site) (hx : x ∈ tile.sites), planeTarget w p x = tile.height ⟨x, hx⟩ + c) ∧
    SatisfiesPeriodicity fraction (planeTarget w p) ∧
    HasQuadraticGrowth (planeTarget w p) fraction.matrix ∧
    (∃ b : Fin 2 → ℝ, ∀ v ∈ fraction.modifiedDeck.span,
      Function.Periodic (fun x : Site => ((planeTarget w p x : ℤ) : ℝ) - matrixQuadratic fraction.matrix x -
        dotProduct b (siteVector x)) v) ∧
    (∀ x, laplacian (planeTarget w p) x = -1 ∨ laplacian (planeTarget w p) x = 0) ∧
    Superharmonic (planeTarget w p) ∧ Recurrent (planeTarget w p) ∧
    (∀ H : Field, SatisfiesPeriodicity fraction H →
      (∀ v ∈ fraction.modifiedDeck.span, H v - H 0 = planeTarget w p v - planeTarget w p 0) →
      ∀ gH : ℤ, tile.Agrees H gH → ∃ c : ℤ, ∀ x, H x = planeTarget w p x + c) := by
  subst hbirth
  have htwo : ∀ k : ℕ, (frameAt (List.replicate (k + 1) Digit.two)).Packet
      (standardField (List.replicate (k + 1) Digit.two)) :=
    fun k => twos_packet_standard k (fun _ hz ht => twos_zero_strip k hz ht)
      (fun _ hz hs => twos_harm_strip k hz hs)
  have hpk : ∀ u : Word, (frameAt u).Packet (standardField u) :=
    packet_standardField_of_twos htwo hstar hsheet
  have hsr := super_rec_of_word hpk hstar hsheet harc hodd hbulk
  obtain ⟨gauge, hag⟩ := htile
  have hcov : ((parentsAt w).current p).modifiedDeck.Covers tile.sites := by
    rcases hsites with ⟨rfl, hs⟩ | ⟨rfl, hs⟩ | hc
    · exact covers_of_eq_even bdEven simpleEven hs
    · exact covers_of_eq_odd bdOdd simpleOdd hs
    · exact hc
  have hfacts : SatisfiesPeriodicity ((parentsAt w).current p) (planeTarget w p) ∧
      HasQuadraticGrowth (planeTarget w p) ((parentsAt w).current p).matrix ∧
      (∀ x, laplacian (planeTarget w p) x = -1 ∨ laplacian (planeTarget w p) x = 0) ∧
      Superharmonic (planeTarget w p) ∧ Recurrent (planeTarget w p) := by
    cases p with
    | even => exact facts_even rfl hint (hpk w) (hsr w)
    | odd =>
      exact facts_odd (current_swap w).1 (parentsAt_valid w).current_odd_parity hint (hpk (swapW w))
        (hsr (swapW w))
  obtain ⟨hSP, hgr, hbin, hsup, hrec⟩ := hfacts
  refine ⟨⟨-gauge, fun x hx => ?_⟩, hSP, hgr, exists_tilt hint.inUnitInterval hSP, hbin, hsup, hrec,
    fun H hH hcc gH hHt => ⟨gauge - gH, fun x => ?_⟩⟩
  · have := hag ⟨x, hx⟩
    linarith
  · exact unique_of_covers tile hcov hSP hH hcc hag hHt x


/-! ### The alternate odometer and the distinctness -/

/-- The plane alternate of a birth: `ĝ = ⌈(g + g(· + σ))/2⌉` of the even child, or the quarter turn of the swapped word's
alternate at odd births (the same convention as `planeTarget`). -/
noncomputable def planeAlternate (w : Word) : Parity → Field
  | .even => (frameAt w).alternate (standardField w)
  | .odd => quarterTurnField ((frameAt (swapW w)).alternate (standardField (swapW w)))

theorem planeAlternate_even (w : Word) : planeAlternate w .even = (frameAt w).alternate (standardField w) := rfl

theorem planeAlternate_odd (w : Word) :
    planeAlternate w .odd = quarterTurnField ((frameAt (swapW w)).alternate (standardField (swapW w))) := rfl

/-- The star estimates of every word: the base words (pure words and powers of two) are named, the proper words come from
the open local inputs. -/
theorem starEstimates_all (hpk : ∀ u : Word, (frameAt u).Packet (standardField u))
    (hstar : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word → StarZoneInputs word)
    (hsheet : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word → SheetLocalInputs word)
    (harc : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word →
      VArcInputs (frameAt word) (standardField word))
    (hodd : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word →
      OddBlackNoRise (standardField word) (frameAt word).shortShift)
    (hbulk : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word →
      S3NoFortInputs (frameAt word) (standardField word))
    (hbase : ∀ u : Word, ((∀ x ∈ u, x = Digit.three) ∨ IsTwoPow u) → StarEstimates u) (u : Word) :
    StarEstimates u := by
  by_cases hall : ∀ x ∈ u, x = Digit.three
  · exact hbase u (Or.inl hall)
  · have hproper : ∃ x ∈ u, x ≠ Digit.three := by
      by_contra h
      push Not at h
      exact hall h
    by_cases htw : IsTwoPow u
    · exact hbase u (Or.inr htw)
    · exact starEstimates_of_inputs u hproper (hpk (conjWord u)) (hpk u) (hstar u hproper htw)
        (hsheet u hproper htw) (harc u hproper htw) (hodd u hproper htw) (hbulk u hproper htw)

/-- The even alternate of a word with its star estimates: the periods, growth, binary Laplacian, recurrence and the
non-integer-affine difference from the standard field. -/
theorem alternate_facts_word (u : Word) (hpk : (frameAt u).Packet (standardField u)) (hS : StarEstimates u) :
    SatisfiesPeriodicity (frameAt u).child ((frameAt u).alternate (standardField u)) ∧
      HasQuadraticGrowth ((frameAt u).alternate (standardField u)) (frameAt u).child.matrix ∧
      (∀ x, laplacian ((frameAt u).alternate (standardField u)) x = -1 ∨
        laplacian ((frameAt u).alternate (standardField u)) x = 0) ∧
      Superharmonic ((frameAt u).alternate (standardField u)) ∧
      Recurrent ((frameAt u).alternate (standardField u)) ∧
      ¬ IntegerAffine (fun x => (frameAt u).alternate (standardField u) x - standardField u x) := by
  obtain ⟨hU, hNS, rank, hrank⟩ := hS
  exact (frameAt u).alternate_facts hpk.periods hU hNS hrank

/-- The quarter turn of an even alternate: the same facts at the odd type (the transfer of `odometersTheoremAt_of_rotate`). -/
theorem alternate_quarterTurn_facts {fr : Fraction} {A G : Field} (hodd : fr.Odd)
    (hinterval : fr.InUnitInterval) (hA : SatisfiesPeriodicity fr.rotate A)
    (hgrA : HasQuadraticGrowth A fr.rotate.matrix)
    (hbinA : ∀ x, laplacian A x = -1 ∨ laplacian A x = 0) (hsupA : Superharmonic A) (hrecA : Recurrent A)
    (hnot : ¬ IntegerAffine (fun x => A x - G x)) :
    SatisfiesPeriodicity fr (quarterTurnField A) ∧ HasQuadraticGrowth (quarterTurnField A) fr.matrix ∧
      (∀ x, laplacian (quarterTurnField A) x = -1 ∨ laplacian (quarterTurnField A) x = 0) ∧
      Superharmonic (quarterTurnField A) ∧ Recurrent (quarterTurnField A) ∧
      ¬ IntegerAffine (fun x => quarterTurnField A x - quarterTurnField G x) := by
  have hT : (fr.periodDenominator : ℝ) ≠ 0 := by
    have := Fraction.periodDenominator_pos hinterval
    exact_mod_cast this.ne'
  have hoff : ¬ EvenSite (0, -1) := by decide
  have hq : Superharmonic (quarterTurnField A) ∧ Recurrent (quarterTurnField A) :=
    Recurrent.quarterTurn (correction := harmonicGrid) hrecA hsupA QuarterTurn.counterclockwise (0, -1) hoff
      (fun x => harmonicGrid_harmonic x)
  have hdiff : (fun x => quarterTurnField A x - quarterTurnField G x) =
      fun x => (fun y => A y - G y) (-x.2, x.1 - 1) := by
    funext x
    simp only [quarterTurnField_eq]
    ring
  refine ⟨satisfiesPeriodicity_quarterTurn hodd hT hA, ?_, fun x => quarterTurnField_binary hbinA x, hq.1,
    hq.2, ?_⟩
  · rw [quarterTurnField_eq]
    exact growth_of_affine_remainder hgrA harmonicGrid _ _ _ (growth_identity hodd hT)
  · rw [hdiff]
    exact not_integerAffine_comp_quarterTurn hnot

/-- The alternate facts of a birth `(w, p)` of `fr`, at both parities: the quarter turn at the odd birth. -/
theorem alternate_facts_birth (w : Word) (p : Parity) {fr : Fraction} (hfr : (parentsAt w).current p = fr)
    (hint : fr.Interior) (hpk : ∀ u : Word, (frameAt u).Packet (standardField u))
    (hS : ∀ u : Word, StarEstimates u) :
    SatisfiesPeriodicity fr (planeAlternate w p) ∧ HasQuadraticGrowth (planeAlternate w p) fr.matrix ∧
      (∀ x, laplacian (planeAlternate w p) x = -1 ∨ laplacian (planeAlternate w p) x = 0) ∧
      Superharmonic (planeAlternate w p) ∧ Recurrent (planeAlternate w p) ∧
      ¬ IntegerAffine (fun x => planeAlternate w p x - planeTarget w p x) := by
  subst hfr
  cases p with
  | even =>
    rw [planeAlternate_even, planeTarget_even]
    exact alternate_facts_word w (hpk w) (hS w)
  | odd =>
    have hodd : ((parentsAt w).current .odd).Odd := (parentsAt_valid w).current_odd_parity
    have hch : (frameAt (swapW w)).child = ((parentsAt w).current .odd).rotate := (current_swap w).1
    obtain ⟨hA1, hA2, hA3, hA4, hA5, hA6⟩ := alternate_facts_word (swapW w) (hpk (swapW w)) (hS (swapW w))
    rw [hch] at hA1 hA2
    rw [planeAlternate_odd, planeTarget_odd]
    exact alternate_quarterTurn_facts hodd hint.inUnitInterval hA1 hA2 hA3 hA4 hA5 hA6

/-- The incoming neighbours average to the site. -/
theorem incoming_add (x : Site) : incomingNeg x + incomingPos x = x + x := by
  by_cases h : EvenSite x
  · rw [HarmonicConstant.incomingNeg_even h, HarmonicConstant.incomingPos_even h]
    simp only [Prod.mk_add_mk]
    congr 1; ring
  · rw [HarmonicConstant.incomingNeg_odd h, HarmonicConstant.incomingPos_odd h]
    simp only [Prod.mk_add_mk]
    congr 1; ring

theorem dotProduct_siteVector_eq (b : Fin 2 → ℝ) (x : Site) :
    dotProduct b (siteVector x) = b 0 * (x.1 : ℝ) + b 1 * (x.2 : ℝ) := by
  simp only [dotProduct, Fin.sum_univ_two, siteVector, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem dot_siteVector_zero (b : Fin 2 → ℝ) : dotProduct b (siteVector (0 : Site)) = 0 := by
  rw [dotProduct_siteVector_eq]
  simp

theorem dot_siteVector_one_zero (b : Fin 2 → ℝ) : dotProduct b (siteVector ((1 : ℤ), (0 : ℤ))) = b 0 := by
  rw [dotProduct_siteVector_eq]
  simp

theorem dot_siteVector_zero_one (b : Fin 2 → ℝ) : dotProduct b (siteVector ((0 : ℤ), (1 : ℤ))) = b 1 := by
  rw [dotProduct_siteVector_eq]
  simp

/-- The deck contains `(kN, lN)` for `N = det`. -/
theorem det_mul_mem_span (deck : PeriodDeck) (k l : ℤ) : (k * deck.det, l * deck.det) ∈ deck.span := by
  refine ⟨k * deck.transverse.2 - l * deck.transverse.1, l * deck.kernel.1 - k * deck.kernel.2, ?_⟩
  ext <;> simp [PeriodDeck.combine, PeriodDeck.det] <;> ring

/-- Two fields with `eq:periodicity` and a non-integer-affine difference have different Laplacians somewhere: a harmonic
difference of this kind is periodic up to a real linear function, hence constant by the maximum principle, hence integer
affine. -/
theorem laplacian_differs {fraction : Fraction} (hinterval : fraction.InUnitInterval) {H F : Field}
    (hH : SatisfiesPeriodicity fraction H) (hF : SatisfiesPeriodicity fraction F)
    (hnot : ¬ IntegerAffine (fun x => H x - F x)) : ∃ x, laplacian H x ≠ laplacian F x := by
  by_contra hcon
  push Not at hcon
  have hD : ∀ v ∈ fraction.modifiedDeck.span, ∃ c : ℤ, ∀ x : Site,
      (((H (x + v) - F (x + v) : ℤ)) : ℝ) = (((H x - F x : ℤ)) : ℝ) +
        dotProduct (siteVector x) ((0 : Matrix (Fin 2) (Fin 2) ℝ).mulVec (siteVector v)) + (c : ℝ) := by
    intro v hv
    refine ⟨(H v - H 0) - (F v - F 0), fun x => ?_⟩
    have h1 := sat_shift fraction.matrix fraction.modifiedDeck hH hv x
    have h2 := sat_shift fraction.matrix fraction.modifiedDeck hF hv x
    simp only [Matrix.zero_mulVec, dotProduct_zero, add_zero]
    push_cast at h1 h2 ⊢
    linarith
  have hdet : 0 < fraction.modifiedDeck.det := Fraction.det_modifiedDeck_pos hinterval
  have hsym0 : ∀ x y : Site, dotProduct (siteVector x) ((0 : Matrix (Fin 2) (Fin 2) ℝ).mulVec (siteVector y)) =
      dotProduct (siteVector y) ((0 : Matrix (Fin 2) (Fin 2) ℝ).mulVec (siteVector x)) := by
    intro x y
    simp
  obtain ⟨b, hb⟩ := exists_tilt_of_deck (H := fun y => H y - F y) (0 : Matrix (Fin 2) (Fin 2) ℝ)
    fraction.modifiedDeck hdet hsym0 hD
  obtain ⟨E, hE⟩ : ∃ E : Site → ℝ, ∀ x, E x = (((H x - F x : ℤ)) : ℝ) - dotProduct b (siteVector x) :=
    ⟨fun x => (((H x - F x : ℤ)) : ℝ) - dotProduct b (siteVector x), fun x => rfl⟩
  have h0 : ∀ y : Site, matrixQuadratic (0 : Matrix (Fin 2) (Fin 2) ℝ) y = 0 := by
    intro y
    unfold matrixQuadratic
    simp
  have hEper : ∀ v ∈ fraction.modifiedDeck.span, ∀ x, E (x + v) = E x := by
    intro v hv x
    have h := hb v hv x
    dsimp only at h
    rw [h0, h0] at h
    rw [hE, hE]
    linarith
  have hharm : ∀ x : Site, E (incomingNeg x) + E (incomingPos x) = 2 * E x := by
    intro x
    have hl := hcon x
    unfold laplacian at hl
    have hr : (H (incomingNeg x) : ℝ) + H (incomingPos x) - 2 * H x =
        (F (incomingNeg x) : ℝ) + F (incomingPos x) - 2 * F x := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hl
      push_cast at this
      linarith
    have hd : dotProduct b (siteVector (incomingNeg x)) + dotProduct b (siteVector (incomingPos x)) =
        2 * dotProduct b (siteVector x) := by
      rw [← dotProduct_add, ← siteVector_add, incoming_add, siteVector_add, dotProduct_add]
      ring
    rw [hE, hE, hE]
    push_cast at hr ⊢
    linarith
  have hN : (0 : ℤ) < fraction.modifiedDeck.det := hdet
  have hconst := HarmonicConstant.harmonic_periodic_constant E fraction.modifiedDeck.det hN
    (fun x k l => hEper _ (det_mul_mem_span fraction.modifiedDeck k l) x) hharm
  have hb0 : b 0 = ((H ((1 : ℤ), (0 : ℤ)) - F ((1 : ℤ), (0 : ℤ)) : ℤ) : ℝ) - ((H 0 - F 0 : ℤ) : ℝ) := by
    have h1 := hconst ((1 : ℤ), (0 : ℤ))
    rw [hE, hE, dot_siteVector_one_zero, dot_siteVector_zero] at h1
    linarith
  have hb1 : b 1 = ((H ((0 : ℤ), (1 : ℤ)) - F ((0 : ℤ), (1 : ℤ)) : ℤ) : ℝ) - ((H 0 - F 0 : ℤ) : ℝ) := by
    have h1 := hconst ((0 : ℤ), (1 : ℤ))
    rw [hE, hE, dot_siteVector_zero_one, dot_siteVector_zero] at h1
    linarith
  apply hnot
  refine ⟨((H ((1 : ℤ), (0 : ℤ)) - F ((1 : ℤ), (0 : ℤ))) - (H 0 - F 0),
    (H ((0 : ℤ), (1 : ℤ)) - F ((0 : ℤ), (1 : ℤ))) - (H 0 - F 0)), H 0 - F 0, fun x => ?_⟩
  have hx := hconst x
  rw [hE, hE, dot_siteVector_zero, dotProduct_siteVector_eq, hb0, hb1] at hx
  have key : (((H x - F x : ℤ)) : ℝ) = ((((H ((1 : ℤ), (0 : ℤ)) - F ((1 : ℤ), (0 : ℤ))) - (H 0 - F 0)) * x.1 +
      ((H ((0 : ℤ), (1 : ℤ)) - F ((0 : ℤ), (1 : ℤ))) - (H 0 - F 0)) * x.2 + (H 0 - F 0) : ℤ) : ℝ) := by
    push_cast at hx ⊢
    linear_combination hx
  exact_mod_cast key


/-- The packets of every word, from the powers of two and the open inputs (as in `odometersTheorem_of_nearOne_unconditional`). -/
theorem packet_all (hstar : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word → StarZoneInputs word)
    (hsheet : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word → SheetLocalInputs word) :
    ∀ u : Word, (frameAt u).Packet (standardField u) :=
  packet_standardField_of_twos
    (fun k => twos_packet_standard k (fun _ hz ht => twos_zero_strip k hz ht)
      (fun _ hz hs => twos_harm_strip k hz hs))
    hstar hsheet

/-- `lemma:global_odometers` for both odometers at a birth `(w, p)` of `fraction = n/d`: the standard one (`global_odometers`),
and the alternate `ĝ = planeAlternate w p`, with its identification of the constructor's alternate tile (`htileAlt`) and the
coverage of that tile (`hcovAlt`), and the distinctness of the two: the difference is not integer affine (in the fixed
coordinates of `eq:periodicity`), and the Laplacians differ somewhere.

The inputs are those of `global_odometers` together with `hbase`: the star estimates of the base words (pure words and
powers of two), which the library does not yet derive for the standard fields at those words. -/
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
    (hbase : ∀ u : Word, ((∀ x ∈ u, x = Digit.three) ∨ IsTwoPow u) → StarEstimates u)
    (bdOdd : ∀ v : Word, StandardBoundaryOdd v) (bdEven : ∀ v : Word, StandardBoundaryEven v)
    (simpleOdd : ∀ v : Word, IsSimpleTile (cellTileOf (oddTile v)))
    (simpleEven : ∀ v : Word, IsSimpleTile (cellTileOf (evenTile v)))
    (tile : HeightTile Site)
    (htile : ∃ gauge : ℤ, tile.Agrees (planeTarget w p) gauge)
    (hsites : (p = .even ∧ tile.sites = evenTile w) ∨ (p = .odd ∧ tile.sites = oddTile w) ∨
      fraction.modifiedDeck.Covers tile.sites)
    (altTile : HeightTile Site) (htileAlt : ∃ gauge : ℤ, altTile.Agrees (planeAlternate w p) gauge)
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
    (∃ c : ℤ, ∀ (x : Site) (hx : x ∈ altTile.sites), planeAlternate w p x = altTile.height ⟨x, hx⟩ + c) ∧
    SatisfiesPeriodicity fraction (planeAlternate w p) ∧
    HasQuadraticGrowth (planeAlternate w p) fraction.matrix ∧
    (∃ b : Fin 2 → ℝ, ∀ v ∈ fraction.modifiedDeck.span,
      Function.Periodic (fun x : Site => ((planeAlternate w p x : ℤ) : ℝ) - matrixQuadratic fraction.matrix x -
        dotProduct b (siteVector x)) v) ∧
    (∀ x, laplacian (planeAlternate w p) x = -1 ∨ laplacian (planeAlternate w p) x = 0) ∧
    Superharmonic (planeAlternate w p) ∧ Recurrent (planeAlternate w p) ∧
    (∀ H : Field, SatisfiesPeriodicity fraction H →
      (∀ v ∈ fraction.modifiedDeck.span, H v - H 0 = planeAlternate w p v - planeAlternate w p 0) →
      ∀ gH : ℤ, altTile.Agrees H gH → ∃ c : ℤ, ∀ x, H x = planeAlternate w p x + c) ∧
    ¬ IntegerAffine (fun x => planeAlternate w p x - planeTarget w p x) ∧
    (∃ x, laplacian (planeAlternate w p) x ≠ laplacian (planeTarget w p) x) := by
  have hpk : ∀ u : Word, (frameAt u).Packet (standardField u) := packet_all hstar hsheet
  have hS : ∀ u : Word, StarEstimates u := starEstimates_all hpk hstar hsheet harc hodd hbulk hbase
  have hstd := global_odometers hint hbirth hstar hsheet harc hodd hbulk bdOdd bdEven simpleOdd simpleEven
    tile htile hsites
  have hstdSP : SatisfiesPeriodicity fraction (planeTarget w p) := hstd.2.1
  obtain ⟨hAS, hAGr, hAB, hAS2, hAR, hAN⟩ := alternate_facts_birth w p hbirth hint hpk hS
  obtain ⟨gauge, hag⟩ := htileAlt
  refine ⟨hstd, ⟨-gauge, fun x hx => ?_⟩, hAS, hAGr, exists_tilt hint.inUnitInterval hAS, hAB, hAS2, hAR,
    fun H hH hcc gH hHt => ⟨gauge - gH, fun x => unique_of_covers altTile hcovAlt hAS hH hcc hag hHt x⟩,
    hAN, laplacian_differs hint.inUnitInterval hAS hstdSP hAN⟩
  have := hag ⟨x, hx⟩
  linarith

end FLatticePaper.GlobalOdometers
