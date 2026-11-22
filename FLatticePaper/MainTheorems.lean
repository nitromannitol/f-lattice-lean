import FLatticePaper.Plane.HyperbolaBoundary
import FLatticePaper.Plane.OdometerTheorem
import FLatticePaper.Plane.OdometersStatement
import FLatticePaper.Plane.Induction.EvenStep
import FLatticePaper.Plane.Induction.OddStep
import FLatticePaper.Plane.Induction.Packet
import FLatticePaper.Plane.Induction.StandardField
import FLatticePaper.Plane.Induction.WordInduction
import FLatticePaper.Plane.Induction.LocalPremises
import FLatticePaper.Plane.Induction.LocalPremisesRestricted
import FLatticePaper.Plane.RestrictedBellmanRank
import FLatticePaper.Plane.Induction.OpenLocal
import FLatticePaper.Plane.Induction.TwosInduction
import FLatticePaper.Plane.Induction.TwosPeriods
import FLatticePaper.Plane.Induction.TwosStripFacts

/-! The two headline theorems from `theorem:odometers` at every reduced interior slope. -/

namespace FLatticePaper

open Farey

private theorem recurrentInterior_of_odometersTheorem (h : OdometersTheorem) :
    ∀ fraction : Fraction, fraction.Interior → fraction.Reduced →
      ∃ height : Field, Superharmonic height ∧ Recurrent height ∧
        HasQuadraticGrowth height fraction.matrix := by
  intro fraction hinterior hreduced
  obtain ⟨standard, _, ⟨hsuper, hrec, hgrowth⟩, _⟩ := h fraction hinterior hreduced
  exact ⟨standard, hsuper, hrec, hgrowth⟩

/-- `theorem:hyperbola` from `theorem:odometers`. -/
theorem hyperbola_of_odometersTheorem (h : OdometersTheorem) (t : ℝ) (ht : 0 ≤ t) (hu : t ≤ 1) :
    symmetricCircleMatrix t (1 - t) (-Real.sqrt (t ^ 2 + (1 - t) ^ 2)) ∈ frontier symmetricGrowthSet :=
  hyperbolaBoundary_of_recurrentInterior (recurrentInterior_of_odometersTheorem h) t ht hu

/-- `theorem:circle_packing` from `theorem:odometers`. -/
theorem circlePacking_of_odometersTheorem (h : OdometersTheorem) (matrix : Matrix (Fin 2) (Fin 2) ℝ) :
    matrix ∈ integerSuperharmonicMatrices ↔ ∃ s t : ℤ, (harmonicPeak s t - matrix).PosSemidef :=
  circlePacking_of_recurrentInterior (recurrentInterior_of_odometersTheorem h) matrix

/-- The Part I data of the standard field at the even child of a frame (used in `EvenStep`). -/
def Induction.ChildFrame.HasStandardData (frame : Induction.ChildFrame) : Prop :=
  ∃ F : Field, ∃ cU cV : ℤ, HasGeneratorPeriods frame.child F cU cV ∧
    HasUnitSlip F (fun z => F (z + frame.shortShift)) ∧
    NoEvenSlipSaddle F (fun z => F (z + frame.shortShift)) ∧
    ∃ rank : Site → ℤ, IsConstrainedBurningRank F rank
      (fun center input => slipIncrement F (fun z => F (z + frame.shortShift)) center input ≤ 0)

/-- All three headline results follow from the standard data at the even child of every word. -/
theorem odometersTheorem_of_standardData
    (h : ∀ word : Word, (⟨parentsAt word, parentsAt_valid word⟩ : Induction.ChildFrame).HasStandardData) :
    OdometersTheorem := by
  refine Induction.odometersTheorem_of_even ?_
  intro fraction hint hred heven
  obtain ⟨birth, hbirth, -⟩ := existsUnique_birth fraction hint hred
  obtain ⟨word, parity⟩ := birth
  have hparity : parity = Parity.even := by
    cases parity with
    | even => rfl
    | odd =>
      exfalso
      have hodd : fraction.Odd := by
        rw [← hbirth]
        exact (parentsAt_valid word).current_odd_parity
      unfold Fraction.Odd at hodd
      unfold Fraction.Even at heven
      omega
  subst hparity
  have hchild : (⟨parentsAt word, parentsAt_valid word⟩ : Induction.ChildFrame).child = fraction := hbirth
  obtain ⟨F, cU, cV, hper, hstep, hnoSaddle, rank, hrank⟩ := h word
  have key := Induction.ChildFrame.odometersTheoremAt_of_standard
    (⟨parentsAt word, parentsAt_valid word⟩ : Induction.ChildFrame) hper hstep hnoSaddle hrank
  rw [hchild] at key
  exact key

open Induction

/-- The three star estimates and a constrained rank of the standard field of a word (Section 9). -/
def StarEstimates (word : Word) : Prop :=
  let F := standardField word
  let frame := frameAt word
  HasUnitSlip F (fun z => F (z + frame.shortShift)) ∧
    NoEvenSlipSaddle F (fun z => F (z + frame.shortShift)) ∧
    ∃ rank : Site → ℤ, IsConstrainedBurningRank F rank
      (fun center input => slipIncrement F (fun z => F (z + frame.shortShift)) center input ≤ 0)

/-- All three headline results from the packets and the star estimates at every proper word. -/
theorem odometersTheorem_of_packets
    (hpacket : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → (frameAt word).Packet (standardField word))
    (hest : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → StarEstimates word) :
    OdometersTheorem := by
  refine Induction.odometersTheorem_of_even ?_
  intro fraction hint hred heven
  obtain ⟨birth, hbirth, -⟩ := existsUnique_birth fraction hint hred
  obtain ⟨word, parity⟩ := birth
  have hparity : parity = Parity.even := by
    cases parity with
    | even => rfl
    | odd =>
      exfalso
      have hodd : fraction.Odd := by
        rw [← hbirth]
        exact (parentsAt_valid word).current_odd_parity
      unfold Fraction.Odd at hodd
      unfold Fraction.Even at heven
      omega
  subst hparity
  have hchild : (⟨parentsAt word, parentsAt_valid word⟩ : Induction.ChildFrame).child = fraction := hbirth
  by_cases hall : ∀ x ∈ word, x = .three
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, word = List.replicate k Digit.three :=
      ⟨word.length, List.eq_replicate_iff.mpr ⟨rfl, hall⟩⟩
    subst hk
    have hfr : fraction = ⟨1, 2 * (k : ℤ) + 3⟩ := by
      rw [← hchild]
      exact reciprocalFrame_child k
    rw [hfr]
    exact (odometersTheoremAt_base (by omega)).1
  · push Not at hall
    have hp := hpacket word hall
    obtain ⟨hU, hNS, rank, hrank⟩ := hest word hall
    have key := Induction.ChildFrame.odometersTheoremAt_of_standard
      (⟨parentsAt word, parentsAt_valid word⟩ : Induction.ChildFrame) hp.periods hU hNS hrank
    rw [hchild] at key
    exact key

/-- `theorem:odometers` from the open inputs of the plane induction and the star estimates at every proper word. -/
theorem odometersTheorem_of_openInputs
    (hopen : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → Induction.OpenInputs word)
    (hest : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → StarEstimates word) :
    OdometersTheorem :=
  odometersTheorem_of_packets (fun word _ => Induction.packet_standardField hopen word) hest

/-- `theorem:hyperbola` from the open inputs and the star estimates. -/
theorem hyperbola_of_openInputs
    (hopen : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → Induction.OpenInputs word)
    (hest : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → StarEstimates word) (t : ℝ) (ht : 0 ≤ t) (hu : t ≤ 1) :
    symmetricCircleMatrix t (1 - t) (-Real.sqrt (t ^ 2 + (1 - t) ^ 2)) ∈ frontier symmetricGrowthSet :=
  hyperbola_of_odometersTheorem (odometersTheorem_of_openInputs hopen hest) t ht hu

/-- `theorem:circle_packing` from the open inputs and the star estimates. -/
theorem circlePacking_of_openInputs
    (hopen : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → Induction.OpenInputs word)
    (hest : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → StarEstimates word) (matrix : Matrix (Fin 2) (Fin 2) ℝ) :
    matrix ∈ integerSuperharmonicMatrices ↔ ∃ s t : ℤ, (harmonicPeak s t - matrix).PosSemidef :=
  circlePacking_of_odometersTheorem (odometersTheorem_of_openInputs hopen hest) matrix

/-- The three star estimates at a proper word, from its packet and its local premises. -/
theorem starEstimates_of_localPremises {word : Word} (hp : (frameAt word).Packet (standardField word))
    (hloc : Induction.LocalPremises word) : StarEstimates word := by
  dsimp only [Induction.LocalPremises] at hloc
  obtain ⟨-, -, -, -, -, hEr, hNr, hJ, hlocal, hno⟩ := hloc
  obtain ⟨hU, hNS⟩ := Induction.ChildFrame.star_of_closedPolygon (frameAt word) hp.periods hEr hNr hJ
  obtain ⟨rank, hrank⟩ := S3_of_packet_restrictedNoFort word hp hlocal hno
  unfold StarEstimates
  exact ⟨hU, hNS, rank, hrank⟩

/-- `theorem:odometers` from the local premises at every proper word. -/
theorem odometersTheorem_of_localPremises
    (h : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → Induction.LocalPremises word) : OdometersTheorem :=
  odometersTheorem_of_packets (fun word _ => Induction.packet_of_localPremises h word)
    (fun word hw => starEstimates_of_localPremises (Induction.packet_of_localPremises h word) (h word hw))

/-- `theorem:odometers` from the variant of the local premises (restricted forts) at every proper word. -/
theorem odometersTheorem_of_localPremises'
    (h : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → Induction.LocalPremises' word) : OdometersTheorem :=
  odometersTheorem_of_packets (fun word _ => Induction.packet_of_localPremises' h word)
    (fun word hw => starEstimates_of_localPremises (Induction.packet_of_localPremises' h word)
      (Induction.localPremises_of_variant hw (Induction.packet_of_localPremises' h (Induction.conjWord word))
        (h word hw)))

/-- `theorem:hyperbola` from the local premises at every proper word. -/
theorem hyperbola_of_localPremises
    (h : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → Induction.LocalPremises word) (t : ℝ) (ht : 0 ≤ t) (hu : t ≤ 1) :
    symmetricCircleMatrix t (1 - t) (-Real.sqrt (t ^ 2 + (1 - t) ^ 2)) ∈ frontier symmetricGrowthSet :=
  hyperbola_of_odometersTheorem (odometersTheorem_of_localPremises h) t ht hu

/-- `theorem:circle_packing` from the local premises at every proper word. -/
theorem circlePacking_of_localPremises
    (h : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → Induction.LocalPremises word) (matrix : Matrix (Fin 2) (Fin 2) ℝ) :
    matrix ∈ integerSuperharmonicMatrices ↔ ∃ s t : ℤ, (harmonicPeak s t - matrix).PosSemidef :=
  circlePacking_of_odometersTheorem (odometersTheorem_of_localPremises h) matrix

/-- The headline `theorem:odometers` from the open inputs only: at every proper word, the I1 and I2 zone witnesses
(`StarZoneInputs`), the I3 sheet inputs (`SheetLocalInputs`), the V arc range (`VArcInputs`), the odd black no-rise premise
(`OddBlackNoRise`, the one case of the slip permits that the local data do not exclude), and the S3 no-fort inputs
(`S3NoFortInputs`). The packets, the conjugate induction, the S1 and S2 window, the halo, the recurrence of the sheet
minimum, the slip permits and the S3 rank are proved inside. -/
theorem odometersTheorem_of_openLocalInputs
    (hstar : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → Induction.StarZoneInputs word)
    (hsheet : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → Induction.SheetLocalInputs word)
    (harc : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → Induction.VArcInputs (frameAt word) (standardField word))
    (hodd : ∀ word : Word, (∃ x ∈ word, x ≠ .three) →
      OddBlackNoRise (standardField word) (frameAt word).shortShift)
    (hbulk : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → Induction.S3NoFortInputs (frameAt word) (standardField word)) :
    OdometersTheorem := by
  have hpk := Induction.packet_standardField_of_inputs hstar hsheet
  refine odometersTheorem_of_packets (fun word _ => hpk word) ?_
  intro word hw
  exact Induction.starEstimates_of_inputs word hw (hpk (Induction.conjWord word)) (hpk word) (hstar word hw)
    (hsheet word hw) (harc word hw) (hodd word hw) (hbulk word hw)

/-- The packet induction with the powers of two as base cases, and the star estimates at the other proper words, give
`theorem:odometers`. The child of `2^(k+1)` is the base fraction `R(1/(2k+4))`, whose odometer theorem holds by
`odometersTheoremAt_base`, so its star estimates are not needed. -/
theorem odometersTheorem_of_packets_twos
    (hpacket : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → (frameAt word).Packet (standardField word))
    (hest : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word → StarEstimates word) :
    OdometersTheorem := by
  refine Induction.odometersTheorem_of_even ?_
  intro fraction hint hred heven
  obtain ⟨birth, hbirth, -⟩ := existsUnique_birth fraction hint hred
  obtain ⟨word, parity⟩ := birth
  have hparity : parity = Parity.even := by
    cases parity with
    | even => rfl
    | odd =>
      exfalso
      have hodd : fraction.Odd := by
        rw [← hbirth]
        exact (parentsAt_valid word).current_odd_parity
      unfold Fraction.Odd at hodd
      unfold Fraction.Even at heven
      omega
  subst hparity
  have hchild : (⟨parentsAt word, parentsAt_valid word⟩ : Induction.ChildFrame).child = fraction := hbirth
  by_cases hall : ∀ x ∈ word, x = .three
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, word = List.replicate k Digit.three :=
      ⟨word.length, List.eq_replicate_iff.mpr ⟨rfl, hall⟩⟩
    subst hk
    have hfr : fraction = ⟨1, 2 * (k : ℤ) + 3⟩ := by
      rw [← hchild]
      exact reciprocalFrame_child k
    rw [hfr]
    exact (odometersTheoremAt_base (by omega)).1
  · push Not at hall
    by_cases htw : Induction.IsTwoPow word
    · obtain ⟨k, hk⟩ := htw
      subst hk
      have hfr : fraction = Fraction.rotate ⟨1, 2 * (k : ℤ) + 4⟩ := by
        rw [← hchild]
        exact Induction.child_replicate_two_succ k
      rw [hfr]
      exact (odometersTheoremAt_base (d := 2 * (k : ℤ) + 4) (by omega)).2
    · have hp := hpacket word hall
      obtain ⟨hU, hNS, rank, hrank⟩ := hest word hall htw
      have key := Induction.ChildFrame.odometersTheoremAt_of_standard
        (⟨parentsAt word, parentsAt_valid word⟩ : Induction.ChildFrame) hp.periods hU hNS hrank
      rw [hchild] at key
      exact key

/-- `theorem:odometers` from the open local inputs at the proper words that are not powers of two, and the packets of the
powers of two. The old `odometersTheorem_of_openLocalInputs` is kept as it was. -/
theorem odometersTheorem_of_openLocalInputs_twos
    (htwo : ∀ k : ℕ, (frameAt (List.replicate (k + 1) Digit.two)).Packet
      (standardField (List.replicate (k + 1) Digit.two)))
    (hstar : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word → Induction.StarZoneInputs word)
    (hsheet : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      Induction.SheetLocalInputs word)
    (harc : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      Induction.VArcInputs (frameAt word) (standardField word))
    (hodd : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      OddBlackNoRise (standardField word) (frameAt word).shortShift)
    (hbulk : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      Induction.S3NoFortInputs (frameAt word) (standardField word)) :
    OdometersTheorem := by
  have hpk := Induction.packet_standardField_of_twos htwo hstar hsheet
  refine odometersTheorem_of_packets_twos (fun word _ => hpk word) ?_
  intro word hw htw
  exact Induction.starEstimates_of_inputs word hw (hpk (Induction.conjWord word)) (hpk word)
    (hstar word hw htw) (hsheet word hw htw) (harc word hw htw) (hodd word hw htw) (hbulk word hw htw)

/-- `theorem:odometers` from the open local inputs at the proper words that are not powers of two, with the powers of two
taken from the near-one constants: the periods of their standard fields, with the strip inputs and the polygon binarity
of those fields (`Induction.twos_packet_of_stripInputs`). -/
theorem odometersTheorem_of_nearOne_twos
    (hper : ∀ k : ℕ, HasGeneratorPeriods (frameAt (List.replicate (k + 1) Digit.two)).child
      (standardField (List.replicate (k + 1) Digit.two)) 0 (Construction.ladderEvenConstantV (2 * (k : ℤ) + 4)))
    (hS : ∀ k : ℕ, (frameAt (List.replicate (k + 1) Digit.two)).StripInputs
      (standardField (List.replicate (k + 1) Digit.two)))
    (hbin : ∀ k : ℕ, ∀ z ∈ (frameAt (List.replicate (k + 1) Digit.two)).closedPolygon,
      laplacian (standardField (List.replicate (k + 1) Digit.two)) z = -1 ∨
        laplacian (standardField (List.replicate (k + 1) Digit.two)) z = 0)
    (hstar : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word → Induction.StarZoneInputs word)
    (hsheet : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      Induction.SheetLocalInputs word)
    (harc : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      Induction.VArcInputs (frameAt word) (standardField word))
    (hodd : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      OddBlackNoRise (standardField word) (frameAt word).shortShift)
    (hbulk : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      Induction.S3NoFortInputs (frameAt word) (standardField word)) :
    OdometersTheorem :=
  odometersTheorem_of_openLocalInputs_twos
    (fun k => Induction.twos_packet_of_stripInputs k (hper k) (hS k) (hbin k)) hstar hsheet harc hodd hbulk

/-- `theorem:odometers` from the open local inputs at the proper words that are not powers of two. The powers of two are
the standard fields of `2^(k+1)`, identified with the physical near-one field on the whole plane
(`Induction.twos_standardField_eq_rotate`): their periods, reflection and binarity are proved, and only the zero and
harmonic strip facts on the closed polygon of `2^(k+1)` remain as the hypotheses `hzero`, `hharm`. -/
theorem odometersTheorem_of_nearOne_standard
    (hzero : ∀ k : ℕ, ∀ z ∈ (frameAt (List.replicate (k + 1) Digit.two)).closedPolygon,
      1 - (frameAt (List.replicate (k + 1) Digit.two)).child.den ≤
        (frameAt (List.replicate (k + 1) Digit.two)).tGrade z →
      standardField (List.replicate (k + 1) Digit.two) z = 0)
    (hharm : ∀ k : ℕ, ∀ z ∈ (frameAt (List.replicate (k + 1) Digit.two)).closedPolygon,
      (frameAt (List.replicate (k + 1) Digit.two)).sGrade z ≤
        2 * ((frameAt (List.replicate (k + 1) Digit.two)).child.den +
          (frameAt (List.replicate (k + 1) Digit.two)).child.num) - 1 →
      standardField (List.replicate (k + 1) Digit.two) z = harmonicGrid z)
    (hstar : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word → Induction.StarZoneInputs word)
    (hsheet : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      Induction.SheetLocalInputs word)
    (harc : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      Induction.VArcInputs (frameAt word) (standardField word))
    (hodd : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      OddBlackNoRise (standardField word) (frameAt word).shortShift)
    (hbulk : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      Induction.S3NoFortInputs (frameAt word) (standardField word)) :
    OdometersTheorem :=
  odometersTheorem_of_openLocalInputs_twos
    (fun k => Induction.twos_packet_standard k (hzero k) (hharm k)) hstar hsheet harc hodd hbulk

/-- `theorem:odometers` from the open local inputs at the proper words that are not powers of two. The powers of two are
now unconditional base words: their standard fields are the physical near-one field on the whole plane
(`Induction.twos_standardField_eq_rotate`), with the zero and harmonic strip facts on the closed polygon proved
(`Induction.twos_zero_strip`, `Induction.twos_harm_strip`). -/
theorem odometersTheorem_of_nearOne_unconditional
    (hstar : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word → Induction.StarZoneInputs word)
    (hsheet : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      Induction.SheetLocalInputs word)
    (harc : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      Induction.VArcInputs (frameAt word) (standardField word))
    (hodd : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      OddBlackNoRise (standardField word) (frameAt word).shortShift)
    (hbulk : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      Induction.S3NoFortInputs (frameAt word) (standardField word)) :
    OdometersTheorem :=
  odometersTheorem_of_openLocalInputs_twos
    (fun k => Induction.twos_packet_standard k
      (fun _ hz ht => Induction.twos_zero_strip k hz ht) (fun _ hz hs => Induction.twos_harm_strip k hz hs))
    hstar hsheet harc hodd hbulk

/-- `theorem:hyperbola` from the open inputs. -/
theorem hyperbola_of_openLocalInputs
    (hstar : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → Induction.StarZoneInputs word)
    (hsheet : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → Induction.SheetLocalInputs word)
    (harc : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → Induction.VArcInputs (frameAt word) (standardField word))
    (hodd : ∀ word : Word, (∃ x ∈ word, x ≠ .three) →
      OddBlackNoRise (standardField word) (frameAt word).shortShift)
    (hbulk : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → Induction.S3NoFortInputs (frameAt word) (standardField word))
    (t : ℝ) (ht : 0 ≤ t) (hu : t ≤ 1) :
    symmetricCircleMatrix t (1 - t) (-Real.sqrt (t ^ 2 + (1 - t) ^ 2)) ∈ frontier symmetricGrowthSet :=
  hyperbola_of_odometersTheorem (odometersTheorem_of_openLocalInputs hstar hsheet harc hodd hbulk) t ht hu

/-- `theorem:circle_packing` from the open inputs. -/
theorem circlePacking_of_openLocalInputs
    (hstar : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → Induction.StarZoneInputs word)
    (hsheet : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → Induction.SheetLocalInputs word)
    (harc : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → Induction.VArcInputs (frameAt word) (standardField word))
    (hodd : ∀ word : Word, (∃ x ∈ word, x ≠ .three) →
      OddBlackNoRise (standardField word) (frameAt word).shortShift)
    (hbulk : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → Induction.S3NoFortInputs (frameAt word) (standardField word))
    (matrix : Matrix (Fin 2) (Fin 2) ℝ) :
    matrix ∈ integerSuperharmonicMatrices ↔ ∃ s t : ℤ, (harmonicPeak s t - matrix).PosSemidef :=
  circlePacking_of_odometersTheorem (odometersTheorem_of_openLocalInputs hstar hsheet harc hodd hbulk) matrix

end FLatticePaper
