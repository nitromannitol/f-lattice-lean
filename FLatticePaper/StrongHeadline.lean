import FLatticePaper.MainTheorems
import FLatticePaper.Plane.Induction.I3CSheet
import FLatticePaper.Plane.Induction.StrongProducer
import FLatticePaper.Plane.Induction.StrongInduction
import FLatticePaper.Plane.Induction.BaseFields
import FLatticePaper.Plane.Induction.StrongBridge
import FLatticePaper.Plane.Induction.TieReduce
import FLatticePaper.Plane.Induction.StrongCoreDef

/-! Task 39, step 1: the odometers theorem from the strong estimates of the conjugate words.

The sheet inputs `SheetLocalInputs w` at a proper word `w` (not a power of two) follow from `StrongEstimates (conjWord w)` by
`i3_sheetLocalInputs_of_strong`, so the headline needs the strong estimates of the earlier word in place of the sheet inputs. -/

namespace FLatticePaper

open Farey Induction

/-- **The odometers theorem from the strong estimates of the conjugate words** (the sheet inputs are derived from them). -/
theorem odometersTheorem_of_strong
    (hstrong : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      Induction.StrongEstimates (Induction.conjWord word))
    (hstar : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word → Induction.StarZoneInputs word)
    (harc : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      Induction.VArcInputs (frameAt word) (standardField word))
    (hodd : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      OddBlackNoRise (standardField word) (frameAt word).shortShift)
    (hbulk : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      Induction.S3NoFortInputs (frameAt word) (standardField word)) :
    OdometersTheorem :=
  odometersTheorem_of_nearOne_unconditional hstar
    (fun word hw hn => Induction.i3_sheetLocalInputs_of_strong hw (hstrong word hw hn)) harc hodd hbulk

/-- **The odometers theorem from the producer** (task 39): at every proper word that is not a power of two, the strong estimates
of the conjugate word are the packet of its standard field together with the open part `StrongProducer`. -/
theorem odometersTheorem_of_producer
    (hpk : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      (frameAt (Induction.conjWord word)).Packet (standardField (Induction.conjWord word)))
    (hprod : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      Induction.StrongProducer (Induction.conjWord word))
    (hstar : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word → Induction.StarZoneInputs word)
    (harc : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      Induction.VArcInputs (frameAt word) (standardField word))
    (hodd : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      OddBlackNoRise (standardField word) (frameAt word).shortShift)
    (hbulk : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      Induction.S3NoFortInputs (frameAt word) (standardField word)) :
    OdometersTheorem :=
  odometersTheorem_of_strong
    (fun word hw hn => Induction.StrongEstimates.of_producer (hpk word hw hn) (hprod word hw hn)) hstar harc hodd hbulk

/-- **The odometers theorem from the residual** (task 40): the strong estimates of every word follow from the pure words, the
two-powers and the residual at every proper non-two-power word, by the word induction. -/
theorem odometersTheorem_of_residual
    (hpure : ∀ k : ℕ, Induction.StrongEstimates (List.replicate k Digit.three))
    (htwo : ∀ k : ℕ, Induction.StrongEstimates (List.replicate (k + 1) Digit.two))
    (hres : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word → Induction.StrongResidual word)
    (hstar : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word → Induction.StarZoneInputs word)
    (harc : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      Induction.VArcInputs (frameAt word) (standardField word))
    (hodd : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      OddBlackNoRise (standardField word) (frameAt word).shortShift)
    (hbulk : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      Induction.S3NoFortInputs (frameAt word) (standardField word)) :
    OdometersTheorem :=
  odometersTheorem_of_strong
    (fun word _ _ => Induction.strongEstimates_of_all hpure htwo hres hstar harc (Induction.conjWord word))
    hstar harc hodd hbulk

/-- **The odometers theorem from the named base inputs** (task 41): the base words `3^k` and `2^(k+1)` need only their slip
fields and their residual; their packets are proved. -/
theorem odometersTheorem_of_base
    (hpureSlip : ∀ k : ℕ, Induction.BaseSlip (List.replicate k Digit.three))
    (hpureRes : ∀ k : ℕ, Induction.StrongResidual (List.replicate k Digit.three))
    (htwoSlip : ∀ k : ℕ, Induction.BaseSlip (List.replicate (k + 1) Digit.two))
    (htwoRes : ∀ k : ℕ, Induction.StrongResidual (List.replicate (k + 1) Digit.two))
    (hres : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word → Induction.StrongResidual word)
    (hstar : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word → Induction.StarZoneInputs word)
    (harc : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      Induction.VArcInputs (frameAt word) (standardField word))
    (hodd : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      OddBlackNoRise (standardField word) (frameAt word).shortShift)
    (hbulk : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      Induction.S3NoFortInputs (frameAt word) (standardField word)) :
    OdometersTheorem :=
  odometersTheorem_of_residual
    (fun k => Induction.StrongEstimates.of_base_pure k (hpureSlip k) (hpureRes k))
    (fun k => Induction.StrongEstimates.of_base_two k (htwoSlip k) (htwoRes k))
    hres hstar harc hodd hbulk

/-- The star estimates of a proper word from its own strong estimates, with the odd black no-rise and the S3 inputs. -/
theorem starEstimates_of_strong {word : Word} (hS : StrongCore word)
    (hodd : OddBlackNoRise (standardField word) (frameAt word).shortShift)
    (hS3n : S3NoFortInputs (frameAt word) (standardField word)) : StarEstimates word := by
  have hS3p := permitLocal_of_star_data (evenSite_shortShift (frameAt word)) hS.packet.binary hS.F1_unitSlip
    hS.F1_noSlipSaddle hodd
  have hno := restrictedNoFort_S3_of_inputs (frameAt word) hS.packet.periods hS.packet.binary hS3p hS3n
  obtain ⟨rank, hrank⟩ := S3_of_packet_restrictedNoFort word hS.packet hS3p hno
  unfold StarEstimates
  exact ⟨hS.F1_unitSlip, hS.F1_noSlipSaddle, rank, hrank⟩


/-- **The odometers theorem from the named base inputs and the residuals, with no star-zone or arc inputs** (task 50): the base
words `3^k` and `2^(k+1)` need only their slip fields and residuals; the strong estimates of every word follow by the word
induction (`strongEstimates_of_residual_all`), and the star estimates come from the strong estimates with the odd black
no-rise and the S3 inputs. -/
theorem odometersTheorem_of_strongResidual
    (hpureSlip : ∀ k : ℕ, Induction.BaseSlip (List.replicate k Digit.three))
    (hpureRes : ∀ k : ℕ, Induction.StrongResidual (List.replicate k Digit.three))
    (htwoSlip : ∀ k : ℕ, Induction.BaseSlip (List.replicate (k + 1) Digit.two))
    (htwoRes : ∀ k : ℕ, Induction.StrongResidual (List.replicate (k + 1) Digit.two))
    (hres : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word → Induction.StrongResidual word)
    (hodd : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      OddBlackNoRise (standardField word) (frameAt word).shortShift)
    (hbulk : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      Induction.S3NoFortInputs (frameAt word) (standardField word)) :
    OdometersTheorem := by
  have hE : ∀ word : Word, Induction.StrongEstimates word :=
    Induction.strongEstimates_of_residual_all
      (fun k => Induction.StrongEstimates.of_base_pure k (hpureSlip k) (hpureRes k))
      (fun k => Induction.StrongEstimates.of_base_two k (htwoSlip k) (htwoRes k)) hres
  exact odometersTheorem_of_packets_twos (fun word _ => (hE word).packet)
    (fun word hw hn => starEstimates_of_strong (hE word) (hodd word hw hn) (hbulk word hw hn))

/-- **`theorem:hyperbola` from the strong headline** (task 50): the hyperbola boundary, with no star-zone or arc inputs. -/
theorem hyperbola_of_strongResidual
    (hpureSlip : ∀ k : ℕ, Induction.BaseSlip (List.replicate k Digit.three))
    (hpureRes : ∀ k : ℕ, Induction.StrongResidual (List.replicate k Digit.three))
    (htwoSlip : ∀ k : ℕ, Induction.BaseSlip (List.replicate (k + 1) Digit.two))
    (htwoRes : ∀ k : ℕ, Induction.StrongResidual (List.replicate (k + 1) Digit.two))
    (hres : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word → Induction.StrongResidual word)
    (hodd : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      OddBlackNoRise (standardField word) (frameAt word).shortShift)
    (hbulk : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      Induction.S3NoFortInputs (frameAt word) (standardField word))
    (t : ℝ) (ht : 0 ≤ t) (hu : t ≤ 1) :
    symmetricCircleMatrix t (1 - t) (-Real.sqrt (t ^ 2 + (1 - t) ^ 2)) ∈ frontier symmetricGrowthSet :=
  hyperbola_of_odometersTheorem
    (odometersTheorem_of_strongResidual hpureSlip hpureRes htwoSlip htwoRes hres hodd hbulk) t ht hu

/-- **`theorem:circle_packing` from the strong headline** (task 50): the integer superharmonic matrices, with no star-zone or
arc inputs. -/
theorem circlePacking_of_strongResidual
    (hpureSlip : ∀ k : ℕ, Induction.BaseSlip (List.replicate k Digit.three))
    (hpureRes : ∀ k : ℕ, Induction.StrongResidual (List.replicate k Digit.three))
    (htwoSlip : ∀ k : ℕ, Induction.BaseSlip (List.replicate (k + 1) Digit.two))
    (htwoRes : ∀ k : ℕ, Induction.StrongResidual (List.replicate (k + 1) Digit.two))
    (hres : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word → Induction.StrongResidual word)
    (hodd : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      OddBlackNoRise (standardField word) (frameAt word).shortShift)
    (hbulk : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      Induction.S3NoFortInputs (frameAt word) (standardField word))
    (matrix : Matrix (Fin 2) (Fin 2) ℝ) :
    matrix ∈ integerSuperharmonicMatrices ↔ ∃ s t : ℤ, (harmonicPeak s t - matrix).PosSemidef :=
  circlePacking_of_odometersTheorem
    (odometersTheorem_of_strongResidual hpureSlip hpureRes htwoSlip htwoRes hres hodd hbulk) matrix

/-- **The odometers theorem with the odd black no-rise discharged** (task 70): the odd black no-rise at each proper word is
`oddBlackNoRise_of_narrow`, from the conjugate's policy and the two narrowed tie leaves; the rest as in
`odometersTheorem_of_strongResidual`. -/
theorem odometersTheorem_of_policy
    (hpureSlip : ∀ k : ℕ, Induction.BaseSlip (List.replicate k Digit.three))
    (hpureRes : ∀ k : ℕ, Induction.StrongResidual (List.replicate k Digit.three))
    (htwoSlip : ∀ k : ℕ, Induction.BaseSlip (List.replicate (k + 1) Digit.two))
    (htwoRes : ∀ k : ℕ, Induction.StrongResidual (List.replicate (k + 1) Digit.two))
    (hres : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word → Induction.StrongResidual word)
    (hpol : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      ∃ seed, Nonempty (Induction.OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed
        (frameAt word).eps))
    (hResP : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      ∀ c i, RisingBlackPair (standardField word) (frameAt word).shortShift c i →
        c ∈ (frameAt word).closedPolygon →
        (c - (frameAt word).uq ∈ (frameAt word).closedPolygon ∧ i - (frameAt word).uq ∈ (frameAt word).closedPolygon) →
        sheetDiffW word c = 0 → (∃ j, FLatticePaper.Edge j c ∧ sheetDiffW word j = -1) → False)
    (hResN : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      ∀ c i, RisingBlackPair (standardField word) (-(frameAt word).shortShift) c i →
        c ∈ (frameAt word).closedPolygon →
        (c + (frameAt word).uq ∈ (frameAt word).closedPolygon ∧ i + (frameAt word).uq ∈ (frameAt word).closedPolygon) →
        sheetDiffW word c = 0 → (∃ j, FLatticePaper.Edge j c ∧ sheetDiffW word j = -1) → False)
    (hbulk : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      Induction.S3NoFortInputs (frameAt word) (standardField word)) :
    OdometersTheorem := by
  have hE : ∀ word : Word, Induction.StrongEstimates word :=
    Induction.strongEstimates_of_residual_all
      (fun k => Induction.StrongEstimates.of_base_pure k (hpureSlip k) (hpureRes k))
      (fun k => Induction.StrongEstimates.of_base_two k (htwoSlip k) (htwoRes k)) hres
  have hodd : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      OddBlackNoRise (standardField word) (frameAt word).shortShift := by
    intro word hw hn
    obtain ⟨seed, ⟨P⟩⟩ := hpol word hw hn
    exact Induction.oddBlackNoRise_of_narrow hw (hE (conjWord word)) P (hResP word hw hn) (hResN word hw hn)
  exact odometersTheorem_of_strongResidual hpureSlip hpureRes htwoSlip htwoRes hres hodd hbulk

/-- **`theorem:hyperbola` from the policy headline** (task 70). -/
theorem hyperbola_of_policy
    (hpureSlip : ∀ k : ℕ, Induction.BaseSlip (List.replicate k Digit.three))
    (hpureRes : ∀ k : ℕ, Induction.StrongResidual (List.replicate k Digit.three))
    (htwoSlip : ∀ k : ℕ, Induction.BaseSlip (List.replicate (k + 1) Digit.two))
    (htwoRes : ∀ k : ℕ, Induction.StrongResidual (List.replicate (k + 1) Digit.two))
    (hres : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word → Induction.StrongResidual word)
    (hpol : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      ∃ seed, Nonempty (Induction.OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed
        (frameAt word).eps))
    (hResP : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      ∀ c i, RisingBlackPair (standardField word) (frameAt word).shortShift c i →
        c ∈ (frameAt word).closedPolygon →
        (c - (frameAt word).uq ∈ (frameAt word).closedPolygon ∧ i - (frameAt word).uq ∈ (frameAt word).closedPolygon) →
        sheetDiffW word c = 0 → (∃ j, FLatticePaper.Edge j c ∧ sheetDiffW word j = -1) → False)
    (hResN : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      ∀ c i, RisingBlackPair (standardField word) (-(frameAt word).shortShift) c i →
        c ∈ (frameAt word).closedPolygon →
        (c + (frameAt word).uq ∈ (frameAt word).closedPolygon ∧ i + (frameAt word).uq ∈ (frameAt word).closedPolygon) →
        sheetDiffW word c = 0 → (∃ j, FLatticePaper.Edge j c ∧ sheetDiffW word j = -1) → False)
    (hbulk : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      Induction.S3NoFortInputs (frameAt word) (standardField word))
    (t : ℝ) (ht : 0 ≤ t) (hu : t ≤ 1) :
    symmetricCircleMatrix t (1 - t) (-Real.sqrt (t ^ 2 + (1 - t) ^ 2)) ∈ frontier symmetricGrowthSet :=
  hyperbola_of_odometersTheorem
    (odometersTheorem_of_policy hpureSlip hpureRes htwoSlip htwoRes hres hpol hResP hResN hbulk) t ht hu

/-- **`theorem:circle_packing` from the policy headline** (task 70). -/
theorem circlePacking_of_policy
    (hpureSlip : ∀ k : ℕ, Induction.BaseSlip (List.replicate k Digit.three))
    (hpureRes : ∀ k : ℕ, Induction.StrongResidual (List.replicate k Digit.three))
    (htwoSlip : ∀ k : ℕ, Induction.BaseSlip (List.replicate (k + 1) Digit.two))
    (htwoRes : ∀ k : ℕ, Induction.StrongResidual (List.replicate (k + 1) Digit.two))
    (hres : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word → Induction.StrongResidual word)
    (hpol : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      ∃ seed, Nonempty (Induction.OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed
        (frameAt word).eps))
    (hResP : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      ∀ c i, RisingBlackPair (standardField word) (frameAt word).shortShift c i →
        c ∈ (frameAt word).closedPolygon →
        (c - (frameAt word).uq ∈ (frameAt word).closedPolygon ∧ i - (frameAt word).uq ∈ (frameAt word).closedPolygon) →
        sheetDiffW word c = 0 → (∃ j, FLatticePaper.Edge j c ∧ sheetDiffW word j = -1) → False)
    (hResN : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      ∀ c i, RisingBlackPair (standardField word) (-(frameAt word).shortShift) c i →
        c ∈ (frameAt word).closedPolygon →
        (c + (frameAt word).uq ∈ (frameAt word).closedPolygon ∧ i + (frameAt word).uq ∈ (frameAt word).closedPolygon) →
        sheetDiffW word c = 0 → (∃ j, FLatticePaper.Edge j c ∧ sheetDiffW word j = -1) → False)
    (hbulk : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      Induction.S3NoFortInputs (frameAt word) (standardField word))
    (matrix : Matrix (Fin 2) (Fin 2) ℝ) :
    matrix ∈ integerSuperharmonicMatrices ↔ ∃ s t : ℤ, (harmonicPeak s t - matrix).PosSemidef :=
  circlePacking_of_odometersTheorem
    (odometersTheorem_of_policy hpureSlip hpureRes htwoSlip htwoRes hres hpol hResP hResN hbulk) matrix

end FLatticePaper
