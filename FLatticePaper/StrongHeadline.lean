import FLatticePaper.MainTheorems
import FLatticePaper.Plane.Induction.I3CSheet
import FLatticePaper.Plane.Induction.StrongProducer
import FLatticePaper.Plane.Induction.StrongInduction
import FLatticePaper.Plane.Induction.BaseFields

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

end FLatticePaper
