import FLatticePaper.MainTheorems
import FLatticePaper.Plane.Induction.I3CSheet
import FLatticePaper.Plane.Induction.StrongProducer

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

end FLatticePaper
