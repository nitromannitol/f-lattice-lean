import FLatticePaper.Plane.Induction.TieReduce
import FLatticePaper.Plane.Induction.HResPWire
import FLatticePaper.Plane.Induction.HResNCases
import FLatticePaper.Plane.Induction.OddBlackStep

/-! # The tie case of the raw-slip permit, with no named input from the resonance premises

`TieReduce.tie_excluded_of_narrow` takes the two resonance premises `hResP` and `hResN` as arguments. Here they are discharged:
the slip range from the conjugate's strong estimates (`TieReduce.slipRange_of_strong`), the unseeded premise `hQ21` from the
conjugate's old-policy data (`OddBlackStep.hQ21_of_old`), `hResP` from `hQ21` (`HResPWire.hResP_of_Q21`), the negative tie from
`hQ21` (`HResPWire.hNegTie_of_Q21`), and `hResN` from the negative tie (`HResNCases.hResN_of_cases`). -/

namespace FLatticePaper.TieAssembled

open Farey FLatticePaper FLatticePaper.Induction

/-- **The tie case, assembled.** A rising black pair for `σ` with a tie (`Ψ(c) = 0` or `Ψ(i) = 0`) at a point of the polygon is
impossible. The inputs are the word's strong estimates on the conjugate, the packet, the seed fields and the old-policy data. -/
theorem tie_excluded_assembled {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hE : StrongEstimates word) (hEc : StrongEstimates (conjWord word))
    (hpk : (frameAt word).Packet (standardField word))
    (hpar : FLatticePaper.W1Seeds.SeedFields (conjWord word))
    {seed : Site → Site → Prop}
    (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
      (standardField (conjWord word))) :
    ∀ c i, RisingBlackPair (standardField word) (frameAt word).shortShift c i →
      c ∈ (frameAt word).closedPolygon → (sheetDiffW word c = 0 ∨ sheetDiffW word i = 0) → False := by
  have hslip := slipRange_of_strong h hEc
  have hQ21 := FLatticePaper.OddBlackStep.hQ21_of_old h hEc hpk P hslip
  have hResP := hResP_of_Q21 h hE hEc hpar P hW1 hQ21
  have hNegTie := hNegTie_of_Q21 h hE hEc hpar P hW1 hQ21
  have hResN : ∀ c i, RisingBlackPair (standardField word) (-(frameAt word).shortShift) c i →
      c ∈ (frameAt word).closedPolygon → (c + (frameAt word).uq ∈ (frameAt word).closedPolygon ∧
        i + (frameAt word).uq ∈ (frameAt word).closedPolygon) →
      sheetDiffW word c = 0 → (∃ j, FLatticePaper.Edge j c ∧ sheetDiffW word j = -1) → False :=
    fun c i hr hcE hcu hΨc hj => hResN_of_cases h hEc hpk P hNegTie hr hcE hcu.1 hcu.2 hΨc hj
  exact tie_excluded_of_narrow h hEc hpk P hResP hResN

end FLatticePaper.TieAssembled
