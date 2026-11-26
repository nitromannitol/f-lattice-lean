import FLatticePaper.Plane.Induction.PsiSign
import FLatticePaper.Plane.Induction.TopPsi

/-! # `PsiFaceSign` from the opposite half (wiring)

`PsiSign.psiFaceSign_of_top` needs `Ψ ≤ 0` on the top or the opposite witnesses. The top half is `TopPsi.top_sheetPsi_le`;
the opposite half is the explicit hypothesis `hopp` (proved in `OppositePsi` once it is available). -/

namespace FLatticePaper.PsiFromOpposite

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1 FLatticePaper.W1Step FLatticePaper.FaceWitness FLatticePaper.W1MSheet FLatticePaper.W1CollarFrame

/-- **`PsiFaceSign` from the opposite half**: the top half is proved, the opposite half is the input `hopp`. -/
theorem psiFaceSign_of_opposite {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpar : FLatticePaper.W1Seeds.SeedFields (conjWord word))
    (hn3 : 3 ≤ (frameAt word).child.num)
    (hopp : ∀ c : Site, FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      laplacian (MW word) c = 0 → CollarFrame (frameAt word) c → OppositeWit (frameAt word) c →
        sheetPsi word c ≤ 0) :
    PsiFaceSign word :=
  FLatticePaper.PsiSign.psiFaceSign_of_top hw hSE (fun c hc hM hCF h => by
    rcases h with hT | hO
    · exact FLatticePaper.TopPsi.top_sheetPsi_le hw hSE hpar hn3 hc hT
    · exact hopp c hc hM hCF hO)

end FLatticePaper.PsiFromOpposite
