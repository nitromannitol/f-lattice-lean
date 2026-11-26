import FLatticePaper.Plane.Induction.PsiFromOpposite
import FLatticePaper.Plane.Induction.OppMain

/-! # The face sign `Ψ` from the packet alone

`PsiFaceSign word` (`Ψ ≥ 0` on the bottom or aligned face, `Ψ ≤ 0` on the top or opposite face) is obtained from the top half
(`TopPsi`, through `PsiFromOpposite.psiFaceSign_of_opposite`) and the opposite half (`OppMain.opposite_sheetPsi`). The
hypotheses are exactly those the packet supplies: the word's strong core, the seeds of the word and of its conjugate, the strong
estimates of the conjugate, the word's non-triviality, and `3 ≤ num`. -/

namespace FLatticePaper.PsiPacket

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1Seeds FLatticePaper.FaceWitness

/-- **The face sign from the packet.** -/
theorem psiFaceSign_of_packet {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hS : StrongCore word)
    (hpw : SeedFields word) (hSE : StrongEstimates (conjWord word)) (hpc : SeedFields (conjWord word))
    (hn3 : 3 ≤ (frameAt word).child.num) : PsiFaceSign word :=
  FLatticePaper.PsiFromOpposite.psiFaceSign_of_opposite hw hSE hpc hn3
    (fun c hc _ _ hopp => FLatticePaper.OppMain.opposite_sheetPsi hw hS hpw hpc hSE hn3 c hc hopp)

end FLatticePaper.PsiPacket
