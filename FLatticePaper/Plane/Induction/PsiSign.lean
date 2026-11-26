import FLatticePaper.Plane.Induction.W1NonfreeHsqC
import FLatticePaper.Plane.Induction.CollarCReflect
import FLatticePaper.Plane.Induction.CollarTop
import FLatticePaper.Plane.Induction.FaceReflect
import FLatticePaper.Plane.Induction.PairClass
import FLatticePaper.Plane.Induction.FaceWitness

/-! # `PsiFaceSign` from its top and opposite half

`PsiFaceSign word` asserts `0 ≤ Ψ` on the bottom and aligned faces and `Ψ ≤ 0` on the top and opposite faces, where
`Ψ = sheetPsi word` is the difference `C − A` of the sheets. The reflection `z ↦ R − z` (the centre of the child frame)
exchanges bottom with top and aligned with opposite, keeps the collar, the strictness and the white colour, and
negates `Ψ` (`psi_reflect`). So the bottom and aligned halves follow from the top and opposite halves, which are the
named input `htop` (the audit's identity `C = F` on the top and opposite collars). -/

namespace FLatticePaper.PsiSign

open FLatticePaper FLatticePaper.FaceWitness FLatticePaper.FaceReflect FLatticePaper.CollarTop
  FLatticePaper.CollarCReflect FLatticePaper.W1NonfreeHsqC FLatticePaper.PairClass FLatticePaper.W1CollarFrame
  FLatticePaper.W1 FLatticePaper.Induction FLatticePaper.Farey FLatticePaper.W1MSheet
  FLatticePaper.W1Step

/-- An aligned witness of `c` is an opposite witness of the reflected centre. -/
theorem aligned_opposite (frame : FLatticePaper.Induction.ChildFrame) {c : Site} (h : AlignedWit frame c) :
    OppositeWit frame (frame.centre - c) := by
  rcases h with ⟨he, hL⟩ | ⟨he, hR⟩
  · exact Or.inl ⟨he, leftWit_rightWit frame hL⟩
  · exact Or.inr ⟨he, rightWit_leftWit frame hR⟩

/-- **`PsiFaceSign` from the top and opposite half.** The hypothesis `htop` is the sign `Ψ ≤ 0` on the top and opposite
collar; the bottom and aligned signs are its reflection. -/
theorem psiFaceSign_of_top {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word))
    (htop : ∀ c : Site,
      FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c →
        laplacian (MW word) c = 0 → CollarFrame (frameAt word) c →
        (TopWit (frameAt word) c ∨ OppositeWit (frameAt word) c) → sheetPsi word c ≤ 0) :
    PsiFaceSign word := by
  intro c hc hM hCF
  constructor
  · rintro (hB | hA)
    · have h := htop ((frameAt word).centre - c)
        ((strict_reflect_centre (frameAt word) c).mpr hc)
        (by rw [lap_MW_reflect hw hSE c]; exact hM)
        (collar_reflect hw hCF)
        (Or.inl (bottomTop_witness (frameAt word) hB))
      rw [psi_reflect hw hSE c] at h
      linarith
    · have h := htop ((frameAt word).centre - c)
        ((strict_reflect_centre (frameAt word) c).mpr hc)
        (by rw [lap_MW_reflect hw hSE c]; exact hM)
        (collar_reflect hw hCF)
        (Or.inr (aligned_opposite (frameAt word) hA))
      rw [psi_reflect hw hSE c] at h
      linarith
  · intro h
    exact htop c hc hM hCF h

end FLatticePaper.PsiSign
