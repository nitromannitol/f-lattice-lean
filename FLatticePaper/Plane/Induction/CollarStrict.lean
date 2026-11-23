import FLatticePaper.Plane.Induction.CollarTop
import FLatticePaper.Plane.Induction.CollarOneOne
import FLatticePaper.Plane.Induction.W1NonfreeHsqC
import FLatticePaper.Plane.Induction.CollarGlue
import FLatticePaper.Plane.Induction.CollarLeft
import FLatticePaper.Plane.Induction.CollarRight
import FLatticePaper.Plane.Induction.ChildNumerator

/-! Task 72 (hcollar, band (a)): the `collarBase` split for `hstrict`.

The bottom and top classes are proved (`bottom_square_strict`, `top_square_strict`). The black exclusions come from the
laplacian: `laplacian (MW word) (1, 1) = −1`, and the centre reflection preserves the laplacian (`lap_MW_reflect`), so
`R − c ≠ (1, 1)` for a laplacian-0 centre. The left and right classes are the named inputs `hL` and `hR`. -/

namespace FLatticePaper.CollarStrict

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1 FLatticePaper.W1Phase FLatticePaper.W1MSheet
  FLatticePaper.W1Step FLatticePaper.W1CollarFrame FLatticePaper.AndOrRank FLatticePaper.CollarGlue
  FLatticePaper.CollarBottomSquare FLatticePaper.CollarTop FLatticePaper.W1NonfreeHsqNonneg
  FLatticePaper.CollarLeft FLatticePaper.CollarRight

/-- `hstrict` for a word: the bottom, top, left and right classes (`collarBase`). -/
theorem hstrict_of_strong {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) :
    ∀ c, StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      CollarFrame (frameAt word) c → laplacian (MW word) c = 0 →
        ∀ c' ∈ collarSquare (frameAt word) c,
          StrictInterior (frameAt word).child.num (frameAt word).child.den c' := by
  intro c hcS hcol hM
  have hn3 : 3 ≤ (frameAt word).child.num := FLatticePaper.Induction.child_num_ge_three hw
  have hne : c ≠ (1, 1) := by
    rintro rfl
    have h1 := FLatticePaper.Induction.laplacian_MW_one_one hw hSE
    rw [hM] at h1
    norm_num at h1
  unfold collarSquare collarBase
  split_ifs with hB hT hLf
  · exact bottom_square_strict (frameAt word) hcS hne hB
  · have hne' : (frameAt word).centre - c ≠ (1, 1) := by
      intro h
      have h1 := FLatticePaper.W1NonfreeHsqC.lap_MW_reflect hw hSE c
      rw [h, FLatticePaper.Induction.laplacian_MW_one_one hw hSE, hM] at h1
      norm_num at h1
    exact top_square_strict (frameAt word) hcS hne' hT
  · exact left_square_strict (frameAt word) hn3 hcS hB hT hLf
  · exact right_square_strict (frameAt word) hn3 hcS hB hT
      (FLatticePaper.CollarRight.rightArc_of_collarFrame (frameAt word) hcol hB hT hLf)

/-- `hcollar` for a word, from the inherited chains (the strict-centre premise is the collar's own). -/
theorem hcollar_discharged {word : Word} {seed : Site → Site → Prop}
    (P : OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed)
    (chains : CollarChains word P)
    (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word)) :
    ∀ c : Site, StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      laplacian (MW word) c = 0 → CollarFrame (frameAt word) c → HsqAt word P c :=
  hcollar_of_chains P chains (hstrict_of_strong hw hSE)

end FLatticePaper.CollarStrict
