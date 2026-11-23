import FLatticePaper.Plane.Induction.CollarTop
import FLatticePaper.Plane.Induction.CollarOneOne
import FLatticePaper.Plane.Induction.W1NonfreeHsqC
import FLatticePaper.Plane.Induction.CollarGlue

/-! Task 72 (hcollar, band (a)): the `collarBase` split for `hstrict`.

The bottom and top classes are proved (`bottom_square_strict`, `top_square_strict`). The black exclusions come from the
laplacian: `laplacian (MW word) (1, 1) = −1`, and the centre reflection preserves the laplacian (`lap_MW_reflect`), so
`R − c ≠ (1, 1)` for a laplacian-0 centre. The left and right classes are the named inputs `hL` and `hR`. -/

namespace FLatticePaper.CollarStrict

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1 FLatticePaper.W1Phase FLatticePaper.W1MSheet
  FLatticePaper.W1Step FLatticePaper.W1CollarFrame FLatticePaper.AndOrRank FLatticePaper.CollarGlue
  FLatticePaper.CollarBottomSquare FLatticePaper.CollarTop FLatticePaper.W1NonfreeHsqNonneg

/-- `hstrict` for a word, from the left and right class inputs. -/
theorem hstrict_of_strong {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word))
    (hL : ∀ c, StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      CollarFrame (frameAt word) c → laplacian (MW word) c = 0 → ¬ BottomArc (frameAt word) c →
        ¬ TopArc (frameAt word) c → LeftArc (frameAt word) c →
        ∀ c' ∈ squareCorners c.1 c.2, StrictInterior (frameAt word).child.num (frameAt word).child.den c')
    (hR : ∀ c, StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      CollarFrame (frameAt word) c → laplacian (MW word) c = 0 → ¬ BottomArc (frameAt word) c →
        ¬ TopArc (frameAt word) c → ¬ LeftArc (frameAt word) c →
        ∀ c' ∈ squareCorners (c.1 - 1) (c.2 - 1),
          StrictInterior (frameAt word).child.num (frameAt word).child.den c') :
    ∀ c, StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      CollarFrame (frameAt word) c → laplacian (MW word) c = 0 →
        ∀ c' ∈ collarSquare (frameAt word) c,
          StrictInterior (frameAt word).child.num (frameAt word).child.den c' := by
  intro c hcS hcol hM
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
  · exact hL c hcS hcol hM hB hT hLf
  · exact hR c hcS hcol hM hB hT hLf

/-- `hcollar` for a word, from the inherited chains and the left and right class inputs. -/
theorem hcollar_discharged {word : Word} {seed : Site → Site → Prop}
    (P : OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed)
    (chains : CollarChains word P)
    (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hL : ∀ c, StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      CollarFrame (frameAt word) c → laplacian (MW word) c = 0 → ¬ BottomArc (frameAt word) c →
        ¬ TopArc (frameAt word) c → LeftArc (frameAt word) c →
        ∀ c' ∈ squareCorners c.1 c.2, StrictInterior (frameAt word).child.num (frameAt word).child.den c')
    (hR : ∀ c, StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      CollarFrame (frameAt word) c → laplacian (MW word) c = 0 → ¬ BottomArc (frameAt word) c →
        ¬ TopArc (frameAt word) c → ¬ LeftArc (frameAt word) c →
        ∀ c' ∈ squareCorners (c.1 - 1) (c.2 - 1),
          StrictInterior (frameAt word).child.num (frameAt word).child.den c') :
    ∀ c : Site, StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      laplacian (MW word) c = 0 → CollarFrame (frameAt word) c → HsqAt word P c :=
  hcollar_of_chains P chains (hstrict_of_strong hw hSE hL hR)

end FLatticePaper.CollarStrict
