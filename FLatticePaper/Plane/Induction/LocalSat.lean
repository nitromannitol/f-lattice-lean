import FLatticePaper.Plane.Induction.W1MRank
import FLatticePaper.Plane.Induction.SheetPieces
import FLatticePaper.Plane.Induction.TransferW1

/-! # A local satisfying selection of the standard field on the strict interior

`HasSatOn Q F` is the satisfying-selection clause (W) of `F` restricted to the unit squares whose corners all lie in `Q`
(the white selection is required everywhere). Where `F` agrees with a field `M` satisfying (W) on the sites that enter the
Laplacians and the clauses, the local clause is inherited from `M`. For `Q = StrictInterior` the agreement is
`standardField word = sheetMin` on the closed polygon, and the stars of strict interior sites lie in the closed polygon
(`TransferW1.strictInterior_star`). -/

namespace FLatticePaper.LocalSat

open Farey FLatticePaper FLatticePaper.SquareClauses FLatticePaper.AndOrRank FLatticePaper.Induction

/-- (W) on the unit squares whose corners lie in `Q`: a white selection satisfying the clauses of those squares. -/
def HasSatOn (Q : Site → Prop) (F : Field) : Prop :=
  ∃ sel : Site → Site, (∀ c, laplacian F c = 0 → sel c = incomingNeg c ∨ sel c = incomingPos c) ∧
    ∀ a b : ℤ, (∀ x ∈ squareCorners a b, Q x) → SquareClauseSat F sel a b

/-- The Laplacian at `c` reads only `c` and its two inputs, so fields agreeing there have equal Laplacians. -/
theorem laplacian_congr_star {F M : Field} {c : Site}
    (h₁ : F (incomingNeg c) = M (incomingNeg c)) (h₂ : F c = M c) (h₃ : F (incomingPos c) = M (incomingPos c)) :
    laplacian F c = laplacian M c := by
  unfold laplacian
  rw [h₁, h₂, h₃]

/-- **Local (W) from a global one.** If `F` agrees with `M` on `P` and every site of `Q` has its star in `P`, then the
satisfying selection of `M` gives a white selection satisfying the clauses of `F` on the squares with corners in `Q`. -/
theorem hasSatOn_of_agree {F M : Field} {Q P : Site → Prop} (hP : ∀ z, P z → F z = M z)
    (hQ : ∀ c, Q c → P c ∧ P (incomingNeg c) ∧ P (incomingPos c)) (hM : HasSatSelection M) : HasSatOn Q F := by
  classical
  obtain ⟨selM, hselM, hsqM⟩ := hM
  have hl : ∀ c, Q c → laplacian F c = laplacian M c := by
    intro c hc
    obtain ⟨h1, h2, h3⟩ := hQ c hc
    exact laplacian_congr_star (hP _ h2) (hP _ h1) (hP _ h3)
  refine ⟨fun c => if Q c then selM c else incomingNeg c, ?_, ?_⟩
  · intro c hc
    dsimp only
    by_cases hq : Q c
    · rw [if_pos hq]
      exact hselM c (by rw [← hl c hq]; exact hc)
    · rw [if_neg hq]
      exact Or.inl rfl
  · intro a b hQS
    have hkept : ∀ c ∈ squareCorners a b,
        keptInside F (fun c => if Q c then selM c else incomingNeg c) (squareCorners a b) c ↔
          keptInside M selM (squareCorners a b) c := by
      intro c hc
      have hq := hQS c hc
      simp only [keptInside, hl c hq, if_pos hq]
    intro H
    exact hsqM a b (fun c hc => (hkept c hc).mp (H c hc))

/-- **The standard field has a local satisfying selection on the strict interior squares**, supplied by the sheet minimum
(`W1MRank.sheetMin_hasSat_of_strong`) through `standardField = sheetMin` on the closed polygon. -/
theorem standardField_hasSatOn_strictInterior {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hS : StrongEstimates (conjWord word)) :
    HasSatOn (fun c => FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c)
      (standardField word) :=
  hasSatOn_of_agree (P := fun z => z ∈ (frameAt word).closedPolygon)
    (fun _ hz => standardField_eq_sheetMin_of_strong h hS hz)
    (fun _ hc => FLatticePaper.TransferW1.strictInterior_star (frameAt word) hc)
    (FLatticePaper.W1MRank.sheetMin_hasSat_of_strong h hS)

end FLatticePaper.LocalSat
