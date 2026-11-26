import FLatticePaper.Plane.Induction.RowBottomAssembly
import FLatticePaper.Plane.Induction.RowAlignedAssembly

/-! # `RowFaceStrictHyp` assembled from the root classes

The face row hypothesis `CollarChain.RowFaceStrictHyp` is discharged by the bottom and aligned face lemmas, given the three root-class
facts for the centres of each face and the two side facts (`c ≠ (1,1)` for the bottom centres, and that no aligned centre with `Ψ ≥ 0`
carries a top witness). The root-class facts are the endpoint-coset statements `zTurn (c - lv) - x ∈ span`; they are numerically
exact (words of length at most four) and are the remaining Q33 content. -/

namespace FLatticePaper.RowFaceAssembly

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank FLatticePaper.W1NonfreeOut
  FLatticePaper.CollarSquare FLatticePaper.FaceWitness FLatticePaper.W1Phase FLatticePaper.CollarChain FLatticePaper.W1CollarFrame
  FLatticePaper.RowBottomAssembly FLatticePaper.RowAlignedAssembly FLatticePaper.W1Step FLatticePaper.W1MSheet

theorem rowFaceStrictHyp_of_classes {word : Word} {G : Field} {R : Site → Site → Prop}
    (hP : (frameAt (conjWord word)).Packet G)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den G)
    (hpres : PrescribedAt (frameAt (conjWord word)) G (frameAt word).eps R)
    (hwu : ∀ c j j', laplacian G c = 0 → R c j → R c j' → j = j')
    (hdeck : ∀ (i j : ℤ) (z u : Site), R z u →
      R (z - (frameAt (conjWord word)).child.modifiedDeck.combine i j)
        (u - (frameAt (conjWord word)).child.modifiedDeck.combine i j))
    (hq : RetainQuota G R)
    (hret : ∀ c i, ForcedEdge G (fun _ _ => False) c i → R c i)
    (hn3 : 3 ≤ (frameAt word).child.num)
    (hOne : ∀ c, laplacian (MW word) c = 0 → c ≠ (1, 1))
    (hClassB : ∀ c, FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      laplacian (MW word) c = 0 → 0 ≤ sheetPsi word c → CollarFrame (frameAt word) c → BottomWit (frameAt word) c →
      ¬ Nonfree (frameAt (conjWord word)) (zTurn (c - (frameAt word).sheetShift)) →
      (zTurn (c - (frameAt word).sheetShift) - (0, -1) ∈ (frameAt (conjWord word)).child.modifiedDeck.span ∨
        zTurn (c - (frameAt word).sheetShift) - (0, 0) ∈ (frameAt (conjWord word)).child.modifiedDeck.span))
    (hClassL : ∀ c, FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      laplacian (MW word) c = 0 → 0 ≤ sheetPsi word c → CollarFrame (frameAt word) c → LeftWit (frameAt word) c →
      (frameAt word).eps = 1 → ¬ Nonfree (frameAt (conjWord word)) (zTurn (c - (frameAt word).sheetShift)) →
      (zTurn (c - (frameAt word).sheetShift) - (1, 0) ∈ (frameAt (conjWord word)).child.modifiedDeck.span ∨
        zTurn (c - (frameAt word).sheetShift) - (0, 0) ∈ (frameAt (conjWord word)).child.modifiedDeck.span))
    (hClassR : ∀ c, FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      laplacian (MW word) c = 0 → 0 ≤ sheetPsi word c → CollarFrame (frameAt word) c → RightWit (frameAt word) c →
      (frameAt word).eps = -1 → ¬ Nonfree (frameAt (conjWord word)) (zTurn (c - (frameAt word).sheetShift)) →
      (zTurn (c - (frameAt word).sheetShift) - (0, -1) ∈ (frameAt (conjWord word)).child.modifiedDeck.span ∨
        zTurn (c - (frameAt word).sheetShift) - (1, -1) ∈ (frameAt (conjWord word)).child.modifiedDeck.span)) :
    FLatticePaper.CollarChain.RowFaceStrictHyp word G R := by
  intro c hcS hM hc0 hcoll hWit hnot hnf
  rcases hWit with hB | hA
  · exact bottom_face_of_class hP hW1 hpres hwu hdeck hq hret hcS (hOne c hM) hB
      (hClassB c hcS hM hc0 hcoll hB hnf)
  · have hT : ¬ TopWit (frameAt word) c := fun h => hnot (Or.inl h)
    by_cases hBc : BottomWit (frameAt word) c
    · exact bottom_face_of_class hP hW1 hpres hwu hdeck hq hret hcS (hOne c hM) hBc
        (hClassB c hcS hM hc0 hcoll hBc hnf)
    · unfold AlignedWit at hA
      rcases hA with ⟨he, hL⟩ | ⟨he, hR⟩
      · have hpres1 : PrescribedAt (frameAt (conjWord word)) G 1 R := by
          rw [he] at hpres; exact hpres
        exact left_face_of_class hP hW1 hpres1 hwu hdeck hq hret hn3 hcS hBc hT hL
          (hClassL c hcS hM hc0 hcoll hL he hnf)
      · have hpres1 : PrescribedAt (frameAt (conjWord word)) G (-1) R := by
          rw [he] at hpres; exact hpres
        exact right_face_of_class hP hW1 hpres1 hwu hdeck hq hret hn3 hcS hBc hT hR
          (hClassR c hcS hM hc0 hcoll hR he hnf)

end FLatticePaper.RowFaceAssembly
