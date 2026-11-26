import FLatticePaper.Plane.Induction.RowBottomAssembly
import FLatticePaper.Plane.Induction.FaceRows

/-! # The aligned face rows from their root classes

The aligned face of a centre is the left face when `ε = +1` and the right face when `ε = -1`. Its root lies in one of two endpoint
cosets: `H_0` or `V_0` on the left (`ε = +1`), `H_last - U` or `V_last - V` on the right (`ε = -1`). The fixed-root rows are translated
to the root by the span (`CollarChain.psquare_sub_span`), and the corner images are strict by `RowCorners`. The top witness is excluded
as a hypothesis (the strictness lemmas need it). -/

namespace FLatticePaper.RowAlignedAssembly

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank FLatticePaper.W1NonfreeOut
  FLatticePaper.CollarSquare FLatticePaper.FaceWitness FLatticePaper.W1Phase FLatticePaper.CollarChain
  FLatticePaper.FaceRowsForced FLatticePaper.FaceRows FLatticePaper.BottomV0Row FLatticePaper.RowCorners
  FLatticePaper.RowBottomAssembly FLatticePaper.EndpointStrips

/-- **The left face row (`ε = +1`).** A left centre (not bottom, not top) whose root lies in the coset of `H_0` or of `V_0`. -/
theorem left_face_of_class {word : Word} {G : Field} {R : Site → Site → Prop}
    (hP : (frameAt (conjWord word)).Packet G)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den G)
    (hpres : PrescribedAt (frameAt (conjWord word)) G 1 R)
    (hwu : ∀ c j j', laplacian G c = 0 → R c j → R c j' → j = j')
    (hdeck : ∀ (i j : ℤ) (z u : Site), R z u →
      R (z - (frameAt (conjWord word)).child.modifiedDeck.combine i j)
        (u - (frameAt (conjWord word)).child.modifiedDeck.combine i j))
    (hq : RetainQuota G R)
    (hret : ∀ c i, ForcedEdge G (fun _ _ => False) c i → R c i)
    {c : Site} (hn3 : 3 ≤ (frameAt word).child.num)
    (hcS : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hB : ¬ BottomWit (frameAt word) c) (hT : ¬ TopWit (frameAt word) c) (hL : LeftWit (frameAt word) c)
    (hcls : zTurn (c - (frameAt word).sheetShift) - (1, 0) ∈ (frameAt (conjWord word)).child.modifiedDeck.span ∨
      zTurn (c - (frameAt word).sheetShift) - (0, 0) ∈ (frameAt (conjWord word)).child.modifiedDeck.span) :
    ∃ q0 q1 q2 o : Site, ∃ qa qb : ℤ,
      PSquare G R (zTurn (c - (frameAt word).sheetShift)) q0 q1 q2 o qa qb ∧
      FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den
        ((frameAt word).sheetShift + zTurnInv q0) ∧
      FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den
        ((frameAt word).sheetShift + zTurnInv q1) ∧
      FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den
        ((frameAt word).sheetShift + zTurnInv q2) := by
  have hF := FLatticePaper.EndpointStrips.endpointFacts_of_strips hP.strips
  rcases hcls with hv | hv
  · -- the class of H_0: the row at (1,0) on squareCorners 0 0, translated to r
    have hPS0 : PSquare G R (1, 0) (1, 1) (0, 1) (0, 0) (1, -1) 0 0 := row_H10_left hP hpres hwu hq hF
    have hv' : (1, 0) - zTurn (c - (frameAt word).sheetShift) ∈
        (frameAt (conjWord word)).child.modifiedDeck.span := by
      have h := span_neg_mem (frameAt (conjWord word)) hv
      rwa [neg_sub] at h
    have hP' := psquare_sub_span hP hdeck hv' hPS0
    have hrr : (1, 0) - ((1, 0) - zTurn (c - (frameAt word).sheetShift)) = zTurn (c - (frameAt word).sheetShift) := by
      ext <;> simp
    have ha : (0 : ℤ) - ((1, 0) - zTurn (c - (frameAt word).sheetShift)).1 =
        (zTurn (c - (frameAt word).sheetShift)).1 - 1 := by
      simp only [Prod.fst_sub]; ring
    have hb : (0 : ℤ) - ((1, 0) - zTurn (c - (frameAt word).sheetShift)).2 =
        (zTurn (c - (frameAt word).sheetShift)).2 := by
      simp only [Prod.snd_sub]; ring
    rw [hrr, ha, hb] at hP'
    exact ⟨_, _, _, _, _, _, hP',
      left_row_strict hn3 hcS hB hT hL hP'.2.1, left_row_strict hn3 hcS hB hT hL hP'.2.2.1,
      left_row_strict hn3 hcS hB hT hL hP'.2.2.2.1⟩
  · -- the class of V_0: the row at (0,0) on squareCorners (-1) 0, translated to r
    have hPS0 : PSquare G R (0, 0) (-1, 0) (-1, 1) (0, 1) (1, 0) (-1) 0 := row_V00_left hP hW1 hpres hwu hq hret hF
    have hv' : (0, 0) - zTurn (c - (frameAt word).sheetShift) ∈
        (frameAt (conjWord word)).child.modifiedDeck.span := by
      have h := span_neg_mem (frameAt (conjWord word)) hv
      rwa [neg_sub] at h
    have hP' := psquare_sub_span hP hdeck hv' hPS0
    have hrr : (0, 0) - ((0, 0) - zTurn (c - (frameAt word).sheetShift)) = zTurn (c - (frameAt word).sheetShift) := by
      ext <;> simp
    have ha : (-1 : ℤ) - ((0, 0) - zTurn (c - (frameAt word).sheetShift)).1 =
        (zTurn (c - (frameAt word).sheetShift)).1 - 1 := by
      simp only [Prod.fst_sub]; ring
    have hb : (0 : ℤ) - ((0, 0) - zTurn (c - (frameAt word).sheetShift)).2 =
        (zTurn (c - (frameAt word).sheetShift)).2 := by
      simp only [Prod.snd_sub]; ring
    rw [hrr, ha, hb] at hP'
    exact ⟨_, _, _, _, _, _, hP',
      left_row_strict hn3 hcS hB hT hL hP'.2.1, left_row_strict hn3 hcS hB hT hL hP'.2.2.1,
      left_row_strict hn3 hcS hB hT hL hP'.2.2.2.1⟩

/-- **The right face row (`ε = -1`).** A right centre (not bottom, not top) whose root lies in the coset of `H_last - U` or of `V_last - V`. -/
theorem right_face_of_class {word : Word} {G : Field} {R : Site → Site → Prop}
    (hP : (frameAt (conjWord word)).Packet G)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den G)
    (hpres : PrescribedAt (frameAt (conjWord word)) G (-1) R)
    (hwu : ∀ c j j', laplacian G c = 0 → R c j → R c j' → j = j')
    (hdeck : ∀ (i j : ℤ) (z u : Site), R z u →
      R (z - (frameAt (conjWord word)).child.modifiedDeck.combine i j)
        (u - (frameAt (conjWord word)).child.modifiedDeck.combine i j))
    (hq : RetainQuota G R)
    (hret : ∀ c i, ForcedEdge G (fun _ _ => False) c i → R c i)
    {c : Site} (hn3 : 3 ≤ (frameAt word).child.num)
    (hcS : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hB : ¬ BottomWit (frameAt word) c) (hT : ¬ TopWit (frameAt word) c) (hR : RightWit (frameAt word) c)
    (hcls : zTurn (c - (frameAt word).sheetShift) - (0, -1) ∈ (frameAt (conjWord word)).child.modifiedDeck.span ∨
      zTurn (c - (frameAt word).sheetShift) - (1, -1) ∈ (frameAt (conjWord word)).child.modifiedDeck.span) :
    ∃ q0 q1 q2 o : Site, ∃ qa qb : ℤ,
      PSquare G R (zTurn (c - (frameAt word).sheetShift)) q0 q1 q2 o qa qb ∧
      FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den
        ((frameAt word).sheetShift + zTurnInv q0) ∧
      FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den
        ((frameAt word).sheetShift + zTurnInv q1) ∧
      FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den
        ((frameAt word).sheetShift + zTurnInv q2) := by
  have hF := FLatticePaper.EndpointStrips.endpointFacts_of_strips hP.strips
  rcases hcls with hv | hv
  · -- the class of H_last - U: the row at (0,-1) on squareCorners 0 (-2), translated to r
    have hPS0 : PSquare G R (0, -1) (0, -2) (1, -2) (1, -1) (0, 0) 0 (-2) :=
      row_Vm1_right hP hpres hwu hdeck hq hF
    have hv' : (0, -1) - zTurn (c - (frameAt word).sheetShift) ∈
        (frameAt (conjWord word)).child.modifiedDeck.span := by
      have h := span_neg_mem (frameAt (conjWord word)) hv
      rwa [neg_sub] at h
    have hP' := psquare_sub_span hP hdeck hv' hPS0
    have hrr : (0, -1) - ((0, -1) - zTurn (c - (frameAt word).sheetShift)) = zTurn (c - (frameAt word).sheetShift) := by
      ext <;> simp
    have ha : (0 : ℤ) - ((0, -1) - zTurn (c - (frameAt word).sheetShift)).1 =
        (zTurn (c - (frameAt word).sheetShift)).1 := by
      simp only [Prod.fst_sub]; ring
    have hb : (-2 : ℤ) - ((0, -1) - zTurn (c - (frameAt word).sheetShift)).2 =
        (zTurn (c - (frameAt word).sheetShift)).2 - 1 := by
      simp only [Prod.snd_sub]; ring
    rw [hrr, ha, hb] at hP'
    exact ⟨_, _, _, _, _, _, hP',
      right_row_strict hn3 hcS hB hT hR hP'.2.1, right_row_strict hn3 hcS hB hT hR hP'.2.2.1,
      right_row_strict hn3 hcS hB hT hR hP'.2.2.2.1⟩
  · -- the class of V_last - V: the row at (1,-1) on squareCorners 1 (-2), translated to r
    have hPS0 : PSquare G R (1, -1) (2, -1) (2, -2) (1, -2) (0, -1) 1 (-2) :=
      row_1m1_right hP hW1 hpres hwu hdeck hq hret hF
    have hv' : (1, -1) - zTurn (c - (frameAt word).sheetShift) ∈
        (frameAt (conjWord word)).child.modifiedDeck.span := by
      have h := span_neg_mem (frameAt (conjWord word)) hv
      rwa [neg_sub] at h
    have hP' := psquare_sub_span hP hdeck hv' hPS0
    have hrr : (1, -1) - ((1, -1) - zTurn (c - (frameAt word).sheetShift)) = zTurn (c - (frameAt word).sheetShift) := by
      ext <;> simp
    have ha : (1 : ℤ) - ((1, -1) - zTurn (c - (frameAt word).sheetShift)).1 =
        (zTurn (c - (frameAt word).sheetShift)).1 := by
      simp only [Prod.fst_sub]; ring
    have hb : (-2 : ℤ) - ((1, -1) - zTurn (c - (frameAt word).sheetShift)).2 =
        (zTurn (c - (frameAt word).sheetShift)).2 - 1 := by
      simp only [Prod.snd_sub]; ring
    rw [hrr, ha, hb] at hP'
    exact ⟨_, _, _, _, _, _, hP',
      right_row_strict hn3 hcS hB hT hR hP'.2.1, right_row_strict hn3 hcS hB hT hR hP'.2.2.1,
      right_row_strict hn3 hcS hB hT hR hP'.2.2.2.1⟩

end FLatticePaper.RowAlignedAssembly
