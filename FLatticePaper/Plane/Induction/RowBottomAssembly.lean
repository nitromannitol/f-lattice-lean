import FLatticePaper.Plane.Induction.FaceRowsForced
import FLatticePaper.Plane.Induction.BottomV0Row
import FLatticePaper.Plane.Induction.CollarChain
import FLatticePaper.Plane.Induction.RowCorners
import FLatticePaper.Plane.Induction.EndpointStrips

/-! # The bottom face row, assembled from its two root classes

A bottom centre `c` with root `r = zTurn (c - lv)` whose root lies in the class of `H_last - U` or of `V_0` (the endpoint cosets of the
span, numerically the only classes of in-scope roots) has a `PSquare` on the UR square `squareCorners (r.1 - 1) (r.2 - 1)` with strict
corner images. The fixed-root rows (`FaceRowsForced.row_Vm01_bottom`, `BottomV0Row.row_V00_bottom`) are translated by the span vector
that carries the endpoint to `r` (`CollarChain.psquare_sub_span`). -/

namespace FLatticePaper.RowBottomAssembly

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank FLatticePaper.W1NonfreeOut
  FLatticePaper.CollarSquare FLatticePaper.FaceWitness FLatticePaper.W1Phase FLatticePaper.CollarChain
  FLatticePaper.FaceRowsForced FLatticePaper.BottomV0Row FLatticePaper.RowCorners

theorem span_neg_mem (frame : ChildFrame) {x : Site} (hx : x ∈ frame.child.modifiedDeck.span) :
    -x ∈ frame.child.modifiedDeck.span := by
  obtain ⟨i, j, rfl⟩ := hx
  exact ⟨-i, -j, by unfold PeriodDeck.combine; ext <;> simp <;> ring⟩

/-- **The bottom face row from its root class.** A bottom centre `c` (strict, `c ≠ (1,1)`, bottom witness) whose root `r` lies in the
endpoint coset of `H_last - U` or of `V_0` has a `PSquare` on `squareCorners (r.1 - 1) (r.2 - 1)` with strict corner images. -/
theorem bottom_face_of_class {word : Word} {G : Field} {R : Site → Site → Prop} {η : ℤ}
    (hP : (frameAt (conjWord word)).Packet G)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den G)
    (hpres : PrescribedAt (frameAt (conjWord word)) G η R)
    (hwu : ∀ c j j', laplacian G c = 0 → R c j → R c j' → j = j')
    (hdeck : ∀ (i j : ℤ) (z u : Site), R z u →
      R (z - (frameAt (conjWord word)).child.modifiedDeck.combine i j)
        (u - (frameAt (conjWord word)).child.modifiedDeck.combine i j))
    (hq : RetainQuota G R)
    (hret : ∀ c i, ForcedEdge G (fun _ _ => False) c i → R c i)
    {c : Site}
    (hcS : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hne : c ≠ (1, 1)) (hB : BottomWit (frameAt word) c)
    (hcls : zTurn (c - (frameAt word).sheetShift) - (0, -1) ∈ (frameAt (conjWord word)).child.modifiedDeck.span ∨
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
  · -- the class of H_last - U: the row at (0,-1) on squareCorners (-1) (-2), translated to r
    have hPS0 : PSquare G R (0, -1) (0, -2) (-1, -2) (-1, -1) (0, 0) (-1) (-2) :=
      row_Vm01_bottom hP hW1 hpres hwu hdeck hq hret hF
    have hv' : (0, -1) - zTurn (c - (frameAt word).sheetShift) ∈
        (frameAt (conjWord word)).child.modifiedDeck.span := by
      have h := span_neg_mem (frameAt (conjWord word)) hv
      rwa [neg_sub] at h
    have hP' := psquare_sub_span hP hdeck hv' hPS0
    have hrr : (0, -1) - ((0, -1) - zTurn (c - (frameAt word).sheetShift)) = zTurn (c - (frameAt word).sheetShift) := by
      ext <;> simp
    have ha : (-1 : ℤ) - ((0, -1) - zTurn (c - (frameAt word).sheetShift)).1 =
        (zTurn (c - (frameAt word).sheetShift)).1 - 1 := by
      simp only [Prod.fst_sub]; ring
    have hb : (-2 : ℤ) - ((0, -1) - zTurn (c - (frameAt word).sheetShift)).2 =
        (zTurn (c - (frameAt word).sheetShift)).2 - 1 := by
      simp only [Prod.snd_sub]; ring
    rw [hrr, ha, hb] at hP'
    exact ⟨_, _, _, _, _, _, hP',
      bottom_row_strict hcS hne hB hP'.2.1, bottom_row_strict hcS hne hB hP'.2.2.1,
      bottom_row_strict hcS hne hB hP'.2.2.2.1⟩
  · -- the class of V_0: the row at (0,0) on squareCorners (-1) (-1), translated to r
    have hPS0 : PSquare G R (0, 0) (-1, 0) (-1, -1) (0, -1) (1, 0) (-1) (-1) :=
      row_V00_bottom hP hpres hwu hdeck hq hF
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
    have hb : (-1 : ℤ) - ((0, 0) - zTurn (c - (frameAt word).sheetShift)).2 =
        (zTurn (c - (frameAt word).sheetShift)).2 - 1 := by
      simp only [Prod.snd_sub]; ring
    rw [hrr, ha, hb] at hP'
    exact ⟨_, _, _, _, _, _, hP',
      bottom_row_strict hcS hne hB hP'.2.1, bottom_row_strict hcS hne hB hP'.2.2.1,
      bottom_row_strict hcS hne hB hP'.2.2.2.1⟩

end FLatticePaper.RowBottomAssembly
