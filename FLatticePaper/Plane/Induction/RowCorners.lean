import FLatticePaper.Plane.Induction.FaceSquares

/-! # The corner images of the face rows are strict

A face row of the collar has its parent square at the conjugate root `r = zTurn (c - lv)` (with `lv` the sheet shift), and its corners
`q` are mapped to the physical sites `lv + zTurnInv q`. For the three collar faces the parent square is fixed by the face shape:

* bottom: `squareCorners (r.1 - 1) (r.2 - 1)` is mapped onto `squareCorners (c.1 - 1) c.2`;
* left: `squareCorners (r.1 - 1) r.2` onto `squareCorners c.1 c.2`;
* right: `squareCorners r.1 (r.2 - 1)` onto `squareCorners (c.1 - 1) (c.2 - 1)`.

The physical squares are the face squares of `FaceSquares`, whose corners are strict for a strict collar centre. So the corner images of
every face row are strict, for both roots of the face (the shape of the parent square is the only input). -/

namespace FLatticePaper.RowCorners

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.AndOrRank FLatticePaper.W1Phase FLatticePaper.FaceSquares
  FLatticePaper.FaceWitness

theorem mem_coords {a b : ℤ} {y : Site} :
    y ∈ squareCorners a b ↔ (y.1 = a ∨ y.1 = a + 1) ∧ (y.2 = b ∨ y.2 = b + 1) := by
  obtain ⟨y1, y2⟩ := y
  simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  omega

/-- The bottom face row: the corner `q` of the parent square `squareCorners (r.1 - 1) (r.2 - 1)`, `r = zTurn (c - lv)`, maps to a corner
of the bottom face square of `c`. -/
theorem bottom_image {lv c q : Site}
    (hq : q ∈ squareCorners ((zTurn (c - lv)).1 - 1) ((zTurn (c - lv)).2 - 1)) :
    lv + zTurnInv q ∈ squareCorners (c.1 - 1) c.2 := by
  obtain ⟨q1, q2⟩ := q
  obtain ⟨l1, l2⟩ := lv
  obtain ⟨c1, c2⟩ := c
  rw [mem_coords] at hq ⊢
  simp only [zTurn, zTurnInv, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] at hq ⊢
  omega

/-- The left face row: `q ∈ squareCorners (r.1 - 1) r.2` maps to the left face square `squareCorners c.1 c.2`. -/
theorem left_image {lv c q : Site}
    (hq : q ∈ squareCorners ((zTurn (c - lv)).1 - 1) (zTurn (c - lv)).2) :
    lv + zTurnInv q ∈ squareCorners c.1 c.2 := by
  obtain ⟨q1, q2⟩ := q
  obtain ⟨l1, l2⟩ := lv
  obtain ⟨c1, c2⟩ := c
  rw [mem_coords] at hq ⊢
  simp only [zTurn, zTurnInv, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] at hq ⊢
  omega

/-- The right face row: `q ∈ squareCorners r.1 (r.2 - 1)` maps to the right face square `squareCorners (c.1 - 1) (c.2 - 1)`. -/
theorem right_image {lv c q : Site}
    (hq : q ∈ squareCorners (zTurn (c - lv)).1 ((zTurn (c - lv)).2 - 1)) :
    lv + zTurnInv q ∈ squareCorners (c.1 - 1) (c.2 - 1) := by
  obtain ⟨q1, q2⟩ := q
  obtain ⟨l1, l2⟩ := lv
  obtain ⟨c1, c2⟩ := c
  rw [mem_coords] at hq ⊢
  simp only [zTurn, zTurnInv, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] at hq ⊢
  omega

/-- **Corner images of the bottom face row are strict.** -/
theorem bottom_row_strict {word : Word} {c q : Site}
    (hcS : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c) (hne : c ≠ (1, 1))
    (hB : BottomWit (frameAt word) c)
    (hq : q ∈ squareCorners ((zTurn (c - (frameAt word).sheetShift)).1 - 1)
      ((zTurn (c - (frameAt word).sheetShift)).2 - 1)) :
    FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den
      ((frameAt word).sheetShift + zTurnInv q) :=
  bottom_face_strict hcS hne hB _ (bottom_image hq)

/-- **Corner images of the left face row are strict.** -/
theorem left_row_strict {word : Word} {c q : Site} (hn3 : 3 ≤ (frameAt word).child.num)
    (hcS : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hB : ¬ BottomWit (frameAt word) c) (hT : ¬ TopWit (frameAt word) c) (hL : LeftWit (frameAt word) c)
    (hq : q ∈ squareCorners ((zTurn (c - (frameAt word).sheetShift)).1 - 1) (zTurn (c - (frameAt word).sheetShift)).2) :
    FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den
      ((frameAt word).sheetShift + zTurnInv q) :=
  left_face_strict hn3 hcS hB hT hL _ (left_image hq)

/-- **Corner images of the right face row are strict.** -/
theorem right_row_strict {word : Word} {c q : Site} (hn3 : 3 ≤ (frameAt word).child.num)
    (hcS : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hB : ¬ BottomWit (frameAt word) c) (hT : ¬ TopWit (frameAt word) c) (hR : RightWit (frameAt word) c)
    (hq : q ∈ squareCorners (zTurn (c - (frameAt word).sheetShift)).1 ((zTurn (c - (frameAt word).sheetShift)).2 - 1)) :
    FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den
      ((frameAt word).sheetShift + zTurnInv q) :=
  right_face_strict hn3 hcS hB hT hR _ (right_image hq)

end FLatticePaper.RowCorners
