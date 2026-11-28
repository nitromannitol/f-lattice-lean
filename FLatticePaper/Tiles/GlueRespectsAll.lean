import FLatticePaper.Tiles.GlueRespectsStd
import FLatticePaper.Tiles.WeakStepAssembly
import FLatticePaper.Tiles.LatticeOfRespects

/-! # Item (a) for the glued standard children

The glued odometer of a standard child (`WeakStepAssembly.GluedChildren`) is, on the kept part of each copy, the placed
subodometer of that copy plus its constant. A site of a block of the child's boundary strings (`GlueStringDecomp`) lies in its
copy (the register strings lie in the register tile), and it lies in the kept part of the copy as soon as it lies in no earlier
copy of the same register other than the doubled partner. `SameParentOffStringsOdd`, `SameParentOffStringsEven` state that no site
of the child's boundary strings lies in two copies of the same register other than a doubled pair (numerically true at every
uncorrected child, `tmp-w4/c_glue_same.py`; it fails at the corrected odd children `w = 2 3^k`); with it the glued odometer has
the block values of `GlueRespectsStd`, so it respects the strings of the child (`odd_glue_respects`, `even_glue_respects`). -/

namespace FLatticePaper.Tiles.GlueRespectsAll

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.GlueRegister
open FLatticePaper.Tiles.GlueRespectsStd
open FLatticePaper.Tiles.SiteStrings (hWordOf vWordOf)
open FLatticePaper.Tiles.StandardClause (fracOdd fracEven)
open FLatticePaper.Tiles.SurgicalWeak (regsAt RespectsAnchored)
open FLatticePaper.Tiles.ChildGlue (keptSet dblOdd dblEven oddP oddQ evenP evenQ tOddSet tEvenSet pieceSet pieceFlag)
open FLatticePaper.Tiles.ClosedPathAssembly (placedOdd placedEven affOdd affEven)
open FLatticePaper.Tiles.SiteInduction (shiftS)

/-- The four boundary strings of a standard tile, in the order of `RespectsAnchored`. -/
def fourStrings (wh wv : BinaryWord) : List (ZTile × GInt) :=
  hStringAt wh 0 ++ hRevStringAt wh.reverse (lastPosOf (vRevStringAt wv.reverse 0)) ++ vRevStringAt wv.reverse 0 ++
    vStringAt wv (lastPosOf (hStringAt wh 0))

/-- **No site of the boundary strings of the odd child lies in two copies of the same register other than a doubled pair.** -/
def SameParentOffStringsOdd (w u1 u2 : Word) : Prop :=
  ∀ x ∈ placedSites (fourStrings (hWordOf w false) (vWordOf w false)), ∀ i j, j < i → i < 6 →
    pieceFlag (oddP w) j = pieceFlag (oddP w) i → ¬ dblOdd w j i →
    x ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) i → x ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) j →
    False

/-- **The same for the even child.** -/
def SameParentOffStringsEven (w u1 u2 : Word) : Prop :=
  ∀ x ∈ placedSites (fourStrings (hWordOf w true) (vWordOf w true)), ∀ i j, j < i → i < 6 →
    pieceFlag (evenP w) j = pieceFlag (evenP w) i → ¬ dblEven j i →
    x ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) i →
    x ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) j → False

theorem ps_append (l1 l2 : List (ZTile × GInt)) : placedSites (l1 ++ l2) = placedSites l1 ++ placedSites l2 := by
  unfold placedSites; rw [List.flatMap_append]

theorem ps_map_shift (s : List (ZTile × GInt)) (off : GInt) :
    placedSites (s.map fun p => (p.1, p.2 + off)) = (placedSites s).map (· + off) := by
  unfold placedSites
  induction s with
  | nil => rfl
  | cons t s ih =>
    simp only [List.map_cons, List.flatMap_cons, List.map_append, ih, List.map_map]
    congr 1
    apply List.map_congr_left
    intro y _
    simp [add_assoc]

/-- A site of a register string started at the copy's offset lies in the copy. -/
theorem mem_copy (T : Finset GInt) (s s' : List (ZTile × GInt)) (hIn : ∀ y ∈ placedSites s, y ∈ (↑T : Set GInt))
    (off : GInt) (hs : s.map (fun p => (p.1, p.2 + off)) = s') (x : GInt) (hx : x ∈ placedSites s') :
    x ∈ shiftS (↑T : Set GInt) off := by
  rw [← hs, ps_map_shift] at hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  exact ⟨y, hIn y hy, rfl⟩

/-- A site of a copy in no earlier copy of the same register, other than its doubled partner, is in its kept part. -/
theorem kept_of (D : ℕ → Set GInt) (flag : ℕ → Bool) (Dbl : ℕ → ℕ → Prop) (i : ℕ) (x : GInt) (hx : x ∈ D i)
    (hex : ∀ j, j < i → flag j = flag i → ¬ Dbl j i → x ∈ D j → False) : x ∈ keptSet D flag Dbl i :=
  ⟨hx, fun ⟨j, hj, hf, hd, hxj⟩ => hex j hj hf hd hxj⟩

theorem in_bot (wh wv : BinaryWord) (T : Set GInt) (h : ∀ y ∈ placedSites (fourStrings wh wv), y ∈ T) :
    ∀ y ∈ placedSites (hStringAt wh 0), y ∈ T := fun y hy => h y (by
  unfold fourStrings; simp only [ps_append, List.mem_append]; tauto)

theorem in_top (wh wv : BinaryWord) (T : Set GInt) (h : ∀ y ∈ placedSites (fourStrings wh wv), y ∈ T) :
    ∀ y ∈ placedSites (hRevStringAt wh.reverse (lastPosOf (vRevStringAt wv.reverse 0))), y ∈ T := fun y hy => h y (by
  unfold fourStrings; simp only [ps_append, List.mem_append]; tauto)

theorem in_left (wh wv : BinaryWord) (T : Set GInt) (h : ∀ y ∈ placedSites (fourStrings wh wv), y ∈ T) :
    ∀ y ∈ placedSites (vRevStringAt wv.reverse 0), y ∈ T := fun y hy => h y (by
  unfold fourStrings; simp only [ps_append, List.mem_append]; tauto)

theorem in_right (wh wv : BinaryWord) (T : Set GInt) (h : ∀ y ∈ placedSites (fourStrings wh wv), y ∈ T) :
    ∀ y ∈ placedSites (vStringAt wv (lastPosOf (hStringAt wh 0))), y ∈ T := fun y hy => h y (by
  unfold fourStrings; simp only [ps_append, List.mem_append]; tauto)

/-- **Item (a) for the glued odd child, W_1 even.** -/
theorem odd_ef_glue (w u1 u2 : Word) (hw : ¬ Standard.IsBase w) (hreg : regsAt w = (some u1, some u2)) (hph : phase w ≠ 1)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2) (oP oQ : GInt → ℤ)
    (hRP : RespectsAnchored (Standard.oddTile u1) (hWordOf u1 false) (vWordOf u1 false) oP) (βP : ℤ)
    (hNP : ∀ x ∈ tileShape ZTile.one, oP x = zTileOdo ZTile.one x + βP)
    (hRQ : RespectsAnchored (Standard.evenTile u2) (hWordOf u2 true) (vWordOf u2 true) oQ) (βQ : ℤ)
    (hNQ : ∀ x ∈ tileShape ZTile.one, oQ x = zTileOdo ZTile.one x + βQ) (g : GInt → ℤ) (κ : ℕ → ℤ)
    (hg : ∀ i < (oddP w).length + (oddQ w).length, ∀ z ∈ keptSet (pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2)) (pieceFlag (oddP w)) (dblOdd w) i,
      g z = placedOdd w oP oQ 0 i z + κ i)
    (hex : SameParentOffStringsOdd w u1 u2) :
    RespectsAnchored (Standard.oddTile w) (hWordOf w false) (vWordOf w false) g := by
  have hP := ClosedPathAssembly.oddP_ef w hph
  have hQ := ClosedPathAssembly.oddQ_ef w hph
  have RP := regData_odd u1 _ oP hRP βP hNP
  have RQ := regData_even u2 _ oQ hRQ βQ hNQ
  obtain ⟨dbot, dleft, dright, dtop⟩ := GlueStringDecomp.odd_ef w u1 u2 hreg hph
  have hInP : ∀ y ∈ placedSites (fourStrings (hWordOf u1 false) (vWordOf u1 false)), y ∈ (↑(Standard.oddTile u1) : Set GInt) := hRP.1
  have hInQ : ∀ y ∈ placedSites (fourStrings (hWordOf u2 true) (vWordOf u2 true)), y ∈ (↑(Standard.evenTile u2) : Set GInt) := hRQ.1
  have pc0 : pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 0 = shiftS (tOddSet u1) (texV1Even (fracEven u2) + texV1Even (fracEven u2)) := by
    simp [pieceSet, hP, hq]
  have pc1 : pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 1 = shiftS (tOddSet u1) (texV2 (fracEven u2)) := by
    simp [pieceSet, hP, hq]
  have pc2 : pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 2 = shiftS (tEvenSet u2) (0) := by
    simp [pieceSet, hP, hQ, hp, hq, add_assoc]
  have pc3 : pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 3 = shiftS (tEvenSet u2) (texV1Even (fracEven u2)) := by
    simp [pieceSet, hP, hQ, hp, hq, add_assoc]
  have pc4 : pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 4 = shiftS (tEvenSet u2) (texV1Odd (fracOdd u1) + texV2 (fracOdd u1)) := by
    simp [pieceSet, hP, hQ, hp, hq, add_assoc]
  have pc5 : pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 5 = shiftS (tEvenSet u2) (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV1Even (fracEven u2)) := by
    simp [pieceSet, hP, hQ, hp, hq, add_assoc]
  have m2b : ∀ x ∈ placedSites (hStringAt (hWordOf u2 true) (0)), x ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 2 := by
    intro x hx
    rw [pc2]
    exact mem_copy (Standard.evenTile u2) _ _ (in_bot (hWordOf u2 true) (vWordOf u2 true) _ hInQ) (0) (by rw [GlueChain.hStringAt_shift, zero_add]) x hx
  have m3b : ∀ x ∈ placedSites (hStringAt (hWordOf u2 true) (texV1Even (fracEven u2))), x ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 3 := by
    intro x hx
    rw [pc3]
    exact mem_copy (Standard.evenTile u2) _ _ (in_bot (hWordOf u2 true) (vWordOf u2 true) _ hInQ) (texV1Even (fracEven u2)) (by rw [GlueChain.hStringAt_shift, zero_add]) x hx
  have m0b : ∀ x ∈ placedSites (hStringAt (hWordOf u1 false) (texV1Even (fracEven u2) + texV1Even (fracEven u2))), x ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 0 := by
    intro x hx
    rw [pc0]
    exact mem_copy (Standard.oddTile u1) _ _ (in_bot (hWordOf u1 false) (vWordOf u1 false) _ hInP) (texV1Even (fracEven u2) + texV1Even (fracEven u2)) (by rw [GlueChain.hStringAt_shift, zero_add]) x hx
  have m1t : ∀ x ∈ placedSites (hRevStringAt (hWordOf u1 false).reverse (texV2 (fracEven u2) + (texV2 (fracOdd u1) + (1, -2)))), x ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 1 := by
    intro x hx
    rw [pc1]
    exact mem_copy (Standard.oddTile u1) _ _ (in_top (hWordOf u1 false) (vWordOf u1 false) _ hInP) (texV2 (fracEven u2)) (by rw [GlueChain.hRevStringAt_shift, RP.pY, add_comm (texV2 (fracOdd u1) + (1, -2)) (texV2 (fracEven u2))]) x hx
  have m4t : ∀ x ∈ placedSites (hRevStringAt (hWordOf u2 true).reverse (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + (texV2 (fracEven u2) + (1, -2)))), x ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 4 := by
    intro x hx
    rw [pc4]
    exact mem_copy (Standard.evenTile u2) _ _ (in_top (hWordOf u2 true) (vWordOf u2 true) _ hInQ) (texV1Odd (fracOdd u1) + texV2 (fracOdd u1)) (by rw [GlueChain.hRevStringAt_shift, RQ.pY, add_comm (texV2 (fracEven u2) + (1, -2)) (texV1Odd (fracOdd u1) + texV2 (fracOdd u1))]) x hx
  have m5t : ∀ x ∈ placedSites (hRevStringAt (hWordOf u2 true).reverse (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV1Even (fracEven u2) + (texV2 (fracEven u2) + (1, -2)))), x ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 5 := by
    intro x hx
    rw [pc5]
    exact mem_copy (Standard.evenTile u2) _ _ (in_top (hWordOf u2 true) (vWordOf u2 true) _ hInQ) (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV1Even (fracEven u2)) (by rw [GlueChain.hRevStringAt_shift, RQ.pY, add_comm (texV2 (fracEven u2) + (1, -2)) (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV1Even (fracEven u2))]) x hx
  have m2l : ∀ x ∈ placedSites (vRevStringAt (vWordOf u2 true).reverse (0)), x ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 2 := by
    intro x hx
    rw [pc2]
    exact mem_copy (Standard.evenTile u2) _ _ (in_left (hWordOf u2 true) (vWordOf u2 true) _ hInQ) (0) (by rw [GlueChain.vRevStringAt_shift, zero_add]) x hx
  have m1l : ∀ x ∈ placedSites (vRevStringAt (vWordOf u1 false).reverse (texV2 (fracEven u2))), x ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 1 := by
    intro x hx
    rw [pc1]
    exact mem_copy (Standard.oddTile u1) _ _ (in_left (hWordOf u1 false) (vWordOf u1 false) _ hInP) (texV2 (fracEven u2)) (by rw [GlueChain.vRevStringAt_shift, zero_add]) x hx
  have m0r : ∀ x ∈ placedSites (vStringAt (vWordOf u1 false) (texV1Even (fracEven u2) + texV1Even (fracEven u2) + (texV1Odd (fracOdd u1) - (1, 1)))), x ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 0 := by
    intro x hx
    rw [pc0]
    exact mem_copy (Standard.oddTile u1) _ _ (in_right (hWordOf u1 false) (vWordOf u1 false) _ hInP) (texV1Even (fracEven u2) + texV1Even (fracEven u2)) (by rw [GlueChain.vStringAt_shift, RP.pX, add_comm (texV1Odd (fracOdd u1) - (1, 1)) (texV1Even (fracEven u2) + texV1Even (fracEven u2))]) x hx
  have m5r : ∀ x ∈ placedSites (vStringAt (vWordOf u2 true) (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV1Even (fracEven u2) + (texV1Even (fracEven u2) - (1, 1)))), x ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 5 := by
    intro x hx
    rw [pc5]
    exact mem_copy (Standard.evenTile u2) _ _ (in_right (hWordOf u2 true) (vWordOf u2 true) _ hInQ) (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV1Even (fracEven u2)) (by rw [GlueChain.vStringAt_shift, RQ.pX, add_comm (texV1Even (fracEven u2) - (1, 1)) (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV1Even (fracEven u2))]) x hx
  have hch : ∀ x, x ∈ placedSites (fourStrings (hWordOf w false) (vWordOf w false)) ↔
      x ∈ placedSites (hStringAt (hWordOf u2 true) (0)) ∨ x ∈ placedSites (hStringAt (hWordOf u2 true) (texV1Even (fracEven u2))) ∨ x ∈ placedSites (hStringAt (hWordOf u1 false) (texV1Even (fracEven u2) + texV1Even (fracEven u2))) ∨ x ∈ placedSites (hRevStringAt (hWordOf u1 false).reverse (texV2 (fracEven u2) + (texV2 (fracOdd u1) + (1, -2)))) ∨ x ∈ placedSites (hRevStringAt (hWordOf u2 true).reverse (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + (texV2 (fracEven u2) + (1, -2)))) ∨ x ∈ placedSites (hRevStringAt (hWordOf u2 true).reverse (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV1Even (fracEven u2) + (texV2 (fracEven u2) + (1, -2)))) ∨ x ∈ placedSites (vRevStringAt (vWordOf u2 true).reverse (0)) ∨ x ∈ placedSites (vRevStringAt (vWordOf u1 false).reverse (texV2 (fracEven u2))) ∨ x ∈ placedSites (vStringAt (vWordOf u1 false) (texV1Even (fracEven u2) + texV1Even (fracEven u2) + (texV1Odd (fracOdd u1) - (1, 1)))) ∨ x ∈ placedSites (vStringAt (vWordOf u2 true) (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV1Even (fracEven u2) + (texV1Even (fracEven u2) - (1, 1)))) := by
    intro x
    unfold fourStrings
    rw [dright, dtop, dbot, dleft]
    simp only [ps_append, List.mem_append, or_assoc]
  obtain ⟨hbot, htop, hleft, hright⟩ := odd_ef_respects w u1 u2 hreg hph _ _ oP oQ hRP βP hNP hRQ βQ hNQ g κ
    (fun x hx => by
      rw [hg 2 (by simp [hP, hQ]) x (kept_of _ _ _ 2 x (m2b x hx) (fun j hj hf hd hxj => hex x ((hch x).2 (Or.inl hx)) 2 j hj (by norm_num) hf hd (m2b x hx) hxj))]
      simp [placedOdd, pl, ClosedPathSum.dot2, affOdd, hQ, hp, hq])
    (fun x hx => by
      rw [hg 3 (by simp [hP, hQ]) x (kept_of _ _ _ 3 x (m3b x hx) (fun j hj hf hd hxj => hex x ((hch x).2 (Or.inr (Or.inl hx))) 3 j hj (by norm_num) hf hd (m3b x hx) hxj))]
      simp [placedOdd, pl, ClosedPathSum.dot2, affOdd, hQ, hp, hq])
    (fun x hx => by
      rw [hg 0 (by simp [hP, hQ]) x (kept_of _ _ _ 0 x (m0b x hx) (fun j hj hf hd hxj => hex x ((hch x).2 (Or.inr (Or.inr (Or.inl hx)))) 0 j hj (by norm_num) hf hd (m0b x hx) hxj))]
      simp [placedOdd, pl, ClosedPathSum.dot2, affOdd, hP, hq])
    (fun x hx => by
      rw [hg 1 (by simp [hP, hQ]) x (kept_of _ _ _ 1 x (m1t x hx) (fun j hj hf hd hxj => hex x ((hch x).2 (Or.inr (Or.inr (Or.inr (Or.inl hx))))) 1 j hj (by norm_num) hf hd (m1t x hx) hxj))]
      simp [placedOdd, pl, ClosedPathSum.dot2, affOdd, hP, hq]
      ring)
    (fun x hx => by
      rw [hg 4 (by simp [hP, hQ]) x (kept_of _ _ _ 4 x (m4t x hx) (fun j hj hf hd hxj => hex x ((hch x).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx)))))) 4 j hj (by norm_num) hf hd (m4t x hx) hxj))]
      simp [placedOdd, pl, ClosedPathSum.dot2, affOdd, hQ, hp, hq]
      ring)
    (fun x hx => by
      rw [hg 5 (by simp [hP, hQ]) x (kept_of _ _ _ 5 x (m5t x hx) (fun j hj hf hd hxj => hex x ((hch x).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx))))))) 5 j hj (by norm_num) hf hd (m5t x hx) hxj))]
      simp [placedOdd, pl, ClosedPathSum.dot2, affOdd, hQ, hp, hq]
      ring)
    (fun x hx => by
      rw [hg 2 (by simp [hP, hQ]) x (kept_of _ _ _ 2 x (m2l x hx) (fun j hj hf hd hxj => hex x ((hch x).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx)))))))) 2 j hj (by norm_num) hf hd (m2l x hx) hxj))]
      simp [placedOdd, pl, ClosedPathSum.dot2, affOdd, hQ, hp, hq])
    (fun x hx => by
      rw [hg 1 (by simp [hP, hQ]) x (kept_of _ _ _ 1 x (m1l x hx) (fun j hj hf hd hxj => hex x ((hch x).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx))))))))) 1 j hj (by norm_num) hf hd (m1l x hx) hxj))]
      simp [placedOdd, pl, ClosedPathSum.dot2, affOdd, hP, hq]
      ring)
    (fun x hx => by
      rw [hg 0 (by simp [hP, hQ]) x (kept_of _ _ _ 0 x (m0r x hx) (fun j hj hf hd hxj => hex x ((hch x).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx)))))))))) 0 j hj (by norm_num) hf hd (m0r x hx) hxj))]
      simp [placedOdd, pl, ClosedPathSum.dot2, affOdd, hP, hq])
    (fun x hx => by
      rw [hg 5 (by simp [hP, hQ]) x (kept_of _ _ _ 5 x (m5r x hx) (fun j hj hf hd hxj => hex x ((hch x).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hx))))))))))) 5 j hj (by norm_num) hf hd (m5r x hx) hxj))]
      simp [placedOdd, pl, ClosedPathSum.dot2, affOdd, hQ, hp, hq]
      ring)
  refine ⟨fun x hx => ?_, hbot, htop, hleft, hright⟩
  rcases (hch x).1 hx with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact WeakStepPaper.oddCopy_sub w u1 u2 hw ((WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])) ((WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])) 2 (by norm_num) (by rw [WeakStepPaper.oddCopies_eq w u1 u2 2 (by norm_num)]; exact m2b x h0)
  · exact WeakStepPaper.oddCopy_sub w u1 u2 hw ((WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])) ((WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])) 3 (by norm_num) (by rw [WeakStepPaper.oddCopies_eq w u1 u2 3 (by norm_num)]; exact m3b x h1)
  · exact WeakStepPaper.oddCopy_sub w u1 u2 hw ((WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])) ((WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])) 0 (by norm_num) (by rw [WeakStepPaper.oddCopies_eq w u1 u2 0 (by norm_num)]; exact m0b x h2)
  · exact WeakStepPaper.oddCopy_sub w u1 u2 hw ((WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])) ((WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])) 1 (by norm_num) (by rw [WeakStepPaper.oddCopies_eq w u1 u2 1 (by norm_num)]; exact m1t x h3)
  · exact WeakStepPaper.oddCopy_sub w u1 u2 hw ((WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])) ((WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])) 4 (by norm_num) (by rw [WeakStepPaper.oddCopies_eq w u1 u2 4 (by norm_num)]; exact m4t x h4)
  · exact WeakStepPaper.oddCopy_sub w u1 u2 hw ((WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])) ((WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])) 5 (by norm_num) (by rw [WeakStepPaper.oddCopies_eq w u1 u2 5 (by norm_num)]; exact m5t x h5)
  · exact WeakStepPaper.oddCopy_sub w u1 u2 hw ((WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])) ((WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])) 2 (by norm_num) (by rw [WeakStepPaper.oddCopies_eq w u1 u2 2 (by norm_num)]; exact m2l x h6)
  · exact WeakStepPaper.oddCopy_sub w u1 u2 hw ((WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])) ((WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])) 1 (by norm_num) (by rw [WeakStepPaper.oddCopies_eq w u1 u2 1 (by norm_num)]; exact m1l x h7)
  · exact WeakStepPaper.oddCopy_sub w u1 u2 hw ((WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])) ((WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])) 0 (by norm_num) (by rw [WeakStepPaper.oddCopies_eq w u1 u2 0 (by norm_num)]; exact m0r x h8)
  · exact WeakStepPaper.oddCopy_sub w u1 u2 hw ((WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])) ((WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])) 5 (by norm_num) (by rw [WeakStepPaper.oddCopies_eq w u1 u2 5 (by norm_num)]; exact m5r x h9)

/-- **Item (a) for the glued odd child, W_1 odd.** -/
theorem odd_of_glue (w u1 u2 : Word) (hw : ¬ Standard.IsBase w) (hreg : regsAt w = (some u1, some u2)) (hph : phase w = 1)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2) (oP oQ : GInt → ℤ)
    (hRP : RespectsAnchored (Standard.oddTile u1) (hWordOf u1 false) (vWordOf u1 false) oP) (βP : ℤ)
    (hNP : ∀ x ∈ tileShape ZTile.one, oP x = zTileOdo ZTile.one x + βP)
    (hRQ : RespectsAnchored (Standard.evenTile u2) (hWordOf u2 true) (vWordOf u2 true) oQ) (βQ : ℤ)
    (hNQ : ∀ x ∈ tileShape ZTile.one, oQ x = zTileOdo ZTile.one x + βQ) (g : GInt → ℤ) (κ : ℕ → ℤ)
    (hg : ∀ i < (oddP w).length + (oddQ w).length, ∀ z ∈ keptSet (pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2)) (pieceFlag (oddP w)) (dblOdd w) i,
      g z = placedOdd w oP oQ 0 i z + κ i)
    (hex : SameParentOffStringsOdd w u1 u2) :
    RespectsAnchored (Standard.oddTile w) (hWordOf w false) (vWordOf w false) g := by
  have hP := ClosedPathAssembly.oddP_of w hph
  have hQ := ClosedPathAssembly.oddQ_of w hph
  have RP := regData_odd u1 _ oP hRP βP hNP
  have RQ := regData_even u2 _ oQ hRQ βQ hNQ
  obtain ⟨dbot, dleft, dright, dtop⟩ := GlueStringDecomp.odd_of w u1 u2 hreg hph
  have hInP : ∀ y ∈ placedSites (fourStrings (hWordOf u1 false) (vWordOf u1 false)), y ∈ (↑(Standard.oddTile u1) : Set GInt) := hRP.1
  have hInQ : ∀ y ∈ placedSites (fourStrings (hWordOf u2 true) (vWordOf u2 true)), y ∈ (↑(Standard.evenTile u2) : Set GInt) := hRQ.1
  have pc0 : pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 0 = shiftS (tOddSet u1) (0) := by
    simp [pieceSet, hP, hq, add_assoc]
  have pc1 : pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 1 = shiftS (tOddSet u1) (texV1Even (fracEven u2) + texV1Even (fracEven u2) + texV2 (fracEven u2)) := by
    simp [pieceSet, hP, hq, add_assoc]
  have pc2 : pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 2 = shiftS (tEvenSet u2) (texV1Odd (fracOdd u1)) := by
    simp [pieceSet, hP, hQ, hp, hq, add_assoc]
  have pc3 : pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 3 = shiftS (tEvenSet u2) (texV1Odd (fracOdd u1) + texV1Even (fracEven u2)) := by
    simp [pieceSet, hP, hQ, hp, hq, add_assoc]
  have pc4 : pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 4 = shiftS (tEvenSet u2) (texV2 (fracOdd u1)) := by
    simp [pieceSet, hP, hQ, hp, hq, add_assoc]
  have pc5 : pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 5 = shiftS (tEvenSet u2) (texV2 (fracOdd u1) + texV1Even (fracEven u2)) := by
    simp [pieceSet, hP, hQ, hp, hq, add_assoc]
  have m0b : ∀ x ∈ placedSites (hStringAt (hWordOf u1 false) (0)), x ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 0 := by
    intro x hx
    rw [pc0]
    exact mem_copy (Standard.oddTile u1) _ _ (in_bot (hWordOf u1 false) (vWordOf u1 false) _ hInP) (0) (by rw [GlueChain.hStringAt_shift, zero_add]) x hx
  have m2b : ∀ x ∈ placedSites (hStringAt (hWordOf u2 true) (texV1Odd (fracOdd u1))), x ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 2 := by
    intro x hx
    rw [pc2]
    exact mem_copy (Standard.evenTile u2) _ _ (in_bot (hWordOf u2 true) (vWordOf u2 true) _ hInQ) (texV1Odd (fracOdd u1)) (by rw [GlueChain.hStringAt_shift, zero_add]) x hx
  have m3b : ∀ x ∈ placedSites (hStringAt (hWordOf u2 true) (texV1Odd (fracOdd u1) + texV1Even (fracEven u2))), x ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 3 := by
    intro x hx
    rw [pc3]
    exact mem_copy (Standard.evenTile u2) _ _ (in_bot (hWordOf u2 true) (vWordOf u2 true) _ hInQ) (texV1Odd (fracOdd u1) + texV1Even (fracEven u2)) (by rw [GlueChain.hStringAt_shift, zero_add]) x hx
  have m4t : ∀ x ∈ placedSites (hRevStringAt (hWordOf u2 true).reverse (texV2 (fracOdd u1) + (texV2 (fracEven u2) + (1, -2)))), x ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 4 := by
    intro x hx
    rw [pc4]
    exact mem_copy (Standard.evenTile u2) _ _ (in_top (hWordOf u2 true) (vWordOf u2 true) _ hInQ) (texV2 (fracOdd u1)) (by rw [GlueChain.hRevStringAt_shift, RQ.pY, add_comm (texV2 (fracEven u2) + (1, -2)) (texV2 (fracOdd u1))]) x hx
  have m5t : ∀ x ∈ placedSites (hRevStringAt (hWordOf u2 true).reverse (texV2 (fracOdd u1) + texV1Even (fracEven u2) + (texV2 (fracEven u2) + (1, -2)))), x ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 5 := by
    intro x hx
    rw [pc5]
    exact mem_copy (Standard.evenTile u2) _ _ (in_top (hWordOf u2 true) (vWordOf u2 true) _ hInQ) (texV2 (fracOdd u1) + texV1Even (fracEven u2)) (by rw [GlueChain.hRevStringAt_shift, RQ.pY, add_comm (texV2 (fracEven u2) + (1, -2)) (texV2 (fracOdd u1) + texV1Even (fracEven u2))]) x hx
  have m1t : ∀ x ∈ placedSites (hRevStringAt (hWordOf u1 false).reverse (texV1Even (fracEven u2) + texV1Even (fracEven u2) + texV2 (fracEven u2) + (texV2 (fracOdd u1) + (1, -2)))), x ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 1 := by
    intro x hx
    rw [pc1]
    exact mem_copy (Standard.oddTile u1) _ _ (in_top (hWordOf u1 false) (vWordOf u1 false) _ hInP) (texV1Even (fracEven u2) + texV1Even (fracEven u2) + texV2 (fracEven u2)) (by rw [GlueChain.hRevStringAt_shift, RP.pY, add_comm (texV2 (fracOdd u1) + (1, -2)) (texV1Even (fracEven u2) + texV1Even (fracEven u2) + texV2 (fracEven u2))]) x hx
  have m0l : ∀ x ∈ placedSites (vRevStringAt (vWordOf u1 false).reverse (0)), x ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 0 := by
    intro x hx
    rw [pc0]
    exact mem_copy (Standard.oddTile u1) _ _ (in_left (hWordOf u1 false) (vWordOf u1 false) _ hInP) (0) (by rw [GlueChain.vRevStringAt_shift, zero_add]) x hx
  have m4l : ∀ x ∈ placedSites (vRevStringAt (vWordOf u2 true).reverse (texV2 (fracOdd u1))), x ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 4 := by
    intro x hx
    rw [pc4]
    exact mem_copy (Standard.evenTile u2) _ _ (in_left (hWordOf u2 true) (vWordOf u2 true) _ hInQ) (texV2 (fracOdd u1)) (by rw [GlueChain.vRevStringAt_shift, zero_add]) x hx
  have m3r : ∀ x ∈ placedSites (vStringAt (vWordOf u2 true) (texV1Odd (fracOdd u1) + texV1Even (fracEven u2) + (texV1Even (fracEven u2) - (1, 1)))), x ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 3 := by
    intro x hx
    rw [pc3]
    exact mem_copy (Standard.evenTile u2) _ _ (in_right (hWordOf u2 true) (vWordOf u2 true) _ hInQ) (texV1Odd (fracOdd u1) + texV1Even (fracEven u2)) (by rw [GlueChain.vStringAt_shift, RQ.pX, add_comm (texV1Even (fracEven u2) - (1, 1)) (texV1Odd (fracOdd u1) + texV1Even (fracEven u2))]) x hx
  have m1r : ∀ x ∈ placedSites (vStringAt (vWordOf u1 false) (texV1Even (fracEven u2) + texV1Even (fracEven u2) + texV2 (fracEven u2) + (texV1Odd (fracOdd u1) - (1, 1)))), x ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 1 := by
    intro x hx
    rw [pc1]
    exact mem_copy (Standard.oddTile u1) _ _ (in_right (hWordOf u1 false) (vWordOf u1 false) _ hInP) (texV1Even (fracEven u2) + texV1Even (fracEven u2) + texV2 (fracEven u2)) (by rw [GlueChain.vStringAt_shift, RP.pX, add_comm (texV1Odd (fracOdd u1) - (1, 1)) (texV1Even (fracEven u2) + texV1Even (fracEven u2) + texV2 (fracEven u2))]) x hx
  have hch : ∀ x, x ∈ placedSites (fourStrings (hWordOf w false) (vWordOf w false)) ↔
      x ∈ placedSites (hStringAt (hWordOf u1 false) (0)) ∨ x ∈ placedSites (hStringAt (hWordOf u2 true) (texV1Odd (fracOdd u1))) ∨ x ∈ placedSites (hStringAt (hWordOf u2 true) (texV1Odd (fracOdd u1) + texV1Even (fracEven u2))) ∨ x ∈ placedSites (hRevStringAt (hWordOf u2 true).reverse (texV2 (fracOdd u1) + (texV2 (fracEven u2) + (1, -2)))) ∨ x ∈ placedSites (hRevStringAt (hWordOf u2 true).reverse (texV2 (fracOdd u1) + texV1Even (fracEven u2) + (texV2 (fracEven u2) + (1, -2)))) ∨ x ∈ placedSites (hRevStringAt (hWordOf u1 false).reverse (texV1Even (fracEven u2) + texV1Even (fracEven u2) + texV2 (fracEven u2) + (texV2 (fracOdd u1) + (1, -2)))) ∨ x ∈ placedSites (vRevStringAt (vWordOf u1 false).reverse (0)) ∨ x ∈ placedSites (vRevStringAt (vWordOf u2 true).reverse (texV2 (fracOdd u1))) ∨ x ∈ placedSites (vStringAt (vWordOf u2 true) (texV1Odd (fracOdd u1) + texV1Even (fracEven u2) + (texV1Even (fracEven u2) - (1, 1)))) ∨ x ∈ placedSites (vStringAt (vWordOf u1 false) (texV1Even (fracEven u2) + texV1Even (fracEven u2) + texV2 (fracEven u2) + (texV1Odd (fracOdd u1) - (1, 1)))) := by
    intro x
    unfold fourStrings
    rw [dright, dtop, dbot, dleft]
    simp only [ps_append, List.mem_append, or_assoc]
  obtain ⟨hbot, htop, hleft, hright⟩ := odd_of_respects w u1 u2 hreg hph _ _ oP oQ hRP βP hNP hRQ βQ hNQ g κ
    (fun x hx => by
      rw [hg 0 (by simp [hP, hQ]) x (kept_of _ _ _ 0 x (m0b x hx) (fun j hj hf hd hxj => hex x ((hch x).2 (Or.inl hx)) 0 j hj (by norm_num) hf hd (m0b x hx) hxj))]
      simp [placedOdd, pl, ClosedPathSum.dot2, affOdd, hP, hq])
    (fun x hx => by
      rw [hg 2 (by simp [hP, hQ]) x (kept_of _ _ _ 2 x (m2b x hx) (fun j hj hf hd hxj => hex x ((hch x).2 (Or.inr (Or.inl hx))) 2 j hj (by norm_num) hf hd (m2b x hx) hxj))]
      simp [placedOdd, pl, ClosedPathSum.dot2, affOdd, hQ, hp, hq])
    (fun x hx => by
      rw [hg 3 (by simp [hP, hQ]) x (kept_of _ _ _ 3 x (m3b x hx) (fun j hj hf hd hxj => hex x ((hch x).2 (Or.inr (Or.inr (Or.inl hx)))) 3 j hj (by norm_num) hf hd (m3b x hx) hxj))]
      simp [placedOdd, pl, ClosedPathSum.dot2, affOdd, hQ, hp, hq])
    (fun x hx => by
      rw [hg 4 (by simp [hP, hQ]) x (kept_of _ _ _ 4 x (m4t x hx) (fun j hj hf hd hxj => hex x ((hch x).2 (Or.inr (Or.inr (Or.inr (Or.inl hx))))) 4 j hj (by norm_num) hf hd (m4t x hx) hxj))]
      simp [placedOdd, pl, ClosedPathSum.dot2, affOdd, hQ, hp, hq]
      ring)
    (fun x hx => by
      rw [hg 5 (by simp [hP, hQ]) x (kept_of _ _ _ 5 x (m5t x hx) (fun j hj hf hd hxj => hex x ((hch x).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx)))))) 5 j hj (by norm_num) hf hd (m5t x hx) hxj))]
      simp [placedOdd, pl, ClosedPathSum.dot2, affOdd, hQ, hp, hq]
      ring)
    (fun x hx => by
      rw [hg 1 (by simp [hP, hQ]) x (kept_of _ _ _ 1 x (m1t x hx) (fun j hj hf hd hxj => hex x ((hch x).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx))))))) 1 j hj (by norm_num) hf hd (m1t x hx) hxj))]
      simp [placedOdd, pl, ClosedPathSum.dot2, affOdd, hP, hq]
      ring)
    (fun x hx => by
      rw [hg 0 (by simp [hP, hQ]) x (kept_of _ _ _ 0 x (m0l x hx) (fun j hj hf hd hxj => hex x ((hch x).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx)))))))) 0 j hj (by norm_num) hf hd (m0l x hx) hxj))]
      simp [placedOdd, pl, ClosedPathSum.dot2, affOdd, hP, hq])
    (fun x hx => by
      rw [hg 4 (by simp [hP, hQ]) x (kept_of _ _ _ 4 x (m4l x hx) (fun j hj hf hd hxj => hex x ((hch x).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx))))))))) 4 j hj (by norm_num) hf hd (m4l x hx) hxj))]
      simp [placedOdd, pl, ClosedPathSum.dot2, affOdd, hQ, hp, hq]
      ring)
    (fun x hx => by
      rw [hg 3 (by simp [hP, hQ]) x (kept_of _ _ _ 3 x (m3r x hx) (fun j hj hf hd hxj => hex x ((hch x).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx)))))))))) 3 j hj (by norm_num) hf hd (m3r x hx) hxj))]
      simp [placedOdd, pl, ClosedPathSum.dot2, affOdd, hQ, hp, hq])
    (fun x hx => by
      rw [hg 1 (by simp [hP, hQ]) x (kept_of _ _ _ 1 x (m1r x hx) (fun j hj hf hd hxj => hex x ((hch x).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hx))))))))))) 1 j hj (by norm_num) hf hd (m1r x hx) hxj))]
      simp [placedOdd, pl, ClosedPathSum.dot2, affOdd, hP, hq]
      ring)
  refine ⟨fun x hx => ?_, hbot, htop, hleft, hright⟩
  rcases (hch x).1 hx with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact WeakStepPaper.oddCopy_sub w u1 u2 hw ((WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])) ((WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])) 0 (by norm_num) (by rw [WeakStepPaper.oddCopies_eq w u1 u2 0 (by norm_num)]; exact m0b x h0)
  · exact WeakStepPaper.oddCopy_sub w u1 u2 hw ((WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])) ((WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])) 2 (by norm_num) (by rw [WeakStepPaper.oddCopies_eq w u1 u2 2 (by norm_num)]; exact m2b x h1)
  · exact WeakStepPaper.oddCopy_sub w u1 u2 hw ((WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])) ((WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])) 3 (by norm_num) (by rw [WeakStepPaper.oddCopies_eq w u1 u2 3 (by norm_num)]; exact m3b x h2)
  · exact WeakStepPaper.oddCopy_sub w u1 u2 hw ((WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])) ((WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])) 4 (by norm_num) (by rw [WeakStepPaper.oddCopies_eq w u1 u2 4 (by norm_num)]; exact m4t x h3)
  · exact WeakStepPaper.oddCopy_sub w u1 u2 hw ((WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])) ((WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])) 5 (by norm_num) (by rw [WeakStepPaper.oddCopies_eq w u1 u2 5 (by norm_num)]; exact m5t x h4)
  · exact WeakStepPaper.oddCopy_sub w u1 u2 hw ((WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])) ((WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])) 1 (by norm_num) (by rw [WeakStepPaper.oddCopies_eq w u1 u2 1 (by norm_num)]; exact m1t x h5)
  · exact WeakStepPaper.oddCopy_sub w u1 u2 hw ((WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])) ((WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])) 0 (by norm_num) (by rw [WeakStepPaper.oddCopies_eq w u1 u2 0 (by norm_num)]; exact m0l x h6)
  · exact WeakStepPaper.oddCopy_sub w u1 u2 hw ((WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])) ((WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])) 4 (by norm_num) (by rw [WeakStepPaper.oddCopies_eq w u1 u2 4 (by norm_num)]; exact m4l x h7)
  · exact WeakStepPaper.oddCopy_sub w u1 u2 hw ((WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])) ((WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])) 3 (by norm_num) (by rw [WeakStepPaper.oddCopies_eq w u1 u2 3 (by norm_num)]; exact m3r x h8)
  · exact WeakStepPaper.oddCopy_sub w u1 u2 hw ((WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])) ((WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])) 1 (by norm_num) (by rw [WeakStepPaper.oddCopies_eq w u1 u2 1 (by norm_num)]; exact m1r x h9)

/-- **Item (a) for the glued even child, W_1 even.** -/
theorem even_ef_glue (w u1 u2 : Word) (hw : ¬ Standard.IsBase w) (hreg : regsAt w = (some u1, some u2)) (hph : phase w ≠ 1)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2) (oP oQ : GInt → ℤ)
    (hRP : RespectsAnchored (Standard.oddTile u1) (hWordOf u1 false) (vWordOf u1 false) oP) (βP : ℤ)
    (hNP : ∀ x ∈ tileShape ZTile.one, oP x = zTileOdo ZTile.one x + βP)
    (hRQ : RespectsAnchored (Standard.evenTile u2) (hWordOf u2 true) (vWordOf u2 true) oQ) (βQ : ℤ)
    (hNQ : ∀ x ∈ tileShape ZTile.one, oQ x = zTileOdo ZTile.one x + βQ) (g : GInt → ℤ) (κ : ℕ → ℤ)
    (hg : ∀ i < (evenP w).length + (evenQ w).length, ∀ z ∈ keptSet (pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2)) (pieceFlag (evenP w)) dblEven i,
      g z = placedEven w oP oQ 0 i z + κ i)
    (hex : SameParentOffStringsEven w u1 u2) :
    RespectsAnchored (Standard.evenTile w) (hWordOf w true) (vWordOf w true) g := by
  have hP := ClosedPathAssembly.evenP_ef w hph
  have hQ := ClosedPathAssembly.evenQ_ef w hph
  have RP := regData_odd u1 _ oP hRP βP hNP
  have RQ := regData_even u2 _ oQ hRQ βQ hNQ
  obtain ⟨dbot, dleft, dright, dtop⟩ := GlueStringDecomp.even_ef w u1 u2 hreg hph
  have hInP : ∀ y ∈ placedSites (fourStrings (hWordOf u1 false) (vWordOf u1 false)), y ∈ (↑(Standard.oddTile u1) : Set GInt) := hRP.1
  have hInQ : ∀ y ∈ placedSites (fourStrings (hWordOf u2 true) (vWordOf u2 true)), y ∈ (↑(Standard.evenTile u2) : Set GInt) := hRQ.1
  have pc0 : pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 0 = shiftS (tOddSet u1) (texV1Even (fracEven u2)) := by
    simp [pieceSet, hP, hp, hq]
  have pc1 : pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 1 = shiftS (tOddSet u1) (texV1Even (fracEven u2) + texV2 (fracOdd u1)) := by
    simp [pieceSet, hP, hp, hq]
  have pc2 : pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 2 = shiftS (tOddSet u1) (texV2 (fracEven u2)) := by
    simp [pieceSet, hP, hp, hq]
  have pc3 : pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 3 = shiftS (tOddSet u1) (texV2 (fracEven u2) + texV2 (fracOdd u1)) := by
    simp [pieceSet, hP, hp, hq]
  have pc4 : pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 4 = shiftS (tEvenSet u2) (0) := by
    simp [pieceSet, hP, hQ, hp, hq]
  have pc5 : pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 5 = shiftS (tEvenSet u2) (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV2 (fracOdd u1)) := by
    simp [pieceSet, hP, hQ, hp, hq, add_assoc]
  have m4b : ∀ x ∈ placedSites (hStringAt (hWordOf u2 true) (0)), x ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 4 := by
    intro x hx
    rw [pc4]
    exact mem_copy (Standard.evenTile u2) _ _ (in_bot (hWordOf u2 true) (vWordOf u2 true) _ hInQ) (0) (by rw [GlueChain.hStringAt_shift, zero_add]) x hx
  have m0b : ∀ x ∈ placedSites (hStringAt (hWordOf u1 false) (texV1Even (fracEven u2))), x ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 0 := by
    intro x hx
    rw [pc0]
    exact mem_copy (Standard.oddTile u1) _ _ (in_bot (hWordOf u1 false) (vWordOf u1 false) _ hInP) (texV1Even (fracEven u2)) (by rw [GlueChain.hStringAt_shift, zero_add]) x hx
  have m3t : ∀ x ∈ placedSites (hRevStringAt (hWordOf u1 false).reverse (texV2 (fracEven u2) + texV2 (fracOdd u1) + (texV2 (fracOdd u1) + (1, -2)))), x ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 3 := by
    intro x hx
    rw [pc3]
    exact mem_copy (Standard.oddTile u1) _ _ (in_top (hWordOf u1 false) (vWordOf u1 false) _ hInP) (texV2 (fracEven u2) + texV2 (fracOdd u1)) (by rw [GlueChain.hRevStringAt_shift, RP.pY, add_comm (texV2 (fracOdd u1) + (1, -2)) (texV2 (fracEven u2) + texV2 (fracOdd u1))]) x hx
  have m5t : ∀ x ∈ placedSites (hRevStringAt (hWordOf u2 true).reverse (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV2 (fracOdd u1) + (texV2 (fracEven u2) + (1, -2)))), x ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 5 := by
    intro x hx
    rw [pc5]
    exact mem_copy (Standard.evenTile u2) _ _ (in_top (hWordOf u2 true) (vWordOf u2 true) _ hInQ) (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV2 (fracOdd u1)) (by rw [GlueChain.hRevStringAt_shift, RQ.pY, add_comm (texV2 (fracEven u2) + (1, -2)) (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV2 (fracOdd u1))]) x hx
  have m4l : ∀ x ∈ placedSites (vRevStringAt (vWordOf u2 true).reverse (0)), x ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 4 := by
    intro x hx
    rw [pc4]
    exact mem_copy (Standard.evenTile u2) _ _ (in_left (hWordOf u2 true) (vWordOf u2 true) _ hInQ) (0) (by rw [GlueChain.vRevStringAt_shift, zero_add]) x hx
  have m2l : ∀ x ∈ placedSites (vRevStringAt (vWordOf u1 false).reverse (texV2 (fracEven u2))), x ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 2 := by
    intro x hx
    rw [pc2]
    exact mem_copy (Standard.oddTile u1) _ _ (in_left (hWordOf u1 false) (vWordOf u1 false) _ hInP) (texV2 (fracEven u2)) (by rw [GlueChain.vRevStringAt_shift, zero_add]) x hx
  have m3l : ∀ x ∈ placedSites (vRevStringAt (vWordOf u1 false).reverse (texV2 (fracEven u2) + texV2 (fracOdd u1))), x ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 3 := by
    intro x hx
    rw [pc3]
    exact mem_copy (Standard.oddTile u1) _ _ (in_left (hWordOf u1 false) (vWordOf u1 false) _ hInP) (texV2 (fracEven u2) + texV2 (fracOdd u1)) (by rw [GlueChain.vRevStringAt_shift, zero_add]) x hx
  have m0r : ∀ x ∈ placedSites (vStringAt (vWordOf u1 false) (texV1Even (fracEven u2) + (texV1Odd (fracOdd u1) - (1, 1)))), x ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 0 := by
    intro x hx
    rw [pc0]
    exact mem_copy (Standard.oddTile u1) _ _ (in_right (hWordOf u1 false) (vWordOf u1 false) _ hInP) (texV1Even (fracEven u2)) (by rw [GlueChain.vStringAt_shift, RP.pX, add_comm (texV1Odd (fracOdd u1) - (1, 1)) (texV1Even (fracEven u2))]) x hx
  have m1r : ∀ x ∈ placedSites (vStringAt (vWordOf u1 false) (texV1Even (fracEven u2) + texV2 (fracOdd u1) + (texV1Odd (fracOdd u1) - (1, 1)))), x ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 1 := by
    intro x hx
    rw [pc1]
    exact mem_copy (Standard.oddTile u1) _ _ (in_right (hWordOf u1 false) (vWordOf u1 false) _ hInP) (texV1Even (fracEven u2) + texV2 (fracOdd u1)) (by rw [GlueChain.vStringAt_shift, RP.pX, add_comm (texV1Odd (fracOdd u1) - (1, 1)) (texV1Even (fracEven u2) + texV2 (fracOdd u1))]) x hx
  have m5r : ∀ x ∈ placedSites (vStringAt (vWordOf u2 true) (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV2 (fracOdd u1) + (texV1Even (fracEven u2) - (1, 1)))), x ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 5 := by
    intro x hx
    rw [pc5]
    exact mem_copy (Standard.evenTile u2) _ _ (in_right (hWordOf u2 true) (vWordOf u2 true) _ hInQ) (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV2 (fracOdd u1)) (by rw [GlueChain.vStringAt_shift, RQ.pX, add_comm (texV1Even (fracEven u2) - (1, 1)) (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV2 (fracOdd u1))]) x hx
  have hch : ∀ x, x ∈ placedSites (fourStrings (hWordOf w true) (vWordOf w true)) ↔
      x ∈ placedSites (hStringAt (hWordOf u2 true) (0)) ∨ x ∈ placedSites (hStringAt (hWordOf u1 false) (texV1Even (fracEven u2))) ∨ x ∈ placedSites (hRevStringAt (hWordOf u1 false).reverse (texV2 (fracEven u2) + texV2 (fracOdd u1) + (texV2 (fracOdd u1) + (1, -2)))) ∨ x ∈ placedSites (hRevStringAt (hWordOf u2 true).reverse (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV2 (fracOdd u1) + (texV2 (fracEven u2) + (1, -2)))) ∨ x ∈ placedSites (vRevStringAt (vWordOf u2 true).reverse (0)) ∨ x ∈ placedSites (vRevStringAt (vWordOf u1 false).reverse (texV2 (fracEven u2))) ∨ x ∈ placedSites (vRevStringAt (vWordOf u1 false).reverse (texV2 (fracEven u2) + texV2 (fracOdd u1))) ∨ x ∈ placedSites (vStringAt (vWordOf u1 false) (texV1Even (fracEven u2) + (texV1Odd (fracOdd u1) - (1, 1)))) ∨ x ∈ placedSites (vStringAt (vWordOf u1 false) (texV1Even (fracEven u2) + texV2 (fracOdd u1) + (texV1Odd (fracOdd u1) - (1, 1)))) ∨ x ∈ placedSites (vStringAt (vWordOf u2 true) (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV2 (fracOdd u1) + (texV1Even (fracEven u2) - (1, 1)))) := by
    intro x
    unfold fourStrings
    rw [dright, dtop, dbot, dleft]
    simp only [ps_append, List.mem_append, or_assoc]
  obtain ⟨hbot, htop, hleft, hright⟩ := even_ef_respects w u1 u2 hreg hph _ _ oP oQ hRP βP hNP hRQ βQ hNQ g κ
    (fun x hx => by
      rw [hg 4 (by simp [hP, hQ]) x (kept_of _ _ _ 4 x (m4b x hx) (fun j hj hf hd hxj => hex x ((hch x).2 (Or.inl hx)) 4 j hj (by norm_num) hf hd (m4b x hx) hxj))]
      simp [placedEven, pl, ClosedPathSum.dot2, affEven, hQ, hp])
    (fun x hx => by
      rw [hg 0 (by simp [hP, hQ]) x (kept_of _ _ _ 0 x (m0b x hx) (fun j hj hf hd hxj => hex x ((hch x).2 (Or.inr (Or.inl hx))) 0 j hj (by norm_num) hf hd (m0b x hx) hxj))]
      simp [placedEven, pl, ClosedPathSum.dot2, affEven, hP, hp, hq])
    (fun x hx => by
      rw [hg 3 (by simp [hP, hQ]) x (kept_of _ _ _ 3 x (m3t x hx) (fun j hj hf hd hxj => hex x ((hch x).2 (Or.inr (Or.inr (Or.inl hx)))) 3 j hj (by norm_num) hf hd (m3t x hx) hxj))]
      simp [placedEven, pl, ClosedPathSum.dot2, affEven, hP, hp, hq]
      ring)
    (fun x hx => by
      rw [hg 5 (by simp [hP, hQ]) x (kept_of _ _ _ 5 x (m5t x hx) (fun j hj hf hd hxj => hex x ((hch x).2 (Or.inr (Or.inr (Or.inr (Or.inl hx))))) 5 j hj (by norm_num) hf hd (m5t x hx) hxj))]
      simp [placedEven, pl, ClosedPathSum.dot2, affEven, hQ, hp]
      ring)
    (fun x hx => by
      rw [hg 4 (by simp [hP, hQ]) x (kept_of _ _ _ 4 x (m4l x hx) (fun j hj hf hd hxj => hex x ((hch x).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx)))))) 4 j hj (by norm_num) hf hd (m4l x hx) hxj))]
      simp [placedEven, pl, ClosedPathSum.dot2, affEven, hQ, hp])
    (fun x hx => by
      rw [hg 2 (by simp [hP, hQ]) x (kept_of _ _ _ 2 x (m2l x hx) (fun j hj hf hd hxj => hex x ((hch x).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx))))))) 2 j hj (by norm_num) hf hd (m2l x hx) hxj))]
      simp [placedEven, pl, ClosedPathSum.dot2, affEven, hP, hp, hq]
      ring)
    (fun x hx => by
      rw [hg 3 (by simp [hP, hQ]) x (kept_of _ _ _ 3 x (m3l x hx) (fun j hj hf hd hxj => hex x ((hch x).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx)))))))) 3 j hj (by norm_num) hf hd (m3l x hx) hxj))]
      simp [placedEven, pl, ClosedPathSum.dot2, affEven, hP, hp, hq]
      ring)
    (fun x hx => by
      rw [hg 0 (by simp [hP, hQ]) x (kept_of _ _ _ 0 x (m0r x hx) (fun j hj hf hd hxj => hex x ((hch x).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx))))))))) 0 j hj (by norm_num) hf hd (m0r x hx) hxj))]
      simp [placedEven, pl, ClosedPathSum.dot2, affEven, hP, hp, hq])
    (fun x hx => by
      rw [hg 1 (by simp [hP, hQ]) x (kept_of _ _ _ 1 x (m1r x hx) (fun j hj hf hd hxj => hex x ((hch x).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx)))))))))) 1 j hj (by norm_num) hf hd (m1r x hx) hxj))]
      simp [placedEven, pl, ClosedPathSum.dot2, affEven, hP, hp, hq]
      ring)
    (fun x hx => by
      rw [hg 5 (by simp [hP, hQ]) x (kept_of _ _ _ 5 x (m5r x hx) (fun j hj hf hd hxj => hex x ((hch x).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hx))))))))))) 5 j hj (by norm_num) hf hd (m5r x hx) hxj))]
      simp [placedEven, pl, ClosedPathSum.dot2, affEven, hQ, hp]
      ring)
  refine ⟨fun x hx => ?_, hbot, htop, hleft, hright⟩
  rcases (hch x).1 hx with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact WeakStepPaper.evenCopy_sub w u1 u2 hw ((WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])) ((WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])) 4 (by norm_num) (by rw [WeakStepPaper.evenCopies_eq w u1 u2 4 (by norm_num)]; exact m4b x h0)
  · exact WeakStepPaper.evenCopy_sub w u1 u2 hw ((WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])) ((WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])) 0 (by norm_num) (by rw [WeakStepPaper.evenCopies_eq w u1 u2 0 (by norm_num)]; exact m0b x h1)
  · exact WeakStepPaper.evenCopy_sub w u1 u2 hw ((WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])) ((WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])) 3 (by norm_num) (by rw [WeakStepPaper.evenCopies_eq w u1 u2 3 (by norm_num)]; exact m3t x h2)
  · exact WeakStepPaper.evenCopy_sub w u1 u2 hw ((WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])) ((WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])) 5 (by norm_num) (by rw [WeakStepPaper.evenCopies_eq w u1 u2 5 (by norm_num)]; exact m5t x h3)
  · exact WeakStepPaper.evenCopy_sub w u1 u2 hw ((WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])) ((WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])) 4 (by norm_num) (by rw [WeakStepPaper.evenCopies_eq w u1 u2 4 (by norm_num)]; exact m4l x h4)
  · exact WeakStepPaper.evenCopy_sub w u1 u2 hw ((WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])) ((WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])) 2 (by norm_num) (by rw [WeakStepPaper.evenCopies_eq w u1 u2 2 (by norm_num)]; exact m2l x h5)
  · exact WeakStepPaper.evenCopy_sub w u1 u2 hw ((WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])) ((WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])) 3 (by norm_num) (by rw [WeakStepPaper.evenCopies_eq w u1 u2 3 (by norm_num)]; exact m3l x h6)
  · exact WeakStepPaper.evenCopy_sub w u1 u2 hw ((WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])) ((WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])) 0 (by norm_num) (by rw [WeakStepPaper.evenCopies_eq w u1 u2 0 (by norm_num)]; exact m0r x h7)
  · exact WeakStepPaper.evenCopy_sub w u1 u2 hw ((WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])) ((WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])) 1 (by norm_num) (by rw [WeakStepPaper.evenCopies_eq w u1 u2 1 (by norm_num)]; exact m1r x h8)
  · exact WeakStepPaper.evenCopy_sub w u1 u2 hw ((WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])) ((WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])) 5 (by norm_num) (by rw [WeakStepPaper.evenCopies_eq w u1 u2 5 (by norm_num)]; exact m5r x h9)

/-- **Item (a) for the glued even child, W_1 odd.** -/
theorem even_of_glue (w u1 u2 : Word) (hw : ¬ Standard.IsBase w) (hreg : regsAt w = (some u1, some u2)) (hph : phase w = 1)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2) (oP oQ : GInt → ℤ)
    (hRP : RespectsAnchored (Standard.oddTile u1) (hWordOf u1 false) (vWordOf u1 false) oP) (βP : ℤ)
    (hNP : ∀ x ∈ tileShape ZTile.one, oP x = zTileOdo ZTile.one x + βP)
    (hRQ : RespectsAnchored (Standard.evenTile u2) (hWordOf u2 true) (vWordOf u2 true) oQ) (βQ : ℤ)
    (hNQ : ∀ x ∈ tileShape ZTile.one, oQ x = zTileOdo ZTile.one x + βQ) (g : GInt → ℤ) (κ : ℕ → ℤ)
    (hg : ∀ i < (evenP w).length + (evenQ w).length, ∀ z ∈ keptSet (pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2)) (pieceFlag (evenP w)) dblEven i,
      g z = placedEven w oP oQ 0 i z + κ i)
    (hex : SameParentOffStringsEven w u1 u2) :
    RespectsAnchored (Standard.evenTile w) (hWordOf w true) (vWordOf w true) g := by
  have hP := ClosedPathAssembly.evenP_of w hph
  have hQ := ClosedPathAssembly.evenQ_of w hph
  have RP := regData_odd u1 _ oP hRP βP hNP
  have RQ := regData_even u2 _ oQ hRQ βQ hNQ
  obtain ⟨dbot, dleft, dright, dtop⟩ := GlueStringDecomp.even_of w u1 u2 hreg hph
  have hInP : ∀ y ∈ placedSites (fourStrings (hWordOf u1 false) (vWordOf u1 false)), y ∈ (↑(Standard.oddTile u1) : Set GInt) := hRP.1
  have hInQ : ∀ y ∈ placedSites (fourStrings (hWordOf u2 true) (vWordOf u2 true)), y ∈ (↑(Standard.evenTile u2) : Set GInt) := hRQ.1
  have pc0 : pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 0 = shiftS (tOddSet u1) (0) := by
    simp [pieceSet, hP, hp, hq, add_assoc]
  have pc1 : pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 1 = shiftS (tOddSet u1) (texV2 (fracOdd u1)) := by
    simp [pieceSet, hP, hp, hq, add_assoc]
  have pc2 : pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 2 = shiftS (tOddSet u1) (texV1Even (fracEven u2) + texV2 (fracEven u2)) := by
    simp [pieceSet, hP, hp, hq, add_assoc]
  have pc3 : pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 3 = shiftS (tOddSet u1) (texV1Even (fracEven u2) + texV2 (fracEven u2) + texV2 (fracOdd u1)) := by
    simp [pieceSet, hP, hp, hq, add_assoc]
  have pc4 : pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 4 = shiftS (tEvenSet u2) (texV1Odd (fracOdd u1)) := by
    simp [pieceSet, hP, hQ, hp, hq, add_assoc]
  have pc5 : pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 5 = shiftS (tEvenSet u2) (texV2 (fracOdd u1) + texV2 (fracOdd u1)) := by
    simp [pieceSet, hP, hQ, hp, hq, add_assoc]
  have m0b : ∀ x ∈ placedSites (hStringAt (hWordOf u1 false) (0)), x ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 0 := by
    intro x hx
    rw [pc0]
    exact mem_copy (Standard.oddTile u1) _ _ (in_bot (hWordOf u1 false) (vWordOf u1 false) _ hInP) (0) (by rw [GlueChain.hStringAt_shift, zero_add]) x hx
  have m4b : ∀ x ∈ placedSites (hStringAt (hWordOf u2 true) (texV1Odd (fracOdd u1))), x ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 4 := by
    intro x hx
    rw [pc4]
    exact mem_copy (Standard.evenTile u2) _ _ (in_bot (hWordOf u2 true) (vWordOf u2 true) _ hInQ) (texV1Odd (fracOdd u1)) (by rw [GlueChain.hStringAt_shift, zero_add]) x hx
  have m5t : ∀ x ∈ placedSites (hRevStringAt (hWordOf u2 true).reverse (texV2 (fracOdd u1) + texV2 (fracOdd u1) + (texV2 (fracEven u2) + (1, -2)))), x ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 5 := by
    intro x hx
    rw [pc5]
    exact mem_copy (Standard.evenTile u2) _ _ (in_top (hWordOf u2 true) (vWordOf u2 true) _ hInQ) (texV2 (fracOdd u1) + texV2 (fracOdd u1)) (by rw [GlueChain.hRevStringAt_shift, RQ.pY, add_comm (texV2 (fracEven u2) + (1, -2)) (texV2 (fracOdd u1) + texV2 (fracOdd u1))]) x hx
  have m3t : ∀ x ∈ placedSites (hRevStringAt (hWordOf u1 false).reverse (texV1Even (fracEven u2) + texV2 (fracEven u2) + texV2 (fracOdd u1) + (texV2 (fracOdd u1) + (1, -2)))), x ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 3 := by
    intro x hx
    rw [pc3]
    exact mem_copy (Standard.oddTile u1) _ _ (in_top (hWordOf u1 false) (vWordOf u1 false) _ hInP) (texV1Even (fracEven u2) + texV2 (fracEven u2) + texV2 (fracOdd u1)) (by rw [GlueChain.hRevStringAt_shift, RP.pY, add_comm (texV2 (fracOdd u1) + (1, -2)) (texV1Even (fracEven u2) + texV2 (fracEven u2) + texV2 (fracOdd u1))]) x hx
  have m0l : ∀ x ∈ placedSites (vRevStringAt (vWordOf u1 false).reverse (0)), x ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 0 := by
    intro x hx
    rw [pc0]
    exact mem_copy (Standard.oddTile u1) _ _ (in_left (hWordOf u1 false) (vWordOf u1 false) _ hInP) (0) (by rw [GlueChain.vRevStringAt_shift, zero_add]) x hx
  have m1l : ∀ x ∈ placedSites (vRevStringAt (vWordOf u1 false).reverse (texV2 (fracOdd u1))), x ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 1 := by
    intro x hx
    rw [pc1]
    exact mem_copy (Standard.oddTile u1) _ _ (in_left (hWordOf u1 false) (vWordOf u1 false) _ hInP) (texV2 (fracOdd u1)) (by rw [GlueChain.vRevStringAt_shift, zero_add]) x hx
  have m5l : ∀ x ∈ placedSites (vRevStringAt (vWordOf u2 true).reverse (texV2 (fracOdd u1) + texV2 (fracOdd u1))), x ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 5 := by
    intro x hx
    rw [pc5]
    exact mem_copy (Standard.evenTile u2) _ _ (in_left (hWordOf u2 true) (vWordOf u2 true) _ hInQ) (texV2 (fracOdd u1) + texV2 (fracOdd u1)) (by rw [GlueChain.vRevStringAt_shift, zero_add]) x hx
  have m4r : ∀ x ∈ placedSites (vStringAt (vWordOf u2 true) (texV1Odd (fracOdd u1) + (texV1Even (fracEven u2) - (1, 1)))), x ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 4 := by
    intro x hx
    rw [pc4]
    exact mem_copy (Standard.evenTile u2) _ _ (in_right (hWordOf u2 true) (vWordOf u2 true) _ hInQ) (texV1Odd (fracOdd u1)) (by rw [GlueChain.vStringAt_shift, RQ.pX, add_comm (texV1Even (fracEven u2) - (1, 1)) (texV1Odd (fracOdd u1))]) x hx
  have m2r : ∀ x ∈ placedSites (vStringAt (vWordOf u1 false) (texV1Even (fracEven u2) + texV2 (fracEven u2) + (texV1Odd (fracOdd u1) - (1, 1)))), x ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 2 := by
    intro x hx
    rw [pc2]
    exact mem_copy (Standard.oddTile u1) _ _ (in_right (hWordOf u1 false) (vWordOf u1 false) _ hInP) (texV1Even (fracEven u2) + texV2 (fracEven u2)) (by rw [GlueChain.vStringAt_shift, RP.pX, add_comm (texV1Odd (fracOdd u1) - (1, 1)) (texV1Even (fracEven u2) + texV2 (fracEven u2))]) x hx
  have m3r : ∀ x ∈ placedSites (vStringAt (vWordOf u1 false) (texV1Even (fracEven u2) + texV2 (fracEven u2) + texV2 (fracOdd u1) + (texV1Odd (fracOdd u1) - (1, 1)))), x ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 3 := by
    intro x hx
    rw [pc3]
    exact mem_copy (Standard.oddTile u1) _ _ (in_right (hWordOf u1 false) (vWordOf u1 false) _ hInP) (texV1Even (fracEven u2) + texV2 (fracEven u2) + texV2 (fracOdd u1)) (by rw [GlueChain.vStringAt_shift, RP.pX, add_comm (texV1Odd (fracOdd u1) - (1, 1)) (texV1Even (fracEven u2) + texV2 (fracEven u2) + texV2 (fracOdd u1))]) x hx
  have hch : ∀ x, x ∈ placedSites (fourStrings (hWordOf w true) (vWordOf w true)) ↔
      x ∈ placedSites (hStringAt (hWordOf u1 false) (0)) ∨ x ∈ placedSites (hStringAt (hWordOf u2 true) (texV1Odd (fracOdd u1))) ∨ x ∈ placedSites (hRevStringAt (hWordOf u2 true).reverse (texV2 (fracOdd u1) + texV2 (fracOdd u1) + (texV2 (fracEven u2) + (1, -2)))) ∨ x ∈ placedSites (hRevStringAt (hWordOf u1 false).reverse (texV1Even (fracEven u2) + texV2 (fracEven u2) + texV2 (fracOdd u1) + (texV2 (fracOdd u1) + (1, -2)))) ∨ x ∈ placedSites (vRevStringAt (vWordOf u1 false).reverse (0)) ∨ x ∈ placedSites (vRevStringAt (vWordOf u1 false).reverse (texV2 (fracOdd u1))) ∨ x ∈ placedSites (vRevStringAt (vWordOf u2 true).reverse (texV2 (fracOdd u1) + texV2 (fracOdd u1))) ∨ x ∈ placedSites (vStringAt (vWordOf u2 true) (texV1Odd (fracOdd u1) + (texV1Even (fracEven u2) - (1, 1)))) ∨ x ∈ placedSites (vStringAt (vWordOf u1 false) (texV1Even (fracEven u2) + texV2 (fracEven u2) + (texV1Odd (fracOdd u1) - (1, 1)))) ∨ x ∈ placedSites (vStringAt (vWordOf u1 false) (texV1Even (fracEven u2) + texV2 (fracEven u2) + texV2 (fracOdd u1) + (texV1Odd (fracOdd u1) - (1, 1)))) := by
    intro x
    unfold fourStrings
    rw [dright, dtop, dbot, dleft]
    simp only [ps_append, List.mem_append, or_assoc]
  obtain ⟨hbot, htop, hleft, hright⟩ := even_of_respects w u1 u2 hreg hph _ _ oP oQ hRP βP hNP hRQ βQ hNQ g κ
    (fun x hx => by
      rw [hg 0 (by simp [hP, hQ]) x (kept_of _ _ _ 0 x (m0b x hx) (fun j hj hf hd hxj => hex x ((hch x).2 (Or.inl hx)) 0 j hj (by norm_num) hf hd (m0b x hx) hxj))]
      simp [placedEven, pl, ClosedPathSum.dot2, affEven, hP, hp, hq])
    (fun x hx => by
      rw [hg 4 (by simp [hP, hQ]) x (kept_of _ _ _ 4 x (m4b x hx) (fun j hj hf hd hxj => hex x ((hch x).2 (Or.inr (Or.inl hx))) 4 j hj (by norm_num) hf hd (m4b x hx) hxj))]
      simp [placedEven, pl, ClosedPathSum.dot2, affEven, hQ, hp])
    (fun x hx => by
      rw [hg 5 (by simp [hP, hQ]) x (kept_of _ _ _ 5 x (m5t x hx) (fun j hj hf hd hxj => hex x ((hch x).2 (Or.inr (Or.inr (Or.inl hx)))) 5 j hj (by norm_num) hf hd (m5t x hx) hxj))]
      simp [placedEven, pl, ClosedPathSum.dot2, affEven, hQ, hp]
      ring)
    (fun x hx => by
      rw [hg 3 (by simp [hP, hQ]) x (kept_of _ _ _ 3 x (m3t x hx) (fun j hj hf hd hxj => hex x ((hch x).2 (Or.inr (Or.inr (Or.inr (Or.inl hx))))) 3 j hj (by norm_num) hf hd (m3t x hx) hxj))]
      simp [placedEven, pl, ClosedPathSum.dot2, affEven, hP, hp, hq]
      ring)
    (fun x hx => by
      rw [hg 0 (by simp [hP, hQ]) x (kept_of _ _ _ 0 x (m0l x hx) (fun j hj hf hd hxj => hex x ((hch x).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx)))))) 0 j hj (by norm_num) hf hd (m0l x hx) hxj))]
      simp [placedEven, pl, ClosedPathSum.dot2, affEven, hP, hp, hq])
    (fun x hx => by
      rw [hg 1 (by simp [hP, hQ]) x (kept_of _ _ _ 1 x (m1l x hx) (fun j hj hf hd hxj => hex x ((hch x).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx))))))) 1 j hj (by norm_num) hf hd (m1l x hx) hxj))]
      simp [placedEven, pl, ClosedPathSum.dot2, affEven, hP, hp, hq]
      ring)
    (fun x hx => by
      rw [hg 5 (by simp [hP, hQ]) x (kept_of _ _ _ 5 x (m5l x hx) (fun j hj hf hd hxj => hex x ((hch x).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx)))))))) 5 j hj (by norm_num) hf hd (m5l x hx) hxj))]
      simp [placedEven, pl, ClosedPathSum.dot2, affEven, hQ, hp]
      ring)
    (fun x hx => by
      rw [hg 4 (by simp [hP, hQ]) x (kept_of _ _ _ 4 x (m4r x hx) (fun j hj hf hd hxj => hex x ((hch x).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx))))))))) 4 j hj (by norm_num) hf hd (m4r x hx) hxj))]
      simp [placedEven, pl, ClosedPathSum.dot2, affEven, hQ, hp])
    (fun x hx => by
      rw [hg 2 (by simp [hP, hQ]) x (kept_of _ _ _ 2 x (m2r x hx) (fun j hj hf hd hxj => hex x ((hch x).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx)))))))))) 2 j hj (by norm_num) hf hd (m2r x hx) hxj))]
      simp [placedEven, pl, ClosedPathSum.dot2, affEven, hP, hp, hq]
      ring)
    (fun x hx => by
      rw [hg 3 (by simp [hP, hQ]) x (kept_of _ _ _ 3 x (m3r x hx) (fun j hj hf hd hxj => hex x ((hch x).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hx))))))))))) 3 j hj (by norm_num) hf hd (m3r x hx) hxj))]
      simp [placedEven, pl, ClosedPathSum.dot2, affEven, hP, hp, hq]
      ring)
  refine ⟨fun x hx => ?_, hbot, htop, hleft, hright⟩
  rcases (hch x).1 hx with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact WeakStepPaper.evenCopy_sub w u1 u2 hw ((WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])) ((WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])) 0 (by norm_num) (by rw [WeakStepPaper.evenCopies_eq w u1 u2 0 (by norm_num)]; exact m0b x h0)
  · exact WeakStepPaper.evenCopy_sub w u1 u2 hw ((WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])) ((WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])) 4 (by norm_num) (by rw [WeakStepPaper.evenCopies_eq w u1 u2 4 (by norm_num)]; exact m4b x h1)
  · exact WeakStepPaper.evenCopy_sub w u1 u2 hw ((WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])) ((WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])) 5 (by norm_num) (by rw [WeakStepPaper.evenCopies_eq w u1 u2 5 (by norm_num)]; exact m5t x h2)
  · exact WeakStepPaper.evenCopy_sub w u1 u2 hw ((WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])) ((WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])) 3 (by norm_num) (by rw [WeakStepPaper.evenCopies_eq w u1 u2 3 (by norm_num)]; exact m3t x h3)
  · exact WeakStepPaper.evenCopy_sub w u1 u2 hw ((WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])) ((WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])) 0 (by norm_num) (by rw [WeakStepPaper.evenCopies_eq w u1 u2 0 (by norm_num)]; exact m0l x h4)
  · exact WeakStepPaper.evenCopy_sub w u1 u2 hw ((WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])) ((WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])) 1 (by norm_num) (by rw [WeakStepPaper.evenCopies_eq w u1 u2 1 (by norm_num)]; exact m1l x h5)
  · exact WeakStepPaper.evenCopy_sub w u1 u2 hw ((WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])) ((WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])) 5 (by norm_num) (by rw [WeakStepPaper.evenCopies_eq w u1 u2 5 (by norm_num)]; exact m5l x h6)
  · exact WeakStepPaper.evenCopy_sub w u1 u2 hw ((WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])) ((WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])) 4 (by norm_num) (by rw [WeakStepPaper.evenCopies_eq w u1 u2 4 (by norm_num)]; exact m4r x h7)
  · exact WeakStepPaper.evenCopy_sub w u1 u2 hw ((WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])) ((WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])) 2 (by norm_num) (by rw [WeakStepPaper.evenCopies_eq w u1 u2 2 (by norm_num)]; exact m2r x h8)
  · exact WeakStepPaper.evenCopy_sub w u1 u2 hw ((WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])) ((WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])) 3 (by norm_num) (by rw [WeakStepPaper.evenCopies_eq w u1 u2 3 (by norm_num)]; exact m3r x h9)

/-! ### `GlueRespectsInput` -/

theorem normal_of (o : PartialOdometer) (β : ℤ) (h : JointFamily.FirstTileNormal o 0 β) :
    ∀ x ∈ tileShape ZTile.one, o.val x = zTileOdo ZTile.one x + β := by
  intro x hx
  have := (h x hx).2
  simp only [JointFamily.normed, dotS, Prod.fst_zero, Prod.snd_zero, zero_mul, add_zero, sub_zero] at this
  linarith

/-- **`GlueRespectsInput` for the paper's data**, from the same-parent exclusions on the strings of the uncorrected
children (`SameParentOffStringsOdd`, `SameParentOffStringsEven`, the remaining geometric input). -/
theorem glueRespectsInput (D : JointFamily.JointData) (hS : D.S = WeakStepPaper.paperS)
    (hex : ∀ w u1 u2 : Word, ¬ Standard.IsBase w → regsAt w = (some u1, some u2) →
      (¬ JointFamily.CorrectedAfterThree w → SameParentOffStringsOdd w u1 u2) ∧
        (¬ JointFamily.CorrectedAfterTwo w → SameParentOffStringsEven w u1 u2)) :
    WeakStepAssembly.GlueRespectsInput D := by
  intro f w u1 u2 hgood hw hreg hnorm κo κe go ge hglue
  obtain ⟨-, -, hgo, -, -, hge⟩ := hglue
  have hl1 : u1.length < w.length := JointInduction.regsAt_lt w u1 (Or.inl (by rw [hreg]))
  have hl2 : u2.length < w.length := JointInduction.regsAt_lt w u2 (Or.inr (by rw [hreg]))
  have hp : (parentsAt w).odd = fracOdd u1 := (WeakStepAssembly.regsAt_parents w).1 u1 (by rw [hreg])
  have hq : (parentsAt w).even = fracEven u2 := (WeakStepAssembly.regsAt_parents w).2 u2 (by rw [hreg])
  obtain ⟨hS1, -⟩ := hgood u1 hl1
  obtain ⟨hS2, -⟩ := hgood u2 hl2
  have hdO : (f u1).tOdd.dom = Standard.oddTile u1 := by
    rw [(WeakStepAssembly.slice_domains D f u1 hS1).1, hS]; rfl
  have hdE : (f u2).tEven.dom = Standard.evenTile u2 := by
    rw [(WeakStepAssembly.slice_domains D f u2 hS2).2, hS]; rfl
  have hRP := (WeakStepAssembly.slice_respects D f u1 hS1).1
  have hRQ := (WeakStepAssembly.slice_respects D f u2 hS2).2
  rw [hdO] at hRP
  rw [hdE] at hRQ
  obtain ⟨⟨βP, hNP⟩, -⟩ := hnorm u1 hl1
  obtain ⟨-, ⟨βQ, hNQ⟩⟩ := hnorm u2 hl2
  obtain ⟨hexO, hexE⟩ := hex w u1 u2 hw hreg
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · by_cases hph : phase w = 1
    · exact odd_of_glue w u1 u2 hw hreg hph hp hq _ _ hRP βP (normal_of _ _ hNP) hRQ βQ (normal_of _ _ hNQ) go κo hgo
        (hexO hc)
    · exact odd_ef_glue w u1 u2 hw hreg hph hp hq _ _ hRP βP (normal_of _ _ hNP) hRQ βQ (normal_of _ _ hNQ) go κo hgo
        (hexO hc)
  · by_cases hph : phase w = 1
    · exact even_of_glue w u1 u2 hw hreg hph hp hq _ _ hRP βP (normal_of _ _ hNP) hRQ βQ (normal_of _ _ hNQ) ge κe hge
        (hexE hc)
    · exact even_ef_glue w u1 u2 hw hreg hph hp hq _ _ hRP βP (normal_of _ _ hNP) hRQ βQ (normal_of _ _ hNQ) ge κe hge
        (hexE hc)

/-- **`GlueLatticeInput` for the paper's data**: item (c) of the glued children follows from item (a) word by word
(`LatticeOfRespects`), with the zero-slope normalisation of the registers (`TileSlopeZero`). -/
theorem glueLatticeInput (D : JointFamily.JointData) (hS : D.S = WeakStepPaper.paperS)
    (hsl : WeakStepAssembly.TileSlopeZero D)
    (hex : ∀ w u1 u2 : Word, ¬ Standard.IsBase w → regsAt w = (some u1, some u2) →
      (¬ JointFamily.CorrectedAfterThree w → SameParentOffStringsOdd w u1 u2) ∧
        (¬ JointFamily.CorrectedAfterTwo w → SameParentOffStringsEven w u1 u2)) :
    WeakStepAssembly.GlueLatticeInput D := by
  intro f w u1 u2 hgood hw hreg κo κe go ge hglue
  have hr := glueRespectsInput D hS hex f w u1 u2 hgood hw hreg (fun u hu => hsl f w.length hgood u hu) κo κe go ge
    hglue
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · exact LatticeOfRespects.latticeSelfCompatible_odd w ⟨Standard.oddTile w, go⟩ rfl (hr.1 hc)
  · exact LatticeOfRespects.latticeSelfCompatible_even w ⟨Standard.evenTile w, ge⟩ rfl (hr.2 hc)

end FLatticePaper.Tiles.GlueRespectsAll
