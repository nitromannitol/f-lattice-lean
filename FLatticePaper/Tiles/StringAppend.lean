import FLatticePaper.Tiles.StringJoin
import FLatticePaper.Tiles.PseudoSquareAnchored
import FLatticePaper.Tiles.ClosedPathCorners
import FLatticePaper.Tiles.StdCornerAnchors

/-! # The zero-one strings of a concatenated word

A boundary string of a child word is the concatenation of the strings of its blocks (`childWords`), the later blocks started at
the end of the earlier ones. This module gives the four string kinds of `PseudoSquareSites` on a concatenation `X ++ Y`:

* forward horizontal, when `X` ends with `p` (so the doubling rule `q q ↦ q q_d` does not cross the seam): this is
  `StringJoin.hStringAt_join`;
* `hRevStringAt_append`: reversed horizontal, when `Y` starts with `p`;
* `vStringAt_append`, `vRevStringAt_append`: vertical, with no condition (vertical strings have no enlarged tiles).

In each case the second string starts at the first one's start plus its steps plus the step of the seam. -/

namespace FLatticePaper.Tiles.StringAppend

open FLatticePaper.Tiles

/-- A string `tiles.zip (scanl (+) c steps)` of a concatenation. -/
theorem zip_scanl_append {α : Type*} (TX TY : List α) (sX sY : List GInt) (j c : GInt)
    (hX : TX.length = sX.length + 1) :
    (TX ++ TY).zip (List.scanl (· + ·) c (sX ++ j :: sY)) =
      TX.zip (List.scanl (· + ·) c sX) ++ TY.zip (List.scanl (· + ·) (sX.foldl (· + ·) c + j) sY) := by
  rw [List.scanl_append, List.scanl_cons, List.tail_cons, List.zip_append (by simp [hX])]

theorem foldl_add_eq (c : GInt) (s : List GInt) : s.foldl (· + ·) c = c + s.sum := by
  induction s generalizing c with
  | nil => simp
  | cons a s ih => simp [ih, add_assoc]

/-- The consecutive pairs of a concatenation: those of the two parts and the pair at the seam. -/
theorem zip_tail_append (U' V' : BinaryWord) (u v : Letter) :
    (U' ++ [u] ++ v :: V').zip (U' ++ [u] ++ v :: V').tail =
      (U' ++ [u]).zip (U' ++ [u]).tail ++ (u, v) :: (v :: V').zip (v :: V').tail := by
  induction U' with
  | nil => simp
  | cons a U'' ih =>
    cases U'' with
    | nil => simp
    | cons b U''' =>
      simp only [List.cons_append, List.tail_cons, List.zip_cons_cons] at ih ⊢
      rw [ih]

/-- The enlargement rule does not cross a seam before a `p`. -/
theorem tileSeqAux_append_cons_p (prev : Option Letter) (U V' : BinaryWord) :
    tileSeqAux prev (U ++ Letter.p :: V') = tileSeqAux prev U ++ tileSeqAux none (Letter.p :: V') := by
  induction U generalizing prev with
  | nil => cases prev <;> rfl
  | cons x U ih => simp only [List.cons_append, tileSeqAux, ih]

/-- **The reversed horizontal string of `U ++ Y`**, when `Y` starts with `p`. -/
theorem hRevStringAt_append (U' V' : BinaryWord) (u : Letter) (c : GInt) :
    hRevStringAt (U' ++ [u] ++ Letter.p :: V') c =
      hRevStringAt (U' ++ [u]) c ++ hRevStringAt (Letter.p :: V')
        (c + (((U' ++ [u]).zip (U' ++ [u]).tail).map fun ab => hRevOffset ab.1 ab.2).sum + hRevOffset u Letter.p) := by
  have ht : tileSeq (U' ++ [u] ++ Letter.p :: V') = tileSeq (U' ++ [u]) ++ tileSeq (Letter.p :: V') := by
    unfold tileSeq
    exact tileSeqAux_append_cons_p none _ V'
  unfold hRevStringAt
  rw [ht, zip_tail_append, List.map_append, List.map_cons, zip_scanl_append _ _ _ _ _ c, foldl_add_eq]
  simp [tileSeq, StringJoin.tileSeqAux_length]

/-- **The forward vertical string of `X ++ Y`.** -/
theorem vStringAt_append (X Y' : BinaryWord) (y : Letter) (c : GInt) (hX : X ≠ []) :
    vStringAt (X ++ y :: Y') c =
      vStringAt X c ++ vStringAt (y :: Y') (c + (X.tail.map vOffset).sum + vOffset y) := by
  unfold vStringAt
  rw [List.tail_append_of_ne_nil hX]
  simp only [List.map_append, List.map_cons, List.tail_cons]
  rw [zip_scanl_append _ _ _ _ _ c, foldl_add_eq]
  obtain ⟨a, X', rfl⟩ := List.exists_cons_of_ne_nil hX
  simp

/-- **The reversed vertical string of `U ++ Y`.** -/
theorem vRevStringAt_append (U' V' : BinaryWord) (u v : Letter) (c : GInt) :
    vRevStringAt (U' ++ [u] ++ v :: V') c =
      vRevStringAt (U' ++ [u]) c ++ vRevStringAt (v :: V')
        (c + (((U' ++ [u]).zip (U' ++ [u]).tail).map fun ab => vRevOffset ab.1 ab.2).sum + vRevOffset u v) := by
  unfold vRevStringAt
  rw [zip_tail_append]
  simp only [List.map_append, List.map_cons]
  rw [zip_scanl_append _ _ _ _ _ c, foldl_add_eq]
  simp


/-! ### The seams of the boundary strings of a child

The blocks of a child word begin with `q` and end with `p` (horizontal), or begin with `p` and end with `q` (vertical), so the
four kinds of seam have a fixed step: `(1, 1)`, `(1, 0)`, `(-1, 1)`, `(-1, 2)`. -/

theorem exists_snoc_of_getLast (X : BinaryWord) (l : Letter) (h : X.getLast? = some l) : ∃ X', X = X' ++ [l] := by
  induction X using List.reverseRecOn with
  | nil => simp at h
  | append_singleton X' x _ =>
    simp at h
    exact ⟨X', by rw [h]⟩

theorem exists_cons_of_head (Y : BinaryWord) (l : Letter) (h : Y.head? = some l) : ∃ Y', Y = l :: Y' := by
  cases Y with
  | nil => simp at h
  | cons y Y' =>
    simp at h
    exact ⟨Y', by rw [h]⟩

/-- A forward horizontal seam `p | q`. -/
theorem hStringAt_app (X Y : BinaryWord) (c : GInt) (hXl : X.getLast? = some Letter.p) (hYh : Y.head? = some Letter.q) :
    hStringAt (X ++ Y) c = hStringAt X c ++ hStringAt Y (lastPosOf (hStringAt X c) + (1, 1)) := by
  obtain ⟨X', rfl⟩ := exists_snoc_of_getLast X _ hXl
  obtain ⟨Y', rfl⟩ := exists_cons_of_head Y _ hYh
  rw [StringJoin.hStringAt_join, ClosedPathCorners.hFwd_lastPos _ _ (by simp)]
  rfl

/-- A reversed horizontal seam `q | p`. -/
theorem hRevStringAt_app (U V : BinaryWord) (c : GInt) (hUl : U.getLast? = some Letter.q)
    (hVh : V.head? = some Letter.p) :
    hRevStringAt (U ++ V) c = hRevStringAt U c ++ hRevStringAt V (lastPosOf (hRevStringAt U c) + (1, 0)) := by
  obtain ⟨U', rfl⟩ := exists_snoc_of_getLast U _ hUl
  obtain ⟨V', rfl⟩ := exists_cons_of_head V _ hVh
  rw [hRevStringAt_append]
  congr 2
  unfold hRevStringAt
  rw [ClosedPathCorners.lastPos_zip_scanl _ _ _ (by simp [tileSeq, StringJoin.tileSeqAux_length])]
  rfl

/-- A forward vertical seam `q | p`. -/
theorem vStringAt_app (X Y : BinaryWord) (c : GInt) (hX : X ≠ []) (hYh : Y.head? = some Letter.p) :
    vStringAt (X ++ Y) c = vStringAt X c ++ vStringAt Y (lastPosOf (vStringAt X c) + (-1, 1)) := by
  obtain ⟨Y', rfl⟩ := exists_cons_of_head Y _ hYh
  rw [vStringAt_append X Y' _ c hX]
  congr 2
  obtain ⟨a, X', rfl⟩ := List.exists_cons_of_ne_nil hX
  rw [StdCornerAnchors.stdLastPos_vStringAt]
  rfl

/-- A reversed vertical seam `p | q`. -/
theorem vRevStringAt_app (U V : BinaryWord) (c : GInt) (hUl : U.getLast? = some Letter.p)
    (hVh : V.head? = some Letter.q) :
    vRevStringAt (U ++ V) c = vRevStringAt U c ++ vRevStringAt V (lastPosOf (vRevStringAt U c) + (-1, 2)) := by
  obtain ⟨U', rfl⟩ := exists_snoc_of_getLast U _ hUl
  obtain ⟨V', rfl⟩ := exists_cons_of_head V _ hVh
  rw [vRevStringAt_append]
  congr 2
  unfold vRevStringAt
  rw [ClosedPathCorners.lastPos_zip_scanl _ _ _ (by simp)]
  rfl

/-- The last tile of a reversed vertical string moves with its start. -/
theorem lastPos_vRevStringAt (u : BinaryWord) (c : GInt) (hu : u ≠ []) :
    lastPosOf (vRevStringAt u c) = c + lastPosOf (vRevStringAt u 0) := by
  have hl : (u.map letterZTile).length = ((u.zip u.tail).map fun ab => vRevOffset ab.1 ab.2).length + 1 := by
    obtain ⟨a, u', rfl⟩ := List.exists_cons_of_ne_nil hu
    simp
  unfold vRevStringAt
  rw [ClosedPathCorners.lastPos_zip_scanl _ _ _ hl, ClosedPathCorners.lastPos_zip_scanl _ _ _ hl, zero_add]

end FLatticePaper.Tiles.StringAppend
