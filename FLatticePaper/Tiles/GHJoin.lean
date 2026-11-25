import FLatticePaper.Tiles.PseudoSquare
import FLatticePaper.Tiles.BinaryWords

/-! Task Q25 (c), the join rule of the pseudo-square map `gH`.

`gH w` is the pair map of the tile sequence of the binary word `w`, followed by a final `1`. For a word `X' ++ [p]` ending in
the letter `p` and a word `q :: Y'` starting with `q`, the tile sequence of the concatenation is the concatenation of the tile
sequences, the boundary pair is `gPair zero one = [1, i]`, and so `gH (X ++ Y) = gH X ++ [i] ++ gH Y`. This is the single
combinatorial identity that turns the register recursion of the bottom edges into the child words of the quad. -/

namespace FLatticePaper.Tiles.GHJoin

open FLatticePaper.Tiles

/-- The pair map of a tile sequence, in recursive form. -/
def G : List ZTile → F2Word
  | [] => []
  | [_] => []
  | a :: b :: r => gPair a b ++ G (b :: r)

theorem G_cons_cons (a b : ZTile) (r : List ZTile) : G (a :: b :: r) = gPair a b ++ G (b :: r) := rfl

theorem G_singleton (z : ZTile) : G [z] = [] := rfl

/-- The flat-map form of the pair map is the recursive `G`. -/
theorem pairs_eq_G : ∀ ts : List ZTile, ((ts.zip ts.tail).flatMap fun ab => gPair ab.1 ab.2) = G ts
  | [] => rfl
  | [_] => rfl
  | a :: b :: r => by
      have ih := pairs_eq_G (b :: r)
      simp only [List.tail_cons] at ih
      rw [G_cons_cons, ← ih]
      simp [List.zip_cons_cons, List.flatMap_cons]

/-- The pair map of `gH` (the trailing `1` is outside). -/
theorem gH_eq (w : BinaryWord) : gH w = G (tileSeq w) ++ [Unit4.one] := by
  show ((tileSeq w).zip (tileSeq w).tail).flatMap (fun ab => gPair ab.1 ab.2) ++ [Unit4.one] = _
  rw [pairs_eq_G]

/-- Splitting the pair map at a letter `z`: `G (a ++ z :: v) = G (a ++ [z]) ++ G (z :: v)`. -/
theorem G_split (a : List ZTile) (z : ZTile) (v : List ZTile) :
    G (a ++ z :: v) = G (a ++ [z]) ++ G (z :: v) := by
  induction a with
  | nil => rw [List.nil_append, List.nil_append, G_singleton, List.nil_append]
  | cons x a ih =>
    cases a with
    | nil =>
      show G (x :: z :: v) = G (x :: [z]) ++ G (z :: v)
      rw [G_cons_cons, G_cons_cons, G_singleton, List.append_nil]
    | cons y a' =>
      show G (x :: y :: (a' ++ z :: v)) = G (x :: y :: (a' ++ [z])) ++ G (z :: v)
      have ih' : G (y :: a' ++ z :: v) = G (y :: a' ++ [z]) ++ G (z :: v) := ih
      rw [G_cons_cons, G_cons_cons]
      have e : G (y :: (a' ++ z :: v)) = G (y :: a' ++ z :: v) := rfl
      have e2 : G (y :: (a' ++ [z])) = G (y :: a' ++ [z]) := rfl
      rw [e, e2, ih', List.append_assoc]

/-- The tile sequence of the letter `p` is `zero` after any previous letter, and the tile after `p` is independent of it. -/
theorem tileSeqAux_some_p (Y : BinaryWord) : tileSeqAux (some Letter.p) Y = tileSeqAux none Y := by
  induction Y with
  | nil => rfl
  | cons y Y ih =>
    cases y <;> simp [tileSeqAux, ih]

/-- The tile sequence of a word `X ++ [p]` is the tile sequence of `X` followed by `zero`. -/
theorem tileSeqAux_snoc_p (prev : Option Letter) (X : BinaryWord) :
    tileSeqAux prev (X ++ [Letter.p]) = tileSeqAux prev X ++ [ZTile.zero] := by
  induction X generalizing prev with
  | nil => simp [tileSeqAux]
  | cons x X ih =>
    cases x <;> simp [tileSeqAux, ih]

theorem tileSeq_snoc_p (X : BinaryWord) : tileSeq (X ++ [Letter.p]) = tileSeq X ++ [ZTile.zero] :=
  tileSeqAux_snoc_p none X

/-- The tile sequence of `X' ++ [p] ++ Y` is the tile sequence of `X' ++ [p]` followed by that of `Y` after `p`. -/
theorem tileSeqAux_append_p (prev : Option Letter) (X' Y : BinaryWord) :
    tileSeqAux prev (X' ++ [Letter.p] ++ Y) = tileSeqAux prev (X' ++ [Letter.p]) ++ tileSeqAux (some Letter.p) Y := by
  induction X' generalizing prev with
  | nil => simp [tileSeqAux]
  | cons x X' ih =>
    simp only [List.cons_append]
    cases x <;> simp only [tileSeqAux, ih, List.cons_append]

theorem tileSeq_append_p (X' Y : BinaryWord) :
    tileSeq (X' ++ [Letter.p] ++ Y) = tileSeq (X' ++ [Letter.p]) ++ tileSeqAux (some Letter.p) Y :=
  tileSeqAux_append_p none X' Y

/-- The join: `gH (X' ++ [p] ++ (q :: Y')) = gH (X' ++ [p]) ++ [i] ++ gH (q :: Y')`. -/
theorem gH_join (X' Y' : BinaryWord) :
    gH (X' ++ [Letter.p] ++ (Letter.q :: Y')) = gH (X' ++ [Letter.p]) ++ [Unit4.i] ++ gH (Letter.q :: Y') := by
  have hl : tileSeq (X' ++ [Letter.p] ++ (Letter.q :: Y')) =
      tileSeq X' ++ [ZTile.zero] ++ (ZTile.one :: tileSeqAux (some Letter.q) Y') := by
    rw [tileSeq_append_p, tileSeq_snoc_p, tileSeqAux_some_p]
    rfl
  have hr : tileSeq (Letter.q :: Y') = ZTile.one :: tileSeqAux (some Letter.q) Y' := rfl
  rw [gH_eq, gH_eq, gH_eq, hl, hr, tileSeq_snoc_p]
  have hs : tileSeq X' ++ [ZTile.zero] ++ (ZTile.one :: tileSeqAux (some Letter.q) Y') =
      tileSeq X' ++ ZTile.zero :: (ZTile.one :: tileSeqAux (some Letter.q) Y') := by
    simp
  rw [hs, G_split, G_cons_cons]
  simp [gPair, List.append_assoc]

end FLatticePaper.Tiles.GHJoin
