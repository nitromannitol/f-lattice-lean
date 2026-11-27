import FLatticePaper.Tiles.GHJoin

/-! Stage 1 of the text form of clause (d) (the stacked zero-one strings of the interfaces).

For a binary word `b`, `Bp b = B(b)` is its boundary path `gH b` and `Dp b = D(b)` is the reversed path `rev (B b)`. The join laws of
the text, `B(ab) = B(a) * i * B(b)` and `D(ab) = D(b) * i * D(a)` for `a` ending in `p` and `b` starting with `q`, are
`GHJoin.gH_join` and its reversal. -/

namespace FLatticePaper.Tiles.StackedPaths

open FLatticePaper.Tiles

/-- The boundary path `B(b)` of a binary word. -/
def Bp (b : BinaryWord) : F2Word := gH b

/-- The reversed boundary path `D(b) = rev (B b)`. -/
def Dp (b : BinaryWord) : F2Word := (gH b).reverse

/-- **The join law of `B`.** -/
theorem Bp_join (a b : BinaryWord) (ha : a.getLast? = some Letter.p) (hb : b.head? = some Letter.q) :
    Bp (a ++ b) = Bp a ++ [Unit4.i] ++ Bp b := by
  obtain ⟨X', rfl⟩ := List.getLast?_eq_some_iff.1 ha
  cases b with
  | nil => simp at hb
  | cons y Y =>
    simp only [List.head?_cons, Option.some.injEq] at hb
    subst hb
    exact GHJoin.gH_join X' Y

/-- **The join law of `D`**: the join read backwards. -/
theorem Dp_join (a b : BinaryWord) (ha : a.getLast? = some Letter.p) (hb : b.head? = some Letter.q) :
    Dp (a ++ b) = Dp b ++ [Unit4.i] ++ Dp a := by
  have h := Bp_join a b ha hb
  simp only [Bp] at h
  simp [Dp, h, List.reverse_append, List.reverse_cons, List.append_assoc]

end FLatticePaper.Tiles.StackedPaths
