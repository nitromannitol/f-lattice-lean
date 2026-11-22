import FLatticePaper.Tiles.PseudoSquareSites

namespace FLatticePaper.Tiles

/-! The literal pseudo-square predicate, `def:tile_boundary_strings` (lines 1626-1636) as printed, with the starts that
the text does not fix quantified existentially. This is the PROVISIONAL literal reading of the task-27 call; it is not the
walk reading of `PseudoSquareAlong` and not the fixed stacking of `pseudoStrings` (`stackH`, `stackV`).

The text fixes `c(T^+_{1,h}) = c(T^-_{1,v}) = c(T)`: the forward horizontal string of `w_h` and the reversed vertical string
of `rev w_v` start at `c(T) = lowerLeftList T`. The starts `s1` of the reversed horizontal string `T^-_{1,h}` and `s2` of the
forward vertical string `T^+_{1,v}` are not fixed by the text: they range over the sites of `T`. Each string is rigid once its
first tile is placed (lemma:zero-one-fixed-offsets), which is `hStringAt`, `hRevStringAt`, `vStringAt`, `vRevStringAt`.
Clause 1: the placed sites lie in `T`. Clause 2: they cover `∂⁻T = innerBoundaryList T`. -/

/-- The four strings with the starts `c` (forward horizontal, reversed vertical), `s1` (reversed horizontal) and `s2`
(forward vertical). -/
def literalStrings (wh wv : BinaryWord) (c s1 s2 : GInt) : List (ZTile × GInt) :=
  hStringAt wh c ++ hRevStringAt wh.reverse s1 ++ vRevStringAt wv.reverse c ++ vStringAt wv s2

/-- The two clauses of the literal definition for the starts `c`, `s1`, `s2`. -/
def LiteralWith (T : List GInt) (wh wv : BinaryWord) (c s1 s2 : GInt) : Prop :=
  (∀ x ∈ placedSites (literalStrings wh wv c s1 s2), x ∈ T) ∧
    ∀ x ∈ innerBoundaryList T, x ∈ placedSites (literalStrings wh wv c s1 s2)

/-- `T` is a `(w_h, w_v)`-pseudo-square in the literal reading: with `c = c(T)`, some starts `s1, s2` in `T` satisfy the
two clauses. For `T` with no sites the predicate is false. -/
def IsPseudoSquareLiteral (T : List GInt) (wh wv : BinaryWord) : Prop :=
  match lowerLeftList T with
  | none => False
  | some c => ∃ s1 ∈ T, ∃ s2 ∈ T, LiteralWith T wh wv c s1 s2

/-- The decision procedure for `IsPseudoSquareLiteral`. The clauses on the fixed strings are checked once. The starts are
first restricted to the sites `s` whose string lies in `T` (`cands1`, `cands2`), since that condition involves one start
only; the covering clause is then checked for the remaining pairs. -/
def literalCheck (T : List GInt) (wh wv : BinaryWord) : Bool :=
  match lowerLeftList T with
  | none => false
  | some c =>
    let A := placedSites (hStringAt wh c)
    let C := placedSites (vRevStringAt wv.reverse c)
    let bd := innerBoundaryList T
    let cands1 := T.filter fun s => (placedSites (hRevStringAt wh.reverse s)).all fun x => T.contains x
    let cands2 := T.filter fun s => (placedSites (vStringAt wv s)).all fun x => T.contains x
    (A.all fun x => T.contains x) && (C.all fun x => T.contains x) &&
      cands1.any fun s1 => cands2.any fun s2 =>
        bd.all fun x => A.contains x || (C.contains x ||
          ((placedSites (hRevStringAt wh.reverse s1)).contains x || (placedSites (vStringAt wv s2)).contains x))

theorem mem_placedSites_literal (wh wv : BinaryWord) (c s1 s2 x : GInt) :
    x ∈ placedSites (literalStrings wh wv c s1 s2) ↔
      x ∈ placedSites (hStringAt wh c) ∨ x ∈ placedSites (vRevStringAt wv.reverse c) ∨
        x ∈ placedSites (hRevStringAt wh.reverse s1) ∨ x ∈ placedSites (vStringAt wv s2) := by
  simp only [literalStrings, placedSites, List.flatMap_append, List.mem_append]
  tauto

/-- The decision procedure is correct: the pruned search finds the same starts as the literal existential. -/
theorem literalCheck_iff (T : List GInt) (wh wv : BinaryWord) :
    literalCheck T wh wv = true ↔ IsPseudoSquareLiteral T wh wv := by
  unfold literalCheck IsPseudoSquareLiteral
  cases h : lowerLeftList T with
  | none => simp
  | some c =>
    simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_filter, List.contains_iff_mem,
      Bool.or_eq_true]
    constructor
    · rintro ⟨⟨hA, hC⟩, s1, ⟨hs1, hP1⟩, s2, ⟨hs2, hP2⟩, hcov⟩
      refine ⟨s1, hs1, s2, hs2, fun x hx => ?_, fun x hx => ?_⟩
      · rcases (mem_placedSites_literal wh wv c s1 s2 x).mp hx with h1 | h1 | h1 | h1
        · exact hA x h1
        · exact hC x h1
        · exact hP1 x h1
        · exact hP2 x h1
      · exact (mem_placedSites_literal wh wv c s1 s2 x).mpr (hcov x hx)
    · rintro ⟨s1, hs1, s2, hs2, hin, hcov⟩
      have hA : ∀ x, x ∈ placedSites (hStringAt wh c) → x ∈ T := fun x hx =>
        hin x ((mem_placedSites_literal wh wv c s1 s2 x).mpr (Or.inl hx))
      have hC : ∀ x, x ∈ placedSites (vRevStringAt wv.reverse c) → x ∈ T := fun x hx =>
        hin x ((mem_placedSites_literal wh wv c s1 s2 x).mpr (Or.inr (Or.inl hx)))
      have hP1 : ∀ x, x ∈ placedSites (hRevStringAt wh.reverse s1) → x ∈ T := fun x hx =>
        hin x ((mem_placedSites_literal wh wv c s1 s2 x).mpr (Or.inr (Or.inr (Or.inl hx))))
      have hP2 : ∀ x, x ∈ placedSites (vStringAt wv s2) → x ∈ T := fun x hx =>
        hin x ((mem_placedSites_literal wh wv c s1 s2 x).mpr (Or.inr (Or.inr (Or.inr hx))))
      exact ⟨⟨hA, hC⟩, s1, ⟨hs1, hP1⟩, s2, ⟨hs2, hP2⟩, fun x hx =>
        (mem_placedSites_literal wh wv c s1 s2 x).mp (hcov x hx)⟩
