import FLatticePaper.Tiles.BottomEdges
import FLatticePaper.Tiles.StandardTiles
import FLatticePaper.Tiles.StandardClauseA
import FLatticePaper.Tiles.StandardBoundary

/-! Task 55 (R1/R3): the register-to-tile link S2, and its induction over words.

S2 w says: when the prefix `w` has read a letter `1` or `2`, the odd register of `w` (`(regsAfter w).1`, the first arc of the
odd bottom recursion) is the first arc of the boundary of the odd register tile of `w`; and likewise for the even register with
the letters `1` or `3`. S2 is used only for prefixes (the parents). The step `S2 pre → S2 (pre ++ [d])` is the single hypothesis
of the induction `S2_all`; it is where the child's arcs are proved from the parents' arcs (pattern comparisons and R1 covering).
Everything else is proved here: the register recursion, its identification with `bottomEdges`, and the induction. -/

namespace FLatticePaper.Tiles.RegisterInduction

open FLatticePaper FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.Standard FLatticePaper.Tiles.StandardClause
open FLatticePaper.Tiles.StandardBoundary

/-- The registers after reading `rest` from the prefix `pre`: the recursion of `bottomFrom`, as a function of the registers. -/
def regsGo : Word → Word → F2Word × F2Word → F2Word × F2Word
  | _, [], regs => regs
  | pre, x :: rest, regs => regsGo (pre ++ [x]) rest (updateRegs x regs (prefixEdges pre regs.1 regs.2))

/-- The registers after the whole word `w`. -/
def regsAfter (w : Word) : F2Word × F2Word := regsGo [] w ([], [])

theorem bottomFrom_eq_regsGo (rest : Word) : ∀ (pre : Word) (regs : F2Word × F2Word),
    bottomFrom pre rest regs =
      prefixEdges (pre ++ rest) (regsGo pre rest regs).1 (regsGo pre rest regs).2 := by
  induction rest with
  | nil => intro pre regs; simp [bottomFrom, regsGo]
  | cons x rest ih =>
    intro pre regs
    simp only [bottomFrom, regsGo, ih, List.append_assoc, List.singleton_append]

/-- The bottom edges of a word are the prefix edges at the registers after the word. -/
theorem bottomEdges_eq_regs (w : Word) :
    bottomEdges w = prefixEdges w (regsAfter w).1 (regsAfter w).2 := by
  have h := bottomFrom_eq_regsGo w [] ([], [])
  simpa [bottomEdges, regsAfter] using h

theorem oddBottom_eq_regs (w : Word) :
    oddBottom w = (prefixEdges w (regsAfter w).1 (regsAfter w).2).1 := by
  unfold oddBottom
  rw [bottomEdges_eq_regs]

theorem evenBottom_eq_regs (w : Word) :
    evenBottom w = (prefixEdges w (regsAfter w).1 (regsAfter w).2).2 := by
  unfold evenBottom
  rw [bottomEdges_eq_regs]

/-- The prefix `w` has read a letter `1` or `2` (the odd register is defined). -/
def HasOne2 (w : Word) : Prop := ∃ y ∈ w, y = Digit.one ∨ y = Digit.two

/-- The prefix `w` has read a letter `1` or `3` (the even register is defined). -/
def HasOne3 (w : Word) : Prop := ∃ y ∈ w, y = Digit.one ∨ y = Digit.three

/-- S2 for the odd register: the first arc of the odd register tile's boundary is the odd register of `w`. -/
def S2odd (w : Word) : Prop :=
  HasOne2 w → ∃ w2 : F2Word,
    IsBoundaryWordAt (cellTileOf (stateAt w).tOdd) (0, 0) (boundaryWordOf (regsAfter w).1 w2)

/-- S2 for the even register: the first arc of the even register tile's boundary is the even register of `w`. -/
def S2even (w : Word) : Prop :=
  HasOne3 w → ∃ w2 : F2Word,
    IsBoundaryWordAt (cellTileOf (stateAt w).tEven) (0, 0) (boundaryWordOf (regsAfter w).2 w2)

def S2 (w : Word) : Prop := S2odd w ∧ S2even w

/-- S2 holds for the empty word: no letter has been read, so neither register is defined. -/
theorem S2_nil : S2 [] :=
  ⟨fun ⟨y, hy, _⟩ => by simp at hy, fun ⟨y, hy, _⟩ => by simp at hy⟩

/-- The induction: the step (parents' S2 to the child's S2, by one letter) gives S2 for every word. The step is the
only hypothesis; its proof is the pattern comparisons and the R1 covering applied to the parents' S2. -/
theorem S2_all (hstep : ∀ (pre : Word) (d : Digit), S2 pre → S2 (pre ++ [d])) : ∀ w : Word, S2 w := by
  intro w
  induction w using List.reverseRecOn with
  | nil => exact S2_nil
  | append_singleton v d ih => exact hstep v d ih

end FLatticePaper.Tiles.RegisterInduction
