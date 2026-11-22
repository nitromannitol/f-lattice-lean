import FLatticePaper.Tiles.AlmostTiling
import FLatticePaper.Construction.OffsetTables
import FLatticePaper.Farey.Rotation

/-! Task 51: the bottom-edge recursion of `lemma:standard_boundary_word_recursion` (Step 2).

For a recursion word `str` (letters `1, 2, 3`) the odd and even bottom edges `(w, v)` of the odd-even parent pair
are produced by the registers of the Farey recursion: a letter `1` replaces both registers by the child edges, `2`
replaces the odd register, `3` replaces the even register. The base cases are the words `2^k` and `3^k`; the step
is `(w i v i v, w i v)` for an odd number of ones, and `(v i v i w, v i w)` otherwise. -/

namespace FLatticePaper.Tiles
open Farey Construction

/-- The word `(1 i)^n`. -/
def oneI (n : ℕ) : F2Word := (List.replicate n [Unit4.one, Unit4.i]).flatten

/-- The word `(1 1)^n`. -/
def oneOne (n : ℕ) : F2Word := (List.replicate n [Unit4.one, Unit4.one]).flatten

/-- The base edges of `2^k`: `w_0 = 1 (1i)^{2k+1} (1 1)`, `v_0 = 1 (1i)^{2k} (1 1)`. -/
def baseTwoEdges (k : ℕ) : F2Word × F2Word :=
  ([Unit4.one] ++ oneI (2 * k + 1) ++ [Unit4.one, Unit4.one], [Unit4.one] ++ oneI (2 * k) ++ [Unit4.one, Unit4.one])

/-- The base edges of `3^k`: `w_0 = (1 1)^k (1 i) (1 1)^{k+1} 1`, `v_0 = 1 (1 1)^{k+1}`. -/
def baseThreeEdges (k : ℕ) : F2Word × F2Word :=
  (oneOne k ++ [Unit4.one, Unit4.i] ++ oneOne (k + 1) ++ [Unit4.one], [Unit4.one] ++ oneOne (k + 1))

/-- The recursive step from the odd register `w` and the even register `v`. -/
def edgeStep (odd : Bool) (w v : F2Word) : F2Word × F2Word :=
  if odd then (w ++ [Unit4.i] ++ v ++ [Unit4.i] ++ v, w ++ [Unit4.i] ++ v)
  else (v ++ [Unit4.i] ++ v ++ [Unit4.i] ++ w, v ++ [Unit4.i] ++ w)

/-- `u` is a power of the letter `2` (the empty word included). -/
def allTwos (u : Word) : Bool := u.all (fun x => x == Digit.two)

/-- `u` is a nonempty power of the letter `3`. -/
def allThrees (u : Word) : Bool := !u.isEmpty && u.all (fun x => x == Digit.three)

/-- The edges of the quadruple at the prefix `u`, from the registers `(regO, regE)` of its parents. -/
def prefixEdges (u : Word) (regO regE : F2Word) : F2Word × F2Word :=
  if allTwos u then baseTwoEdges u.length
  else if allThrees u then baseThreeEdges u.length
  else edgeStep (u.count Digit.one % 2 == 1) regO regE

/-- The register update by the next letter: `1` takes both child edges, `2` the odd one, `3` the even one. -/
def updateRegs (x : Digit) (regs e : F2Word × F2Word) : F2Word × F2Word :=
  match x with
  | .one => e
  | .two => (e.1, regs.2)
  | .three => (regs.1, e.2)

/-- The bottom edges read letter by letter: `prefix` is the part already read, `rest` the part to read. -/
def bottomFrom : Word → Word → F2Word × F2Word → F2Word × F2Word
  | pre, [], regs => prefixEdges pre regs.1 regs.2
  | pre, x :: rest, regs =>
      bottomFrom (pre ++ [x]) rest (updateRegs x regs (prefixEdges pre regs.1 regs.2))

/-- The bottom edges `(w_t, v_t)` of the recursion word `word` (odd edge first, even edge second). -/
def bottomEdges (word : Word) : F2Word × F2Word := bottomFrom [] word ([], [])

theorem F2Word_sum_append (a b : F2Word) : F2Word.sum (a ++ b) = F2Word.sum a + F2Word.sum b := by
  simp [F2Word.sum, List.map_append, List.sum_append]

theorem F2Word_sum_one : F2Word.sum [Unit4.one] = (1, 0) := by
  simp [F2Word.sum, Unit4.vec]

theorem F2Word_sum_pair_one : F2Word.sum [Unit4.one, Unit4.one] = (2, 0) := by
  simp [F2Word.sum, Unit4.vec]

theorem F2Word_sum_one_i : F2Word.sum [Unit4.one, Unit4.i] = (1, 1) := by
  simp [F2Word.sum, Unit4.vec]

theorem F2Word_sum_i : F2Word.sum [Unit4.i] = (0, 1) := by
  simp [F2Word.sum, Unit4.vec]

theorem sum_oneI (n : ℕ) : F2Word.sum (oneI n) = ((n : ℤ), (n : ℤ)) := by
  induction n with
  | zero => simp [oneI, F2Word.sum, Prod.ext_iff]
  | succ n ih =>
    have h : oneI (n + 1) = [Unit4.one, Unit4.i] ++ oneI n := by
      simp [oneI, List.replicate_succ, List.flatten_cons]
    rw [h, F2Word_sum_append, ih, F2Word_sum_one_i]
    ext
    all_goals simp
    all_goals ring

theorem sum_oneOne (n : ℕ) : F2Word.sum (oneOne n) = (2 * (n : ℤ), 0) := by
  induction n with
  | zero => simp [oneOne, F2Word.sum, Prod.ext_iff]
  | succ n ih =>
    have h : oneOne (n + 1) = [Unit4.one, Unit4.one] ++ oneOne n := by
      simp [oneOne, List.replicate_succ, List.flatten_cons]
    rw [h, F2Word_sum_append, ih, F2Word_sum_pair_one]
    ext
    all_goals simp
    all_goals ring

/-- The Farey parents of `2^k` are `(k/(k+1), 1/1)`. -/
theorem parentsAt_replicate_two (k : ℕ) :
    parentsAt (List.replicate k Digit.two) = ⟨⟨(k : ℤ), (k : ℤ) + 1⟩, ⟨1, 1⟩⟩ := by
  induction k with
  | zero => simp [parentsAt, root, Parents.walk]
  | succ k ih =>
    rw [List.replicate_succ', parentsAt_append_singleton, ih]
    simp only [Parents.step, Parents.current, Parents.combine]
    push_cast
    ring_nf

/-- The Farey parents of `3^k` are `(0/1, 1/(2k+1))`. -/
theorem parentsAt_replicate_three (k : ℕ) :
    parentsAt (List.replicate k Digit.three) = ⟨⟨0, 1⟩, ⟨1, 2 * (k : ℤ) + 1⟩⟩ := by
  induction k with
  | zero => simp [parentsAt, root, Parents.walk]
  | succ k ih =>
    rw [List.replicate_succ', parentsAt_append_singleton, ih]
    simp only [Parents.step, Parents.current, Parents.combine]
    push_cast
    ring_nf

theorem baseTwo_odd_sum (k : ℕ) :
    F2Word.sum (baseTwoEdges k).1 + gI =
      texV1Odd ((parentsAt (List.replicate k Digit.two)).current .odd) := by
  rw [parentsAt_replicate_two]
  simp only [baseTwoEdges, Parents.current, Parents.combine, texV1Odd, F2Word_sum_append, sum_oneI,
    F2Word_sum_one, F2Word_sum_pair_one, gI]
  ext
  all_goals simp
  all_goals ring

theorem baseTwo_even_sum (k : ℕ) :
    F2Word.sum (baseTwoEdges k).2 + gI =
      texV1Even ((parentsAt (List.replicate k Digit.two)).current .even) := by
  rw [parentsAt_replicate_two]
  simp only [baseTwoEdges, Parents.current, Parents.combine, texV1Even, F2Word_sum_append, sum_oneI,
    F2Word_sum_one, F2Word_sum_pair_one, gI]
  ext
  all_goals simp
  all_goals ring

theorem baseThree_odd_sum (k : ℕ) :
    F2Word.sum (baseThreeEdges k).1 + gI =
      texV1Odd ((parentsAt (List.replicate k Digit.three)).current .odd) := by
  rw [parentsAt_replicate_three]
  simp only [baseThreeEdges, Parents.current, Parents.combine, texV1Odd, F2Word_sum_append, sum_oneOne,
    F2Word_sum_one, F2Word_sum_one_i, gI]
  ext
  all_goals simp
  all_goals ring

theorem baseThree_even_sum (k : ℕ) :
    F2Word.sum (baseThreeEdges k).2 + gI =
      texV1Even ((parentsAt (List.replicate k Digit.three)).current .even) := by
  rw [parentsAt_replicate_three]
  simp only [baseThreeEdges, Parents.current, Parents.combine, texV1Even, F2Word_sum_append, sum_oneOne,
    F2Word_sum_one, gI]
  ext
  all_goals simp
  all_goals ring

end FLatticePaper.Tiles
