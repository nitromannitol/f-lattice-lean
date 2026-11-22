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

theorem allTwos_iff (u : Word) : allTwos u = true ↔ ∀ y ∈ u, y = Digit.two := by
  simp [allTwos, List.all_eq_true]

theorem allThrees_iff (u : Word) : allThrees u = true ↔ u ≠ [] ∧ ∀ y ∈ u, y = Digit.three := by
  simp [allThrees, List.all_eq_true]

theorem allTwos_eq {u : Word} (h : allTwos u = true) : u = List.replicate u.length Digit.two :=
  List.eq_replicate_iff.mpr ⟨rfl, (allTwos_iff u).1 h⟩

theorem allThrees_eq {u : Word} (h : allThrees u = true) : u = List.replicate u.length Digit.three :=
  List.eq_replicate_iff.mpr ⟨rfl, ((allThrees_iff u).1 h).2⟩

/-- The odd register is the odd edge of the parents once a letter `1` or `2` has been read. -/
def OddReg (P : Parents) (w : F2Word) : Prop := F2Word.sum w + gI = texV1Odd P.odd

/-- The even register is the even edge of the parents once a letter `1` or `3` has been read. -/
def EvenReg (P : Parents) (v : F2Word) : Prop := F2Word.sum v + gI = texV1Even P.even

/-- The odd register is correct at the prefix `pre`, as soon as a letter `1` or `2` occurs in `pre`. -/
def IOInv (pre : Word) (regs : F2Word × F2Word) : Prop :=
  (∃ y ∈ pre, y = Digit.one ∨ y = Digit.two) → OddReg (parentsAt pre) regs.1

/-- The even register is correct at the prefix `pre`, as soon as a letter `1` or `3` occurs in `pre`. -/
def IEInv (pre : Word) (regs : F2Word × F2Word) : Prop :=
  (∃ y ∈ pre, y = Digit.one ∨ y = Digit.three) → EvenReg (parentsAt pre) regs.2

theorem F2Word_sum_i' : F2Word.sum [Unit4.i] = gI := by
  simp [F2Word.sum, Unit4.vec, gI]

theorem texV1Odd_current_odd (P : Parents) :
    texV1Odd (P.current .odd) = texV1Odd P.odd + texV1Even P.even + texV1Even P.even := by
  simp only [Parents.current, Parents.combine, texV1Odd, texV1Even]
  ext <;> simp <;> ring

theorem texV1Even_current_even (P : Parents) :
    texV1Even (P.current .even) = texV1Odd P.odd + texV1Even P.even := by
  simp only [Parents.current, Parents.combine, texV1Odd, texV1Even]
  ext <;> simp

theorem edgeStep_sums (P : Parents) (w v : F2Word) (hw : OddReg P w) (hv : EvenReg P v) (odd : Bool) :
    F2Word.sum (edgeStep odd w v).1 + gI = texV1Odd (P.current .odd) ∧
      F2Word.sum (edgeStep odd w v).2 + gI = texV1Even (P.current .even) := by
  have hwv : F2Word.sum w + gI + (F2Word.sum v + gI) + (F2Word.sum v + gI) =
      texV1Odd P.odd + texV1Even P.even + texV1Even P.even := by
    rw [hw, hv]
  have hwv' : F2Word.sum w + gI + (F2Word.sum v + gI) =
      texV1Odd P.odd + texV1Even P.even := by
    rw [hw, hv]
  have hvv : F2Word.sum v + gI + (F2Word.sum v + gI) + (F2Word.sum w + gI) =
      texV1Odd P.odd + texV1Even P.even + texV1Even P.even := by
    rw [hw, hv]; abel
  cases odd
  · simp only [edgeStep, Bool.false_eq_true, if_false, F2Word_sum_append, F2Word_sum_i', texV1Odd_current_odd,
      texV1Even_current_even]
    constructor
    · rw [← hvv]; abel
    · rw [← hwv']; abel
  · simp only [edgeStep, if_true, F2Word_sum_append, F2Word_sum_i', texV1Odd_current_odd,
      texV1Even_current_even]
    constructor
    · rw [← hwv]; abel
    · rw [← hwv']; abel

/-- The edges at a prefix are correct when both registers are correct: from the registers of the parents. -/
theorem prefixEdges_sums (pre : Word) (regs : F2Word × F2Word) (hO : IOInv pre regs) (hE : IEInv pre regs) :
    F2Word.sum (prefixEdges pre regs.1 regs.2).1 + gI = texV1Odd ((parentsAt pre).current .odd) ∧
      F2Word.sum (prefixEdges pre regs.1 regs.2).2 + gI = texV1Even ((parentsAt pre).current .even) := by
  unfold prefixEdges
  by_cases h2 : allTwos pre = true
  · obtain ⟨k, rfl⟩ : ∃ k, pre = List.replicate k Digit.two := ⟨pre.length, allTwos_eq h2⟩
    simp only [if_pos h2, List.length_replicate]
    exact ⟨baseTwo_odd_sum k, baseTwo_even_sum k⟩
  · rw [if_neg h2]
    by_cases h3 : allThrees pre = true
    · obtain ⟨k, rfl⟩ : ∃ k, pre = List.replicate k Digit.three := ⟨pre.length, allThrees_eq h3⟩
      simp only [if_pos h3, List.length_replicate]
      exact ⟨baseThree_odd_sum k, baseThree_even_sum k⟩
    · rw [if_neg h3]
      have hone : ∃ y ∈ pre, y = Digit.one ∨ y = Digit.two := by
        by_contra hc
        apply h3
        rw [allThrees_iff]
        constructor
        · intro hnil
          apply h2
          rw [hnil]
          rfl
        · intro y hy
          have hn := fun hh : ∃ y ∈ pre, y = Digit.one ∨ y = Digit.two => hc hh
          rcases y with _ | _ | _
          · exact absurd ⟨Digit.one, hy, Or.inl rfl⟩ hc
          · exact absurd ⟨Digit.two, hy, Or.inr rfl⟩ hc
          · rfl
      have hthr : ∃ y ∈ pre, y = Digit.one ∨ y = Digit.three := by
        by_contra hc
        apply h2
        rw [allTwos_iff]
        intro y hy
        rcases y with _ | _ | _
        · exact absurd ⟨Digit.one, hy, Or.inl rfl⟩ hc
        · rfl
        · exact absurd ⟨Digit.three, hy, Or.inr rfl⟩ hc
      exact edgeStep_sums (parentsAt pre) regs.1 regs.2 (hO hone) (hE hthr) _

/-- The registers stay correct after reading one letter. -/
theorem invariants_step (pre : Word) (regs : F2Word × F2Word) (x : Digit) (hO : IOInv pre regs)
    (hE : IEInv pre regs) :
    IOInv (pre ++ [x]) (updateRegs x regs (prefixEdges pre regs.1 regs.2)) ∧
      IEInv (pre ++ [x]) (updateRegs x regs (prefixEdges pre regs.1 regs.2)) := by
  obtain ⟨eO, eE⟩ := prefixEdges_sums pre regs hO hE
  have hsplit : ∀ Q : Digit → Prop, (∃ y ∈ pre ++ [x], Q y) → (∃ y ∈ pre, Q y) ∨ Q x := by
    intro Q h
    obtain ⟨y, hy, hq⟩ := h
    rcases List.mem_append.1 hy with h1 | h1
    · exact Or.inl ⟨y, h1, hq⟩
    · rw [List.mem_singleton] at h1
      subst h1
      exact Or.inr hq
  constructor
  · intro hex
    rw [parentsAt_append_singleton]
    cases x
    · exact eO
    · exact eO
    · refine hO ?_
      rcases hsplit (fun y => y = Digit.one ∨ y = Digit.two) hex with h | h
      · exact h
      · exact absurd h (by decide)
  · intro hex
    rw [parentsAt_append_singleton]
    cases x
    · exact eE
    · refine hE ?_
      rcases hsplit (fun y => y = Digit.one ∨ y = Digit.three) hex with h | h
      · exact h
      · exact absurd h (by decide)
    · exact eE

/-- The edges read from the prefix `pre` with registers `regs` are the child edges of `pre ++ rest`. -/
theorem bottomFrom_sums (rest : Word) : ∀ (pre : Word) (regs : F2Word × F2Word), IOInv pre regs →
    IEInv pre regs →
      F2Word.sum (bottomFrom pre rest regs).1 + gI = texV1Odd ((parentsAt (pre ++ rest)).current .odd) ∧
        F2Word.sum (bottomFrom pre rest regs).2 + gI = texV1Even ((parentsAt (pre ++ rest)).current .even) := by
  induction rest with
  | nil =>
    intro pre regs hO hE
    simpa [bottomFrom] using prefixEdges_sums pre regs hO hE
  | cons x rest ih =>
    intro pre regs hO hE
    obtain ⟨hO', hE'⟩ := invariants_step pre regs x hO hE
    simpa [bottomFrom, List.append_assoc] using ih (pre ++ [x]) _ hO' hE'

/-- The odd bottom edge of the recursion word: its sum plus `i` is the odd doubled vector of the child's odd parent. -/
theorem bottomEdges_odd_sum (word : Word) :
    F2Word.sum (bottomEdges word).1 + gI = texV1Odd ((parentsAt word).current .odd) := by
  have hO : IOInv [] ([], []) := by
    intro h
    obtain ⟨y, hy, _⟩ := h
    simp at hy
  have hE : IEInv [] ([], []) := by
    intro h
    obtain ⟨y, hy, _⟩ := h
    simp at hy
  simpa [bottomEdges] using (bottomFrom_sums word [] ([], []) hO hE).1

/-- The even bottom edge `v_t` of the recursion word: its sum plus `i` is the vector `𝔳_{n/d,1}` of the child. -/
theorem bottomEdges_even_sum (word : Word) :
    F2Word.sum (bottomEdges word).2 + gI = texV1Even ((parentsAt word).current .even) := by
  have hO : IOInv [] ([], []) := by
    intro h
    obtain ⟨y, hy, _⟩ := h
    simp at hy
  have hE : IEInv [] ([], []) := by
    intro h
    obtain ⟨y, hy, _⟩ := h
    simp at hy
  simpa [bottomEdges] using (bottomFrom_sums word [] ([], []) hO hE).2

/-- Multiplication by `i` on Gaussian integers `(a, b) ↦ (-b, a)`. -/
def rotI (z : GInt) : GInt := (-z.2, z.1)

theorem rotI_add (a b : GInt) : rotI (a + b) = rotI a + rotI b := by
  unfold rotI
  simp only [Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, neg_add]

theorem rotI_sub (a b : GInt) : rotI (a - b) = rotI a - rotI b := by
  unfold rotI
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk, neg_sub]
  ring_nf

theorem F2Word_sum_cons (x : Unit4) (w : F2Word) : F2Word.sum (x :: w) = Unit4.vec x + F2Word.sum w := by
  simp [F2Word.sum]

theorem vec_mulI (x : Unit4) : Unit4.vec (Unit4.mulI x) = rotI (Unit4.vec x) := by
  cases x <;> simp [Unit4.mulI, Unit4.vec, rotI]

/-- The sum of the letterwise `i`-multiple is the `i`-multiple of the sum. -/
theorem F2Word_sum_map_mulI (w : F2Word) : F2Word.sum (w.map Unit4.mulI) = rotI (F2Word.sum w) := by
  induction w with
  | nil => simp [F2Word.sum, rotI, Prod.ext_iff]
  | cons x w ih =>
    rw [List.map_cons, F2Word_sum_cons, F2Word_sum_cons, ih, vec_mulI, rotI_add]

theorem parentsAt_swap_eq (word : Word) :
    parentsAt (word.map Digit.swapTwoThree) = ⟨(parentsAt word).even.rotate, (parentsAt word).odd.rotate⟩ :=
  (rotate_parentsAt word).symm

/-- The child of a valid frame is an even fraction. -/
theorem child_even_of_valid (parents : Parents) (hv : parents.ValidFrame) :
    (parents.current .even).Even := by
  have he : parents.even.Even := hv.even_parity
  unfold Fraction.Even at he ⊢
  simp only [Parents.current, Parents.combine] at ⊢
  omega

/-- The second bottom edge `w_2 = i · (odd edge of the rotated word)`: its sum minus `1` is `v_{n/d,2}`. -/
theorem bottomEdges_second_sum (word : Word) :
    F2Word.sum ((bottomEdges (word.map Digit.swapTwoThree)).1.map Unit4.mulI) - gOne =
      texV2 ((parentsAt word).current .even) := by
  have hodd := bottomEdges_odd_sum (word.map Digit.swapTwoThree)
  rw [F2Word_sum_map_mulI, parentsAt_swap_eq] at *
  have hV := parentsAt_valid word
  have he : (parentsAt word).even.Even := hV.even_parity
  have ho : (parentsAt word).odd.Odd := hV.odd_parity
  have hC : (⟨(parentsAt word).even.rotate, (parentsAt word).odd.rotate⟩ : Parents).current .odd =
      ⟨((parentsAt word).even.den - (parentsAt word).even.num) / 2 +
          ((parentsAt word).odd.den - (parentsAt word).odd.num),
        ((parentsAt word).even.den + (parentsAt word).even.num) / 2 +
          ((parentsAt word).odd.den + (parentsAt word).odd.num)⟩ := by
    rw [Fraction.rotate_of_even he, Fraction.rotate_of_odd ho]
    simp only [Parents.current, Parents.combine, one_mul]
  rw [hC] at hodd
  have hE := eq_sub_of_add_eq hodd
  rw [hE]
  have he' : ((parentsAt word).even.num + (parentsAt word).even.den) % 2 = 0 := he
  have ho' : ((parentsAt word).odd.num + (parentsAt word).odd.den) % 2 = 1 := ho
  apply Prod.ext
  · simp only [rotI, gI, gOne, texV1Odd, texV2, Parents.current, Parents.combine, Prod.fst_sub, Prod.snd_sub]
    omega
  · simp only [rotI, gI, gOne, texV1Odd, texV2, Parents.current, Parents.combine, Prod.fst_sub, Prod.snd_sub]
    omega

end FLatticePaper.Tiles
