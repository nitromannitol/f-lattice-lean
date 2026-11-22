import FLatticePaper.Tiles.BottomEdges

/-! The word-level recursion of the bottom edges (TeX 2723, the augmented recursion without the trailing `i`).

`bottomEdges u` is computed letter by letter by `bottomFrom`, with two registers. Each register holds the bottom edge of
the last prefix that set it: the odd register is set by the letters `1` and `2`, the even one by `1` and `3`. So for a
non-base word `u` the edges are one `edgeStep` of the bottom edges of two earlier prefixes, `srcOf u`:
`bottomEdges u = edgeStep (parity of u) (bottom edge of srcO) (bottom edge of srcE)`. -/

namespace FLatticePaper.Tiles.RecursionIdentity

open FLatticePaper FLatticePaper.Farey FLatticePaper.Tiles

/-- The registers after reading `rest` from the prefix `pre`, as `bottomFrom` updates them. -/
def regsFrom (pre : Word) : Word → F2Word × F2Word → F2Word × F2Word
  | [], regs => regs
  | x :: rest, regs => regsFrom (pre ++ [x]) rest (updateRegs x regs (prefixEdges pre regs.1 regs.2))

/-- The prefixes that the registers were last set from: (odd source, even source). -/
def srcFrom (pre : Word) : Word → Word × Word → Word × Word
  | [], s => s
  | x :: rest, s => srcFrom (pre ++ [x]) rest
      (if x = Digit.one ∨ x = Digit.two then pre else s.1, if x = Digit.one ∨ x = Digit.three then pre else s.2)

/-- The prefixes of `u` whose edges the two registers hold after reading `u`. -/
def srcOf (u : Word) : Word × Word := srcFrom [] u ([], [])

theorem bottomFrom_eq (rest : Word) : ∀ (pre : Word) (regs : F2Word × F2Word),
    bottomFrom pre rest regs = prefixEdges (pre ++ rest) (regsFrom pre rest regs).1 (regsFrom pre rest regs).2 := by
  induction rest with
  | nil =>
    intro pre regs
    simp [bottomFrom, regsFrom]
  | cons x rest ih =>
    intro pre regs
    simp only [bottomFrom, regsFrom]
    rw [ih]
    simp [List.append_assoc]

/-- The edges of `bottomEdges u` are the prefix edges with the registers after reading `u`. -/
theorem bottomEdges_eq (u : Word) :
    bottomEdges u = prefixEdges u (regsFrom [] u ([], [])).1 (regsFrom [] u ([], [])).2 := by
  unfold bottomEdges
  rw [bottomFrom_eq]
  simp

/-- Reading one more letter: the registers update with the edges of the prefix `pre ++ rest`. -/
theorem regsFrom_snoc (x : Digit) : ∀ (pre rest : Word) (regs : F2Word × F2Word),
    regsFrom pre (rest ++ [x]) regs =
      updateRegs x (regsFrom pre rest regs) (prefixEdges (pre ++ rest) (regsFrom pre rest regs).1
        (regsFrom pre rest regs).2) := by
  intro pre rest
  induction rest generalizing pre with
  | nil =>
    intro regs
    simp [regsFrom]
  | cons y rest ih =>
    intro regs
    simp only [List.cons_append, regsFrom]
    rw [ih]
    simp [List.append_assoc]

theorem srcFrom_snoc (x : Digit) : ∀ (pre rest : Word) (s : Word × Word),
    srcFrom pre (rest ++ [x]) s =
      (if x = Digit.one ∨ x = Digit.two then pre ++ rest else (srcFrom pre rest s).1,
        if x = Digit.one ∨ x = Digit.three then pre ++ rest else (srcFrom pre rest s).2) := by
  intro pre rest
  induction rest generalizing pre with
  | nil =>
    intro s
    simp [srcFrom]
  | cons y rest ih =>
    intro s
    simp only [List.cons_append, srcFrom]
    rw [ih]
    simp [List.append_assoc]

/-- The registers after the prefix `u ++ [x]`, in terms of the bottom edges of `u`. -/
theorem regsFrom_append_single (u : Word) (x : Digit) :
    regsFrom [] (u ++ [x]) ([], []) = updateRegs x (regsFrom [] u ([], [])) (bottomEdges u) := by
  rw [regsFrom_snoc, List.nil_append, ← bottomEdges_eq]

/-- The odd register holds the bottom edge of its source once the letter `1` or `2` has occurred. -/
theorem regs_odd_inv (u : Word) : (∃ y ∈ u, y = Digit.one ∨ y = Digit.two) →
    (regsFrom [] u ([], [])).1 = (bottomEdges (srcOf u).1).1 := by
  induction u using List.reverseRecOn with
  | nil => intro h; simp at h
  | append_singleton u x ih =>
    intro h
    have hsrc := srcFrom_snoc x [] u ([], [])
    unfold srcOf
    rw [regsFrom_append_single, hsrc]
    cases x with
    | one => simp [updateRegs]
    | two => simp [updateRegs]
    | three =>
      simp only [updateRegs]
      have h' : ∃ y ∈ u, y = Digit.one ∨ y = Digit.two := by
        obtain ⟨y, hy, hy'⟩ := h
        rcases List.mem_append.mp hy with hy | hy
        · exact ⟨y, hy, hy'⟩
        · simp at hy
          subst hy
          simp at hy'
      simp only [srcOf] at ih
      simp only [if_neg (show ¬ (Digit.three = Digit.one ∨ Digit.three = Digit.two) by decide)]
      exact ih h'

/-- The even register holds the bottom edge of its source once the letter `1` or `3` has occurred. -/
theorem regs_even_inv (u : Word) : (∃ y ∈ u, y = Digit.one ∨ y = Digit.three) →
    (regsFrom [] u ([], [])).2 = (bottomEdges (srcOf u).2).2 := by
  induction u using List.reverseRecOn with
  | nil => intro h; simp at h
  | append_singleton u x ih =>
    intro h
    have hsrc := srcFrom_snoc x [] u ([], [])
    unfold srcOf
    rw [regsFrom_append_single, hsrc]
    cases x with
    | one => simp [updateRegs]
    | two =>
      simp only [updateRegs]
      have h' : ∃ y ∈ u, y = Digit.one ∨ y = Digit.three := by
        obtain ⟨y, hy, hy'⟩ := h
        rcases List.mem_append.mp hy with hy | hy
        · exact ⟨y, hy, hy'⟩
        · simp at hy
          subst hy
          simp at hy'
      simp only [srcOf] at ih
      simp only [if_neg (show ¬ (Digit.two = Digit.one ∨ Digit.two = Digit.three) by decide)]
      exact ih h'
    | three => simp [updateRegs]

/-- A word that is neither empty nor a power of `2` contains `1` or `2`. -/
theorem exists_one_or_two (u : Word) (hT : allTwos u = false) (hH : allThrees u = false) :
    ∃ y ∈ u, y = Digit.one ∨ y = Digit.two := by
  by_contra h
  push Not at h
  have hne : u ≠ [] := by
    rintro rfl
    simp [allTwos] at hT
  have hall : allThrees u = true := by
    rw [allThrees_iff]
    refine ⟨hne, fun y hy => ?_⟩
    have := h y hy
    cases y <;> simp_all
  simp [hH] at hall

/-- A word that is not a power of `3` contains `1` or `3`. -/
theorem exists_one_or_three (u : Word) (hT : allTwos u = false) :
    ∃ y ∈ u, y = Digit.one ∨ y = Digit.three := by
  by_contra h
  push Not at h
  have hall : allTwos u = true := by
    rw [allTwos_iff]
    intro y hy
    have := h y hy
    cases y <;> simp_all
  simp [hT] at hall

/-- The recursion of the bottom edges: for a word that is neither a power of `2` nor of `3`, the bottom edges are one
`edgeStep` of the bottom edges of the two source prefixes. -/
theorem bottomEdges_rec (u : Word) (hT : allTwos u = false) (hH : allThrees u = false) :
    bottomEdges u = edgeStep (u.count Digit.one % 2 == 1) (bottomEdges (srcOf u).1).1 (bottomEdges (srcOf u).2).2 := by
  rw [bottomEdges_eq]
  unfold prefixEdges
  rw [if_neg (by simp [hT]), if_neg (by simp [hH]), regs_odd_inv u (exists_one_or_two u hT hH),
    regs_even_inv u (exists_one_or_three u hT)]

end FLatticePaper.Tiles.RecursionIdentity
