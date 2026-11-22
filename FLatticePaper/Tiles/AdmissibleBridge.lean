import FLatticePaper.Tiles.AdmissibleForms
import FLatticePaper.Tiles.BinaryWords

/-! Task 51, admissibility, part 3: the bridge between the register recursion `bottomFrom` and the binary
quadruples `quadAt` (BinaryWords.lean), through the augmented token morphism `muOf A B`. -/

namespace FLatticePaper.Tiles
open Farey

/-- The binary quadruple at a prefix is determined by its parents: the children are the child operator
applied to the parents, with the parity of the prefix. -/
def QInv (pre : Word) (Q : WordQuad) : Prop :=
  Q.childP = (childWords pre Q.parentP Q.parentQ).1 ∧ Q.childQ = (childWords pre Q.parentP Q.parentQ).2

/-- The registers carry the augmented tokens of the parents. -/
def RegInv (A B : F2Word) (Q : WordQuad) (regs : F2Word × F2Word) : Prop :=
  regs.1 ++ [Unit4.i] = muOf A B Q.parentP ∧ regs.2 ++ [Unit4.i] = muOf A B Q.parentQ

/-- The prefixes where the register recursion is the edge step: they contain a `1`, or both a `2` and a `3`. -/
def HOK (pre : Word) : Prop :=
  (∃ y ∈ pre, y = Digit.one) ∨ ((∃ y ∈ pre, y = Digit.two) ∧ (∃ y ∈ pre, y = Digit.three))

theorem HOK_append (pre : Word) (x : Digit) (h : HOK pre) : HOK (pre ++ [x]) := by
  rcases h with ⟨y, hy, hy1⟩ | ⟨⟨y, hy, hy2⟩, ⟨z, hz, hz3⟩⟩
  · exact Or.inl ⟨y, List.mem_append_left _ hy, hy1⟩
  · exact Or.inr ⟨⟨y, List.mem_append_left _ hy, hy2⟩, ⟨z, List.mem_append_left _ hz, hz3⟩⟩

theorem HOK_not_two {pre : Word} (h : HOK pre) : allTwos pre = false := by
  cases hb : allTwos pre with
  | false => rfl
  | true =>
    exfalso
    have hall := (allTwos_iff pre).mp hb
    rcases h with ⟨y, hy, hy1⟩ | ⟨⟨y, hy, hy2⟩, ⟨z, hz, hz3⟩⟩
    · have := hall y hy; rw [hy1] at this; exact absurd this (by decide)
    · have := hall z hz; rw [hz3] at this; exact absurd this (by decide)

theorem HOK_not_three {pre : Word} (h : HOK pre) : allThrees pre = false := by
  cases hb : allThrees pre with
  | false => rfl
  | true =>
    exfalso
    have hall := ((allThrees_iff pre).mp hb).2
    rcases h with ⟨y, hy, hy1⟩ | ⟨⟨y, hy, hy2⟩, ⟨z, hz, hz3⟩⟩
    · have := hall y hy; rw [hy1] at this; exact absurd this (by decide)
    · have := hall y hy; rw [hy2] at this; exact absurd this (by decide)

theorem prefixEdges_of_HOK {pre : Word} (h : HOK pre) (regO regE : F2Word) :
    prefixEdges pre regO regE = edgeStep (pre.count Digit.one % 2 == 1) regO regE := by
  unfold prefixEdges
  rw [HOK_not_two h, HOK_not_three h]
  simp

/-- One edge step, augmented: the children of the parents are the images of the child operator. -/
theorem edgeStep_aug (A B : F2Word) (pre : Word) (P Q : BinaryWord) (regs : F2Word × F2Word)
    (hreg : regs.1 ++ [Unit4.i] = muOf A B P ∧ regs.2 ++ [Unit4.i] = muOf A B Q) :
    (edgeStep (pre.count Digit.one % 2 == 1) regs.1 regs.2).1 ++ [Unit4.i]
        = muOf A B (childWords pre P Q).1 ∧
    (edgeStep (pre.count Digit.one % 2 == 1) regs.1 regs.2).2 ++ [Unit4.i]
        = muOf A B (childWords pre P Q).2 := by
  obtain ⟨hA, hB⟩ := hreg
  by_cases h : pre.count Digit.one % 2 = 0
  · have hb : (pre.count Digit.one % 2 == 1) = false := by simp [h]
    rw [hb]
    simp only [childWords, if_pos h, edgeStep, Bool.false_eq_true, if_false]
    constructor
    · rw [muOf_append, muOf_append, ← hA, ← hB]
      simp [List.append_assoc]
    · rw [muOf_append, ← hA, ← hB]
      simp [List.append_assoc]
  · have hb : (pre.count Digit.one % 2 == 1) = true := by
      simp only [beq_iff_eq]; omega
    rw [hb]
    simp only [childWords, if_neg h, edgeStep, if_true]
    constructor
    · rw [muOf_append, muOf_append, ← hA, ← hB]
      simp [List.append_assoc]
    · rw [muOf_append, ← hA, ← hB]
      simp [List.append_assoc]

theorem QInv_step (pre : Word) (Q : WordQuad) (x : Digit) :
    QInv (pre ++ [x]) (Q.step pre x) := by
  cases x <;> simp [QInv, WordQuad.step, childWords]

/-- The bridge: the odd and even edges of the register recursion, augmented, are the images of the children of
the binary quadruple obtained by reading `u` from `pre`. -/
theorem bridge (A B : F2Word) (u : Word) : ∀ (pre : Word) (Q : WordQuad) (regs : F2Word × F2Word),
    HOK pre → QInv pre Q → RegInv A B Q regs →
    (bottomFrom pre u regs).1 ++ [Unit4.i]
        = muOf A B ((u.foldl (fun (acc : Word × WordQuad) d => (acc.1 ++ [d], acc.2.step acc.1 d)) (pre, Q)).2.childP)
    ∧ (bottomFrom pre u regs).2 ++ [Unit4.i]
        = muOf A B ((u.foldl (fun (acc : Word × WordQuad) d => (acc.1 ++ [d], acc.2.step acc.1 d)) (pre, Q)).2.childQ) := by
  induction u with
  | nil =>
    intro pre Q regs hH hQ hR
    simp only [bottomFrom, List.foldl_nil]
    rw [prefixEdges_of_HOK hH]
    obtain ⟨e1, e2⟩ := edgeStep_aug A B pre Q.parentP Q.parentQ regs hR
    rw [hQ.1, hQ.2]
    exact ⟨e1, e2⟩
  | cons x u ih =>
    intro pre Q regs hH hQ hR
    simp only [bottomFrom, List.foldl_cons]
    have hH' := HOK_append pre x hH
    have hQ' := QInv_step pre Q x
    have hR' : RegInv A B (Q.step pre x)
        (updateRegs x regs (prefixEdges pre regs.1 regs.2)) := by
      rw [prefixEdges_of_HOK hH]
      obtain ⟨e1, e2⟩ := edgeStep_aug A B pre Q.parentP Q.parentQ regs hR
      rw [← hQ.1] at e1
      rw [← hQ.2] at e2
      unfold RegInv
      cases x with
      | one => exact ⟨by simpa [updateRegs, WordQuad.step] using e1, by simpa [updateRegs, WordQuad.step] using e2⟩
      | two => exact ⟨by simpa [updateRegs, WordQuad.step] using e1, by simpa [updateRegs, WordQuad.step] using hR.2⟩
      | three => exact ⟨by simpa [updateRegs, WordQuad.step] using hR.1, by simpa [updateRegs, WordQuad.step] using e2⟩
    exact ih (pre ++ [x]) (Q.step pre x) _ hH' hQ' hR'


/-- Reading a word after a prefix: the bottom-edge recursion splits along any decomposition of the word. -/
theorem bottomFrom_append (u : Word) : ∀ (pre rest : Word) (regs : F2Word × F2Word),
    ∃ regs', bottomFrom pre (u ++ rest) regs = bottomFrom (pre ++ u) rest regs' := by
  induction u with
  | nil => intro pre rest regs; exact ⟨regs, by simp⟩
  | cons x u ih =>
    intro pre rest regs
    obtain ⟨regs', h⟩ := ih (pre ++ [x]) rest (updateRegs x regs (prefixEdges pre regs.1 regs.2))
    refine ⟨regs', ?_⟩
    simp only [List.cons_append, bottomFrom]
    rw [h]
    simp [List.append_assoc]

theorem prefixEdges_twos (k : ℕ) (a b : F2Word) :
    prefixEdges (List.replicate k Digit.two) a b = baseTwoEdges k := by
  have h : allTwos (List.replicate k Digit.two) = true := by
    rw [allTwos_iff]
    intro y hy
    exact List.eq_of_mem_replicate hy
  unfold prefixEdges
  rw [if_pos h, List.length_replicate]

theorem prefixEdges_threes (k : ℕ) (hk : 1 ≤ k) (a b : F2Word) :
    prefixEdges (List.replicate k Digit.three) a b = baseThreeEdges k := by
  have h2 : allTwos (List.replicate k Digit.three) = false := by
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    simp [allTwos, List.replicate_succ]
  have h3 : allThrees (List.replicate k Digit.three) = true := by
    rw [allThrees_iff]
    refine ⟨fun h => ?_, fun y hy => List.eq_of_mem_replicate hy⟩
    have := congrArg List.length h
    simp at this
    omega
  unfold prefixEdges
  rw [if_neg (by simp [h2]), if_pos h3, List.length_replicate]

/-- Two steps of the register recursion over `2`: after `m + k + 1` twos from `2^m`, the odd register is the base. -/
theorem bottomFrom_two_run (k : ℕ) : ∀ (m : ℕ) (rest : Word) (regs : F2Word × F2Word),
    bottomFrom (List.replicate m Digit.two) (List.replicate (k + 1) Digit.two ++ rest) regs
      = bottomFrom (List.replicate (m + k + 1) Digit.two) rest ((baseTwoEdges (m + k)).1, regs.2) := by
  induction k with
  | zero =>
    intro m rest regs
    simp only [List.replicate_one, zero_add, List.singleton_append]
    rw [List.replicate_succ']
    simp [bottomFrom, prefixEdges_twos, updateRegs]
  | succ k ih =>
    intro m rest regs
    have h1 : List.replicate (k + 1 + 1) Digit.two ++ rest
        = Digit.two :: (List.replicate (k + 1) Digit.two ++ rest) := by
      simp [List.replicate_succ]
    rw [h1]
    have h2 : bottomFrom (List.replicate m Digit.two) (Digit.two :: (List.replicate (k + 1) Digit.two ++ rest)) regs
        = bottomFrom (List.replicate (m + 1) Digit.two) (List.replicate (k + 1) Digit.two ++ rest)
            ((baseTwoEdges m).1, regs.2) := by
      simp only [bottomFrom, prefixEdges_twos, updateRegs]
      rw [show List.replicate (m + 1) Digit.two = List.replicate m Digit.two ++ [Digit.two] from List.replicate_succ']
    rw [h2, ih (m + 1) rest ((baseTwoEdges m).1, regs.2)]
    have e1 : m + 1 + k = m + (k + 1) := by omega
    simp only [e1]

end FLatticePaper.Tiles
