import FLatticePaper.Tiles.ArcInequality

/-! Task 55 (R2): the run lemma of a walk. Let `u` be a word over the letters `1`, `i`, `-1` with no adjacent pair
`(1, -1)` or `(-1, 1)`, walked from the origin. Let `H = cntI u` (the number of north steps) and let `FF u j` be the
column of the north step at height `j` (`0 ≤ j < H`), with `FF u (-1) = 0` and `FF u H = (sum u).1`. Then the walk's
horizontal edges at height `k` run between `FF u (k-1)` and `FF u k`, and its north edges are the north steps:

* `((q, k), (q+1, k))` is an edge iff `0 ≤ k ≤ H` and `FF (k-1) ≤ q < FF k`;
* `((q+1, k), (q, k))` is an edge iff `0 ≤ k ≤ H` and `FF k ≤ q < FF (k-1)`;
* `((x, k), (x, k+1))` is an edge iff `0 ≤ k < H` and `x = colN u 0 k`;
* the walk has no repeated edge.

The proof appends one letter at a time (`List.reverseRecOn`); the adjacency condition is carried by `List.Chain'`. -/

namespace FLatticePaper.Tiles.RegionRuns

open FLatticePaper FLatticePaper.Tiles

/-- The column function of a word: the north column at height `j`, `0` below, the endpoint column at the top. -/
def FF (u : F2Word) (j : ℤ) : ℤ :=
  if j < 0 then 0 else if j < cntI u then colN u (0, 0) j else (F2Word.sum u).1

theorem cntI_snoc (u : F2Word) (x : Unit4) :
    cntI (u ++ [x]) = cntI u + (if x = .i then 1 else 0) := by
  rw [cntI_append]
  cases x <;> simp [cntI]

theorem sum_snoc (u : F2Word) (x : Unit4) : F2Word.sum (u ++ [x]) = F2Word.sum u + x.vec := by
  rw [arc_sum_append]
  simp [F2Word.sum]

theorem edges_snoc (u : F2Word) (x : Unit4) (e : GInt × GInt) :
    e ∈ edgesFrom (0, 0) (u ++ [x]) ↔ e ∈ edgesFrom (0, 0) u ∨ e = (F2Word.sum u, F2Word.sum u + x.vec) := by
  rw [edgesFrom_append]
  simp [edgesFrom, arc_zero_add]

theorem edges_snoc_eq (u : F2Word) (x : Unit4) :
    edgesFrom (0, 0) (u ++ [x]) = edgesFrom (0, 0) u ++ [(F2Word.sum u, F2Word.sum u + x.vec)] := by
  rw [edgesFrom_append]
  simp [edgesFrom, arc_zero_add]

theorem colN_snoc_lt (u : F2Word) (x : Unit4) (hu : ∀ y ∈ u, y ≠ .negI) (k : ℤ) (hk0 : 0 ≤ k)
    (hk : k < cntI u) : colN (u ++ [x]) (0, 0) k = colN u (0, 0) k := by
  apply colN_lo u [x] hu (0, 0) k
  · show (0 : ℤ) ≤ k
    exact hk0
  · show k < (0 : ℤ) + cntI u
    omega

theorem colN_snoc_i_cnt (u : F2Word) (hu : ∀ y ∈ u, y ≠ .negI) :
    colN (u ++ [.i]) (0, 0) (cntI u) = (F2Word.sum u).1 := by
  have h := colN_hi u [.i] hu (0, 0) (cntI u) (by
    show (0 : ℤ) + cntI u ≤ cntI u
    omega)
  rw [h]
  have hs : (F2Word.sum u).2 = cntI u := sum_snd u hu
  simp only [colN]
  simp [hs]

theorem FF_snoc_lt (u : F2Word) (x : Unit4) (hu : ∀ y ∈ u, y ≠ .negI) (j : ℤ) (hj : j < cntI u) :
    FF (u ++ [x]) j = FF u j := by
  have hc : cntI u ≤ cntI (u ++ [x]) := by
    rw [cntI_snoc]
    split_ifs <;> omega
  by_cases h0 : j < 0
  · simp [FF, h0]
  · have h1 : j < cntI (u ++ [x]) := lt_of_lt_of_le hj hc
    unfold FF
    rw [if_neg h0, if_pos h1, if_neg h0, if_pos hj]
    exact colN_snoc_lt u x hu j (by omega) hj

theorem FF_at_cnt (u : F2Word) : FF u (cntI u) = (F2Word.sum u).1 := by
  have hnn := cntI_nonneg u
  unfold FF
  rw [if_neg (by omega), if_neg (lt_irrefl _)]

theorem FF_snoc_one_cnt (u : F2Word) : FF (u ++ [.one]) (cntI u) = (F2Word.sum u).1 + 1 := by
  have hc : cntI (u ++ [Unit4.one]) = cntI u := by
    rw [cntI_snoc]
    simp
  have hnn := cntI_nonneg u
  unfold FF
  rw [hc, if_neg (by omega), if_neg (lt_irrefl _), sum_snoc]
  simp [Unit4.vec]

theorem FF_snoc_negOne_cnt (u : F2Word) : FF (u ++ [.negOne]) (cntI u) = (F2Word.sum u).1 - 1 := by
  have hc : cntI (u ++ [Unit4.negOne]) = cntI u := by
    rw [cntI_snoc]
    simp
  have hnn := cntI_nonneg u
  unfold FF
  rw [hc, if_neg (by omega), if_neg (lt_irrefl _), sum_snoc]
  simp [Unit4.vec]
  ring

theorem FF_snoc_i_cnt (u : F2Word) (hu : ∀ y ∈ u, y ≠ .negI) :
    FF (u ++ [.i]) (cntI u) = (F2Word.sum u).1 := by
  have hc : cntI (u ++ [Unit4.i]) = cntI u + 1 := by
    rw [cntI_snoc]
    simp
  have hnn := cntI_nonneg u
  unfold FF
  rw [hc, if_neg (by omega), if_pos (by omega), colN_snoc_i_cnt u hu]

theorem FF_snoc_i_succ (u : F2Word) : FF (u ++ [.i]) (cntI u + 1) = (F2Word.sum u).1 := by
  have hc : cntI (u ++ [Unit4.i]) = cntI u + 1 := by
    rw [cntI_snoc]
    simp
  have hnn := cntI_nonneg u
  unfold FF
  rw [hc, if_neg (by omega), if_neg (lt_irrefl _), sum_snoc]
  simp [Unit4.vec]

/-- The new edges of an appended letter, written in the shapes of the run formulas. -/
theorem edge_one_eq (u : F2Word) (hu : ∀ y ∈ u, y ≠ .negI) (q k : ℤ) (hq : q = (F2Word.sum u).1)
    (hk : k = cntI u) : ((q, k), (q + 1, k)) = (F2Word.sum u, F2Word.sum u + Unit4.vec .one) := by
  have hs : (F2Word.sum u).2 = k := by rw [sum_snd u hu, hk]
  subst hq
  simp [Prod.ext_iff, Unit4.vec, hs]

theorem edge_negOne_eq (u : F2Word) (hu : ∀ y ∈ u, y ≠ .negI) (q k : ℤ) (hq : q = (F2Word.sum u).1 - 1)
    (hk : k = cntI u) : ((q + 1, k), (q, k)) = (F2Word.sum u, F2Word.sum u + Unit4.vec .negOne) := by
  have hs : (F2Word.sum u).2 = k := by rw [sum_snd u hu, hk]
  subst hq
  simp [Prod.ext_iff, Unit4.vec, hs]
  ring

theorem edge_i_eq (u : F2Word) (hu : ∀ y ∈ u, y ≠ .negI) (x k : ℤ) (hx : x = (F2Word.sum u).1)
    (hk : k = cntI u) : ((x, k), (x, k + 1)) = (F2Word.sum u, F2Word.sum u + Unit4.vec .i) := by
  have hs : (F2Word.sum u).2 = k := by rw [sum_snd u hu, hk]
  subst hx
  simp [Prod.ext_iff, Unit4.vec, hs]

/-- The run data of a word: the north, east and west edges, the nodup property, and the endpoint inequalities. -/
structure RunData (u : F2Word) : Prop where
  N : ∀ x k : ℤ, ((x, k), (x, k + 1)) ∈ edgesFrom (0, 0) u ↔ 0 ≤ k ∧ k < cntI u ∧ x = colN u (0, 0) k
  E : ∀ q k : ℤ, ((q, k), (q + 1, k)) ∈ edgesFrom (0, 0) u ↔
      0 ≤ k ∧ k ≤ cntI u ∧ FF u (k - 1) ≤ q ∧ q < FF u k
  W : ∀ q k : ℤ, ((q + 1, k), (q, k)) ∈ edgesFrom (0, 0) u ↔
      0 ≤ k ∧ k ≤ cntI u ∧ FF u k ≤ q ∧ q < FF u (k - 1)
  nodup : (edgesFrom (0, 0) u).Nodup
  inv1 : u.getLast? ≠ some .negOne → FF u (cntI u - 1) ≤ (F2Word.sum u).1
  inv2 : u.getLast? ≠ some .one → (F2Word.sum u).1 ≤ FF u (cntI u - 1)

theorem runData_nil : RunData [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x k
    constructor
    · intro h
      simp [edgesFrom] at h
    · rintro ⟨h0, hk, _⟩
      have : cntI ([] : F2Word) = 0 := rfl
      omega
  · intro q k
    simp [edgesFrom, cntI, FF, F2Word.sum]
    omega
  · intro q k
    simp [edgesFrom, cntI, FF, F2Word.sum]
    omega
  · simp [edgesFrom]
  · intro _
    simp [FF, cntI, F2Word.sum]
  · intro _
    simp [FF, cntI, F2Word.sum]

/-- Appending the letter `1`, after a word whose last letter is not `-1`. -/
theorem runData_snoc_one (u : F2Word) (hu : ∀ y ∈ u, y ≠ .negI) (h : RunData u)
    (hl : u.getLast? ≠ some .negOne) : RunData (u ++ [.one]) := by
  have hs := sum_snd u hu
  have hnn := cntI_nonneg u
  have hc : cntI (u ++ [Unit4.one]) = cntI u := by
    rw [cntI_snoc]
    simp
  have hFH : FF (u ++ [Unit4.one]) (cntI u) = (F2Word.sum u).1 + 1 := FF_snoc_one_cnt u
  have hFold : FF u (cntI u) = (F2Word.sum u).1 := FF_at_cnt u
  have hFlt : ∀ j, j < cntI u → FF (u ++ [Unit4.one]) j = FF u j :=
    fun j hj => FF_snoc_lt u Unit4.one hu j hj
  have hinv : FF u (cntI u - 1) ≤ (F2Word.sum u).1 := h.inv1 hl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x k
    rw [edges_snoc, h.N, hc]
    constructor
    · rintro (⟨h0, hk, hx⟩ | hn)
      · refine ⟨h0, hk, ?_⟩
        rw [colN_snoc_lt u Unit4.one hu k h0 hk]
        exact hx
      · exfalso
        have a1 := congrArg (fun p => p.1.2) hn
        have a2 := congrArg (fun p => p.2.2) hn
        simp [Unit4.vec] at a1 a2
        omega
    · rintro ⟨h0, hk, hx⟩
      left
      refine ⟨h0, hk, ?_⟩
      rw [colN_snoc_lt u Unit4.one hu k h0 hk] at hx
      exact hx
  · intro q k
    rw [edges_snoc, h.E, hc]
    rcases lt_trichotomy k (cntI u) with hk | hk | hk
    · rw [hFlt (k - 1) (by omega), hFlt k hk]
      constructor
      · rintro (h1 | hn)
        · exact h1
        · exfalso
          have a1 := congrArg (fun p => p.1.2) hn
          simp at a1
          omega
      · intro h1
        exact Or.inl h1
    · subst hk
      rw [hFlt (cntI u - 1) (by omega), hFH, hFold]
      constructor
      · rintro (h1 | hn)
        · obtain ⟨h0, h1a, h1b, h1c⟩ := h1
          exact ⟨h0, h1a, h1b, by omega⟩
        · have a1 := congrArg (fun p => p.1.1) hn
          simp at a1
          refine ⟨by omega, by omega, ?_, ?_⟩
          · rw [a1]
            exact hinv
          · rw [a1]
            omega
      · rintro ⟨h0, hk2, h1, h2⟩
        by_cases hq : q < (F2Word.sum u).1
        · exact Or.inl ⟨h0, hk2, h1, hq⟩
        · right
          have hq' : q = (F2Word.sum u).1 := by omega
          rw [hq']
          exact edge_one_eq u hu _ _ rfl rfl
    · have hnk : ¬ (k ≤ cntI u) := by omega
      constructor
      · rintro (h1 | hn)
        · exact absurd h1.2.1 hnk
        · exfalso
          have a1 := congrArg (fun p => p.1.2) hn
          simp at a1
          omega
      · rintro ⟨h0, hk2, _⟩
        exact absurd hk2 hnk
  · intro q k
    rw [edges_snoc, h.W, hc]
    rcases lt_trichotomy k (cntI u) with hk | hk | hk
    · rw [hFlt k hk, hFlt (k - 1) (by omega)]
      constructor
      · rintro (h1 | hn)
        · exact h1
        · exfalso
          have a1 := congrArg (fun p => p.1.1) hn
          have a2 := congrArg (fun p => p.2.1) hn
          simp [Unit4.vec] at a1 a2
          omega
      · intro h1
        exact Or.inl h1
    · subst hk
      rw [hFH, hFold, hFlt (cntI u - 1) (by omega)]
      constructor
      · rintro (h1 | hn)
        · exfalso
          obtain ⟨-, -, h3, h4⟩ := h1
          omega
        · exfalso
          have a1 := congrArg (fun p => p.1.1) hn
          have a2 := congrArg (fun p => p.2.1) hn
          simp [Unit4.vec] at a1 a2
          omega
      · rintro ⟨h0, hk2, h1, h2⟩
        exfalso
        omega
    · have hnk : ¬ (k ≤ cntI u) := by omega
      constructor
      · rintro (h1 | hn)
        · exact absurd h1.2.1 hnk
        · exfalso
          have a1 := congrArg (fun p => p.1.2) hn
          simp at a1
          omega
      · rintro ⟨h0, hk2, _⟩
        exact absurd hk2 hnk
  · have hnot : (F2Word.sum u, F2Word.sum u + Unit4.vec .one) ∉ edgesFrom (0, 0) u := by
      intro hmem
      rw [← edge_one_eq u hu _ _ rfl rfl] at hmem
      have hE := (h.E (F2Word.sum u).1 (cntI u)).1 hmem
      obtain ⟨-, -, -, h4⟩ := hE
      omega
    rw [edges_snoc_eq, List.nodup_append]
    refine ⟨h.nodup, List.nodup_singleton _, ?_⟩
    intro a ha b hb hab
    rw [List.mem_singleton] at hb
    rw [hb] at hab
    rw [hab] at ha
    exact hnot ha
  · intro _
    rw [hc, sum_snoc, hFlt (cntI u - 1) (by omega)]
    have e1 : (F2Word.sum u + Unit4.vec .one).1 = (F2Word.sum u).1 + 1 := by simp [Unit4.vec]
    rw [e1]
    omega
  · intro h2
    exfalso
    apply h2
    simp

/-- Appending the letter `-1`, after a word whose last letter is not `1`. -/
theorem runData_snoc_negOne (u : F2Word) (hu : ∀ y ∈ u, y ≠ .negI) (h : RunData u)
    (hl : u.getLast? ≠ some .one) : RunData (u ++ [.negOne]) := by
  have hs := sum_snd u hu
  have hnn := cntI_nonneg u
  have hc : cntI (u ++ [Unit4.negOne]) = cntI u := by
    rw [cntI_snoc]
    simp
  have hFH : FF (u ++ [Unit4.negOne]) (cntI u) = (F2Word.sum u).1 - 1 := FF_snoc_negOne_cnt u
  have hFold : FF u (cntI u) = (F2Word.sum u).1 := FF_at_cnt u
  have hFlt : ∀ j, j < cntI u → FF (u ++ [Unit4.negOne]) j = FF u j :=
    fun j hj => FF_snoc_lt u Unit4.negOne hu j hj
  have hinv : (F2Word.sum u).1 ≤ FF u (cntI u - 1) := h.inv2 hl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x k
    rw [edges_snoc, h.N, hc]
    constructor
    · rintro (⟨h0, hk, hx⟩ | hn)
      · refine ⟨h0, hk, ?_⟩
        rw [colN_snoc_lt u Unit4.negOne hu k h0 hk]
        exact hx
      · exfalso
        have a1 := congrArg (fun p => p.1.2) hn
        have a2 := congrArg (fun p => p.2.2) hn
        simp [Unit4.vec] at a1 a2
        omega
    · rintro ⟨h0, hk, hx⟩
      left
      refine ⟨h0, hk, ?_⟩
      rw [colN_snoc_lt u Unit4.negOne hu k h0 hk] at hx
      exact hx
  · intro q k
    rw [edges_snoc, h.E, hc]
    rcases lt_trichotomy k (cntI u) with hk | hk | hk
    · rw [hFlt (k - 1) (by omega), hFlt k hk]
      constructor
      · rintro (h1 | hn)
        · exact h1
        · exfalso
          have a1 := congrArg (fun p => p.1.2) hn
          simp at a1
          omega
      · intro h1
        exact Or.inl h1
    · subst hk
      rw [hFlt (cntI u - 1) (by omega), hFH, hFold]
      constructor
      · rintro (h1 | hn)
        · exfalso
          obtain ⟨-, -, h3, h4⟩ := h1
          omega
        · exfalso
          have a1 := congrArg (fun p => p.1.1) hn
          have a2 := congrArg (fun p => p.2.1) hn
          simp [Unit4.vec] at a1 a2
          omega
      · rintro ⟨h0, hk2, h1, h2⟩
        exfalso
        omega
    · have hnk : ¬ (k ≤ cntI u) := by omega
      constructor
      · rintro (h1 | hn)
        · exact absurd h1.2.1 hnk
        · exfalso
          have a1 := congrArg (fun p => p.1.2) hn
          simp at a1
          omega
      · rintro ⟨h0, hk2, _⟩
        exact absurd hk2 hnk
  · intro q k
    rw [edges_snoc, h.W, hc]
    rcases lt_trichotomy k (cntI u) with hk | hk | hk
    · rw [hFlt k hk, hFlt (k - 1) (by omega)]
      constructor
      · rintro (h1 | hn)
        · exact h1
        · exfalso
          have a1 := congrArg (fun p => p.1.2) hn
          simp at a1
          omega
      · intro h1
        exact Or.inl h1
    · subst hk
      rw [hFlt (cntI u - 1) (by omega), hFH, hFold]
      constructor
      · rintro (h1 | hn)
        · obtain ⟨h0, h1a, h1b, h1c⟩ := h1
          refine ⟨h0, h1a, by omega, h1c⟩
        · have a1 := congrArg (fun p => p.1.1) hn
          have a2 := congrArg (fun p => p.2.1) hn
          simp [Unit4.vec] at a1 a2
          refine ⟨by omega, by omega, by omega, by omega⟩
      · rintro ⟨h0, hk2, h1, h2⟩
        by_cases hq : (F2Word.sum u).1 ≤ q
        · exact Or.inl ⟨h0, hk2, hq, h2⟩
        · right
          exact edge_negOne_eq u hu _ _ (by omega) rfl
    · have hnk : ¬ (k ≤ cntI u) := by omega
      constructor
      · rintro (h1 | hn)
        · exact absurd h1.2.1 hnk
        · exfalso
          have a1 := congrArg (fun p => p.1.2) hn
          simp at a1
          omega
      · rintro ⟨h0, hk2, _⟩
        exact absurd hk2 hnk
  · have hnot : (F2Word.sum u, F2Word.sum u + Unit4.vec .negOne) ∉ edgesFrom (0, 0) u := by
      intro hmem
      rw [← edge_negOne_eq u hu _ _ rfl rfl] at hmem
      have hW := (h.W ((F2Word.sum u).1 - 1) (cntI u)).1 hmem
      obtain ⟨-, -, h3, -⟩ := hW
      omega
    rw [edges_snoc_eq, List.nodup_append]
    refine ⟨h.nodup, List.nodup_singleton _, ?_⟩
    intro a ha b hb hab
    rw [List.mem_singleton] at hb
    rw [hb] at hab
    rw [hab] at ha
    exact hnot ha
  · intro h2
    exfalso
    apply h2
    simp
  · intro _
    rw [hc, sum_snoc, hFlt (cntI u - 1) (by omega)]
    have e1 : (F2Word.sum u + Unit4.vec .negOne).1 = (F2Word.sum u).1 - 1 := by simp [Unit4.vec]; ring
    rw [e1]
    omega

/-- Appending the letter `i`. -/
theorem runData_snoc_i (u : F2Word) (hu : ∀ y ∈ u, y ≠ .negI) (h : RunData u) : RunData (u ++ [.i]) := by
  have hs := sum_snd u hu
  have hnn := cntI_nonneg u
  have hc : cntI (u ++ [Unit4.i]) = cntI u + 1 := by
    rw [cntI_snoc]
    simp
  have hFH : FF (u ++ [Unit4.i]) (cntI u) = (F2Word.sum u).1 := FF_snoc_i_cnt u hu
  have hFS : FF (u ++ [Unit4.i]) (cntI u + 1) = (F2Word.sum u).1 := FF_snoc_i_succ u
  have hFold : FF u (cntI u) = (F2Word.sum u).1 := FF_at_cnt u
  have hFlt : ∀ j, j < cntI u → FF (u ++ [Unit4.i]) j = FF u j :=
    fun j hj => FF_snoc_lt u Unit4.i hu j hj
  have hFeq : ∀ j, j ≤ cntI u → FF (u ++ [Unit4.i]) j = FF u j := by
    intro j hj
    rcases lt_or_eq_of_le hj with hj' | hj'
    · exact hFlt j hj'
    · rw [hj', hFH, hFold]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x k
    rw [edges_snoc, h.N, hc]
    constructor
    · rintro (⟨h0, hk, hx⟩ | hn)
      · refine ⟨h0, by omega, ?_⟩
        rw [colN_snoc_lt u Unit4.i hu k h0 hk]
        exact hx
      · have a1 := congrArg (fun p => p.1.2) hn
        have a2 := congrArg (fun p => p.1.1) hn
        simp at a1 a2
        refine ⟨by omega, by omega, ?_⟩
        rw [show k = cntI u by omega, colN_snoc_i_cnt u hu, a2]
    · rintro ⟨h0, hk, hx⟩
      by_cases hk2 : k < cntI u
      · left
        refine ⟨h0, hk2, ?_⟩
        rw [colN_snoc_lt u Unit4.i hu k h0 hk2] at hx
        exact hx
      · right
        have hk' : k = cntI u := by omega
        have hx' : x = (F2Word.sum u).1 := by
          rw [hk', colN_snoc_i_cnt u hu] at hx
          exact hx
        exact edge_i_eq u hu x k hx' hk'
  · intro q k
    rw [edges_snoc, h.E, hc]
    rcases (show k ≤ cntI u ∨ cntI u < k by omega) with hkle | hkgt
    · rw [hFeq (k - 1) (by omega), hFeq k hkle]
      constructor
      · rintro (h1 | hn)
        · exact ⟨h1.1, by omega, h1.2.2.1, h1.2.2.2⟩
        · exfalso
          have a1 := congrArg (fun p => p.1.2) hn
          have a2 := congrArg (fun p => p.2.2) hn
          simp [Unit4.vec] at a1 a2
          omega
      · intro h1
        exact Or.inl ⟨h1.1, hkle, h1.2.2.1, h1.2.2.2⟩
    · constructor
      · rintro (h1 | hn)
        · exact absurd h1.2.1 (by omega)
        · exfalso
          have a1 := congrArg (fun p => p.1.2) hn
          have a2 := congrArg (fun p => p.2.2) hn
          simp [Unit4.vec] at a1 a2
          omega
      · rintro ⟨h0, hk, h1, h2⟩
        have hk1 : k = cntI u + 1 := by omega
        have e : k - 1 = cntI u := by omega
        rw [e, hFH] at h1
        rw [hk1, hFS] at h2
        exfalso
        omega
  · intro q k
    rw [edges_snoc, h.W, hc]
    rcases (show k ≤ cntI u ∨ cntI u < k by omega) with hkle | hkgt
    · rw [hFeq k hkle, hFeq (k - 1) (by omega)]
      constructor
      · rintro (h1 | hn)
        · exact ⟨h1.1, by omega, h1.2.2.1, h1.2.2.2⟩
        · exfalso
          have a1 := congrArg (fun p => p.1.1) hn
          have a2 := congrArg (fun p => p.2.1) hn
          simp [Unit4.vec] at a1 a2
          omega
      · intro h1
        exact Or.inl ⟨h1.1, hkle, h1.2.2.1, h1.2.2.2⟩
    · constructor
      · rintro (h1 | hn)
        · exact absurd h1.2.1 (by omega)
        · exfalso
          have a1 := congrArg (fun p => p.1.2) hn
          have a2 := congrArg (fun p => p.2.2) hn
          simp [Unit4.vec] at a1 a2
          omega
      · rintro ⟨h0, hk, h1, h2⟩
        have hk1 : k = cntI u + 1 := by omega
        have e : k - 1 = cntI u := by omega
        rw [hk1, hFS] at h1
        rw [e, hFH] at h2
        exfalso
        omega
  · have hnot : (F2Word.sum u, F2Word.sum u + Unit4.vec .i) ∉ edgesFrom (0, 0) u := by
      intro hmem
      rw [← edge_i_eq u hu _ _ rfl rfl] at hmem
      have hN' := (h.N (F2Word.sum u).1 (cntI u)).1 hmem
      obtain ⟨-, h5, -⟩ := hN'
      omega
    rw [edges_snoc_eq, List.nodup_append]
    refine ⟨h.nodup, List.nodup_singleton _, ?_⟩
    intro a ha b hb hab
    rw [List.mem_singleton] at hb
    rw [hb] at hab
    rw [hab] at ha
    exact hnot ha
  · intro _
    have e : cntI u + 1 - 1 = cntI u := by omega
    rw [hc, e, hFH, sum_snoc]
    have e1 : (F2Word.sum u + Unit4.vec .i).1 = (F2Word.sum u).1 := by simp [Unit4.vec]
    rw [e1]
  · intro _
    have e : cntI u + 1 - 1 = cntI u := by omega
    rw [hc, e, hFH, sum_snoc]
    have e1 : (F2Word.sum u + Unit4.vec .i).1 = (F2Word.sum u).1 := by simp [Unit4.vec]
    rw [e1]

/-- Adjacent letters that are not `1, -1` and not `-1, 1`. -/
def NoEWAdj (a b : Unit4) : Prop := ¬ ((a = .one ∧ b = .negOne) ∨ (a = .negOne ∧ b = .one))

/-- No adjacent pair of letters is `1, -1` or `-1, 1`. -/
def NoEWChain : F2Word → Prop
  | [] => True
  | [_] => True
  | x :: y :: u => NoEWAdj x y ∧ NoEWChain (y :: u)

theorem noEWChain_snoc : ∀ (u : F2Word) (x : Unit4),
    NoEWChain (u ++ [x]) ↔ NoEWChain u ∧ ∀ y ∈ u.getLast?, NoEWAdj y x
  | [], x => by simp [NoEWChain]
  | [a], x => by simp [NoEWChain]
  | a :: b :: u, x => by
      have ih := noEWChain_snoc (b :: u) x
      simp only [List.cons_append, NoEWChain, List.getLast?_cons_cons] at ih ⊢
      rw [ih]
      tauto

/-- The run data of every word over `1, i, -1` without adjacent `1, -1` or `-1, 1`. -/
theorem runData_of (u : F2Word) :
    (∀ y ∈ u, y = .one ∨ y = .i ∨ y = .negOne) → NoEWChain u → RunData u := by
  induction u using List.reverseRecOn with
  | nil => intro _ _; exact runData_nil
  | append_singleton v x ih =>
    intro hu hch
    rw [noEWChain_snoc] at hch
    obtain ⟨hv, hlast⟩ := hch
    have huv : ∀ y ∈ v, y = .one ∨ y = .i ∨ y = .negOne := fun y hy => hu y (List.mem_append_left _ hy)
    have hvr := ih huv hv
    have hnegI : ∀ y ∈ v, y ≠ .negI := fun y hy => by
      rcases huv y hy with h | h | h <;> simp [h]
    rcases hu x (List.mem_append_right _ (List.mem_singleton_self _)) with rfl | rfl | rfl
    · exact runData_snoc_one v hnegI hvr (fun hcontra =>
        hlast _ (Option.mem_def.mpr hcontra) (Or.inr ⟨rfl, rfl⟩))
    · exact runData_snoc_i v hnegI hvr
    · exact runData_snoc_negOne v hnegI hvr (fun hcontra =>
        hlast _ (Option.mem_def.mpr hcontra) (Or.inl ⟨rfl, rfl⟩))

end FLatticePaper.Tiles.RegionRuns
