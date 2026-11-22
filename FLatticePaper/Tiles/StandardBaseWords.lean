import FLatticePaper.Tiles.StandardBoundary
import FLatticePaper.Tiles.NearLadderBoundary
import FLatticePaper.Tiles.BaseCellIdentities

/-! The standard boundary words at the base words: the empty word, `3^k` (`k ≥ 1`) and `2^k` (`k ≥ 1`).

Their odd and even standard tiles are the base tiles of `childTiles` (`StandardTiles.lean`), and their bottom edges are
the base edges `baseTwoEdges`, `baseThreeEdges` of the recursion (`BottomEdges.lean`). The boundary words are then the
explicit words of the repo's base walks: `stairWord` (stair tile), `ladderWord` (ladder tile), and the near-one words of
`NearStairBoundary.lean` and `NearLadderBoundary.lean`. -/

namespace FLatticePaper.Tiles.StandardBaseWords

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
open FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.StandardClause FLatticePaper.Tiles.BaseCellIdentities
open FLatticePaper.Tiles.NearStairBoundary FLatticePaper.Tiles.NearLadderBoundary

/-! ### Flattened pairs -/

theorem flat_shift_gen (a b : Unit4) (n : ℕ) :
    (List.replicate n [a, b]).flatten ++ [a] = a :: (List.replicate n [b, a]).flatten := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.replicate_succ, List.flatten_cons, ih, List.cons_append, List.nil_append]

/-- The middle of the stair and ladder walks, `i (i, -1)^n` against `(i, -1)` shifted: `i · (1 i)` pairs. -/
theorem shift_mid (n : ℕ) :
    [Unit4.i] ++ (List.replicate n [Unit4.i, Unit4.negOne]).flatten ++ [Unit4.i, Unit4.i] =
      [Unit4.i, Unit4.i] ++ (List.replicate n [Unit4.negOne, Unit4.i]).flatten ++ [Unit4.i] := by
  have e : [Unit4.i] ++ (List.replicate n [Unit4.i, Unit4.negOne]).flatten ++ [Unit4.i, Unit4.i] =
      [Unit4.i] ++ ((List.replicate n [Unit4.i, Unit4.negOne]).flatten ++ [Unit4.i]) ++ [Unit4.i] := by
    simp
  rw [e, flat_shift_gen]
  simp

/-- The negative counterpart of `shift_mid`. -/
theorem shift_mid_neg (n : ℕ) :
    [Unit4.negI] ++ (List.replicate n [Unit4.negI, Unit4.one]).flatten ++ [Unit4.negI, Unit4.negI] =
      [Unit4.negI, Unit4.negI] ++ (List.replicate n [Unit4.one, Unit4.negI]).flatten ++ [Unit4.negI] := by
  have e : [Unit4.negI] ++ (List.replicate n [Unit4.negI, Unit4.one]).flatten ++ [Unit4.negI, Unit4.negI] =
      [Unit4.negI] ++ ((List.replicate n [Unit4.negI, Unit4.one]).flatten ++ [Unit4.negI]) ++ [Unit4.negI] := by
    simp
  rw [e, flat_shift_gen]
  simp

/-! ### The turned base edges -/

theorem M1_eq (k : ℕ) : (baseTwoEdges k).1.map Unit4.mulI =
    [Unit4.i] ++ (List.replicate (2 * k + 1) [Unit4.i, Unit4.negOne]).flatten ++ [Unit4.i, Unit4.i] := by
  unfold baseTwoEdges oneI
  simp only [List.map_append, List.map_cons, List.map_nil, map_flatten_rep, Unit4.mulI]

theorem M2_eq (m : ℕ) : (baseTwoEdges (m + 1)).2.map Unit4.mulI =
    [Unit4.i] ++ (List.replicate (2 * m + 1 + 1) [Unit4.i, Unit4.negOne]).flatten ++ [Unit4.i, Unit4.i] := by
  unfold baseTwoEdges oneI
  simp only [List.map_append, List.map_cons, List.map_nil, map_flatten_rep, Unit4.mulI,
    show 2 * (m + 1) = 2 * m + 1 + 1 by ring]

theorem baseTwo_zero_snd : (baseTwoEdges 0).2 = (baseThreeEdges 0).2 := by decide

theorem baseTwo_zero_snd_eq : (baseTwoEdges 0).2 = List.replicate (2 * 0 + 3) Unit4.one := by decide

/-! ### The base words of the recursion -/

theorem allTwos_replicate_two (k : ℕ) : allTwos (List.replicate k Digit.two) = true := by
  rw [allTwos_iff]
  intro y hy
  exact List.eq_of_mem_replicate hy

theorem allThrees_replicate_three {k : ℕ} (hk : 1 ≤ k) :
    allThrees (List.replicate k Digit.three) = true := by
  rw [allThrees_iff]
  refine ⟨?_, fun y hy => List.eq_of_mem_replicate hy⟩
  intro h
  have := congrArg List.length h
  simp at this
  omega

theorem allTwos_false_of_allThrees (u : Word) (h : allThrees u = true) : allTwos u = false := by
  obtain ⟨hne, hall⟩ := (allThrees_iff u).1 h
  cases u with
  | nil => exact absurd rfl hne
  | cons y u =>
    have hy : y = Digit.three := hall y (by simp)
    subst hy
    simp [allTwos]

theorem bottomFrom_two (rest : Word) : ∀ (pre : Word) (regs : F2Word × F2Word),
    allTwos (pre ++ rest) = true → bottomFrom pre rest regs = baseTwoEdges (pre ++ rest).length := by
  induction rest with
  | nil =>
    intro pre regs h
    simp only [bottomFrom, List.append_nil] at h ⊢
    simp [prefixEdges, h]
  | cons x rest ih =>
    intro pre regs h
    simp only [bottomFrom]
    rw [ih (pre ++ [x]) _ (by simpa [List.append_assoc] using h)]
    simp only [List.append_assoc, List.singleton_append]

theorem bottomFrom_three (rest : Word) : ∀ (pre : Word) (regs : F2Word × F2Word),
    allThrees (pre ++ rest) = true → bottomFrom pre rest regs = baseThreeEdges (pre ++ rest).length := by
  induction rest with
  | nil =>
    intro pre regs h
    simp only [bottomFrom, List.append_nil] at h ⊢
    simp [prefixEdges, h, allTwos_false_of_allThrees pre h]
  | cons x rest ih =>
    intro pre regs h
    simp only [bottomFrom]
    rw [ih (pre ++ [x]) _ (by simpa [List.append_assoc] using h)]
    simp only [List.append_assoc, List.singleton_append]

theorem bottomEdges_two (k : ℕ) : bottomEdges (List.replicate k Digit.two) = baseTwoEdges k := by
  unfold bottomEdges
  rw [bottomFrom_two (List.replicate k Digit.two) [] ([], []) (by simpa using allTwos_replicate_two k)]
  simp

theorem bottomEdges_three (k : ℕ) (hk : 1 ≤ k) :
    bottomEdges (List.replicate k Digit.three) = baseThreeEdges k := by
  unfold bottomEdges
  rw [bottomFrom_three (List.replicate k Digit.three) [] ([], [])
    (by simpa using allThrees_replicate_three hk)]
  simp

theorem bottomEdges_nil : bottomEdges [] = baseTwoEdges 0 := by
  simpa using bottomEdges_two 0

theorem swap_replicate_two (k : ℕ) :
    (List.replicate k Digit.two).map Digit.swapTwoThree = List.replicate k Digit.three := by
  simp [List.map_replicate, Digit.swapTwoThree]

theorem swap_replicate_three (k : ℕ) :
    (List.replicate k Digit.three).map Digit.swapTwoThree = List.replicate k Digit.two := by
  simp [List.map_replicate, Digit.swapTwoThree]

/-! ### The edges of the standard tiles at the base words -/

theorem oddBottom_rep_two (k : ℕ) : oddBottom (List.replicate k Digit.two) = (baseTwoEdges k).1 := by
  unfold oddBottom
  rw [bottomEdges_two]

theorem oddRight_rep_two (k : ℕ) (hk : 1 ≤ k) :
    oddRight (List.replicate k Digit.two) = (baseThreeEdges k).2.map Unit4.mulI := by
  unfold oddRight
  rw [swap_replicate_two, bottomEdges_three k hk]

theorem evenBottom_rep_two (k : ℕ) : evenBottom (List.replicate k Digit.two) = (baseTwoEdges k).2 := by
  unfold evenBottom
  rw [bottomEdges_two]

theorem evenRight_rep_two (k : ℕ) (hk : 1 ≤ k) :
    evenRight (List.replicate k Digit.two) = (baseThreeEdges k).1.map Unit4.mulI := by
  unfold evenRight
  rw [swap_replicate_two, bottomEdges_three k hk]

theorem oddBottom_rep_three (k : ℕ) (hk : 1 ≤ k) :
    oddBottom (List.replicate k Digit.three) = (baseThreeEdges k).1 := by
  unfold oddBottom
  rw [bottomEdges_three k hk]

theorem oddRight_rep_three (k : ℕ) :
    oddRight (List.replicate k Digit.three) = (baseTwoEdges k).2.map Unit4.mulI := by
  unfold oddRight
  rw [swap_replicate_three, bottomEdges_two]

theorem evenBottom_rep_three (k : ℕ) (hk : 1 ≤ k) :
    evenBottom (List.replicate k Digit.three) = (baseThreeEdges k).2 := by
  unfold evenBottom
  rw [bottomEdges_three k hk]

theorem evenRight_rep_three (k : ℕ) :
    evenRight (List.replicate k Digit.three) = (baseTwoEdges k).1.map Unit4.mulI := by
  unfold evenRight
  rw [swap_replicate_three, bottomEdges_two]

theorem oddBottom_nil : oddBottom [] = (baseTwoEdges 0).1 := by
  unfold oddBottom
  rw [bottomEdges_nil]

theorem oddRight_nil : oddRight [] = (baseTwoEdges 0).2.map Unit4.mulI := by
  unfold oddRight
  rw [List.map_nil, bottomEdges_nil]

theorem evenBottom_nil : evenBottom [] = (baseTwoEdges 0).2 := by
  unfold evenBottom
  rw [bottomEdges_nil]

theorem evenRight_nil : evenRight [] = (baseTwoEdges 0).1.map Unit4.mulI := by
  unfold evenRight
  rw [List.map_nil, bottomEdges_nil]

/-! ### The base words as boundary words of the repo's walks -/

/-- The stair walk is the boundary word of `(1^(2k+3), i · w₀ (2^k))`. -/
theorem stairWord_eq (k : ℕ) :
    stairWord k = boundaryWordOf (List.replicate (2 * k + 3) Unit4.one) ((baseTwoEdges k).1.map Unit4.mulI) := by
  rw [M1_eq]
  unfold stairWord boundaryWordOf
  rw [hat_rev_map_neg, hat_rev_map_neg]
  simp only [List.map_append, List.map_cons, List.map_nil, List.map_replicate, map_flatten_rep, Unit4.neg]
  rw [shift_mid (2 * k + 1), shift_mid_neg (2 * k + 1)]
  simp only [List.append_assoc]

/-- The ladder walk is the boundary word of `(w₀ (3^(m+1)), i · v₀ (2^(m+1)))`. -/
theorem ladderWord_eq (m : ℕ) :
    ladderWord m = boundaryWordOf (baseThreeEdges (m + 1)).1 ((baseTwoEdges (m + 1)).2.map Unit4.mulI) := by
  rw [W1_eq, M2_eq, ladderWord_split]
  unfold boundaryWordOf
  rw [hat_rev_map_neg, hat_rev_map_neg]
  simp only [lU, lV, List.map_append, List.map_cons, List.map_nil, List.map_replicate, map_flatten_rep,
    Unit4.neg]
  rw [shift_mid (2 * m + 1 + 1), shift_mid_neg (2 * m + 1 + 1)]

/-! ### The standard boundary words of the three families -/

/-- The odd tile of `3^(m+1)` is `ladderF (2m+4)`, with the ladder walk. -/
theorem standardOdd_three (m : ℕ) : StandardBoundaryOdd (List.replicate (m + 1) Digit.three) := by
  unfold StandardBoundaryOdd
  have ht : oddTile (List.replicate (m + 1) Digit.three) = ladderF (2 * ((m + 1 : ℕ) : ℤ) + 2) := by
    unfold oddTile
    rw [childTiles_three (k := m + 1) (by omega)]
  have e : (2 * ((m + 1 : ℕ) : ℤ) + 2) = 2 * (m : ℤ) + 4 := by
    push_cast
    ring
  rw [ht, e, cellTileOf_ladderF (2 * (m : ℤ) + 4) (by omega)]
  have hw : boundaryWordOf (oddBottom (List.replicate (m + 1) Digit.three))
      (oddRight (List.replicate (m + 1) Digit.three)) = ladderWord m := by
    rw [oddBottom_rep_three (m + 1) (by omega), oddRight_rep_three, ladderWord_eq]
  rw [hw]
  exact ladder_boundary m

/-- The even tile of `3^(m+1)` is `stairF (2(m+1)+3)`, with the stair walk. -/
theorem standardEven_three (m : ℕ) : StandardBoundaryEven (List.replicate (m + 1) Digit.three) := by
  unfold StandardBoundaryEven
  have ht : evenTile (List.replicate (m + 1) Digit.three) = stairF (2 * ((m + 1 : ℕ) : ℤ) + 3) := by
    unfold evenTile
    rw [childTiles_three (k := m + 1) (by omega)]
  rw [ht, cellTileOf_stairF (2 * ((m + 1 : ℕ) : ℤ) + 3) (by omega)]
  have hw : boundaryWordOf (evenBottom (List.replicate (m + 1) Digit.three))
      (evenRight (List.replicate (m + 1) Digit.three)) = stairWord (m + 1) := by
    rw [evenBottom_rep_three (m + 1) (by omega), evenRight_rep_three, baseThree_two, stairWord_eq]
  rw [hw]
  exact stairWord_boundary (m + 1)

/-- The odd tile of `2^(m+1)` is `nstairN (2(m+1)+3)`, with the near-one stair walk. -/
theorem standardOdd_two (m : ℕ) : StandardBoundaryOdd (List.replicate (m + 1) Digit.two) := by
  unfold StandardBoundaryOdd
  have ht : oddTile (List.replicate (m + 1) Digit.two) = nstairN (2 * ((m + 1 : ℕ) : ℤ) + 3) := by
    unfold oddTile
    rw [childTiles_two (k := m + 1) (by omega)]
  have hw : boundaryWordOf (oddBottom (List.replicate (m + 1) Digit.two))
      (oddRight (List.replicate (m + 1) Digit.two)) =
        boundaryWordOf (baseTwoEdges (m + 1)).1 ((baseThreeEdges (m + 1)).2.map Unit4.mulI) := by
    rw [oddBottom_rep_two, oddRight_rep_two (m + 1) (by omega)]
  rw [ht, hw]
  exact nstairN_boundary (m + 1)

/-- The even tile of `2^(m+1)` is `nladderN (2(m+1)+2)`, with the near-one ladder walk. -/
theorem standardEven_two (m : ℕ) : StandardBoundaryEven (List.replicate (m + 1) Digit.two) := by
  unfold StandardBoundaryEven
  have ht : evenTile (List.replicate (m + 1) Digit.two) = nladderN (2 * ((m + 1 : ℕ) : ℤ) + 2) := by
    unfold evenTile
    rw [childTiles_two (k := m + 1) (by omega)]
  have e : (2 * ((m + 1 : ℕ) : ℤ) + 2) = 2 * (m : ℤ) + 4 := by
    push_cast
    ring
  have hw : boundaryWordOf (evenBottom (List.replicate (m + 1) Digit.two))
      (evenRight (List.replicate (m + 1) Digit.two)) =
        boundaryWordOf (baseTwoEdges (m + 1)).2 ((baseThreeEdges (m + 1)).1.map Unit4.mulI) := by
    rw [evenBottom_rep_two, evenRight_rep_two (m + 1) (by omega)]
  rw [ht, e, hw]
  exact nladderN_boundary m

/-- The odd tile of the empty word is `nstairN 3`, with the word `(w₀, i·v₀)` of `2^0`. -/
theorem standardOdd_nil : StandardBoundaryOdd [] := by
  unfold StandardBoundaryOdd
  have ht : oddTile [] = nstairN 3 := by
    unfold oddTile
    rw [childTiles_nil]
  have h0 := nstairN_boundary 0
  have e0 : (2 * ((0 : ℕ) : ℤ) + 3) = 3 := by norm_num
  rw [e0] at h0
  have hw : boundaryWordOf (oddBottom []) (oddRight []) =
      boundaryWordOf (baseTwoEdges 0).1 ((baseThreeEdges 0).2.map Unit4.mulI) := by
    rw [oddBottom_nil, oddRight_nil, baseTwo_zero_snd]
  rw [ht, hw]
  exact h0

/-- The even tile of the empty word is `stairF 3`, with the stair walk `stairWord 0`. -/
theorem standardEven_nil : StandardBoundaryEven [] := by
  unfold StandardBoundaryEven
  have ht : evenTile [] = stairF 3 := by
    unfold evenTile
    rw [childTiles_nil]
  rw [ht, cellTileOf_stairF 3 (by norm_num)]
  have h0 := stairWord_boundary 0
  have e0 : (2 * ((0 : ℕ) : ℤ) + 3) = 3 := by norm_num
  rw [e0] at h0
  have hw : boundaryWordOf (evenBottom []) (evenRight []) = stairWord 0 := by
    rw [evenBottom_nil, evenRight_nil, stairWord_eq 0, baseTwo_zero_snd_eq]
  rw [hw]
  exact h0

/-- The standard boundary words at the base words `3^(m+1)`. -/
theorem standardBoundaryWord_three (m : ℕ) : StandardBoundaryWord (List.replicate (m + 1) Digit.three) :=
  ⟨standardOdd_three m, standardEven_three m⟩

/-- The standard boundary words at the base words `2^(m+1)`. -/
theorem standardBoundaryWord_two (m : ℕ) : StandardBoundaryWord (List.replicate (m + 1) Digit.two) :=
  ⟨standardOdd_two m, standardEven_two m⟩

/-- The standard boundary words at the empty word. -/
theorem standardBoundaryWord_nil : StandardBoundaryWord [] :=
  ⟨standardOdd_nil, standardEven_nil⟩

end FLatticePaper.Tiles.StandardBaseWords
