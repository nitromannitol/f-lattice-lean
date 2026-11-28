import FLatticePaper.Tiles.GlueFull
import FLatticePaper.Tiles.SurgicalWeakOdometers
import FLatticePaper.Tiles.BaseTileProps
import FLatticePaper.Tiles.SpecialCells
import FLatticePaper.Tiles.DoubleBottomBase

/-! # Vacuity of the one-base-register clauses of `SwapBaseInput`

For the words whose one register is a base word, the clause is vacuous: the translates `O.dom + offO w i` and
`O.dom + offO w j` are disjoint, where `O` is the base odometer of that register (`PaperBaseCond`). This is the input of
`SwapBaseClauses.pairCompat_of_disjoint`. The offsets of the family word are closed forms in the run length, by
`Parents.step`. This file proves the family `V1`: the word `3^k · 2`, with the register `3^(k-1)` on the even side. -/

namespace FLatticePaper.Tiles.SwapVacuity

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Tiles.GlueFull FLatticePaper.Tiles.ChildGlue FLatticePaper.Tiles.BaseTileProps
open FLatticePaper.Tiles.SurgicalWeak
open FLatticePaper.Tiles.MixedPieces (qOffsetsOdd pOffsetsOdd pOffsetsEven qOffsetsEven)
open FLatticePaper.Tiles.Standard (stairF ladderF nstairN nstairF nladderN nladderF)
open FLatticePaper.Tiles.SpecialCells (parents_twos)
open FLatticePaper.Tiles.DoubleBottomBase (mem_nstairN_iff mem_nladderN_iff)

/-- The parents of `3^k · 2`: the odd parent is `1/(2k+2)`, the even parent `1/(2k+1)`. -/
theorem parents_V1 (k : ℕ) :
    parentsAt (List.replicate k Digit.three ++ [Digit.two]) = ⟨⟨1, 2 * (k : ℤ) + 2⟩, ⟨1, 2 * (k : ℤ) + 1⟩⟩ := by
  rw [parentsAt_append_singleton, parents_three]
  simp [Parents.step, Parents.current, Parents.combine]
  ring

/-- The phase of `3^k · 2` is `0`. -/
theorem phase_V1 (k : ℕ) : phase (List.replicate k Digit.three ++ [Digit.two]) = 0 := by
  simp [phase, List.count_append, List.count_replicate]

theorem offO_V1_2 (k : ℕ) : offO (List.replicate k Digit.three ++ [Digit.two]) 2 = (0, 0) := by
  unfold offO
  rw [if_neg (by norm_num)]
  unfold oddQ
  rw [parents_V1, phase_V1]
  refine Prod.ext ?_ ?_ <;> simp [qOffsetsOdd]

theorem offO_V1_3 (k : ℕ) :
    offO (List.replicate k Digit.three ++ [Digit.two]) 3 = (2 * (k : ℤ) + 1, 1) := by
  unfold offO
  rw [if_neg (by norm_num)]
  unfold oddQ
  rw [parents_V1, phase_V1]
  refine Prod.ext ?_ ?_ <;> simp [qOffsetsOdd, texV1Even, texV1Odd, texV2]

theorem offO_V1_4 (k : ℕ) :
    offO (List.replicate k Digit.three ++ [Digit.two]) 4 = (2 * (k : ℤ) + 3, 2 * (k : ℤ) + 5) := by
  unfold offO
  rw [if_neg (by norm_num)]
  unfold oddQ
  rw [parents_V1, phase_V1]
  refine Prod.ext ?_ ?_
  all_goals simp [qOffsetsOdd, texV1Even, texV1Odd, texV2]
  all_goals ring

theorem offO_V1_5 (k : ℕ) :
    offO (List.replicate k Digit.three ++ [Digit.two]) 5 = (4 * (k : ℤ) + 4, 2 * (k : ℤ) + 6) := by
  unfold offO
  rw [if_neg (by norm_num)]
  unfold oddQ
  rw [parents_V1, phase_V1]
  refine Prod.ext ?_ ?_
  all_goals simp [qOffsetsOdd, texV1Even, texV1Odd, texV2]
  all_goals ring

/-- The base domain of `3^m`: the even child of `3^m` has the domain `stairF (2m+3)`. -/
theorem pbc_three_even (m : ℕ) (O E : PartialOdometer)
    (h : PaperBaseCond (List.replicate m Digit.three) O E) : E.dom = stairF (2 * (m : ℤ) + 3) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · obtain ⟨-, -, hd, -⟩ := h.1 rfl
    rw [hd]
    norm_num
  · obtain ⟨-, -, hd, -⟩ := h.2.1 m hm rfl
    exact hd

/-- The two clauses `V1` of the family `3^k · 2` (odd `(3,4)` and `(2,5)` on the even register `3^(k-1)`): the even base
domain `stairF (2k+1)` has second coordinates in `[0, 2k+2]`, and the offsets differ by more. -/
theorem vac_V1_pure (k : ℕ) :
    (∀ x ∈ stairF (2 * (k : ℤ) + 1), ∀ y ∈ stairF (2 * (k : ℤ) + 1),
      x + offO (List.replicate k Digit.three ++ [Digit.two]) 3 ≠
        y + offO (List.replicate k Digit.three ++ [Digit.two]) 4) ∧
    (∀ x ∈ stairF (2 * (k : ℤ) + 1), ∀ y ∈ stairF (2 * (k : ℤ) + 1),
      x + offO (List.replicate k Digit.three ++ [Digit.two]) 2 ≠
        y + offO (List.replicate k Digit.three ++ [Digit.two]) 5) := by
  constructor
  · intro x hx y hy heq
    rw [offO_V1_3, offO_V1_4] at heq
    simp only [stairF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hx hy
    simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add] at heq
    omega
  · intro x hx y hy heq
    rw [offO_V1_2, offO_V1_5] at heq
    simp only [stairF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hx hy
    simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add] at heq
    omega

/-- The clauses `V1` on the even base odometer of the register `3^(k-1)`. -/
theorem vac_V1 (k : ℕ) (hk : 1 ≤ k) (O E : PartialOdometer)
    (h : PaperBaseCond (List.replicate (k - 1) Digit.three) O E) :
    (∀ x ∈ E.dom, ∀ y ∈ E.dom,
      x + offO (List.replicate k Digit.three ++ [Digit.two]) 3 ≠
        y + offO (List.replicate k Digit.three ++ [Digit.two]) 4) ∧
    (∀ x ∈ E.dom, ∀ y ∈ E.dom,
      x + offO (List.replicate k Digit.three ++ [Digit.two]) 2 ≠
        y + offO (List.replicate k Digit.three ++ [Digit.two]) 5) := by
  have hd := pbc_three_even (k - 1) O E h
  have hd' : 2 * ((k - 1 : ℕ) : ℤ) + 3 = 2 * (k : ℤ) + 1 := by omega
  rw [hd, hd']
  exact vac_V1_pure k

/-! ### Tile bounds -/

theorem bnd_stairF (d : ℤ) (x : GInt) (hx : x ∈ stairF d) : 2 - d ≤ x.1 ∧ x.1 ≤ d ∧ 0 ≤ x.2 ∧ x.2 ≤ d + 1 := by
  simp only [stairF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hx
  omega

theorem bnd_ladderF (d : ℤ) (x : GInt) (hx : x ∈ ladderF d) : 2 - d ≤ x.1 ∧ x.1 ≤ 2 * d ∧ 0 ≤ x.2 ∧ x.2 ≤ d + 2 := by
  simp only [ladderF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hx
  omega

theorem bnd_nstairN (d : ℤ) (x : GInt) (hx : x ∈ nstairN d) :
    0 ≤ x.1 ∧ x.1 ≤ d + 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ 2 * d - 2 := by
  rw [mem_nstairN_iff] at hx
  simp only [nstairF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Prod.fst_add, Prod.snd_add] at hx
  omega

theorem bnd_nladderN (d : ℤ) (x : GInt) (hx : x ∈ nladderN d) :
    -1 ≤ x.1 ∧ x.1 ≤ d + 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ 3 * d - 2 := by
  rw [mem_nladderN_iff] at hx
  simp only [nladderF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Prod.fst_add, Prod.snd_add] at hx
  omega

/-! ### The base domains of the register words -/

theorem pbc_three_odd (m : ℕ) (hm : 1 ≤ m) (O E : PartialOdometer)
    (h : PaperBaseCond (List.replicate m Digit.three) O E) : O.dom = ladderF (2 * (m : ℤ) + 2) :=
  (h.2.1 m hm rfl).1

theorem pbc_two_odd_all (m : ℕ) (O E : PartialOdometer)
    (h : PaperBaseCond (List.replicate m Digit.two) O E) : O.dom = nstairN (2 * (m : ℤ) + 3) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · obtain ⟨hd, -, -, -⟩ := h.1 rfl
    rw [hd]
    norm_num
  · exact (h.2.2 m hm rfl).1

theorem pbc_two_even (m : ℕ) (hm : 1 ≤ m) (O E : PartialOdometer)
    (h : PaperBaseCond (List.replicate m Digit.two) O E) : E.dom = nladderN (2 * (m : ℤ) + 2) :=
  (h.2.2 m hm rfl).2.2.1

theorem pbc_empty_odd_even (O E : PartialOdometer) (h : PaperBaseCond [] O E) :
    O.dom = nstairN 3 ∧ E.dom = stairF 3 := by
  obtain ⟨hO, -, hE, -⟩ := h.1 rfl
  exact ⟨hO, hE⟩

/-! ### The family `V3`: the word `3^k · 1` (`k ≥ 1`), the register `3^k` on both sides -/

theorem parents_V3 (k : ℕ) :
    parentsAt (List.replicate k Digit.three ++ [Digit.one]) = ⟨⟨1, 2 * (k : ℤ) + 2⟩, ⟨1, 2 * (k : ℤ) + 3⟩⟩ := by
  rw [parentsAt_append_singleton, parents_three]
  simp [Parents.step, Parents.current, Parents.combine]
  all_goals (try constructor)
  all_goals ring

theorem phase_V3 (k : ℕ) : phase (List.replicate k Digit.three ++ [Digit.one]) = 1 := by
  simp [phase, List.count_append, List.count_replicate]

theorem offO_V3_0 (k : ℕ) : offO (List.replicate k Digit.three ++ [Digit.one]) 0 = (0, 0) := by
  unfold offO
  rw [if_pos (by norm_num)]
  unfold oddP
  rw [parents_V3, phase_V3]
  rfl

theorem offO_V3_1 (k : ℕ) :
    offO (List.replicate k Digit.three ++ [Digit.one]) 1 = (2 * (k : ℤ) + 4, 2 * (k : ℤ) + 6) := by
  unfold offO
  rw [if_pos (by norm_num)]
  unfold oddP
  rw [parents_V3, phase_V3]
  refine Prod.ext ?_ ?_
  all_goals simp [pOffsetsOdd, texV1Even, texV2]
  all_goals ring

theorem offO_V3_3 (k : ℕ) :
    offO (List.replicate k Digit.three ++ [Digit.one]) 3 = (6 * (k : ℤ) + 7, 3) := by
  unfold offO
  rw [if_neg (by norm_num)]
  unfold oddQ
  rw [parents_V3, phase_V3]
  refine Prod.ext ?_ ?_
  all_goals simp [qOffsetsOdd, texV1Even, texV1Odd, texV2]
  all_goals ring

theorem offO_V3_4 (k : ℕ) :
    offO (List.replicate k Digit.three ++ [Digit.one]) 4 = (-2 * (k : ℤ) - 1, 2 * (k : ℤ) + 3) := by
  unfold offO
  rw [if_neg (by norm_num)]
  unfold oddQ
  rw [parents_V3, phase_V3]
  refine Prod.ext ?_ ?_
  all_goals simp [qOffsetsOdd, texV1Even, texV1Odd, texV2]
  all_goals ring

theorem offE_V3_0 (k : ℕ) : offE (List.replicate k Digit.three ++ [Digit.one]) 0 = (0, 0) := by
  unfold offE
  rw [if_pos (by norm_num)]
  unfold evenP
  rw [parents_V3, phase_V3]
  rfl

theorem offE_V3_3 (k : ℕ) :
    offE (List.replicate k Digit.three ++ [Digit.one]) 3 = (-2 * (k : ℤ), 4 * (k : ℤ) + 8) := by
  unfold offE
  rw [if_pos (by norm_num)]
  unfold evenP
  rw [parents_V3, phase_V3]
  refine Prod.ext ?_ ?_
  all_goals simp [pOffsetsEven, texV1Even, texV2]
  all_goals ring

theorem offE_V3_4 (k : ℕ) :
    offE (List.replicate k Digit.three ++ [Digit.one]) 4 = (4 * (k : ℤ) + 4, 2) := by
  unfold offE
  rw [if_neg (by norm_num)]
  unfold evenQ
  rw [parents_V3, phase_V3]
  refine Prod.ext ?_ ?_
  all_goals simp [qOffsetsEven, texV1Odd]
  all_goals ring

theorem offE_V3_5 (k : ℕ) :
    offE (List.replicate k Digit.three ++ [Digit.one]) 5 = (-4 * (k : ℤ) - 2, 4 * (k : ℤ) + 6) := by
  unfold offE
  rw [if_neg (by norm_num)]
  unfold evenQ
  rw [parents_V3, phase_V3]
  refine Prod.ext ?_ ?_
  all_goals simp [qOffsetsEven, texV2]
  all_goals ring

/-- The four clauses of `V3` on the register `3^k` (odd `(0,1)`, `(3,4)`; even `(0,3)`, `(4,5)`). -/
theorem vac_V3 (k : ℕ) (hk : 1 ≤ k) (O E : PartialOdometer)
    (h : PaperBaseCond (List.replicate k Digit.three) O E) :
    (∀ x ∈ O.dom, ∀ y ∈ O.dom,
      x + offO (List.replicate k Digit.three ++ [Digit.one]) 0 ≠
        y + offO (List.replicate k Digit.three ++ [Digit.one]) 1) ∧
    (∀ x ∈ E.dom, ∀ y ∈ E.dom,
      x + offO (List.replicate k Digit.three ++ [Digit.one]) 3 ≠
        y + offO (List.replicate k Digit.three ++ [Digit.one]) 4) ∧
    (∀ x ∈ O.dom, ∀ y ∈ O.dom,
      x + offE (List.replicate k Digit.three ++ [Digit.one]) 0 ≠
        y + offE (List.replicate k Digit.three ++ [Digit.one]) 3) ∧
    (∀ x ∈ E.dom, ∀ y ∈ E.dom,
      x + offE (List.replicate k Digit.three ++ [Digit.one]) 4 ≠
        y + offE (List.replicate k Digit.three ++ [Digit.one]) 5) := by
  have hO := pbc_three_odd k hk O E h
  have hE := pbc_three_even k O E h
  rw [hO, hE]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx y hy heq
    rw [offO_V3_0, offO_V3_1] at heq
    have hx' := bnd_ladderF _ x hx
    have hy' := bnd_ladderF _ y hy
    simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add] at heq
    omega
  · intro x hx y hy heq
    rw [offO_V3_3, offO_V3_4] at heq
    have hx' := bnd_stairF _ x hx
    have hy' := bnd_stairF _ y hy
    simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add] at heq
    omega
  · intro x hx y hy heq
    rw [offE_V3_0, offE_V3_3] at heq
    have hx' := bnd_ladderF _ x hx
    have hy' := bnd_ladderF _ y hy
    simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add] at heq
    omega
  · intro x hx y hy heq
    rw [offE_V3_4, offE_V3_5] at heq
    have hx' := bnd_stairF _ x hx
    have hy' := bnd_stairF _ y hy
    simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add] at heq
    omega

/-! ### The family `V4`: the word `2^k · 1` (`k ≥ 1`), the register `2^k` on both sides -/

theorem parents_V4 (k : ℕ) :
    parentsAt (List.replicate k Digit.two ++ [Digit.one]) =
      ⟨⟨(k : ℤ) + 1, (k : ℤ) + 2⟩, ⟨2 * (k : ℤ) + 1, 2 * (k : ℤ) + 3⟩⟩ := by
  rw [parentsAt_append_singleton, parents_twos]
  simp [Parents.step, Parents.current, Parents.combine]
  all_goals (try constructor)
  all_goals (try trivial)

theorem phase_V4 (k : ℕ) : phase (List.replicate k Digit.two ++ [Digit.one]) = 1 := by
  simp [phase, List.count_append, List.count_replicate]

theorem offO_V4_0 (k : ℕ) : offO (List.replicate k Digit.two ++ [Digit.one]) 0 = (0, 0) := by
  unfold offO
  rw [if_pos (by norm_num)]
  unfold oddP
  rw [parents_V4, phase_V4]
  rfl

theorem offO_V4_1 (k : ℕ) :
    offO (List.replicate k Digit.two ++ [Digit.one]) 1 = (4 * (k : ℤ) + 4, 8 * (k : ℤ) + 6) := by
  unfold offO
  rw [if_pos (by norm_num)]
  unfold oddP
  rw [parents_V4, phase_V4]
  refine Prod.ext ?_ ?_
  all_goals simp [pOffsetsOdd, texV1Even, texV2]
  all_goals ring

theorem offO_V4_3 (k : ℕ) :
    offO (List.replicate k Digit.two ++ [Digit.one]) 3 = (4 * (k : ℤ) + 7, 4 * (k : ℤ) + 3) := by
  unfold offO
  rw [if_neg (by norm_num)]
  unfold oddQ
  rw [parents_V4, phase_V4]
  refine Prod.ext ?_ ?_
  all_goals simp [qOffsetsOdd, texV1Even, texV1Odd, texV2]
  all_goals ring

theorem offO_V4_4 (k : ℕ) :
    offO (List.replicate k Digit.two ++ [Digit.one]) 4 = (-1, 2 * (k : ℤ) + 3) := by
  unfold offO
  rw [if_neg (by norm_num)]
  unfold oddQ
  rw [parents_V4, phase_V4]
  refine Prod.ext ?_ ?_
  all_goals simp [qOffsetsOdd, texV1Even, texV1Odd, texV2]
  all_goals ring

theorem offE_V4_0 (k : ℕ) : offE (List.replicate k Digit.two ++ [Digit.one]) 0 = (0, 0) := by
  unfold offE
  rw [if_pos (by norm_num)]
  unfold evenP
  rw [parents_V4, phase_V4]
  rfl

theorem offE_V4_3 (k : ℕ) :
    offE (List.replicate k Digit.two ++ [Digit.one]) 3 = (2 * (k : ℤ), 8 * (k : ℤ) + 8) := by
  unfold offE
  rw [if_pos (by norm_num)]
  unfold evenP
  rw [parents_V4, phase_V4]
  refine Prod.ext ?_ ?_
  all_goals simp [pOffsetsEven, texV1Even, texV2]
  all_goals ring

theorem offE_V4_4 (k : ℕ) :
    offE (List.replicate k Digit.two ++ [Digit.one]) 4 = (2 * (k : ℤ) + 4, 2 * (k : ℤ) + 2) := by
  unfold offE
  rw [if_neg (by norm_num)]
  unfold evenQ
  rw [parents_V4, phase_V4]
  refine Prod.ext ?_ ?_
  all_goals simp [qOffsetsEven, texV1Odd]
  all_goals ring

theorem offE_V4_5 (k : ℕ) :
    offE (List.replicate k Digit.two ++ [Digit.one]) 5 = (-2, 4 * (k : ℤ) + 6) := by
  unfold offE
  rw [if_neg (by norm_num)]
  unfold evenQ
  rw [parents_V4, phase_V4]
  refine Prod.ext ?_ ?_
  all_goals simp [qOffsetsEven, texV2]
  all_goals ring

/-- The four clauses of `V4` on the register `2^k` (`O` the odd base odometer, `E` the even one). -/
theorem vac_V4 (k : ℕ) (hk : 1 ≤ k) (O E : PartialOdometer)
    (h : PaperBaseCond (List.replicate k Digit.two) O E) :
    (∀ x ∈ O.dom, ∀ y ∈ O.dom,
      x + offO (List.replicate k Digit.two ++ [Digit.one]) 0 ≠
        y + offO (List.replicate k Digit.two ++ [Digit.one]) 1) ∧
    (∀ x ∈ E.dom, ∀ y ∈ E.dom,
      x + offO (List.replicate k Digit.two ++ [Digit.one]) 3 ≠
        y + offO (List.replicate k Digit.two ++ [Digit.one]) 4) ∧
    (∀ x ∈ O.dom, ∀ y ∈ O.dom,
      x + offE (List.replicate k Digit.two ++ [Digit.one]) 0 ≠
        y + offE (List.replicate k Digit.two ++ [Digit.one]) 3) ∧
    (∀ x ∈ E.dom, ∀ y ∈ E.dom,
      x + offE (List.replicate k Digit.two ++ [Digit.one]) 4 ≠
        y + offE (List.replicate k Digit.two ++ [Digit.one]) 5) := by
  have hO := pbc_two_odd_all k O E h
  have hE := pbc_two_even k hk O E h
  rw [hO, hE]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx y hy heq
    rw [offO_V4_0, offO_V4_1] at heq
    have hx' := bnd_nstairN _ x hx
    have hy' := bnd_nstairN _ y hy
    simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add] at heq
    omega
  · intro x hx y hy heq
    rw [offO_V4_3, offO_V4_4] at heq
    have hx' := bnd_nladderN _ x hx
    have hy' := bnd_nladderN _ y hy
    simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add] at heq
    omega
  · intro x hx y hy heq
    rw [offE_V4_0, offE_V4_3] at heq
    have hx' := bnd_nstairN _ x hx
    have hy' := bnd_nstairN _ y hy
    simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add] at heq
    omega
  · intro x hx y hy heq
    rw [offE_V4_4, offE_V4_5] at heq
    have hx' := bnd_nladderN _ x hx
    have hy' := bnd_nladderN _ y hy
    simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add] at heq
    omega

/-! ### The family `V5`: the word `1` (the empty register on both sides) -/

theorem parents_V5 : parentsAt [Digit.one] = ⟨⟨1, 2⟩, ⟨1, 3⟩⟩ := by
  rfl

theorem phase_V5 : phase [Digit.one] = 1 := by
  simp [phase]

theorem offO_V5_0 : offO [Digit.one] 0 = (0, 0) := by
  unfold offO
  rw [if_pos (by norm_num)]
  unfold oddP
  rw [parents_V5, phase_V5]
  rfl

theorem offO_V5_1 : offO [Digit.one] 1 = (4, 6) := by
  unfold offO
  rw [if_pos (by norm_num)]
  unfold oddP
  rw [parents_V5, phase_V5]
  norm_num [pOffsetsOdd, texV1Even, texV2]

theorem offO_V5_3 : offO [Digit.one] 3 = (7, 3) := by
  unfold offO
  rw [if_neg (by norm_num)]
  unfold oddQ
  rw [parents_V5, phase_V5]
  norm_num [qOffsetsOdd, texV1Even, texV1Odd, texV2]

theorem offO_V5_4 : offO [Digit.one] 4 = (-1, 3) := by
  unfold offO
  rw [if_neg (by norm_num)]
  unfold oddQ
  rw [parents_V5, phase_V5]
  norm_num [qOffsetsOdd, texV1Odd, texV2]

theorem offE_V5_0 : offE [Digit.one] 0 = (0, 0) := by
  unfold offE
  rw [if_pos (by norm_num)]
  unfold evenP
  rw [parents_V5, phase_V5]
  rfl

theorem offE_V5_3 : offE [Digit.one] 3 = (0, 8) := by
  unfold offE
  rw [if_pos (by norm_num)]
  unfold evenP
  rw [parents_V5, phase_V5]
  norm_num [pOffsetsEven, texV1Even, texV2]

theorem offE_V5_4 : offE [Digit.one] 4 = (4, 2) := by
  unfold offE
  rw [if_neg (by norm_num)]
  unfold evenQ
  rw [parents_V5, phase_V5]
  norm_num [qOffsetsEven, texV1Odd]

theorem offE_V5_5 : offE [Digit.one] 5 = (-2, 6) := by
  unfold offE
  rw [if_neg (by norm_num)]
  unfold evenQ
  rw [parents_V5, phase_V5]
  norm_num [qOffsetsEven, texV2]

/-- The four clauses of `V5` on the empty register (`O` the odd base odometer, `E` the even one). -/
theorem vac_V5 (O E : PartialOdometer) (h : PaperBaseCond [] O E) :
    (∀ x ∈ O.dom, ∀ y ∈ O.dom,
      x + offO [Digit.one] 0 ≠ y + offO [Digit.one] 1) ∧
    (∀ x ∈ E.dom, ∀ y ∈ E.dom,
      x + offO [Digit.one] 3 ≠ y + offO [Digit.one] 4) ∧
    (∀ x ∈ O.dom, ∀ y ∈ O.dom,
      x + offE [Digit.one] 0 ≠ y + offE [Digit.one] 3) ∧
    (∀ x ∈ E.dom, ∀ y ∈ E.dom,
      x + offE [Digit.one] 4 ≠ y + offE [Digit.one] 5) := by
  obtain ⟨hO, hE⟩ := pbc_empty_odd_even O E h
  rw [hO, hE]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx y hy heq
    rw [offO_V5_0, offO_V5_1] at heq
    have hx' := bnd_nstairN _ x hx
    have hy' := bnd_nstairN _ y hy
    simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add] at heq
    omega
  · intro x hx y hy heq
    rw [offO_V5_3, offO_V5_4] at heq
    have hx' := bnd_stairF _ x hx
    have hy' := bnd_stairF _ y hy
    simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add] at heq
    omega
  · intro x hx y hy heq
    rw [offE_V5_0, offE_V5_3] at heq
    have hx' := bnd_nstairN _ x hx
    have hy' := bnd_nstairN _ y hy
    simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add] at heq
    omega
  · intro x hx y hy heq
    rw [offE_V5_4, offE_V5_5] at heq
    have hx' := bnd_stairF _ x hx
    have hy' := bnd_stairF _ y hy
    simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add] at heq
    omega

/-! ### The family `V6`: the word `2^(m+1) · 3`; pieces 0–3 of the even pieces use the odd tile of `2^m` -/

theorem parents_V6 (m : ℕ) :
    parentsAt (List.replicate (m + 1) Digit.two ++ [Digit.three]) =
      ⟨⟨(m : ℤ) + 1, (m : ℤ) + 2⟩, ⟨2 * (m : ℤ) + 3, 2 * (m : ℤ) + 5⟩⟩ := by
  rw [parentsAt_append_singleton, parents_twos]
  simp [Parents.step, Parents.current, Parents.combine]
  all_goals (try constructor)
  all_goals (try trivial)

theorem phase_V6 (m : ℕ) : phase (List.replicate (m + 1) Digit.two ++ [Digit.three]) = 0 := by
  simp [phase, List.count_append, List.count_replicate]

theorem offE_V6_0 (m : ℕ) :
    offE (List.replicate (m + 1) Digit.two ++ [Digit.three]) 0 = (2 * (m : ℤ) + 5, 2 * (m : ℤ) + 3) := by
  unfold offE
  rw [if_pos (by norm_num)]
  unfold evenP
  rw [parents_V6, phase_V6]
  refine Prod.ext ?_ ?_ <;> simp [pOffsetsEven, texV1Even, texV2]

theorem offE_V6_1 (m : ℕ) :
    offE (List.replicate (m + 1) Digit.two ++ [Digit.three]) 1 = (2 * (m : ℤ) + 4, 4 * (m : ℤ) + 6) := by
  unfold offE
  rw [if_pos (by norm_num)]
  unfold evenP
  rw [parents_V6, phase_V6]
  refine Prod.ext ?_ ?_
  all_goals simp [pOffsetsEven, texV1Even, texV2]
  all_goals ring

theorem offE_V6_2 (m : ℕ) :
    offE (List.replicate (m + 1) Digit.two ++ [Digit.three]) 2 = (-2, 4 * (m : ℤ) + 8) := by
  unfold offE
  rw [if_pos (by norm_num)]
  unfold evenP
  rw [parents_V6, phase_V6]
  refine Prod.ext ?_ ?_
  all_goals simp [pOffsetsEven, texV1Even, texV2]
  all_goals ring

theorem offE_V6_3 (m : ℕ) :
    offE (List.replicate (m + 1) Digit.two ++ [Digit.three]) 3 = (-3, 6 * (m : ℤ) + 11) := by
  unfold offE
  rw [if_pos (by norm_num)]
  unfold evenP
  rw [parents_V6, phase_V6]
  refine Prod.ext ?_ ?_
  all_goals simp [pOffsetsEven, texV1Even, texV2]
  all_goals ring

/-- The two clauses of `V6`: the pairs (0,3) and (1,2) of the even pieces, on the odd tile `O` of `2^m`. -/
theorem vac_V6 (m : ℕ) (O E : PartialOdometer) (h : PaperBaseCond (List.replicate m Digit.two) O E) :
    (∀ x ∈ O.dom, ∀ y ∈ O.dom,
      x + offE (List.replicate (m + 1) Digit.two ++ [Digit.three]) 0 ≠
        y + offE (List.replicate (m + 1) Digit.two ++ [Digit.three]) 3) ∧
    (∀ x ∈ O.dom, ∀ y ∈ O.dom,
      x + offE (List.replicate (m + 1) Digit.two ++ [Digit.three]) 1 ≠
        y + offE (List.replicate (m + 1) Digit.two ++ [Digit.three]) 2) := by
  rw [pbc_two_odd_all m O E h]
  refine ⟨?_, ?_⟩
  · intro x hx y hy heq
    rw [offE_V6_0 m, offE_V6_3 m] at heq
    have hx' := bnd_nstairN _ x hx
    have hy' := bnd_nstairN _ y hy
    simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add] at heq
    omega
  · intro x hx y hy heq
    rw [offE_V6_1 m, offE_V6_2 m] at heq
    have hx' := bnd_nstairN _ x hx
    have hy' := bnd_nstairN _ y hy
    simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add] at heq
    omega

end FLatticePaper.Tiles.SwapVacuity
