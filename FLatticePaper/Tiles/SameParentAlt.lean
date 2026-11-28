import FLatticePaper.Tiles.SameParentCopies
import FLatticePaper.Tiles.ClosedPathAlt

/-! Copies of one parent tile that are not a doubled pair, among the six standard copies of the decomposition of an alternate
child that is not corrected (the even alternate child after a `1` or a `2`, the odd one after a `1` or a `3`), do not meet.

The separation is that of `SameParentCopies`, with one more bound from the parents of the shorter word: the even parent of every
word has a positive numerator (`even_num_pos`), and after a `1` with `W_1` even the shorter word contains a `1`, so its even parent
is interior (`rel_one_qint`). The statements on the copies of `ClosedPathAlt` are `altEven_same_disjoint` and
`altOdd_same_disjoint`. -/

namespace FLatticePaper.Tiles.SameParentAlt

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
  FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.H3Bounds FLatticePaper.Tiles.H3Pairs
  FLatticePaper.Tiles.SameParentCopies
open FLatticePaper.Tiles.ClosedPathAlt (altEvenD altEvenR altOddD altOddR dAE dAO)
open FLatticePaper.Tiles.StandardClause (fracOdd fracEven)

theorem lam_neg' (n0 d0 : ℤ) (u : GInt) : lam n0 d0 (-u) = -lam n0 d0 u := by
  simp only [lam, Prod.fst_neg, Prod.snd_neg]
  ring

theorem sig_neg' (n0 d0 : ℤ) (u : GInt) : sig n0 d0 (-u) = -sig n0 d0 u := by
  simp only [sig, Prod.fst_neg, Prod.snd_neg]
  ring

/-- `sep_close` with negated vectors (the doubling shifts). -/
macro "sep_close'" : tactic => `(tactic| (simp only [mLP, mLQ, mSP, mSQ, lam_add, lam_sub, lam_neg', lam_zero, sig_add,
  sig_sub, sig_neg', sig_zero, Bool.false_eq_true, if_true, if_false, one_eq_neg_one_false, neg_one_eq_one_false]; linarith))

/-! ### The parents of the shorter word -/

theorem eq_snoc_of_getLast (w : Word) (d : Digit) (h : w.getLast? = some d) : w = w.dropLast ++ [d] := by
  induction w using List.reverseRecOn with
  | nil => simp at h
  | append_singleton v x _ =>
    simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.some.injEq] at h
    subst h
    simp

/-- The even parent of every word has a positive numerator. -/
theorem even_num_pos (w : Word) : 1 ≤ (parentsAt w).even.num := by
  induction w using List.reverseRecOn with
  | nil => simp [parentsAt, root, Parents.walk]
  | append_singleton v d ih =>
    have h0 := (parentsAt_valid v).odd_bounds.2.1
    rw [parentsAt_append_singleton]
    cases d <;> simp [Parents.step, Parents.current, Parents.combine] <;> omega

/-- After a `1`: the even parent of the shorter word has a positive numerator. -/
theorem rel_one_qnum (w : Word) (hw : ¬ IsBase w) (h : w.getLast? = some Digit.one) :
    2 * dM w ≤ 2 * lam (nM w) (dM w) (texV2 (parentsAt w).odd) - lam (nM w) (dM w) (texV2 (parentsAt w).even) := by
  have hs := parents_last w _ h
  obtain ⟨hc1, hc2⟩ := mediant_bounds w hw
  have hn := even_num_pos w.dropLast
  obtain ⟨hd, -, -⟩ := (parentsAt_valid w.dropLast).even_bounds
  have ho : (parentsAt w).odd = ⟨(parentsAt w.dropLast).odd.num + (parentsAt w.dropLast).even.num,
      (parentsAt w.dropLast).odd.den + (parentsAt w.dropLast).even.den⟩ := by
    rw [hs]; simp [Parents.step, Parents.current, Parents.combine]
  have he : (parentsAt w).even = ⟨2 * (parentsAt w.dropLast).odd.num + (parentsAt w.dropLast).even.num,
      2 * (parentsAt w.dropLast).odd.den + (parentsAt w.dropLast).even.den⟩ := by
    rw [hs]; simp [Parents.step, Parents.current, Parents.combine]
  rw [lam_texV2, lam_texV2, ho, he]
  have h1 := mul_le_mul_of_nonneg_left hn (show (0 : ℤ) ≤ dM w - nM w by omega)
  have h2 := mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ (parentsAt w.dropLast).even.den by omega)
    (show (0 : ℤ) ≤ dM w + nM w by omega)
  nlinarith [h1, h2]

/-- After a `1` with `W_1` even: the shorter word contains a `1`, so its even parent is interior. -/
theorem rel_one_qint (w : Word) (hw : ¬ IsBase w) (h : w.getLast? = some Digit.one) (hph : phase w ≠ 1) :
    3 * dM w + nM w ≤ 2 * lam (nM w) (dM w) (texV2 (parentsAt w).odd) - lam (nM w) (dM w) (texV2 (parentsAt w).even) := by
  have hs := parents_last w _ h
  obtain ⟨hc1, hc2⟩ := mediant_bounds w hw
  have hmem : Digit.one ∈ w.dropLast := by
    by_contra hn
    apply hph
    rw [eq_snoc_of_getLast w _ h]
    simp [phase, List.count_append, List.count_eq_zero_of_not_mem hn]
  obtain ⟨hn1, hd1⟩ := H3Data.even_parent_interior w.dropLast ⟨_, hmem, Or.inl rfl⟩
  have ho : (parentsAt w).odd = ⟨(parentsAt w.dropLast).odd.num + (parentsAt w.dropLast).even.num,
      (parentsAt w.dropLast).odd.den + (parentsAt w.dropLast).even.den⟩ := by
    rw [hs]; simp [Parents.step, Parents.current, Parents.combine]
  have he : (parentsAt w).even = ⟨2 * (parentsAt w.dropLast).odd.num + (parentsAt w.dropLast).even.num,
      2 * (parentsAt w.dropLast).odd.den + (parentsAt w.dropLast).even.den⟩ := by
    rw [hs]; simp [Parents.step, Parents.current, Parents.combine]
  rw [lam_texV2, lam_texV2, ho, he]
  have h1 := mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ (parentsAt w.dropLast).even.num by omega)
    (show (0 : ℤ) ≤ dM w - nM w by omega)
  have h2 := mul_le_mul_of_nonneg_left (show (2 : ℤ) ≤ (parentsAt w.dropLast).even.den by omega)
    (show (0 : ℤ) ≤ dM w + nM w by omega)
  nlinarith [h1, h2]

/-- After a `2`: the even parent is that of the shorter word, with a positive numerator. -/
theorem rel_two_qnum (w : Word) (hw : ¬ IsBase w) (h : w.getLast? = some Digit.two) :
    2 * dM w ≤ lam (nM w) (dM w) (texV2 (parentsAt w).even) := by
  have hs := parents_last w _ h
  obtain ⟨hc1, hc2⟩ := mediant_bounds w hw
  have hn := even_num_pos w.dropLast
  obtain ⟨hd, -, -⟩ := (parentsAt_valid w.dropLast).even_bounds
  have he : (parentsAt w).even = (parentsAt w.dropLast).even := by
    rw [hs]; simp [Parents.step]
  rw [lam_texV2, he]
  have h1 := mul_le_mul_of_nonneg_left hn (show (0 : ℤ) ≤ dM w - nM w by omega)
  have h2 := mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ (parentsAt w.dropLast).even.den by omega)
    (show (0 : ℤ) ≤ dM w + nM w by omega)
  nlinarith [h1, h2]

/-! ### The pairs -/

/-- Copies `0` and `2` of the even alternate child after a `1`, `W_1` odd. -/
theorem ae02_one_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.one) (hph : phase w = 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (altEvenD w).getD 0 0 ∈ evenTile U)
    (hb : z - (altEvenD w).getD 2 0 ∈ evenTile U) : False := by
  obtain ⟨hD, -, -, -⟩ := ClosedPathAlt.altEven_of w hph
  rw [hD] at ha hb
  simp only [List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_one w hw hd
  have r3 := rel_one_qnum w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepQ_sig w hw U hU (fun A => ?_) hb ha
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `0` and `2` of the even alternate child after a `1`, `W_1` even. -/
theorem ae02_one_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.one) (hph : phase w ≠ 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (altEvenD w).getD 0 0 ∈ evenTile U)
    (hb : z - (altEvenD w).getD 2 0 ∈ evenTile U) : False := by
  obtain ⟨hD, -, -, -⟩ := ClosedPathAlt.altEven_ef w hph
  rw [hD] at ha hb
  simp only [List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_one w hw hd
  have r3 := rel_one_qint w hw hd hph
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepQ_sig w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `0` and `2` of the even alternate child after a `2`, `W_1` odd. -/
theorem ae02_two_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.two) (hph : phase w = 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (altEvenD w).getD 0 0 ∈ evenTile U)
    (hb : z - (altEvenD w).getD 2 0 ∈ evenTile U) : False := by
  obtain ⟨hD, -, -, -⟩ := ClosedPathAlt.altEven_of w hph
  rw [hD] at ha hb
  simp only [List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_two w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepQ_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `0` and `2` of the even alternate child after a `2`, `W_1` even. -/
theorem ae02_two_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.two) (hph : phase w ≠ 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (altEvenD w).getD 0 0 ∈ evenTile U)
    (hb : z - (altEvenD w).getD 2 0 ∈ evenTile U) : False := by
  obtain ⟨hD, -, -, -⟩ := ClosedPathAlt.altEven_ef w hph
  rw [hD] at ha hb
  simp only [List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_two w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepQ_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `0` and `3` of the even alternate child after a `1`, `W_1` odd. -/
theorem ae03_one_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.one) (hph : phase w = 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (altEvenD w).getD 0 0 ∈ evenTile U)
    (hb : z - (altEvenD w).getD 3 0 ∈ evenTile U) : False := by
  obtain ⟨hD, -, -, hsh⟩ := ClosedPathAlt.altEven_of w hph
  rw [hD] at ha hb
  simp only [List.getD_cons_succ, List.getD_cons_zero, hsh] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_one w hw hd
  have r3 := rel_one_qnum w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepQ_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `0` and `3` of the even alternate child after a `1`, `W_1` even. -/
theorem ae03_one_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.one) (hph : phase w ≠ 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (altEvenD w).getD 0 0 ∈ evenTile U)
    (hb : z - (altEvenD w).getD 3 0 ∈ evenTile U) : False := by
  obtain ⟨hD, -, -, hsh⟩ := ClosedPathAlt.altEven_ef w hph
  rw [hD] at ha hb
  simp only [List.getD_cons_succ, List.getD_cons_zero, hsh] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_one w hw hd
  have r3 := rel_one_qint w hw hd hph
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepQ_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `0` and `3` of the even alternate child after a `2`, `W_1` odd. -/
theorem ae03_two_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.two) (hph : phase w = 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (altEvenD w).getD 0 0 ∈ evenTile U)
    (hb : z - (altEvenD w).getD 3 0 ∈ evenTile U) : False := by
  obtain ⟨hD, -, -, hsh⟩ := ClosedPathAlt.altEven_of w hph
  rw [hD] at ha hb
  simp only [List.getD_cons_succ, List.getD_cons_zero, hsh] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_two w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepQ_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `0` and `3` of the even alternate child after a `2`, `W_1` even. -/
theorem ae03_two_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.two) (hph : phase w ≠ 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (altEvenD w).getD 0 0 ∈ evenTile U)
    (hb : z - (altEvenD w).getD 3 0 ∈ evenTile U) : False := by
  obtain ⟨hD, -, -, hsh⟩ := ClosedPathAlt.altEven_ef w hph
  rw [hD] at ha hb
  simp only [List.getD_cons_succ, List.getD_cons_zero, hsh] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_two w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepQ_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `1` and `2` of the even alternate child after a `1`, `W_1` odd. -/
theorem ae12_one_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.one) (hph : phase w = 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (altEvenD w).getD 1 0 ∈ evenTile U)
    (hb : z - (altEvenD w).getD 2 0 ∈ evenTile U) : False := by
  obtain ⟨hD, -, -, hsh⟩ := ClosedPathAlt.altEven_of w hph
  rw [hD] at ha hb
  simp only [List.getD_cons_succ, List.getD_cons_zero, hsh] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_one w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepQ_sig w hw U hU (fun A => ?_) hb ha
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `1` and `2` of the even alternate child after a `1`, `W_1` even. -/
theorem ae12_one_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.one) (hph : phase w ≠ 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (altEvenD w).getD 1 0 ∈ evenTile U)
    (hb : z - (altEvenD w).getD 2 0 ∈ evenTile U) : False := by
  obtain ⟨hD, -, -, hsh⟩ := ClosedPathAlt.altEven_ef w hph
  rw [hD] at ha hb
  simp only [List.getD_cons_succ, List.getD_cons_zero, hsh] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_one w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepQ_sig w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `1` and `2` of the even alternate child after a `2`, `W_1` odd. -/
theorem ae12_two_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.two) (hph : phase w = 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (altEvenD w).getD 1 0 ∈ evenTile U)
    (hb : z - (altEvenD w).getD 2 0 ∈ evenTile U) : False := by
  obtain ⟨hD, -, -, hsh⟩ := ClosedPathAlt.altEven_of w hph
  rw [hD] at ha hb
  simp only [List.getD_cons_succ, List.getD_cons_zero, hsh] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_two w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepQ_sig w hw U hU (fun A => ?_) hb ha
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `1` and `2` of the even alternate child after a `2`, `W_1` even. -/
theorem ae12_two_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.two) (hph : phase w ≠ 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (altEvenD w).getD 1 0 ∈ evenTile U)
    (hb : z - (altEvenD w).getD 2 0 ∈ evenTile U) : False := by
  obtain ⟨hD, -, -, hsh⟩ := ClosedPathAlt.altEven_ef w hph
  rw [hD] at ha hb
  simp only [List.getD_cons_succ, List.getD_cons_zero, hsh] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_two w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepQ_sig w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `1` and `3` of the even alternate child after a `1`, `W_1` odd. -/
theorem ae13_one_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.one) (hph : phase w = 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (altEvenD w).getD 1 0 ∈ evenTile U)
    (hb : z - (altEvenD w).getD 3 0 ∈ evenTile U) : False := by
  obtain ⟨hD, -, -, hsh⟩ := ClosedPathAlt.altEven_of w hph
  rw [hD] at ha hb
  simp only [List.getD_cons_succ, List.getD_cons_zero, hsh] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_one w hw hd
  have r3 := rel_one_qnum w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepQ_sig w hw U hU (fun A => ?_) hb ha
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `1` and `3` of the even alternate child after a `1`, `W_1` even. -/
theorem ae13_one_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.one) (hph : phase w ≠ 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (altEvenD w).getD 1 0 ∈ evenTile U)
    (hb : z - (altEvenD w).getD 3 0 ∈ evenTile U) : False := by
  obtain ⟨hD, -, -, hsh⟩ := ClosedPathAlt.altEven_ef w hph
  rw [hD] at ha hb
  simp only [List.getD_cons_succ, List.getD_cons_zero, hsh] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_one w hw hd
  have r3 := rel_one_qint w hw hd hph
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepQ_sig w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `1` and `3` of the even alternate child after a `2`, `W_1` odd. -/
theorem ae13_two_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.two) (hph : phase w = 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (altEvenD w).getD 1 0 ∈ evenTile U)
    (hb : z - (altEvenD w).getD 3 0 ∈ evenTile U) : False := by
  obtain ⟨hD, -, -, hsh⟩ := ClosedPathAlt.altEven_of w hph
  rw [hD] at ha hb
  simp only [List.getD_cons_succ, List.getD_cons_zero, hsh] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_two w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepQ_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `1` and `3` of the even alternate child after a `2`, `W_1` even. -/
theorem ae13_two_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.two) (hph : phase w ≠ 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (altEvenD w).getD 1 0 ∈ evenTile U)
    (hb : z - (altEvenD w).getD 3 0 ∈ evenTile U) : False := by
  obtain ⟨hD, -, -, hsh⟩ := ClosedPathAlt.altEven_ef w hph
  rw [hD] at ha hb
  simp only [List.getD_cons_succ, List.getD_cons_zero, hsh] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_two w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepQ_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `4` and `5` of the even alternate child after a `1`, `W_1` odd. -/
theorem ae45_one_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.one) (hph : phase w = 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (altEvenR w).getD 0 0 ∈ oddTile U)
    (hb : z - (altEvenR w).getD 1 0 ∈ oddTile U) : False := by
  obtain ⟨-, hD, -, -⟩ := ClosedPathAlt.altEven_of w hph
  rw [hD] at ha hb
  simp only [List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_one w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepP_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `4` and `5` of the even alternate child after a `1`, `W_1` even. -/
theorem ae45_one_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.one) (hph : phase w ≠ 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (altEvenR w).getD 0 0 ∈ oddTile U)
    (hb : z - (altEvenR w).getD 1 0 ∈ oddTile U) : False := by
  obtain ⟨-, hD, -, -⟩ := ClosedPathAlt.altEven_ef w hph
  rw [hD] at ha hb
  simp only [List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_one w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepP_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `4` and `5` of the even alternate child after a `2`, `W_1` odd. -/
theorem ae45_two_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.two) (hph : phase w = 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (altEvenR w).getD 0 0 ∈ oddTile U)
    (hb : z - (altEvenR w).getD 1 0 ∈ oddTile U) : False := by
  obtain ⟨-, hD, -, -⟩ := ClosedPathAlt.altEven_of w hph
  rw [hD] at ha hb
  simp only [List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_two w hw hd
  have r3 := rel_two_qnum w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepP_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `4` and `5` of the even alternate child after a `2`, `W_1` even. -/
theorem ae45_two_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.two) (hph : phase w ≠ 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (altEvenR w).getD 0 0 ∈ oddTile U)
    (hb : z - (altEvenR w).getD 1 0 ∈ oddTile U) : False := by
  obtain ⟨-, hD, -, -⟩ := ClosedPathAlt.altEven_ef w hph
  rw [hD] at ha hb
  simp only [List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_two w hw hd
  have r3 := rel_two_qnum w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepP_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `0` and `2` of the odd alternate child after a `1`, `W_1` odd. -/
theorem ao02_one_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.one) (hph : phase w = 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (altOddD w).getD 0 0 ∈ oddTile U)
    (hb : z - (altOddD w).getD 2 0 ∈ oddTile U) : False := by
  obtain ⟨hD, -, -, -⟩ := ClosedPathAlt.altOdd_of w hph
  rw [hD] at ha hb
  simp only [List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_one w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepP_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `0` and `2` of the odd alternate child after a `1`, `W_1` even. -/
theorem ao02_one_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.one) (hph : phase w ≠ 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (altOddD w).getD 0 0 ∈ oddTile U)
    (hb : z - (altOddD w).getD 2 0 ∈ oddTile U) : False := by
  obtain ⟨hD, -, -, -⟩ := ClosedPathAlt.altOdd_ef w hph
  rw [hD] at ha hb
  simp only [List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_one w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepP_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `0` and `2` of the odd alternate child after a `3`, `W_1` odd. -/
theorem ao02_three_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.three) (hph : phase w = 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (altOddD w).getD 0 0 ∈ oddTile U)
    (hb : z - (altOddD w).getD 2 0 ∈ oddTile U) : False := by
  obtain ⟨hD, -, -, -⟩ := ClosedPathAlt.altOdd_of w hph
  rw [hD] at ha hb
  simp only [List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_three w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepP_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `0` and `2` of the odd alternate child after a `3`, `W_1` even. -/
theorem ao02_three_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.three) (hph : phase w ≠ 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (altOddD w).getD 0 0 ∈ oddTile U)
    (hb : z - (altOddD w).getD 2 0 ∈ oddTile U) : False := by
  obtain ⟨hD, -, -, -⟩ := ClosedPathAlt.altOdd_ef w hph
  rw [hD] at ha hb
  simp only [List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_three w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepP_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `0` and `3` of the odd alternate child after a `1`, `W_1` odd. -/
theorem ao03_one_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.one) (hph : phase w = 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (altOddD w).getD 0 0 ∈ oddTile U)
    (hb : z - (altOddD w).getD 3 0 ∈ oddTile U) : False := by
  obtain ⟨hD, -, -, hsh⟩ := ClosedPathAlt.altOdd_of w hph
  rw [hD] at ha hb
  simp only [List.getD_cons_succ, List.getD_cons_zero, hsh] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_one w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepP_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `0` and `3` of the odd alternate child after a `1`, `W_1` even. -/
theorem ao03_one_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.one) (hph : phase w ≠ 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (altOddD w).getD 0 0 ∈ oddTile U)
    (hb : z - (altOddD w).getD 3 0 ∈ oddTile U) : False := by
  obtain ⟨hD, -, -, hsh⟩ := ClosedPathAlt.altOdd_ef w hph
  rw [hD] at ha hb
  simp only [List.getD_cons_succ, List.getD_cons_zero, hsh] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_one w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepP_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `0` and `3` of the odd alternate child after a `3`, `W_1` odd. -/
theorem ao03_three_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.three) (hph : phase w = 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (altOddD w).getD 0 0 ∈ oddTile U)
    (hb : z - (altOddD w).getD 3 0 ∈ oddTile U) : False := by
  obtain ⟨hD, -, -, hsh⟩ := ClosedPathAlt.altOdd_of w hph
  rw [hD] at ha hb
  simp only [List.getD_cons_succ, List.getD_cons_zero, hsh] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_three w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepP_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `0` and `3` of the odd alternate child after a `3`, `W_1` even. -/
theorem ao03_three_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.three) (hph : phase w ≠ 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (altOddD w).getD 0 0 ∈ oddTile U)
    (hb : z - (altOddD w).getD 3 0 ∈ oddTile U) : False := by
  obtain ⟨hD, -, -, hsh⟩ := ClosedPathAlt.altOdd_ef w hph
  rw [hD] at ha hb
  simp only [List.getD_cons_succ, List.getD_cons_zero, hsh] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_three w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepP_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `1` and `2` of the odd alternate child after a `1`, `W_1` odd. -/
theorem ao12_one_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.one) (hph : phase w = 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (altOddD w).getD 1 0 ∈ oddTile U)
    (hb : z - (altOddD w).getD 2 0 ∈ oddTile U) : False := by
  obtain ⟨hD, -, -, hsh⟩ := ClosedPathAlt.altOdd_of w hph
  rw [hD] at ha hb
  simp only [List.getD_cons_succ, List.getD_cons_zero, hsh] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_one w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepP_sig w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `1` and `2` of the odd alternate child after a `1`, `W_1` even. -/
theorem ao12_one_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.one) (hph : phase w ≠ 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (altOddD w).getD 1 0 ∈ oddTile U)
    (hb : z - (altOddD w).getD 2 0 ∈ oddTile U) : False := by
  obtain ⟨hD, -, -, hsh⟩ := ClosedPathAlt.altOdd_ef w hph
  rw [hD] at ha hb
  simp only [List.getD_cons_succ, List.getD_cons_zero, hsh] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_one w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepP_sig w hw U hU (fun A => ?_) hb ha
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `1` and `2` of the odd alternate child after a `3`, `W_1` odd. -/
theorem ao12_three_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.three) (hph : phase w = 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (altOddD w).getD 1 0 ∈ oddTile U)
    (hb : z - (altOddD w).getD 2 0 ∈ oddTile U) : False := by
  obtain ⟨hD, -, -, hsh⟩ := ClosedPathAlt.altOdd_of w hph
  rw [hD] at ha hb
  simp only [List.getD_cons_succ, List.getD_cons_zero, hsh] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_three w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepP_sig w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `1` and `2` of the odd alternate child after a `3`, `W_1` even. -/
theorem ao12_three_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.three) (hph : phase w ≠ 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (altOddD w).getD 1 0 ∈ oddTile U)
    (hb : z - (altOddD w).getD 2 0 ∈ oddTile U) : False := by
  obtain ⟨hD, -, -, hsh⟩ := ClosedPathAlt.altOdd_ef w hph
  rw [hD] at ha hb
  simp only [List.getD_cons_succ, List.getD_cons_zero, hsh] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_three w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepP_sig w hw U hU (fun A => ?_) hb ha
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `1` and `3` of the odd alternate child after a `1`, `W_1` odd. -/
theorem ao13_one_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.one) (hph : phase w = 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (altOddD w).getD 1 0 ∈ oddTile U)
    (hb : z - (altOddD w).getD 3 0 ∈ oddTile U) : False := by
  obtain ⟨hD, -, -, hsh⟩ := ClosedPathAlt.altOdd_of w hph
  rw [hD] at ha hb
  simp only [List.getD_cons_succ, List.getD_cons_zero, hsh] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_one w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepP_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `1` and `3` of the odd alternate child after a `1`, `W_1` even. -/
theorem ao13_one_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.one) (hph : phase w ≠ 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (altOddD w).getD 1 0 ∈ oddTile U)
    (hb : z - (altOddD w).getD 3 0 ∈ oddTile U) : False := by
  obtain ⟨hD, -, -, hsh⟩ := ClosedPathAlt.altOdd_ef w hph
  rw [hD] at ha hb
  simp only [List.getD_cons_succ, List.getD_cons_zero, hsh] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_one w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepP_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `1` and `3` of the odd alternate child after a `3`, `W_1` odd. -/
theorem ao13_three_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.three) (hph : phase w = 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (altOddD w).getD 1 0 ∈ oddTile U)
    (hb : z - (altOddD w).getD 3 0 ∈ oddTile U) : False := by
  obtain ⟨hD, -, -, hsh⟩ := ClosedPathAlt.altOdd_of w hph
  rw [hD] at ha hb
  simp only [List.getD_cons_succ, List.getD_cons_zero, hsh] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_three w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepP_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `1` and `3` of the odd alternate child after a `3`, `W_1` even. -/
theorem ao13_three_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.three) (hph : phase w ≠ 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (altOddD w).getD 1 0 ∈ oddTile U)
    (hb : z - (altOddD w).getD 3 0 ∈ oddTile U) : False := by
  obtain ⟨hD, -, -, hsh⟩ := ClosedPathAlt.altOdd_ef w hph
  rw [hD] at ha hb
  simp only [List.getD_cons_succ, List.getD_cons_zero, hsh] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_three w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepP_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `4` and `5` of the odd alternate child after a `1`, `W_1` odd. -/
theorem ao45_one_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.one) (hph : phase w = 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (altOddR w).getD 0 0 ∈ evenTile U)
    (hb : z - (altOddR w).getD 1 0 ∈ evenTile U) : False := by
  obtain ⟨-, hD, -, -⟩ := ClosedPathAlt.altOdd_of w hph
  rw [hD] at ha hb
  simp only [List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_one w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepQ_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `4` and `5` of the odd alternate child after a `1`, `W_1` even. -/
theorem ao45_one_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.one) (hph : phase w ≠ 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (altOddR w).getD 0 0 ∈ evenTile U)
    (hb : z - (altOddR w).getD 1 0 ∈ evenTile U) : False := by
  obtain ⟨-, hD, -, -⟩ := ClosedPathAlt.altOdd_ef w hph
  rw [hD] at ha hb
  simp only [List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_one w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepQ_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `4` and `5` of the odd alternate child after a `3`, `W_1` odd. -/
theorem ao45_three_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.three) (hph : phase w = 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (altOddR w).getD 0 0 ∈ evenTile U)
    (hb : z - (altOddR w).getD 1 0 ∈ evenTile U) : False := by
  obtain ⟨-, hD, -, -⟩ := ClosedPathAlt.altOdd_of w hph
  rw [hD] at ha hb
  simp only [List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_three w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepQ_sig w hw U hU (fun A => ?_) hb ha
  cases A <;> simp only [hE] <;> sep_close'

/-- Copies `4` and `5` of the odd alternate child after a `3`, `W_1` even. -/
theorem ao45_three_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.three) (hph : phase w ≠ 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (altOddR w).getD 0 0 ∈ evenTile U)
    (hb : z - (altOddR w).getD 1 0 ∈ evenTile U) : False := by
  obtain ⟨-, hD, -, -⟩ := ClosedPathAlt.altOdd_ef w hph
  rw [hD] at ha hb
  simp only [List.getD_cons_succ, List.getD_cons_zero] at ha hb
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_three w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepQ_sig w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close'

/-- The copies of `ClosedPathAlt` of the even alternate child, as differences in the parent tiles. -/
theorem dAE_sub (w u1 u2 : Word) {z : ℤ × ℤ} {k : ℕ} (h : z ∈ dAE w u1 u2 k) :
    (k < 4 → z - (altEvenD w).getD k 0 ∈ evenTile u2) ∧ (4 ≤ k → z - (altEvenR w).getD (k - 4) 0 ∈ oddTile u1) := by
  have hl : (altEvenD w).length = 4 := rfl
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · simp only [dAE, ChildGlue.pieceSet, hl, if_pos hk] at h
    exact Finset.mem_coe.1 (ClosedPathAssembly.sub_mem_of_shift _ _ _ h)
  · simp only [dAE, ChildGlue.pieceSet, hl, if_neg (show ¬ k < 4 by omega)] at h
    exact Finset.mem_coe.1 (ClosedPathAssembly.sub_mem_of_shift _ _ _ h)

theorem even_same_lt (w u1 u2 : Word) (hw : ¬ IsBase w) (hp : (parentsAt w).odd = fracOdd u1)
    (hq : (parentsAt w).even = fracEven u2) (hd : w.getLast? ≠ some Digit.three) (i j : ℕ) (hij : i < j) (hj : j < 6)
    (hsame : (i < 4 ↔ j < 4)) (hnd : ¬ ((i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 3))) (z : ℤ × ℤ) (h1 : z ∈ dAE w u1 u2 i)
    (h2 : z ∈ dAE w u1 u2 j) : False := by
  have hU1 : curO u1 = (parentsAt w).odd := hp.symm
  have hU2 : curE u2 = (parentsAt w).even := hq.symm
  obtain ⟨a1, b1⟩ := dAE_sub w u1 u2 h1
  obtain ⟨a2, b2⟩ := dAE_sub w u1 u2 h2
  have hne : w.getLast? ≠ none := by
    intro h
    exact hw (Or.inl (List.getLast?_eq_none_iff.1 h))
  obtain ⟨dg, hdg⟩ := Option.ne_none_iff_exists'.mp hne
  cases dg
  · by_cases hph : phase w = 1
    · interval_cases j <;> interval_cases i
      · simp at hnd
      · exact ae02_one_of w hw hdg hph u2 hU2 (a1 (by omega)) (a2 (by omega))
      · exact ae12_one_of w hw hdg hph u2 hU2 (a1 (by omega)) (a2 (by omega))
      · exact ae03_one_of w hw hdg hph u2 hU2 (a1 (by omega)) (a2 (by omega))
      · exact ae13_one_of w hw hdg hph u2 hU2 (a1 (by omega)) (a2 (by omega))
      · simp at hnd
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · exact ae45_one_of w hw hdg hph u1 hU1 (b1 (by omega)) (b2 (by omega))
    · interval_cases j <;> interval_cases i
      · simp at hnd
      · exact ae02_one_ef w hw hdg hph u2 hU2 (a1 (by omega)) (a2 (by omega))
      · exact ae12_one_ef w hw hdg hph u2 hU2 (a1 (by omega)) (a2 (by omega))
      · exact ae03_one_ef w hw hdg hph u2 hU2 (a1 (by omega)) (a2 (by omega))
      · exact ae13_one_ef w hw hdg hph u2 hU2 (a1 (by omega)) (a2 (by omega))
      · simp at hnd
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · exact ae45_one_ef w hw hdg hph u1 hU1 (b1 (by omega)) (b2 (by omega))
  · by_cases hph : phase w = 1
    · interval_cases j <;> interval_cases i
      · simp at hnd
      · exact ae02_two_of w hw hdg hph u2 hU2 (a1 (by omega)) (a2 (by omega))
      · exact ae12_two_of w hw hdg hph u2 hU2 (a1 (by omega)) (a2 (by omega))
      · exact ae03_two_of w hw hdg hph u2 hU2 (a1 (by omega)) (a2 (by omega))
      · exact ae13_two_of w hw hdg hph u2 hU2 (a1 (by omega)) (a2 (by omega))
      · simp at hnd
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · exact ae45_two_of w hw hdg hph u1 hU1 (b1 (by omega)) (b2 (by omega))
    · interval_cases j <;> interval_cases i
      · simp at hnd
      · exact ae02_two_ef w hw hdg hph u2 hU2 (a1 (by omega)) (a2 (by omega))
      · exact ae12_two_ef w hw hdg hph u2 hU2 (a1 (by omega)) (a2 (by omega))
      · exact ae03_two_ef w hw hdg hph u2 hU2 (a1 (by omega)) (a2 (by omega))
      · exact ae13_two_ef w hw hdg hph u2 hU2 (a1 (by omega)) (a2 (by omega))
      · simp at hnd
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · exact ae45_two_ef w hw hdg hph u1 hU1 (b1 (by omega)) (b2 (by omega))
  · exact absurd hdg hd

/-- **Same-parent copies of the even alternate child that are not a doubled pair do not meet**, at every non-base word whose
even alternate child is not corrected. -/
theorem altEven_same_disjoint (w u1 u2 : Word) (hw : ¬ IsBase w) (hp : (parentsAt w).odd = fracOdd u1)
    (hq : (parentsAt w).even = fracEven u2) (hd : w.getLast? ≠ some Digit.three) (i j : ℕ) (hi : i < 6) (hj : j < 6)
    (hij : i ≠ j) (hsame : (i < 4 ↔ j < 4)) (hnd : ¬ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)))
    (z : ℤ × ℤ) (h1 : z ∈ dAE w u1 u2 i) (h2 : z ∈ dAE w u1 u2 j) : False := by
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact even_same_lt w u1 u2 hw hp hq hd i j h hj hsame (by tauto) z h1 h2
  · exact even_same_lt w u1 u2 hw hp hq hd j i h hi hsame.symm (by tauto) z h2 h1

/-- The copies of `ClosedPathAlt` of the odd alternate child, as differences in the parent tiles. -/
theorem dAO_sub (w u1 u2 : Word) {z : ℤ × ℤ} {k : ℕ} (h : z ∈ dAO w u1 u2 k) :
    (k < 4 → z - (altOddD w).getD k 0 ∈ oddTile u1) ∧ (4 ≤ k → z - (altOddR w).getD (k - 4) 0 ∈ evenTile u2) := by
  have hl : (altOddD w).length = 4 := rfl
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · simp only [dAO, ChildGlue.pieceSet, hl, if_pos hk] at h
    exact Finset.mem_coe.1 (ClosedPathAssembly.sub_mem_of_shift _ _ _ h)
  · simp only [dAO, ChildGlue.pieceSet, hl, if_neg (show ¬ k < 4 by omega)] at h
    exact Finset.mem_coe.1 (ClosedPathAssembly.sub_mem_of_shift _ _ _ h)

theorem odd_same_lt (w u1 u2 : Word) (hw : ¬ IsBase w) (hp : (parentsAt w).odd = fracOdd u1)
    (hq : (parentsAt w).even = fracEven u2) (hd : w.getLast? ≠ some Digit.two) (i j : ℕ) (hij : i < j) (hj : j < 6)
    (hsame : (i < 4 ↔ j < 4)) (hnd : ¬ ((i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 3))) (z : ℤ × ℤ) (h1 : z ∈ dAO w u1 u2 i)
    (h2 : z ∈ dAO w u1 u2 j) : False := by
  have hU1 : curO u1 = (parentsAt w).odd := hp.symm
  have hU2 : curE u2 = (parentsAt w).even := hq.symm
  obtain ⟨a1, b1⟩ := dAO_sub w u1 u2 h1
  obtain ⟨a2, b2⟩ := dAO_sub w u1 u2 h2
  have hne : w.getLast? ≠ none := by
    intro h
    exact hw (Or.inl (List.getLast?_eq_none_iff.1 h))
  obtain ⟨dg, hdg⟩ := Option.ne_none_iff_exists'.mp hne
  cases dg
  · by_cases hph : phase w = 1
    · interval_cases j <;> interval_cases i
      · simp at hnd
      · exact ao02_one_of w hw hdg hph u1 hU1 (a1 (by omega)) (a2 (by omega))
      · exact ao12_one_of w hw hdg hph u1 hU1 (a1 (by omega)) (a2 (by omega))
      · exact ao03_one_of w hw hdg hph u1 hU1 (a1 (by omega)) (a2 (by omega))
      · exact ao13_one_of w hw hdg hph u1 hU1 (a1 (by omega)) (a2 (by omega))
      · simp at hnd
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · exact ao45_one_of w hw hdg hph u2 hU2 (b1 (by omega)) (b2 (by omega))
    · interval_cases j <;> interval_cases i
      · simp at hnd
      · exact ao02_one_ef w hw hdg hph u1 hU1 (a1 (by omega)) (a2 (by omega))
      · exact ao12_one_ef w hw hdg hph u1 hU1 (a1 (by omega)) (a2 (by omega))
      · exact ao03_one_ef w hw hdg hph u1 hU1 (a1 (by omega)) (a2 (by omega))
      · exact ao13_one_ef w hw hdg hph u1 hU1 (a1 (by omega)) (a2 (by omega))
      · simp at hnd
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · exact ao45_one_ef w hw hdg hph u2 hU2 (b1 (by omega)) (b2 (by omega))
  · exact absurd hdg hd
  · by_cases hph : phase w = 1
    · interval_cases j <;> interval_cases i
      · simp at hnd
      · exact ao02_three_of w hw hdg hph u1 hU1 (a1 (by omega)) (a2 (by omega))
      · exact ao12_three_of w hw hdg hph u1 hU1 (a1 (by omega)) (a2 (by omega))
      · exact ao03_three_of w hw hdg hph u1 hU1 (a1 (by omega)) (a2 (by omega))
      · exact ao13_three_of w hw hdg hph u1 hU1 (a1 (by omega)) (a2 (by omega))
      · simp at hnd
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · exact ao45_three_of w hw hdg hph u2 hU2 (b1 (by omega)) (b2 (by omega))
    · interval_cases j <;> interval_cases i
      · simp at hnd
      · exact ao02_three_ef w hw hdg hph u1 hU1 (a1 (by omega)) (a2 (by omega))
      · exact ao12_three_ef w hw hdg hph u1 hU1 (a1 (by omega)) (a2 (by omega))
      · exact ao03_three_ef w hw hdg hph u1 hU1 (a1 (by omega)) (a2 (by omega))
      · exact ao13_three_ef w hw hdg hph u1 hU1 (a1 (by omega)) (a2 (by omega))
      · simp at hnd
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · simp at hsame
      · exact ao45_three_ef w hw hdg hph u2 hU2 (b1 (by omega)) (b2 (by omega))

/-- **Same-parent copies of the odd alternate child that are not a doubled pair do not meet**, at every non-base word whose
odd alternate child is not corrected. -/
theorem altOdd_same_disjoint (w u1 u2 : Word) (hw : ¬ IsBase w) (hp : (parentsAt w).odd = fracOdd u1)
    (hq : (parentsAt w).even = fracEven u2) (hd : w.getLast? ≠ some Digit.two) (i j : ℕ) (hi : i < 6) (hj : j < 6)
    (hij : i ≠ j) (hsame : (i < 4 ↔ j < 4)) (hnd : ¬ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)))
    (z : ℤ × ℤ) (h1 : z ∈ dAO w u1 u2 i) (h2 : z ∈ dAO w u1 u2 j) : False := by
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact odd_same_lt w u1 u2 hw hp hq hd i j h hj hsame (by tauto) z h1 h2
  · exact odd_same_lt w u1 u2 hw hp hq hd j i h hi hsame.symm (by tauto) z h2 h1

end FLatticePaper.Tiles.SameParentAlt
