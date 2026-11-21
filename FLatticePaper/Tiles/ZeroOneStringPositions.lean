import FLatticePaper.Tiles.ZeroOneSentence

/-! The positions of the zero-one families are the offsets of the string (task 16): `stringPositions` of
`ZeroOneOdometers` is the `posF` of the letter sequence, and the first sentence of the lemma holds for every word. -/

namespace FLatticePaper.Tiles

/-- The offsets of a zero-one string, as in `stringPositions`. -/
def stringOffsets (o : Orientation) (rev : Bool) (ls : BinaryWord) : List Site :=
  if rev then
    List.zipWith (fun a l => match o with
      | .horizontal => zeroOneHorizontalReversedStep a l
      | .vertical => zeroOneVerticalReversedStep a l) ls ls.tail
  else
    ls.tail.map (fun l => match o with
      | .horizontal => zeroOneHorizontalStep l
      | .vertical => zeroOneVerticalStep l)

theorem stringPositions_eq (o : Orientation) (rev : Bool) (L : BinaryWord) :
    stringPositions o rev L = List.scanl (· + ·) 0 (stringOffsets o rev L) := rfl

theorem stringOffsets_length (o : Orientation) (rev : Bool) (L : BinaryWord) :
    (stringOffsets o rev L).length = L.length - 1 := by
  unfold stringOffsets
  cases rev <;> simp [List.length_zipWith, List.length_tail]

theorem stringOffsets_getD (o : Orientation) (rev : Bool) (L : BinaryWord) (j : ℕ) (hj : j + 1 < L.length) :
    (stringOffsets o rev L).getD j 0 = stepOf o rev (L.getD j .p) (L.getD (j + 1) .p) := by
  have hj' : j < (stringOffsets o rev L).length := by rw [stringOffsets_length]; omega
  have h0 : L.getD j Letter.p = L[j]'(by omega) := List.getD_eq_getElem _ _ (by omega)
  have h1 : L.getD (j + 1) Letter.p = L[j + 1]'hj := List.getD_eq_getElem _ _ hj
  rw [List.getD_eq_getElem _ _ hj', h0, h1]
  unfold stringOffsets
  cases o <;> cases rev <;> simp [stepOf, List.getElem_map, List.getElem_tail, List.getElem_zipWith]

theorem scanl_getD_eq (off : List Site) (a : Site) :
    ∀ k ≤ off.length, (List.scanl (· + ·) a off).getD k 0 = a + (off.take k).sum := by
  induction off generalizing a with
  | nil =>
    intro k hk
    have : k = 0 := by simpa using hk
    subst this
    simp
  | cons x off ih =>
    intro k hk
    cases k with
    | zero => simp
    | succ k =>
      simp only [List.scanl_cons, List.getD_cons_succ, List.take_succ_cons, List.sum_cons]
      rw [ih (a + x) k (by simp at hk; omega)]
      abel

theorem posF_eq_take_sum (o : Orientation) (rev : Bool) (L : BinaryWord) :
    ∀ k, k + 1 ≤ L.length →
      ((stringOffsets o rev L).take k).sum = posF o rev (fun j => L.getD j .p) k := by
  intro k
  induction k with
  | zero => intro _; simp [posF]
  | succ k ih =>
    intro hk
    have hlt : k < (stringOffsets o rev L).length := by rw [stringOffsets_length]; omega
    rw [List.sum_take_succ _ _ hlt, ih (by omega)]
    have hg := stringOffsets_getD o rev L k (by omega)
    have hget : (stringOffsets o rev L)[k] = stepOf o rev (L.getD k .p) (L.getD (k + 1) .p) := by
      rw [← hg, List.getD_eq_getElem _ _ hlt]
    rw [hget]
    rfl

theorem stringPositions_eq_posF (o : Orientation) (rev : Bool) (L : BinaryWord) (k : ℕ) (hk : k < L.length) :
    (stringPositions o rev L).getD k 0 = posF o rev (fun j => L.getD j .p) k := by
  rw [stringPositions_eq, scanl_getD_eq _ _ k (by rw [stringOffsets_length]; omega), zero_add,
    posF_eq_take_sum o rev L k hk]

/-- `lemma:stacked_zero_one_string`, first sentence, for every binary word: a zero-one family respecting the
horizontal (vertical) string of the word and of its reversal, with offset zero on overlaps. -/
theorem zeroOneFirstSentence_all (o : Orientation) (rev : Bool) (w : BinaryWord) :
    ZeroOneFirstSentence o rev w := by
  obtain ⟨h1, h2⟩ := familyF_checks o rev (lettersOf w rev) (if rev then w.reverse else w).length
  exact ⟨familyF o rev (lettersOf w rev) (if rev then w.reverse else w).length, rfl,
    fun k _ => rfl, fun k hk => (stringPositions_eq_posF o rev _ k hk).symm, h1, h2⟩

end FLatticePaper.Tiles
