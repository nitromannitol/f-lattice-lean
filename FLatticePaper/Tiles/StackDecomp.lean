import FLatticePaper.Tiles.StackTruth
import FLatticePaper.Tiles.StackedStringConnected

/-! The stacked site set of an almost palindrome is the local union of its first `n - 1` letters, plus the last plus tile
and one final minus tile. The minus family runs over the reversed word; its positions are the plus positions of the
word shifted by the palindrome identity, tile by tile. -/

namespace FLatticePaper.Tiles

/-- The letters of a word, as a function (`p` beyond its end). -/
def wℓ (w : BinaryWord) : ℕ → Letter := fun i => w.getD i Letter.p

theorem wℓ_eq (w : BinaryWord) (k : ℕ) (hk : k < w.length) : wℓ w k = w[k] := by
  unfold wℓ
  rw [List.getD_eq_getElem _ _ hk]

/-- A scan of a list records the prefix sums. -/
theorem scanl_getD_take (a : Site) (xs : List Site) :
    ∀ (d : Site) (k : ℕ), k ≤ xs.length → (List.scanl (· + ·) a xs).getD k d = a + (xs.take k).sum := by
  induction xs generalizing a with
  | nil =>
    intro d k hk
    have : k = 0 := by simpa using hk
    subst this
    simp
  | cons x xs ih =>
    intro d k hk
    cases k with
    | zero => simp
    | succ k =>
      rw [List.scanl_cons, List.getD_cons_succ, ih (a + x) d k (by simp at hk; omega)]
      simp only [List.take_succ_cons, List.sum_cons]
      abel

theorem stringPositions_plus (o : Orientation) (w : BinaryWord) :
    stringPositions o false w = List.scanl (· + ·) 0 (w.tail.map (plusStepO o)) := by
  cases o <;> rfl

/-- The prefix sums of the plus steps are the plus positions of the local union. -/
theorem take_sum_plus (o : Orientation) (w : BinaryWord) :
    ∀ k, k + 1 ≤ w.length → ((w.tail.map (plusStepO o)).take k).sum = posO o (wℓ w) k := by
  intro k
  induction k with
  | zero =>
    intro _
    simp only [List.take_zero, List.sum_nil, posO]
    rfl
  | succ k ih =>
    intro hk
    have hlen : k < (w.tail.map (plusStepO o)).length := by
      simp only [List.length_map, List.length_tail]
      omega
    rw [List.sum_take_succ _ _ hlen, ih (by omega), posO_succ]
    congr 1
    rw [List.getElem_map, List.getElem_tail, wℓ_eq w (k + 1) (by omega)]

/-- The plus positions of the stacked string, read at an index. -/
theorem plus_position_eq (o : Orientation) (w : BinaryWord) (k : ℕ) (hk : k < w.length) :
    (stringPositions o false w).getD k 0 = posO o (wℓ w) k := by
  rw [stringPositions_plus, scanl_getD_take 0 _ 0 k (by simp; omega), zero_add,
    take_sum_plus o w k (by omega)]

/-! ### The minus family -/

/-- The offset of the reversed family between two consecutive letters of the reversed word. -/
def revStepO : Orientation → Letter → Letter → Site
  | .horizontal, a, b => zeroOneHorizontalReversedStep a b
  | .vertical, a, b => zeroOneVerticalReversedStep a b

theorem stringPositions_rev (o : Orientation) (w : BinaryWord) :
    stringPositions o true w = List.scanl (· + ·) 0 (List.zipWith (revStepO o) w w.tail) := by
  cases o <;> rfl

/-- The position of the minus tile of index `j` in the word of length `n` (the prefix sums of the reversed steps). -/
def Qf (o : Orientation) (ℓ : ℕ → Letter) (n : ℕ) (j : ℕ) : Site :=
  ((List.range j).map (fun i => revStepO o (ℓ (n - 1 - i)) (ℓ (n - 2 - i)))).sum

theorem Qf_zero (o : Orientation) (ℓ : ℕ → Letter) (n : ℕ) : Qf o ℓ n 0 = 0 := by
  simp [Qf]

theorem Qf_succ (o : Orientation) (ℓ : ℕ → Letter) (n j : ℕ) :
    Qf o ℓ n (j + 1) = Qf o ℓ n j + revStepO o (ℓ (n - 1 - j)) (ℓ (n - 2 - j)) := by
  unfold Qf
  rw [List.range_succ, List.map_append, List.sum_append]
  simp

/-- The reversed word reads the letters of `w` backwards. -/
theorem rev_getElem_eq (w : BinaryWord) (i : ℕ) (hi : i < w.length) (hr : i < w.reverse.length) :
    w.reverse[i] = wℓ w (w.length - 1 - i) := by
  rw [List.getElem_reverse, wℓ_eq w _ (by omega)]

theorem take_sum_rev (o : Orientation) (w : BinaryWord) :
    ∀ k, k ≤ w.length - 1 → ((List.zipWith (revStepO o) w.reverse w.reverse.tail).take k).sum =
      Qf o (wℓ w) w.length k := by
  intro k
  induction k with
  | zero =>
    intro _
    simp [Qf]
  | succ k ih =>
    intro hk
    have hlen : k < (List.zipWith (revStepO o) w.reverse w.reverse.tail).length := by
      simp only [List.length_zipWith, List.length_reverse, List.length_tail]
      omega
    rw [List.sum_take_succ _ _ hlen, ih (by omega), Qf_succ]
    congr 1
    have h1 : k < w.reverse.length := by simp; omega
    have h2 : k + 1 < w.reverse.length := by simp; omega
    rw [List.getElem_zipWith, List.getElem_tail, rev_getElem_eq w k (by omega) h1,
      rev_getElem_eq w (k + 1) (by omega) h2]
    rw [show w.length - 1 - (k + 1) = w.length - 2 - k from by omega]

/-- The minus positions: the reversed family's offsets at index `j`. -/
theorem minus_position_eq (o : Orientation) (w : BinaryWord) (j : ℕ) (hj : j < w.length) :
    (stringPositions o true w.reverse).getD j 0 = Qf o (wℓ w) w.length j := by
  rw [stringPositions_rev, scanl_getD_take 0 _ 0 j (by simp; omega), zero_add,
    take_sum_rev o w j (by omega)]

/-- The enlargement flag of the plus family at index `k + 1`. -/
theorem enlarged_succ (o : Orientation) (L : BinaryWord) (k : ℕ) (hk : k + 1 < L.length) :
    (enlargedFlags o L).getD (k + 1) false =
      (decide (o = Orientation.horizontal) && decide (L.getD k Letter.p = Letter.q) &&
        decide (L.getD (k + 1) Letter.p = Letter.q)) := by
  have h1 : k < L.length := by omega
  have h2 : k + 1 < L.length := hk
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2]
  unfold enlargedFlags
  rw [List.getD_cons_succ, List.getD_eq_getElem?_getD, List.getElem?_zipWith]
  simp [List.getElem?_tail, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2]

end FLatticePaper.Tiles
