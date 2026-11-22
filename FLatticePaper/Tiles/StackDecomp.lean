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


/-! ### The palindrome identities -/

/-- The offset of a shadow relative to the minus family shift. -/
def ccO (o : Orientation) (l : Letter) : Site := shadowO o l - familyShift o

theorem ccO_add_shift (o : Orientation) (l : Letter) : ccO o l + familyShift o = shadowO o l := by
  unfold ccO
  exact sub_add_cancel _ _

/-- The consecutive-letter identity behind the palindrome: a reversed step and a plus step differ by the offsets. -/
theorem key_identity (o : Orientation) (a b : Letter) :
    revStepO o a b + ccO o a = plusStepO o b + ccO o b := by
  cases o <;> cases a <;> cases b <;> decide

/-- The palindrome in the middle of an almost palindrome, as an identity of letters. -/
theorem almost_pal_index (w : BinaryWord) (hA : IsAlmostPalindrome w) (i : ℕ) (h1 : 1 ≤ i)
    (h2 : i ≤ w.length - 2) : wℓ w (w.length - 1 - i) = wℓ w i := by
  obtain ⟨f, l, mid, hmid, rfl⟩ := hA
  have hkey : ∀ t (ht : t < mid.length), mid[t] = mid[mid.length - 1 - t]'(by omega) := by
    intro t ht
    have h3 := List.getElem_reverse (l := mid) (i := t) (by simpa using ht)
    simp only [hmid] at h3
    exact h3
  have hget : ∀ t (ht : t < mid.length), wℓ (f :: (mid ++ [l])) (t + 1) = mid[t] := by
    intro t ht
    unfold wℓ
    rw [List.getD_cons_succ, List.getD_append _ _ _ _ (by simpa using ht), List.getD_eq_getElem _ _ ht]
  have hlen : (f :: (mid ++ [l])).length = mid.length + 2 := by
    simp only [List.length_cons, List.length_append, List.length_nil]
  rw [hlen] at h2 ⊢
  obtain ⟨s, rfl⟩ : ∃ s, i = s + 1 := ⟨i - 1, by omega⟩
  have e1 : mid.length + 2 - 1 - (s + 1) = (mid.length - (s + 1)) + 1 := by omega
  rw [e1, hget _ (by omega), hget s (by omega), hkey s (by omega)]
  congr 1
  omega

theorem Qf_mid (o : Orientation) (ℓ : ℕ → Letter) (n : ℕ)
    (hpal : ∀ i, 1 ≤ i → i ≤ n - 2 → ℓ (n - 1 - i) = ℓ i) (hlast : ccO o (ℓ (n - 1)) = 0) :
    ∀ j, 1 ≤ j → j ≤ n - 2 → Qf o ℓ n j = posO o ℓ j + ccO o (ℓ j) := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    intro _
    have h1 : ℓ (n - 2) = ℓ 1 := by
      have := hpal 1 le_rfl (by omega)
      rwa [show n - 1 - 1 = n - 2 from by omega] at this
    have hq1 : Qf o ℓ n 1 = revStepO o (ℓ (n - 1)) (ℓ (n - 2)) := by
      have := Qf_succ o ℓ n 0
      simpa [Qf_zero] using this
    have hp1 : posO o ℓ 1 = plusStepO o (ℓ 1) := by
      simp [posO]
    rw [hq1, hp1, h1]
    have hk := key_identity o (ℓ (n - 1)) (ℓ 1)
    rw [hlast, add_zero] at hk
    exact hk
  | succ j hj ih =>
    intro hjn
    rw [Qf_succ, ih (by omega), posO_succ]
    have a1 := hpal j hj (by omega)
    have a2 : ℓ (n - 2 - j) = ℓ (j + 1) := by
      have := hpal (j + 1) (by omega) (by omega)
      rwa [show n - 1 - (j + 1) = n - 2 - j from by omega] at this
    rw [a1, a2]
    have hk := key_identity o (ℓ j) (ℓ (j + 1))
    calc posO o ℓ j + ccO o (ℓ j) + revStepO o (ℓ j) (ℓ (j + 1))
        = posO o ℓ j + (revStepO o (ℓ j) (ℓ (j + 1)) + ccO o (ℓ j)) := by abel
      _ = posO o ℓ j + (plusStepO o (ℓ (j + 1)) + ccO o (ℓ (j + 1))) := by rw [hk]
      _ = posO o ℓ j + plusStepO o (ℓ (j + 1)) + ccO o (ℓ (j + 1)) := by abel

theorem Qf_last (o : Orientation) (ℓ : ℕ → Letter) (n : ℕ) (hn : 3 ≤ n)
    (hpal : ∀ i, 1 ≤ i → i ≤ n - 2 → ℓ (n - 1 - i) = ℓ i) (hlast : ccO o (ℓ (n - 1)) = 0) :
    Qf o ℓ n (n - 1) = posO o ℓ (n - 1) + (plusStepO o (ℓ 0) + ccO o (ℓ 0) - plusStepO o (ℓ (n - 1))) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hA : Qf o ℓ (m + 3) (m + 2) = Qf o ℓ (m + 3) (m + 1) + revStepO o (ℓ (m + 3 - 1 - (m + 1)))
      (ℓ (m + 3 - 2 - (m + 1))) := Qf_succ o ℓ (m + 3) (m + 1)
  have e1 : m + 3 - 1 - (m + 1) = 1 := by omega
  have e0 : m + 3 - 2 - (m + 1) = 0 := by omega
  have eL : m + 3 - 1 = m + 2 := by omega
  rw [e1, e0] at hA
  have hm1 : ℓ (m + 1) = ℓ 1 := by
    have := hpal 1 le_rfl (by omega)
    rwa [show m + 3 - 1 - 1 = m + 1 from by omega] at this
  have hQ := Qf_mid o ℓ (m + 3) hpal hlast (m + 1) (by omega) (by omega)
  have hk := key_identity o (ℓ 1) (ℓ 0)
  have hP : posO o ℓ (m + 2) = posO o ℓ (m + 1) + plusStepO o (ℓ (m + 2)) := posO_succ o ℓ (m + 1)
  show Qf o ℓ (m + 3) (m + 2) = posO o ℓ (m + 2) + _
  rw [hA, hQ, hm1, eL, hP]
  calc posO o ℓ (m + 1) + ccO o (ℓ 1) + revStepO o (ℓ 1) (ℓ 0)
      = posO o ℓ (m + 1) + (revStepO o (ℓ 1) (ℓ 0) + ccO o (ℓ 1)) := by abel
    _ = posO o ℓ (m + 1) + (plusStepO o (ℓ 0) + ccO o (ℓ 0)) := by rw [hk]
    _ = posO o ℓ (m + 1) + plusStepO o (ℓ (m + 2)) + (plusStepO o (ℓ 0) + ccO o (ℓ 0) - plusStepO o (ℓ (m + 2))) := by
      abel



/-! ### Membership in the stacked sites, index by index -/

theorem len_enlarged (o : Orientation) (L : BinaryWord) (hL : L ≠ []) :
    (enlargedFlags o L).length = L.length := by
  have h1 : 1 ≤ L.length := List.length_pos_iff.2 hL
  unfold enlargedFlags
  simp only [List.length_cons, List.length_zipWith, List.length_tail]
  omega

theorem len_stringPos (o : Orientation) (rev : Bool) (L : BinaryWord) (hL : L ≠ []) :
    (stringPositions o rev L).length = L.length := by
  have h1 : 1 ≤ L.length := List.length_pos_iff.2 hL
  unfold stringPositions
  cases rev <;> simp only [Bool.false_eq_true, if_false, if_true, List.length_scanl,
    List.length_map, List.length_tail, List.length_zipWith] <;> omega

theorem mem_familySites (o : Orientation) (rev : Bool) (L : BinaryWord) (hL : L ≠ []) (shift x : Site) :
    x ∈ familySites o rev L shift ↔ ∃ k, k < L.length ∧
      x ∈ pieceAt (L.getD k Letter.p) ((enlargedFlags o L).getD k false)
        ((stringPositions o rev L).getD k 0 + shift) := by
  have hF := len_enlarged o L hL
  have hP := len_stringPos o rev L hL
  unfold familySites
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨t, ht, hx⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 ht
    have hkL : k < L.length := by
      simp only [List.length_zip, hF, hP] at hk
      omega
    simp only [List.getElem_zip] at hx
    rw [List.mem_map] at hx
    obtain ⟨c, hc, hcx⟩ := hx
    refine ⟨k, hkL, ?_⟩
    have e1 : L.getD k Letter.p = L[k] := List.getD_eq_getElem _ _ hkL
    have e2 : (enlargedFlags o L).getD k false = (enlargedFlags o L)[k]'(by omega) :=
      List.getD_eq_getElem _ _ (by omega)
    have e3 : (stringPositions o rev L).getD k 0 = (stringPositions o rev L)[k]'(by omega) :=
      List.getD_eq_getElem _ _ (by omega)
    rw [mem_pieceAt, e1, e2, e3]
    refine ⟨c, hc, ?_⟩
    rw [← hcx]
    exact Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring)
  · rintro ⟨k, hk, hx⟩
    rw [mem_pieceAt] at hx
    obtain ⟨c, hc, hcx⟩ := hx
    have e1 : L.getD k Letter.p = L[k] := List.getD_eq_getElem _ _ hk
    have e2 : (enlargedFlags o L).getD k false = (enlargedFlags o L)[k]'(by omega) :=
      List.getD_eq_getElem _ _ (by omega)
    have e3 : (stringPositions o rev L).getD k 0 = (stringPositions o rev L)[k]'(by omega) :=
      List.getD_eq_getElem _ _ (by omega)
    rw [e1, e2] at hc
    rw [e3] at hcx
    refine ⟨(L[k], ((enlargedFlags o L)[k]'(by omega), (stringPositions o rev L)[k]'(by omega))), ?_, ?_⟩
    · apply List.mem_iff_getElem.2
      refine ⟨k, ?_, ?_⟩
      · simp only [List.length_zip, hF, hP]
        omega
      · simp only [List.getElem_zip]
    · rw [List.mem_map]
      refine ⟨c, hc, ?_⟩
      rw [← hcx]
      exact Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring)

theorem mem_stackedSites (o : Orientation) (w : BinaryWord) (hw : w ≠ []) (x : Site) :
    x ∈ stackedSites o w ↔
      (∃ k, k < w.length ∧ x ∈ pieceAt (w.getD k Letter.p) ((enlargedFlags o w).getD k false)
          ((stringPositions o false w).getD k 0 + (0, 0))) ∨
      (∃ j, j < w.length ∧ x ∈ pieceAt (w.reverse.getD j Letter.p) ((enlargedFlags o w.reverse).getD j false)
          ((stringPositions o true w.reverse).getD j 0 + familyShift o)) := by
  have hr : w.reverse ≠ [] := by simpa using hw
  unfold stackedSites
  rw [List.mem_toFinset, List.mem_append, mem_familySites o false w hw, mem_familySites o true w.reverse hr]
  simp only [List.length_reverse]

/-- The reversed word reads the letters of `w` backwards. -/
theorem reverse_getD_letter (w : BinaryWord) (j : ℕ) (hj : j < w.length) :
    w.reverse.getD j Letter.p = wℓ w (w.length - 1 - j) := by
  unfold wℓ
  rw [List.getD_eq_getElem _ _ (by simp; omega),
    List.getD_eq_getElem _ _ (show w.length - 1 - j < w.length by omega), List.getElem_reverse]

/-- The flag of the minus tile of index `j`. -/
def flagR (o : Orientation) (ℓ : ℕ → Letter) (n : ℕ) : ℕ → Bool
  | 0 => false
  | j + 1 => decide (o = Orientation.horizontal) && decide (ℓ (n - 1 - j) = Letter.q) &&
      decide (ℓ (n - 1 - (j + 1)) = Letter.q)

/-- The plus tile of index `k` of the stacked string, as the local union has it. -/
def plusPc (o : Orientation) (w : BinaryWord) (k : ℕ) : Finset Site :=
  pieceAt (wℓ w k) (flagO o (wℓ w) k) (posO o (wℓ w) k)

/-- The minus tile of index `j` of the stacked string. -/
def minusPc (o : Orientation) (w : BinaryWord) (j : ℕ) : Finset Site :=
  pieceAt (wℓ w (w.length - 1 - j)) (flagR o (wℓ w) w.length j) (Qf o (wℓ w) w.length j + familyShift o)

theorem plus_index (o : Orientation) (w : BinaryWord) (k : ℕ) (hk : k < w.length) :
    pieceAt (w.getD k Letter.p) ((enlargedFlags o w).getD k false)
        ((stringPositions o false w).getD k 0 + (0, 0)) = plusPc o w k := by
  unfold plusPc
  rw [plus_position_eq o w k hk]
  simp only [Prod.mk_zero_zero, add_zero]
  cases k with
  | zero => rfl
  | succ k' =>
    rw [enlarged_succ o w k' hk]
    rfl

theorem minus_index (o : Orientation) (w : BinaryWord) (j : ℕ) (hj : j < w.length) :
    pieceAt (w.reverse.getD j Letter.p) ((enlargedFlags o w.reverse).getD j false)
        ((stringPositions o true w.reverse).getD j 0 + familyShift o) = minusPc o w j := by
  unfold minusPc
  rw [minus_position_eq o w j hj, reverse_getD_letter w j hj]
  cases j with
  | zero => rfl
  | succ j' =>
    have hlt : j' + 1 < w.reverse.length := by simp; omega
    rw [enlarged_succ o w.reverse j' hlt, reverse_getD_letter w j' (by omega),
      reverse_getD_letter w (j' + 1) hj]
    rfl



/-! ### The decomposition -/

theorem stacked_eq_PM (o : Orientation) (w : BinaryWord) (hw : w ≠ []) :
    stackedSites o w = (Finset.range w.length).biUnion (plusPc o w) ∪
      (Finset.range w.length).biUnion (minusPc o w) := by
  ext x
  rw [mem_stackedSites o w hw x, Finset.mem_union, Finset.mem_biUnion, Finset.mem_biUnion]
  constructor
  · rintro (⟨k, hk, hx⟩ | ⟨j, hj, hx⟩)
    · rw [plus_index o w k hk] at hx
      exact Or.inl ⟨k, Finset.mem_range.2 hk, hx⟩
    · rw [minus_index o w j hj] at hx
      exact Or.inr ⟨j, Finset.mem_range.2 hj, hx⟩
  · rintro (⟨k, hk, hx⟩ | ⟨j, hj, hx⟩)
    · have hk' := Finset.mem_range.1 hk
      rw [← plus_index o w k hk'] at hx
      exact Or.inl ⟨k, hk', hx⟩
    · have hj' := Finset.mem_range.1 hj
      rw [← minus_index o w j hj'] at hx
      exact Or.inr ⟨j, hj', hx⟩

theorem minusPc_zero (o : Orientation) (w : BinaryWord) (hm0 : m0Piece o = pieceAt (wℓ w (w.length - 1)) false (familyShift o)) :
    minusPc o w 0 = m0Piece o := by
  unfold minusPc
  rw [Qf_zero, zero_add, Nat.sub_zero, hm0]
  rfl

theorem minusPc_one (o : Orientation) (w : BinaryWord) (hn : 3 ≤ w.length)
    (hpal : ∀ i, 1 ≤ i → i ≤ w.length - 2 → wℓ w (w.length - 1 - i) = wℓ w i)
    (hlast : ccO o (wℓ w (w.length - 1)) = 0) (hf1 : flagR o (wℓ w) w.length 1 = false) :
    minusPc o w 1 = pieceAt (wℓ w 1) false (posO o (wℓ w) 1 + shadowO o (wℓ w 1)) := by
  unfold minusPc
  rw [hf1, Qf_mid o (wℓ w) w.length hpal hlast 1 le_rfl (by omega), add_assoc, ccO_add_shift]
  rw [hpal 1 le_rfl (by omega)]

theorem minusPc_mid (o : Orientation) (w : BinaryWord) (hn : 3 ≤ w.length)
    (hpal : ∀ i, 1 ≤ i → i ≤ w.length - 2 → wℓ w (w.length - 1 - i) = wℓ w i)
    (hlast : ccO o (wℓ w (w.length - 1)) = 0) (j : ℕ) (h2 : 2 ≤ j) (hj : j ≤ w.length - 2) :
    minusPc o w j = pieceAt (wℓ w j) (flagO o (wℓ w) j) (posO o (wℓ w) j + shadowO o (wℓ w j)) := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hl1 := hpal j' (by omega) (by omega)
  have hl2 := hpal (j' + 1) (by omega) hj
  have hf : flagR o (wℓ w) w.length (j' + 1) = flagO o (wℓ w) (j' + 1) := by
    simp only [flagR, flagO]
    rw [hl1, hl2]
  unfold minusPc
  rw [hf, hl2, Qf_mid o (wℓ w) w.length hpal hlast (j' + 1) (by omega) hj, add_assoc, ccO_add_shift]

theorem minusPc_last (o : Orientation) (w : BinaryWord) (hn : 3 ≤ w.length)
    (hpal : ∀ i, 1 ≤ i → i ≤ w.length - 2 → wℓ w (w.length - 1 - i) = wℓ w i)
    (hlast : ccO o (wℓ w (w.length - 1)) = 0) :
    minusPc o w (w.length - 1) = pieceAt (wℓ w 0) (decide (o = Orientation.horizontal) &&
      decide (wℓ w 1 = Letter.q) && decide (wℓ w 0 = Letter.q))
      (posO o (wℓ w) (w.length - 1) + (plusStepO o (wℓ w 0) + ccO o (wℓ w 0) -
        plusStepO o (wℓ w (w.length - 1)) + familyShift o)) := by
  unfold minusPc
  have hf : flagR o (wℓ w) w.length (w.length - 1) = (decide (o = Orientation.horizontal) &&
      decide (wℓ w 1 = Letter.q) && decide (wℓ w 0 = Letter.q)) := by
    have e : w.length - 1 = (w.length - 2) + 1 := by omega
    rw [e]
    simp only [flagR]
    rw [show w.length - 1 - (w.length - 2) = 1 by omega, show w.length - 1 - ((w.length - 2) + 1) = 0 by omega]
  rw [hf, Nat.sub_self, Qf_last o (wℓ w) w.length hn hpal hlast, add_assoc]

theorem plusPc_last (o : Orientation) (w : BinaryWord) (hflag : flagO o (wℓ w) (w.length - 1) = false) :
    plusPc o w (w.length - 1) = pieceAt (wℓ w (w.length - 1)) false (posO o (wℓ w) (w.length - 1)) := by
  unfold plusPc
  rw [hflag]


/-- The stacked sites of an almost palindrome: the local union of its first `n - 1` letters, the last plus tile and
the last minus tile. -/
theorem stacked_decomp (o : Orientation) (w : BinaryWord) (hn : 3 ≤ w.length)
    (hpal : ∀ i, 1 ≤ i → i ≤ w.length - 2 → wℓ w (w.length - 1 - i) = wℓ w i)
    (hlast : ccO o (wℓ w (w.length - 1)) = 0)
    (hm0 : m0Piece o = pieceAt (wℓ w (w.length - 1)) false (familyShift o))
    (hf1 : flagR o (wℓ w) w.length 1 = false)
    (hPn : flagO o (wℓ w) (w.length - 1) = false) :
    stackedSites o w = lamO o (wℓ w) (w.length - 1) ∪
      pieceAt (wℓ w (w.length - 1)) false (posO o (wℓ w) (w.length - 1)) ∪
      pieceAt (wℓ w 0) (decide (o = Orientation.horizontal) && decide (wℓ w 1 = Letter.q) &&
        decide (wℓ w 0 = Letter.q))
        (posO o (wℓ w) (w.length - 1) + (plusStepO o (wℓ w 0) + ccO o (wℓ w 0) -
          plusStepO o (wℓ w (w.length - 1)) + familyShift o)) := by
  have hw : w ≠ [] := by
    rintro rfl
    simp at hn
  rw [stacked_eq_PM o w hw]
  have hL : lamO o (wℓ w) (w.length - 1) =
      (Finset.range (w.length - 1)).biUnion (fun k => pieceAt (wℓ w k) (flagO o (wℓ w) k) (posO o (wℓ w) k)) ∪
      (Finset.Ico 2 (w.length - 1)).biUnion (fun k => pieceAt (wℓ w k) (flagO o (wℓ w) k)
        (posO o (wℓ w) k + shadowO o (wℓ w k))) ∪ m0Piece o ∪
      pieceAt (wℓ w 1) false (posO o (wℓ w) 1 + shadowO o (wℓ w 1)) := by
    unfold lamO
    rw [if_pos (by omega), if_pos (by omega)]
  have hP : (Finset.range w.length).biUnion (plusPc o w) =
      (Finset.range (w.length - 1)).biUnion (fun k => pieceAt (wℓ w k) (flagO o (wℓ w) k) (posO o (wℓ w) k)) ∪
      pieceAt (wℓ w (w.length - 1)) false (posO o (wℓ w) (w.length - 1)) := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_union]
    constructor
    · rintro ⟨k, hk, hx⟩
      by_cases hk' : k = w.length - 1
      · rw [hk'] at hx
        rw [plusPc_last o w hPn] at hx
        exact Or.inr hx
      · exact Or.inl ⟨k, by omega, hx⟩
    · rintro (⟨k, hk, hx⟩ | hx)
      · exact ⟨k, by omega, hx⟩
      · exact ⟨w.length - 1, by omega, by rw [plusPc_last o w hPn]; exact hx⟩
  have hM : (Finset.range w.length).biUnion (minusPc o w) =
      m0Piece o ∪ pieceAt (wℓ w 1) false (posO o (wℓ w) 1 + shadowO o (wℓ w 1)) ∪
      (Finset.Ico 2 (w.length - 1)).biUnion (fun k => pieceAt (wℓ w k) (flagO o (wℓ w) k)
        (posO o (wℓ w) k + shadowO o (wℓ w k))) ∪
      pieceAt (wℓ w 0) (decide (o = Orientation.horizontal) && decide (wℓ w 1 = Letter.q) &&
        decide (wℓ w 0 = Letter.q))
        (posO o (wℓ w) (w.length - 1) + (plusStepO o (wℓ w 0) + ccO o (wℓ w 0) -
          plusStepO o (wℓ w (w.length - 1)) + familyShift o)) := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    constructor
    · rintro ⟨j, hj, hx⟩
      rcases (show j = 0 ∨ j = 1 ∨ (2 ≤ j ∧ j ≤ w.length - 2) ∨ j = w.length - 1 by omega) with h | h | ⟨h1, h2⟩ | h
      · subst h
        rw [minusPc_zero o w hm0] at hx
        exact Or.inl (Or.inl (Or.inl hx))
      · subst h
        rw [minusPc_one o w hn hpal hlast hf1] at hx
        exact Or.inl (Or.inl (Or.inr hx))
      · refine Or.inl (Or.inr ⟨j, ⟨h1, by omega⟩, ?_⟩)
        rw [minusPc_mid o w hn hpal hlast j h1 h2] at hx
        exact hx
      · subst h
        rw [minusPc_last o w hn hpal hlast] at hx
        exact Or.inr hx
    · rintro (((h | h) | ⟨a, ⟨ha1, ha2⟩, hx⟩) | h)
      · exact ⟨0, by omega, by rw [minusPc_zero o w hm0]; exact h⟩
      · exact ⟨1, by omega, by rw [minusPc_one o w hn hpal hlast hf1]; exact h⟩
      · exact ⟨a, by omega, by rw [minusPc_mid o w hn hpal hlast a ha1 (by omega)]; exact hx⟩
      · exact ⟨w.length - 1, by omega, by rw [minusPc_last o w hn hpal hlast]; exact h⟩
  rw [hP, hM, hL]
  ext x
  simp only [Finset.mem_union]
  tauto

end FLatticePaper.Tiles

