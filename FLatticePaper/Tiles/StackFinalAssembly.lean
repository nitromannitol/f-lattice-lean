import FLatticePaper.Tiles.StackFinalTruth
import FLatticePaper.Tiles.StackDecomp
import FLatticePaper.Tiles.StackedStringConnected

/-! The simple connectivity of the stacked strings of almost palindromes of length at least three, from the truth of
the final union and the decomposition. -/

namespace FLatticePaper.Tiles

/-- The final union, in the shape of the decomposition (anchor `posO (q + 1)`). -/
def finSetDef (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) : Finset Site :=
  lamO o ℓ (q + 1) ∪ pieceAt (ℓ (q + 1)) false (posO o ℓ (q + 1)) ∪
    pieceAt (ℓ 0) (decide (o = Orientation.horizontal) && decide (ℓ 1 = Letter.q) && decide (ℓ 0 = Letter.q))
      (posO o ℓ (q + 1) + (plusStepO o (ℓ 0) + ccO o (ℓ 0) - plusStepO o (ℓ (q + 1)) + familyShift o))

theorem mem_pieceAt_shift (l : Letter) (e : Bool) (A d x : Site) :
    x ∈ pieceAt l e (A + d) ↔ (x - A) - d ∈ tileSitesOf l e := by
  rw [piece_mem_iff, show x - (A + d) = x - A - d from by abel]

theorem finSetDef_mem_h (q : ℕ) (ℓ : ℕ → Letter) (hl0 : ℓ 0 = Letter.q) (hl : ℓ (q + 1) = Letter.p) (x : Site) :
    x ∈ finSetDef .horizontal ℓ q ↔
      x ∈ lamO .horizontal ℓ (q + 1) ∨ x - posO .horizontal ℓ (q + 1) ∈ finRel .horizontal (stateOf .horizontal ℓ (q + 1)).secondL := by
  have hc : plusStepO .horizontal (ℓ 0) + ccO .horizontal (ℓ 0) - plusStepO .horizontal (ℓ (q + 1)) +
      familyShift .horizontal = ((1 : ℤ), (-1 : ℤ)) := by
    rw [hl0, hl]
    decide
  unfold finSetDef
  rw [hc]
  simp only [Finset.mem_union, hl0, hl, decide_true, Bool.true_and, Bool.and_true]
  rw [or_assoc]
  apply or_congr Iff.rfl
  show _ ↔ x - posO .horizontal ℓ (q + 1) ∈ tileSitesOf .p false ++
    (tileSitesOf .q (decide (ℓ 1 = Letter.q))).map (fun c => c + ((1 : ℤ), (-1 : ℤ)))
  rw [List.mem_append, List.mem_map]
  constructor
  · rintro (h | h)
    · exact Or.inl ((piece_mem_iff _ _ _ _).1 h)
    · rw [mem_pieceAt_shift] at h
      exact Or.inr ⟨_, h, by abel⟩
  · rintro (h | ⟨c, hc, hcx⟩)
    · exact Or.inl ((piece_mem_iff _ _ _ _).2 h)
    · right
      rw [mem_pieceAt_shift]
      have e : x - posO .horizontal ℓ (q + 1) - ((1 : ℤ), (-1 : ℤ)) = c := by
        rw [← hcx]
        abel
      rw [e]
      exact hc


theorem finSetDef_mem_v (q : ℕ) (ℓ : ℕ → Letter) (hl0 : ℓ 0 = Letter.p) (hl : ℓ (q + 1) = Letter.q) (x : Site) :
    x ∈ finSetDef .vertical ℓ q ↔
      x ∈ lamO .vertical ℓ (q + 1) ∨ x - posO .vertical ℓ (q + 1) ∈ finRel .vertical (stateOf .vertical ℓ (q + 1)).secondL := by
  have hc : plusStepO .vertical (ℓ 0) + ccO .vertical (ℓ 0) - plusStepO .vertical (ℓ (q + 1)) +
      familyShift .vertical = ((1 : ℤ), (0 : ℤ)) := by
    rw [hl0, hl]
    decide
  have hf : decide (Orientation.vertical = Orientation.horizontal) = false := by decide
  unfold finSetDef
  rw [hc, hf, Bool.false_and]
  simp only [Finset.mem_union, hl0, hl]
  rw [or_assoc]
  apply or_congr Iff.rfl
  show _ ↔ x - posO .vertical ℓ (q + 1) ∈ tileSitesOf .q false ++
    (tileSitesOf .p false).map (fun c => c + ((1 : ℤ), (0 : ℤ)))
  rw [List.mem_append, List.mem_map]
  constructor
  · rintro (h | h)
    · exact Or.inl ((piece_mem_iff _ _ _ _).1 h)
    · rw [mem_pieceAt_shift] at h
      exact Or.inr ⟨_, h, by abel⟩
  · rintro (h | ⟨c, hc, hcx⟩)
    · exact Or.inl ((piece_mem_iff _ _ _ _).2 h)
    · right
      rw [mem_pieceAt_shift]
      have e : x - posO .vertical ℓ (q + 1) - ((1 : ℤ), (0 : ℤ)) = c := by
        rw [← hcx]
        abel
      rw [e]
      exact hc


theorem wℓ_zero_of_head (w : BinaryWord) (a : Letter) (h : w.head? = some a) : wℓ w 0 = a := by
  cases w with
  | nil => simp at h
  | cons b t =>
    simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    rfl

theorem wℓ_last_of_getLast (w : BinaryWord) (a : Letter) (h : w.getLast? = some a) :
    wℓ w (w.length - 1) = a := by
  unfold wℓ
  rw [List.getD_eq_getElem?_getD, ← List.getLast?_eq_getElem?, h]
  rfl

theorem stacked_horizontal_simply_connected (w : BinaryWord) (hA : IsAlmostPalindrome w) (hn : 3 ≤ w.length)
    (h0 : w.head? = some Letter.q) (hl : w.getLast? = some Letter.p) :
    SimplyConnectedCells (stackedSites .horizontal w) := by
  have hw0 := wℓ_zero_of_head w _ h0
  have hwl := wℓ_last_of_getLast w _ hl
  have hpal : ∀ i, 1 ≤ i → i ≤ w.length - 2 → wℓ w (w.length - 1 - i) = wℓ w i :=
    fun i h1 h2 => almost_pal_index w hA i h1 h2
  have hlast : ccO .horizontal (wℓ w (w.length - 1)) = 0 := by
    rw [hwl]
    decide
  have hm0 : m0Piece .horizontal = pieceAt (wℓ w (w.length - 1)) false (familyShift .horizontal) := by
    rw [hwl]
    rfl
  have hf1 : flagR .horizontal (wℓ w) w.length 1 = false := by
    simp [flagR, hwl]
  have hPn : flagO .horizontal (wℓ w) (w.length - 1) = false := by
    obtain ⟨m, hm⟩ : ∃ m, w.length - 1 = m + 1 := ⟨w.length - 2, by omega⟩
    rw [hm] at hwl ⊢
    simp [flagO, hwl]
  have hdec := stacked_decomp .horizontal w hn hpal hlast hm0 hf1 hPn
  have hS : stackedSites .horizontal w = finSetDef .horizontal (wℓ w) (w.length - 2) := by
    rw [hdec]
    unfold finSetDef
    rw [show w.length - 1 = w.length - 2 + 1 by omega]
  have hq1 : 1 ≤ w.length - 2 := by omega
  have hGood := goodAt_all .horizontal (wℓ w) (w.length - 2) hq1
  have hl' : wℓ w (w.length - 2 + 1) = Letter.p := by
    rw [show w.length - 2 + 1 = w.length - 1 by omega]
    exact hwl
  have hF := fun x => finSetDef_mem_h (w.length - 2) (wℓ w) hw0 hl' x
  have hlastsec : (stateOf .horizontal (wℓ w) (w.length - 2 + 1)).lastL =
      (stateOf .horizontal (wℓ w) (w.length - 2 + 1)).secondL := by
    show wℓ w (w.length - 2 + 1 - 1) = wℓ w 1
    rw [show w.length - 2 + 1 - 1 = w.length - 2 by omega]
    have h1 := hpal 1 le_rfl (by omega)
    rw [show w.length - 1 - 1 = w.length - 2 by omega] at h1
    exact h1
  have hok0 := okF_h _ hGood.reach hlastsec
  have hlL : lastLetter .horizontal = wℓ w (w.length - 2 + 1) := hl'.symm
  unfold okF at hok0
  rw [hlL] at hok0
  have hok : ∀ i : ℕ, i < 8 → rowOkF .horizontal (stateOf .horizontal (wℓ w) (w.length - 2 + 1))
      (wℓ w (w.length - 2 + 1)) i = true := by
    intro i hi
    exact List.all_eq_true.1 ((Bool.and_eq_true _ _).mp hok0).1 i (List.mem_range.2 hi)
  have hpair : ∀ k : ℕ, k < 7 → pairOkF .horizontal (stateOf .horizontal (wℓ w) (w.length - 2 + 1))
      (wℓ w (w.length - 2 + 1)) k = true := by
    intro k hk
    exact List.all_eq_true.1 ((Bool.and_eq_true _ _).mp hok0).2 k (List.mem_range.2 hk)
  have hGF := goodF .horizontal (wℓ w) (w.length - 2) hq1 (finSetDef .horizontal (wℓ w) (w.length - 2))
    hF hGood hok hpair
  rw [hS]
  exact simplyConnectedCells_of_rows hGF.1 hGF.2

theorem stacked_vertical_simply_connected (w : BinaryWord) (hA : IsAlmostPalindrome w) (hn : 3 ≤ w.length)
    (h0 : w.head? = some Letter.p) (hl : w.getLast? = some Letter.q) :
    SimplyConnectedCells (stackedSites .vertical w) := by
  have hw0 := wℓ_zero_of_head w _ h0
  have hwl := wℓ_last_of_getLast w _ hl
  have hpal : ∀ i, 1 ≤ i → i ≤ w.length - 2 → wℓ w (w.length - 1 - i) = wℓ w i :=
    fun i h1 h2 => almost_pal_index w hA i h1 h2
  have hlast : ccO .vertical (wℓ w (w.length - 1)) = 0 := by
    rw [hwl]
    decide
  have hm0 : m0Piece .vertical = pieceAt (wℓ w (w.length - 1)) false (familyShift .vertical) := by
    rw [hwl]
    rfl
  have hf1 : flagR .vertical (wℓ w) w.length 1 = false := by
    simp [flagR]
  have hPn : flagO .vertical (wℓ w) (w.length - 1) = false := by
    obtain ⟨m, hm⟩ : ∃ m, w.length - 1 = m + 1 := ⟨w.length - 2, by omega⟩
    rw [hm]
    simp [flagO]
  have hdec := stacked_decomp .vertical w hn hpal hlast hm0 hf1 hPn
  have hS : stackedSites .vertical w = finSetDef .vertical (wℓ w) (w.length - 2) := by
    rw [hdec]
    unfold finSetDef
    rw [show w.length - 1 = w.length - 2 + 1 by omega]
  have hq1 : 1 ≤ w.length - 2 := by omega
  have hGood := goodAt_all .vertical (wℓ w) (w.length - 2) hq1
  have hl' : wℓ w (w.length - 2 + 1) = Letter.q := by
    rw [show w.length - 2 + 1 = w.length - 1 by omega]
    exact hwl
  have hF := fun x => finSetDef_mem_v (w.length - 2) (wℓ w) hw0 hl' x
  have hlastsec : (stateOf .vertical (wℓ w) (w.length - 2 + 1)).lastL =
      (stateOf .vertical (wℓ w) (w.length - 2 + 1)).secondL := by
    show wℓ w (w.length - 2 + 1 - 1) = wℓ w 1
    rw [show w.length - 2 + 1 - 1 = w.length - 2 by omega]
    have h1 := hpal 1 le_rfl (by omega)
    rw [show w.length - 1 - 1 = w.length - 2 by omega] at h1
    exact h1
  have hok0 := okF_v _ hGood.reach hlastsec
  have hlL : lastLetter .vertical = wℓ w (w.length - 2 + 1) := hl'.symm
  unfold okF at hok0
  rw [hlL] at hok0
  have hok : ∀ i : ℕ, i < 8 → rowOkF .vertical (stateOf .vertical (wℓ w) (w.length - 2 + 1))
      (wℓ w (w.length - 2 + 1)) i = true := by
    intro i hi
    exact List.all_eq_true.1 ((Bool.and_eq_true _ _).mp hok0).1 i (List.mem_range.2 hi)
  have hpair : ∀ k : ℕ, k < 7 → pairOkF .vertical (stateOf .vertical (wℓ w) (w.length - 2 + 1))
      (wℓ w (w.length - 2 + 1)) k = true := by
    intro k hk
    exact List.all_eq_true.1 ((Bool.and_eq_true _ _).mp hok0).2 k (List.mem_range.2 hk)
  have hGF := goodF .vertical (wℓ w) (w.length - 2) hq1 (finSetDef .vertical (wℓ w) (w.length - 2))
    hF hGood hok hpair
  rw [hS]
  exact simplyConnectedCells_of_rows hGF.1 hGF.2

end FLatticePaper.Tiles
