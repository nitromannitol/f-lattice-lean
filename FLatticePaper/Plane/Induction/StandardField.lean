import FLatticePaper.Plane.Induction.Coherence
import FLatticePaper.Plane.Induction.OddStep
import FLatticePaper.Construction.StaircaseExtension

namespace FLatticePaper.Induction
open Farey Construction

/-- The explicit periodization of `M`: the value at `z` is read from the representative of `z` in the
parity window, and the period increment of that representative is added. -/
def ChildFrame.sewnField (frame : ChildFrame) (M : Site → ℤ) (cU cV : ℤ) : Field := fun z =>
  let T := frame.child.periodDenominator
  let a := if EvenSite z then 2 else frame.child.num
  let c := if EvenSite z then 0 else 2 - frame.child.den + frame.child.num
  let j := -((frame.tGrade z - (a - T)) / T)
  let i := (frame.sGrade z - c) / T
  let y := z - frame.child.modifiedDeck.combine i j
  M y + periodIncrement frame.child cU cV y i j

/-- A site lies in the fundamental window of its parity: its transverse grade lies in `[a − T, a − 1]` and its
longitudinal grade in `[c, c + T − 1]`, with `(a, c) = (2, 0)` at even sites and `(n, 2 − d + n)` at odd sites. -/
def ChildFrame.InWindow (frame : ChildFrame) (y : Site) : Prop :=
  (EvenSite y ∧ 2 - frame.child.periodDenominator ≤ frame.tGrade y ∧ frame.tGrade y ≤ 1 ∧
      0 ≤ frame.sGrade y ∧ frame.sGrade y ≤ frame.child.periodDenominator - 1) ∨
    (¬ EvenSite y ∧ frame.child.num - frame.child.periodDenominator ≤ frame.tGrade y ∧
      frame.tGrade y ≤ frame.child.num - 1 ∧
      2 - frame.child.den + frame.child.num ≤ frame.sGrade y ∧
      frame.sGrade y ≤ 2 - frame.child.den + frame.child.num + frame.child.periodDenominator - 1)

theorem ediv_eq_of_window (x r k T : ℤ) (hT : 0 < T) (hx : x = r + k * T) (h0 : 0 ≤ r) (h1 : r < T) :
    x / T = k := by
  rw [hx, Int.add_mul_ediv_right r k hT.ne', Int.ediv_eq_zero_of_lt h0 h1, zero_add]

theorem chooseTwo_succ_eq (j : ℤ) : chooseTwo (j + 1) = chooseTwo j + j := by
  rw [chooseTwo_add]
  have h1 : chooseTwo 1 = 0 := by decide
  rw [h1]
  ring

theorem ChildFrame.combine_add_combine (frame : ChildFrame) (i j i' j' : ℤ) :
    frame.child.modifiedDeck.combine i j + frame.child.modifiedDeck.combine i' j' =
      frame.child.modifiedDeck.combine (i + i') (j + j') := by
  simp only [ChildFrame.child_modifiedDeck_combine]
  exact Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring)

theorem ChildFrame.transverseGrade_child (frame : ChildFrame) (site : Site) :
    frame.child.transverseGrade site = -frame.tGrade site := by
  unfold Fraction.transverseGrade ChildFrame.tGrade
  ring

/-- On a window representative `y`, the explicit periodization is the value of `M` at `y` plus the increment. -/
theorem ChildFrame.sewnField_apply_of_window (frame : ChildFrame) (M : Site → ℤ) (cU cV : ℤ)
    {y : Site} (hy : frame.InWindow y) (i j : ℤ) :
    frame.sewnField M cU cV (y + frame.child.modifiedDeck.combine i j) =
      M y + periodIncrement frame.child cU cV y i j := by
  have hT : 0 < frame.child.periodDenominator := frame.T_pos
  have ht := frame.tGrade_add_combine y i j
  have hs := frame.sGrade_add_combine y i j
  have hpar := frame.evenSite_add_combine y i j
  rcases hy with ⟨hE, t1, t2, s1, s2⟩ | ⟨hO, t1, t2, s1, s2⟩
  · have hI : (frame.sGrade (y + frame.child.modifiedDeck.combine i j) - 0) /
        frame.child.periodDenominator = i :=
      ediv_eq_of_window _ (frame.sGrade y - 0) i _ hT (by rw [hs]; ring) (by linarith) (by linarith)
    have hq : (frame.tGrade (y + frame.child.modifiedDeck.combine i j) -
        (2 - frame.child.periodDenominator)) / frame.child.periodDenominator = -j :=
      ediv_eq_of_window _ (frame.tGrade y - (2 - frame.child.periodDenominator)) (-j) _ hT
        (by rw [ht]; ring) (by linarith) (by linarith)
    have hpar' : EvenSite (y + frame.child.modifiedDeck.combine i j) := hpar.mpr hE
    simp only [ChildFrame.sewnField, if_pos hpar']
    rw [hI, hq, neg_neg, add_sub_cancel_right]
  · have hpar' : ¬ EvenSite (y + frame.child.modifiedDeck.combine i j) := fun h => hO (hpar.mp h)
    have hI : (frame.sGrade (y + frame.child.modifiedDeck.combine i j) -
        (2 - frame.child.den + frame.child.num)) / frame.child.periodDenominator = i :=
      ediv_eq_of_window _ (frame.sGrade y - (2 - frame.child.den + frame.child.num)) i _ hT
        (by rw [hs]; ring) (by linarith) (by linarith)
    have hq : (frame.tGrade (y + frame.child.modifiedDeck.combine i j) -
        (frame.child.num - frame.child.periodDenominator)) / frame.child.periodDenominator = -j :=
      ediv_eq_of_window _ (frame.tGrade y - (frame.child.num - frame.child.periodDenominator)) (-j) _ hT
        (by rw [ht]; ring) (by linarith) (by linarith)
    simp only [ChildFrame.sewnField, if_neg hpar']
    rw [hI, hq, neg_neg, add_sub_cancel_right]

/-- Every site has a representative in the window of its parity. -/
theorem ChildFrame.exists_window_rep (frame : ChildFrame) (z : Site) :
    ∃ y : Site, ∃ i j : ℤ, z = y + frame.child.modifiedDeck.combine i j ∧ frame.InWindow y := by
  have hT : 0 < frame.child.periodDenominator := frame.T_pos
  have aux : ∀ a c : ℤ, ∃ y : Site, ∃ i j : ℤ, z = y + frame.child.modifiedDeck.combine i j ∧
      0 ≤ frame.tGrade y - (a - frame.child.periodDenominator) ∧
      frame.tGrade y - (a - frame.child.periodDenominator) < frame.child.periodDenominator ∧
      0 ≤ frame.sGrade y - c ∧ frame.sGrade y - c < frame.child.periodDenominator := by
    intro a c
    have hr1 := Int.emod_add_ediv_mul (frame.tGrade z - (a - frame.child.periodDenominator))
      frame.child.periodDenominator
    have hr2 := Int.emod_add_ediv_mul (frame.sGrade z - c) frame.child.periodDenominator
    have h01 := Int.emod_nonneg (frame.tGrade z - (a - frame.child.periodDenominator)) hT.ne'
    have h11 := Int.emod_lt_of_pos (frame.tGrade z - (a - frame.child.periodDenominator)) hT
    have h02 := Int.emod_nonneg (frame.sGrade z - c) hT.ne'
    have h12 := Int.emod_lt_of_pos (frame.sGrade z - c) hT
    obtain ⟨y, hy⟩ : ∃ y : Site, y = z - frame.child.modifiedDeck.combine
        ((frame.sGrade z - c) / frame.child.periodDenominator)
        (-((frame.tGrade z - (a - frame.child.periodDenominator)) / frame.child.periodDenominator)) :=
      ⟨_, rfl⟩
    have hzy : z = y + frame.child.modifiedDeck.combine
        ((frame.sGrade z - c) / frame.child.periodDenominator)
        (-((frame.tGrade z - (a - frame.child.periodDenominator)) / frame.child.periodDenominator)) := by
      rw [hy, sub_add_cancel]
    have ht := frame.tGrade_add_combine y
      ((frame.sGrade z - c) / frame.child.periodDenominator)
      (-((frame.tGrade z - (a - frame.child.periodDenominator)) / frame.child.periodDenominator))
    have hs := frame.sGrade_add_combine y
      ((frame.sGrade z - c) / frame.child.periodDenominator)
      (-((frame.tGrade z - (a - frame.child.periodDenominator)) / frame.child.periodDenominator))
    rw [← hzy] at ht hs
    have e1 : frame.tGrade y - (a - frame.child.periodDenominator) =
        (frame.tGrade z - (a - frame.child.periodDenominator)) % frame.child.periodDenominator := by
      linear_combination (-1 : ℤ) * ht + (-1 : ℤ) * hr1
    have e2 : frame.sGrade y - c = (frame.sGrade z - c) % frame.child.periodDenominator := by
      linear_combination (-1 : ℤ) * hs + (-1 : ℤ) * hr2
    refine ⟨y, _, _, hzy, ?_, ?_, ?_, ?_⟩
    · rw [e1]; exact h01
    · rw [e1]; exact h11
    · rw [e2]; exact h02
    · rw [e2]; exact h12
  by_cases hE : EvenSite z
  · obtain ⟨y, i, j, hzy, t1, t2, s1, s2⟩ := aux 2 0
    have hEy : EvenSite y := (frame.evenSite_add_combine y i j).mp (by rw [← hzy]; exact hE)
    exact ⟨y, i, j, hzy, Or.inl ⟨hEy, by linarith, by linarith, by linarith, by linarith⟩⟩
  · obtain ⟨y, i, j, hzy, t1, t2, s1, s2⟩ := aux frame.child.num (2 - frame.child.den + frame.child.num)
    have hOy : ¬ EvenSite y := fun h => hE (by rw [hzy]; exact (frame.evenSite_add_combine y i j).mpr h)
    exact ⟨y, i, j, hzy, Or.inr ⟨hOy, by linarith, by linarith, by linarith, by linarith⟩⟩

/-- Windows lie in the closed polygon. -/
theorem ChildFrame.mem_of_inWindow (frame : ChildFrame) {y : Site} (hy : frame.InWindow y) :
    y ∈ frame.closedPolygon := by
  obtain ⟨hN, hND, hdiff, hD3, -⟩ := frame.child_facts
  rw [frame.mem_closedPolygon_iff]
  rcases hy with ⟨hE, t1, t2, s1, s2⟩ | ⟨hO, t1, t2, s1, s2⟩
  · exact Or.inl ⟨hE, t1, by linarith, s1, by linarith⟩
  · exact Or.inr ⟨hO, t1, by linarith, s1, by linarith⟩

/-- The explicit periodization satisfies the period law on `E` and the generator identities. -/
theorem ChildFrame.sewnField_spec (frame : ChildFrame) {M : Site → ℤ} {cU cV : ℤ}
    (h : RespectsPeriodsOn frame.child cU cV frame.closedPolygon M) :
    (∀ y ∈ frame.closedPolygon, frame.sewnField M cU cV y = M y) ∧
      HasGeneratorPeriods frame.child (frame.sewnField M cU cV) cU cV := by
  have hkernel : frame.child.modifiedDeck.combine 1 0 = frame.child.modifiedDeck.kernel := by
    rw [frame.child_modifiedDeck_kernel, frame.child_modifiedDeck_combine]
    exact Prod.ext (by dsimp only; ring) (by dsimp only; ring)
  have htransverse : frame.child.modifiedDeck.combine 0 1 = frame.child.modifiedDeck.transverse := by
    rw [frame.child_modifiedDeck_transverse, frame.child_modifiedDeck_combine]
    exact Prod.ext (by dsimp only; ring) (by dsimp only; ring)
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨y, i, j, hzy, hy⟩ := frame.exists_window_rep z
    subst hzy
    rw [frame.sewnField_apply_of_window M cU cV hy i j, h y (frame.mem_of_inWindow hy) i j hz]
  · unfold HasGeneratorPeriods
    refine ⟨fun site => ?_, fun site => ?_⟩
    · obtain ⟨y, i, j, hzy, hy⟩ := frame.exists_window_rep site
      subst hzy
      rw [← hkernel, add_assoc, frame.combine_add_combine, frame.sewnField_apply_of_window M cU cV hy,
        frame.sewnField_apply_of_window M cU cV hy]
      simp only [add_zero, frame.periodIncrement_child]
      ring
    · obtain ⟨y, i, j, hzy, hy⟩ := frame.exists_window_rep site
      subst hzy
      rw [← htransverse, add_assoc, frame.combine_add_combine, frame.sewnField_apply_of_window M cU cV hy,
        frame.sewnField_apply_of_window M cU cV hy, frame.transverseGrade_child, frame.tGrade_add_combine]
      simp only [add_zero, frame.periodIncrement_child]
      rw [chooseTwo_succ_eq]
      ring

/-! ### Words: the birth word of the odd register -/

/-- The prefix before the last digit `1` or `2`: the birth word of the odd register. -/
def oddBirthPrefix (word : Word) : Word :=
  ((word.reverse.dropWhile (fun d => decide (d = Digit.three))).drop 1).reverse

theorem exists_of_not_all {word : Word} (h : ¬ ∀ x ∈ word, x = Digit.three) :
    ∃ x ∈ word, x ≠ Digit.three := by
  by_contra hc
  exact h (fun x hx => by_contra fun hne => hc ⟨x, hx, hne⟩)

theorem split_at_last_nonthree (r : Word) (h : ∃ x ∈ r, x ≠ Digit.three) :
    ∃ T rest : Word, ∃ x : Digit, x ≠ Digit.three ∧ r = T ++ x :: rest ∧
      (∀ y ∈ T, y = Digit.three) ∧
      r.dropWhile (fun d => decide (d = Digit.three)) = x :: rest := by
  induction r with
  | nil =>
    obtain ⟨x, hx, -⟩ := h
    simp at hx
  | cons a r ih =>
    by_cases ha : a = Digit.three
    · have h' : ∃ x ∈ r, x ≠ Digit.three := by
        obtain ⟨x, hx, hne⟩ := h
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact absurd ha hne
        · exact ⟨x, hx', hne⟩
      obtain ⟨T, rest, x, hx, hr, hT, hd⟩ := ih h'
      refine ⟨a :: T, rest, x, hx, by simp [hr], ?_, ?_⟩
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact ha
        · exact hT y hy'
      · simp [ha, hd]
    · refine ⟨[], r, a, ha, by simp, by simp, ?_⟩
      simp [ha]

theorem all_three_eq_replicate {word : Word} (h : ∀ x ∈ word, x = Digit.three) :
    word = List.replicate word.length Digit.three := by
  induction word with
  | nil => rfl
  | cons a w ih =>
    have ha : a = Digit.three := h a (by simp)
    have hw : ∀ x ∈ w, x = Digit.three := fun x hx => h x (by simp [hx])
    subst ha
    rw [List.length_cons, List.replicate_succ]
    exact congrArg (List.cons Digit.three) (ih hw)

theorem oddBirthPrefix_decomp {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) :
    ∃ x : Digit, x ≠ Digit.three ∧
      ∃ k : ℕ, word = oddBirthPrefix word ++ [x] ++ List.replicate k Digit.three := by
  have h' : ∃ x ∈ word.reverse, x ≠ Digit.three := by
    obtain ⟨x, hx, hne⟩ := h
    exact ⟨x, List.mem_reverse.mpr hx, hne⟩
  obtain ⟨T, rest, x, hx, hr, hT, hd⟩ := split_at_last_nonthree word.reverse h'
  have hP : oddBirthPrefix word = rest.reverse := by
    unfold oddBirthPrefix
    rw [hd]
    simp
  have hTr : T.reverse = List.replicate T.reverse.length Digit.three := by
    apply all_three_eq_replicate
    intro y hy
    exact hT y (List.mem_reverse.mp hy)
  have hw : word = rest.reverse ++ [x] ++ T.reverse := by
    have hrev := congrArg List.reverse hr
    rw [List.reverse_reverse] at hrev
    rw [hrev]
    simp [List.reverse_append, List.append_assoc]
  refine ⟨x, hx, T.reverse.length, ?_⟩
  rw [hP, ← hTr]
  exact hw

theorem oddBirthPrefix_length_lt {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) :
    (oddBirthPrefix word).length < word.length := by
  obtain ⟨x, -, k, hw⟩ := oddBirthPrefix_decomp h
  have hl := congrArg List.length hw
  simp only [List.length_append, List.length_replicate, List.length_singleton] at hl
  omega

theorem length_map_oddBirthPrefix_lt {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) :
    ((oddBirthPrefix word).map Digit.swapTwoThree).length < word.length := by
  rw [List.length_map]
  exact oddBirthPrefix_length_lt h

theorem walk_three_odd (p : Parents) (R : Word) (hR : ∀ y ∈ R, y = Digit.three) :
    (p.walk R).odd = p.odd := by
  induction R generalizing p with
  | nil => rfl
  | cons a R ih =>
    have ha : a = Digit.three := hR a (by simp)
    subst ha
    rw [Parents.walk_cons, ih (p.step Digit.three) (fun y hy => hR y (by simp [hy]))]
    rfl

/-- The odd register of a word is the current odd fraction of its birth prefix. -/
theorem parentsAt_odd_eq {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) :
    (parentsAt word).odd = (parentsAt (oddBirthPrefix word)).current .odd := by
  obtain ⟨x, hx, k, hw⟩ := oddBirthPrefix_decomp h
  obtain ⟨P, hP⟩ : ∃ P, P = oddBirthPrefix word := ⟨_, rfl⟩
  rw [← hP] at hw ⊢
  have hR : ∀ y ∈ List.replicate k Digit.three, y = Digit.three :=
    fun y hy => List.eq_of_mem_replicate hy
  have hpa : parentsAt (P ++ [x] ++ List.replicate k Digit.three) =
      (parentsAt (P ++ [x])).walk (List.replicate k Digit.three) :=
    Parents.walk_append root (P ++ [x]) (List.replicate k Digit.three)
  rw [hw, hpa, parentsAt_append_singleton, walk_three_odd _ _ hR]
  cases x with
  | one => rfl
  | two => rfl
  | three => exact absurd rfl hx

/-! ### The standard field -/

/-- The frame of a word. -/
def frameAt (word : Word) : ChildFrame := ⟨parentsAt word, parentsAt_valid word⟩

theorem stairEven_valid_reciprocal (k : ℕ) : BaseMask.stairEven.Valid (2 * (k : ℤ) + 3) := by
  show 3 ≤ 2 * (k : ℤ) + 3 ∧ (2 * (k : ℤ) + 3) % 2 = 1
  constructor <;> omega

/-- The reciprocal staircase field (B1) at the child `1/(2k+3)`, which is the even child of the word `3^k`. -/
noncomputable def reciprocalField (k : ℕ) : Field :=
  Classical.choose (stairEven_exists_extension (den := 2 * (k : ℤ) + 3) (stairEven_valid_reciprocal k))

/-- The standard field at the even child of every word. -/
noncomputable def standardField (word : Word) : Field :=
  if _h : ∀ x ∈ word, x = Digit.three then reciprocalField word.length
  else
    (frameAt word).sewnField
      ((frameAt word).sheetMin
        (quarterTurnField (standardField ((oddBirthPrefix word).map Digit.swapTwoThree))))
      (frameAt word).coherentConstantU (frameAt word).coherentConstantV
termination_by word.length
decreasing_by
  all_goals simp_wf
  all_goals exact oddBirthPrefix_length_lt (exists_of_not_all (by assumption))

theorem standardField_threes (k : ℕ) :
    standardField (List.replicate k Digit.three) = reciprocalField k := by
  rw [standardField, dif_pos]
  · simp
  · intro x hx
    exact List.eq_of_mem_replicate hx

theorem standardField_proper {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) :
    standardField word = (frameAt word).sewnField
      ((frameAt word).sheetMin
        (quarterTurnField (standardField ((oddBirthPrefix word).map Digit.swapTwoThree))))
      (frameAt word).coherentConstantU (frameAt word).coherentConstantV := by
  have hnot : ¬ ∀ x ∈ word, x = Digit.three := fun hall => by
    obtain ⟨x, hx, hne⟩ := h
    exact hne (hall x hx)
  rw [standardField, dif_neg hnot]

end FLatticePaper.Induction
