import FLatticePaper.Construction.AlternateIdentification

/-! # The parity of the odd alternate chart (task 46)

For an odd-parity word `w = p ++ [d]` (`d` is `1` or `3`), the chart `alternateOddChart w = alternateOddDelta w − alternateOddLowerLeft w`
has an even coordinate sum (`EvenSite`), so the odd target has the even parity required by `global_odometers_pair`.

* The chart offset `alternateOddDelta` has an even sum: the transverse offsets have sum `2 · num`, and the kernel offset of the even
  parent has sum `den + num`, which is even (`Parents.ValidFrame.even_parity`).
* The lower-left site is an offset of one of the seven copies. Every alternate jet offset of the odd output has an even sum (the odd
  parent's kernel only appears doubled), and so does the seventh copy's offset.
* The seventh copy adds the restoration `alternateRestoration w .even`, whose birth is `(p, even)` (the even parent of `w` changed at its
  last letter). Its sum is even unless `p` is a power of three; in that case the lower-left site is `(0, 0)`, checked on the explicit
  parents of `3^k` and `3^k 1`. -/

namespace FLatticePaper.Construction

open Farey FLatticePaper

/-! ## The lower-left order -/

/-- The order of the lower-left choice: the lower row first, then the column. -/
def lexLe (a b : Site) : Prop := a.2 < b.2 ∨ (a.2 = b.2 ∧ a.1 ≤ b.1)

theorem lexLe_refl (a : Site) : lexLe a a := Or.inr ⟨rfl, le_refl _⟩

theorem lexLe_trans {a b c : Site} (h1 : lexLe a b) (h2 : lexLe b c) : lexLe a c := by
  unfold lexLe at *
  omega

theorem lexLe_total (a b : Site) : lexLe a b ∨ lexLe b a := by
  unfold lexLe
  omega

theorem lexLe_antisymm {a b : Site} (h1 : lexLe a b) (h2 : lexLe b a) : a = b := by
  unfold lexLe at *
  exact Prod.ext (by omega) (by omega)

theorem siteLexMin_le_iff (a b : Site) : toLex (a.2, a.1) ≤ toLex (b.2, b.1) ↔ lexLe a b := by
  unfold lexLe
  simp [Prod.Lex.le_iff]

theorem siteLexMin_spec (a b : Site) :
    (siteLexMin a b = a ∨ siteLexMin a b = b) ∧ lexLe (siteLexMin a b) a ∧ lexLe (siteLexMin a b) b := by
  unfold siteLexMin
  split_ifs with h
  · exact ⟨Or.inl rfl, lexLe_refl a, (siteLexMin_le_iff a b).mp h⟩
  · have h' : lexLe b a := (lexLe_total a b).resolve_left (fun hab => h ((siteLexMin_le_iff a b).mpr hab))
    exact ⟨Or.inr rfl, h', lexLe_refl b⟩

/-- The lower-left fold returns one of its arguments. -/
theorem foldl_siteLexMin_mem (l : List Site) (init : Site) :
    List.foldl siteLexMin init l ∈ init :: l := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
    have h := ih (siteLexMin init x)
    rw [List.foldl_cons]
    rcases (siteLexMin_spec init x).1 with h1 | h1 <;> rw [h1] at h ⊢ <;> simp only [List.mem_cons] at h ⊢ <;> tauto

/-- The lower-left fold is below every one of its arguments. -/
theorem foldl_siteLexMin_le (l : List Site) (init : Site) :
    ∀ x ∈ init :: l, lexLe (List.foldl siteLexMin init l) x := by
  induction l generalizing init with
  | nil =>
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rw [hx]
    exact lexLe_refl _
  | cons y ys ih =>
    intro x hx
    rw [List.foldl_cons]
    have hres := ih (siteLexMin init y)
    have hspec := siteLexMin_spec init y
    rcases List.mem_cons.mp hx with h | h
    · rw [h]
      exact lexLe_trans (hres (siteLexMin init y) (by simp)) hspec.2.1
    · rcases List.mem_cons.mp h with h' | h'
      · rw [h']
        exact lexLe_trans (hres (siteLexMin init y) (by simp)) hspec.2.2
      · exact hres x (List.mem_cons_of_mem _ h')

/-- If a site of the list is below every site of the list, the fold returns it. -/
theorem foldl_siteLexMin_eq_of_min (init : Site) (l : List Site) (m : Site) (hm : m ∈ init :: l)
    (hmin : ∀ x ∈ init :: l, lexLe m x) :
    List.foldl siteLexMin init l = m :=
  lexLe_antisymm (foldl_siteLexMin_le l init m hm) (hmin _ (foldl_siteLexMin_mem l init))

/-- Parity of the lower-left fold: if every candidate is even, so is the lower-left site. -/
theorem evenSite_foldl_siteLexMin (init : Site) (l : List Site) (h : ∀ x ∈ init :: l, EvenSite x) :
    EvenSite (List.foldl siteLexMin init l) :=
  h _ (foldl_siteLexMin_mem l init)

/-! ## Parities of the sites -/

theorem evenSite_add {a b : Site} (ha : EvenSite a) (hb : EvenSite b) : EvenSite (a + b) := by
  unfold EvenSite at *
  simp only [Prod.fst_add, Prod.snd_add]
  omega

theorem evenSite_sub {a b : Site} (ha : EvenSite a) (hb : EvenSite b) : EvenSite (a - b) := by
  unfold EvenSite at *
  simp only [Prod.fst_sub, Prod.snd_sub]
  omega

theorem evenSite_zero : EvenSite (0 : Site) := by
  unfold EvenSite
  simp

/-! ## The delta and the jets of the odd output -/

/-- The chart offset `alternateOddDelta` has an even sum: `2 · num − (den + num)` of the even parent in phase one. -/
theorem evenSite_delta (w : Word) : EvenSite (alternateOddDelta w) := by
  have he : ((parentsAt w).even.num + (parentsAt w).even.den) % 2 = 0 := (parentsAt_valid w).even_parity
  unfold alternateOddDelta
  split_ifs
  · unfold EvenSite
    simp only [Prod.fst_sub, Prod.snd_sub, transverseJet, kernelJet]
    omega
  · exact evenSite_zero

/-- Every offset of an alternate jet of the odd output has an even sum (the odd parent's kernel only appears doubled). -/
theorem evenSite_alternateJets_odd (w : Word) (k : Fin 6) : EvenSite (alternateJets w .odd k).1 := by
  have ho : ((parentsAt w).odd.num + (parentsAt w).odd.den) % 2 = 1 := (parentsAt_valid w).odd_parity
  have he : ((parentsAt w).even.num + (parentsAt w).even.den) % 2 = 0 := (parentsAt_valid w).even_parity
  unfold alternateJets
  by_cases h : phase w = 0 <;> fin_cases k <;>
    simp [h, doubleLast, kernelJet, transverseJet, EvenSite] <;> omega

/-- The offset of the seventh jet of the odd output has an even sum. -/
theorem evenSite_seventh_odd (p : Word) (d : Digit) : EvenSite (seventhAlternateJet p d .odd).1 := by
  have ho : ((parentsAt (p ++ [d])).odd.num + (parentsAt (p ++ [d])).odd.den) % 2 = 1 :=
    (parentsAt_valid (p ++ [d])).odd_parity
  have he : ((parentsAt (p ++ [d])).even.num + (parentsAt (p ++ [d])).even.den) % 2 = 0 :=
    (parentsAt_valid (p ++ [d])).even_parity
  unfold seventhAlternateJet
  by_cases h : phase (p ++ [d]) = 0 <;> cases d <;>
    simp [h, kernelJet, transverseJet, EvenSite] <;> omega

/-! ## The restoration of the seventh copy -/

/-- The birth of the even parent of a word ending in `1` or `3` is the prefix before the last letter. -/
theorem retainedBirth?_even_snoc (p : Word) (d : Digit) (hd : d = Digit.one ∨ d = Digit.three) :
    retainedBirth? (p ++ [d]) .even = some (p, .even) := by
  have hret : (parentsAt (p ++ [d])).retained .even = (parentsAt p).current .even := by
    rw [parentsAt_append_singleton]
    rcases hd with rfl | rfl <;> rfl
  have hne : (parentsAt (p ++ [d])).retained .even ≠ root.retained .even := by
    rw [hret]
    intro h
    have hint := (parentsAt_valid p).current_interior .even
    rw [h] at hint
    obtain ⟨_, h2⟩ := hint
    simp [root, Parents.retained] at h2
  unfold retainedBirth?
  rw [dif_neg hne]
  congr 1
  apply Birth.fraction_injective
  rw [fraction_birthOf, hret]
  rfl

/-- The restoration of the seventh copy of an odd word: either the prefix is a power of three, or its sum is even. -/
theorem evenSite_alternateRestoration_snoc (p : Word) (d : Digit) (hd : d = Digit.one ∨ d = Digit.three) :
    (∀ x ∈ p, x = Digit.three) ∨ EvenSite (alternateRestoration (p ++ [d]) .even) := by
  by_cases hall : ∀ x ∈ p, x = Digit.three
  · exact Or.inl hall
  · right
    have he : ((parentsAt p).even.num + (parentsAt p).even.den) % 2 = 0 := (parentsAt_valid p).even_parity
    have hfalse : p.all (fun digit => decide (digit = Digit.three)) = false := by
      rw [Bool.eq_false_iff]
      intro h
      exact hall (fun x hx => by simpa using (List.all_eq_true.mp h) x hx)
    unfold alternateRestoration
    rw [retainedBirth?_even_snoc p d hd]
    simp only [hfalse]
    unfold EvenSite
    split_ifs
    all_goals simp_all [kernelJet, transverseJet]
    all_goals omega

/-! ## The lower-left site of a non-cube prefix -/

/-- The lower-left site of the raw odd output of `p ++ [d]` is even when the prefix is not a power of three. -/
theorem evenSite_alternateOddLowerLeft_snoc (p : Word) (d : Digit) (hd : d = Digit.one ∨ d = Digit.three)
    (hnp : ¬ ∀ x ∈ p, x = Digit.three) : EvenSite (alternateOddLowerLeft (p ++ [d])) := by
  have hR : EvenSite (alternateRestoration (p ++ [d]) .even) :=
    (evenSite_alternateRestoration_snoc p d hd).resolve_left hnp
  have hl : (p ++ [d]).getLast? = some d := by simp
  have hdl : (p ++ [d]).dropLast = p := by simp
  unfold alternateOddLowerLeft
  simp only [hl, hdl]
  apply evenSite_foldl_siteLexMin
  intro x hx
  rcases List.mem_cons.mp hx with h | h
  · rw [h]
    exact evenSite_alternateJets_odd _ 0
  · rcases List.mem_cons.mp h with h' | h'
    · rw [h']
      exact evenSite_add (evenSite_seventh_odd p d) hR
    · simp only [List.mem_ofFn] at h'
      obtain ⟨k, rfl⟩ := h'
      exact evenSite_alternateJets_odd _ k

/-! ## The powers of three -/

theorem parentsAt_replicate_three_one (k : ℕ) :
    parentsAt (List.replicate k Digit.three ++ [Digit.one]) = ⟨⟨1, 2 * (k : ℤ) + 2⟩, ⟨1, 2 * (k : ℤ) + 3⟩⟩ := by
  rw [parentsAt_append_singleton, parentsAt_replicate_three]
  simp [Parents.step, Parents.current, Parents.combine]
  constructor <;> omega

theorem phase_replicate_three (k : ℕ) : phase (List.replicate k Digit.three) = 0 := by
  simp [phase, List.count_replicate]

theorem phase_replicate_three_one (k : ℕ) : phase (List.replicate k Digit.three ++ [Digit.one]) = 1 := by
  simp [phase, List.count_append, List.count_replicate]

/-- The restoration of the seventh copy of a power of three followed by `1` or `3`: the offset is `(−(2k+2), −1)`. -/
theorem alternateRestoration_replicate (k : ℕ) (d : Digit) (hd : d = Digit.one ∨ d = Digit.three) :
    alternateRestoration (List.replicate k Digit.three ++ [d]) .even = (-(2 * (k : ℤ) + 2), -1) := by
  unfold alternateRestoration
  rw [retainedBirth?_even_snoc _ d hd]
  have hall : (List.replicate k Digit.three).all (fun digit => decide (digit = Digit.three)) = true := by
    simp
  simp only [parentsAt_replicate_three, phase_replicate_three, hall, kernelJet, transverseJet]
  simp
  ring

/-- The explicit parents of `3^k` followed by `3`. -/
theorem parentsAt_replicate_three_snoc (k : ℕ) :
    parentsAt (List.replicate k Digit.three ++ [Digit.three]) = ⟨⟨0, 1⟩, ⟨1, 2 * (k : ℤ) + 3⟩⟩ := by
  rw [parentsAt_append_singleton, parentsAt_replicate_three]
  simp [Parents.step, Parents.current, Parents.combine]
  omega

theorem lexLe_zero_of_pos {x : Site} (h : 0 < x.2) : lexLe 0 x := Or.inl (by simpa using h)

/-- Every alternate offset of `3^k 1` is at or above the origin in the lower-left order. -/
theorem lexLe_zero_alternateJets_one (k : ℕ) (j : Fin 6) :
    lexLe 0 (alternateJets (List.replicate k Digit.three ++ [Digit.one]) .odd j).1 := by
  have hpar := parentsAt_replicate_three_one k
  have hph := phase_replicate_three_one k
  unfold lexLe
  fin_cases j <;> simp [alternateJets, hpar, hph, doubleLast, kernelJet, transverseJet] <;> omega

theorem phase_replicate_three_snoc_three (k : ℕ) :
    phase (List.replicate k Digit.three ++ [Digit.three]) = 0 := by
  simp [phase, List.count_append, List.count_replicate]

/-- The seventh copy of `3^k 1`, with its restoration `(−(2k+2), −1)`, is above the origin. -/
theorem lexLe_zero_seventh_one (k : ℕ) :
    lexLe 0 ((seventhAlternateJet (List.replicate k Digit.three) Digit.one .odd).1 + (-(2 * (k : ℤ) + 2), -1)) := by
  have hpar := parentsAt_replicate_three_one k
  have hph := phase_replicate_three_one k
  unfold lexLe
  simp [seventhAlternateJet, hpar, hph, kernelJet, transverseJet]
  omega

/-- The lower-left site of the odd output of `3^k 1` is the origin. -/
theorem alternateOddLowerLeft_replicate_one (k : ℕ) :
    alternateOddLowerLeft (List.replicate k Digit.three ++ [Digit.one]) = 0 := by
  have hl : (List.replicate k Digit.three ++ [Digit.one]).getLast? = some Digit.one := by simp
  have hdl : (List.replicate k Digit.three ++ [Digit.one]).dropLast = List.replicate k Digit.three := by simp
  unfold alternateOddLowerLeft
  simp only [hl, hdl]
  rw [alternateRestoration_replicate k .one (Or.inl rfl)]
  apply foldl_siteLexMin_eq_of_min
  · have h2 : (alternateJets (List.replicate k Digit.three ++ [Digit.one]) .odd 2).1 = 0 := by
      have hpar := parentsAt_replicate_three_one k
      have hph := phase_replicate_three_one k
      simp [alternateJets, hpar, hph, doubleLast, kernelJet, transverseJet]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨2, h2⟩))
  · intro x hx
    simp only [List.mem_cons, List.mem_ofFn] at hx
    rcases hx with rfl | rfl | ⟨j, rfl⟩
    · exact lexLe_zero_alternateJets_one k 0
    · exact lexLe_zero_seventh_one k
    · exact lexLe_zero_alternateJets_one k j

/-- The seventh copy of `3^k·3`, with its restoration `(−(2k+2), −1)`, is above the origin. -/
theorem lexLe_zero_seventh_three (k : ℕ) :
    lexLe 0 ((seventhAlternateJet (List.replicate k Digit.three) Digit.three .odd).1 + (-(2 * (k : ℤ) + 2), -1)) := by
  have hpar := parentsAt_replicate_three_snoc k
  have hph := phase_replicate_three_snoc_three k
  unfold lexLe
  simp [seventhAlternateJet, hpar, hph, kernelJet, transverseJet]

/-- Every alternate offset of `3^k·3` is at or above the origin in the lower-left order. -/
theorem lexLe_zero_alternateJets_three (k : ℕ) (j : Fin 6) :
    lexLe 0 (alternateJets (List.replicate k Digit.three ++ [Digit.three]) .odd j).1 := by
  have hpar := parentsAt_replicate_three_snoc k
  have hph := phase_replicate_three_snoc_three k
  unfold lexLe
  fin_cases j <;> simp [alternateJets, hpar, hph, doubleLast, kernelJet, transverseJet] <;> omega

/-- The lower-left site of the odd output of `3^(k+1)` is the origin. -/
theorem alternateOddLowerLeft_replicate_three (k : ℕ) :
    alternateOddLowerLeft (List.replicate (k + 1) Digit.three) = 0 := by
  rw [List.replicate_succ']
  have hl : (List.replicate k Digit.three ++ [Digit.three]).getLast? = some Digit.three := by simp
  have hdl : (List.replicate k Digit.three ++ [Digit.three]).dropLast = List.replicate k Digit.three := by simp
  unfold alternateOddLowerLeft
  simp only [hl, hdl]
  rw [alternateRestoration_replicate k .three (Or.inr rfl)]
  apply foldl_siteLexMin_eq_of_min
  · have h0 : (alternateJets (List.replicate k Digit.three ++ [Digit.three]) .odd 0).1 = 0 := by
      have hpar := parentsAt_replicate_three_snoc k
      have hph := phase_replicate_three_snoc_three k
      simp [alternateJets, hpar, hph, doubleLast, kernelJet, transverseJet]
    rw [h0]
    exact List.mem_cons_self
  · intro x hx
    simp only [List.mem_cons, List.mem_ofFn] at hx
    rcases hx with rfl | rfl | ⟨j, rfl⟩
    · exact lexLe_zero_alternateJets_three k 0
    · exact lexLe_zero_seventh_three k
    · exact lexLe_zero_alternateJets_three k j

/-! ## The parity of the odd chart -/

/-- **The odd chart has an even coordinate sum.** For every word ending in `1` or `3`, `EvenSite (alternateOddChart w)`: the
transverse offset of the chart is even, and the lower-left site is even (every candidate is an even offset, and the restoration
of the seventh copy is even unless the prefix is a power of three, where the lower-left site is the origin). -/
theorem evenSite_alternateOddChart (w : Word) (hw : w.getLast? = some Digit.one ∨ w.getLast? = some Digit.three) :
    EvenSite (alternateOddChart w) := by
  rcases List.eq_nil_or_concat w with rfl | ⟨p, d, rfl⟩
  · simp at hw
  · simp only [List.concat_eq_append] at hw ⊢
    have hl : (p ++ [d]).getLast? = some d := by simp
    rw [hl] at hw
    have hd : d = Digit.one ∨ d = Digit.three := by
      rcases hw with h | h <;> simp at h <;> simp [h]
    rw [alternateOddChart_eq_delta]
    apply evenSite_sub (evenSite_delta _)
    by_cases hp : ∀ x ∈ p, x = Digit.three
    · obtain ⟨k, rfl⟩ : ∃ k, p = List.replicate k Digit.three := ⟨p.length, List.eq_replicate_iff.mpr ⟨rfl, hp⟩⟩
      rcases hd with rfl | rfl
      · rw [alternateOddLowerLeft_replicate_one]
        exact evenSite_zero
      · rw [← List.replicate_succ', alternateOddLowerLeft_replicate_three]
        exact evenSite_zero
    · exact evenSite_alternateOddLowerLeft_snoc p d hd hp

end FLatticePaper.Construction
