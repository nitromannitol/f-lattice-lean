import FLatticePaper.Tiles.AdmissibleFamilies

/-! Task 51, admissibility, part 5: the families of bottom edges, the base cases, and the final theorem
`bottomEdges_admissible`: both edges of every recursion word are admissible in the sense of
`lemma:almost_square_tiling`. -/

namespace FLatticePaper.Tiles
open Farey

/-! ### Palindromic tokens -/

theorem pal_tok_left (n : ℕ) :
    ([Unit4.one] ++ oneI n ++ [Unit4.one, Unit4.one, Unit4.i]).reverse ++ [Unit4.i]
      = [Unit4.i] ++ ([Unit4.one] ++ oneI n ++ [Unit4.one, Unit4.one, Unit4.i]) := by
  have e : [Unit4.one] ++ oneI n ++ [Unit4.one, Unit4.one, Unit4.i]
      = ([Unit4.one] ++ oneI n ++ [Unit4.one, Unit4.one]) ++ [Unit4.i] := by simp
  rw [e, List.reverse_append, block_rev]
  simp

theorem pal_tok_mid (n : ℕ) :
    ([Unit4.one, Unit4.one, Unit4.i] ++ oneI n ++ [Unit4.one, Unit4.one, Unit4.i]).reverse ++ [Unit4.i]
      = [Unit4.i] ++ ([Unit4.one, Unit4.one, Unit4.i] ++ oneI n ++ [Unit4.one, Unit4.one, Unit4.i]) := by
  have e : [Unit4.one, Unit4.one, Unit4.i] ++ oneI n ++ [Unit4.one, Unit4.one, Unit4.i]
      = ([Unit4.one] ++ oneI (n + 1) ++ [Unit4.one, Unit4.one]) ++ [Unit4.i] := by
    rw [oneI_succ]; simp
  rw [e, List.reverse_append, block_rev]
  simp

/-- The bridge for the words `w0 ++ u`, read through `quadAt`. -/
theorem family_bridge (w0 : Word) (R : F2Word × F2Word) (hH : HOK w0) (u : Word) :
    (bottomFrom w0 u R).1 ++ [Unit4.i]
        = muOf (R.1 ++ [Unit4.i]) (R.2 ++ [Unit4.i]) (quadAt w0 u).childP
    ∧ (bottomFrom w0 u R).2 ++ [Unit4.i]
        = muOf (R.1 ++ [Unit4.i]) (R.2 ++ [Unit4.i]) (quadAt w0 u).childQ := by
  unfold quadAt
  refine bridge (R.1 ++ [Unit4.i]) (R.2 ++ [Unit4.i]) u w0 (initialQuad w0) R hH ?_ ?_
  · exact ⟨rfl, rfl⟩
  · unfold RegInv
    simp [initialQuad, muOf, tokOf]

/-! ### Endpoints of the binary words -/

theorem endpoints_form (X : BinaryWord) (hA : IsAlmostPalindrome X) (f l : Letter)
    (hf : X.head? = some f) (hl : X.getLast? = some l) :
    ∃ M : BinaryWord, M.reverse = M ∧ X = f :: (M ++ [l]) := by
  obtain ⟨f', l', M, hM, rfl⟩ := hA
  have hf' : f' = f := by simpa using hf
  have hl' : l' = l := by
    rw [getLast_wrap M f' l'] at hl
    simpa using hl
  subst hf'
  subst hl'
  exact ⟨M, hM, rfl⟩

/-! ### The (b) and (c) cores -/

theorem muOf_rev_Z' (A B : F2Word) (Z : F2Word) (hA : A.reverse ++ Z = Z ++ A) (hB : B.reverse ++ Z = Z ++ B)
    (M : BinaryWord) (hM : M.reverse = M) : (muOf A B M).reverse ++ Z = Z ++ muOf A B M := by
  have h := muOf_rev_Z A B Z hA hB M
  rw [hM] at h
  exact h

theorem muOf_rev_Y' (A B : F2Word) (Y : F2Word) (hA : Y ++ A.reverse = A ++ Y) (hB : Y ++ B.reverse = B ++ Y)
    (M : BinaryWord) (hM : M.reverse = M) : Y ++ (muOf A B M).reverse = muOf A B M ++ Y := by
  have h := muOf_rev_Y A B Y hA hB M
  rw [hM] at h
  exact h

/-- Case (b): the image of an odd-palindrome shape with `1 (1 i)^m` tokens. -/
theorem core_b (m : ℕ) (A B : F2Word) (hAz : A.reverse ++ [Unit4.i] = [Unit4.i] ++ A)
    (hBz : B.reverse ++ [Unit4.i] = [Unit4.i] ++ B) (hAL : OneI A) (hBL : OneI B)
    (hA : IFollowedBy 1 (A ++ [Unit4.one])) (hB : IFollowedBy 1 (B ++ [Unit4.one]))
    (hA1 : A[0]? = some Unit4.one) (hB1 : B[0]? = some Unit4.one)
    (E : F2Word) (M : BinaryWord) (hM : M.reverse = M) (x : BinaryWord)
    (hShape : muOf A B x = [Unit4.one, Unit4.one, Unit4.i] ++ oneI m ++ [Unit4.one, Unit4.one, Unit4.i]
      ++ muOf A B M ++ [Unit4.one] ++ oneI m ++ [Unit4.one, Unit4.one, Unit4.i])
    (hEx : E ++ [Unit4.i] = muOf A B x) : Admissible E := by
  have hY : (muOf A B M).reverse ++ [Unit4.i] = [Unit4.i] ++ muOf A B M := by
    have h := muOf_rev_Z A B [Unit4.i] hAz hBz M
    rw [hM] at h
    exact h
  have hYL : OneI (muOf A B M) := muOf_letters A B hAL hBL M
  have hE' : E ++ [Unit4.i] = [Unit4.one, Unit4.one, Unit4.i] ++ oneI m ++ [Unit4.one, Unit4.one, Unit4.i]
      ++ muOf A B M ++ [Unit4.one] ++ oneI m ++ [Unit4.one, Unit4.one, Unit4.i] := by
    rw [hEx, hShape]
  -- the padded form for the `IFollowedBy 1` condition
  have hA' : IFollowedBy 1 (A ++ List.replicate 1 Unit4.one) := by simpa using hA
  have hB' : IFollowedBy 1 (B ++ List.replicate 1 Unit4.one) := by simpa using hB
  have hA1' : ∀ j < 1, A[j]? = some Unit4.one := by
    intro j hj
    obtain rfl : j = 0 := by omega
    exact hA1
  have hB1' : ∀ j < 1, B[j]? = some Unit4.one := by
    intro j hj
    obtain rfl : j = 0 := by omega
    exact hB1
  have hEq0 : muOf A B x = ([Unit4.one, Unit4.one, Unit4.i] ++ oneI m ++ [Unit4.one, Unit4.one, Unit4.i]
      ++ muOf A B M ++ [Unit4.one] ++ oneI m ++ [Unit4.one]) ++ List.replicate 1 Unit4.one ++ [Unit4.i] := by
    rw [hShape]; simp
  have hifb0 := ifb_of_muOf_pad 1 A B hA' hB' hA1' hB1' x _ hEq0
  have hEeq : E = ([Unit4.one, Unit4.one, Unit4.i] ++ oneI m ++ [Unit4.one, Unit4.one, Unit4.i]
      ++ muOf A B M ++ [Unit4.one] ++ oneI m ++ [Unit4.one]) ++ List.replicate 1 Unit4.one := by
    apply List.append_cancel_right (bs := [Unit4.i])
    rw [hEx, hEq0]
  have hifb : IFollowedBy 1 E := by rw [hEeq]; exact hifb0
  exact admissible_b_shape m (muOf A B M) E hY hYL hE' hifb

theorem OneI_113 : OneI [Unit4.one, Unit4.one, Unit4.i] := OneI_lit _ (by
  intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx; rcases hx with rfl | rfl | rfl <;> simp)

theorem OneI_1 : OneI [Unit4.one] := OneI_lit _ (by
  intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx; subst hx; simp)

theorem OneI_I : OneI [Unit4.i] := OneI_lit _ (by
  intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx; subst hx; simp)

theorem OneI_mid (n : ℕ) : OneI ([Unit4.one, Unit4.one, Unit4.i] ++ oneI n ++ [Unit4.one, Unit4.one, Unit4.i]) :=
  OneI_append _ _ (OneI_append _ _ OneI_113 (oneI_letters n)) OneI_113

theorem OneI_left (n : ℕ) : OneI ([Unit4.one] ++ oneI n ++ [Unit4.one, Unit4.one, Unit4.i]) :=
  OneI_append _ _ (OneI_append _ _ OneI_1 (oneI_letters n)) OneI_113

theorem OneI_c (n : ℕ) :
    OneI (List.replicate (2 * n + 1) Unit4.one ++ [Unit4.i] ++ (List.replicate (2 * n + 3) Unit4.one ++ [Unit4.i])) :=
  OneI_append _ _ (OneI_append _ _ (OneI_rep _) OneI_I) (OneI_append _ _ (OneI_rep _) OneI_I)


/-! ### Replicate arithmetic and the token lemmas -/

theorem OneI_cons (x : Unit4) (w : F2Word) (hx : x = Unit4.one ∨ x = Unit4.i) (hw : OneI w) :
    OneI (x :: w) := by
  intro y hy
  rcases List.mem_cons.mp hy with h | h
  · rw [h]; exact hx
  · exact hw y h

theorem admissible_of_palindrome_core (E : F2Word) (hE : E.reverse = E) (hmono : OneI E)
    (hh : E.head? = some Unit4.one) (hl : E.getLast? = some Unit4.one) : Admissible E :=
  ⟨hmono, hh, hl, Or.inl hE⟩

theorem rep_succ1 (a : ℕ) : List.replicate (a + 1) Unit4.one = [Unit4.one] ++ List.replicate a Unit4.one := by
  rw [List.replicate_succ]; rfl

theorem rep_add3 (a : ℕ) :
    List.replicate (a + 3) Unit4.one = List.replicate a Unit4.one ++ [Unit4.one, Unit4.one, Unit4.one] := by
  rw [List.replicate_add]; rfl

theorem oneOne_eq (n : ℕ) : oneOne n = List.replicate (2 * n) Unit4.one := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold oneOne at ih ⊢
    rw [List.replicate_succ, List.flatten_cons, ih]
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, List.replicate_succ, List.replicate_succ]
    rfl

theorem oneOne_letters (n : ℕ) : OneI (oneOne n) := by
  rw [oneOne_eq]
  exact OneI_rep _

/-- The tokens of `2^k`. -/
theorem baseTwo_tokens (k : ℕ) :
    (baseTwoEdges k).1 ++ [Unit4.i]
        = [Unit4.one, Unit4.one, Unit4.i] ++ oneI (2 * k) ++ [Unit4.one, Unit4.one, Unit4.i]
    ∧ (baseTwoEdges k).2 ++ [Unit4.i] = [Unit4.one] ++ oneI (2 * k) ++ [Unit4.one, Unit4.one, Unit4.i] := by
  constructor
  · unfold baseTwoEdges; rw [oneI_succ]; simp
  · unfold baseTwoEdges; simp

theorem baseTwo_tokens_succ (k : ℕ) :
    (baseTwoEdges (k + 1)).2 ++ [Unit4.i]
      = [Unit4.one, Unit4.one, Unit4.i] ++ oneI (2 * k + 1) ++ [Unit4.one, Unit4.one, Unit4.i] := by
  unfold baseTwoEdges
  rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, oneI_succ (2 * k + 1)]
  simp

theorem baseTwo_tokens_first (k : ℕ) :
    (baseTwoEdges k).1 ++ [Unit4.i] = [Unit4.one] ++ oneI (2 * k + 1) ++ [Unit4.one, Unit4.one, Unit4.i] := by
  unfold baseTwoEdges; simp

/-- The tokens of `3^n`: `p = 1^{2n+1} i 1^{2n+3} i`, `q = 1^{2n+3} i`. -/
theorem baseThree_tokens (n : ℕ) :
    (baseThreeEdges n).1 ++ [Unit4.i]
        = List.replicate (2 * n + 1) Unit4.one ++ [Unit4.i] ++ (List.replicate (2 * n + 3) Unit4.one ++ [Unit4.i])
    ∧ (baseThreeEdges n).2 ++ [Unit4.i] = List.replicate (2 * n + 3) Unit4.one ++ [Unit4.i] := by
  constructor
  · unfold baseThreeEdges
    dsimp only
    have h1 : List.replicate (2 * n + 1) Unit4.one = List.replicate (2 * n) Unit4.one ++ [Unit4.one] :=
      List.replicate_succ'
    have h3 : List.replicate (2 * n + 3) Unit4.one = List.replicate (2 * n + 2) Unit4.one ++ [Unit4.one] :=
      List.replicate_succ'
    rw [oneOne_eq, oneOne_eq, show 2 * (n + 1) = 2 * n + 2 by ring, h1, h3]
    simp
  · unfold baseThreeEdges
    dsimp only
    have h3 : List.replicate (2 * n + 3) Unit4.one = [Unit4.one] ++ List.replicate (2 * n + 2) Unit4.one :=
      List.replicate_succ
    rw [oneOne_eq, show 2 * (n + 1) = 2 * n + 2 by ring, h3]

/-- Case (c) for the even families: `x = q M p` with `q = 1^{a+1} i`, `p = 1^{a+1} i 1^{a+3} i`. -/
theorem admissible_c4_shape (a : ℕ) (Y E : F2Word)
    (hY : List.replicate (a + 1) Unit4.one ++ Y.reverse = Y ++ List.replicate (a + 1) Unit4.one)
    (hYL : OneI Y)
    (hE : E ++ [Unit4.i] = List.replicate (a + 1) Unit4.one ++ [Unit4.i] ++ Y ++ List.replicate (a + 1) Unit4.one
      ++ [Unit4.i] ++ (List.replicate (a + 3) Unit4.one ++ [Unit4.i]))
    (hifb : IFollowedBy 3 E) : Admissible E := by
  have hE' : E = [Unit4.one] ++ (List.replicate a Unit4.one ++ [Unit4.i] ++ Y ++ List.replicate (a + 1) Unit4.one
      ++ [Unit4.i] ++ List.replicate a Unit4.one) ++ [Unit4.one, Unit4.one, Unit4.one] := by
    apply List.append_cancel_right (bs := [Unit4.i])
    rw [hE, rep_succ1 a, rep_add3 a]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hR : OneI [Unit4.one] := OneI_1
  have hI : OneI [Unit4.i] := OneI_I
  have hO3 : OneI [Unit4.one, Unit4.one, Unit4.one] := OneI_lit _ (by
    intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx; rcases hx with rfl | rfl | rfl <;> simp)
  have hwt : OneI (List.replicate a Unit4.one ++ [Unit4.i] ++ Y ++ List.replicate (a + 1) Unit4.one
      ++ [Unit4.i] ++ List.replicate a Unit4.one) :=
    OneI_append _ _ (OneI_append _ _ (OneI_append _ _ (OneI_append _ _ (OneI_append _ _ (OneI_rep a) hI) hYL)
      (OneI_rep _)) hI) (OneI_rep a)
  apply admissible_of_c E (List.replicate a Unit4.one ++ [Unit4.i] ++ Y ++ List.replicate (a + 1) Unit4.one
      ++ [Unit4.i] ++ List.replicate a Unit4.one) hE' (pal_c_Y a (a + 1) Y hY) hifb
  rw [hE']
  exact OneI_append _ _ (OneI_append _ _ hR hwt) hO3
theorem zA_id (n : ℕ) :
    (List.replicate (2 * n + 1) Unit4.one ++ [Unit4.i] ++ (List.replicate (2 * n + 3) Unit4.one ++ [Unit4.i])).reverse
        ++ ([Unit4.i] ++ (List.replicate (2 * n + 3) Unit4.one ++ [Unit4.i]))
      = ([Unit4.i] ++ (List.replicate (2 * n + 3) Unit4.one ++ [Unit4.i]))
        ++ (List.replicate (2 * n + 1) Unit4.one ++ [Unit4.i] ++ (List.replicate (2 * n + 3) Unit4.one ++ [Unit4.i])) := by
  simp only [List.reverse_append, List.reverse_replicate, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.append_assoc]

theorem zB_id (n : ℕ) :
    (List.replicate (2 * n + 3) Unit4.one ++ [Unit4.i]).reverse ++ ([Unit4.i] ++ (List.replicate (2 * n + 3) Unit4.one ++ [Unit4.i]))
      = ([Unit4.i] ++ (List.replicate (2 * n + 3) Unit4.one ++ [Unit4.i])) ++ (List.replicate (2 * n + 3) Unit4.one ++ [Unit4.i]) := by
  simp only [List.reverse_append, List.reverse_replicate, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.append_assoc]

/-- The (c)-core for the odd families `F3`: `x = p M q` with the `3`-tokens `p = 1^{a+1} i 1^{a+3} i`, `q = 1^{a+3} i`. -/
theorem core_c3 (a : ℕ) (A B : F2Word)
    (hAz : A.reverse ++ ([Unit4.i] ++ (List.replicate (a + 3) Unit4.one ++ [Unit4.i]))
      = ([Unit4.i] ++ (List.replicate (a + 3) Unit4.one ++ [Unit4.i])) ++ A)
    (hBz : B.reverse ++ ([Unit4.i] ++ (List.replicate (a + 3) Unit4.one ++ [Unit4.i]))
      = ([Unit4.i] ++ (List.replicate (a + 3) Unit4.one ++ [Unit4.i])) ++ B)
    (hAL : OneI A) (hBL : OneI B)
    (hA : IFollowedBy 3 (A ++ List.replicate 3 Unit4.one)) (hB : IFollowedBy 3 (B ++ List.replicate 3 Unit4.one))
    (hA1 : ∀ j < 3, A[j]? = some Unit4.one) (hB1 : ∀ j < 3, B[j]? = some Unit4.one)
    (E : F2Word) (M : BinaryWord) (hM : M.reverse = M) (x : BinaryWord)
    (hShape : muOf A B x = List.replicate (a + 1) Unit4.one ++ [Unit4.i]
      ++ (List.replicate (a + 3) Unit4.one ++ [Unit4.i]) ++ muOf A B M ++ List.replicate (a + 3) Unit4.one ++ [Unit4.i])
    (hEx : E ++ [Unit4.i] = muOf A B x) : Admissible E := by
  have hY := muOf_rev_Z' A B _ hAz hBz M hM
  have hYL : OneI (muOf A B M) := muOf_letters A B hAL hBL M
  have hE' : E ++ [Unit4.i] = List.replicate (a + 1) Unit4.one ++ [Unit4.i]
      ++ (List.replicate (a + 3) Unit4.one ++ [Unit4.i]) ++ muOf A B M ++ List.replicate (a + 3) Unit4.one ++ [Unit4.i] := by
    rw [hEx, hShape]
  have hEq0 : muOf A B x = ([Unit4.one] ++ (List.replicate a Unit4.one ++ [Unit4.i]
      ++ (List.replicate (a + 3) Unit4.one ++ [Unit4.i]) ++ muOf A B M ++ List.replicate a Unit4.one))
      ++ List.replicate 3 Unit4.one ++ [Unit4.i] := by
    rw [hShape, rep_succ1 a, rep_add3 a, show List.replicate 3 Unit4.one = [Unit4.one, Unit4.one, Unit4.one] from rfl]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hifb0 := ifb_of_muOf_pad 3 A B hA hB hA1 hB1 x _ hEq0
  have hEeq : E = ([Unit4.one] ++ (List.replicate a Unit4.one ++ [Unit4.i]
      ++ (List.replicate (a + 3) Unit4.one ++ [Unit4.i]) ++ muOf A B M ++ List.replicate a Unit4.one))
      ++ List.replicate 3 Unit4.one := by
    apply List.append_cancel_right (bs := [Unit4.i])
    rw [hEx, hEq0]
  have hifb : IFollowedBy 3 E := by rw [hEeq]; exact hifb0
  exact admissible_c3_shape a (muOf A B M) E hY hYL hE' hifb

/-- The (c)-core for the even families `F4`: `x = q M p` with the tokens `q = 1^{a+1} i`, `p = 1^{a+1} i 1^{a+3} i`. -/
theorem core_c4 (a : ℕ) (A B : F2Word)
    (hAY : List.replicate (a + 1) Unit4.one ++ A.reverse = A ++ List.replicate (a + 1) Unit4.one)
    (hBY : List.replicate (a + 1) Unit4.one ++ B.reverse = B ++ List.replicate (a + 1) Unit4.one)
    (hAL : OneI A) (hBL : OneI B)
    (hA : IFollowedBy 3 (A ++ List.replicate 3 Unit4.one)) (hB : IFollowedBy 3 (B ++ List.replicate 3 Unit4.one))
    (hA1 : ∀ j < 3, A[j]? = some Unit4.one) (hB1 : ∀ j < 3, B[j]? = some Unit4.one)
    (E : F2Word) (M : BinaryWord) (hM : M.reverse = M) (x : BinaryWord)
    (hShape : muOf A B x = List.replicate (a + 1) Unit4.one ++ [Unit4.i] ++ muOf A B M
      ++ List.replicate (a + 1) Unit4.one ++ [Unit4.i] ++ (List.replicate (a + 3) Unit4.one ++ [Unit4.i]))
    (hEx : E ++ [Unit4.i] = muOf A B x) : Admissible E := by
  have hY := muOf_rev_Y' A B (List.replicate (a + 1) Unit4.one) hAY hBY M hM
  have hYL : OneI (muOf A B M) := muOf_letters A B hAL hBL M
  have hE' : E ++ [Unit4.i] = List.replicate (a + 1) Unit4.one ++ [Unit4.i] ++ muOf A B M
      ++ List.replicate (a + 1) Unit4.one ++ [Unit4.i] ++ (List.replicate (a + 3) Unit4.one ++ [Unit4.i]) := by
    rw [hEx, hShape]
  have hEq0 : muOf A B x = ([Unit4.one] ++ (List.replicate a Unit4.one ++ [Unit4.i] ++ muOf A B M
      ++ List.replicate (a + 1) Unit4.one ++ [Unit4.i] ++ List.replicate a Unit4.one))
      ++ List.replicate 3 Unit4.one ++ [Unit4.i] := by
    rw [hShape, rep_succ1 a, rep_add3 a, show List.replicate 3 Unit4.one = [Unit4.one, Unit4.one, Unit4.one] from rfl]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hifb0 := ifb_of_muOf_pad 3 A B hA hB hA1 hB1 x _ hEq0
  have hEeq : E = ([Unit4.one] ++ (List.replicate a Unit4.one ++ [Unit4.i] ++ muOf A B M
      ++ List.replicate (a + 1) Unit4.one ++ [Unit4.i] ++ List.replicate a Unit4.one))
      ++ List.replicate 3 Unit4.one := by
    apply List.append_cancel_right (bs := [Unit4.i])
    rw [hEx, hEq0]
  have hifb : IFollowedBy 3 E := by rw [hEeq]; exact hifb0
  exact admissible_c4_shape a (muOf A B M) E hY hYL hE' hifb

/-! ### The four families of recursion words -/

theorem count_one_fam (k : ℕ) (w : Word) (h : w = List.replicate k Digit.two ++ [Digit.one]) :
    w.count Digit.one % 2 = 1 := by
  subst h
  simp [List.count_append, List.count_replicate]

theorem count_one_even_fam (k : ℕ) (w : Word) (h : w = List.replicate k Digit.two ++ [Digit.three]) :
    w.count Digit.one % 2 = 0 := by
  subst h
  simp [List.count_append, List.count_replicate]

theorem fam1 (k : ℕ) (rest : Word) :
    Admissible (bottomFrom (List.replicate k Digit.two ++ [Digit.one]) rest (baseTwoEdges k)).1
    ∧ Admissible (bottomFrom (List.replicate k Digit.two ++ [Digit.one]) rest (baseTwoEdges k)).2 := by
  have hH : HOK (List.replicate k Digit.two ++ [Digit.one]) := Or.inl ⟨Digit.one, by simp, rfl⟩
  obtain ⟨h1, h2⟩ := family_bridge (List.replicate k Digit.two ++ [Digit.one]) (baseTwoEdges k) hH rest
  obtain ⟨hA, hB⟩ := baseTwo_tokens k
  have hpar := count_one_fam k _ rfl
  obtain ⟨hAP1, hAP2⟩ := almost_palindrome_one (List.replicate k Digit.two ++ [Digit.one]) rest
  obtain ⟨hP1, hP2, hQ1, hQ2⟩ := (almost_palindrome_two (List.replicate k Digit.two ++ [Digit.one]) rest).2 hpar
  obtain ⟨Mp, hMp, hXp⟩ := endpoints_form _ hAP1 Letter.p Letter.q hP1 hP2
  obtain ⟨Mq, hMq, hXq⟩ := endpoints_form _ hAP2 Letter.p Letter.q hQ1 hQ2
  have hShape : ∀ M : BinaryWord, muOf ((baseTwoEdges k).1 ++ [Unit4.i]) ((baseTwoEdges k).2 ++ [Unit4.i])
      (Letter.p :: (M ++ [Letter.q]))
      = [Unit4.one, Unit4.one, Unit4.i] ++ oneI (2 * k) ++ [Unit4.one, Unit4.one, Unit4.i]
        ++ muOf ((baseTwoEdges k).1 ++ [Unit4.i]) ((baseTwoEdges k).2 ++ [Unit4.i]) M ++ [Unit4.one]
        ++ oneI (2 * k) ++ [Unit4.one, Unit4.one, Unit4.i] := by
    intro M
    simp only [muOf, tokOf, muOf_append]
    rw [hA, hB]
    simp only [List.append_assoc, List.append_nil]
  constructor
  · exact core_b (2 * k) ((baseTwoEdges k).1 ++ [Unit4.i]) ((baseTwoEdges k).2 ++ [Unit4.i])
      (by rw [hA]; exact pal_tok_mid _) (by rw [hB]; exact pal_tok_left _)
      (by rw [hA]; exact OneI_mid _) (by rw [hB]; exact OneI_left _)
      (by rw [hA]; exact ifb_tok_b_two _) (by rw [hB]; exact ifb_tok_b_one _)
      (by rw [hA]; simp) (by rw [hB]; simp) _ Mp hMp _ (hShape Mp)
      (by rw [h1, hXp])
  · exact core_b (2 * k) ((baseTwoEdges k).1 ++ [Unit4.i]) ((baseTwoEdges k).2 ++ [Unit4.i])
      (by rw [hA]; exact pal_tok_mid _) (by rw [hB]; exact pal_tok_left _)
      (by rw [hA]; exact OneI_mid _) (by rw [hB]; exact OneI_left _)
      (by rw [hA]; exact ifb_tok_b_two _) (by rw [hB]; exact ifb_tok_b_one _)
      (by rw [hA]; simp) (by rw [hB]; simp) _ Mq hMq _ (hShape Mq)
      (by rw [h2, hXq])

theorem count_one_three_one (k : ℕ) : (List.replicate k Digit.three ++ [Digit.one]).count Digit.one % 2 = 1 := by
  simp [List.count_append, List.count_replicate]

theorem count_one_three_two (k : ℕ) : (List.replicate k Digit.three ++ [Digit.two]).count Digit.one % 2 = 0 := by
  simp [List.count_append, List.count_replicate]

theorem prefixEdges_threes_snd (j : ℕ) (a b : F2Word) :
    (prefixEdges (List.replicate j Digit.three) a b).2 = (baseThreeEdges j).2 := by
  cases j with
  | zero => simp [prefixEdges, allTwos, baseTwoEdges, baseThreeEdges, oneI, oneOne]
  | succ j => rw [prefixEdges_threes (j + 1) (by omega)]

theorem bottomEdges_twos (n : ℕ) : bottomEdges (List.replicate n Digit.two) = baseTwoEdges n := by
  unfold bottomEdges
  obtain ⟨r, h⟩ := bottomFrom_append (List.replicate n Digit.two) [] [] ([], [])
  simp only [List.append_nil, List.nil_append] at h
  rw [h]
  simp [bottomFrom, prefixEdges_twos]

theorem bottomEdges_threes (n : ℕ) (hn : 1 ≤ n) : bottomEdges (List.replicate n Digit.three) = baseThreeEdges n := by
  unfold bottomEdges
  obtain ⟨r, h⟩ := bottomFrom_append (List.replicate n Digit.three) [] [] ([], [])
  simp only [List.append_nil, List.nil_append] at h
  rw [h]
  simp [bottomFrom, prefixEdges_threes n hn]

theorem bottomEdges_fam1 (k : ℕ) (rest : Word) :
    bottomEdges (List.replicate k Digit.two ++ Digit.one :: rest)
      = bottomFrom (List.replicate k Digit.two ++ [Digit.one]) rest (baseTwoEdges k) := by
  unfold bottomEdges
  obtain ⟨r, h⟩ := bottomFrom_append (List.replicate k Digit.two) [] (Digit.one :: rest) ([], [])
  simp only [List.nil_append] at h
  rw [h]
  simp [bottomFrom, prefixEdges_twos, updateRegs]

theorem bottomEdges_fam2 (k : ℕ) (rest : Word) :
    bottomEdges (List.replicate (k + 1) Digit.two ++ Digit.three :: rest)
      = bottomFrom (List.replicate (k + 1) Digit.two ++ [Digit.three]) rest
          ((baseTwoEdges k).1, (baseTwoEdges (k + 1)).2) := by
  unfold bottomEdges
  have h := bottomFrom_two_run k 0 (Digit.three :: rest) ([], [])
  simp only [List.replicate_zero, zero_add] at h
  rw [h]
  simp [bottomFrom, prefixEdges_twos, updateRegs]

theorem bottomEdges_fam3 (j : ℕ) (rest : Word) :
    bottomEdges (List.replicate (j + 1) Digit.three ++ Digit.one :: rest)
      = bottomFrom (List.replicate (j + 1) Digit.three ++ [Digit.one]) rest (baseThreeEdges (j + 1)) := by
  unfold bottomEdges
  obtain ⟨r, h⟩ := bottomFrom_append (List.replicate (j + 1) Digit.three) [] (Digit.one :: rest) ([], [])
  simp only [List.nil_append] at h
  rw [h]
  simp [bottomFrom, prefixEdges_threes (j + 1) (by omega), updateRegs]

theorem bottomEdges_fam4 (j : ℕ) (rest : Word) :
    bottomEdges (List.replicate (j + 1) Digit.three ++ Digit.two :: rest)
      = bottomFrom (List.replicate (j + 1) Digit.three ++ [Digit.two]) rest
          ((baseThreeEdges (j + 1)).1, (baseThreeEdges j).2) := by
  unfold bottomEdges
  have e : List.replicate (j + 1) Digit.three ++ Digit.two :: rest
      = List.replicate j Digit.three ++ (Digit.three :: Digit.two :: rest) := by
    rw [List.replicate_succ', List.append_assoc]; rfl
  obtain ⟨r, h⟩ := bottomFrom_append (List.replicate j Digit.three) [] (Digit.three :: Digit.two :: rest) ([], [])
  simp only [List.nil_append] at h
  rw [e, h]
  simp only [bottomFrom, updateRegs]
  rw [prefixEdges_threes_snd]
  have e2 : List.replicate j Digit.three ++ [Digit.three] = List.replicate (j + 1) Digit.three :=
    List.replicate_succ'.symm
  simp only [e2]
  simp [prefixEdges_threes (j + 1) (by omega)]

/-- The base cases: the edges of `2^n` are palindromes. -/
theorem adm_base2 (n : ℕ) : Admissible (baseTwoEdges n).1 ∧ Admissible (baseTwoEdges n).2 := by
  constructor
  · apply admissible_of_palindrome_core
    · unfold baseTwoEdges; exact block_rev _
    · unfold baseTwoEdges
      exact OneI_append _ _ (OneI_append _ _ OneI_1 (oneI_letters _)) (OneI_lit _ (by
        intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx; rcases hx with rfl | rfl <;> simp))
    · unfold baseTwoEdges; simp
    · unfold baseTwoEdges; dsimp only; rw [List.getLast?_append_of_ne_nil _ (by simp)]; simp
  · apply admissible_of_palindrome_core
    · unfold baseTwoEdges; exact block_rev _
    · unfold baseTwoEdges
      exact OneI_append _ _ (OneI_append _ _ OneI_1 (oneI_letters _)) (OneI_lit _ (by
        intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx; rcases hx with rfl | rfl <;> simp))
    · unfold baseTwoEdges; simp
    · unfold baseTwoEdges; dsimp only; rw [List.getLast?_append_of_ne_nil _ (by simp)]; simp

theorem adm_base3 (n : ℕ) (hn : 1 ≤ n) : Admissible (baseThreeEdges n).1 ∧ Admissible (baseThreeEdges n).2 := by
  constructor
  · have hE : (baseThreeEdges n).1 = List.replicate (2 * n + 1) Unit4.one
        ++ (Unit4.i :: List.replicate (2 * n + 3) Unit4.one) := by
      apply List.append_cancel_right (bs := [Unit4.i])
      rw [(baseThree_tokens n).1]
      simp
    have hE' : (baseThreeEdges n).1 = [Unit4.one] ++ (List.replicate (2 * n) Unit4.one ++ [Unit4.i]
        ++ List.replicate (2 * n) Unit4.one) ++ [Unit4.one, Unit4.one, Unit4.one] := by
      rw [hE, rep_succ1 (2 * n), rep_add3 (2 * n)]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    have hifb : IFollowedBy 3 (baseThreeEdges n).1 := by
      rw [hE, ifb_rep_prefix, ifb_cons_i]
      exact ⟨fun m hm => by
        simp only [List.getElem?_replicate]
        rw [if_pos (show m < 2 * n + 3 by omega)], ifb_replicate 3 _⟩
    have hmono : OneI (baseThreeEdges n).1 := by
      rw [hE]
      exact OneI_append _ _ (OneI_rep _) (OneI_cons _ _ (Or.inr rfl) (OneI_rep _))
    exact admissible_of_c _ (List.replicate (2 * n) Unit4.one ++ [Unit4.i] ++ List.replicate (2 * n) Unit4.one)
      hE' (by simp [List.reverse_replicate]) hifb hmono
  · apply admissible_of_palindrome_core
    · unfold baseThreeEdges
      dsimp only
      rw [oneOne_eq, ← rep_succ1 (2 * (n + 1))]
      simp [List.reverse_replicate]
    · unfold baseThreeEdges
      dsimp only
      rw [oneOne_eq]
      exact OneI_append _ _ OneI_1 (OneI_rep _)
    · unfold baseThreeEdges
      dsimp only
      rw [oneOne_eq, ← rep_succ1 (2 * (n + 1))]
      rfl
    · unfold baseThreeEdges
      dsimp only
      rw [oneOne_eq, ← rep_succ1 (2 * (n + 1))]
      rw [List.replicate_succ', List.getLast?_concat]

theorem zY_A (a : ℕ) : List.replicate (a + 1) Unit4.one ++ (List.replicate (a + 1) Unit4.one ++ [Unit4.i]
      ++ (List.replicate (a + 3) Unit4.one ++ [Unit4.i])).reverse
    = (List.replicate (a + 1) Unit4.one ++ [Unit4.i] ++ (List.replicate (a + 3) Unit4.one ++ [Unit4.i]))
      ++ List.replicate (a + 1) Unit4.one := by
  simp only [List.reverse_append, List.reverse_replicate, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.append_assoc]

theorem zY_B (a : ℕ) : List.replicate (a + 1) Unit4.one ++ (List.replicate (a + 1) Unit4.one ++ [Unit4.i]).reverse
    = (List.replicate (a + 1) Unit4.one ++ [Unit4.i]) ++ List.replicate (a + 1) Unit4.one := by
  simp only [List.reverse_append, List.reverse_replicate, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.append_assoc]

/-! ### The families `F2`, `F3`, `F4` -/

theorem fam2 (k : ℕ) (rest : Word) :
    Admissible (bottomFrom (List.replicate (k + 1) Digit.two ++ [Digit.three]) rest
      ((baseTwoEdges k).1, (baseTwoEdges (k + 1)).2)).1
    ∧ Admissible (bottomFrom (List.replicate (k + 1) Digit.two ++ [Digit.three]) rest
      ((baseTwoEdges k).1, (baseTwoEdges (k + 1)).2)).2 := by
  have hH : HOK (List.replicate (k + 1) Digit.two ++ [Digit.three]) :=
    Or.inr ⟨⟨Digit.two, by simp, rfl⟩, ⟨Digit.three, by simp, rfl⟩⟩
  obtain ⟨h1, h2⟩ := family_bridge _ ((baseTwoEdges k).1, (baseTwoEdges (k + 1)).2) hH rest
  dsimp only at h1 h2
  obtain ⟨hA, hB⟩ := And.intro (baseTwo_tokens_first k) (baseTwo_tokens_succ k)
  have hpar := count_one_even_fam (k + 1) _ rfl
  obtain ⟨hAP1, hAP2⟩ := almost_palindrome_one (List.replicate (k + 1) Digit.two ++ [Digit.three]) rest
  obtain ⟨hP1, hP2, hQ1, hQ2⟩ :=
    (almost_palindrome_two (List.replicate (k + 1) Digit.two ++ [Digit.three]) rest).1 hpar
  obtain ⟨Mp, hMp, hXp⟩ := endpoints_form _ hAP1 Letter.q Letter.p hP1 hP2
  obtain ⟨Mq, hMq, hXq⟩ := endpoints_form _ hAP2 Letter.q Letter.p hQ1 hQ2
  have hShape : ∀ M : BinaryWord,
      muOf ((baseTwoEdges k).1 ++ [Unit4.i]) ((baseTwoEdges (k + 1)).2 ++ [Unit4.i]) (Letter.q :: (M ++ [Letter.p]))
        = [Unit4.one, Unit4.one, Unit4.i] ++ oneI (2 * k + 1) ++ [Unit4.one, Unit4.one, Unit4.i]
          ++ muOf ((baseTwoEdges k).1 ++ [Unit4.i]) ((baseTwoEdges (k + 1)).2 ++ [Unit4.i]) M ++ [Unit4.one]
          ++ oneI (2 * k + 1) ++ [Unit4.one, Unit4.one, Unit4.i] := by
    intro M
    simp only [muOf, tokOf, muOf_append]
    rw [hA, hB]
    simp only [List.append_assoc, List.append_nil]
  have hAz : ((baseTwoEdges k).1 ++ [Unit4.i]).reverse ++ [Unit4.i] = [Unit4.i] ++ ((baseTwoEdges k).1 ++ [Unit4.i]) := by
    rw [hA]; exact pal_tok_left _
  have hBz : ((baseTwoEdges (k + 1)).2 ++ [Unit4.i]).reverse ++ [Unit4.i]
      = [Unit4.i] ++ ((baseTwoEdges (k + 1)).2 ++ [Unit4.i]) := by
    rw [hB]; exact pal_tok_mid _
  constructor
  · exact core_b (2 * k + 1) ((baseTwoEdges k).1 ++ [Unit4.i]) ((baseTwoEdges (k + 1)).2 ++ [Unit4.i])
      hAz hBz (by rw [hA]; exact OneI_left _) (by rw [hB]; exact OneI_mid _)
      (by rw [hA]; exact ifb_tok_b_one _) (by rw [hB]; exact ifb_tok_b_two _)
      (by rw [hA]; simp) (by rw [hB]; simp) _ Mp hMp _ (hShape Mp) (by rw [h1, hXp])
  · exact core_b (2 * k + 1) ((baseTwoEdges k).1 ++ [Unit4.i]) ((baseTwoEdges (k + 1)).2 ++ [Unit4.i])
      hAz hBz (by rw [hA]; exact OneI_left _) (by rw [hB]; exact OneI_mid _)
      (by rw [hA]; exact ifb_tok_b_one _) (by rw [hB]; exact ifb_tok_b_two _)
      (by rw [hA]; simp) (by rw [hB]; simp) _ Mq hMq _ (hShape Mq) (by rw [h2, hXq])

theorem fam3 (j : ℕ) (rest : Word) :
    Admissible (bottomFrom (List.replicate (j + 1) Digit.three ++ [Digit.one]) rest (baseThreeEdges (j + 1))).1
    ∧ Admissible (bottomFrom (List.replicate (j + 1) Digit.three ++ [Digit.one]) rest (baseThreeEdges (j + 1))).2 := by
  have hH : HOK (List.replicate (j + 1) Digit.three ++ [Digit.one]) := Or.inl ⟨Digit.one, by simp, rfl⟩
  obtain ⟨h1, h2⟩ := family_bridge _ (baseThreeEdges (j + 1)) hH rest
  obtain ⟨hA, hB⟩ := baseThree_tokens (j + 1)
  have hpar := count_one_three_one (j + 1)
  obtain ⟨hAP1, hAP2⟩ := almost_palindrome_one (List.replicate (j + 1) Digit.three ++ [Digit.one]) rest
  obtain ⟨hP1, hP2, hQ1, hQ2⟩ :=
    (almost_palindrome_two (List.replicate (j + 1) Digit.three ++ [Digit.one]) rest).2 hpar
  obtain ⟨Mp, hMp, hXp⟩ := endpoints_form _ hAP1 Letter.p Letter.q hP1 hP2
  obtain ⟨Mq, hMq, hXq⟩ := endpoints_form _ hAP2 Letter.p Letter.q hQ1 hQ2
  have hShape : ∀ M : BinaryWord,
      muOf ((baseThreeEdges (j + 1)).1 ++ [Unit4.i]) ((baseThreeEdges (j + 1)).2 ++ [Unit4.i]) (Letter.p :: (M ++ [Letter.q]))
        = List.replicate (2 * (j + 1) + 1) Unit4.one ++ [Unit4.i]
          ++ (List.replicate (2 * (j + 1) + 3) Unit4.one ++ [Unit4.i])
          ++ muOf ((baseThreeEdges (j + 1)).1 ++ [Unit4.i]) ((baseThreeEdges (j + 1)).2 ++ [Unit4.i]) M
          ++ List.replicate (2 * (j + 1) + 3) Unit4.one ++ [Unit4.i] := by
    intro M
    simp only [muOf, tokOf, muOf_append]
    rw [hA, hB]
    simp only [List.append_assoc, List.append_nil]
  have hAz : ((baseThreeEdges (j + 1)).1 ++ [Unit4.i]).reverse ++ ([Unit4.i] ++ (List.replicate (2 * (j + 1) + 3) Unit4.one
      ++ [Unit4.i])) = ([Unit4.i] ++ (List.replicate (2 * (j + 1) + 3) Unit4.one ++ [Unit4.i])) ++ ((baseThreeEdges (j + 1)).1 ++ [Unit4.i]) := by
    rw [hA]; exact zA_id (j + 1)
  have hBz : ((baseThreeEdges (j + 1)).2 ++ [Unit4.i]).reverse ++ ([Unit4.i] ++ (List.replicate (2 * (j + 1) + 3) Unit4.one
      ++ [Unit4.i])) = ([Unit4.i] ++ (List.replicate (2 * (j + 1) + 3) Unit4.one ++ [Unit4.i])) ++ ((baseThreeEdges (j + 1)).2 ++ [Unit4.i]) := by
    rw [hB]; exact zB_id (j + 1)
  have hA3 : IFollowedBy 3 (((baseThreeEdges (j + 1)).1 ++ [Unit4.i]) ++ List.replicate 3 Unit4.one) := by
    rw [hA]; exact ifb3_tok_A _ _ (by omega)
  have hB3 : IFollowedBy 3 (((baseThreeEdges (j + 1)).2 ++ [Unit4.i]) ++ List.replicate 3 Unit4.one) := by
    rw [hB]; exact ifb3_tok_B _
  have hA1 : ∀ m < 3, ((baseThreeEdges (j + 1)).1 ++ [Unit4.i])[m]? = some Unit4.one := by
    intro m hm
    rw [hA]
    simp only [List.append_assoc]
    exact rep_prefix_ones _ 3 (by omega) _ m hm
  have hB1 : ∀ m < 3, ((baseThreeEdges (j + 1)).2 ++ [Unit4.i])[m]? = some Unit4.one := by
    intro m hm
    rw [hB]
    exact rep_prefix_ones _ 3 (by omega) _ m hm
  constructor
  · exact core_c3 (2 * (j + 1)) ((baseThreeEdges (j + 1)).1 ++ [Unit4.i]) ((baseThreeEdges (j + 1)).2 ++ [Unit4.i])
      hAz hBz (by rw [hA]; exact OneI_c _) (by rw [hB]; exact OneI_append _ _ (OneI_rep _) OneI_I)
      hA3 hB3 hA1 hB1 _ Mp hMp _ (hShape Mp) (by rw [h1, hXp])
  · exact core_c3 (2 * (j + 1)) ((baseThreeEdges (j + 1)).1 ++ [Unit4.i]) ((baseThreeEdges (j + 1)).2 ++ [Unit4.i])
      hAz hBz (by rw [hA]; exact OneI_c _) (by rw [hB]; exact OneI_append _ _ (OneI_rep _) OneI_I)
      hA3 hB3 hA1 hB1 _ Mq hMq _ (hShape Mq) (by rw [h2, hXq])

theorem fam4 (j : ℕ) (rest : Word) :
    Admissible (bottomFrom (List.replicate (j + 1) Digit.three ++ [Digit.two]) rest
      ((baseThreeEdges (j + 1)).1, (baseThreeEdges j).2)).1
    ∧ Admissible (bottomFrom (List.replicate (j + 1) Digit.three ++ [Digit.two]) rest
      ((baseThreeEdges (j + 1)).1, (baseThreeEdges j).2)).2 := by
  have hH : HOK (List.replicate (j + 1) Digit.three ++ [Digit.two]) :=
    Or.inr ⟨⟨Digit.two, by simp, rfl⟩, ⟨Digit.three, by simp, rfl⟩⟩
  obtain ⟨h1, h2⟩ := family_bridge _ ((baseThreeEdges (j + 1)).1, (baseThreeEdges j).2) hH rest
  dsimp only at h1 h2
  have hAeq : (baseThreeEdges (j + 1)).1 ++ [Unit4.i]
      = List.replicate (2 * j + 2 + 1) Unit4.one ++ [Unit4.i] ++ (List.replicate (2 * j + 2 + 3) Unit4.one ++ [Unit4.i]) := by
    rw [(baseThree_tokens (j + 1)).1]; ring_nf
  have hBeq : (baseThreeEdges j).2 ++ [Unit4.i] = List.replicate (2 * j + 2 + 1) Unit4.one ++ [Unit4.i] := by
    rw [(baseThree_tokens j).2]
  have hpar := count_one_three_two (j + 1)
  obtain ⟨hAP1, hAP2⟩ := almost_palindrome_one (List.replicate (j + 1) Digit.three ++ [Digit.two]) rest
  obtain ⟨hP1, hP2, hQ1, hQ2⟩ :=
    (almost_palindrome_two (List.replicate (j + 1) Digit.three ++ [Digit.two]) rest).1 hpar
  obtain ⟨Mp, hMp, hXp⟩ := endpoints_form _ hAP1 Letter.q Letter.p hP1 hP2
  obtain ⟨Mq, hMq, hXq⟩ := endpoints_form _ hAP2 Letter.q Letter.p hQ1 hQ2
  have hShape : ∀ M : BinaryWord,
      muOf ((baseThreeEdges (j + 1)).1 ++ [Unit4.i]) ((baseThreeEdges j).2 ++ [Unit4.i]) (Letter.q :: (M ++ [Letter.p]))
        = List.replicate (2 * j + 2 + 1) Unit4.one ++ [Unit4.i]
          ++ muOf ((baseThreeEdges (j + 1)).1 ++ [Unit4.i]) ((baseThreeEdges j).2 ++ [Unit4.i]) M
          ++ List.replicate (2 * j + 2 + 1) Unit4.one ++ [Unit4.i]
          ++ (List.replicate (2 * j + 2 + 3) Unit4.one ++ [Unit4.i]) := by
    intro M
    simp only [muOf, tokOf, muOf_append]
    rw [hAeq, hBeq]
    simp only [List.append_assoc, List.append_nil]
  have hA3 : IFollowedBy 3 (((baseThreeEdges (j + 1)).1 ++ [Unit4.i]) ++ List.replicate 3 Unit4.one) := by
    rw [hAeq]; exact ifb3_tok_A _ _ (by omega)
  have hB3 : IFollowedBy 3 (((baseThreeEdges j).2 ++ [Unit4.i]) ++ List.replicate 3 Unit4.one) := by
    rw [hBeq]; exact ifb3_tok_B _
  have hA1 : ∀ m < 3, ((baseThreeEdges (j + 1)).1 ++ [Unit4.i])[m]? = some Unit4.one := by
    intro m hm
    rw [hAeq]
    simp only [List.append_assoc]
    exact rep_prefix_ones _ 3 (by omega) _ m hm
  have hB1 : ∀ m < 3, ((baseThreeEdges j).2 ++ [Unit4.i])[m]? = some Unit4.one := by
    intro m hm
    rw [hBeq]
    exact rep_prefix_ones _ 3 (by omega) _ m hm
  constructor
  · exact core_c4 (2 * j + 2) ((baseThreeEdges (j + 1)).1 ++ [Unit4.i]) ((baseThreeEdges j).2 ++ [Unit4.i])
      (by rw [hAeq]; exact zY_A _) (by rw [hBeq]; exact zY_B _)
      (by rw [hAeq]; exact OneI_append _ _ (OneI_append _ _ (OneI_rep _) OneI_I) (OneI_append _ _ (OneI_rep _) OneI_I))
      (by rw [hBeq]; exact OneI_append _ _ (OneI_rep _) OneI_I)
      hA3 hB3 hA1 hB1 _ Mp hMp _ (hShape Mp) (by rw [h1, hXp])
  · exact core_c4 (2 * j + 2) ((baseThreeEdges (j + 1)).1 ++ [Unit4.i]) ((baseThreeEdges j).2 ++ [Unit4.i])
      (by rw [hAeq]; exact zY_A _) (by rw [hBeq]; exact zY_B _)
      (by rw [hAeq]; exact OneI_append _ _ (OneI_append _ _ (OneI_rep _) OneI_I) (OneI_append _ _ (OneI_rep _) OneI_I))
      (by rw [hBeq]; exact OneI_append _ _ (OneI_rep _) OneI_I)
      hA3 hB3 hA1 hB1 _ Mq hMq _ (hShape Mq) (by rw [h2, hXq])

/-! ### Case analysis on recursion words -/

theorem first_not_two : ∀ v : Word, allTwos v ≠ true →
    ∃ k rest x, x ≠ Digit.two ∧ v = List.replicate k Digit.two ++ x :: rest
  | [], h => absurd rfl h
  | y :: v, h => by
      by_cases hy : y = Digit.two
      · subst hy
        have h' : allTwos v ≠ true := by
          intro hv
          apply h
          rw [allTwos_iff] at hv ⊢
          intro z hz
          rcases List.mem_cons.mp hz with hz | hz
          · exact hz
          · exact hv z hz
        obtain ⟨k, rest, x, hx, hv⟩ := first_not_two v h'
        exact ⟨k + 1, rest, x, hx, by rw [hv]; simp [List.replicate_succ]⟩
      · exact ⟨0, v, y, hy, by simp⟩

theorem first_not_three : ∀ v : Word, v ≠ [] → allThrees v ≠ true →
    ∃ j rest y, y ≠ Digit.three ∧ v = List.replicate j Digit.three ++ y :: rest
  | [], hne, _ => absurd rfl hne
  | y :: v, _, h => by
      by_cases hy : y = Digit.three
      · subst hy
        by_cases hv : v = []
        · subst hv
          exact absurd (by decide : allThrees [Digit.three] = true) h
        · have h' : allThrees v ≠ true := by
            intro hh
            apply h
            rw [allThrees_iff] at hh ⊢
            refine ⟨by simp, ?_⟩
            intro z hz
            rcases List.mem_cons.mp hz with hz | hz
            · exact hz
            · exact hh.2 z hz
          obtain ⟨j, rest, y', hy', hv2⟩ := first_not_three v hv h'
          exact ⟨j + 1, rest, y', hy', by rw [hv2]; simp [List.replicate_succ]⟩
      · exact ⟨0, v, y, hy, by simp⟩

/-- The bottom edges of every recursion word are admissible: `Admissible w₁` and `Admissible (-i w₂)`. -/
theorem bottomEdges_admissible (v : Word) : Admissible (bottomEdges v).1 ∧ Admissible (bottomEdges v).2 := by
  by_cases h2 : allTwos v = true
  · obtain ⟨n, rfl⟩ : ∃ n, v = List.replicate n Digit.two := ⟨v.length, allTwos_eq h2⟩
    rw [bottomEdges_twos]
    exact adm_base2 n
  by_cases h3 : allThrees v = true
  · obtain ⟨n, rfl⟩ : ∃ n, v = List.replicate n Digit.three := ⟨v.length, allThrees_eq h3⟩
    have hn : 1 ≤ n := Nat.pos_of_ne_zero (fun h0 => (allThrees_iff _).mp h3 |>.1 (by rw [h0]; rfl))
    rw [bottomEdges_threes n hn]
    exact adm_base3 n hn
  obtain ⟨k, rest, x, hx, hv⟩ := first_not_two v h2
  subst hv
  cases x with
  | one =>
    rw [bottomEdges_fam1]
    exact fam1 k rest
  | two => exact absurd rfl hx
  | three =>
    cases k with
    | zero =>
      have hv0 : List.replicate 0 Digit.two ++ Digit.three :: rest = Digit.three :: rest := rfl
      rw [hv0] at h3 ⊢
      obtain ⟨j, rest', y, hy, hv'⟩ := first_not_three (Digit.three :: rest) (by simp) h3
      rw [hv']
      cases j with
      | zero =>
        simp only [List.replicate_zero, List.nil_append, List.cons.injEq] at hv'
        exact absurd hv'.1.symm hy
      | succ j =>
        cases y with
        | one =>
          rw [bottomEdges_fam3]
          exact fam3 j rest'
        | two =>
          rw [bottomEdges_fam4]
          exact fam4 j rest'
        | three => exact absurd rfl hy
    | succ k =>
      rw [bottomEdges_fam2]
      exact fam2 k rest

end FLatticePaper.Tiles
