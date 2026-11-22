import FLatticePaper.Tiles.AdmissibleBridge

/-! Task 51, admissibility, part 4: the `IFollowedBy` facts of the augmented tokens and the admissibility of the
family shapes `E ++ [i] = muOf A B x` for the (b) and (c) cases of `almost_square_tiling`. -/

namespace FLatticePaper.Tiles
open Farey

theorem OneI_append (u v : F2Word) (hu : OneI u) (hv : OneI v) : OneI (u ++ v) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact hu x h
  · exact hv x h

theorem OneI_rep (n : ℕ) : OneI (List.replicate n Unit4.one) := by
  intro x hx
  rw [List.eq_of_mem_replicate hx]
  exact Or.inl rfl

theorem OneI_lit (w : F2Word) (h : ∀ x ∈ w, x = Unit4.one ∨ x = Unit4.i) : OneI w := h

theorem oneI_head (m : ℕ) (S : F2Word) (hS0 : S[0]? = some Unit4.one) :
    (oneI m ++ S)[0]? = some Unit4.one := by
  cases m with
  | zero => simpa [oneI] using hS0
  | succ m => rw [oneI_succ]; simp

/-- `(1 i)^m S` is `1`-followed when `S` is, and starts with a `1`. -/
theorem ifb_oneI (m : ℕ) (S : F2Word) (hS : IFollowedBy 1 S) (hS0 : S[0]? = some Unit4.one) :
    IFollowedBy 1 (oneI m ++ S) := by
  induction m with
  | zero => simpa [oneI] using hS
  | succ m ih =>
    have e : oneI (m + 1) ++ S = Unit4.one :: Unit4.i :: (oneI m ++ S) := by
      rw [oneI_succ]; simp
    rw [e, ifb_cons_one, ifb_cons_i]
    refine ⟨fun j hj => ?_, ih⟩
    obtain rfl : j = 0 := by omega
    exact oneI_head m S hS0

/-- The `B`-type token of the (b) case: `1 (1 i)^m 1 1 i` followed by `1`. -/
theorem ifb_tok_b_two (m : ℕ) : IFollowedBy 1 ([Unit4.one, Unit4.one, Unit4.i] ++ oneI m ++ [Unit4.one, Unit4.one, Unit4.i]
    ++ [Unit4.one]) := by
  have e : [Unit4.one, Unit4.one, Unit4.i] ++ oneI m ++ [Unit4.one, Unit4.one, Unit4.i] ++ [Unit4.one]
      = Unit4.one :: Unit4.one :: Unit4.i :: (oneI m ++ [Unit4.one, Unit4.one, Unit4.i, Unit4.one]) := by
    simp
  rw [e, ifb_cons_one, ifb_cons_one, ifb_cons_i]
  refine ⟨fun j hj => ?_, ifb_oneI m _ (by decide) (by simp)⟩
  obtain rfl : j = 0 := by omega
  exact oneI_head m _ (by simp)

/-- The `A`-type token of the (b) case: `1 (1 i)^m 1 1 i` followed by `1`. -/
theorem ifb_tok_b_one (m : ℕ) : IFollowedBy 1 ([Unit4.one] ++ oneI m ++ [Unit4.one, Unit4.one, Unit4.i]
    ++ [Unit4.one]) := by
  have e : [Unit4.one] ++ oneI m ++ [Unit4.one, Unit4.one, Unit4.i] ++ [Unit4.one]
      = Unit4.one :: (oneI m ++ [Unit4.one, Unit4.one, Unit4.i, Unit4.one]) := by
    simp
  rw [e, ifb_cons_one]
  exact ifb_oneI m _ (by decide) (by simp)

theorem ifb_rep_prefix (k a : ℕ) (X : F2Word) :
    IFollowedBy k (List.replicate a Unit4.one ++ X) ↔ IFollowedBy k X := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [List.replicate_succ, List.cons_append, ifb_cons_one, ih]

theorem rep_prefix_ones (b k : ℕ) (hb : k ≤ b) (X : F2Word) :
    ∀ m < k, (List.replicate b Unit4.one ++ X)[m]? = some Unit4.one := by
  intro m hm
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_replicate]
  simp [show m < b by omega]

/-- The `A`-type token of the (c) case, followed by three ones. -/
theorem ifb3_tok_A (a b : ℕ) (hb : 3 ≤ b) :
    IFollowedBy 3 (List.replicate a Unit4.one ++ [Unit4.i] ++ (List.replicate b Unit4.one ++ [Unit4.i])
      ++ List.replicate 3 Unit4.one) := by
  have e : List.replicate a Unit4.one ++ [Unit4.i] ++ (List.replicate b Unit4.one ++ [Unit4.i])
        ++ List.replicate 3 Unit4.one
      = List.replicate a Unit4.one ++ (Unit4.i :: (List.replicate b Unit4.one
          ++ (Unit4.i :: List.replicate 3 Unit4.one))) := by
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [e, ifb_rep_prefix, ifb_cons_i]
  refine ⟨rep_prefix_ones b 3 hb _, ?_⟩
  rw [ifb_rep_prefix, ifb_cons_i]
  exact ⟨fun m hm => by rw [List.getElem?_replicate, if_pos hm], ifb_replicate 3 3⟩

/-- The `B`-type token of the (c) case, followed by three ones. -/
theorem ifb3_tok_B (c : ℕ) :
    IFollowedBy 3 (List.replicate c Unit4.one ++ [Unit4.i] ++ List.replicate 3 Unit4.one) := by
  have e : List.replicate c Unit4.one ++ [Unit4.i] ++ List.replicate 3 Unit4.one
      = List.replicate c Unit4.one ++ (Unit4.i :: List.replicate 3 Unit4.one) := by
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [e, ifb_rep_prefix, ifb_cons_i]
  exact ⟨fun m hm => by rw [List.getElem?_replicate, if_pos hm], ifb_replicate 3 3⟩

/-- The `1`-prefix of a token followed by `k` ones, for every letter of a binary word. -/
theorem prefix_ones_of (k : ℕ) (T Z : F2Word) (hT : ∀ m < k, T[m]? = some Unit4.one) :
    ∀ m < k, (T ++ Z)[m]? = some Unit4.one := by
  intro m hm
  have hlen : m < T.length := by
    by_contra hcon
    have h := hT m hm
    rw [List.getElem?_eq_none (by omega)] at h
    simp at h
  rw [List.getElem?_append_left hlen]
  exact hT m hm

/-- Every token followed by `k` ones is fine, so is every image of a binary word. -/
theorem ifb_muOf (k : ℕ) (A B : F2Word) (hA : IFollowedBy k (A ++ List.replicate k Unit4.one))
    (hB : IFollowedBy k (B ++ List.replicate k Unit4.one))
    (hA1 : ∀ m < k, A[m]? = some Unit4.one) (hB1 : ∀ m < k, B[m]? = some Unit4.one) :
    ∀ x : BinaryWord, IFollowedBy k (muOf A B x ++ List.replicate k Unit4.one) := by
  intro x
  induction x with
  | nil => simpa [muOf] using ifb_replicate k k
  | cons c x ih =>
    have hT : IFollowedBy k (tokOf A B c ++ List.replicate k Unit4.one) := by
      cases c with
      | p => exact hA
      | q => exact hB
    have hT1 : ∀ m < k, (tokOf A B c)[m]? = some Unit4.one := by
      cases c with
      | p => exact hA1
      | q => exact hB1
    have hstart : ∀ m < k, (muOf A B x ++ List.replicate k Unit4.one)[m]? = some Unit4.one := by
      intro m hm
      cases x with
      | nil =>
        simp only [muOf, List.nil_append]
        rw [List.getElem?_replicate]
        simp [hm]
      | cons d y =>
        have hd : ∀ m < k, (tokOf A B d)[m]? = some Unit4.one := by
          cases d with
          | p => exact hA1
          | q => exact hB1
        have e : muOf A B (d :: y) ++ List.replicate k Unit4.one
            = tokOf A B d ++ (muOf A B y ++ List.replicate k Unit4.one) := by
          simp [muOf, List.append_assoc]
        rw [e]
        exact prefix_ones_of k _ _ hd m hm
    have key := ifb_app k (tokOf A B c) (muOf A B x ++ List.replicate k Unit4.one) hT ih hstart
    simpa [muOf, List.append_assoc] using key

/-- The padded form: if `muOf A B x = E0 ++ 1^k ++ [i]`, then `E0 ++ 1^k` is `k`-followed. -/
theorem ifb_of_muOf_pad (k : ℕ) (A B : F2Word) (hA : IFollowedBy k (A ++ List.replicate k Unit4.one))
    (hB : IFollowedBy k (B ++ List.replicate k Unit4.one))
    (hA1 : ∀ m < k, A[m]? = some Unit4.one) (hB1 : ∀ m < k, B[m]? = some Unit4.one)
    (x : BinaryWord) (E0 : F2Word) (hE : muOf A B x = E0 ++ List.replicate k Unit4.one ++ [Unit4.i]) :
    IFollowedBy k (E0 ++ List.replicate k Unit4.one) := by
  apply ifb_of_pad k E0
  have h := ifb_muOf k A B hA hB hA1 hB1 x
  rw [hE] at h
  exact h

/-- The (b)-shape: `E ++ [i] = 11i (1 i)^m 11i Y 1 (1 i)^m 11i` gives the admissible case (b). -/
theorem admissible_b_shape (m : ℕ) (Y E : F2Word) (hY : Y.reverse ++ [Unit4.i] = [Unit4.i] ++ Y)
    (hYL : OneI Y)
    (hE : E ++ [Unit4.i] = [Unit4.one, Unit4.one, Unit4.i] ++ oneI m ++ [Unit4.one, Unit4.one, Unit4.i] ++ Y
      ++ [Unit4.one] ++ oneI m ++ [Unit4.one, Unit4.one, Unit4.i])
    (hifb : IFollowedBy 1 E) : Admissible E := by
  have hE' : E = [Unit4.one, Unit4.one, Unit4.i]
      ++ (oneI m ++ [Unit4.one, Unit4.one, Unit4.i] ++ Y ++ [Unit4.one] ++ oneI m ++ [Unit4.one]) ++ [Unit4.one] := by
    apply List.append_cancel_right (bs := [Unit4.i])
    rw [hE]
    simp
  have hA : OneI [Unit4.one, Unit4.one, Unit4.i] := OneI_lit _ (by
    intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx; rcases hx with rfl | rfl | rfl <;> simp)
  have hR : OneI [Unit4.one] := OneI_lit _ (by
    intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx; subst hx; simp)
  have hw : OneI (oneI m ++ [Unit4.one, Unit4.one, Unit4.i] ++ Y ++ [Unit4.one] ++ oneI m ++ [Unit4.one]) :=
    OneI_append _ _ (OneI_append _ _ (OneI_append _ _ (OneI_append _ _ (OneI_append _ _
      (oneI_letters m) hA) hYL) hR) (oneI_letters m)) hR
  apply admissible_of_b E (oneI m ++ [Unit4.one, Unit4.one, Unit4.i] ++ Y ++ [Unit4.one] ++ oneI m ++ [Unit4.one])
    hE' (pal_b m Y hY) hifb
  rw [hE']
  exact OneI_append _ _ (OneI_append _ _ hA hw) hR

/-- The (c)-shape of the `A`-type words: `E ++ [i] = 1^{a+1} i (1^{a+3} i) Y 1^{a+3} i` gives case (c). -/
theorem admissible_c3_shape (a : ℕ) (Y E : F2Word)
    (hY : Y.reverse ++ ([Unit4.i] ++ (List.replicate (a + 3) Unit4.one ++ [Unit4.i]))
      = ([Unit4.i] ++ (List.replicate (a + 3) Unit4.one ++ [Unit4.i])) ++ Y)
    (hYL : OneI Y)
    (hE : E ++ [Unit4.i] = List.replicate (a + 1) Unit4.one ++ [Unit4.i]
      ++ (List.replicate (a + 3) Unit4.one ++ [Unit4.i]) ++ Y ++ List.replicate (a + 3) Unit4.one ++ [Unit4.i])
    (hifb : IFollowedBy 3 E) : Admissible E := by
  have hr1 : List.replicate (a + 1) Unit4.one = [Unit4.one] ++ List.replicate a Unit4.one := by
    rw [List.replicate_succ]; rfl
  have hr3 : List.replicate (a + 3) Unit4.one = List.replicate a Unit4.one ++ [Unit4.one, Unit4.one, Unit4.one] := by
    rw [List.replicate_add]; rfl
  have hE' : E = [Unit4.one] ++ (List.replicate a Unit4.one ++ [Unit4.i]
      ++ (List.replicate (a + 3) Unit4.one ++ [Unit4.i]) ++ Y ++ List.replicate a Unit4.one)
      ++ [Unit4.one, Unit4.one, Unit4.one] := by
    apply List.append_cancel_right (bs := [Unit4.i])
    rw [hE, hr1, hr3]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hI : OneI [Unit4.i] := OneI_lit _ (by
    intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx; subst hx; simp)
  have hR : OneI [Unit4.one] := OneI_lit _ (by
    intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx; subst hx; simp)
  have hwt : OneI (List.replicate a Unit4.one ++ [Unit4.i]
      ++ (List.replicate (a + 3) Unit4.one ++ [Unit4.i]) ++ Y ++ List.replicate a Unit4.one) :=
    OneI_append _ _ (OneI_append _ _ (OneI_append _ _ (OneI_append _ _ (OneI_rep a) hI)
      (OneI_append _ _ (OneI_rep _) hI)) hYL) (OneI_rep a)
  have hO3 : OneI [Unit4.one, Unit4.one, Unit4.one] := OneI_lit _ (by
    intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx; rcases hx with rfl | rfl | rfl <;> simp)
  apply admissible_of_c E (List.replicate a Unit4.one ++ [Unit4.i]
      ++ (List.replicate (a + 3) Unit4.one ++ [Unit4.i]) ++ Y ++ List.replicate a Unit4.one) hE'
    (pal_c3 a (a + 3) Y hY) hifb
  rw [hE']
  exact OneI_append _ _ (OneI_append _ _ hR hwt) hO3

end FLatticePaper.Tiles
