import FLatticePaper.Farey.Recursion

namespace FLatticePaper.Tiles
open Farey

inductive Letter
  | p | q
  deriving DecidableEq, Repr

abbrev BinaryWord := List Letter

/-- The child operator `C_{(w)}(p_t,q_t)` on binary words; the case is the parity of the number of ones in `w`. -/
def childWords (word : Word) (pw qw : BinaryWord) : BinaryWord × BinaryWord :=
  if word.count .one % 2 = 0 then (qw ++ qw ++ pw, qw ++ pw) else (pw ++ qw ++ qw, pw ++ qw)

/-- A binary word quadruple `(p_{t+1}, q_{t+1}, p_t, q_t)`. -/
structure WordQuad where
  childP : BinaryWord
  childQ : BinaryWord
  parentP : BinaryWord
  parentQ : BinaryWord
  deriving DecidableEq, Repr

/-- `Q_{(w_0)} = (C_{w_0}(p,q), p, q)`. -/
def initialQuad (w0 : Word) : WordQuad :=
  ⟨(childWords w0 [.p] [.q]).1, (childWords w0 [.p] [.q]).2, [.p], [.q]⟩

/-- One step of `eq:child_farey_quad_continuedfrac`, from `Q_{(w)}` to `Q_{(w*digit)}`. -/
def WordQuad.step (w : Word) (quad : WordQuad) : Digit → WordQuad
  | .one => ⟨(childWords (w ++ [Digit.one]) quad.childP quad.childQ).1,
      (childWords (w ++ [Digit.one]) quad.childP quad.childQ).2, quad.childP, quad.childQ⟩
  | .two => ⟨(childWords (w ++ [Digit.two]) quad.childP quad.parentQ).1,
      (childWords (w ++ [Digit.two]) quad.childP quad.parentQ).2, quad.childP, quad.parentQ⟩
  | .three => ⟨(childWords (w ++ [Digit.three]) quad.parentP quad.childQ).1,
      (childWords (w ++ [Digit.three]) quad.parentP quad.childQ).2, quad.parentP, quad.childQ⟩

/-- `Q_{(w_0 u)}` for an extension `u` of `w_0`, built digit by digit. -/
def quadAt (w0 u : Word) : WordQuad :=
  (u.foldl (fun (acc : Word × WordQuad) digit => (acc.1 ++ [digit], acc.2.step acc.1 digit))
    (w0, initialQuad w0)).2

def IsAlmostPalindrome (w : BinaryWord) : Prop :=
  ∃ (first last : Letter) (middle : BinaryWord), middle.reverse = middle ∧ w = first :: (middle ++ [last])

/-- `w[2:n]`: the letters in positions `2, …, n`, counted from one. -/
def slice2 (w : BinaryWord) (n : ℕ) : BinaryWord := (w.drop 1).take (n - 1)

theorem quadAt_nil (w0 : Word) : quadAt w0 [] = initialQuad w0 := rfl

/-- The word component of the accumulator grows by the appended digits. -/
theorem foldl_fst (u : Word) (acc : Word × WordQuad) :
    (u.foldl (fun (acc : Word × WordQuad) digit => (acc.1 ++ [digit], acc.2.step acc.1 digit)) acc).1
      = acc.1 ++ u := by
  induction u generalizing acc with
  | nil => simp
  | cons d ds ih =>
    rw [List.foldl_cons, ih]
    simp

theorem quadAt_append_singleton (w0 u : Word) (d : Digit) :
    quadAt w0 (u ++ [d]) = (quadAt w0 u).step (w0 ++ u) d := by
  have h := foldl_fst u (w0, initialQuad w0)
  unfold quadAt at *
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [h]

theorem childWords_congr {w w' : Word} (h : w.count .one % 2 = w'.count .one % 2)
    (pw qw : BinaryWord) : childWords w pw qw = childWords w' pw qw := by
  unfold childWords
  rw [h]

theorem WordQuad.step_congr {w w' : Word} (h : w.count .one % 2 = w'.count .one % 2)
    (quad : WordQuad) (d : Digit) : quad.step w d = quad.step w' d := by
  have h1 : (w ++ [Digit.one]).count .one % 2 = (w' ++ [Digit.one]).count .one % 2 := by
    simp [List.count_append]; omega
  have h2 : (w ++ [Digit.two]).count .one % 2 = (w' ++ [Digit.two]).count .one % 2 := by
    simp [List.count_append]; omega
  have h3 : (w ++ [Digit.three]).count .one % 2 = (w' ++ [Digit.three]).count .one % 2 := by
    simp [List.count_append]; omega
  cases d
  · simp only [WordQuad.step, childWords_congr h1]
  · simp only [WordQuad.step, childWords_congr h2]
  · simp only [WordQuad.step, childWords_congr h3]

/-- `Q_{(w_0 u)}` depends on `w_0` only through the parity of its ones. -/
theorem quadAt_congr {w0 w0' : Word} (h : w0.count .one % 2 = w0'.count .one % 2) (u : Word) :
    quadAt w0 u = quadAt w0' u := by
  induction u using List.reverseRecOn with
  | nil =>
    rw [quadAt_nil, quadAt_nil]
    unfold initialQuad
    rw [childWords_congr h]
  | append_singleton u d ih =>
    have h' : (w0 ++ u).count .one % 2 = (w0' ++ u).count .one % 2 := by
      simp only [List.count_append]; omega
    rw [quadAt_append_singleton, quadAt_append_singleton, ih, WordQuad.step_congr h']

/-- Reversing every word of a quadruple. -/
def WordQuad.rev (quad : WordQuad) : WordQuad :=
  ⟨quad.childP.reverse, quad.childQ.reverse, quad.parentP.reverse, quad.parentQ.reverse⟩

/-- Reversal exchanges the two parities of the child operator. -/
theorem childWords_reverse (w : Word) (X Y : BinaryWord) :
    childWords (.one :: w) X.reverse Y.reverse
      = ((childWords w X Y).1.reverse, (childWords w X Y).2.reverse) := by
  unfold childWords
  rw [List.count_cons_self]
  split_ifs <;> first | (exfalso; omega) | simp [List.reverse_append, List.append_assoc]

theorem WordQuad.rev_step (w : Word) (quad : WordQuad) (d : Digit) :
    quad.rev.step ([Digit.one] ++ w) d = (quad.step w d).rev := by
  cases d with
  | one =>
    simp only [WordQuad.step, WordQuad.rev, List.cons_append, List.nil_append]
    rw [childWords_reverse (w ++ [Digit.one]) quad.childP quad.childQ]
  | two =>
    simp only [WordQuad.step, WordQuad.rev, List.cons_append, List.nil_append]
    rw [childWords_reverse (w ++ [Digit.two]) quad.childP quad.parentQ]
  | three =>
    simp only [WordQuad.step, WordQuad.rev, List.cons_append, List.nil_append]
    rw [childWords_reverse (w ++ [Digit.three]) quad.parentP quad.childQ]

/-- The odd-root family is the reversal of the even-root family. -/
theorem quadAt_one_eq_rev (u : Word) : quadAt [Digit.one] u = (quadAt [] u).rev := by
  induction u using List.reverseRecOn with
  | nil =>
    rw [quadAt_nil, quadAt_nil]
    have hc : childWords [Digit.one] [.p] [.q]
        = ((childWords [] [.p] [.q]).1.reverse, (childWords [] [.p] [.q]).2.reverse) := by
      have := childWords_reverse [] [.p] [.q]
      simpa using this
    unfold initialQuad WordQuad.rev
    rw [hc]
    simp
  | append_singleton u d ih =>
    rw [quadAt_append_singleton, quadAt_append_singleton, ih, WordQuad.rev_step, List.nil_append]

/-- A central pair: palindromes `a`, `b` with `b p q a = a q p b`. -/
def Cen (a b : BinaryWord) : Prop :=
  a.reverse = a ∧ b.reverse = b ∧ b ++ [Letter.p, Letter.q] ++ a = a ++ [Letter.q, Letter.p] ++ b

section Even

variable {a b M : BinaryWord}

theorem mid_rev_even (ha : a.reverse = a) (hb : b.reverse = b)
    (hM1 : M = b ++ [Letter.p, Letter.q] ++ a) (hM2 : M = a ++ [Letter.q, Letter.p] ++ b) :
    M.reverse = M := by
  have h : M.reverse = a ++ [Letter.q, Letter.p] ++ b := by
    rw [hM1]; simp [List.reverse_append, ha, hb, List.append_assoc]
  rw [h]; exact hM2.symm

theorem k1_even (hM1 : M = b ++ [Letter.p, Letter.q] ++ a) (hM2 : M = a ++ [Letter.q, Letter.p] ++ b) :
    (b ++ [Letter.p, Letter.q]) ++ M = M ++ [Letter.q, Letter.p] ++ b := by
  calc (b ++ [Letter.p, Letter.q]) ++ M
      = (b ++ [Letter.p, Letter.q]) ++ (a ++ [Letter.q, Letter.p] ++ b) := by rw [← hM2]
    _ = (b ++ [Letter.p, Letter.q] ++ a) ++ [Letter.q, Letter.p] ++ b := by simp [List.append_assoc]
    _ = M ++ [Letter.q, Letter.p] ++ b := by rw [← hM1]

theorem z_rev_even (hb : b.reverse = b) (hMr : M.reverse = M)
    (k1 : (b ++ [Letter.p, Letter.q]) ++ M = M ++ [Letter.q, Letter.p] ++ b) :
    ((b ++ [Letter.p, Letter.q]) ++ M).reverse = (b ++ [Letter.p, Letter.q]) ++ M := by
  have h1 : ((b ++ [Letter.p, Letter.q]) ++ M).reverse = M ++ [Letter.q, Letter.p] ++ b := by
    simp [List.reverse_append, hMr, hb, List.append_assoc]
  rw [h1]; exact k1.symm

/-- `Cen M Z` for `Z = (b p q) M`: the even-parity child pair recurses. -/
theorem cen_even_one (k1 : (b ++ [Letter.p, Letter.q]) ++ M = M ++ [Letter.q, Letter.p] ++ b) :
    ((b ++ [Letter.p, Letter.q]) ++ M) ++ [Letter.p, Letter.q] ++ M
      = M ++ [Letter.q, Letter.p] ++ ((b ++ [Letter.p, Letter.q]) ++ M) := by
  calc ((b ++ [Letter.p, Letter.q]) ++ M) ++ [Letter.p, Letter.q] ++ M
      = (M ++ [Letter.q, Letter.p] ++ b) ++ [Letter.p, Letter.q] ++ M := by rw [k1]
    _ = M ++ [Letter.q, Letter.p] ++ ((b ++ [Letter.p, Letter.q]) ++ M) := by
          simp [List.append_assoc]

/-- `Cen Z b` for `Z = (b p q) M`. -/
theorem cen_even_two (k1 : (b ++ [Letter.p, Letter.q]) ++ M = M ++ [Letter.q, Letter.p] ++ b) :
    b ++ [Letter.p, Letter.q] ++ ((b ++ [Letter.p, Letter.q]) ++ M)
      = ((b ++ [Letter.p, Letter.q]) ++ M) ++ [Letter.q, Letter.p] ++ b := by
  calc b ++ [Letter.p, Letter.q] ++ ((b ++ [Letter.p, Letter.q]) ++ M)
      = (b ++ [Letter.p, Letter.q]) ++ (M ++ [Letter.q, Letter.p] ++ b) := by rw [k1]
    _ = ((b ++ [Letter.p, Letter.q]) ++ M) ++ [Letter.q, Letter.p] ++ b := by
          simp [List.append_assoc]

/-- `Cen a M` for the middle word `M = b p q a = a q p b`. -/
theorem cen_even_three (hM1 : M = b ++ [Letter.p, Letter.q] ++ a)
    (hM2 : M = a ++ [Letter.q, Letter.p] ++ b) :
    M ++ [Letter.p, Letter.q] ++ a = a ++ [Letter.q, Letter.p] ++ M := by
  calc M ++ [Letter.p, Letter.q] ++ a
      = (a ++ [Letter.q, Letter.p] ++ b) ++ [Letter.p, Letter.q] ++ a := by rw [← hM2]
    _ = a ++ [Letter.q, Letter.p] ++ (b ++ [Letter.p, Letter.q] ++ a) := by
          simp [List.append_assoc]
    _ = a ++ [Letter.q, Letter.p] ++ M := by rw [← hM1]

end Even

section Odd

variable {a b N : BinaryWord}

theorem mid_rev_odd (ha : a.reverse = a) (hb : b.reverse = b)
    (hN1 : N = a ++ [Letter.p, Letter.q] ++ b) (hN2 : N = b ++ [Letter.q, Letter.p] ++ a) :
    N.reverse = N := by
  have h : N.reverse = a ++ [Letter.p, Letter.q] ++ b := by
    rw [hN2]; simp [List.reverse_append, ha, hb, List.append_assoc]
  rw [h]; exact hN1.symm

/-- The relation `N p q b = b q p N` identifies the odd child `N p q b`. -/
theorem hR_odd (hN1 : N = a ++ [Letter.p, Letter.q] ++ b) (hN2 : N = b ++ [Letter.q, Letter.p] ++ a) :
    N ++ [Letter.p, Letter.q] ++ b = b ++ [Letter.q, Letter.p] ++ N := by
  calc N ++ [Letter.p, Letter.q] ++ b
      = (b ++ [Letter.q, Letter.p] ++ a) ++ [Letter.p, Letter.q] ++ b := by rw [← hN2]
    _ = b ++ [Letter.q, Letter.p] ++ (a ++ [Letter.p, Letter.q] ++ b) := by
          simp [List.append_assoc]
    _ = b ++ [Letter.q, Letter.p] ++ N := by rw [← hN1]

theorem k1_odd (hN1 : N = a ++ [Letter.p, Letter.q] ++ b) (hN2 : N = b ++ [Letter.q, Letter.p] ++ a) :
    a ++ [Letter.p, Letter.q] ++ N = N ++ [Letter.q, Letter.p] ++ a := by
  calc a ++ [Letter.p, Letter.q] ++ N
      = a ++ [Letter.p, Letter.q] ++ (b ++ [Letter.q, Letter.p] ++ a) := by rw [← hN2]
    _ = (a ++ [Letter.p, Letter.q] ++ b) ++ [Letter.q, Letter.p] ++ a := by
          simp [List.append_assoc]
    _ = N ++ [Letter.q, Letter.p] ++ a := by rw [← hN1]

theorem r_rev_odd (ha : a.reverse = a) (hb : b.reverse = b)
    (hN1 : N = a ++ [Letter.p, Letter.q] ++ b) (hN2 : N = b ++ [Letter.q, Letter.p] ++ a) :
    (N ++ [Letter.p, Letter.q] ++ b).reverse = N ++ [Letter.p, Letter.q] ++ b := by
  have hNr := mid_rev_odd ha hb hN1 hN2
  have h1 : (N ++ [Letter.p, Letter.q] ++ b).reverse = b ++ [Letter.q, Letter.p] ++ N := by
    simp [List.reverse_append, hNr, hb, List.append_assoc]
  rw [h1]; exact (hR_odd hN1 hN2).symm

/-- `Cen R N` for the odd child `R = N p q b`. -/
theorem cen_odd_one (hN1 : N = a ++ [Letter.p, Letter.q] ++ b) (hN2 : N = b ++ [Letter.q, Letter.p] ++ a) :
    N ++ [Letter.p, Letter.q] ++ (N ++ [Letter.p, Letter.q] ++ b)
      = (N ++ [Letter.p, Letter.q] ++ b) ++ [Letter.q, Letter.p] ++ N := by
  calc N ++ [Letter.p, Letter.q] ++ (N ++ [Letter.p, Letter.q] ++ b)
      = N ++ [Letter.p, Letter.q] ++ (b ++ [Letter.q, Letter.p] ++ N) := by
          rw [hR_odd hN1 hN2]
    _ = (N ++ [Letter.p, Letter.q] ++ b) ++ [Letter.q, Letter.p] ++ N := by
          simp [List.append_assoc]

/-- `Cen b R` for the odd child `R = N p q b`. -/
theorem cen_odd_two (hN1 : N = a ++ [Letter.p, Letter.q] ++ b) (hN2 : N = b ++ [Letter.q, Letter.p] ++ a) :
    (N ++ [Letter.p, Letter.q] ++ b) ++ [Letter.p, Letter.q] ++ b
      = b ++ [Letter.q, Letter.p] ++ (N ++ [Letter.p, Letter.q] ++ b) := by
  calc (N ++ [Letter.p, Letter.q] ++ b) ++ [Letter.p, Letter.q] ++ b
      = (b ++ [Letter.q, Letter.p] ++ N) ++ [Letter.p, Letter.q] ++ b := by rw [hR_odd hN1 hN2]
    _ = b ++ [Letter.q, Letter.p] ++ (N ++ [Letter.p, Letter.q] ++ b) := by
          simp [List.append_assoc]

end Odd

/-- The wrapped word `q a p`. -/
def cw (a : BinaryWord) : BinaryWord := Letter.q :: (a ++ [Letter.p])

/-- Both parents are wrapped central pairs `cw a`, `cw b` with `Cen a b` (even parity). -/
def CForm0 (X Y : BinaryWord) : Prop := ∃ a b : BinaryWord, X = cw a ∧ Y = cw b ∧ Cen a b

/-- Both parents are wrapped central pairs with `Cen b a` (odd parity). -/
def CForm1 (X Y : BinaryWord) : Prop := ∃ a b : BinaryWord, X = cw a ∧ Y = cw b ∧ Cen b a

section Transitions

theorem c0_one {a b : BinaryWord} (hC : Cen a b) :
    CForm1 (cw b ++ cw b ++ cw a) (cw b ++ cw a) := by
  obtain ⟨ha, hb, hM⟩ := hC
  have hMr := mid_rev_even (M := b ++ [Letter.p, Letter.q] ++ a) ha hb rfl hM
  have k1 := k1_even (M := b ++ [Letter.p, Letter.q] ++ a) rfl hM
  refine ⟨(b ++ [Letter.p, Letter.q]) ++ (b ++ [Letter.p, Letter.q] ++ a),
    b ++ [Letter.p, Letter.q] ++ a, ?_, ?_, ?_⟩
  · simp [cw, List.append_assoc]
  · simp [cw, List.append_assoc]
  · exact ⟨hMr, z_rev_even hb hMr k1, cen_even_one k1⟩

theorem c0_two {a b : BinaryWord} (hC : Cen a b) :
    CForm0 (cw b ++ cw b ++ cw a) (cw b) := by
  obtain ⟨ha, hb, hM⟩ := hC
  have hMr := mid_rev_even (M := b ++ [Letter.p, Letter.q] ++ a) ha hb rfl hM
  have k1 := k1_even (M := b ++ [Letter.p, Letter.q] ++ a) rfl hM
  refine ⟨(b ++ [Letter.p, Letter.q]) ++ (b ++ [Letter.p, Letter.q] ++ a), b, ?_, rfl, ?_⟩
  · simp [cw, List.append_assoc]
  · exact ⟨z_rev_even hb hMr k1, hb, cen_even_two k1⟩

theorem c0_three {a b : BinaryWord} (hC : Cen a b) :
    CForm0 (cw a) (cw b ++ cw a) := by
  obtain ⟨ha, hb, hM⟩ := hC
  have hMr := mid_rev_even (M := b ++ [Letter.p, Letter.q] ++ a) ha hb rfl hM
  refine ⟨a, b ++ [Letter.p, Letter.q] ++ a, rfl, ?_, ?_⟩
  · simp [cw, List.append_assoc]
  · exact ⟨ha, hMr, cen_even_three rfl hM⟩

theorem c1_one {a b : BinaryWord} (hC : Cen b a) :
    CForm0 (cw a ++ cw b ++ cw b) (cw a ++ cw b) := by
  obtain ⟨hb, ha, hN⟩ := hC
  have hN2 := hN
  have hNr := mid_rev_odd ha hb (N := a ++ [Letter.p, Letter.q] ++ b) rfl hN
  refine ⟨(a ++ [Letter.p, Letter.q] ++ b) ++ [Letter.p, Letter.q] ++ b, a ++ [Letter.p, Letter.q] ++ b,
    ?_, ?_, ?_⟩
  · simp [cw, List.append_assoc]
  · simp [cw, List.append_assoc]
  · exact ⟨r_rev_odd ha hb rfl hN, hNr, cen_odd_one rfl hN⟩

theorem c1_two {a b : BinaryWord} (hC : Cen b a) :
    CForm1 (cw a ++ cw b ++ cw b) (cw b) := by
  obtain ⟨hb, ha, hN⟩ := hC
  have hNr := mid_rev_odd ha hb (N := a ++ [Letter.p, Letter.q] ++ b) rfl hN
  refine ⟨(a ++ [Letter.p, Letter.q] ++ b) ++ [Letter.p, Letter.q] ++ b, b, ?_, rfl, ?_⟩
  · simp [cw, List.append_assoc]
  · exact ⟨hb, r_rev_odd ha hb rfl hN, cen_odd_two rfl hN⟩

theorem c1_three {a b : BinaryWord} (hC : Cen b a) :
    CForm1 (cw a) (cw a ++ cw b) := by
  obtain ⟨hb, ha, hN⟩ := hC
  refine ⟨a, a ++ [Letter.p, Letter.q] ++ b, rfl, ?_, ?_⟩
  · simp [cw, List.append_assoc]
  · exact ⟨mid_rev_odd ha hb (N := a ++ [Letter.p, Letter.q] ++ b) rfl hN, ha,
      k1_odd rfl hN⟩

end Transitions

section Powers

theorem rep_snoc (n : ℕ) (x : Letter) :
    List.replicate n x ++ [x] = x :: List.replicate n x := by
  rw [← List.replicate_succ', List.replicate_succ]

theorem rep_comm (m : ℕ) (x : Letter) (l : BinaryWord) :
    List.replicate m x ++ x :: l = x :: (List.replicate m x ++ l) := by
  induction m with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, ih]

/-- `q^(m+1)` and `q^m` form a central pair. -/
theorem cen_pow_q (m : ℕ) :
    Cen (List.replicate m Letter.q) (List.replicate (m + 1) Letter.q) := by
  refine ⟨List.reverse_replicate, List.reverse_replicate, ?_⟩
  calc List.replicate (m + 1) Letter.q ++ [Letter.p, Letter.q] ++ List.replicate m Letter.q
      = Letter.q :: (List.replicate m Letter.q ++ Letter.p :: Letter.q :: List.replicate m Letter.q) := by
          simp [List.replicate_succ, List.append_assoc]
    _ = List.replicate m Letter.q ++ Letter.q :: (Letter.p :: Letter.q :: List.replicate m Letter.q) :=
          (rep_comm m Letter.q _).symm
    _ = List.replicate m Letter.q ++ [Letter.q, Letter.p] ++ List.replicate (m + 1) Letter.q := by
          simp [List.replicate_succ, List.append_assoc]

/-- `p^n q p^n` is a palindrome and forms a central pair with `p^n`. -/
theorem cen_rqr (n : ℕ) :
    Cen (List.replicate n Letter.p)
      (List.replicate n Letter.p ++ [Letter.q] ++ List.replicate n Letter.p) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [List.reverse_replicate]
  · simp [List.reverse_replicate]
  · calc (List.replicate n Letter.p ++ [Letter.q] ++ List.replicate n Letter.p)
          ++ [Letter.p, Letter.q] ++ List.replicate n Letter.p
        = List.replicate n Letter.p ++ Letter.q :: (List.replicate n Letter.p ++ Letter.p :: Letter.q :: List.replicate n Letter.p) := by
            simp [List.append_assoc]
      _ = List.replicate n Letter.p ++ Letter.q :: Letter.p :: (List.replicate n Letter.p ++ Letter.q :: List.replicate n Letter.p) := by
            rw [rep_comm n Letter.p (Letter.q :: List.replicate n Letter.p)]
      _ = List.replicate n Letter.p ++ [Letter.q, Letter.p]
            ++ (List.replicate n Letter.p ++ [Letter.q] ++ List.replicate n Letter.p) := by
            simp [List.append_assoc]

/-- `p^(n+1) q p^(n+1)` and `p^n` form a central pair (the even child after `3^(n+1) 2`). -/
theorem cen_a2 (n : ℕ) :
    Cen (List.replicate (n + 1) Letter.p ++ [Letter.q] ++ List.replicate (n + 1) Letter.p)
      (List.replicate n Letter.p) := by
  have hR : List.replicate (n + 1) Letter.p = Letter.p :: List.replicate n Letter.p :=
    List.replicate_succ
  refine ⟨?_, ?_, ?_⟩
  · simp [List.reverse_append, List.reverse_replicate]
  · simp [List.reverse_replicate]
  · rw [hR]
    calc List.replicate n Letter.p ++ [Letter.p, Letter.q]
          ++ ((Letter.p :: List.replicate n Letter.p) ++ [Letter.q] ++ (Letter.p :: List.replicate n Letter.p))
        = List.replicate n Letter.p ++ Letter.p :: Letter.q :: ((Letter.p :: List.replicate n Letter.p) ++ Letter.q :: (Letter.p :: List.replicate n Letter.p)) := by
            simp [List.append_assoc]
      _ = Letter.p :: (List.replicate n Letter.p ++ Letter.q :: ((Letter.p :: List.replicate n Letter.p) ++ Letter.q :: (Letter.p :: List.replicate n Letter.p))) :=
            rep_comm n Letter.p _
      _ = ((Letter.p :: List.replicate n Letter.p) ++ [Letter.q] ++ (Letter.p :: List.replicate n Letter.p))
          ++ [Letter.q, Letter.p] ++ List.replicate n Letter.p := by
            simp [List.append_assoc]

end Powers

section Invariant

theorem childWords_even_gen {u : Word} (h : u.count Digit.one % 2 = 0) (X Y : BinaryWord) :
    childWords u X Y = (Y ++ Y ++ X, Y ++ X) := by
  simp [childWords, h]

theorem childWords_odd_gen {u : Word} (h : u.count Digit.one % 2 = 1) (X Y : BinaryWord) :
    childWords u X Y = (X ++ Y ++ Y, X ++ Y) := by
  simp [childWords, h]

theorem count_snoc_one (u : Word) : (u ++ [Digit.one]).count Digit.one = u.count Digit.one + 1 := by
  simp [List.count_append]

theorem count_snoc_two (u : Word) : (u ++ [Digit.two]).count Digit.one = u.count Digit.one := by
  simp [List.count_append]

theorem count_snoc_three (u : Word) :
    (u ++ [Digit.three]).count Digit.one = u.count Digit.one := by
  simp [List.count_append]

theorem count_rep_two (k : ℕ) : (List.replicate k Digit.two).count Digit.one = 0 := by
  simp [List.count_replicate]

theorem count_rep_three (k : ℕ) : (List.replicate k Digit.three).count Digit.one = 0 := by
  simp [List.count_replicate]

/-- The four shapes of a parent pair: the two singleton families and the two central-pair parities. -/
def Form (u : Word) (X Y : BinaryWord) : Prop :=
  (∃ k : ℕ, u = List.replicate (k + 1) Digit.three ∧ X = [Letter.p]
      ∧ Y = Letter.q :: List.replicate (k + 1) Letter.p) ∨
  (∃ k : ℕ, u = List.replicate k Digit.two ∧ Y = [Letter.q]
      ∧ X = List.replicate (2 * k) Letter.q ++ [Letter.p]) ∨
  (u.count Digit.one % 2 = 0 ∧ CForm0 X Y) ∨
  (u.count Digit.one % 2 = 1 ∧ CForm1 X Y)

/-- One digit step preserves `Form`, with the next parents given by the digit. -/
theorem form_step {u : Word} {X Y : BinaryWord} (h : Form u X Y) :
    Form (u ++ [Digit.one]) (childWords u X Y).1 (childWords u X Y).2 ∧
    Form (u ++ [Digit.two]) (childWords u X Y).1 Y ∧
    Form (u ++ [Digit.three]) X (childWords u X Y).2 := by
  rcases h with ⟨k, rfl, rfl, rfl⟩ | ⟨k, rfl, rfl, rfl⟩ | ⟨hu, a, b, rfl, rfl, hC⟩ |
      ⟨hu, a, b, rfl, rfl, hC⟩
  · -- singleton `3`-family: `u = 3^(k+1)`, `X = p`, `Y = q p^(k+1)`
    have h0 : (List.replicate (k + 1) Digit.three).count Digit.one = 0 := count_rep_three _
    rw [childWords_even_gen (by rw [h0])]
    refine ⟨Or.inr (Or.inr (Or.inr ⟨by rw [count_snoc_one, h0], ?_⟩)),
      Or.inr (Or.inr (Or.inl ⟨by rw [count_snoc_two, h0], ?_⟩)),
      Or.inl ⟨k + 1, (List.replicate_succ').symm, rfl, ?_⟩⟩
    · exact ⟨List.replicate (k + 1) Letter.p ++ [Letter.q] ++ List.replicate (k + 1) Letter.p,
        List.replicate (k + 1) Letter.p, by simp [cw], by simp [cw], cen_rqr (k + 1)⟩
    · exact ⟨List.replicate (k + 1) Letter.p ++ [Letter.q] ++ List.replicate (k + 1) Letter.p,
        List.replicate k Letter.p, by simp [cw], by simp only [cw]; rw [List.replicate_succ'], cen_a2 k⟩
    · simp [List.replicate_succ']
  · -- singleton `2`-family: `u = 2^k`, `Y = q`, `X = q^(2k) p`
    have hpar : (List.replicate k Digit.two).count Digit.one % 2 = 0 := by rw [count_rep_two]
    rw [childWords_even_gen hpar]
    refine ⟨Or.inr (Or.inr (Or.inr ⟨by simp [count_rep_two], ?_⟩)),
      Or.inr (Or.inl ⟨k + 1, (List.replicate_succ').symm, rfl, ?_⟩), ?_⟩
    · exact ⟨List.replicate (2 * k + 1) Letter.q, List.replicate (2 * k) Letter.q,
        by simp [cw, List.replicate_succ], by simp [cw], cen_pow_q (2 * k)⟩
    · have e : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
      rw [e]; simp [List.replicate_succ]
    · cases k with
      | zero => exact Or.inl ⟨0, by simp, by simp, by simp⟩
      | succ j =>
        have e : 2 * (j + 1) = 2 * j + 1 + 1 := by ring
        refine Or.inr (Or.inr (Or.inl ⟨by simp [count_rep_two], ?_⟩))
        refine ⟨List.replicate (2 * j + 1) Letter.q, List.replicate (2 * (j + 1)) Letter.q, ?_, ?_, ?_⟩
        · rw [e]; simp [cw, List.replicate_succ]
        · simp [cw]
        · rw [e]; exact cen_pow_q _
  · -- central pair of even parity
    rw [childWords_even_gen hu]
    refine ⟨Or.inr (Or.inr (Or.inr ⟨by rw [count_snoc_one]; omega, c0_one hC⟩)),
      Or.inr (Or.inr (Or.inl ⟨by rw [count_snoc_two]; exact hu, c0_two hC⟩)),
      Or.inr (Or.inr (Or.inl ⟨by rw [count_snoc_three]; exact hu, c0_three hC⟩))⟩
  · -- central pair of odd parity
    rw [childWords_odd_gen hu]
    refine ⟨Or.inr (Or.inr (Or.inl ⟨by rw [count_snoc_one]; omega, c1_one hC⟩)),
      Or.inr (Or.inr (Or.inr ⟨by rw [count_snoc_two]; exact hu, c1_two hC⟩)),
      Or.inr (Or.inr (Or.inr ⟨by rw [count_snoc_three]; exact hu, c1_three hC⟩))⟩

/-- Every even-root state `Q_(u)` has the form `Form u X Y`. -/
theorem quadAt_form (u : Word) :
    ∃ X Y : BinaryWord, quadAt [] u = ⟨(childWords u X Y).1, (childWords u X Y).2, X, Y⟩
      ∧ Form u X Y := by
  induction u using List.reverseRecOn with
  | nil =>
    refine ⟨[Letter.p], [Letter.q], ?_, Or.inr (Or.inl ⟨0, rfl, rfl, by simp⟩)⟩
    rw [quadAt_nil]; rfl
  | append_singleton u d ih =>
    obtain ⟨X, Y, hq, hF⟩ := ih
    obtain ⟨h1, h2, h3⟩ := form_step hF
    cases d with
    | one => exact ⟨_, _, by rw [quadAt_append_singleton, hq]; simp [WordQuad.step], h1⟩
    | two => exact ⟨_, _, by rw [quadAt_append_singleton, hq]; simp [WordQuad.step], h2⟩
    | three => exact ⟨_, _, by rw [quadAt_append_singleton, hq]; simp [WordQuad.step], h3⟩

/-- Both children of every state are wrapped palindromes `cw m`, `cw m'`. -/
theorem children_pal {u : Word} {X Y : BinaryWord} (h : Form u X Y) :
    ∃ m m' : BinaryWord, m.reverse = m ∧ m'.reverse = m' ∧
      (childWords u X Y).1 = cw m ∧ (childWords u X Y).2 = cw m' := by
  rcases h with ⟨k, rfl, rfl, rfl⟩ | ⟨k, rfl, rfl, rfl⟩ | ⟨hu, a, b, rfl, rfl, hC⟩ |
      ⟨hu, a, b, rfl, rfl, hC⟩
  · have h0 : (List.replicate (k + 1) Digit.three).count Digit.one % 2 = 0 := by
      rw [count_rep_three]
    refine ⟨List.replicate (k + 1) Letter.p ++ [Letter.q] ++ List.replicate (k + 1) Letter.p,
      List.replicate (k + 1) Letter.p, ?_, ?_, ?_, ?_⟩
    · simp [List.reverse_append, List.reverse_replicate]
    · simp [List.reverse_replicate]
    · rw [childWords_even_gen h0]; simp [cw]
    · rw [childWords_even_gen h0]; simp [cw]
  · have h0 : (List.replicate k Digit.two).count Digit.one % 2 = 0 := by
      rw [count_rep_two]
    refine ⟨List.replicate (2 * k + 1) Letter.q, List.replicate (2 * k) Letter.q, ?_, ?_, ?_, ?_⟩
    · simp [List.reverse_replicate]
    · simp [List.reverse_replicate]
    · rw [childWords_even_gen h0]; simp [cw, List.replicate_succ]
    · rw [childWords_even_gen h0]; simp [cw]
  · obtain ⟨ha, hb, hM⟩ := hC
    have hMr := mid_rev_even (M := b ++ [Letter.p, Letter.q] ++ a) ha hb rfl hM
    have k1 := k1_even (M := b ++ [Letter.p, Letter.q] ++ a) rfl hM
    rw [childWords_even_gen hu]
    exact ⟨(b ++ [Letter.p, Letter.q]) ++ (b ++ [Letter.p, Letter.q] ++ a),
      b ++ [Letter.p, Letter.q] ++ a, z_rev_even hb hMr k1, hMr, by simp [cw], by simp [cw]⟩
  · obtain ⟨hb, ha, hN⟩ := hC
    have hNr := mid_rev_odd ha hb (N := a ++ [Letter.p, Letter.q] ++ b) rfl hN
    rw [childWords_odd_gen hu]
    exact ⟨(a ++ [Letter.p, Letter.q] ++ b) ++ [Letter.p, Letter.q] ++ b,
      a ++ [Letter.p, Letter.q] ++ b, r_rev_odd ha hb rfl hN, hNr, by simp [cw], by simp [cw]⟩

end Invariant

end FLatticePaper.Tiles
