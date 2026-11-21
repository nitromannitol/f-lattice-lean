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

theorem quad_even (u : Word) :
    ∃ m m' : BinaryWord, m.reverse = m ∧ m'.reverse = m' ∧
      (quadAt [] u).childP = cw m ∧ (quadAt [] u).childQ = cw m' := by
  obtain ⟨X, Y, hq, hF⟩ := quadAt_form u
  obtain ⟨m, m', hm, hm', h1, h2⟩ := children_pal hF
  exact ⟨m, m', hm, hm', by rw [hq]; exact h1, by rw [hq]; exact h2⟩

theorem quadAt_of_even {w0 : Word} (h : w0.count Digit.one % 2 = 0) (u : Word) :
    quadAt w0 u = quadAt [] u :=
  quadAt_congr (by simp [h]) u

theorem quadAt_of_odd {w0 : Word} (h : w0.count Digit.one % 2 = 1) (u : Word) :
    quadAt w0 u = (quadAt [] u).rev := by
  rw [quadAt_congr (w0' := [Digit.one]) (by simp [h]) u, quadAt_one_eq_rev]

theorem isAP_cw {m : BinaryWord} (hm : m.reverse = m) : IsAlmostPalindrome (cw m) :=
  ⟨Letter.q, Letter.p, m, hm, rfl⟩

theorem isAP_rev {w : BinaryWord} (h : IsAlmostPalindrome w) : IsAlmostPalindrome w.reverse := by
  obtain ⟨f, l, m, hm, rfl⟩ := h
  exact ⟨l, f, m, hm, by simp [List.reverse_append, hm]⟩

/-- `lemma:almost_palindrome` (1): both binary words are almost palindromes. -/
theorem almost_palindrome_one (w0 u : Word) :
    IsAlmostPalindrome (quadAt w0 u).childP ∧ IsAlmostPalindrome (quadAt w0 u).childQ := by
  rcases Nat.mod_two_eq_zero_or_one (w0.count Digit.one) with h | h
  · rw [quadAt_of_even h u]
    obtain ⟨m, m', hm, hm', h1, h2⟩ := quad_even u
    rw [h1, h2]
    exact ⟨isAP_cw hm, isAP_cw hm'⟩
  · rw [quadAt_of_odd h u]
    obtain ⟨m, m', hm, hm', h1, h2⟩ := quad_even u
    show IsAlmostPalindrome (quadAt [] u).childP.reverse ∧
      IsAlmostPalindrome (quadAt [] u).childQ.reverse
    rw [h1, h2]
    exact ⟨isAP_rev (isAP_cw hm), isAP_rev (isAP_cw hm')⟩

theorem getLast_wrap (m : BinaryWord) (x y : Letter) :
    (x :: (m ++ [y])).getLast? = some y := by
  induction m generalizing x with
  | nil => simp
  | cons z zs ih => simpa using ih z

/-- `lemma:almost_palindrome` (2): the endpoint letters are fixed by the parity of `w0`. -/
theorem almost_palindrome_two (w0 u : Word) :
    (w0.count Digit.one % 2 = 0 →
      (quadAt w0 u).childP.head? = some .q ∧ (quadAt w0 u).childP.getLast? = some .p ∧
      (quadAt w0 u).childQ.head? = some .q ∧ (quadAt w0 u).childQ.getLast? = some .p) ∧
    (w0.count Digit.one % 2 = 1 →
      (quadAt w0 u).childP.head? = some .p ∧ (quadAt w0 u).childP.getLast? = some .q ∧
      (quadAt w0 u).childQ.head? = some .p ∧ (quadAt w0 u).childQ.getLast? = some .q) := by
  constructor
  · intro h
    rw [quadAt_of_even h u]
    obtain ⟨m, m', hm, hm', h1, h2⟩ := quad_even u
    rw [h1, h2]
    simp [cw, getLast_wrap]
  · intro h
    rw [quadAt_of_odd h u]
    obtain ⟨m, m', hm, hm', h1, h2⟩ := quad_even u
    show ((quadAt [] u).childP.reverse).head? = some .p ∧
      ((quadAt [] u).childP.reverse).getLast? = some .q ∧
      ((quadAt [] u).childQ.reverse).head? = some .p ∧
      ((quadAt [] u).childQ.reverse).getLast? = some .q
    rw [h1, h2]
    simp [cw, getLast_wrap]

end Invariant

section Agreement

/-- Even-parity agreement of `lemma:almost_palindrome` (3). -/
def AgreeE (P Q : BinaryWord) : Prop :=
  slice2 P (min P.length Q.length) = slice2 Q.reverse (min P.length Q.length) ∧
  slice2 P (min P.length (2 * Q.length)) = slice2 (Q ++ Q).reverse (min P.length (2 * Q.length))

/-- Odd-parity agreement of `lemma:almost_palindrome` (3). -/
def AgreeO (P Q : BinaryWord) : Prop :=
  slice2 P.reverse (min P.length Q.length) = slice2 Q (min P.length Q.length) ∧
  slice2 P.reverse (min P.length (2 * Q.length)) = slice2 (Q ++ Q) (min P.length (2 * Q.length))

/-- A slice is read off any decomposition of `w.drop 1` whose head has the right length. -/
theorem slice2_eq_of {w W S : BinaryWord} {n : ℕ} (h : w.drop 1 = W ++ S)
    (hn : n - 1 = W.length) : slice2 w n = W := by
  unfold slice2
  rw [h, hn]
  simp

/-- The identity `N p q N = (b q p N) q p a` from `N = a p q b = b q p a`. -/
theorem n_pn {a b N : BinaryWord} (hN1 : N = a ++ [Letter.p, Letter.q] ++ b)
    (hN2 : N = b ++ [Letter.q, Letter.p] ++ a) :
    N ++ [Letter.p, Letter.q] ++ N = (b ++ [Letter.q, Letter.p] ++ N) ++ [Letter.q, Letter.p] ++ a := by
  calc N ++ [Letter.p, Letter.q] ++ N
      = N ++ [Letter.p, Letter.q] ++ (b ++ [Letter.q, Letter.p] ++ a) := by rw [← hN2]
    _ = (N ++ [Letter.p, Letter.q] ++ b) ++ [Letter.q, Letter.p] ++ a := by
          simp [List.append_assoc]
    _ = (b ++ [Letter.q, Letter.p] ++ N) ++ [Letter.q, Letter.p] ++ a := by
          rw [hR_odd hN1 hN2]

theorem agreeE_c0 {a b : BinaryWord} (hC : Cen a b) :
    AgreeE (cw b ++ cw b ++ cw a) (cw b ++ cw a) := by
  obtain ⟨ha, hb, hM⟩ := hC
  have hMr := mid_rev_even (M := b ++ [Letter.p, Letter.q] ++ a) ha hb rfl hM
  have k1 := k1_even (M := b ++ [Letter.p, Letter.q] ++ a) rfl hM
  -- the even child `P` drops to `W1 ++ S1` with `W1 = M q`
  have hP1 : (cw b ++ cw b ++ cw a).drop 1
      = ((b ++ [Letter.p, Letter.q] ++ a) ++ [Letter.q]) ++ (Letter.p :: (b ++ [Letter.p])) := by
    have e : cw b ++ cw b ++ cw a
        = Letter.q :: (((b ++ [Letter.p, Letter.q]) ++ (b ++ [Letter.p, Letter.q] ++ a)) ++ [Letter.p]) := by
      simp [cw]
    rw [e]
    simp only [List.drop_succ_cons, List.drop_zero]
    rw [k1]
    simp [List.append_assoc]
  have e0 : cw b ++ cw a = Letter.q :: ((b ++ [Letter.p, Letter.q] ++ a) ++ [Letter.p]) := by
    simp [cw]
  have hQr : (cw b ++ cw a).reverse
      = Letter.p :: ((b ++ [Letter.p, Letter.q] ++ a) ++ [Letter.q]) := by
    rw [e0, List.reverse_cons, List.reverse_append, hMr]; simp
  -- the reversed even child drops to `M q`
  have hQ1 : (cw b ++ cw a).reverse.drop 1 = ((b ++ [Letter.p, Letter.q] ++ a) ++ [Letter.q]) ++ [] := by
    rw [hQr]; simp
  -- the even child, after its head, is `M q p b p` in full
  have hP2 : (cw b ++ cw b ++ cw a).drop 1
      = ((b ++ [Letter.p, Letter.q] ++ a) ++ [Letter.q, Letter.p] ++ b ++ [Letter.p]) ++ [] := by
    rw [hP1]; simp [List.append_assoc]
  have hQQ : ((cw b ++ cw a) ++ (cw b ++ cw a)).reverse.drop 1
      = ((b ++ [Letter.p, Letter.q] ++ a) ++ [Letter.q, Letter.p] ++ b ++ [Letter.p])
          ++ ([Letter.q] ++ a ++ [Letter.q]) := by
    rw [List.reverse_append, hQr]; simp [List.append_assoc]
  have hn1 : min (cw b ++ cw b ++ cw a).length (cw b ++ cw a).length - 1
      = ((b ++ [Letter.p, Letter.q] ++ a) ++ [Letter.q]).length := by
    simp [cw]; omega
  have hn2 : min (cw b ++ cw b ++ cw a).length (2 * (cw b ++ cw a).length) - 1
      = ((b ++ [Letter.p, Letter.q] ++ a) ++ [Letter.q, Letter.p] ++ b ++ [Letter.p]).length := by
    simp [cw]; omega
  refine ⟨?_, ?_⟩
  · rw [slice2_eq_of hP1 hn1, slice2_eq_of hQ1 hn1]
  · rw [slice2_eq_of hP2 hn2, slice2_eq_of hQQ hn2]

/-- The odd-parity agreement for the child pair `(N p q b p q b, N p q b)` with the pair word `N`. -/
theorem agreeO_gen {a b N : BinaryWord} (hb : b.reverse = b) (hNr : N.reverse = N)
    (hN1 : N = a ++ [Letter.p, Letter.q] ++ b) (hN2 : N = b ++ [Letter.q, Letter.p] ++ a) :
    AgreeO (cw a ++ cw b ++ cw b) (cw a ++ cw b) := by
  have hR := hR_odd hN1 hN2
  have hNN := n_pn hN1 hN2
  have eQ : cw a ++ cw b = Letter.q :: (N ++ [Letter.p]) := by simp [cw, hN1]
  have eP : cw a ++ cw b ++ cw b
      = Letter.q :: ((N ++ [Letter.p, Letter.q] ++ b) ++ [Letter.p]) := by
    simp [cw, hN1]
  have eR : (cw a ++ cw b ++ cw b).reverse
      = Letter.p :: ((b ++ [Letter.q, Letter.p] ++ N) ++ [Letter.q]) := by
    rw [eP]; simp [List.reverse_append, hb, hNr, List.append_assoc]
  -- left slice: `N p` on both sides
  have hL1 : (cw a ++ cw b ++ cw b).reverse.drop 1
      = (N ++ [Letter.p]) ++ (Letter.q :: (b ++ [Letter.q])) := by
    rw [eR]
    simp only [List.drop_succ_cons, List.drop_zero]
    rw [← hR]
    simp [List.append_assoc]
  have hR1 : (cw a ++ cw b).drop 1 = (N ++ [Letter.p]) ++ [] := by
    rw [eQ]
    simp only [List.drop_succ_cons, List.drop_zero]
    simp
  have hn1 : min (cw a ++ cw b ++ cw b).length (cw a ++ cw b).length - 1
      = (N ++ [Letter.p]).length := by
    simp [cw, hN1]
  -- right slice: the word `b q p N q`
  have hL2 : (cw a ++ cw b ++ cw b).reverse.drop 1
      = (b ++ [Letter.q, Letter.p] ++ N ++ [Letter.q]) ++ [] := by
    rw [eR]
    simp only [List.drop_succ_cons, List.drop_zero]
    simp [List.append_assoc]
  have hQ2 : ((cw a ++ cw b) ++ (cw a ++ cw b)).drop 1
      = (b ++ [Letter.q, Letter.p] ++ N ++ [Letter.q]) ++ ([Letter.p] ++ a ++ [Letter.p]) := by
    calc ((cw a ++ cw b) ++ (cw a ++ cw b)).drop 1
        = (N ++ [Letter.p, Letter.q] ++ N) ++ [Letter.p] := by
          rw [eQ]; simp [List.append_assoc]
      _ = ((b ++ [Letter.q, Letter.p] ++ N) ++ [Letter.q, Letter.p] ++ a) ++ [Letter.p] := by
          rw [hNN]
      _ = (b ++ [Letter.q, Letter.p] ++ N ++ [Letter.q]) ++ ([Letter.p] ++ a ++ [Letter.p]) := by
          simp [List.append_assoc]
  have hn2 : min (cw a ++ cw b ++ cw b).length (2 * (cw a ++ cw b).length) - 1
      = (b ++ [Letter.q, Letter.p] ++ N ++ [Letter.q]).length := by
    simp [cw, hN1]; omega
  refine ⟨?_, ?_⟩
  · rw [slice2_eq_of hL1 hn1, slice2_eq_of hR1 hn1]
  · rw [slice2_eq_of hL2 hn2, slice2_eq_of hQ2 hn2]

theorem agreeO_c1 {a b : BinaryWord} (hC : Cen b a) :
    AgreeO (cw a ++ cw b ++ cw b) (cw a ++ cw b) := by
  obtain ⟨hb, ha, hN⟩ := hC
  exact agreeO_gen hb (mid_rev_odd ha hb (N := a ++ [Letter.p, Letter.q] ++ b) rfl hN) rfl hN

/-- The singleton `3`-family: children `cw (R q R)` and `cw R` with `R = p^(k+1)`. -/
theorem agreeE_A' {R : BinaryWord} (hRr : R.reverse = R) (hR : R ++ [Letter.p] = Letter.p :: R) :
    AgreeE (cw (R ++ [Letter.q] ++ R)) (cw R) := by
  have hQr : (cw R).reverse = Letter.p :: (R ++ [Letter.q]) := by
    simp [cw, List.reverse_append, hRr]
  have hP1 : (cw (R ++ [Letter.q] ++ R)).drop 1 = (R ++ [Letter.q]) ++ (R ++ [Letter.p]) := by
    simp [cw, List.append_assoc]
  have hP2 : (cw (R ++ [Letter.q] ++ R)).drop 1 = (R ++ [Letter.q] ++ R ++ [Letter.p]) ++ [] := by
    simp [cw, List.append_assoc]
  have hQ1 : (cw R).reverse.drop 1 = (R ++ [Letter.q]) ++ [] := by
    rw [hQr]; simp
  have hpq : Letter.p :: (R ++ [Letter.q]) = (R ++ [Letter.p]) ++ [Letter.q] := by
    rw [hR]; simp
  have hQQ : ((cw R) ++ (cw R)).reverse.drop 1 = (R ++ [Letter.q] ++ R ++ [Letter.p]) ++ [Letter.q] := by
    have e1 : ((cw R) ++ (cw R)).reverse.drop 1
        = (R ++ [Letter.q]) ++ (Letter.p :: (R ++ [Letter.q])) := by
      rw [List.reverse_append, hQr]; simp
    rw [e1, hpq]; simp [List.append_assoc]
  have hn1 : min (cw (R ++ [Letter.q] ++ R)).length (cw R).length - 1 = (R ++ [Letter.q]).length := by
    simp [cw]
  have hn2 : min (cw (R ++ [Letter.q] ++ R)).length (2 * (cw R).length) - 1
      = (R ++ [Letter.q] ++ R ++ [Letter.p]).length := by
    simp [cw]; omega
  refine ⟨?_, ?_⟩
  · rw [slice2_eq_of hP1 hn1, slice2_eq_of hQ1 hn1]
  · rw [slice2_eq_of hP2 hn2, slice2_eq_of hQQ hn2]

/-- The singleton `2`-family: children `cw (S q)` and `cw S` with `S = q^(2k)`. -/
theorem agreeE_B' {S : BinaryWord} (hSr : S.reverse = S) :
    AgreeE (cw (S ++ [Letter.q])) (cw S) := by
  have hQr : (cw S).reverse = Letter.p :: (S ++ [Letter.q]) := by
    simp [cw, List.reverse_append, hSr]
  have hP1 : (cw (S ++ [Letter.q])).drop 1 = (S ++ [Letter.q]) ++ [Letter.p] := by
    simp [cw]
  have hP2 : (cw (S ++ [Letter.q])).drop 1 = ((S ++ [Letter.q]) ++ [Letter.p]) ++ [] := by
    simp [cw]
  have hQ1 : (cw S).reverse.drop 1 = (S ++ [Letter.q]) ++ [] := by
    rw [hQr]; simp
  have hQQ : ((cw S) ++ (cw S)).reverse.drop 1 = ((S ++ [Letter.q]) ++ [Letter.p]) ++ (S ++ [Letter.q]) := by
    rw [List.reverse_append, hQr]; simp [List.append_assoc]
  have hn1 : min (cw (S ++ [Letter.q])).length (cw S).length - 1 = (S ++ [Letter.q]).length := by
    simp [cw]
  have hn2 : min (cw (S ++ [Letter.q])).length (2 * (cw S).length) - 1
      = ((S ++ [Letter.q]) ++ [Letter.p]).length := by
    simp [cw]; omega
  refine ⟨?_, ?_⟩
  · rw [slice2_eq_of hP1 hn1, slice2_eq_of hQ1 hn1]
  · rw [slice2_eq_of hP2 hn2, slice2_eq_of hQQ hn2]

/-- The agreement of the children at every shape, split by the parity of the word. -/
theorem family_agree {u : Word} {X Y : BinaryWord} (hF : Form u X Y) :
    (u.count Digit.one % 2 = 0 → AgreeE (childWords u X Y).1 (childWords u X Y).2) ∧
    (u.count Digit.one % 2 = 1 → AgreeO (childWords u X Y).1 (childWords u X Y).2) := by
  rcases hF with ⟨k, rfl, rfl, rfl⟩ | ⟨k, rfl, rfl, rfl⟩ | ⟨hu, a, b, rfl, rfl, hC⟩ |
      ⟨hu, a, b, rfl, rfl, hC⟩
  · have hpar : (List.replicate (k + 1) Digit.three).count Digit.one % 2 = 0 := by
      rw [count_rep_three]
    refine ⟨fun _ => ?_, fun h => ?_⟩
    · rw [childWords_even_gen hpar]
      have eP : (Letter.q :: List.replicate (k + 1) Letter.p)
          ++ (Letter.q :: List.replicate (k + 1) Letter.p) ++ [Letter.p]
          = cw (List.replicate (k + 1) Letter.p ++ [Letter.q] ++ List.replicate (k + 1) Letter.p) := by
        simp [cw]
      have eQ : (Letter.q :: List.replicate (k + 1) Letter.p) ++ [Letter.p]
          = cw (List.replicate (k + 1) Letter.p) := by
        simp [cw]
      show AgreeE ((Letter.q :: List.replicate (k + 1) Letter.p)
          ++ (Letter.q :: List.replicate (k + 1) Letter.p) ++ [Letter.p])
        ((Letter.q :: List.replicate (k + 1) Letter.p) ++ [Letter.p])
      rw [eP, eQ]
      exact agreeE_A' List.reverse_replicate (rep_snoc (k + 1) Letter.p)
    · rw [count_rep_three] at h; norm_num at h
  · have hpar : (List.replicate k Digit.two).count Digit.one % 2 = 0 := by
      rw [count_rep_two]
    refine ⟨fun _ => ?_, fun h => ?_⟩
    · rw [childWords_even_gen hpar]
      have eP : [Letter.q] ++ [Letter.q] ++ (List.replicate (2 * k) Letter.q ++ [Letter.p])
          = cw (List.replicate (2 * k) Letter.q ++ [Letter.q]) := by
        rw [rep_snoc]; simp [cw]
      have eQ : [Letter.q] ++ (List.replicate (2 * k) Letter.q ++ [Letter.p])
          = cw (List.replicate (2 * k) Letter.q) := by
        simp [cw]
      show AgreeE ([Letter.q] ++ [Letter.q] ++ (List.replicate (2 * k) Letter.q ++ [Letter.p]))
        ([Letter.q] ++ (List.replicate (2 * k) Letter.q ++ [Letter.p]))
      rw [eP, eQ]
      exact agreeE_B' List.reverse_replicate
    · rw [count_rep_two] at h; norm_num at h
  · refine ⟨fun _ => ?_, fun h => ?_⟩
    · rw [childWords_even_gen hu]; exact agreeE_c0 hC
    · exact absurd h (by omega)
  · refine ⟨fun h => ?_, fun _ => ?_⟩
    · exact absurd h (by omega)
    · rw [childWords_odd_gen hu]; exact agreeO_c1 hC

theorem family_agree_quad (u : Word) :
    (u.count Digit.one % 2 = 0 → AgreeE (quadAt [] u).childP (quadAt [] u).childQ) ∧
    (u.count Digit.one % 2 = 1 → AgreeO (quadAt [] u).childP (quadAt [] u).childQ) := by
  obtain ⟨X, Y, hq, hF⟩ := quadAt_form u
  rw [hq]
  exact family_agree hF

end Agreement

/-- `lemma:almost_palindrome` (3): the prefix agreements, read at the parity of the current word. -/
theorem almost_palindrome_three (w0 u : Word) :
    let pw := (quadAt w0 u).childP
    let qw := (quadAt w0 u).childQ
    let n := min pw.length qw.length
    let m := min pw.length (2 * qw.length)
    ((w0 ++ u).count .one % 2 = 0 →
      slice2 pw n = slice2 qw.reverse n ∧ slice2 pw m = slice2 (qw ++ qw).reverse m) ∧
    ((w0 ++ u).count .one % 2 = 1 →
      slice2 pw.reverse n = slice2 qw n ∧ slice2 pw.reverse m = slice2 (qw ++ qw) m) := by
  dsimp only
  have hc : (w0 ++ u).count Digit.one % 2 = (w0.count Digit.one + u.count Digit.one) % 2 := by
    rw [List.count_append]
  rcases Nat.mod_two_eq_zero_or_one (w0.count Digit.one) with h | h
  · rw [quadAt_of_even h u]
    obtain ⟨e1, e2⟩ := family_agree_quad u
    exact ⟨fun hp => e1 (by omega), fun hp => e2 (by omega)⟩
  · rw [quadAt_of_odd h u]
    obtain ⟨e1, e2⟩ := family_agree_quad u
    dsimp only [WordQuad.rev]
    constructor
    · intro hp
      obtain ⟨f1, f2⟩ := e2 (by omega)
      constructor
      · simpa using f1
      · simpa [List.reverse_append] using f2
    · intro hp
      obtain ⟨f1, f2⟩ := e1 (by omega)
      constructor
      · simpa using f1
      · simpa [List.reverse_append] using f2

end FLatticePaper.Tiles
