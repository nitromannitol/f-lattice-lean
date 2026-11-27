import FLatticePaper.Tiles.ClosedPathCycle

/-! # Condition (C): the offsets around the closed path of the standard pieces sum to zero

The closed path of each standard child runs through its six copies: the two copies of the plain parent and the four copies of
the doubled one (odd child), or the four copies of the doubled parent and the two of the plain one (even child). Each of the
six interfaces is read at one point: the four mixed interfaces at a point of a corner tile of both copies, the two doubled ones
at the translate of a point of the overlap of the parent with its translate. This follows the closed-path computation of
`notes/C/C_other_proof_all_cases.md` (section "Standard decomposition with plain copies", tables (1) and (2)). The text's proof
(Step 1 of `lemma:weak_standard_odometer_properties`, lines 3536-3545 at 274ad18) reaches the same conclusion through the boundary
odometer `o_∂` and eq:boundary_path_difference; the computation here reads the constants at one point of each interface, and it
is organised by the text's four cases: the odd and the even child, each with `W_1` even (even-first) or odd (odd-first).

Notation: `A = v_{p,1}`, `B = v_{p,2}`, `U = v_{q,1}`, `V = v_{q,2}` for the odd parent `p` and the even parent `q`,
`a = a_{p,2} = (n_p, -d_p)`, `b = a_{q,2} = (n_q, -d_q)`, `e₁ = 1`, `e₂ = i`. A piece is a function
`f i z = o(z - off_i) + α_i · z + c_i` of a parent odometer `o`, with the offsets of `def:standard_tiles` (`MixedPieces`) and the
affine factors of `eq:std_odometer_decomposition` (`SurgicalOdometerStep`): odd child `(0, b, 0, 0, a, a)` for
`(P^+, P^-, Q^{+,1}, Q^{+,2}, Q^{-,1}, Q^{-,2})`, even child `(0, a, b, a + b, 0, 2a)` for
`(P^{+,1}, P^{+,2}, P^{-,1}, P^{-,2}, Q^+, Q^-)`, the second copy of a doubled piece carrying the affine factor of its translation.

The only facts about the parents are the two corner differences of each (`ClosedPathCorners.corner_diffs`, here with
`e₁, e₂`): for a parent `S` with vectors `X, Y` and second affine factor `(n, -d)`,
`S(X + Y + e₁ - e₂) - S(X + Y - e₂) - (S(e₁) - S(0)) = n` and `S(Y + e₁) - S(Y + e₁ - e₂) - (S(X) - S(X - e₂)) = -d`.
The two doubled interfaces use the same pair of parent points with opposite signs, so no doubling constant enters. The
vector identities are `a·V = b·B` and `2 a·U + b·A = 0`. -/

namespace FLatticePaper.Tiles.ClosedPathSum

/-- The dot product of two sites. -/
def dot2 (a z : ℤ × ℤ) : ℤ := a.1 * z.1 + a.2 * z.2

/-- The unit vectors `e₁ = 1`, `e₂ = i`. -/
abbrev e₁ : ℤ × ℤ := (1, 0)
abbrev e₂ : ℤ × ℤ := (0, 1)

/-- The corner differences of a parent `S` with vectors `X, Y` and second affine factor `(n, -d)`. -/
def CornerDiffs (S : ℤ × ℤ → ℤ) (X Y : ℤ × ℤ) (n d : ℤ) : Prop :=
  S (X + Y + e₁ - e₂) - S (X + Y - e₂) - (S e₁ - S 0) = n ∧
  S (Y + e₁) - S (Y + e₁ - e₂) - (S X - S (X - e₂)) = -d

/-- A piece is a translate of a parent odometer `o` by `off`, plus the affine function `α · z + c`. -/
def IsPiece (f : ℤ × ℤ → ℤ) (o : ℤ × ℤ → ℤ) (off α : ℤ × ℤ) (c : ℤ) : Prop :=
  ∀ z, f z = o (z - off) + dot2 α z + c

theorem piece_val {f o : ℤ × ℤ → ℤ} {off α : ℤ × ℤ} {c : ℤ} (h : IsPiece f o off α c) (z r : ℤ × ℤ)
    (hz : z - off = r) : f z = o r + dot2 α z + c := by
  rw [h z, hz]

/-- The vectors of the step and the two affine factors, in the fractions `p = n_p/d_p` (odd parent) and
`q = n_q/d_q` (even parent). -/
structure StepVectors (np dp nq dq : ℤ) (A B U V a b : ℤ × ℤ) : Prop where
  hA : A = (2 * dp, 2 * np)
  hB : B = (np - dp, np + dp)
  hU : U = (dq, nq)
  hV : V = (nq - dq, nq + dq)
  ha : a = (np, -dp)
  hb : b = (nq, -dq)

/-! ### The odd child -/

/-- **Odd child, `W_1` even (even-first).** The pieces `P^+, P^-` at `2U, V`, `Q^{+,1}, Q^{+,2}` at `0, U` and
`Q^{-,1}, Q^{-,2}` at `A + B, A + B + U`. Along the closed path `Q^{+,1}, Q^{+,2}, P^+, Q^{-,2}, Q^{-,1}, P^-` the offsets read at
`U`, `2U`, `2U + A + B - e₂`, `A + B + U`, `A + B + V + e₁ - e₂`, `V + e₁` sum to zero. -/
theorem odd_even_first (np dp nq dq : ℤ) (A B U V a b : ℤ × ℤ) (hv : StepVectors np dp nq dq A B U V a b)
    (oP oQ : ℤ × ℤ → ℤ) (f : ℕ → ℤ × ℤ → ℤ) (c : ℕ → ℤ)
    (h0 : IsPiece (f 0) oP (U + U) 0 (c 0)) (h1 : IsPiece (f 1) oP V b (c 1))
    (h2 : IsPiece (f 2) oQ 0 0 (c 2)) (h3 : IsPiece (f 3) oQ U 0 (c 3))
    (h4 : IsPiece (f 4) oQ (A + B) a (c 4)) (h5 : IsPiece (f 5) oQ (A + B + U) a (c 5))
    (hP : CornerDiffs oP A B np dp) (hQ : CornerDiffs oQ U V nq dq) :
    (f 2 U - f 3 U) + (f 3 (U + U) - f 0 (U + U)) +
      (f 0 (U + U + (A + B - e₂)) - f 5 (U + U + (A + B - e₂))) + (f 5 (A + B + U) - f 4 (A + B + U)) +
      (f 4 (A + B + (V + e₁ - e₂)) - f 1 (A + B + (V + e₁ - e₂))) + (f 1 (V + e₁) - f 2 (V + e₁)) = 0 := by
  rw [piece_val h2 U U (by abel), piece_val h3 U 0 (by abel),
    piece_val h3 (U + U) U (by abel), piece_val h0 (U + U) 0 (by abel),
    piece_val h0 (U + U + (A + B - e₂)) (A + B - e₂) (by abel),
    piece_val h5 (U + U + (A + B - e₂)) (U - e₂) (by abel),
    piece_val h5 (A + B + U) 0 (by abel), piece_val h4 (A + B + U) U (by abel),
    piece_val h4 (A + B + (V + e₁ - e₂)) (V + e₁ - e₂) (by abel),
    piece_val h1 (A + B + (V + e₁ - e₂)) (A + B + e₁ - e₂) (by abel),
    piece_val h1 (V + e₁) e₁ (by abel), piece_val h2 (V + e₁) (V + e₁) (by abel)]
  obtain ⟨hP1, -⟩ := hP
  obtain ⟨-, hQ2⟩ := hQ
  obtain ⟨hA, hB, hU, hV, ha, hb⟩ := hv
  subst hA hB hU hV ha hb
  simp only [dot2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero]
  linear_combination (-1 : ℤ) * hP1 - hQ2

/-- **Odd child, `W_1` odd (odd-first).** The pieces `P^+, P^-` at `0, 2U + V`, `Q^{+,1}, Q^{+,2}` at `A, A + U` and
`Q^{-,1}, Q^{-,2}` at `B, B + U`. Along the closed path `Q^{+,1}, P^+, Q^{-,1}, Q^{-,2}, P^-, Q^{+,2}` the offsets read at
`A`, `B + e₁`, `B + U`, `B + 2U + V + e₁ - e₂`, `2U + V + A - e₂`, `A + U` sum to zero. -/
theorem odd_odd_first (np dp nq dq : ℤ) (A B U V a b : ℤ × ℤ) (hv : StepVectors np dp nq dq A B U V a b)
    (oP oQ : ℤ × ℤ → ℤ) (f : ℕ → ℤ × ℤ → ℤ) (c : ℕ → ℤ)
    (h0 : IsPiece (f 0) oP 0 0 (c 0)) (h1 : IsPiece (f 1) oP (U + U + V) b (c 1))
    (h2 : IsPiece (f 2) oQ A 0 (c 2)) (h3 : IsPiece (f 3) oQ (A + U) 0 (c 3))
    (h4 : IsPiece (f 4) oQ B a (c 4)) (h5 : IsPiece (f 5) oQ (B + U) a (c 5))
    (hP : CornerDiffs oP A B np dp) (hQ : CornerDiffs oQ U V nq dq) :
    (f 2 A - f 0 A) + (f 0 (B + e₁) - f 4 (B + e₁)) + (f 4 (B + U) - f 5 (B + U)) +
      (f 5 (B + U + (U + V + e₁ - e₂)) - f 1 (B + U + (U + V + e₁ - e₂))) +
      (f 1 (U + U + V + (A - e₂)) - f 3 (U + U + V + (A - e₂))) + (f 3 (A + U) - f 2 (A + U)) = 0 := by
  rw [piece_val h2 A 0 (by abel), piece_val h0 A A (by abel),
    piece_val h0 (B + e₁) (B + e₁) (by abel), piece_val h4 (B + e₁) e₁ (by abel),
    piece_val h4 (B + U) U (by abel), piece_val h5 (B + U) 0 (by abel),
    piece_val h5 (B + U + (U + V + e₁ - e₂)) (U + V + e₁ - e₂) (by abel),
    piece_val h1 (B + U + (U + V + e₁ - e₂)) (B + e₁ - e₂) (by abel),
    piece_val h1 (U + U + V + (A - e₂)) (A - e₂) (by abel),
    piece_val h3 (U + U + V + (A - e₂)) (U + V - e₂) (by abel),
    piece_val h3 (A + U) 0 (by abel), piece_val h2 (A + U) U (by abel)]
  obtain ⟨-, hP2⟩ := hP
  obtain ⟨hQ1, -⟩ := hQ
  obtain ⟨hA, hB, hU, hV, ha, hb⟩ := hv
  subst hA hB hU hV ha hb
  simp only [dot2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero]
  linear_combination hP2 + hQ1

/-! ### The even child -/

/-- **Even child, `W_1` even (even-first).** The pieces `P^{+,1}, P^{+,2}` at `U, U + B`, `P^{-,1}, P^{-,2}` at `V, V + B`,
and `Q^+, Q^-` at `0, A + 2B`. Along the closed path `Q^+, P^{+,1}, P^{+,2}, Q^-, P^{-,2}, P^{-,1}` the offsets read at
`U`, `U + B + e₁`, `U + A + 2B - e₂`, `A + 2B + V + e₁ - e₂`, `V + B + e₁`, `V + e₁` sum to zero. -/
theorem even_even_first (np dp nq dq : ℤ) (A B U V a b : ℤ × ℤ) (hv : StepVectors np dp nq dq A B U V a b)
    (oP oQ : ℤ × ℤ → ℤ) (f : ℕ → ℤ × ℤ → ℤ) (c : ℕ → ℤ)
    (h0 : IsPiece (f 0) oP U 0 (c 0)) (h1 : IsPiece (f 1) oP (U + B) a (c 1))
    (h2 : IsPiece (f 2) oP V b (c 2)) (h3 : IsPiece (f 3) oP (V + B) (a + b) (c 3))
    (h4 : IsPiece (f 4) oQ 0 0 (c 4)) (h5 : IsPiece (f 5) oQ (A + B + B) (a + a) (c 5))
    (hP : CornerDiffs oP A B np dp) (hQ : CornerDiffs oQ U V nq dq) :
    (f 4 U - f 0 U) + (f 0 (U + (B + e₁)) - f 1 (U + (B + e₁))) +
      (f 1 (U + B + (A + B - e₂)) - f 5 (U + B + (A + B - e₂))) +
      (f 5 (A + B + B + (V + e₁ - e₂)) - f 3 (A + B + B + (V + e₁ - e₂))) +
      (f 3 (V + B + e₁) - f 2 (V + B + e₁)) + (f 2 (V + e₁) - f 4 (V + e₁)) = 0 := by
  rw [piece_val h4 U U (by abel), piece_val h0 U 0 (by abel),
    piece_val h0 (U + (B + e₁)) (B + e₁) (by abel), piece_val h1 (U + (B + e₁)) e₁ (by abel),
    piece_val h1 (U + B + (A + B - e₂)) (A + B - e₂) (by abel),
    piece_val h5 (U + B + (A + B - e₂)) (U - e₂) (by abel),
    piece_val h5 (A + B + B + (V + e₁ - e₂)) (V + e₁ - e₂) (by abel),
    piece_val h3 (A + B + B + (V + e₁ - e₂)) (A + B + e₁ - e₂) (by abel),
    piece_val h3 (V + B + e₁) e₁ (by abel), piece_val h2 (V + B + e₁) (B + e₁) (by abel),
    piece_val h2 (V + e₁) e₁ (by abel), piece_val h4 (V + e₁) (V + e₁) (by abel)]
  obtain ⟨hP1, -⟩ := hP
  obtain ⟨-, hQ2⟩ := hQ
  obtain ⟨hA, hB, hU, hV, ha, hb⟩ := hv
  subst hA hB hU hV ha hb
  simp only [dot2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero]
  linear_combination (-1 : ℤ) * hP1 - hQ2

/-- **Even child, `W_1` odd (odd-first).** The pieces `P^{+,1}, P^{+,2}` at `0, B`, `P^{-,1}, P^{-,2}` at `U + V, U + V + B`,
and `Q^+, Q^-` at `A, 2B`. Along the closed path `Q^+, P^{+,1}, P^{+,2}, Q^-, P^{-,2}, P^{-,1}` the offsets read at
`A`, `B + e₁`, `2B + e₁`, `2B + U + V + e₁ - e₂`, `U + V + B + e₁`, `U + V + A - e₂` sum to zero. -/
theorem even_odd_first (np dp nq dq : ℤ) (A B U V a b : ℤ × ℤ) (hv : StepVectors np dp nq dq A B U V a b)
    (oP oQ : ℤ × ℤ → ℤ) (f : ℕ → ℤ × ℤ → ℤ) (c : ℕ → ℤ)
    (h0 : IsPiece (f 0) oP 0 0 (c 0)) (h1 : IsPiece (f 1) oP B a (c 1))
    (h2 : IsPiece (f 2) oP (U + V) b (c 2)) (h3 : IsPiece (f 3) oP (U + V + B) (a + b) (c 3))
    (h4 : IsPiece (f 4) oQ A 0 (c 4)) (h5 : IsPiece (f 5) oQ (B + B) (a + a) (c 5))
    (hP : CornerDiffs oP A B np dp) (hQ : CornerDiffs oQ U V nq dq) :
    (f 4 A - f 0 A) + (f 0 (B + e₁) - f 1 (B + e₁)) + (f 1 (B + (B + e₁)) - f 5 (B + (B + e₁))) +
      (f 5 (B + B + (U + V + e₁ - e₂)) - f 3 (B + B + (U + V + e₁ - e₂))) +
      (f 3 (U + V + B + e₁) - f 2 (U + V + B + e₁)) + (f 2 (U + V + (A - e₂)) - f 4 (U + V + (A - e₂))) = 0 := by
  rw [piece_val h4 A 0 (by abel), piece_val h0 A A (by abel),
    piece_val h0 (B + e₁) (B + e₁) (by abel), piece_val h1 (B + e₁) e₁ (by abel),
    piece_val h1 (B + (B + e₁)) (B + e₁) (by abel), piece_val h5 (B + (B + e₁)) e₁ (by abel),
    piece_val h5 (B + B + (U + V + e₁ - e₂)) (U + V + e₁ - e₂) (by abel),
    piece_val h3 (B + B + (U + V + e₁ - e₂)) (B + e₁ - e₂) (by abel),
    piece_val h3 (U + V + B + e₁) e₁ (by abel), piece_val h2 (U + V + B + e₁) (B + e₁) (by abel),
    piece_val h2 (U + V + (A - e₂)) (A - e₂) (by abel),
    piece_val h4 (U + V + (A - e₂)) (U + V - e₂) (by abel)]
  obtain ⟨-, hP2⟩ := hP
  obtain ⟨hQ1, -⟩ := hQ
  obtain ⟨hA, hB, hU, hV, ha, hb⟩ := hv
  subst hA hB hU hV ha hb
  simp only [dot2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero]
  linear_combination hP2 + hQ1

end FLatticePaper.Tiles.ClosedPathSum
