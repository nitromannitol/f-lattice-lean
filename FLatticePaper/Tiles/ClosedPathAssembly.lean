import FLatticePaper.Tiles.ClosedPathContacts

/-! # Condition (C) for the standard children, from named inputs

The subodometers of the standard step are the placed parent odometers `placedOdd w oP oQ c`, `placedEven w oP oQ c`: copy `i`
of a parent `o` at the offset of `def:standard_tiles` (`MixedPieces`), plus the affine factor of
`eq:std_odometer_decomposition` and an arbitrary constant `c i`. The parents `oP`, `oQ` are arbitrary functions (the odometers of
the odd and the even register, handed over by the joint induction).

Condition (C) (`ChildGlue.ClosedPathOdd`, `ClosedPathEven`) is proved from the following facts, all about one step:

* `hcP`, `hcQ`: the two corner differences of each parent (`ClosedPathCorners.corner_diffs`, from `RespectsAnchored` and (b));
* `hdbl`: (c) of the doubled parent: its difference with its translate by the doubling vector is constant on their overlap;
* `hcompat` (`MixedCompatOdd`, `MixedCompatEven`): local compatibility of two copies of different parents, the difference of
  the subodometers being constant on the marks of both copies (Step 1, `lemma:stacked_zero_one_string` with (d));
* `hexcl`: the two mixed pairs of copies that the text shows never meet (monotonicity of the boundary words) are disjoint;
* `htri`: at the two optional mixed interfaces (the copy of the plain parent meeting the farther copy of a doubled piece), the
  offset at one common point equals the offset through the nearer copy and the doubled interface (the text's point `z*`).

The constants `κ` are those of the closed path (`hexKappa`); the six interfaces of the path agree at their contact points
(`ClosedPathSum`, `ClosedPathContacts`), hence on the whole overlap by local compatibility (`agree_of_witness`). -/

namespace FLatticePaper.Tiles.ClosedPathAssembly

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.SiteInduction
open FLatticePaper.Tiles.ChildGlue FLatticePaper.Tiles.MixedPieces FLatticePaper.Tiles.ClosedPathCycle
open FLatticePaper.Tiles.ClosedPathSum FLatticePaper.Tiles.ClosedPathContacts FLatticePaper.Tiles.StandardClause

/-! ### The placed subodometers -/

/-- The affine factors of the six pieces of the odd child: `b` for `P^-`, `a` for the two copies of `Q^-`, `0` otherwise. -/
def affOdd (p q : Fraction) (i : ℕ) : ℤ × ℤ :=
  if i = 1 then (q.num, -q.den) else if i = 4 ∨ i = 5 then (p.num, -p.den) else 0

/-- The affine factors of the six pieces of the even child: `0, a, b, a + b` for the copies of `P`, `0, 2a` for `Q^±`. -/
def affEven (p q : Fraction) (i : ℕ) : ℤ × ℤ :=
  if i = 1 then (p.num, -p.den) else if i = 2 then (q.num, -q.den) else
    if i = 3 then (p.num, -p.den) + (q.num, -q.den) else if i = 5 then (p.num, -p.den) + (p.num, -p.den) else 0

/-- The placed subodometers of the odd child of `w`. -/
def placedOdd (w : Word) (oP oQ : ℤ × ℤ → ℤ) (c : ℕ → ℤ) (i : ℕ) (z : ℤ × ℤ) : ℤ :=
  if i < 2 then oP (z - (oddP w).getD i 0) + dot2 (affOdd (parentsAt w).odd (parentsAt w).even i) z + c i
  else oQ (z - (oddQ w).getD (i - 2) 0) + dot2 (affOdd (parentsAt w).odd (parentsAt w).even i) z + c i

/-- The placed subodometers of the even child of `w`. -/
def placedEven (w : Word) (oP oQ : ℤ × ℤ → ℤ) (c : ℕ → ℤ) (i : ℕ) (z : ℤ × ℤ) : ℤ :=
  if i < 4 then oP (z - (evenP w).getD i 0) + dot2 (affEven (parentsAt w).odd (parentsAt w).even i) z + c i
  else oQ (z - (evenQ w).getD (i - 4) 0) + dot2 (affEven (parentsAt w).odd (parentsAt w).even i) z + c i

/-- The marks and the domains of the copies of the odd child. -/
abbrev mOdd (w u1 u2 : Word) (i : ℕ) : Set (ℤ × ℤ) := pieceSet (oddP w) (oddQ w) (marksOdd u1) (marksEven u2) i
abbrev dOdd (w u1 u2 : Word) (i : ℕ) : Set (ℤ × ℤ) := pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) i
/-- The marks and the domains of the copies of the even child. -/
abbrev mEven (w u1 u2 : Word) (i : ℕ) : Set (ℤ × ℤ) := pieceSet (evenP w) (evenQ w) (marksOdd u1) (marksEven u2) i
abbrev dEven (w u1 u2 : Word) (i : ℕ) : Set (ℤ × ℤ) := pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) i

/-- **Local compatibility of the mixed pairs, odd child** (Step 1: `lemma:stacked_zero_one_string` with (d)): for every copy
`i < 2` of the odd parent and `2 ≤ j < 6` of the even parent, the difference of the subodometers is constant on the marks of
both copies. -/
def MixedCompatOdd (w u1 u2 : Word) (f : ℕ → ℤ × ℤ → ℤ) : Prop :=
  ∀ i j, i < 2 → 2 ≤ j → j < 6 → ∃ C : ℤ, ∀ z, z ∈ mOdd w u1 u2 i → z ∈ mOdd w u1 u2 j → f i z - f j z = C

/-- **Local compatibility of the mixed pairs, even child**: copies `i < 4` of the odd parent, `4 ≤ j < 6` of the even one. -/
def MixedCompatEven (w u1 u2 : Word) (f : ℕ → ℤ × ℤ → ℤ) : Prop :=
  ∀ i j, i < 4 → 4 ≤ j → j < 6 → ∃ C : ℤ, ∀ z, z ∈ mEven w u1 u2 i → z ∈ mEven w u1 u2 j → f i z - f j z = C

/-! ### Membership in a translate -/

theorem mem_shift (S : Set (ℤ × ℤ)) (v z r : ℤ × ℤ) (hr : r ∈ S) (hz : z - v = r) : z ∈ shiftS S v :=
  ⟨r, hr, by rw [← hz]; abel⟩

theorem sub_mem_of_shift (S : Set (ℤ × ℤ)) (v z : ℤ × ℤ) (h : z ∈ shiftS S v) : z - v ∈ S := by
  obtain ⟨r, hr, rfl⟩ := h
  simpa using hr

theorem shift_mono (S T : Set (ℤ × ℤ)) (h : S ⊆ T) (v : ℤ × ℤ) : shiftS S v ⊆ shiftS T v :=
  Set.image_mono h

theorem mOdd_sub (w u1 u2 : Word) (i : ℕ) : mOdd w u1 u2 i ⊆ dOdd w u1 u2 i := by
  unfold mOdd dOdd pieceSet
  split
  · exact shift_mono _ _ (MarksIn.marksOdd_sub u1) _
  · exact shift_mono _ _ (MarksIn.marksEven_sub u2) _

theorem mEven_sub (w u1 u2 : Word) (i : ℕ) : mEven w u1 u2 i ⊆ dEven w u1 u2 i := by
  unfold mEven dEven pieceSet
  split
  · exact shift_mono _ _ (MarksIn.marksOdd_sub u1) _
  · exact shift_mono _ _ (MarksIn.marksEven_sub u2) _

/-! ### The odd child, `W_1` even (even-first) -/

section OddEvenFirst

variable (w u1 u2 : Word) (hph : phase w ≠ 1)

include hph in
theorem oddP_ef : oddP w = [texV1Even (parentsAt w).even + texV1Even (parentsAt w).even, texV2 (parentsAt w).even] := by
  simp [oddP, pOffsetsOdd, hph]

include hph in
theorem oddQ_ef : oddQ w = [0, texV1Even (parentsAt w).even, texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd,
    texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + texV1Even (parentsAt w).even] := by
  simp [oddQ, qOffsetsOdd, hph]

end OddEvenFirst

/-- **Condition (C) for the odd child with `W_1` even** (even-first), from the corner differences of the parents, (c) of the
even parent, local compatibility of the mixed copies, the two excluded pairs `(P^+, Q^{+,1})`, `(P^-, Q^{-,2})` and the triangle
identities at the optional interfaces `(P^-, Q^{+,2})`, `(P^+, Q^{-,1})`. -/
theorem closedPathOdd_evenFirst (w u1 u2 : Word) (hph : phase w ≠ 1)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (oP oQ : ℤ × ℤ → ℤ) (c : ℕ → ℤ)
    (hcP : CornerDiffs oP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      (parentsAt w).odd.num (parentsAt w).odd.den)
    (hcQ : CornerDiffs oQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      (parentsAt w).even.num (parentsAt w).even.den)
    (hdbl : ∃ k : ℤ, ∀ x, x ∈ tEvenSet u2 → x + texV1Even (parentsAt w).even ∈ tEvenSet u2 →
      oQ (x + texV1Even (parentsAt w).even) - oQ x = k)
    (hcompat : MixedCompatOdd w u1 u2 (placedOdd w oP oQ c))
    (hexcl : (∀ z, z ∈ dOdd w u1 u2 0 → z ∈ dOdd w u1 u2 2 → False) ∧
      (∀ z, z ∈ dOdd w u1 u2 1 → z ∈ dOdd w u1 u2 5 → False))
    (htri : ((∃ z, z ∈ mOdd w u1 u2 1 ∧ z ∈ mOdd w u1 u2 3) → ∃ z, z ∈ mOdd w u1 u2 1 ∧ z ∈ mOdd w u1 u2 3 ∧
        placedOdd w oP oQ c 1 z - placedOdd w oP oQ c 3 z =
          (placedOdd w oP oQ c 1 (texV2 (parentsAt w).even + e₁) -
            placedOdd w oP oQ c 2 (texV2 (parentsAt w).even + e₁)) +
          (placedOdd w oP oQ c 2 (texV1Even (parentsAt w).even) -
            placedOdd w oP oQ c 3 (texV1Even (parentsAt w).even))) ∧
      ((∃ z, z ∈ mOdd w u1 u2 0 ∧ z ∈ mOdd w u1 u2 4) → ∃ z, z ∈ mOdd w u1 u2 0 ∧ z ∈ mOdd w u1 u2 4 ∧
        placedOdd w oP oQ c 0 z - placedOdd w oP oQ c 4 z =
          (placedOdd w oP oQ c 0 (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even +
              (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - e₂)) -
            placedOdd w oP oQ c 5 (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even +
              (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - e₂))) +
          (placedOdd w oP oQ c 5 (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd +
              texV1Even (parentsAt w).even) -
            placedOdd w oP oQ c 4 (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd +
              texV1Even (parentsAt w).even)))) :
    ClosedPathOdd w u1 u2 (placedOdd w oP oQ c) := by
  have hP := oddP_ef w hph
  have hQ := oddQ_ef w hph
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p
  set B := texV2 p
  set U := texV1Even q
  set V := texV2 q
  set f := placedOdd w oP oQ c with hfdef
  -- the six pieces
  have h0 : IsPiece (f 0) oP (U + U) 0 (c 0) := fun z => by simp [hfdef, placedOdd, hP, affOdd]
  have h1 : IsPiece (f 1) oP V (q.num, -q.den) (c 1) := fun z => by simp [hfdef, placedOdd, hP, affOdd, hqdef]
  have h2 : IsPiece (f 2) oQ 0 0 (c 2) := fun z => by simp [hfdef, placedOdd, hQ, affOdd]
  have h3 : IsPiece (f 3) oQ U 0 (c 3) := fun z => by simp [hfdef, placedOdd, hQ, affOdd]
  have h4 : IsPiece (f 4) oQ (A + B) (p.num, -p.den) (c 4) := fun z => by simp [hfdef, placedOdd, hQ, affOdd, hpdef]
  have h5 : IsPiece (f 5) oQ (A + B + U) (p.num, -p.den) (c 5) := fun z => by
    simp [hfdef, placedOdd, hQ, affOdd, hpdef]
  have hv : StepVectors p.num p.den q.num q.den A B U V (p.num, -p.den) (q.num, -q.den) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hsum := odd_even_first p.num p.den q.num q.den A B U V _ _ hv oP oQ f c h0 h1 h2 h3 h4 h5 hcP hcQ
  -- the constants of the closed path `Q^{+,1}, Q^{+,2}, P^+, Q^{-,2}, Q^{-,1}, P^-`
  have hnd : [2, 3, 0, 5, 4, 1].Nodup := by decide
  obtain ⟨-, e0, e1, e2, e3, e4, e5⟩ := hexKappa_spec f 2 3 0 5 4 1 U (U + U) (U + U + (A + B - e₂))
    (A + B + U) (A + B + (V + e₁ - e₂)) (V + e₁) hnd
  set κ := hexKappa f 2 3 0 5 4 1 U (U + U) (U + U + (A + B - e₂)) (A + B + U) (A + B + (V + e₁ - e₂))
  have e5' := e5.2 hsum
  -- the marks and the domains of the copies
  have hm0 : mOdd w u1 u2 0 = shiftS (marksOdd u1) (U + U) := by simp [mOdd, pieceSet, hP]
  have hm1 : mOdd w u1 u2 1 = shiftS (marksOdd u1) V := by simp [mOdd, pieceSet, hP]
  have hm2 : mOdd w u1 u2 2 = shiftS (marksEven u2) 0 := by simp [mOdd, pieceSet, hP, hQ]
  have hm3 : mOdd w u1 u2 3 = shiftS (marksEven u2) U := by simp [mOdd, pieceSet, hP, hQ]
  have hm4 : mOdd w u1 u2 4 = shiftS (marksEven u2) (A + B) := by simp [mOdd, pieceSet, hP, hQ]
  have hm5 : mOdd w u1 u2 5 = shiftS (marksEven u2) (A + B + U) := by simp [mOdd, pieceSet, hP, hQ]
  have hd2 : dOdd w u1 u2 2 = shiftS (tEvenSet u2) 0 := by simp [dOdd, pieceSet, hP, hQ]
  have hd3 : dOdd w u1 u2 3 = shiftS (tEvenSet u2) U := by simp [dOdd, pieceSet, hP, hQ]
  have hd4 : dOdd w u1 u2 4 = shiftS (tEvenSet u2) (A + B) := by simp [dOdd, pieceSet, hP, hQ]
  have hd5 : dOdd w u1 u2 5 = shiftS (tEvenSet u2) (A + B + U) := by simp [dOdd, pieceSet, hP, hQ]
  obtain ⟨cP0, cP1, cPA', cPA, cPB1, cPB1', cPD, cPD'⟩ := corner_marks_odd u1
  obtain ⟨cQ0, cQ1, cQU', cQU, cQV1, cQV1', cQD, cQD'⟩ := corner_marks_even u2
  rw [← hp] at cPA' cPA cPB1 cPB1' cPD cPD'
  rw [← hq] at cQU' cQU cQV1 cQV1' cQD cQD'
  -- the doubled interfaces: the difference is constant on the overlap of the two copies
  obtain ⟨k, hk⟩ := hdbl
  have hdc23 : ∃ C : ℤ, ∀ z ∈ {z | z ∈ dOdd w u1 u2 2 ∧ z ∈ dOdd w u1 u2 3}, f 2 z - f 3 z = C := by
    refine ⟨k + c 2 - c 3, fun z hz => ?_⟩
    obtain ⟨hz2, hz3⟩ := hz
    rw [hd2] at hz2
    rw [hd3] at hz3
    have hx := sub_mem_of_shift _ _ _ hz3
    have hx' := sub_mem_of_shift _ _ _ hz2
    have e : z - U + U = z - 0 := by abel
    have := hk (z - U) hx (by rw [e]; exact hx')
    rw [h2 z, h3 z, ← e]
    linarith
  have hdc45 : ∃ C : ℤ, ∀ z ∈ {z | z ∈ dOdd w u1 u2 4 ∧ z ∈ dOdd w u1 u2 5}, f 4 z - f 5 z = C := by
    refine ⟨k + c 4 - c 5, fun z hz => ?_⟩
    obtain ⟨hz4, hz5⟩ := hz
    rw [hd4] at hz4
    rw [hd5] at hz5
    have hx := sub_mem_of_shift _ _ _ hz5
    have hx' := sub_mem_of_shift _ _ _ hz4
    have e : z - (A + B + U) + U = z - (A + B) := by abel
    have := hk (z - (A + B + U)) hx (by rw [e]; exact hx')
    rw [h4 z, h5 z, ← e]
    linarith
  -- a mixed interface agrees once it agrees at one point of the marks
  have mixed : ∀ i j, i < 2 → 2 ≤ j → j < 6 → ∀ y, y ∈ mOdd w u1 u2 i → y ∈ mOdd w u1 u2 j →
      f i y + κ i = f j y + κ j → ∀ z, z ∈ mOdd w u1 u2 i → z ∈ mOdd w u1 u2 j → f i z + κ i = f j z + κ j := by
    intro i j hi hj hj6 y hyi hyj hy z hzi hzj
    obtain ⟨C, hC⟩ := hcompat i j hi hj hj6
    refine agree_of_witness {z | z ∈ mOdd w u1 u2 i ∧ z ∈ mOdd w u1 u2 j} (fun z => f i z + κ i)
      (fun z => f j z + κ j) ⟨C + κ i - κ j, fun z hz => ?_⟩ y ⟨hyi, hyj⟩ hy z ⟨hzi, hzj⟩
    have := hC z hz.1 hz.2
    linarith
  have none : ∀ i j, (∀ z, z ∈ dOdd w u1 u2 i → z ∈ dOdd w u1 u2 j → False) →
      ∀ z, z ∈ mOdd w u1 u2 i → z ∈ mOdd w u1 u2 j → f i z + κ i = f j z + κ j := by
    intro i j h z hzi hzj
    exact (h z (mOdd_sub w u1 u2 i hzi) (mOdd_sub w u1 u2 j hzj)).elim
  apply closedPathOdd_of_pairs w u1 u2 f κ
  · intro i j hi hj hj6 z hzi hzj
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    all_goals obtain rfl | rfl | rfl | rfl : j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
    · exact none 0 2 hexcl.1 z hzi hzj
    · -- `P^+` and `Q^{+,2}` at `2U`
      refine mixed 0 3 (by norm_num) (by norm_num) (by norm_num) (U + U) ?_ ?_ e1.symm z hzi hzj
      · rw [hm0]; exact mem_shift _ _ _ 0 cP0 (by abel)
      · rw [hm3]; exact mem_shift _ _ _ U cQU (by abel)
    · -- the optional interface `P^+`, `Q^{-,1}`
      obtain ⟨y, hy0, hy4, hyv⟩ := htri.2 ⟨z, hzi, hzj⟩
      refine mixed 0 4 (by norm_num) (by norm_num) (by norm_num) y hy0 hy4 ?_ z hzi hzj
      linarith
    · -- `P^+` and `Q^{-,2}` at `2U + A + B - e₂`
      refine mixed 0 5 (by norm_num) (by norm_num) (by norm_num) _ ?_ ?_ e2 z hzi hzj
      · rw [hm0]; exact mem_shift _ _ _ (A + B - e₂) cPD' (by abel)
      · rw [hm5]; exact mem_shift _ _ _ (U - e₂) cQU' (by abel)
    · -- `P^-` and `Q^{+,1}` at `V + e₁` (the closing interface)
      refine mixed 1 2 (by norm_num) (by norm_num) (by norm_num) (V + e₁) ?_ ?_ e5' z hzi hzj
      · rw [hm1]; exact mem_shift _ _ _ e₁ cP1 (by abel)
      · rw [hm2]; exact mem_shift _ _ _ (V + e₁) cQV1 (by abel)
    · -- the optional interface `P^-`, `Q^{+,2}`
      obtain ⟨y, hy1, hy3, hyv⟩ := htri.1 ⟨z, hzi, hzj⟩
      refine mixed 1 3 (by norm_num) (by norm_num) (by norm_num) y hy1 hy3 ?_ z hzi hzj
      linarith
    · -- `P^-` and `Q^{-,1}` at `A + B + V + e₁ - e₂`
      refine mixed 1 4 (by norm_num) (by norm_num) (by norm_num) _ ?_ ?_ e4.symm z hzi hzj
      · rw [hm1]; exact mem_shift _ _ _ (A + B + e₁ - e₂) cPD (by abel)
      · rw [hm4]; exact mem_shift _ _ _ (V + e₁ - e₂) cQV1' (by abel)
    · exact none 1 5 hexcl.2 z hzi hzj
  · -- `Q^{+,1}` and `Q^{+,2}` at `U`
    intro z hz2 hz3
    refine agree_of_witness {z | z ∈ dOdd w u1 u2 2 ∧ z ∈ dOdd w u1 u2 3} (fun z => f 2 z + κ 2)
      (fun z => f 3 z + κ 3) ?_ U ⟨?_, ?_⟩ e0 z ⟨hz2, hz3⟩
    · obtain ⟨C, hC⟩ := hdc23
      exact ⟨C + κ 2 - κ 3, fun z hz => by have := hC z hz; linarith⟩
    · rw [hd2]; exact mem_shift _ _ _ U (MarksIn.marksEven_sub u2 cQU) (by abel)
    · rw [hd3]; exact mem_shift _ _ _ 0 (MarksIn.marksEven_sub u2 cQ0) (by abel)
  · -- `Q^{-,1}` and `Q^{-,2}` at `A + B + U`
    intro z hz4 hz5
    refine agree_of_witness {z | z ∈ dOdd w u1 u2 4 ∧ z ∈ dOdd w u1 u2 5} (fun z => f 4 z + κ 4)
      (fun z => f 5 z + κ 5) ?_ (A + B + U) ⟨?_, ?_⟩ e3.symm z ⟨hz4, hz5⟩
    · obtain ⟨C, hC⟩ := hdc45
      exact ⟨C + κ 4 - κ 5, fun z hz => by have := hC z hz; linarith⟩
    · rw [hd4]; exact mem_shift _ _ _ U (MarksIn.marksEven_sub u2 cQU) (by abel)
    · rw [hd5]; exact mem_shift _ _ _ 0 (MarksIn.marksEven_sub u2 cQ0) (by abel)


/-! ### Two helpers -/

/-- A pair with a constant difference on the overlap `S i ∩ S j` agrees there once it agrees at one point of it. -/
theorem pair_agree (S : ℕ → Set (ℤ × ℤ)) (f : ℕ → ℤ × ℤ → ℤ) (κ : ℕ → ℤ) (i j : ℕ)
    (hC : ∃ C : ℤ, ∀ z, z ∈ S i → z ∈ S j → f i z - f j z = C) (y : ℤ × ℤ) (hyi : y ∈ S i) (hyj : y ∈ S j)
    (hy : f i y + κ i = f j y + κ j) : ∀ z, z ∈ S i → z ∈ S j → f i z + κ i = f j z + κ j := by
  intro z hzi hzj
  obtain ⟨C, hC⟩ := hC
  have h1 := hC z hzi hzj
  have h2 := hC y hyi hyj
  linarith

theorem dot2_zero_left (z : ℤ × ℤ) : dot2 0 z = 0 := by simp [dot2]

theorem dot2_add_left (a b z : ℤ × ℤ) : dot2 (a + b) z = dot2 a z + dot2 b z := by
  simp [dot2]
  ring

theorem dot2_sub_right (a x y : ℤ × ℤ) : dot2 a (x - y) = dot2 a x - dot2 a y := by
  simp [dot2]
  ring

/-! ### The odd child, `W_1` odd (odd-first) -/

theorem oddP_of (w : Word) (hph : phase w = 1) :
    oddP w = [0, texV1Even (parentsAt w).even + texV1Even (parentsAt w).even + texV2 (parentsAt w).even] := by
  simp [oddP, pOffsetsOdd, hph]

theorem oddQ_of (w : Word) (hph : phase w = 1) :
    oddQ w = [texV1Odd (parentsAt w).odd, texV1Odd (parentsAt w).odd + texV1Even (parentsAt w).even,
      texV2 (parentsAt w).odd, texV2 (parentsAt w).odd + texV1Even (parentsAt w).even] := by
  simp [oddQ, qOffsetsOdd, hph]

/-- **Condition (C) for the odd child with `W_1` odd** (odd-first): the excluded pairs are `(P^+, Q^{+,2})`, `(P^-, Q^{-,1})`
and the optional interfaces `(P^-, Q^{+,1})`, `(P^+, Q^{-,2})`. -/
theorem closedPathOdd_oddFirst (w u1 u2 : Word) (hph : phase w = 1)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (oP oQ : ℤ × ℤ → ℤ) (c : ℕ → ℤ)
    (hcP : CornerDiffs oP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      (parentsAt w).odd.num (parentsAt w).odd.den)
    (hcQ : CornerDiffs oQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      (parentsAt w).even.num (parentsAt w).even.den)
    (hdbl : ∃ k : ℤ, ∀ x, x ∈ tEvenSet u2 → x + texV1Even (parentsAt w).even ∈ tEvenSet u2 →
      oQ (x + texV1Even (parentsAt w).even) - oQ x = k)
    (hcompat : MixedCompatOdd w u1 u2 (placedOdd w oP oQ c))
    (hexcl : (∀ z, z ∈ dOdd w u1 u2 0 → z ∈ dOdd w u1 u2 3 → False) ∧
      (∀ z, z ∈ dOdd w u1 u2 1 → z ∈ dOdd w u1 u2 4 → False))
    (htri : ((∃ z, z ∈ mOdd w u1 u2 1 ∧ z ∈ mOdd w u1 u2 2) → ∃ z, z ∈ mOdd w u1 u2 1 ∧ z ∈ mOdd w u1 u2 2 ∧
        placedOdd w oP oQ c 1 z - placedOdd w oP oQ c 2 z =
          (placedOdd w oP oQ c 1 (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even +
              texV2 (parentsAt w).even + (texV1Odd (parentsAt w).odd - e₂)) -
            placedOdd w oP oQ c 3 (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even +
              texV2 (parentsAt w).even + (texV1Odd (parentsAt w).odd - e₂))) +
          (placedOdd w oP oQ c 3 (texV1Odd (parentsAt w).odd + texV1Even (parentsAt w).even) -
            placedOdd w oP oQ c 2 (texV1Odd (parentsAt w).odd + texV1Even (parentsAt w).even))) ∧
      ((∃ z, z ∈ mOdd w u1 u2 0 ∧ z ∈ mOdd w u1 u2 5) → ∃ z, z ∈ mOdd w u1 u2 0 ∧ z ∈ mOdd w u1 u2 5 ∧
        placedOdd w oP oQ c 0 z - placedOdd w oP oQ c 5 z =
          (placedOdd w oP oQ c 0 (texV2 (parentsAt w).odd + e₁) -
            placedOdd w oP oQ c 4 (texV2 (parentsAt w).odd + e₁)) +
          (placedOdd w oP oQ c 4 (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) -
            placedOdd w oP oQ c 5 (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)))) :
    ClosedPathOdd w u1 u2 (placedOdd w oP oQ c) := by
  have hP := oddP_of w hph
  have hQ := oddQ_of w hph
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p
  set B := texV2 p
  set U := texV1Even q
  set V := texV2 q
  set f := placedOdd w oP oQ c with hfdef
  have h0 : IsPiece (f 0) oP 0 0 (c 0) := fun z => by simp [hfdef, placedOdd, hP, affOdd]
  have h1 : IsPiece (f 1) oP (U + U + V) (q.num, -q.den) (c 1) := fun z => by
    simp [hfdef, placedOdd, hP, affOdd, hqdef]
  have h2 : IsPiece (f 2) oQ A 0 (c 2) := fun z => by simp [hfdef, placedOdd, hQ, affOdd]
  have h3 : IsPiece (f 3) oQ (A + U) 0 (c 3) := fun z => by simp [hfdef, placedOdd, hQ, affOdd]
  have h4 : IsPiece (f 4) oQ B (p.num, -p.den) (c 4) := fun z => by simp [hfdef, placedOdd, hQ, affOdd, hpdef]
  have h5 : IsPiece (f 5) oQ (B + U) (p.num, -p.den) (c 5) := fun z => by
    simp [hfdef, placedOdd, hQ, affOdd, hpdef]
  have hv : StepVectors p.num p.den q.num q.den A B U V (p.num, -p.den) (q.num, -q.den) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hsum := odd_odd_first p.num p.den q.num q.den A B U V _ _ hv oP oQ f c h0 h1 h2 h3 h4 h5 hcP hcQ
  have hnd : [2, 0, 4, 5, 1, 3].Nodup := by decide
  obtain ⟨-, e0, e1, e2, e3, e4, e5⟩ := hexKappa_spec f 2 0 4 5 1 3 A (B + e₁) (B + U)
    (B + U + (U + V + e₁ - e₂)) (U + U + V + (A - e₂)) (A + U) hnd
  set κ := hexKappa f 2 0 4 5 1 3 A (B + e₁) (B + U) (B + U + (U + V + e₁ - e₂)) (U + U + V + (A - e₂))
  have e5' := e5.2 hsum
  have hm0 : mOdd w u1 u2 0 = shiftS (marksOdd u1) 0 := by simp [mOdd, pieceSet, hP]
  have hm1 : mOdd w u1 u2 1 = shiftS (marksOdd u1) (U + U + V) := by simp [mOdd, pieceSet, hP]
  have hm2 : mOdd w u1 u2 2 = shiftS (marksEven u2) A := by simp [mOdd, pieceSet, hP, hQ]
  have hm3 : mOdd w u1 u2 3 = shiftS (marksEven u2) (A + U) := by simp [mOdd, pieceSet, hP, hQ]
  have hm4 : mOdd w u1 u2 4 = shiftS (marksEven u2) B := by simp [mOdd, pieceSet, hP, hQ]
  have hm5 : mOdd w u1 u2 5 = shiftS (marksEven u2) (B + U) := by simp [mOdd, pieceSet, hP, hQ]
  have hd2 : dOdd w u1 u2 2 = shiftS (tEvenSet u2) A := by simp [dOdd, pieceSet, hP, hQ]
  have hd3 : dOdd w u1 u2 3 = shiftS (tEvenSet u2) (A + U) := by simp [dOdd, pieceSet, hP, hQ]
  have hd4 : dOdd w u1 u2 4 = shiftS (tEvenSet u2) B := by simp [dOdd, pieceSet, hP, hQ]
  have hd5 : dOdd w u1 u2 5 = shiftS (tEvenSet u2) (B + U) := by simp [dOdd, pieceSet, hP, hQ]
  obtain ⟨cP0, cP1, cPA', cPA, cPB1, cPB1', cPD, cPD'⟩ := corner_marks_odd u1
  obtain ⟨cQ0, cQ1, cQU', cQU, cQV1, cQV1', cQD, cQD'⟩ := corner_marks_even u2
  rw [← hp] at cPA' cPA cPB1 cPB1' cPD cPD'
  rw [← hq] at cQU' cQU cQV1 cQV1' cQD cQD'
  obtain ⟨k, hk⟩ := hdbl
  have hdc23 : ∃ C : ℤ, ∀ z, z ∈ dOdd w u1 u2 2 → z ∈ dOdd w u1 u2 3 → f 2 z - f 3 z = C := by
    refine ⟨k + c 2 - c 3, fun z hz2 hz3 => ?_⟩
    rw [hd2] at hz2
    rw [hd3] at hz3
    have e : z - (A + U) + U = z - A := by abel
    have := hk (z - (A + U)) (sub_mem_of_shift _ _ _ hz3) (by rw [e]; exact sub_mem_of_shift _ _ _ hz2)
    rw [h2 z, h3 z, ← e]
    linarith
  have hdc45 : ∃ C : ℤ, ∀ z, z ∈ dOdd w u1 u2 4 → z ∈ dOdd w u1 u2 5 → f 4 z - f 5 z = C := by
    refine ⟨k + c 4 - c 5, fun z hz4 hz5 => ?_⟩
    rw [hd4] at hz4
    rw [hd5] at hz5
    have e : z - (B + U) + U = z - B := by abel
    have := hk (z - (B + U)) (sub_mem_of_shift _ _ _ hz5) (by rw [e]; exact sub_mem_of_shift _ _ _ hz4)
    rw [h4 z, h5 z, ← e]
    linarith
  have none : ∀ i j, (∀ z, z ∈ dOdd w u1 u2 i → z ∈ dOdd w u1 u2 j → False) →
      ∀ z, z ∈ mOdd w u1 u2 i → z ∈ mOdd w u1 u2 j → f i z + κ i = f j z + κ j := by
    intro i j h z hzi hzj
    exact (h z (mOdd_sub w u1 u2 i hzi) (mOdd_sub w u1 u2 j hzj)).elim
  apply closedPathOdd_of_pairs w u1 u2 f κ
  · intro i j hi hj hj6 z hzi hzj
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    all_goals obtain rfl | rfl | rfl | rfl : j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
    · -- `P^+` and `Q^{+,1}` at `A`
      refine pair_agree (mOdd w u1 u2) f κ 0 2 (hcompat 0 2 (by norm_num) (by norm_num) (by norm_num)) A ?_ ?_
        e0.symm z hzi hzj
      · rw [hm0]; exact mem_shift _ _ _ A cPA (by abel)
      · rw [hm2]; exact mem_shift _ _ _ 0 cQ0 (by abel)
    · exact none 0 3 hexcl.1 z hzi hzj
    · -- `P^+` and `Q^{-,1}` at `B + e₁`
      refine pair_agree (mOdd w u1 u2) f κ 0 4 (hcompat 0 4 (by norm_num) (by norm_num) (by norm_num)) _ ?_ ?_
        e1 z hzi hzj
      · rw [hm0]; exact mem_shift _ _ _ (B + e₁) cPB1 (by abel)
      · rw [hm4]; exact mem_shift _ _ _ e₁ cQ1 (by abel)
    · -- the optional interface `P^+`, `Q^{-,2}`
      obtain ⟨y, hy0, hy5, hyv⟩ := htri.2 ⟨z, hzi, hzj⟩
      refine pair_agree (mOdd w u1 u2) f κ 0 5 (hcompat 0 5 (by norm_num) (by norm_num) (by norm_num)) y hy0 hy5
        ?_ z hzi hzj
      linarith
    · -- the optional interface `P^-`, `Q^{+,1}`
      obtain ⟨y, hy1, hy2, hyv⟩ := htri.1 ⟨z, hzi, hzj⟩
      refine pair_agree (mOdd w u1 u2) f κ 1 2 (hcompat 1 2 (by norm_num) (by norm_num) (by norm_num)) y hy1 hy2
        ?_ z hzi hzj
      linarith
    · -- `P^-` and `Q^{+,2}` at `2U + V + A - e₂`
      refine pair_agree (mOdd w u1 u2) f κ 1 3 (hcompat 1 3 (by norm_num) (by norm_num) (by norm_num)) _ ?_ ?_
        e4 z hzi hzj
      · rw [hm1]; exact mem_shift _ _ _ (A - e₂) cPA' (by abel)
      · rw [hm3]; exact mem_shift _ _ _ (U + V - e₂) cQD' (by abel)
    · exact none 1 4 hexcl.2 z hzi hzj
    · -- `P^-` and `Q^{-,2}` at `B + 2U + V + e₁ - e₂`
      refine pair_agree (mOdd w u1 u2) f κ 1 5 (hcompat 1 5 (by norm_num) (by norm_num) (by norm_num)) _ ?_ ?_
        e3.symm z hzi hzj
      · rw [hm1]; exact mem_shift _ _ _ (B + e₁ - e₂) cPB1' (by abel)
      · rw [hm5]; exact mem_shift _ _ _ (U + V + e₁ - e₂) cQD (by abel)
  · -- `Q^{+,1}` and `Q^{+,2}` at `A + U`
    intro z hz2 hz3
    refine pair_agree (dOdd w u1 u2) f κ 2 3 hdc23 (A + U) ?_ ?_ e5'.symm z hz2 hz3
    · rw [hd2]; exact mem_shift _ _ _ U (MarksIn.marksEven_sub u2 cQU) (by abel)
    · rw [hd3]; exact mem_shift _ _ _ 0 (MarksIn.marksEven_sub u2 cQ0) (by abel)
  · -- `Q^{-,1}` and `Q^{-,2}` at `B + U`
    intro z hz4 hz5
    refine pair_agree (dOdd w u1 u2) f κ 4 5 hdc45 (B + U) ?_ ?_ e2 z hz4 hz5
    · rw [hd4]; exact mem_shift _ _ _ U (MarksIn.marksEven_sub u2 cQU) (by abel)
    · rw [hd5]; exact mem_shift _ _ _ 0 (MarksIn.marksEven_sub u2 cQ0) (by abel)

/-! ### The even child -/

theorem evenP_ef (w : Word) (hph : phase w ≠ 1) :
    evenP w = [texV1Even (parentsAt w).even, texV1Even (parentsAt w).even + texV2 (parentsAt w).odd,
      texV2 (parentsAt w).even, texV2 (parentsAt w).even + texV2 (parentsAt w).odd] := by
  simp [evenP, pOffsetsEven, hph]

theorem evenQ_ef (w : Word) (hph : phase w ≠ 1) :
    evenQ w = [0, texV1Odd (parentsAt w).odd + (texV2 (parentsAt w).odd + texV2 (parentsAt w).odd)] := by
  simp [evenQ, qOffsetsEven, hph]

theorem evenP_of (w : Word) (hph : phase w = 1) :
    evenP w = [0, texV2 (parentsAt w).odd, texV1Even (parentsAt w).even + texV2 (parentsAt w).even,
      texV1Even (parentsAt w).even + texV2 (parentsAt w).even + texV2 (parentsAt w).odd] := by
  simp [evenP, pOffsetsEven, hph]

theorem evenQ_of (w : Word) (hph : phase w = 1) :
    evenQ w = [texV1Odd (parentsAt w).odd, texV2 (parentsAt w).odd + texV2 (parentsAt w).odd] := by
  simp [evenQ, qOffsetsEven, hph]

/-- The doubled interface of the even child: (c) of the odd parent, `oP(x + B) - oP(x) - a·x` constant on the overlap of the
tile with its translate, makes the difference of the two copies constant on their overlap. -/
theorem even_dbl_const (oP : ℤ × ℤ → ℤ) (T : Set (ℤ × ℤ)) (B a α : ℤ × ℤ) (o : ℤ × ℤ) (c0 c1 : ℤ)
    (f0 f1 : ℤ × ℤ → ℤ) (hk : ∃ k : ℤ, ∀ x, x ∈ T → x + B ∈ T → oP (x + B) - oP x - dot2 a x = k)
    (h0 : IsPiece f0 oP o α c0) (h1 : IsPiece f1 oP (o + B) (α + a) c1) :
    ∃ C : ℤ, ∀ z, z ∈ shiftS T o → z ∈ shiftS T (o + B) → f0 z - f1 z = C := by
  obtain ⟨k, hk⟩ := hk
  refine ⟨k - dot2 a (o + B) + c0 - c1, fun z hz0 hz1 => ?_⟩
  have e : z - (o + B) + B = z - o := by abel
  have := hk (z - (o + B)) (sub_mem_of_shift _ _ _ hz1) (by rw [e]; exact sub_mem_of_shift _ _ _ hz0)
  rw [h0 z, h1 z, ← e, dot2_add_left]
  rw [e] at this ⊢
  rw [dot2_sub_right] at this
  linarith

/-- **Condition (C) for the even child with `W_1` even** (even-first): the excluded pairs are `(P^{+,1}, Q^-)`,
`(P^{-,2}, Q^+)` and the optional interfaces `(P^{+,2}, Q^+)`, `(P^{-,1}, Q^-)`. -/
theorem closedPathEven_evenFirst (w u1 u2 : Word) (hph : phase w ≠ 1)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (oP oQ : ℤ × ℤ → ℤ) (c : ℕ → ℤ)
    (hcP : CornerDiffs oP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      (parentsAt w).odd.num (parentsAt w).odd.den)
    (hcQ : CornerDiffs oQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      (parentsAt w).even.num (parentsAt w).even.den)
    (hdbl : ∃ k : ℤ, ∀ x, x ∈ tOddSet u1 → x + texV2 (parentsAt w).odd ∈ tOddSet u1 →
      oP (x + texV2 (parentsAt w).odd) - oP x - dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) x = k)
    (hcompat : MixedCompatEven w u1 u2 (placedEven w oP oQ c))
    (hexcl : (∀ z, z ∈ dEven w u1 u2 0 → z ∈ dEven w u1 u2 5 → False) ∧
      (∀ z, z ∈ dEven w u1 u2 3 → z ∈ dEven w u1 u2 4 → False))
    (htri : ((∃ z, z ∈ mEven w u1 u2 1 ∧ z ∈ mEven w u1 u2 4) → ∃ z, z ∈ mEven w u1 u2 1 ∧ z ∈ mEven w u1 u2 4 ∧
        placedEven w oP oQ c 1 z - placedEven w oP oQ c 4 z =
          (placedEven w oP oQ c 1 (texV1Even (parentsAt w).even + (texV2 (parentsAt w).odd + e₁)) -
            placedEven w oP oQ c 0 (texV1Even (parentsAt w).even + (texV2 (parentsAt w).odd + e₁))) +
          (placedEven w oP oQ c 0 (texV1Even (parentsAt w).even) -
            placedEven w oP oQ c 4 (texV1Even (parentsAt w).even))) ∧
      ((∃ z, z ∈ mEven w u1 u2 2 ∧ z ∈ mEven w u1 u2 5) → ∃ z, z ∈ mEven w u1 u2 2 ∧ z ∈ mEven w u1 u2 5 ∧
        placedEven w oP oQ c 2 z - placedEven w oP oQ c 5 z =
          (placedEven w oP oQ c 2 (texV2 (parentsAt w).even + texV2 (parentsAt w).odd + e₁) -
            placedEven w oP oQ c 3 (texV2 (parentsAt w).even + texV2 (parentsAt w).odd + e₁)) +
          (placedEven w oP oQ c 3 (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + texV2 (parentsAt w).odd +
              (texV2 (parentsAt w).even + e₁ - e₂)) -
            placedEven w oP oQ c 5 (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + texV2 (parentsAt w).odd +
              (texV2 (parentsAt w).even + e₁ - e₂))))) :
    ClosedPathEven w u1 u2 (placedEven w oP oQ c) := by
  have hP := evenP_ef w hph
  have hQ := evenQ_ef w hph
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p
  set B := texV2 p
  set U := texV1Even q
  set V := texV2 q
  set f := placedEven w oP oQ c with hfdef
  have h0 : IsPiece (f 0) oP U 0 (c 0) := fun z => by simp [hfdef, placedEven, hP, affEven]
  have h1 : IsPiece (f 1) oP (U + B) (p.num, -p.den) (c 1) := fun z => by
    simp [hfdef, placedEven, hP, affEven, hpdef]
  have h2 : IsPiece (f 2) oP V (q.num, -q.den) (c 2) := fun z => by simp [hfdef, placedEven, hP, affEven, hqdef]
  have h3 : IsPiece (f 3) oP (V + B) ((p.num, -p.den) + (q.num, -q.den)) (c 3) := fun z => by
    simp [hfdef, placedEven, hP, affEven, hpdef, hqdef]
  have h4 : IsPiece (f 4) oQ 0 0 (c 4) := fun z => by simp [hfdef, placedEven, hQ, affEven]
  have h5 : IsPiece (f 5) oQ (A + B + B) ((p.num, -p.den) + (p.num, -p.den)) (c 5) := fun z => by
    simp [hfdef, placedEven, hQ, affEven, hpdef, add_assoc]
  have hv : StepVectors p.num p.den q.num q.den A B U V (p.num, -p.den) (q.num, -q.den) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hsum := even_even_first p.num p.den q.num q.den A B U V _ _ hv oP oQ f c h0 h1 h2 h3 h4 h5 hcP hcQ
  have hnd : [4, 0, 1, 5, 3, 2].Nodup := by decide
  obtain ⟨-, e0, e1, e2, e3, e4, e5⟩ := hexKappa_spec f 4 0 1 5 3 2 U (U + (B + e₁)) (U + B + (A + B - e₂))
    (A + B + B + (V + e₁ - e₂)) (V + B + e₁) (V + e₁) hnd
  set κ := hexKappa f 4 0 1 5 3 2 U (U + (B + e₁)) (U + B + (A + B - e₂)) (A + B + B + (V + e₁ - e₂)) (V + B + e₁)
  have e5' := e5.2 hsum
  have hm0 : mEven w u1 u2 0 = shiftS (marksOdd u1) U := by simp [mEven, pieceSet, hP]
  have hm1 : mEven w u1 u2 1 = shiftS (marksOdd u1) (U + B) := by simp [mEven, pieceSet, hP]
  have hm2 : mEven w u1 u2 2 = shiftS (marksOdd u1) V := by simp [mEven, pieceSet, hP]
  have hm3 : mEven w u1 u2 3 = shiftS (marksOdd u1) (V + B) := by simp [mEven, pieceSet, hP]
  have hm4 : mEven w u1 u2 4 = shiftS (marksEven u2) 0 := by simp [mEven, pieceSet, hP, hQ]
  have hm5 : mEven w u1 u2 5 = shiftS (marksEven u2) (A + B + B) := by simp [mEven, pieceSet, hP, hQ, add_assoc]
  have hd0 : dEven w u1 u2 0 = shiftS (tOddSet u1) U := by simp [dEven, pieceSet, hP]
  have hd1 : dEven w u1 u2 1 = shiftS (tOddSet u1) (U + B) := by simp [dEven, pieceSet, hP]
  have hd2 : dEven w u1 u2 2 = shiftS (tOddSet u1) V := by simp [dEven, pieceSet, hP]
  have hd3 : dEven w u1 u2 3 = shiftS (tOddSet u1) (V + B) := by simp [dEven, pieceSet, hP]
  obtain ⟨cP0, cP1, cPA', cPA, cPB1, cPB1', cPD, cPD'⟩ := corner_marks_odd u1
  obtain ⟨cQ0, cQ1, cQU', cQU, cQV1, cQV1', cQD, cQD'⟩ := corner_marks_even u2
  rw [← hp] at cPA' cPA cPB1 cPB1' cPD cPD'
  rw [← hq] at cQU' cQU cQV1 cQV1' cQD cQD'
  have hdc01 := even_dbl_const oP (tOddSet u1) B (p.num, -p.den) 0 U (c 0) (c 1) (f 0) (f 1) hdbl h0
    (by simpa using h1)
  have hdc23 := even_dbl_const oP (tOddSet u1) B (p.num, -p.den) (q.num, -q.den) V (c 2) (c 3) (f 2) (f 3) hdbl h2
    (by simpa [add_comm] using h3)
  have none : ∀ i j, (∀ z, z ∈ dEven w u1 u2 i → z ∈ dEven w u1 u2 j → False) →
      ∀ z, z ∈ mEven w u1 u2 i → z ∈ mEven w u1 u2 j → f i z + κ i = f j z + κ j := by
    intro i j h z hzi hzj
    exact (h z (mEven_sub w u1 u2 i hzi) (mEven_sub w u1 u2 j hzj)).elim
  apply closedPathEven_of_pairs w u1 u2 f κ
  · intro i j hi hj hj6 z hzi hzj
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    all_goals obtain rfl | rfl : j = 4 ∨ j = 5 := by omega
    · -- `P^{+,1}` and `Q^+` at `U`
      refine pair_agree (mEven w u1 u2) f κ 0 4 (hcompat 0 4 (by norm_num) (by norm_num) (by norm_num)) U ?_ ?_
        e0.symm z hzi hzj
      · rw [hm0]; exact mem_shift _ _ _ 0 cP0 (by abel)
      · rw [hm4]; exact mem_shift _ _ _ U cQU (by abel)
    · exact none 0 5 hexcl.1 z hzi hzj
    · -- the optional interface `P^{+,2}`, `Q^+`
      obtain ⟨y, hy1, hy4, hyv⟩ := htri.1 ⟨z, hzi, hzj⟩
      refine pair_agree (mEven w u1 u2) f κ 1 4 (hcompat 1 4 (by norm_num) (by norm_num) (by norm_num)) y hy1 hy4
        ?_ z hzi hzj
      linarith
    · -- `P^{+,2}` and `Q^-` at `U + A + 2B - e₂`
      refine pair_agree (mEven w u1 u2) f κ 1 5 (hcompat 1 5 (by norm_num) (by norm_num) (by norm_num)) _ ?_ ?_
        e2 z hzi hzj
      · rw [hm1]; exact mem_shift _ _ _ (A + B - e₂) cPD' (by abel)
      · rw [hm5]; exact mem_shift _ _ _ (U - e₂) cQU' (by abel)
    · -- `P^{-,1}` and `Q^+` at `V + e₁` (the closing interface)
      refine pair_agree (mEven w u1 u2) f κ 2 4 (hcompat 2 4 (by norm_num) (by norm_num) (by norm_num)) _ ?_ ?_
        e5' z hzi hzj
      · rw [hm2]; exact mem_shift _ _ _ e₁ cP1 (by abel)
      · rw [hm4]; exact mem_shift _ _ _ (V + e₁) cQV1 (by abel)
    · -- the optional interface `P^{-,1}`, `Q^-`
      obtain ⟨y, hy2, hy5, hyv⟩ := htri.2 ⟨z, hzi, hzj⟩
      refine pair_agree (mEven w u1 u2) f κ 2 5 (hcompat 2 5 (by norm_num) (by norm_num) (by norm_num)) y hy2 hy5
        ?_ z hzi hzj
      linarith
    · exact none 3 4 hexcl.2 z hzi hzj
    · -- `P^{-,2}` and `Q^-` at `A + 2B + V + e₁ - e₂`
      refine pair_agree (mEven w u1 u2) f κ 3 5 (hcompat 3 5 (by norm_num) (by norm_num) (by norm_num)) _ ?_ ?_
        e3.symm z hzi hzj
      · rw [hm3]; exact mem_shift _ _ _ (A + B + e₁ - e₂) cPD (by abel)
      · rw [hm5]; exact mem_shift _ _ _ (V + e₁ - e₂) cQV1' (by abel)
  · -- `P^{+,1}` and `P^{+,2}` at `U + B + e₁`
    intro z hz0 hz1
    refine pair_agree (dEven w u1 u2) f κ 0 1 ?_ (U + (B + e₁)) ?_ ?_ e1 z hz0 hz1
    · obtain ⟨C, hC⟩ := hdc01
      exact ⟨C, fun z h0' h1' => hC z (by rw [← hd0]; exact h0') (by rw [← hd1]; exact h1')⟩
    · rw [hd0]; exact mem_shift _ _ _ (B + e₁) (MarksIn.marksOdd_sub u1 cPB1) (by abel)
    · rw [hd1]; exact mem_shift _ _ _ e₁ (MarksIn.marksOdd_sub u1 cP1) (by abel)
  · -- `P^{-,1}` and `P^{-,2}` at `V + B + e₁`
    intro z hz2 hz3
    refine pair_agree (dEven w u1 u2) f κ 2 3 ?_ (V + B + e₁) ?_ ?_ e4.symm z hz2 hz3
    · obtain ⟨C, hC⟩ := hdc23
      exact ⟨C, fun z h2' h3' => hC z (by rw [← hd2]; exact h2') (by rw [← hd3]; exact h3')⟩
    · rw [hd2]; exact mem_shift _ _ _ (B + e₁) (MarksIn.marksOdd_sub u1 cPB1) (by abel)
    · rw [hd3]; exact mem_shift _ _ _ e₁ (MarksIn.marksOdd_sub u1 cP1) (by abel)

/-- **Condition (C) for the even child with `W_1` odd** (odd-first): the excluded pairs are `(P^{+,1}, Q^-)`,
`(P^{-,2}, Q^+)` and the optional interfaces `(P^{+,2}, Q^+)`, `(P^{-,1}, Q^-)`. -/
theorem closedPathEven_oddFirst (w u1 u2 : Word) (hph : phase w = 1)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (oP oQ : ℤ × ℤ → ℤ) (c : ℕ → ℤ)
    (hcP : CornerDiffs oP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      (parentsAt w).odd.num (parentsAt w).odd.den)
    (hcQ : CornerDiffs oQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      (parentsAt w).even.num (parentsAt w).even.den)
    (hdbl : ∃ k : ℤ, ∀ x, x ∈ tOddSet u1 → x + texV2 (parentsAt w).odd ∈ tOddSet u1 →
      oP (x + texV2 (parentsAt w).odd) - oP x - dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) x = k)
    (hcompat : MixedCompatEven w u1 u2 (placedEven w oP oQ c))
    (hexcl : (∀ z, z ∈ dEven w u1 u2 0 → z ∈ dEven w u1 u2 5 → False) ∧
      (∀ z, z ∈ dEven w u1 u2 3 → z ∈ dEven w u1 u2 4 → False))
    (htri : ((∃ z, z ∈ mEven w u1 u2 1 ∧ z ∈ mEven w u1 u2 4) → ∃ z, z ∈ mEven w u1 u2 1 ∧ z ∈ mEven w u1 u2 4 ∧
        placedEven w oP oQ c 1 z - placedEven w oP oQ c 4 z =
          (placedEven w oP oQ c 1 (texV2 (parentsAt w).odd + e₁) -
            placedEven w oP oQ c 0 (texV2 (parentsAt w).odd + e₁)) +
          (placedEven w oP oQ c 0 (texV1Odd (parentsAt w).odd) -
            placedEven w oP oQ c 4 (texV1Odd (parentsAt w).odd))) ∧
      ((∃ z, z ∈ mEven w u1 u2 2 ∧ z ∈ mEven w u1 u2 5) → ∃ z, z ∈ mEven w u1 u2 2 ∧ z ∈ mEven w u1 u2 5 ∧
        placedEven w oP oQ c 2 z - placedEven w oP oQ c 5 z =
          (placedEven w oP oQ c 2 (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + texV2 (parentsAt w).odd +
              e₁) -
            placedEven w oP oQ c 3 (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + texV2 (parentsAt w).odd +
              e₁)) +
          (placedEven w oP oQ c 3 (texV2 (parentsAt w).odd + texV2 (parentsAt w).odd +
              (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + e₁ - e₂)) -
            placedEven w oP oQ c 5 (texV2 (parentsAt w).odd + texV2 (parentsAt w).odd +
              (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + e₁ - e₂))))) :
    ClosedPathEven w u1 u2 (placedEven w oP oQ c) := by
  have hP := evenP_of w hph
  have hQ := evenQ_of w hph
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p
  set B := texV2 p
  set U := texV1Even q
  set V := texV2 q
  set f := placedEven w oP oQ c with hfdef
  have h0 : IsPiece (f 0) oP 0 0 (c 0) := fun z => by simp [hfdef, placedEven, hP, affEven]
  have h1 : IsPiece (f 1) oP B (p.num, -p.den) (c 1) := fun z => by
    simp [hfdef, placedEven, hP, affEven, hpdef]
  have h2 : IsPiece (f 2) oP (U + V) (q.num, -q.den) (c 2) := fun z => by
    simp [hfdef, placedEven, hP, affEven, hqdef]
  have h3 : IsPiece (f 3) oP (U + V + B) ((p.num, -p.den) + (q.num, -q.den)) (c 3) := fun z => by
    simp [hfdef, placedEven, hP, affEven, hpdef, hqdef]
  have h4 : IsPiece (f 4) oQ A 0 (c 4) := fun z => by simp [hfdef, placedEven, hQ, affEven]
  have h5 : IsPiece (f 5) oQ (B + B) ((p.num, -p.den) + (p.num, -p.den)) (c 5) := fun z => by
    simp [hfdef, placedEven, hQ, affEven, hpdef]
  have hv : StepVectors p.num p.den q.num q.den A B U V (p.num, -p.den) (q.num, -q.den) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hsum := even_odd_first p.num p.den q.num q.den A B U V _ _ hv oP oQ f c h0 h1 h2 h3 h4 h5 hcP hcQ
  have hnd : [4, 0, 1, 5, 3, 2].Nodup := by decide
  obtain ⟨-, e0, e1, e2, e3, e4, e5⟩ := hexKappa_spec f 4 0 1 5 3 2 A (B + e₁) (B + (B + e₁))
    (B + B + (U + V + e₁ - e₂)) (U + V + B + e₁) (U + V + (A - e₂)) hnd
  set κ := hexKappa f 4 0 1 5 3 2 A (B + e₁) (B + (B + e₁)) (B + B + (U + V + e₁ - e₂)) (U + V + B + e₁)
  have e5' := e5.2 hsum
  have hm0 : mEven w u1 u2 0 = shiftS (marksOdd u1) 0 := by simp [mEven, pieceSet, hP]
  have hm1 : mEven w u1 u2 1 = shiftS (marksOdd u1) B := by simp [mEven, pieceSet, hP]
  have hm2 : mEven w u1 u2 2 = shiftS (marksOdd u1) (U + V) := by simp [mEven, pieceSet, hP]
  have hm3 : mEven w u1 u2 3 = shiftS (marksOdd u1) (U + V + B) := by simp [mEven, pieceSet, hP]
  have hm4 : mEven w u1 u2 4 = shiftS (marksEven u2) A := by simp [mEven, pieceSet, hP, hQ]
  have hm5 : mEven w u1 u2 5 = shiftS (marksEven u2) (B + B) := by simp [mEven, pieceSet, hP, hQ]
  have hd0 : dEven w u1 u2 0 = shiftS (tOddSet u1) 0 := by simp [dEven, pieceSet, hP]
  have hd1 : dEven w u1 u2 1 = shiftS (tOddSet u1) (0 + B) := by simp [dEven, pieceSet, hP]
  have hd2 : dEven w u1 u2 2 = shiftS (tOddSet u1) (U + V) := by simp [dEven, pieceSet, hP]
  have hd3 : dEven w u1 u2 3 = shiftS (tOddSet u1) (U + V + B) := by simp [dEven, pieceSet, hP]
  obtain ⟨cP0, cP1, cPA', cPA, cPB1, cPB1', cPD, cPD'⟩ := corner_marks_odd u1
  obtain ⟨cQ0, cQ1, cQU', cQU, cQV1, cQV1', cQD, cQD'⟩ := corner_marks_even u2
  rw [← hp] at cPA' cPA cPB1 cPB1' cPD cPD'
  rw [← hq] at cQU' cQU cQV1 cQV1' cQD cQD'
  have hdc01 := even_dbl_const oP (tOddSet u1) B (p.num, -p.den) 0 0 (c 0) (c 1) (f 0) (f 1) hdbl h0
    (by simpa using h1)
  have hdc23 := even_dbl_const oP (tOddSet u1) B (p.num, -p.den) (q.num, -q.den) (U + V) (c 2) (c 3) (f 2) (f 3)
    hdbl h2 (by simpa [add_comm] using h3)
  have none : ∀ i j, (∀ z, z ∈ dEven w u1 u2 i → z ∈ dEven w u1 u2 j → False) →
      ∀ z, z ∈ mEven w u1 u2 i → z ∈ mEven w u1 u2 j → f i z + κ i = f j z + κ j := by
    intro i j h z hzi hzj
    exact (h z (mEven_sub w u1 u2 i hzi) (mEven_sub w u1 u2 j hzj)).elim
  apply closedPathEven_of_pairs w u1 u2 f κ
  · intro i j hi hj hj6 z hzi hzj
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    all_goals obtain rfl | rfl : j = 4 ∨ j = 5 := by omega
    · -- `P^{+,1}` and `Q^+` at `A`
      refine pair_agree (mEven w u1 u2) f κ 0 4 (hcompat 0 4 (by norm_num) (by norm_num) (by norm_num)) A ?_ ?_
        e0.symm z hzi hzj
      · rw [hm0]; exact mem_shift _ _ _ A cPA (by abel)
      · rw [hm4]; exact mem_shift _ _ _ 0 cQ0 (by abel)
    · exact none 0 5 hexcl.1 z hzi hzj
    · -- the optional interface `P^{+,2}`, `Q^+`
      obtain ⟨y, hy1, hy4, hyv⟩ := htri.1 ⟨z, hzi, hzj⟩
      refine pair_agree (mEven w u1 u2) f κ 1 4 (hcompat 1 4 (by norm_num) (by norm_num) (by norm_num)) y hy1 hy4
        ?_ z hzi hzj
      linarith
    · -- `P^{+,2}` and `Q^-` at `2B + e₁`
      refine pair_agree (mEven w u1 u2) f κ 1 5 (hcompat 1 5 (by norm_num) (by norm_num) (by norm_num)) _ ?_ ?_
        e2 z hzi hzj
      · rw [hm1]; exact mem_shift _ _ _ (B + e₁) cPB1 (by abel)
      · rw [hm5]; exact mem_shift _ _ _ e₁ cQ1 (by abel)
    · -- `P^{-,1}` and `Q^+` at `U + V + A - e₂` (the closing interface)
      refine pair_agree (mEven w u1 u2) f κ 2 4 (hcompat 2 4 (by norm_num) (by norm_num) (by norm_num)) _ ?_ ?_
        e5' z hzi hzj
      · rw [hm2]; exact mem_shift _ _ _ (A - e₂) cPA' (by abel)
      · rw [hm4]; exact mem_shift _ _ _ (U + V - e₂) cQD' (by abel)
    · -- the optional interface `P^{-,1}`, `Q^-`
      obtain ⟨y, hy2, hy5, hyv⟩ := htri.2 ⟨z, hzi, hzj⟩
      refine pair_agree (mEven w u1 u2) f κ 2 5 (hcompat 2 5 (by norm_num) (by norm_num) (by norm_num)) y hy2 hy5
        ?_ z hzi hzj
      linarith
    · exact none 3 4 hexcl.2 z hzi hzj
    · -- `P^{-,2}` and `Q^-` at `2B + U + V + e₁ - e₂`
      refine pair_agree (mEven w u1 u2) f κ 3 5 (hcompat 3 5 (by norm_num) (by norm_num) (by norm_num)) _ ?_ ?_
        e3.symm z hzi hzj
      · rw [hm3]; exact mem_shift _ _ _ (B + e₁ - e₂) cPB1' (by abel)
      · rw [hm5]; exact mem_shift _ _ _ (U + V + e₁ - e₂) cQD (by abel)
  · -- `P^{+,1}` and `P^{+,2}` at `B + e₁`
    intro z hz0 hz1
    refine pair_agree (dEven w u1 u2) f κ 0 1 ?_ (B + e₁) ?_ ?_ e1 z hz0 hz1
    · obtain ⟨C, hC⟩ := hdc01
      exact ⟨C, fun z h0' h1' => hC z (by rw [← hd0]; exact h0') (by rw [← hd1]; exact h1')⟩
    · rw [hd0]; exact mem_shift _ _ _ (B + e₁) (MarksIn.marksOdd_sub u1 cPB1) (by abel)
    · rw [hd1]; exact mem_shift _ _ _ e₁ (MarksIn.marksOdd_sub u1 cP1) (by abel)
  · -- `P^{-,1}` and `P^{-,2}` at `U + V + B + e₁`
    intro z hz2 hz3
    refine pair_agree (dEven w u1 u2) f κ 2 3 ?_ (U + V + B + e₁) ?_ ?_ e4.symm z hz2 hz3
    · obtain ⟨C, hC⟩ := hdc23
      exact ⟨C, fun z h2' h3' => hC z (by rw [← hd2]; exact h2') (by rw [← hd3]; exact h3')⟩
    · rw [hd2]; exact mem_shift _ _ _ (B + e₁) (MarksIn.marksOdd_sub u1 cPB1) (by abel)
    · rw [hd3]; exact mem_shift _ _ _ e₁ (MarksIn.marksOdd_sub u1 cP1) (by abel)

end FLatticePaper.Tiles.ClosedPathAssembly
