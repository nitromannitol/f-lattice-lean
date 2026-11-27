import FLatticePaper.Tiles.ClosedPathAltSum

/-! # Condition (C) for the six standard subtiles of the alternate decompositions

Step 1 of `lemma:weak_alternate_odometer_properties`: constants can be chosen for the six standard subtiles of the alternate
decomposition (`eq:alt_odometer_decomposition`, both copies of each shifted doubled tile with the whole tile as domain), so that
the subodometers agree on every interface. This is `AltClosedPathOdd` / `AltClosedPathEven` (`ClosedPathAltSum.ClosedPathGen`
for the copies below), proved for every word in both orientations (`altClosedPathOdd_all`, `altClosedPathEven_all`).

**The copies**, in the order of `SurgicalAlt.copies6` (the weak alternate nodes `AltOddNodeP`, `AltEvenNodeP`): `0, 1` the two
copies of `ds(o)^+` (at `c` and `S + c`), `2, 3` those of `ds(o)^-`, `4, 5` the plain copies of the other parent, at the offsets
`coeffOff` of `altP0Coeff` / `altQ0Coeff` (`eq:alt_offsets_w1_odd/even`) with the affine factors `coeffAffine`; the second copy
of each doubling carries the extra affine factor `a_{p,2}` of the shift (`offsetA _ _ true`, as in `IsWeakDoublingAlt`), and `S`
is `S_p` or `S_q` of `altShifts`.

**The proof** follows the text's four cases (`q_0` even and `p_0` odd, `W_1` even and odd, with the text's `S`):

* the pairs `(Q^{+,1}, P^-)`, `(Q^{+,2}, P^+)`, `(Q^{-,1}, P^-)`, `(Q^{-,2}, P^+)` of the even child and `(P^{+,1}, Q^-)`,
  `(P^{+,2}, Q^+)`, `(P^{-,1}, Q^-)`, `(P^{-,2}, Q^+)` of the odd child never meet. They are separated by `x - y` (even child,
  `W_1` even), `y` (even child, `W_1` odd), `x + y` (odd child, `W_1` even) and `x` (odd child, `W_1` odd), from the boxes
  (`ClosedPathExcluded`) and the diagonal bounds (`ClosedPathDiagonal`) of the standard tiles. These exclusions need no
  hypothesis on the type: the text proves the four pairs disjoint only for Type 3 (even) and Type 2 (odd), where the alternate
  parent is omitted, from the box of a tile and a relation of that type; the bounds used here hold for every type.
* the remaining closed path `Q^{+,1}, P^+, Q^{-,1}, Q^{-,2}, P^-, Q^{+,2}` (and its analogue for the odd child) is closed by
  `ClosedPathAltSum.hex_closed`, with one corner point on each mixed interface (`ClosedPathContacts`) and the cycle sums of
  `ClosedPathAltSum`. This is the contact route, as for the standard children: the offsets are read at one point of each
  interface. It is not the text's proof, which moves the three shifted copies by `H̃(y) = H(y + S) - a^T y` onto a
  pseudo-square and applies `eq:boundary_path_difference`.

**Inputs**: the parents respect their strings on their standard tiles (`RespectsAnchored`, for the corner differences), the
doubled parent is compatible along the shift `S` (`o(x + S) - o(x) - a_{p,2}^T x` constant where both points lie in its tile;
this makes the doubled odometer `o ∪ (translate of o)` well defined on the overlap of its copies), and the mixed copies are
locally compatible (`AltMixedCompatOdd` / `AltMixedCompatEven`: their difference is constant on their marks, as for
`ClosedPathAssembly.MixedCompatOdd`). In the types where the alternate parent piece is included, this is (C) for the six
standard subtiles; the closed paths through the parent piece are Case 3 of `lemma:tile-odometer-existence` and are not
treated here. -/

namespace FLatticePaper.Tiles.ClosedPathAlt

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.SiteInduction
open FLatticePaper.Tiles.ChildGlue FLatticePaper.Tiles.MixedPieces FLatticePaper.Tiles.ClosedPathAssembly
open FLatticePaper.Tiles.ClosedPathSum FLatticePaper.Tiles.ClosedPathContacts FLatticePaper.Tiles.StandardClause
open FLatticePaper.Tiles.ClosedPathExcluded FLatticePaper.Tiles.ClosedPathDiagonal FLatticePaper.Tiles.ClosedPathAltSum
open FLatticePaper.Tiles.SurgicalAlt FLatticePaper.Tiles.SurgicalDict FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Tiles.Standard (oddTile evenTile)

/-! ### The copies of the alternate children -/

/-- The offset `Σ c_i v_i` of a coefficient vector, in the vectors of the parents of `w`. -/
abbrev cofW (w : Word) : AltCoeff → ℤ × ℤ :=
  coeffOff (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd) (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)

/-- The affine factor `c_{p,2} a_{p,2} + c_{q,2} a_{q,2}` of a coefficient vector. -/
abbrev cafW (w : Word) : AltCoeff → ℤ × ℤ :=
  coeffAffine (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den

/-- The shift `S_p` of the doubled odd parent (`altShifts`). -/
abbrev shiftP (w : Word) : ℤ × ℤ := (altShifts (phase w == 1) (texV2 (parentsAt w).odd) (texV1Even (parentsAt w).even)).1

/-- The shift `S_q` of the doubled even parent (`altShifts`). -/
abbrev shiftQ (w : Word) : ℤ × ℤ := (altShifts (phase w == 1) (texV2 (parentsAt w).odd) (texV1Even (parentsAt w).even)).2

/-- The affine factor `a_{p,2}` of both shifts. -/
abbrev affS (w : Word) : ℤ × ℤ := offsetA (parentsAt w).odd.num (parentsAt w).odd.den true

/-- The offsets of the four copies of the doubled odd parent in the odd alternate child. -/
def altOddD (w : Word) : List (ℤ × ℤ) :=
  [cofW w (altP0Coeff (phase w == 1) .dsP1Plus), shiftP w + cofW w (altP0Coeff (phase w == 1) .dsP1Plus),
    cofW w (altP0Coeff (phase w == 1) .dsP1Minus), shiftP w + cofW w (altP0Coeff (phase w == 1) .dsP1Minus)]

/-- The offsets of the two plain copies of the even parent in the odd alternate child. -/
def altOddR (w : Word) : List (ℤ × ℤ) :=
  [cofW w (altP0Coeff (phase w == 1) .q1Plus), cofW w (altP0Coeff (phase w == 1) .q1Minus)]

/-- The affine factors of the six copies of the odd alternate child. -/
def altOddAff (w : Word) : List (ℤ × ℤ) :=
  [cafW w (altP0Coeff (phase w == 1) .dsP1Plus), cafW w (altP0Coeff (phase w == 1) .dsP1Plus) + affS w,
    cafW w (altP0Coeff (phase w == 1) .dsP1Minus), cafW w (altP0Coeff (phase w == 1) .dsP1Minus) + affS w,
    cafW w (altP0Coeff (phase w == 1) .q1Plus), cafW w (altP0Coeff (phase w == 1) .q1Minus)]

/-- The offsets of the four copies of the doubled even parent in the even alternate child. -/
def altEvenD (w : Word) : List (ℤ × ℤ) :=
  [cofW w (altQ0Coeff (phase w == 1) .dsQ1Plus), shiftQ w + cofW w (altQ0Coeff (phase w == 1) .dsQ1Plus),
    cofW w (altQ0Coeff (phase w == 1) .dsQ1Minus), shiftQ w + cofW w (altQ0Coeff (phase w == 1) .dsQ1Minus)]

/-- The offsets of the two plain copies of the odd parent in the even alternate child. -/
def altEvenR (w : Word) : List (ℤ × ℤ) :=
  [cofW w (altQ0Coeff (phase w == 1) .p1Plus), cofW w (altQ0Coeff (phase w == 1) .p1Minus)]

/-- The affine factors of the six copies of the even alternate child. -/
def altEvenAff (w : Word) : List (ℤ × ℤ) :=
  [cafW w (altQ0Coeff (phase w == 1) .dsQ1Plus), cafW w (altQ0Coeff (phase w == 1) .dsQ1Plus) + affS w,
    cafW w (altQ0Coeff (phase w == 1) .dsQ1Minus), cafW w (altQ0Coeff (phase w == 1) .dsQ1Minus) + affS w,
    cafW w (altQ0Coeff (phase w == 1) .p1Plus), cafW w (altQ0Coeff (phase w == 1) .p1Minus)]

/-- The placed subodometers of the odd alternate child, from parent odometers `oP`, `oQ` and constants `c`. -/
def placedAltOdd (w : Word) (oP oQ : ℤ × ℤ → ℤ) (c : ℕ → ℤ) (i : ℕ) (z : ℤ × ℤ) : ℤ :=
  if i < 4 then oP (z - (altOddD w).getD i 0) + dot2 ((altOddAff w).getD i 0) z + c i
  else oQ (z - (altOddR w).getD (i - 4) 0) + dot2 ((altOddAff w).getD i 0) z + c i

/-- The placed subodometers of the even alternate child. -/
def placedAltEven (w : Word) (oP oQ : ℤ × ℤ → ℤ) (c : ℕ → ℤ) (i : ℕ) (z : ℤ × ℤ) : ℤ :=
  if i < 4 then oQ (z - (altEvenD w).getD i 0) + dot2 ((altEvenAff w).getD i 0) z + c i
  else oP (z - (altEvenR w).getD (i - 4) 0) + dot2 ((altEvenAff w).getD i 0) z + c i

/-- The marks and the domains of the copies of the odd alternate child. -/
abbrev mAO (w u1 u2 : Word) (i : ℕ) : Set (ℤ × ℤ) := pieceSet (altOddD w) (altOddR w) (marksOdd u1) (marksEven u2) i
abbrev dAO (w u1 u2 : Word) (i : ℕ) : Set (ℤ × ℤ) := pieceSet (altOddD w) (altOddR w) (tOddSet u1) (tEvenSet u2) i
/-- The marks and the domains of the copies of the even alternate child. -/
abbrev mAE (w u1 u2 : Word) (i : ℕ) : Set (ℤ × ℤ) := pieceSet (altEvenD w) (altEvenR w) (marksEven u2) (marksOdd u1) i
abbrev dAE (w u1 u2 : Word) (i : ℕ) : Set (ℤ × ℤ) := pieceSet (altEvenD w) (altEvenR w) (tEvenSet u2) (tOddSet u1) i

/-- **Condition (C) for the six standard subtiles of the odd alternate child.** -/
def AltClosedPathOdd (w u1 u2 : Word) (f0 : ℕ → ℤ × ℤ → ℤ) : Prop :=
  ClosedPathGen (altOddD w) (altOddR w) (tOddSet u1) (tEvenSet u2) (marksOdd u1) (marksEven u2) dblEven f0

/-- **Condition (C) for the six standard subtiles of the even alternate child.** -/
def AltClosedPathEven (w u1 u2 : Word) (f0 : ℕ → ℤ × ℤ → ℤ) : Prop :=
  ClosedPathGen (altEvenD w) (altEvenR w) (tEvenSet u2) (tOddSet u1) (marksEven u2) (marksOdd u1) dblEven f0

/-- **Local compatibility of the mixed copies, odd alternate child**: copies `i < 4` of the odd parent, `4 ≤ j < 6` of the
even one, with a constant difference on their marks. -/
def AltMixedCompatOdd (w u1 u2 : Word) (f : ℕ → ℤ × ℤ → ℤ) : Prop :=
  ∀ i j, i < 4 → 4 ≤ j → j < 6 → ∃ C : ℤ, ∀ z, z ∈ mAO w u1 u2 i → z ∈ mAO w u1 u2 j → f i z - f j z = C

/-- **Local compatibility of the mixed copies, even alternate child**. -/
def AltMixedCompatEven (w u1 u2 : Word) (f : ℕ → ℤ × ℤ → ℤ) : Prop :=
  ∀ i j, i < 4 → 4 ≤ j → j < 6 → ∃ C : ℤ, ∀ z, z ∈ mAE w u1 u2 i → z ∈ mAE w u1 u2 j → f i z - f j z = C

/-! ### The offsets, by orientation -/

theorem cof_0000 (A B U V : ℤ × ℤ) : coeffOff A B U V (0, 0, 0, 0) = 0 := by ext <;> simp [coeffOff]
theorem cof_1000 (A B U V : ℤ × ℤ) : coeffOff A B U V (1, 0, 0, 0) = A := by ext <;> simp [coeffOff]
theorem cof_0100 (A B U V : ℤ × ℤ) : coeffOff A B U V (0, 1, 0, 0) = B := by ext <;> simp [coeffOff]
theorem cof_0010 (A B U V : ℤ × ℤ) : coeffOff A B U V (0, 0, 1, 0) = U := by ext <;> simp [coeffOff]
theorem cof_0001 (A B U V : ℤ × ℤ) : coeffOff A B U V (0, 0, 0, 1) = V := by ext <;> simp [coeffOff]
theorem cof_1100 (A B U V : ℤ × ℤ) : coeffOff A B U V (1, 1, 0, 0) = A + B := by ext <;> simp [coeffOff]
theorem cof_0011 (A B U V : ℤ × ℤ) : coeffOff A B U V (0, 0, 1, 1) = U + V := by ext <;> simp [coeffOff]
theorem cof_01m11 (A B U V : ℤ × ℤ) : coeffOff A B U V (0, 1, -1, 1) = B - U + V := by
  ext <;> (simp [coeffOff]; try ring)
theorem cof_0121 (A B U V : ℤ × ℤ) : coeffOff A B U V (0, 1, 2, 1) = B + U + U + V := by
  ext <;> (simp [coeffOff]; try ring)
theorem cof_1210 (A B U V : ℤ × ℤ) : coeffOff A B U V (1, 2, 1, 0) = A + B + B + U := by
  ext <;> (simp [coeffOff]; try ring)
theorem cof_02m10 (A B U V : ℤ × ℤ) : coeffOff A B U V (0, 2, -1, 0) = B + B - U := by
  ext <;> (simp [coeffOff]; try ring)

theorem caf_0 (np dp nq dq : ℤ) (c1 c3 : ℤ) : coeffAffine np dp nq dq (c1, 0, c3, 0) = 0 := by
  ext <;> simp [coeffAffine]
theorem caf_a (np dp nq dq : ℤ) (c1 c3 : ℤ) : coeffAffine np dp nq dq (c1, 1, c3, 0) = (np, -dp) := by
  ext <;> simp [coeffAffine]
theorem caf_b (np dp nq dq : ℤ) (c1 c3 : ℤ) : coeffAffine np dp nq dq (c1, 0, c3, 1) = (nq, -dq) := by
  ext <;> simp [coeffAffine]
theorem caf_ab (np dp nq dq : ℤ) (c1 c3 : ℤ) :
    coeffAffine np dp nq dq (c1, 1, c3, 1) = (np, -dp) + (nq, -dq) := by
  ext <;> (simp [coeffAffine]; try ring)
theorem caf_2a (np dp nq dq : ℤ) (c1 c3 : ℤ) :
    coeffAffine np dp nq dq (c1, 2, c3, 0) = (np, -dp) + (np, -dp) := by
  ext <;> (simp [coeffAffine]; try ring)

theorem beq_of_ne (w : Word) (h : phase w ≠ 1) : (phase w == 1) = false := by simpa using h
theorem beq_of_eq (w : Word) (h : phase w = 1) : (phase w == 1) = true := by simp [h]

/-- The copies of the odd alternate child for `W_1` even. -/
theorem altOdd_ef (w : Word) (hph : phase w ≠ 1) :
    altOddD w = [texV1Even (parentsAt w).even, shiftP w + texV1Even (parentsAt w).even, texV2 (parentsAt w).even,
      shiftP w + texV2 (parentsAt w).even] ∧
    altOddR w = [0, texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + texV2 (parentsAt w).odd +
      texV1Even (parentsAt w).even] ∧
    altOddAff w = [0, ((parentsAt w).odd.num, -(parentsAt w).odd.den), ((parentsAt w).even.num, -(parentsAt w).even.den),
      ((parentsAt w).even.num, -(parentsAt w).even.den) + ((parentsAt w).odd.num, -(parentsAt w).odd.den), 0,
      ((parentsAt w).odd.num, -(parentsAt w).odd.den) + ((parentsAt w).odd.num, -(parentsAt w).odd.den)] ∧
    shiftP w = texV1Even (parentsAt w).even + texV2 (parentsAt w).odd := by
  have hb := beq_of_ne w hph
  have e1 : altP0Coeff (phase w == 1) .dsP1Plus = (0, 0, 1, 0) := by rw [hb]; rfl
  have e2 : altP0Coeff (phase w == 1) .dsP1Minus = (0, 0, 0, 1) := by rw [hb]; rfl
  have e3 : altP0Coeff (phase w == 1) .q1Plus = (0, 0, 0, 0) := by rw [hb]; rfl
  have e4 : altP0Coeff (phase w == 1) .q1Minus = (1, 2, 1, 0) := by rw [hb]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [altOddD, e1, e2, cofW, cof_0010, cof_0001]
  · simp only [altOddR, e3, e4, cofW, cof_0000, cof_1210]
  · simp only [altOddAff, e1, e2, e3, e4, cafW, caf_0, caf_b, caf_2a, affS, offsetA, zero_add]
  · show (altShifts (phase w == 1) _ _).1 = _
    rw [hb]
    rfl

/-- The copies of the odd alternate child for `W_1` odd. -/
theorem altOdd_of (w : Word) (hph : phase w = 1) :
    altOddD w = [0, shiftP w + 0, texV1Even (parentsAt w).even + texV2 (parentsAt w).even,
      shiftP w + (texV1Even (parentsAt w).even + texV2 (parentsAt w).even)] ∧
    altOddR w = [texV1Odd (parentsAt w).odd, texV2 (parentsAt w).odd + texV2 (parentsAt w).odd -
      texV1Even (parentsAt w).even] ∧
    altOddAff w = [0, ((parentsAt w).odd.num, -(parentsAt w).odd.den), ((parentsAt w).even.num, -(parentsAt w).even.den),
      ((parentsAt w).even.num, -(parentsAt w).even.den) + ((parentsAt w).odd.num, -(parentsAt w).odd.den), 0,
      ((parentsAt w).odd.num, -(parentsAt w).odd.den) + ((parentsAt w).odd.num, -(parentsAt w).odd.den)] ∧
    shiftP w = -texV1Even (parentsAt w).even + texV2 (parentsAt w).odd := by
  have hb := beq_of_eq w hph
  have e1 : altP0Coeff (phase w == 1) .dsP1Plus = (0, 0, 0, 0) := by rw [hb]; rfl
  have e2 : altP0Coeff (phase w == 1) .dsP1Minus = (0, 0, 1, 1) := by rw [hb]; rfl
  have e3 : altP0Coeff (phase w == 1) .q1Plus = (1, 0, 0, 0) := by rw [hb]; rfl
  have e4 : altP0Coeff (phase w == 1) .q1Minus = (0, 2, -1, 0) := by rw [hb]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [altOddD, e1, e2, cofW, cof_0000, cof_0011]
  · simp only [altOddR, e3, e4, cofW, cof_1000, cof_02m10]
  · simp only [altOddAff, e1, e2, e3, e4, cafW, caf_0, caf_b, caf_2a, affS, offsetA, zero_add]
  · show (altShifts (phase w == 1) _ _).1 = _
    rw [hb]
    rfl

/-- The copies of the even alternate child for `W_1` even. -/
theorem altEven_ef (w : Word) (hph : phase w ≠ 1) :
    altEvenD w = [0, shiftQ w + 0, texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd,
      shiftQ w + (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd)] ∧
    altEvenR w = [texV1Even (parentsAt w).even, texV2 (parentsAt w).odd - texV1Even (parentsAt w).even +
      texV2 (parentsAt w).even] ∧
    altEvenAff w = [0, ((parentsAt w).odd.num, -(parentsAt w).odd.den), ((parentsAt w).odd.num, -(parentsAt w).odd.den),
      ((parentsAt w).odd.num, -(parentsAt w).odd.den) + ((parentsAt w).odd.num, -(parentsAt w).odd.den), 0,
      ((parentsAt w).odd.num, -(parentsAt w).odd.den) + ((parentsAt w).even.num, -(parentsAt w).even.den)] ∧
    shiftQ w = -texV1Even (parentsAt w).even + texV2 (parentsAt w).odd := by
  have hb := beq_of_ne w hph
  have e1 : altQ0Coeff (phase w == 1) .dsQ1Plus = (0, 0, 0, 0) := by rw [hb]; rfl
  have e2 : altQ0Coeff (phase w == 1) .dsQ1Minus = (1, 1, 0, 0) := by rw [hb]; rfl
  have e3 : altQ0Coeff (phase w == 1) .p1Plus = (0, 0, 1, 0) := by rw [hb]; rfl
  have e4 : altQ0Coeff (phase w == 1) .p1Minus = (0, 1, -1, 1) := by rw [hb]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [altEvenD, e1, e2, cofW, cof_0000, cof_1100]
  · simp only [altEvenR, e3, e4, cofW, cof_0010, cof_01m11]
  · simp only [altEvenAff, e1, e2, e3, e4, cafW, caf_0, caf_a, caf_ab, affS, offsetA, zero_add]
  · show (altShifts (phase w == 1) _ _).2 = _
    rw [hb]
    rfl

/-- The copies of the even alternate child for `W_1` odd. -/
theorem altEven_of (w : Word) (hph : phase w = 1) :
    altEvenD w = [texV1Odd (parentsAt w).odd, shiftQ w + texV1Odd (parentsAt w).odd, texV2 (parentsAt w).odd,
      shiftQ w + texV2 (parentsAt w).odd] ∧
    altEvenR w = [0, texV2 (parentsAt w).odd + texV1Even (parentsAt w).even + texV1Even (parentsAt w).even +
      texV2 (parentsAt w).even] ∧
    altEvenAff w = [0, ((parentsAt w).odd.num, -(parentsAt w).odd.den), ((parentsAt w).odd.num, -(parentsAt w).odd.den),
      ((parentsAt w).odd.num, -(parentsAt w).odd.den) + ((parentsAt w).odd.num, -(parentsAt w).odd.den), 0,
      ((parentsAt w).odd.num, -(parentsAt w).odd.den) + ((parentsAt w).even.num, -(parentsAt w).even.den)] ∧
    shiftQ w = texV1Even (parentsAt w).even + texV2 (parentsAt w).odd := by
  have hb := beq_of_eq w hph
  have e1 : altQ0Coeff (phase w == 1) .dsQ1Plus = (1, 0, 0, 0) := by rw [hb]; rfl
  have e2 : altQ0Coeff (phase w == 1) .dsQ1Minus = (0, 1, 0, 0) := by rw [hb]; rfl
  have e3 : altQ0Coeff (phase w == 1) .p1Plus = (0, 0, 0, 0) := by rw [hb]; rfl
  have e4 : altQ0Coeff (phase w == 1) .p1Minus = (0, 1, 2, 1) := by rw [hb]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [altEvenD, e1, e2, cofW, cof_1000, cof_0100]
  · simp only [altEvenR, e3, e4, cofW, cof_0000, cof_0121]
  · simp only [altEvenAff, e1, e2, e3, e4, cafW, caf_0, caf_a, caf_ab, affS, offsetA, zero_add]
  · show (altShifts (phase w == 1) _ _).2 = _
    rw [hb]
    rfl

/-! ### The pairs that never meet -/

/-- **The excluded pairs of the even alternate child, `W_1` even**: `Q^{+,1}, Q^{+,2}, Q^{-,1}, Q^{-,2}` against `P^-, P^+,
P^-, P^+`, separated by `x - y`. -/
theorem altExclEven_ef (w u1 u2 : Word) (hph : phase w ≠ 1)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2) :
    (∀ z, z ∈ dAE w u1 u2 0 → z ∈ dAE w u1 u2 5 → False) ∧ (∀ z, z ∈ dAE w u1 u2 1 → z ∈ dAE w u1 u2 4 → False) ∧
    (∀ z, z ∈ dAE w u1 u2 2 → z ∈ dAE w u1 u2 5 → False) ∧ (∀ z, z ∈ dAE w u1 u2 3 → z ∈ dAE w u1 u2 4 → False) := by
  obtain ⟨hD, hR, -, hS⟩ := altEven_ef w hph
  have hpl := SiteHullOdd.curO_pos_lt u1
  have hql := SiteHullEven.curE_pos_lt u2
  have hcu : SiteInduction.curO u1 = fracOdd u1 := rfl
  have hce : SiteInduction.curE u2 = fracEven u2 := rfl
  rw [hcu, ← hp] at hpl
  rw [hce, ← hq] at hql
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro z ha hb <;> simp only [dAE, pieceSet, hD, hR, hS] at ha hb <;> simp at ha hb
  all_goals
    have b1 := diag_shift_even u2 _ z ha
    have b2 := diag_shift_odd u1 _ z hb
    rw [← hq] at b1
    rw [← hp] at b2
    simp only [texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, Prod.fst_sub,
      Prod.snd_sub, Prod.fst_zero, Prod.snd_zero] at b1 b2
    omega

/-- **The excluded pairs of the even alternate child, `W_1` odd**, separated by `y`. -/
theorem altExclEven_of (w u1 u2 : Word) (hph : phase w = 1)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2) :
    (∀ z, z ∈ dAE w u1 u2 0 → z ∈ dAE w u1 u2 5 → False) ∧ (∀ z, z ∈ dAE w u1 u2 1 → z ∈ dAE w u1 u2 4 → False) ∧
    (∀ z, z ∈ dAE w u1 u2 2 → z ∈ dAE w u1 u2 5 → False) ∧ (∀ z, z ∈ dAE w u1 u2 3 → z ∈ dAE w u1 u2 4 → False) := by
  obtain ⟨hD, hR, -, hS⟩ := altEven_of w hph
  have hpl := SiteHullOdd.curO_pos_lt u1
  have hql := SiteHullEven.curE_pos_lt u2
  have hcu : SiteInduction.curO u1 = fracOdd u1 := rfl
  have hce : SiteInduction.curE u2 = fracEven u2 := rfl
  rw [hcu, ← hp] at hpl
  rw [hce, ← hq] at hql
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro z ha hb <;> simp only [dAE, pieceSet, hD, hR, hS] at ha hb <;> simp at ha hb
  all_goals
    have b1 := box_shift_even u2 _ z ha
    have b2 := box_shift_odd u1 _ z hb
    rw [← hq] at b1
    rw [← hp] at b2
    simp only [texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add,
      Prod.fst_zero, Prod.snd_zero] at b1 b2
    omega

/-- **The excluded pairs of the odd alternate child, `W_1` even**: `P^{+,1}, P^{+,2}, P^{-,1}, P^{-,2}` against `Q^-, Q^+,
Q^-, Q^+`, separated by `x + y`. -/
theorem altExclOdd_ef (w u1 u2 : Word) (hph : phase w ≠ 1)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2) :
    (∀ z, z ∈ dAO w u1 u2 0 → z ∈ dAO w u1 u2 5 → False) ∧ (∀ z, z ∈ dAO w u1 u2 1 → z ∈ dAO w u1 u2 4 → False) ∧
    (∀ z, z ∈ dAO w u1 u2 2 → z ∈ dAO w u1 u2 5 → False) ∧ (∀ z, z ∈ dAO w u1 u2 3 → z ∈ dAO w u1 u2 4 → False) := by
  obtain ⟨hD, hR, -, hS⟩ := altOdd_ef w hph
  have hpl := SiteHullOdd.curO_pos_lt u1
  have hql := SiteHullEven.curE_pos_lt u2
  have hcu : SiteInduction.curO u1 = fracOdd u1 := rfl
  have hce : SiteInduction.curE u2 = fracEven u2 := rfl
  rw [hcu, ← hp] at hpl
  rw [hce, ← hq] at hql
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro z ha hb <;> simp only [dAO, pieceSet, hD, hR, hS] at ha hb <;> simp at ha hb
  all_goals
    have b1 := diag_shift_odd u1 _ z ha
    have b2 := diag_shift_even u2 _ z hb
    rw [← hp] at b1
    rw [← hq] at b2
    simp only [texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add,
      Prod.fst_zero, Prod.snd_zero] at b1 b2
    omega

/-- **The excluded pairs of the odd alternate child, `W_1` odd**, separated by `x`. -/
theorem altExclOdd_of (w u1 u2 : Word) (hph : phase w = 1)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2) :
    (∀ z, z ∈ dAO w u1 u2 0 → z ∈ dAO w u1 u2 5 → False) ∧ (∀ z, z ∈ dAO w u1 u2 1 → z ∈ dAO w u1 u2 4 → False) ∧
    (∀ z, z ∈ dAO w u1 u2 2 → z ∈ dAO w u1 u2 5 → False) ∧ (∀ z, z ∈ dAO w u1 u2 3 → z ∈ dAO w u1 u2 4 → False) := by
  obtain ⟨hD, hR, -, hS⟩ := altOdd_of w hph
  have hpl := SiteHullOdd.curO_pos_lt u1
  have hql := SiteHullEven.curE_pos_lt u2
  have hcu : SiteInduction.curO u1 = fracOdd u1 := rfl
  have hce : SiteInduction.curE u2 = fracEven u2 := rfl
  rw [hcu, ← hp] at hpl
  rw [hce, ← hq] at hql
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro z ha hb <;> simp only [dAO, pieceSet, hD, hR, hS] at ha hb <;> simp at ha hb
  all_goals
    have b1 := box_shift_odd u1 _ z ha
    have b2 := box_shift_even u2 _ z hb
    rw [← hp] at b1
    rw [← hq] at b2
    simp only [texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, Prod.fst_sub,
      Prod.snd_sub, Prod.fst_zero, Prod.snd_zero] at b1 b2
    omega

/-! ### Condition (C) in the four cases -/

/-- **Even alternate child, `W_1` even.** -/
theorem altClosedPathEven_ef (w u1 u2 : Word) (hph : phase w ≠ 1)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (oP oQ : ℤ × ℤ → ℤ) (c : ℕ → ℤ)
    (hcP : CornerDiffs oP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      (parentsAt w).odd.num (parentsAt w).odd.den)
    (hcQ : CornerDiffs oQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      (parentsAt w).even.num (parentsAt w).even.den)
    (hk : ∃ k : ℤ, ∀ x, x ∈ tEvenSet u2 → x + shiftQ w ∈ tEvenSet u2 →
      oQ (x + shiftQ w) - oQ x - dot2 (affS w) x = k)
    (hcompat : AltMixedCompatEven w u1 u2 (placedAltEven w oP oQ c)) :
    AltClosedPathEven w u1 u2 (placedAltEven w oP oQ c) := by
  obtain ⟨x05, x14, x25, x34⟩ := altExclEven_ef w u1 u2 hph hp hq
  obtain ⟨hD, hR, hAf, hSh⟩ := altEven_ef w hph
  obtain ⟨k, hk⟩ := hk
  obtain ⟨cP0, cP1, -, -, -, -, cPD, cPD'⟩ := corner_marks_odd u1
  obtain ⟨-, -, cQU', cQU, cQV1, cQV1', -, -⟩ := corner_marks_even u2
  rw [← hp] at cPD cPD'
  rw [← hq] at cQU' cQU cQV1 cQV1'
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p
  set B := texV2 p
  set U := texV1Even q
  set V := texV2 q
  set S := shiftQ w with hSdef
  set f := placedAltEven w oP oQ c with hfdef
  have h0 : IsPiece (f 0) oQ 0 0 (c 0) := fun z => by simp [hfdef, placedAltEven, hD, hAf]
  have h1 : IsPiece (f 1) oQ (S + 0) (p.num, -p.den) (c 1) := fun z => by simp [hfdef, placedAltEven, hD, hAf]
  have h2 : IsPiece (f 2) oQ (A + B) (p.num, -p.den) (c 2) := fun z => by simp [hfdef, placedAltEven, hD, hAf]
  have h3 : IsPiece (f 3) oQ (S + (A + B)) ((p.num, -p.den) + (p.num, -p.den)) (c 3) := fun z => by
    simp [hfdef, placedAltEven, hD, hAf]
  have h4 : IsPiece (f 4) oP U 0 (c 4) := fun z => by simp [hfdef, placedAltEven, hR, hAf]
  have h5 : IsPiece (f 5) oP (B - U + V) ((p.num, -p.den) + (q.num, -q.den)) (c 5) := fun z => by
    simp [hfdef, placedAltEven, hR, hAf]
  have hv : StepVectors p.num p.den q.num q.den A B U V (p.num, -p.den) (q.num, -q.den) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hsum := ClosedPathAltSum.altEven_even_first p.num p.den q.num q.den A B U V _ _ S hv hSh oP oQ f c k
    h0 h1 h2 h3 h4 h5 hcP hcQ
  have hkS : ∀ x, x ∈ tEvenSet u2 → x + S ∈ tEvenSet u2 → oQ (x + S) - oQ x - dot2 (p.num, -p.den) x = k := hk
  have hd0 : pieceSet (altEvenD w) (altEvenR w) (tEvenSet u2) (tOddSet u1) 0 = shiftS (tEvenSet u2) 0 := by
    simp [pieceSet, hD]
  have hd1 : pieceSet (altEvenD w) (altEvenR w) (tEvenSet u2) (tOddSet u1) 1 = shiftS (tEvenSet u2) (S + 0) := by
    simp [pieceSet, hD]
  have hd2 : pieceSet (altEvenD w) (altEvenR w) (tEvenSet u2) (tOddSet u1) 2 = shiftS (tEvenSet u2) (A + B) := by
    simp [pieceSet, hD]
  have hd3 : pieceSet (altEvenD w) (altEvenR w) (tEvenSet u2) (tOddSet u1) 3 = shiftS (tEvenSet u2) (S + (A + B)) := by
    simp [pieceSet, hD]
  have hm0 : pieceSet (altEvenD w) (altEvenR w) (marksEven u2) (marksOdd u1) 0 = shiftS (marksEven u2) 0 := by
    simp [pieceSet, hD]
  have hm1 : pieceSet (altEvenD w) (altEvenR w) (marksEven u2) (marksOdd u1) 1 = shiftS (marksEven u2) (S + 0) := by
    simp [pieceSet, hD]
  have hm2 : pieceSet (altEvenD w) (altEvenR w) (marksEven u2) (marksOdd u1) 2 = shiftS (marksEven u2) (A + B) := by
    simp [pieceSet, hD]
  have hm3 : pieceSet (altEvenD w) (altEvenR w) (marksEven u2) (marksOdd u1) 3 = shiftS (marksEven u2) (S + (A + B)) := by
    simp [pieceSet, hD]
  have hm4 : pieceSet (altEvenD w) (altEvenR w) (marksEven u2) (marksOdd u1) 4 = shiftS (marksOdd u1) U := by
    simp [pieceSet, hD, hR]
  have hm5 : pieceSet (altEvenD w) (altEvenR w) (marksEven u2) (marksOdd u1) 5 = shiftS (marksOdd u1) (B - U + V) := by
    simp [pieceSet, hD, hR]
  refine hex_closed (altEvenD w) (altEvenR w) (tEvenSet u2) (tOddSet u1) (marksEven u2) (marksOdd u1) f
    (by simp [hD]) (by simp [hR]) (MarksIn.marksEven_sub u2) (MarksIn.marksOdd_sub u1) _ _ ?_ ?_ hcompat
    (B - U + V + e₁) U (U + (A + B - e₂)) (B - U + V + (A + B + e₁ - e₂)) ?_ ?_ ?_ ?_ x05 x14 x25 x34 hsum
  · intro z hz0 hz1
    rw [hd0] at hz0
    rw [hd1] at hz1
    exact dbl_const oQ (tEvenSet u2) S (p.num, -p.den) 0 (p.num, -p.den) 0 (c 0) (c 1) k (f 0) (f 1) hkS h0 h1
      (by simp) z hz0 hz1
  · intro z hz2 hz3
    rw [hd2] at hz2
    rw [hd3] at hz3
    exact dbl_const oQ (tEvenSet u2) S (p.num, -p.den) (p.num, -p.den) _ (A + B) (c 2) (c 3) k (f 2) (f 3) hkS h2 h3
      rfl z hz2 hz3
  · rw [hm1, hm5]
    exact ⟨mem_shift _ _ _ (V + e₁) cQV1 (by rw [hSh]; abel), mem_shift _ _ _ e₁ cP1 (by abel)⟩
  · rw [hm0, hm4]
    exact ⟨mem_shift _ _ _ U cQU (by abel), mem_shift _ _ _ 0 cP0 (by abel)⟩
  · rw [hm2, hm4]
    exact ⟨mem_shift _ _ _ (U - e₂) cQU' (by abel), mem_shift _ _ _ (A + B - e₂) cPD' (by abel)⟩
  · rw [hm3, hm5]
    exact ⟨mem_shift _ _ _ (V + e₁ - e₂) cQV1' (by rw [hSh]; abel), mem_shift _ _ _ (A + B + e₁ - e₂) cPD (by abel)⟩

/-- **Even alternate child, `W_1` odd.** -/
theorem altClosedPathEven_of (w u1 u2 : Word) (hph : phase w = 1)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (oP oQ : ℤ × ℤ → ℤ) (c : ℕ → ℤ)
    (hcP : CornerDiffs oP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      (parentsAt w).odd.num (parentsAt w).odd.den)
    (hcQ : CornerDiffs oQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      (parentsAt w).even.num (parentsAt w).even.den)
    (hk : ∃ k : ℤ, ∀ x, x ∈ tEvenSet u2 → x + shiftQ w ∈ tEvenSet u2 →
      oQ (x + shiftQ w) - oQ x - dot2 (affS w) x = k)
    (hcompat : AltMixedCompatEven w u1 u2 (placedAltEven w oP oQ c)) :
    AltClosedPathEven w u1 u2 (placedAltEven w oP oQ c) := by
  obtain ⟨x05, x14, x25, x34⟩ := altExclEven_of w u1 u2 hph hp hq
  obtain ⟨hD, hR, hAf, hSh⟩ := altEven_of w hph
  obtain ⟨k, hk⟩ := hk
  obtain ⟨-, -, cPA', cPA, cPB1, cPB1', -, -⟩ := corner_marks_odd u1
  obtain ⟨cQ0, cQ1, -, -, -, -, cQD, cQD'⟩ := corner_marks_even u2
  rw [← hp] at cPA' cPA cPB1 cPB1'
  rw [← hq] at cQD cQD'
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p
  set B := texV2 p
  set U := texV1Even q
  set V := texV2 q
  set S := shiftQ w with hSdef
  set f := placedAltEven w oP oQ c with hfdef
  have h0 : IsPiece (f 0) oQ A 0 (c 0) := fun z => by simp [hfdef, placedAltEven, hD, hAf]
  have h1 : IsPiece (f 1) oQ (S + A) (p.num, -p.den) (c 1) := fun z => by simp [hfdef, placedAltEven, hD, hAf]
  have h2 : IsPiece (f 2) oQ B (p.num, -p.den) (c 2) := fun z => by simp [hfdef, placedAltEven, hD, hAf]
  have h3 : IsPiece (f 3) oQ (S + B) ((p.num, -p.den) + (p.num, -p.den)) (c 3) := fun z => by
    simp [hfdef, placedAltEven, hD, hAf]
  have h4 : IsPiece (f 4) oP 0 0 (c 4) := fun z => by simp [hfdef, placedAltEven, hR, hAf]
  have h5 : IsPiece (f 5) oP (B + U + U + V) ((p.num, -p.den) + (q.num, -q.den)) (c 5) := fun z => by
    simp [hfdef, placedAltEven, hR, hAf]
  have hv : StepVectors p.num p.den q.num q.den A B U V (p.num, -p.den) (q.num, -q.den) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hsum := ClosedPathAltSum.altEven_odd_first p.num p.den q.num q.den A B U V _ _ S hv hSh oP oQ f c k
    h0 h1 h2 h3 h4 h5 hcP hcQ
  have hkS : ∀ x, x ∈ tEvenSet u2 → x + S ∈ tEvenSet u2 → oQ (x + S) - oQ x - dot2 (p.num, -p.den) x = k := hk
  have hd0 : pieceSet (altEvenD w) (altEvenR w) (tEvenSet u2) (tOddSet u1) 0 = shiftS (tEvenSet u2) A := by
    simp [pieceSet, hD]
  have hd1 : pieceSet (altEvenD w) (altEvenR w) (tEvenSet u2) (tOddSet u1) 1 = shiftS (tEvenSet u2) (S + A) := by
    simp [pieceSet, hD]
  have hd2 : pieceSet (altEvenD w) (altEvenR w) (tEvenSet u2) (tOddSet u1) 2 = shiftS (tEvenSet u2) B := by
    simp [pieceSet, hD]
  have hd3 : pieceSet (altEvenD w) (altEvenR w) (tEvenSet u2) (tOddSet u1) 3 = shiftS (tEvenSet u2) (S + B) := by
    simp [pieceSet, hD]
  have hm0 : pieceSet (altEvenD w) (altEvenR w) (marksEven u2) (marksOdd u1) 0 = shiftS (marksEven u2) A := by
    simp [pieceSet, hD]
  have hm1 : pieceSet (altEvenD w) (altEvenR w) (marksEven u2) (marksOdd u1) 1 = shiftS (marksEven u2) (S + A) := by
    simp [pieceSet, hD]
  have hm2 : pieceSet (altEvenD w) (altEvenR w) (marksEven u2) (marksOdd u1) 2 = shiftS (marksEven u2) B := by
    simp [pieceSet, hD]
  have hm3 : pieceSet (altEvenD w) (altEvenR w) (marksEven u2) (marksOdd u1) 3 = shiftS (marksEven u2) (S + B) := by
    simp [pieceSet, hD]
  have hm4 : pieceSet (altEvenD w) (altEvenR w) (marksEven u2) (marksOdd u1) 4 = shiftS (marksOdd u1) 0 := by
    simp [pieceSet, hD, hR]
  have hm5 : pieceSet (altEvenD w) (altEvenR w) (marksEven u2) (marksOdd u1) 5 = shiftS (marksOdd u1) (B + U + U + V) := by
    simp [pieceSet, hD, hR]
  refine hex_closed (altEvenD w) (altEvenR w) (tEvenSet u2) (tOddSet u1) (marksEven u2) (marksOdd u1) f
    (by simp [hD]) (by simp [hR]) (MarksIn.marksEven_sub u2) (MarksIn.marksOdd_sub u1) _ _ ?_ ?_ hcompat
    (B + U + U + V + (A - e₂)) A (B + e₁) (B + U + U + V + (B + e₁ - e₂)) ?_ ?_ ?_ ?_ x05 x14 x25 x34 hsum
  · intro z hz0 hz1
    rw [hd0] at hz0
    rw [hd1] at hz1
    exact dbl_const oQ (tEvenSet u2) S (p.num, -p.den) 0 (p.num, -p.den) A (c 0) (c 1) k (f 0) (f 1) hkS h0 h1
      (by simp) z hz0 hz1
  · intro z hz2 hz3
    rw [hd2] at hz2
    rw [hd3] at hz3
    exact dbl_const oQ (tEvenSet u2) S (p.num, -p.den) (p.num, -p.den) _ B (c 2) (c 3) k (f 2) (f 3) hkS h2 h3
      rfl z hz2 hz3
  · rw [hm1, hm5]
    exact ⟨mem_shift _ _ _ (U + V - e₂) cQD' (by rw [hSh]; abel), mem_shift _ _ _ (A - e₂) cPA' (by abel)⟩
  · rw [hm0, hm4]
    exact ⟨mem_shift _ _ _ 0 cQ0 (by abel), mem_shift _ _ _ A cPA (by abel)⟩
  · rw [hm2, hm4]
    exact ⟨mem_shift _ _ _ e₁ cQ1 (by abel), mem_shift _ _ _ (B + e₁) cPB1 (by abel)⟩
  · rw [hm3, hm5]
    exact ⟨mem_shift _ _ _ (U + V + e₁ - e₂) cQD (by rw [hSh]; abel), mem_shift _ _ _ (B + e₁ - e₂) cPB1' (by abel)⟩

/-- **Odd alternate child, `W_1` even.** -/
theorem altClosedPathOdd_ef (w u1 u2 : Word) (hph : phase w ≠ 1)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (oP oQ : ℤ × ℤ → ℤ) (c : ℕ → ℤ)
    (hcP : CornerDiffs oP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      (parentsAt w).odd.num (parentsAt w).odd.den)
    (hcQ : CornerDiffs oQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      (parentsAt w).even.num (parentsAt w).even.den)
    (hk : ∃ k : ℤ, ∀ x, x ∈ tOddSet u1 → x + shiftP w ∈ tOddSet u1 →
      oP (x + shiftP w) - oP x - dot2 (affS w) x = k)
    (hcompat : AltMixedCompatOdd w u1 u2 (placedAltOdd w oP oQ c)) :
    AltClosedPathOdd w u1 u2 (placedAltOdd w oP oQ c) := by
  obtain ⟨x05, x14, x25, x34⟩ := altExclOdd_ef w u1 u2 hph hp hq
  obtain ⟨hD, hR, hAf, hSh⟩ := altOdd_ef w hph
  obtain ⟨k, hk⟩ := hk
  obtain ⟨cP0, cP1, -, -, -, -, cPD, cPD'⟩ := corner_marks_odd u1
  obtain ⟨-, -, cQU', cQU, cQV1, cQV1', -, -⟩ := corner_marks_even u2
  rw [← hp] at cPD cPD'
  rw [← hq] at cQU' cQU cQV1 cQV1'
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p
  set B := texV2 p
  set U := texV1Even q
  set V := texV2 q
  set S := shiftP w with hSdef
  set f := placedAltOdd w oP oQ c with hfdef
  have h0 : IsPiece (f 0) oP U 0 (c 0) := fun z => by simp [hfdef, placedAltOdd, hD, hAf]
  have h1 : IsPiece (f 1) oP (S + U) (p.num, -p.den) (c 1) := fun z => by simp [hfdef, placedAltOdd, hD, hAf]
  have h2 : IsPiece (f 2) oP V (q.num, -q.den) (c 2) := fun z => by simp [hfdef, placedAltOdd, hD, hAf]
  have h3 : IsPiece (f 3) oP (S + V) ((q.num, -q.den) + (p.num, -p.den)) (c 3) := fun z => by
    simp [hfdef, placedAltOdd, hD, hAf]
  have h4 : IsPiece (f 4) oQ 0 0 (c 4) := fun z => by simp [hfdef, placedAltOdd, hR, hAf]
  have h5 : IsPiece (f 5) oQ (A + B + B + U) ((p.num, -p.den) + (p.num, -p.den)) (c 5) := fun z => by
    simp [hfdef, placedAltOdd, hR, hAf]
  have hv : StepVectors p.num p.den q.num q.den A B U V (p.num, -p.den) (q.num, -q.den) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hsum := ClosedPathAltSum.altOdd_even_first p.num p.den q.num q.den A B U V _ _ S hv hSh oP oQ f c k
    h0 h1 h2 h3 h4 h5 hcP hcQ
  have hkS : ∀ x, x ∈ tOddSet u1 → x + S ∈ tOddSet u1 → oP (x + S) - oP x - dot2 (p.num, -p.den) x = k := hk
  have hd0 : pieceSet (altOddD w) (altOddR w) (tOddSet u1) (tEvenSet u2) 0 = shiftS (tOddSet u1) U := by
    simp [pieceSet, hD]
  have hd1 : pieceSet (altOddD w) (altOddR w) (tOddSet u1) (tEvenSet u2) 1 = shiftS (tOddSet u1) (S + U) := by
    simp [pieceSet, hD]
  have hd2 : pieceSet (altOddD w) (altOddR w) (tOddSet u1) (tEvenSet u2) 2 = shiftS (tOddSet u1) V := by
    simp [pieceSet, hD]
  have hd3 : pieceSet (altOddD w) (altOddR w) (tOddSet u1) (tEvenSet u2) 3 = shiftS (tOddSet u1) (S + V) := by
    simp [pieceSet, hD]
  have hm0 : pieceSet (altOddD w) (altOddR w) (marksOdd u1) (marksEven u2) 0 = shiftS (marksOdd u1) U := by
    simp [pieceSet, hD]
  have hm1 : pieceSet (altOddD w) (altOddR w) (marksOdd u1) (marksEven u2) 1 = shiftS (marksOdd u1) (S + U) := by
    simp [pieceSet, hD]
  have hm2 : pieceSet (altOddD w) (altOddR w) (marksOdd u1) (marksEven u2) 2 = shiftS (marksOdd u1) V := by
    simp [pieceSet, hD]
  have hm3 : pieceSet (altOddD w) (altOddR w) (marksOdd u1) (marksEven u2) 3 = shiftS (marksOdd u1) (S + V) := by
    simp [pieceSet, hD]
  have hm4 : pieceSet (altOddD w) (altOddR w) (marksOdd u1) (marksEven u2) 4 = shiftS (marksEven u2) 0 := by
    simp [pieceSet, hD, hR]
  have hm5 : pieceSet (altOddD w) (altOddR w) (marksOdd u1) (marksEven u2) 5 = shiftS (marksEven u2) (A + B + B + U) := by
    simp [pieceSet, hD, hR]
  refine hex_closed (altOddD w) (altOddR w) (tOddSet u1) (tEvenSet u2) (marksOdd u1) (marksEven u2) f
    (by simp [hD]) (by simp [hR]) (MarksIn.marksOdd_sub u1) (MarksIn.marksEven_sub u2) _ _ ?_ ?_ hcompat
    (S + U + (A + B - e₂)) U (V + e₁) (S + V + (A + B + e₁ - e₂)) ?_ ?_ ?_ ?_ x05 x14 x25 x34 hsum
  · intro z hz0 hz1
    rw [hd0] at hz0
    rw [hd1] at hz1
    exact dbl_const oP (tOddSet u1) S (p.num, -p.den) 0 (p.num, -p.den) U (c 0) (c 1) k (f 0) (f 1) hkS h0 h1
      (by simp) z hz0 hz1
  · intro z hz2 hz3
    rw [hd2] at hz2
    rw [hd3] at hz3
    exact dbl_const oP (tOddSet u1) S (p.num, -p.den) (q.num, -q.den) _ V (c 2) (c 3) k (f 2) (f 3) hkS h2 h3
      rfl z hz2 hz3
  · rw [hm1, hm5]
    exact ⟨mem_shift _ _ _ (A + B - e₂) cPD' (by abel), mem_shift _ _ _ (U - e₂) cQU' (by rw [hSh]; abel)⟩
  · rw [hm0, hm4]
    exact ⟨mem_shift _ _ _ 0 cP0 (by abel), mem_shift _ _ _ U cQU (by abel)⟩
  · rw [hm2, hm4]
    exact ⟨mem_shift _ _ _ e₁ cP1 (by abel), mem_shift _ _ _ (V + e₁) cQV1 (by abel)⟩
  · rw [hm3, hm5]
    exact ⟨mem_shift _ _ _ (A + B + e₁ - e₂) cPD (by abel), mem_shift _ _ _ (V + e₁ - e₂) cQV1' (by rw [hSh]; abel)⟩

/-- **Odd alternate child, `W_1` odd.** -/
theorem altClosedPathOdd_of (w u1 u2 : Word) (hph : phase w = 1)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (oP oQ : ℤ × ℤ → ℤ) (c : ℕ → ℤ)
    (hcP : CornerDiffs oP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      (parentsAt w).odd.num (parentsAt w).odd.den)
    (hcQ : CornerDiffs oQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      (parentsAt w).even.num (parentsAt w).even.den)
    (hk : ∃ k : ℤ, ∀ x, x ∈ tOddSet u1 → x + shiftP w ∈ tOddSet u1 →
      oP (x + shiftP w) - oP x - dot2 (affS w) x = k)
    (hcompat : AltMixedCompatOdd w u1 u2 (placedAltOdd w oP oQ c)) :
    AltClosedPathOdd w u1 u2 (placedAltOdd w oP oQ c) := by
  obtain ⟨x05, x14, x25, x34⟩ := altExclOdd_of w u1 u2 hph hp hq
  obtain ⟨hD, hR, hAf, hSh⟩ := altOdd_of w hph
  obtain ⟨k, hk⟩ := hk
  obtain ⟨-, -, cPA', cPA, cPB1, cPB1', -, -⟩ := corner_marks_odd u1
  obtain ⟨cQ0, cQ1, -, -, -, -, cQD, cQD'⟩ := corner_marks_even u2
  rw [← hp] at cPA' cPA cPB1 cPB1'
  rw [← hq] at cQD cQD'
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p
  set B := texV2 p
  set U := texV1Even q
  set V := texV2 q
  set S := shiftP w with hSdef
  set f := placedAltOdd w oP oQ c with hfdef
  have h0 : IsPiece (f 0) oP 0 0 (c 0) := fun z => by simp [hfdef, placedAltOdd, hD, hAf]
  have h1 : IsPiece (f 1) oP (S + 0) (p.num, -p.den) (c 1) := fun z => by simp [hfdef, placedAltOdd, hD, hAf]
  have h2 : IsPiece (f 2) oP (U + V) (q.num, -q.den) (c 2) := fun z => by simp [hfdef, placedAltOdd, hD, hAf]
  have h3 : IsPiece (f 3) oP (S + (U + V)) ((q.num, -q.den) + (p.num, -p.den)) (c 3) := fun z => by
    simp [hfdef, placedAltOdd, hD, hAf]
  have h4 : IsPiece (f 4) oQ A 0 (c 4) := fun z => by simp [hfdef, placedAltOdd, hR, hAf]
  have h5 : IsPiece (f 5) oQ (B + B - U) ((p.num, -p.den) + (p.num, -p.den)) (c 5) := fun z => by
    simp [hfdef, placedAltOdd, hR, hAf]
  have hv : StepVectors p.num p.den q.num q.den A B U V (p.num, -p.den) (q.num, -q.den) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hsum := ClosedPathAltSum.altOdd_odd_first p.num p.den q.num q.den A B U V _ _ S hv hSh oP oQ f c k
    h0 h1 h2 h3 h4 h5 hcP hcQ
  have hkS : ∀ x, x ∈ tOddSet u1 → x + S ∈ tOddSet u1 → oP (x + S) - oP x - dot2 (p.num, -p.den) x = k := hk
  have hd0 : pieceSet (altOddD w) (altOddR w) (tOddSet u1) (tEvenSet u2) 0 = shiftS (tOddSet u1) 0 := by
    simp [pieceSet, hD]
  have hd1 : pieceSet (altOddD w) (altOddR w) (tOddSet u1) (tEvenSet u2) 1 = shiftS (tOddSet u1) (S + 0) := by
    simp [pieceSet, hD]
  have hd2 : pieceSet (altOddD w) (altOddR w) (tOddSet u1) (tEvenSet u2) 2 = shiftS (tOddSet u1) (U + V) := by
    simp [pieceSet, hD]
  have hd3 : pieceSet (altOddD w) (altOddR w) (tOddSet u1) (tEvenSet u2) 3 = shiftS (tOddSet u1) (S + (U + V)) := by
    simp [pieceSet, hD]
  have hm0 : pieceSet (altOddD w) (altOddR w) (marksOdd u1) (marksEven u2) 0 = shiftS (marksOdd u1) 0 := by
    simp [pieceSet, hD]
  have hm1 : pieceSet (altOddD w) (altOddR w) (marksOdd u1) (marksEven u2) 1 = shiftS (marksOdd u1) (S + 0) := by
    simp [pieceSet, hD]
  have hm2 : pieceSet (altOddD w) (altOddR w) (marksOdd u1) (marksEven u2) 2 = shiftS (marksOdd u1) (U + V) := by
    simp [pieceSet, hD]
  have hm3 : pieceSet (altOddD w) (altOddR w) (marksOdd u1) (marksEven u2) 3 = shiftS (marksOdd u1) (S + (U + V)) := by
    simp [pieceSet, hD]
  have hm4 : pieceSet (altOddD w) (altOddR w) (marksOdd u1) (marksEven u2) 4 = shiftS (marksEven u2) A := by
    simp [pieceSet, hD, hR]
  have hm5 : pieceSet (altOddD w) (altOddR w) (marksOdd u1) (marksEven u2) 5 = shiftS (marksEven u2) (B + B - U) := by
    simp [pieceSet, hD, hR]
  refine hex_closed (altOddD w) (altOddR w) (tOddSet u1) (tEvenSet u2) (marksOdd u1) (marksEven u2) f
    (by simp [hD]) (by simp [hR]) (MarksIn.marksOdd_sub u1) (MarksIn.marksEven_sub u2) _ _ ?_ ?_ hcompat
    (S + 0 + (B + e₁)) A (U + V + (A - e₂)) (S + (U + V) + (B + e₁ - e₂)) ?_ ?_ ?_ ?_ x05 x14 x25 x34 hsum
  · intro z hz0 hz1
    rw [hd0] at hz0
    rw [hd1] at hz1
    exact dbl_const oP (tOddSet u1) S (p.num, -p.den) 0 (p.num, -p.den) 0 (c 0) (c 1) k (f 0) (f 1) hkS h0 h1
      (by simp) z hz0 hz1
  · intro z hz2 hz3
    rw [hd2] at hz2
    rw [hd3] at hz3
    exact dbl_const oP (tOddSet u1) S (p.num, -p.den) (q.num, -q.den) _ (U + V) (c 2) (c 3) k (f 2) (f 3) hkS h2 h3
      rfl z hz2 hz3
  · rw [hm1, hm5]
    exact ⟨mem_shift _ _ _ (B + e₁) cPB1 (by abel), mem_shift _ _ _ e₁ cQ1 (by rw [hSh]; abel)⟩
  · rw [hm0, hm4]
    exact ⟨mem_shift _ _ _ A cPA (by abel), mem_shift _ _ _ 0 cQ0 (by abel)⟩
  · rw [hm2, hm4]
    exact ⟨mem_shift _ _ _ (A - e₂) cPA' (by abel), mem_shift _ _ _ (U + V - e₂) cQD' (by abel)⟩
  · rw [hm3, hm5]
    exact ⟨mem_shift _ _ _ (B + e₁ - e₂) cPB1' (by abel), mem_shift _ _ _ (U + V + e₁ - e₂) cQD (by rw [hSh]; abel)⟩

/-! ### Condition (C) for the six standard subtiles, both orientations -/

/-- **Condition (C) for the six standard subtiles of the odd alternate child**, for every word, from the respects of both
parents on their standard tiles, the compatibility of the doubled odd parent along `S_p`, and the local compatibility of the
mixed copies. -/
theorem altClosedPathOdd_all (w u1 u2 : Word) (hp : (parentsAt w).odd = fracOdd u1)
    (hq : (parentsAt w).even = fracEven u2) (oP oQ : ℤ × ℤ → ℤ) (c : ℕ → ℤ)
    (hRP : SurgicalWeak.RespectsAnchored (oddTile u1) (hWordOf u1 false) (vWordOf u1 false) oP)
    (hRQ : SurgicalWeak.RespectsAnchored (evenTile u2) (hWordOf u2 true) (vWordOf u2 true) oQ)
    (hk : ∃ k : ℤ, ∀ x, x ∈ tOddSet u1 → x + shiftP w ∈ tOddSet u1 →
      oP (x + shiftP w) - oP x - dot2 (affS w) x = k)
    (hcompat : AltMixedCompatOdd w u1 u2 (placedAltOdd w oP oQ c)) :
    AltClosedPathOdd w u1 u2 (placedAltOdd w oP oQ c) := by
  have hcP := ClosedPathStandard.cornerDiffs_odd u1 (oddTile u1) oP hRP
  have hcQ := ClosedPathStandard.cornerDiffs_even u2 (evenTile u2) oQ hRQ
  rw [← hp] at hcP
  rw [← hq] at hcQ
  by_cases hph : phase w = 1
  · exact altClosedPathOdd_of w u1 u2 hph hp hq oP oQ c hcP hcQ hk hcompat
  · exact altClosedPathOdd_ef w u1 u2 hph hp hq oP oQ c hcP hcQ hk hcompat

/-- **Condition (C) for the six standard subtiles of the even alternate child**, for every word, from the respects of both
parents on their standard tiles, the compatibility of the doubled even parent along `S_q`, and the local compatibility of the
mixed copies. -/
theorem altClosedPathEven_all (w u1 u2 : Word) (hp : (parentsAt w).odd = fracOdd u1)
    (hq : (parentsAt w).even = fracEven u2) (oP oQ : ℤ × ℤ → ℤ) (c : ℕ → ℤ)
    (hRP : SurgicalWeak.RespectsAnchored (oddTile u1) (hWordOf u1 false) (vWordOf u1 false) oP)
    (hRQ : SurgicalWeak.RespectsAnchored (evenTile u2) (hWordOf u2 true) (vWordOf u2 true) oQ)
    (hk : ∃ k : ℤ, ∀ x, x ∈ tEvenSet u2 → x + shiftQ w ∈ tEvenSet u2 →
      oQ (x + shiftQ w) - oQ x - dot2 (affS w) x = k)
    (hcompat : AltMixedCompatEven w u1 u2 (placedAltEven w oP oQ c)) :
    AltClosedPathEven w u1 u2 (placedAltEven w oP oQ c) := by
  have hcP := ClosedPathStandard.cornerDiffs_odd u1 (oddTile u1) oP hRP
  have hcQ := ClosedPathStandard.cornerDiffs_even u2 (evenTile u2) oQ hRQ
  rw [← hp] at hcP
  rw [← hq] at hcQ
  by_cases hph : phase w = 1
  · exact altClosedPathEven_of w u1 u2 hph hp hq oP oQ c hcP hcQ hk hcompat
  · exact altClosedPathEven_ef w u1 u2 hph hp hq oP oQ c hcP hcQ hk hcompat

end FLatticePaper.Tiles.ClosedPathAlt
