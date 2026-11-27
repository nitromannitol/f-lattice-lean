import FLatticePaper.Tiles.MixedPiecesInMarks

/-! The existence step of `lemma:tile-odometer-existence` (Step 1, the common extension), as a reduction.

Operator's notes, Section 7.2 (manuscript dbd159d): Step 1 deletes, from one of two subodometers, the overlap of two copies of the
same parent, other than the two copies of one doubled piece. The kept copy covers every deleted point. Writing `keptSet` for the
kept part of a copy, the glue needs only three inputs:

* `H1`: copies of different parents meet only inside their marks. This is claim (d), `MixedPiecesInMarks`; its cell derivation
  from the cell facts is `CellDerivation.common_point_in_strings`.
* `H2` (`MarksAgreeOdd`/`MarksAgreeEven`): the subodometers of copies of different parents agree on the marks of both copies.
* `H3`, restricted to doubled pairs (`DoubledAgreeOdd`/`DoubledAgreeEven`, (c)): the two copies of one doubled piece agree on
  their whole overlap.

`H2` and `H3` are stated for the subodometers with additive piece constants `κ`, and the existence of constants making both hold is
one hypothesis. This existence is condition (C), the offset constants summing to zero around every closed path; it is not proved here.

No agreement is assumed for the other same-parent pairs. For them the deletion makes the kept parts disjoint (`kept_disjoint`). -/

namespace FLatticePaper.Tiles.ChildGlue

/-- Generic gluing of full copies (used by `ChildAssembly`). -/
theorem glue_full (n : ℕ) (D M : ℕ → Set (ℤ × ℤ)) (flag : ℕ → Bool) (f : ℕ → ℤ × ℤ → ℤ)
    (H1 : ∀ i j, i < n → j < n → flag i ≠ flag j → ∀ z, z ∈ D i → z ∈ D j → z ∈ M i ∧ z ∈ M j)
    (H2 : ∀ i j, i < n → j < n → flag i ≠ flag j → ∀ z, z ∈ M i → z ∈ M j → f i z = f j z)
    (H3 : ∀ i j, i < n → j < n → i ≠ j → flag i = flag j → ∀ z, z ∈ D i → z ∈ D j → f i z = f j z) :
    ∃ g : ℤ × ℤ → ℤ, ∀ i, i < n → ∀ z ∈ D i, g z = f i z := by
  classical
  refine ⟨fun z => if h : ∃ i, i < n ∧ z ∈ D i then f (Classical.choose h) z else 0, ?_⟩
  intro i hi z hz
  have h : ∃ i, i < n ∧ z ∈ D i := ⟨i, hi, hz⟩
  dsimp only
  rw [dif_pos h]
  obtain ⟨hkn, hzk⟩ := Classical.choose_spec h
  by_cases hkeq : Classical.choose h = i
  · rw [hkeq]
  by_cases hfl : flag (Classical.choose h) = flag i
  · exact H3 _ i hkn hi hkeq hfl z hzk hz
  · obtain ⟨hMk, hMi⟩ := H1 _ i hkn hi hfl z hzk hz
    exact H2 _ i hkn hi hfl z hMk hMi

/-- Generic gluing of kept parts: `K i ⊆ D i`, copies of different flags agree on their marks, and kept parts of one flag agree. -/
theorem glue_sets (n : ℕ) (K D M : ℕ → Set (ℤ × ℤ)) (flag : ℕ → Bool) (f : ℕ → ℤ × ℤ → ℤ)
    (hKD : ∀ i, K i ⊆ D i)
    (H1 : ∀ i j, i < n → j < n → flag i ≠ flag j → ∀ z, z ∈ D i → z ∈ D j → z ∈ M i ∧ z ∈ M j)
    (H2 : ∀ i j, i < n → j < n → flag i ≠ flag j → ∀ z, z ∈ M i → z ∈ M j → f i z = f j z)
    (H3 : ∀ i j, i < n → j < n → i ≠ j → flag i = flag j → ∀ z, z ∈ K i → z ∈ K j → f i z = f j z) :
    ∃ g : ℤ × ℤ → ℤ, ∀ i, i < n → ∀ z ∈ K i, g z = f i z := by
  classical
  refine ⟨fun z => if h : ∃ i, i < n ∧ z ∈ K i then f (Classical.choose h) z else 0, ?_⟩
  intro i hi z hz
  have h : ∃ i, i < n ∧ z ∈ K i := ⟨i, hi, hz⟩
  dsimp only
  rw [dif_pos h]
  obtain ⟨hkn, hzk⟩ := Classical.choose_spec h
  by_cases hkeq : Classical.choose h = i
  · rw [hkeq]
  by_cases hfl : flag (Classical.choose h) = flag i
  · exact H3 _ i hkn hi hkeq hfl z hzk hz
  · obtain ⟨hMk, hMi⟩ := H1 _ i hkn hi hfl z (hKD _ hzk) (hKD i hz)
    exact H2 _ i hkn hi hfl z hMk hMi

/-- The kept part of copy `i`: its copy minus the earlier copies `j` of the same parent, except the partner `j` with `Dbl j i`
(the two copies of one doubled piece). -/
def keptSet (D : ℕ → Set (ℤ × ℤ)) (flag : ℕ → Bool) (Dbl : ℕ → ℕ → Prop) (i : ℕ) : Set (ℤ × ℤ) :=
  {z | z ∈ D i ∧ ¬ ∃ j, j < i ∧ flag j = flag i ∧ ¬ Dbl j i ∧ z ∈ D j}

theorem keptSet_subset (D : ℕ → Set (ℤ × ℤ)) (flag : ℕ → Bool) (Dbl : ℕ → ℕ → Prop) (i : ℕ) :
    keptSet D flag Dbl i ⊆ D i :=
  fun _ hz => hz.1

/-- Every point of a copy lies in the kept part of some copy with index at most its own: the least such copy keeps it. -/
theorem kept_cover (D : ℕ → Set (ℤ × ℤ)) (flag : ℕ → Bool) (Dbl : ℕ → ℕ → Prop) (i : ℕ) :
    ∀ z ∈ D i, ∃ k ≤ i, z ∈ keptSet D flag Dbl k := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro z hz
    by_cases h : ∃ j, j < i ∧ flag j = flag i ∧ ¬ Dbl j i ∧ z ∈ D j
    · obtain ⟨j, hji, -, -, hzj⟩ := h
      obtain ⟨k, hk, hzk⟩ := ih j hji z hzj
      exact ⟨k, by omega, hzk⟩
    · exact ⟨i, le_rfl, ⟨hz, h⟩⟩

/-- Two copies of one parent, the earlier not a doubled partner of the later, have disjoint kept parts. -/
theorem kept_disjoint (D : ℕ → Set (ℤ × ℤ)) (flag : ℕ → Bool) (Dbl : ℕ → ℕ → Prop) {i j : ℕ} (hij : i < j)
    (hfl : flag i = flag j) (hnd : ¬ Dbl i j) (z : ℤ × ℤ) (hzi : z ∈ keptSet D flag Dbl i)
    (hzj : z ∈ keptSet D flag Dbl j) : False :=
  hzj.2 ⟨i, hij, hfl, hnd, hzi.1⟩

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
open FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.SiteInduction
open FLatticePaper.Tiles.MixedPieces

/-- Piece `i` of a child: a copy of `T1` at the `i`-th offset of `P` when `i < P.length`, otherwise a copy of `T2` at an
offset of `Q`. -/
def pieceSet (P Q : List (ℤ × ℤ)) (T1 T2 : Set (ℤ × ℤ)) (i : ℕ) : Set (ℤ × ℤ) :=
  if i < P.length then shiftS T1 (P.getD i 0) else shiftS T2 (Q.getD (i - P.length) 0)

/-- The parent of piece `i`: `false` for a copy of `T1`, `true` for a copy of `T2`. -/
def pieceFlag (P : List (ℤ × ℤ)) (i : ℕ) : Bool := decide (P.length ≤ i)

/-- The mixed-piece claim, in the form of `pieceSet`: copies of different parents meeting at `z` have `z` in both marks. -/
theorem copies_mixed (P Q : List (ℤ × ℤ)) (T1 T2 M1 M2 : Set (ℤ × ℤ))
    (hmix : ∀ a ∈ P, ∀ b ∈ Q, ∀ z : ℤ × ℤ, z ∈ shiftS T1 a → z ∈ shiftS T2 b →
      z ∈ shiftS M1 a ∧ z ∈ shiftS M2 b) :
    ∀ i j, i < P.length + Q.length → j < P.length + Q.length → pieceFlag P i ≠ pieceFlag P j →
      ∀ z, z ∈ pieceSet P Q T1 T2 i → z ∈ pieceSet P Q T1 T2 j →
        z ∈ pieceSet P Q M1 M2 i ∧ z ∈ pieceSet P Q M1 M2 j := by
  have memP : ∀ i, i < P.length → P.getD i 0 ∈ P := fun i hi => by
    have e : P.getD i 0 = P[i] := by simp [List.getD_eq_getElem?_getD, hi]
    rw [e]
    exact List.getElem_mem hi
  have memQ : ∀ i, i < P.length + Q.length → P.length ≤ i → Q.getD (i - P.length) 0 ∈ Q := fun i hi hle => by
    have hlt : i - P.length < Q.length := by omega
    have e : Q.getD (i - P.length) 0 = Q[i - P.length] := by simp [List.getD_eq_getElem?_getD, hlt]
    rw [e]
    exact List.getElem_mem hlt
  intro i j hi hj hfl z hzi hzj
  by_cases hiP : i < P.length <;> by_cases hjP : j < P.length
  · have h1 : ¬ P.length ≤ i := not_le.mpr hiP
    have h2 : ¬ P.length ≤ j := not_le.mpr hjP
    simp [pieceFlag, h1, h2] at hfl
  · have hzi' : z ∈ shiftS T1 (P.getD i 0) := by simpa [pieceSet, hiP] using hzi
    have hzj' : z ∈ shiftS T2 (Q.getD (j - P.length) 0) := by
      have : ¬ j < P.length := hjP
      simpa [pieceSet, this] using hzj
    obtain ⟨h1, h2⟩ := hmix _ (memP i hiP) _ (memQ j hj (not_lt.mp hjP)) z hzi' hzj'
    exact ⟨by simpa [pieceSet, hiP] using h1, by simpa [pieceSet, hjP] using h2⟩
  · have hzj' : z ∈ shiftS T1 (P.getD j 0) := by simpa [pieceSet, hjP] using hzj
    have hzi' : z ∈ shiftS T2 (Q.getD (i - P.length) 0) := by
      simpa [pieceSet, hiP] using hzi
    obtain ⟨h1, h2⟩ := hmix _ (memP j hjP) _ (memQ i hi (not_lt.mp hiP)) z hzj' hzi'
    exact ⟨by simpa [pieceSet, hiP] using h2, by simpa [pieceSet, hjP] using h1⟩
  · have h1 : P.length ≤ i := not_lt.mp hiP
    have h2 : P.length ≤ j := not_lt.mp hjP
    simp [pieceFlag, h1, h2] at hfl

/-- The glue of the kept parts of the copies of two registers, with the mixed-piece claim `hmix` (claim (d)), the mixed agreement
on marks `hagree` (`H2`) and the agreement of the two copies of a doubled piece `hdbl` (`H3`, (c)). -/
theorem glue_kept_pieces (P Q : List (ℤ × ℤ)) (T1 T2 M1 M2 : Set (ℤ × ℤ)) (Dbl : ℕ → ℕ → Prop) (f : ℕ → ℤ × ℤ → ℤ)
    (hmix : ∀ a ∈ P, ∀ b ∈ Q, ∀ z : ℤ × ℤ, z ∈ shiftS T1 a → z ∈ shiftS T2 b →
      z ∈ shiftS M1 a ∧ z ∈ shiftS M2 b)
    (hagree : ∀ i j, i < P.length + Q.length → j < P.length + Q.length → pieceFlag P i ≠ pieceFlag P j →
      ∀ z, z ∈ pieceSet P Q M1 M2 i → z ∈ pieceSet P Q M1 M2 j → f i z = f j z)
    (hdbl : ∀ i j, i < P.length + Q.length → j < P.length + Q.length → i < j → pieceFlag P i = pieceFlag P j →
      Dbl i j → ∀ z, z ∈ pieceSet P Q T1 T2 i → z ∈ pieceSet P Q T1 T2 j → f i z = f j z) :
    ∃ g : ℤ × ℤ → ℤ, ∀ i, i < P.length + Q.length →
      ∀ z ∈ keptSet (pieceSet P Q T1 T2) (pieceFlag P) Dbl i, g z = f i z := by
  refine glue_sets (P.length + Q.length) (keptSet (pieceSet P Q T1 T2) (pieceFlag P) Dbl)
    (pieceSet P Q T1 T2) (pieceSet P Q M1 M2) (pieceFlag P) f
    (fun i => keptSet_subset _ _ _ i)
    (copies_mixed P Q T1 T2 M1 M2 hmix) hagree ?_
  intro i j hi hj hij hfl z hzi hzj
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · by_cases hd : Dbl i j
    · exact hdbl i j hi hj hlt hfl hd z hzi.1 hzj.1
    · exact (kept_disjoint _ _ Dbl hlt hfl hd z hzi hzj).elim
  · by_cases hd : Dbl j i
    · exact (hdbl j i hj hi hlt hfl.symm hd z hzj.1 hzi.1).symm
    · exact (kept_disjoint _ _ Dbl hlt hfl.symm hd z hzj hzi).elim

/-- The glue of kept parts for an arbitrary family: copies of different flags agree on their marks (`H1`, `H2`), and the two
copies of a doubled pair agree on their whole overlap (`hdbl`, (c)). Every other same-parent pair has disjoint kept parts. -/
theorem glue_kept_gen (n : ℕ) (D M : ℕ → Set (ℤ × ℤ)) (flag : ℕ → Bool) (Dbl : ℕ → ℕ → Prop) (f : ℕ → ℤ × ℤ → ℤ)
    (H1 : ∀ i j, i < n → j < n → flag i ≠ flag j → ∀ z, z ∈ D i → z ∈ D j → z ∈ M i ∧ z ∈ M j)
    (H2 : ∀ i j, i < n → j < n → flag i ≠ flag j → ∀ z, z ∈ M i → z ∈ M j → f i z = f j z)
    (hdbl : ∀ i j, i < n → j < n → i < j → flag i = flag j → Dbl i j → ∀ z, z ∈ D i → z ∈ D j → f i z = f j z) :
    ∃ g : ℤ × ℤ → ℤ, ∀ i, i < n → ∀ z ∈ keptSet D flag Dbl i, g z = f i z := by
  refine glue_sets n (keptSet D flag Dbl) D M flag f (fun i => keptSet_subset D flag Dbl i) H1 H2 ?_
  intro i j hi hj hij hfl z hzi hzj
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · by_cases hd : Dbl i j
    · exact hdbl i j hi hj hlt hfl hd z hzi.1 hzj.1
    · exact (kept_disjoint D flag Dbl hlt hfl hd z hzi hzj).elim
  · by_cases hd : Dbl j i
    · exact (hdbl j i hj hi hlt hfl.symm hd z hzj.1 hzi.1).symm
    · exact (kept_disjoint D flag Dbl hlt hfl.symm hd z hzj hzi).elim

/-- The pieces of the odd child of `w`. -/
abbrev oddP (w : Word) : List (ℤ × ℤ) := pOffsetsOdd (phase w == 1) (parentsAt w).odd (parentsAt w).even
abbrev oddQ (w : Word) : List (ℤ × ℤ) := qOffsetsOdd (phase w == 1) (parentsAt w).odd (parentsAt w).even
/-- The pieces of the even child of `w`. -/
abbrev evenP (w : Word) : List (ℤ × ℤ) := pOffsetsEven (phase w == 1) (parentsAt w).odd (parentsAt w).even
abbrev evenQ (w : Word) : List (ℤ × ℤ) := qOffsetsEven (phase w == 1) (parentsAt w).odd (parentsAt w).even

/-- The tiles of the registers, as site sets. -/
abbrev tOddSet (u : Word) : Set (ℤ × ℤ) := ((oddTile u : Finset (ℤ × ℤ)) : Set (ℤ × ℤ))
abbrev tEvenSet (u : Word) : Set (ℤ × ℤ) := ((evenTile u : Finset (ℤ × ℤ)) : Set (ℤ × ℤ))

/-- Input `H2`, odd child: the subodometers of two mixed copies agree on the marks of both copies. -/
def MarksAgreeOdd (w : Word) (u1 u2 : Word) (f : ℕ → ℤ × ℤ → ℤ) : Prop :=
  ∀ i j, i < (oddP w).length + (oddQ w).length → j < (oddP w).length + (oddQ w).length →
    pieceFlag (oddP w) i ≠ pieceFlag (oddP w) j →
    ∀ z, z ∈ pieceSet (oddP w) (oddQ w) (marksOdd u1) (marksEven u2) i →
      z ∈ pieceSet (oddP w) (oddQ w) (marksOdd u1) (marksEven u2) j → f i z = f j z

/-- Input `H2`, even child, same content. -/
def MarksAgreeEven (w : Word) (u1 u2 : Word) (f : ℕ → ℤ × ℤ → ℤ) : Prop :=
  ∀ i j, i < (evenP w).length + (evenQ w).length → j < (evenP w).length + (evenQ w).length →
    pieceFlag (evenP w) i ≠ pieceFlag (evenP w) j →
    ∀ z, z ∈ pieceSet (evenP w) (evenQ w) (marksOdd u1) (marksEven u2) i →
      z ∈ pieceSet (evenP w) (evenQ w) (marksOdd u1) (marksEven u2) j → f i z = f j z

/-- Input `H3` (c), odd child: the two copies of a doubled pair `Dbl i j` agree on their whole overlap. Only doubled pairs. -/
def DoubledAgreeOdd (w : Word) (u1 u2 : Word) (Dbl : ℕ → ℕ → Prop) (f : ℕ → ℤ × ℤ → ℤ) : Prop :=
  ∀ i j, i < (oddP w).length + (oddQ w).length → j < (oddP w).length + (oddQ w).length → i < j →
    pieceFlag (oddP w) i = pieceFlag (oddP w) j → Dbl i j →
    ∀ z, z ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) i →
      z ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) j → f i z = f j z

/-- Input `H3` (c), even child, same content. -/
def DoubledAgreeEven (w : Word) (u1 u2 : Word) (Dbl : ℕ → ℕ → Prop) (f : ℕ → ℤ × ℤ → ℤ) : Prop :=
  ∀ i j, i < (evenP w).length + (evenQ w).length → j < (evenP w).length + (evenQ w).length → i < j →
    pieceFlag (evenP w) i = pieceFlag (evenP w) j → Dbl i j →
    ∀ z, z ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) i →
      z ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) j → f i z = f j z

/-- The doubled pairs of the odd child: `OddNode` doubles the even register `q` with shift `v_{q,1}` (`texV1Even`), so the copies
`i`, `i + 1` of the even register are the plus and minus partners, for `i` the first or the third of its copies. -/
def dblOdd (w : Word) (i j : ℕ) : Prop :=
  j = i + 1 ∧ (i = (oddP w).length ∨ i = (oddP w).length + 2)

/-- The doubled pairs of the even child: `EvenNode` doubles the odd register `p` with shift `v_{p,2}` (`texV2`), so the copies
`0, 1` and `2, 3` of the odd register are the partners. -/
def dblEven (i j : ℕ) : Prop :=
  j = i + 1 ∧ (i = 0 ∨ i = 2)

/-- **Condition (C)** of the existence step (operator's notes, S7_FIXES.md section 8), odd child: the offset constants sum to zero
around every closed path of overlapping subodometers. In the existential form used here: there are piece constants `κ` such
that the subodometers `f0 i z + κ i` agree on the marks (`MarksAgreeOdd`) and the two copies of each doubled piece agree on their
overlap (`DoubledAgreeOdd`, (c)). The constants exist after the Step 1 deletion (237/237 uncorrected and 116/116 corrected children,
words up to length 5); the paper gives no proof, so (C) is an input. -/
def ClosedPathOdd (w : Word) (u1 u2 : Word) (f0 : ℕ → ℤ × ℤ → ℤ) : Prop :=
  ∃ κ : ℕ → ℤ, MarksAgreeOdd w u1 u2 (fun i z => f0 i z + κ i) ∧
    DoubledAgreeOdd w u1 u2 (dblOdd w) (fun i z => f0 i z + κ i)

/-- Condition (C), even child (same content as `ClosedPathOdd`). -/
def ClosedPathEven (w : Word) (u1 u2 : Word) (f0 : ℕ → ℤ × ℤ → ℤ) : Prop :=
  ∃ κ : ℕ → ℤ, MarksAgreeEven w u1 u2 (fun i z => f0 i z + κ i) ∧
    DoubledAgreeEven w u1 u2 dblEven (fun i z => f0 i z + κ i)

/-- **The existence assembly for the odd child.** Conditional on (d) `MixedPiecesInMarksOdd w`, and on the existence of piece
constants `κ` (condition (C)) making both `H2` and `H3` hold for the subodometers `f0 i z + κ i`. The glue is
defined on the kept parts, which cover every point of the child. -/
theorem odd_child_glue (w u1 u2 : Word)
    (hT1 : (stateAt w).tOdd = oddTile u1) (hT2 : (stateAt w).tEven = evenTile u2)
    (hd : MixedPiecesInMarksOdd w) (f0 : ℕ → ℤ × ℤ → ℤ) (hC : ClosedPathOdd w u1 u2 f0) :
    ∃ κ : ℕ → ℤ, ∃ g : ℤ × ℤ → ℤ, ∀ i, i < (oddP w).length + (oddQ w).length →
      ∀ z ∈ keptSet (pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2)) (pieceFlag (oddP w)) (dblOdd w) i,
        g z = f0 i z + κ i := by
  obtain ⟨κ, hM, hD⟩ := hC
  obtain ⟨g, hg⟩ := glue_kept_pieces (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) (marksOdd u1) (marksEven u2) (dblOdd w)
    (fun i z => f0 i z + κ i) (fun a ha b hb z h1 h2 => hd u1 u2 hT1 hT2 a ha b hb z h1 h2) hM hD
  exact ⟨κ, g, hg⟩

/-- **The existence assembly for the even child**, conditional in the same way. -/
theorem even_child_glue (w u1 u2 : Word)
    (hT1 : (stateAt w).tOdd = oddTile u1) (hT2 : (stateAt w).tEven = evenTile u2)
    (hd : MixedPiecesInMarksEven w) (f0 : ℕ → ℤ × ℤ → ℤ) (hC : ClosedPathEven w u1 u2 f0) :
    ∃ κ : ℕ → ℤ, ∃ g : ℤ × ℤ → ℤ, ∀ i, i < (evenP w).length + (evenQ w).length →
      ∀ z ∈ keptSet (pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2)) (pieceFlag (evenP w)) dblEven i,
        g z = f0 i z + κ i := by
  obtain ⟨κ, hM, hD⟩ := hC
  obtain ⟨g, hg⟩ := glue_kept_pieces (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) (marksOdd u1) (marksEven u2) dblEven
    (fun i z => f0 i z + κ i) (fun a ha b hb z h1 h2 => hd u1 u2 hT1 hT2 a ha b hb z h1 h2) hM hD
  exact ⟨κ, g, hg⟩

end FLatticePaper.Tiles.ChildGlue
