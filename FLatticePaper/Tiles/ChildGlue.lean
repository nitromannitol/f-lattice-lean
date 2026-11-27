import FLatticePaper.Tiles.MixedPieces

/-! The existence step of `lemma:tile-odometer-existence` (Step 1, the common extension), as a reduction, with full copies.

The operator's reading (manuscript 80eec5b): the two copies of one parent agree on their whole overlap, so the glued odometer
restricts to every FULL copy. The three inputs of the glue are:

* `H1` (`MixedPiecesInMarks`, claim (d), OPEN): copies of different parents meet only inside their marks;
* `H2` (`MarksAgreeOdd`/`MarksAgreeEven`, OPEN): the subodometers of copies of different parents agree on the marks of both.
  This is `lemma:stacked_zero_one_string` for the interface, which is Moreover + (a) + (b) (the Moreover's first-odometer
  factors match: equal vertical, `a_{p,2}` horizontal);
* `H3` (`SameAgreeOdd`/`SameAgreeEven`, OPEN): copies of one parent agree on their whole overlap. This is (c) of the
  inductive hypothesis at the lower depth (the plus and minus copies of a doubled parent are lattice adjacent).

Given these, one function restricts to every full copy. -/

namespace FLatticePaper.Tiles.ChildGlue

/-- Generic gluing of full copies. -/
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

/-- The glue of the copies of two registers, with the three inputs `hmix` (claim (d)), `hagree` (mixed agreement on marks)
and `hsame` (same-parent agreement on the whole overlap). -/
theorem glue_copies (P Q : List (ℤ × ℤ)) (T1 T2 M1 M2 : Set (ℤ × ℤ)) (f : ℕ → ℤ × ℤ → ℤ)
    (hmix : ∀ a ∈ P, ∀ b ∈ Q, ∀ z : ℤ × ℤ, z ∈ shiftS T1 a → z ∈ shiftS T2 b →
      z ∈ shiftS M1 a ∧ z ∈ shiftS M2 b)
    (hagree : ∀ i j, i < P.length + Q.length → j < P.length + Q.length → pieceFlag P i ≠ pieceFlag P j →
      ∀ z, z ∈ pieceSet P Q M1 M2 i → z ∈ pieceSet P Q M1 M2 j → f i z = f j z)
    (hsame : ∀ i j, i < P.length + Q.length → j < P.length + Q.length → i ≠ j → pieceFlag P i = pieceFlag P j →
      ∀ z, z ∈ pieceSet P Q T1 T2 i → z ∈ pieceSet P Q T1 T2 j → f i z = f j z) :
    ∃ g : ℤ × ℤ → ℤ, ∀ i, i < P.length + Q.length → ∀ z ∈ pieceSet P Q T1 T2 i, g z = f i z :=
  glue_full (P.length + Q.length) (pieceSet P Q T1 T2) (pieceSet P Q M1 M2) (pieceFlag P) f
    (copies_mixed P Q T1 T2 M1 M2 hmix) hagree hsame

/-- The pieces of the odd child of `w`. -/
abbrev oddP (w : Word) : List (ℤ × ℤ) := pOffsetsOdd (phase w == 1) (parentsAt w).odd (parentsAt w).even
abbrev oddQ (w : Word) : List (ℤ × ℤ) := qOffsetsOdd (phase w == 1) (parentsAt w).odd (parentsAt w).even
/-- The pieces of the even child of `w`. -/
abbrev evenP (w : Word) : List (ℤ × ℤ) := pOffsetsEven (phase w == 1) (parentsAt w).odd (parentsAt w).even
abbrev evenQ (w : Word) : List (ℤ × ℤ) := qOffsetsEven (phase w == 1) (parentsAt w).odd (parentsAt w).even

/-- The tiles of the registers, as site sets. -/
abbrev tOddSet (u : Word) : Set (ℤ × ℤ) := ((oddTile u : Finset (ℤ × ℤ)) : Set (ℤ × ℤ))
abbrev tEvenSet (u : Word) : Set (ℤ × ℤ) := ((evenTile u : Finset (ℤ × ℤ)) : Set (ℤ × ℤ))

/-- Input `H2`, odd child (OPEN): the subodometers of two mixed copies agree on the marks of both copies. It is the stacked
common extension of `lemma:stacked_zero_one_string` for the interface, that is Moreover + (a) + (b). -/
def MarksAgreeOdd (w u1 u2 : Word) (f : ℕ → ℤ × ℤ → ℤ) : Prop :=
  ∀ i j, i < (oddP w).length + (oddQ w).length → j < (oddP w).length + (oddQ w).length →
    pieceFlag (oddP w) i ≠ pieceFlag (oddP w) j →
    ∀ z, z ∈ pieceSet (oddP w) (oddQ w) (marksOdd u1) (marksEven u2) i →
      z ∈ pieceSet (oddP w) (oddQ w) (marksOdd u1) (marksEven u2) j → f i z = f j z

/-- Input `H2`, even child (OPEN), same content as `MarksAgreeOdd`. -/
def MarksAgreeEven (w u1 u2 : Word) (f : ℕ → ℤ × ℤ → ℤ) : Prop :=
  ∀ i j, i < (evenP w).length + (evenQ w).length → j < (evenP w).length + (evenQ w).length →
    pieceFlag (evenP w) i ≠ pieceFlag (evenP w) j →
    ∀ z, z ∈ pieceSet (evenP w) (evenQ w) (marksOdd u1) (marksEven u2) i →
      z ∈ pieceSet (evenP w) (evenQ w) (marksOdd u1) (marksEven u2) j → f i z = f j z

/-- Input `H3`, odd child (OPEN): copies of one parent agree on their whole overlap (the operator's reading of (c) at the
lower depth, for the lattice adjacent copies of a doubled parent). -/
def SameAgreeOdd (w u1 u2 : Word) (f : ℕ → ℤ × ℤ → ℤ) : Prop :=
  ∀ i j, i < (oddP w).length + (oddQ w).length → j < (oddP w).length + (oddQ w).length → i ≠ j →
    pieceFlag (oddP w) i = pieceFlag (oddP w) j →
    ∀ z, z ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) i →
      z ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) j → f i z = f j z

/-- Input `H3`, even child (OPEN), same content as `SameAgreeOdd`. -/
def SameAgreeEven (w u1 u2 : Word) (f : ℕ → ℤ × ℤ → ℤ) : Prop :=
  ∀ i j, i < (evenP w).length + (evenQ w).length → j < (evenP w).length + (evenQ w).length → i ≠ j →
    pieceFlag (evenP w) i = pieceFlag (evenP w) j →
    ∀ z, z ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) i →
      z ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) j → f i z = f j z

/-- **The existence assembly for the odd child**, conditional on (d) `MixedPiecesInMarksOdd w` and on the two agreement
inputs. One function restricts to every full copy. -/
theorem odd_child_glue (w u1 u2 : Word)
    (hT1 : (stateAt w).tOdd = oddTile u1) (hT2 : (stateAt w).tEven = evenTile u2)
    (hd : MixedPiecesInMarksOdd w) (f : ℕ → ℤ × ℤ → ℤ)
    (hagree : MarksAgreeOdd w u1 u2 f) (hsame : SameAgreeOdd w u1 u2 f) :
    ∃ g : ℤ × ℤ → ℤ, ∀ i, i < (oddP w).length + (oddQ w).length →
      ∀ z ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) i, g z = f i z :=
  glue_copies (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) (marksOdd u1) (marksEven u2) f
    (fun a ha b hb z h1 h2 => hd u1 u2 hT1 hT2 a ha b hb z h1 h2) hagree hsame

/-- **The existence assembly for the even child**, conditional in the same way. -/
theorem even_child_glue (w u1 u2 : Word)
    (hT1 : (stateAt w).tOdd = oddTile u1) (hT2 : (stateAt w).tEven = evenTile u2)
    (hd : MixedPiecesInMarksEven w) (f : ℕ → ℤ × ℤ → ℤ)
    (hagree : MarksAgreeEven w u1 u2 f) (hsame : SameAgreeEven w u1 u2 f) :
    ∃ g : ℤ × ℤ → ℤ, ∀ i, i < (evenP w).length + (evenQ w).length →
      ∀ z ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) i, g z = f i z :=
  glue_copies (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) (marksOdd u1) (marksEven u2) f
    (fun a ha b hb z h1 h2 => hd u1 u2 hT1 hT2 a ha b hb z h1 h2) hagree hsame

end FLatticePaper.Tiles.ChildGlue
