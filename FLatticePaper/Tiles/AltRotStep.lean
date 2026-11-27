import FLatticePaper.Tiles.SurgicalAltTiles
import FLatticePaper.Tiles.AltRotBase
import FLatticePaper.Tiles.BottomEdges

/-! Item (1) of `lemma:alternate_tile_properties`, rotation, for every word: the rotation of the alternate tile `T̂(n/d)` is the
alternate tile `T̂(R(n/d))` up to an explicit translation (`altRot`), for the alternate tiles of `def:alternate_tiles` with the
base alternates of `prop:base_cases` (`PaperAltBase.paperAltBaseTiles`, with `c(T̂_{1/d}) = (0,0)`).

The text says the proof is that of `lemma:standard_boundary_word_recursion`. It is the same induction, with one difference: the
translation is not `t(n/d) = tF` of the standard tiles. The alternate tile is placed by the text's convention `c(T̂) = c` of
its piece at offset `0` (`T^{ds}(p_1)^+` or `T(q_1)^+` for `T̂(p_0)`, `T(p_1)^+` or `T^{ds}(q_1)^{+}` for `T̂(q_0)`), and the
rotation carries every piece of the alternate decomposition of `w` to a piece of the alternate decomposition of the swapped word,
the alternate parent piece to the alternate parent piece. So the translation is the offset of the image of the piece at `0`
minus `tF` of its parent, with the doubling shift in two of the four cases:
* `tauShort p q = (d₁ + n₁ + d₂ + n₂, d₁ - n₁ + d₂ - n₂ - 1)`, which is `-tF` of the child `p₀` of the parents;
* `tauLong p q = (d₂ + 2d₁ + 2n₁, 2d₂ - n₂ + 2d₁ - 2n₁ - 1)`.
The odd child uses `tauLong` when `W₁` is odd and `tauShort` otherwise, the even child the other way round (`tauOdd`,
`tauEven`). At the base words these are the translations of the four base identities of `AltRotBase`.

The induction is on the word, as `good_and_rot`: the standard pieces use the register identities of the standard tiles
(`Standard.good_and_rot`), and the alternate parent piece, present when its register is the child of the prefix `u` of
`w = u ++ [x]`, uses the statement at `u`. Each step is a linear identity in the entries of the parents. -/

namespace FLatticePaper.Tiles.AltRotStep

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (Tile shift rot mem_shift rot_shift shift_shift shift_union rot_union stateAt swapW
  IsBase tF tV rotate_eq_of_odd rotate_eq_of_even)
open FLatticePaper.Tiles.SurgicalDict (doubled altShifts AltP0Piece AltQ0Piece)
open FLatticePaper.Tiles.SurgicalAlt (coeffOff altP0Coeff altQ0Coeff altQ1Coeff altP1Coeff altTypeOf AltCoeff)
open FLatticePaper.Tiles.SurgicalAltTiles

/-! ### Rotations of shifted and doubled tiles -/

theorem shift_zero (T : Tile) : shift T 0 = T := by
  ext x
  simp [mem_shift]

theorem rot_doubled (T : Tile) (S : Site) : rot (doubled T S) = doubled (rot T) (mulI S) := by
  unfold doubled
  rw [rot_union, rot_shift]

theorem shift_doubled (T : Tile) (S v : Site) : shift (doubled T S) v = doubled (shift T v) S := by
  unfold doubled
  rw [shift_union, shift_shift, shift_shift, add_comm]

theorem doubled_neg (T : Tile) (S : Site) : doubled T (-S) = shift (doubled T S) (-S) := by
  unfold doubled
  rw [shift_union, shift_shift, add_neg_cancel, shift_zero]
  ext x
  simp only [Finset.mem_union]
  tauto

theorem rot_empty : rot (∅ : Tile) = ∅ := by
  simp [rot]

theorem shift_empty (v : Site) : shift (∅ : Tile) v = ∅ := by
  simp [shift]

/-- A plain piece: the rotation of `T + c`, translated by `τ`, is `T' + c'`. -/
theorem piece_plain {T Ts : Tile} {t c c' τ : Site} (h : rot T = shift Ts t) (hc : t + mulI c + τ = c') :
    shift (rot (shift T c)) τ = shift Ts c' := by
  rw [rot_shift, h, shift_shift, shift_shift]
  congr 1
  rw [← hc]
  abel

/-- A doubled piece whose doubling shift rotates to the doubling shift of its image. -/
theorem piece_dbl {T Ts : Tile} {S S' t c c' τ : Site} (h : rot T = shift Ts t) (hS : mulI S = S')
    (hc : t + mulI c + τ = c') : shift (rot (shift (doubled T S) c)) τ = shift (doubled Ts S') c' := by
  rw [rot_shift, rot_doubled, h, hS, ← shift_doubled, shift_shift, shift_shift]
  congr 1
  rw [← hc]
  abel

/-- A doubled piece whose doubling shift rotates to minus the doubling shift of its image (the two copies are exchanged). -/
theorem piece_dbl_flip {T Ts : Tile} {S S' t c c' τ : Site} (h : rot T = shift Ts t) (hS : mulI S = -S')
    (hc : -S' + t + mulI c + τ = c') : shift (rot (shift (doubled T S) c)) τ = shift (doubled Ts S') c' := by
  rw [rot_shift, rot_doubled, h, hS, ← shift_doubled, doubled_neg, shift_shift, shift_shift, shift_shift]
  congr 1
  rw [← hc]
  abel

/-- The alternate parent piece, from the rotation identity of the alternate register. -/
theorem piece_alt {aE aO : Tile} {c c' tA τ : Site} (hA : shift (rot aE) tA = aO) (h : mulI c + τ = tA + c') :
    shift (rot (shift aE c)) τ = shift aO c' := by
  rw [rot_shift, ← hA, shift_shift, shift_shift, h]

/-! ### The pieces of the alternate decomposition -/

/-- The offset of a piece of `T̂(p_0)` (`eq:alt_offsets_w1_odd`, `eq:alt_offsets_w1_even`). -/
def offP0 (o : Bool) (p q : Fraction) (x : AltP0Piece) : Site :=
  coeffOff (texV1Odd p) (texV2 p) (texV1Even q) (texV2 q) (altP0Coeff o x)

/-- The offset of a piece of `T̂(q_0)`. -/
def offQ0 (o : Bool) (p q : Fraction) (x : AltQ0Piece) : Site :=
  coeffOff (texV1Odd p) (texV2 p) (texV1Even q) (texV2 q) (altQ0Coeff o x)

/-- The doubling shift `S_p`. -/
def shP (o : Bool) (p q : Fraction) : Site := (altShifts o (texV2 p) (texV1Even q)).1

/-- The doubling shift `S_q`. -/
def shQ (o : Bool) (p q : Fraction) : Site := (altShifts o (texV2 p) (texV1Even q)).2

/-- The standard pieces of `T̂(p_0)`: `T^{ds}(p_1)^±` and `T(q_1)^±`. -/
def oddStd (o : Bool) (T1 T2 : Tile) (p q : Fraction) : Tile :=
  shift (doubled T1 (shP o p q)) (offP0 o p q .dsP1Plus) ∪ shift (doubled T1 (shP o p q)) (offP0 o p q .dsP1Minus) ∪
    shift T2 (offP0 o p q .q1Plus) ∪ shift T2 (offP0 o p q .q1Minus)

/-- The standard pieces of `T̂(q_0)`: `T(p_1)^±` and `T^{ds}(q_1)^±`. -/
def evenStd (o : Bool) (T1 T2 : Tile) (p q : Fraction) : Tile :=
  shift T1 (offQ0 o p q .p1Plus) ∪ shift T1 (offQ0 o p q .p1Minus) ∪
    shift (doubled T2 (shQ o p q)) (offQ0 o p q .dsQ1Plus) ∪ shift (doubled T2 (shQ o p q)) (offQ0 o p q .dsQ1Minus)

/-- The alternate parent piece `T̂(q_1)` of `T̂(p_0)` for the type `x` (omitted for `x = 2`). -/
def altQ1Part (o : Bool) (x : Digit) (aE : Tile) (p q : Fraction) : Tile :=
  match altQ1Coeff o x with
  | none => ∅
  | some c => shift aE (coeffOff (texV1Odd p) (texV2 p) (texV1Even q) (texV2 q) c)

/-- The alternate parent piece `T̂(p_1)` of `T̂(q_0)` for the type `x` (omitted for `x = 3`). -/
def altP1Part (o : Bool) (x : Digit) (aO : Tile) (p q : Fraction) : Tile :=
  match altP1Coeff o x with
  | none => ∅
  | some c => shift aO (coeffOff (texV1Odd p) (texV2 p) (texV1Even q) (texV2 q) c)

theorem altTypeOf_snoc (u : Word) (x : Digit) : altTypeOf (u ++ [x]) = some x := by
  simp [altTypeOf]

theorem altOddPieces_snoc (u : Word) (x : Digit) (aE : Tile) :
    altOddPieces (u ++ [x]) aE =
      oddStd (phase (u ++ [x]) == 1) (stateAt (u ++ [x])).tOdd (stateAt (u ++ [x])).tEven (parentsAt (u ++ [x])).odd
          (parentsAt (u ++ [x])).even ∪
        altQ1Part (phase (u ++ [x]) == 1) x aE (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even := by
  simp only [altOddPieces, altTypeOf_snoc, oddStd, altQ1Part, offP0, shP]
  cases altQ1Coeff (phase (u ++ [x]) == 1) x <;> rfl

theorem altEvenPieces_snoc (u : Word) (x : Digit) (aO : Tile) :
    altEvenPieces (u ++ [x]) aO =
      evenStd (phase (u ++ [x]) == 1) (stateAt (u ++ [x])).tOdd (stateAt (u ++ [x])).tEven (parentsAt (u ++ [x])).odd
          (parentsAt (u ++ [x])).even ∪
        altP1Part (phase (u ++ [x]) == 1) x aO (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even := by
  simp only [altEvenPieces, altTypeOf_snoc, evenStd, altP1Part, offQ0, shQ]
  cases altP1Coeff (phase (u ++ [x]) == 1) x <;> rfl

/-! ### The translations -/

/-- `-tF` of the child `p₀`: the translation in the cases where the piece at offset `0` is plain. -/
def tauShort (p q : Fraction) : Site := (p.den + p.num + q.den + q.num, p.den - p.num + q.den - q.num - 1)

/-- The translation in the cases where the piece at offset `0` is doubled. -/
def tauLong (p q : Fraction) : Site :=
  (q.den + 2 * p.den + 2 * p.num, 2 * q.den - q.num + 2 * p.den - 2 * p.num - 1)

/-- The translation of the rotation of `T̂(p_0)` (`o`: `W₁` odd). -/
def tauOdd (o : Bool) (p q : Fraction) : Site := if o then tauLong p q else tauShort p q

/-- The translation of the rotation of `T̂(q_0)`. -/
def tauEven (o : Bool) (p q : Fraction) : Site := if o then tauShort p q else tauLong p q

/-- The translation of the rotation of the alternate odd child of `w`. -/
def tauO (w : Word) : Site := tauOdd (phase w == 1) (parentsAt w).odd (parentsAt w).even

/-- The translation of the rotation of the alternate even child of `w`. -/
def tauE (w : Word) : Site := tauEven (phase w == 1) (parentsAt w).odd (parentsAt w).even

/-! ### The standard pieces, case by case -/

theorem rot_oddStd_true (T1 T2 T1s T2s : Tile) (p q : Fraction) (hp : p.Odd) (hq : q.Even)
    (h1 : rot T1 = shift T2s (tF p)) (h2 : rot T2 = shift T1s (tF q)) :
    shift (rot (oddStd true T1 T2 p q)) (tauLong p q) = evenStd true T1s T2s q.rotate p.rotate := by
  have hp' : (p.num + p.den) % 2 = 1 := hp
  have hq' : (q.num + q.den) % 2 = 0 := hq
  have e1 : shift (rot (shift (doubled T1 (shP true p q)) (offP0 true p q .dsP1Plus))) (tauLong p q) =
      shift (doubled T2s (shQ true q.rotate p.rotate)) (offQ0 true q.rotate p.rotate .dsQ1Plus) :=
    piece_dbl_flip h1 (by simp only [rotate_eq_of_odd hp, rotate_eq_of_even hq, shP, shQ, altShifts, texV1Even, texV2, mulI]; ext <;> simp <;> omega) (by simp only [rotate_eq_of_odd hp, rotate_eq_of_even hq, shQ, offP0, offQ0, coeffOff, altP0Coeff, altQ0Coeff, altShifts, tF, tV, texV1Odd, texV1Even, texV2, mulI, tauLong]; ext <;> simp <;> omega)
  have e2 : shift (rot (shift (doubled T1 (shP true p q)) (offP0 true p q .dsP1Minus))) (tauLong p q) =
      shift (doubled T2s (shQ true q.rotate p.rotate)) (offQ0 true q.rotate p.rotate .dsQ1Minus) :=
    piece_dbl_flip h1 (by simp only [rotate_eq_of_odd hp, rotate_eq_of_even hq, shP, shQ, altShifts, texV1Even, texV2, mulI]; ext <;> simp <;> omega) (by simp only [rotate_eq_of_odd hp, rotate_eq_of_even hq, shQ, offP0, offQ0, coeffOff, altP0Coeff, altQ0Coeff, altShifts, tF, tV, texV1Odd, texV1Even, texV2, mulI, tauLong]; ext <;> simp <;> omega)
  have e3 : shift (rot (shift T2 (offP0 true p q .q1Plus))) (tauLong p q) =
      shift T1s (offQ0 true q.rotate p.rotate .p1Minus) := piece_plain h2 (by simp only [rotate_eq_of_odd hp, rotate_eq_of_even hq, offP0, offQ0, coeffOff, altP0Coeff, altQ0Coeff, tF, tV, texV1Odd, texV1Even, texV2, mulI, tauLong]; ext <;> simp <;> omega)
  have e4 : shift (rot (shift T2 (offP0 true p q .q1Minus))) (tauLong p q) =
      shift T1s (offQ0 true q.rotate p.rotate .p1Plus) := piece_plain h2 (by simp only [rotate_eq_of_odd hp, rotate_eq_of_even hq, offP0, offQ0, coeffOff, altP0Coeff, altQ0Coeff, tF, tV, texV1Odd, texV1Even, texV2, mulI, tauLong]; ext <;> simp <;> omega)
  unfold oddStd evenStd
  simp only [rot_union, shift_union, e1, e2, e3, e4]
  ext x
  simp only [Finset.mem_union]
  tauto

theorem rot_oddStd_false (T1 T2 T1s T2s : Tile) (p q : Fraction) (hp : p.Odd) (hq : q.Even)
    (h1 : rot T1 = shift T2s (tF p)) (h2 : rot T2 = shift T1s (tF q)) :
    shift (rot (oddStd false T1 T2 p q)) (tauShort p q) = evenStd false T1s T2s q.rotate p.rotate := by
  have hp' : (p.num + p.den) % 2 = 1 := hp
  have hq' : (q.num + q.den) % 2 = 0 := hq
  have e1 : shift (rot (shift (doubled T1 (shP false p q)) (offP0 false p q .dsP1Plus))) (tauShort p q) =
      shift (doubled T2s (shQ false q.rotate p.rotate)) (offQ0 false q.rotate p.rotate .dsQ1Minus) :=
    piece_dbl h1 (by simp only [rotate_eq_of_odd hp, rotate_eq_of_even hq, shP, shQ, altShifts, texV1Even, texV2, mulI]; ext <;> simp <;> omega) (by simp only [rotate_eq_of_odd hp, rotate_eq_of_even hq, offP0, offQ0, coeffOff, altP0Coeff, altQ0Coeff, tF, tV, texV1Odd, texV1Even, texV2, mulI, tauShort]; ext <;> simp <;> omega)
  have e2 : shift (rot (shift (doubled T1 (shP false p q)) (offP0 false p q .dsP1Minus))) (tauShort p q) =
      shift (doubled T2s (shQ false q.rotate p.rotate)) (offQ0 false q.rotate p.rotate .dsQ1Plus) :=
    piece_dbl h1 (by simp only [rotate_eq_of_odd hp, rotate_eq_of_even hq, shP, shQ, altShifts, texV1Even, texV2, mulI]; ext <;> simp <;> omega) (by simp only [rotate_eq_of_odd hp, rotate_eq_of_even hq, offP0, offQ0, coeffOff, altP0Coeff, altQ0Coeff, tF, tV, texV1Odd, texV1Even, texV2, mulI, tauShort]; ext <;> simp <;> omega)
  have e3 : shift (rot (shift T2 (offP0 false p q .q1Plus))) (tauShort p q) =
      shift T1s (offQ0 false q.rotate p.rotate .p1Plus) := piece_plain h2 (by simp only [rotate_eq_of_odd hp, rotate_eq_of_even hq, offP0, offQ0, coeffOff, altP0Coeff, altQ0Coeff, tF, tV, texV1Odd, texV1Even, texV2, mulI, tauShort]; ext <;> simp <;> omega)
  have e4 : shift (rot (shift T2 (offP0 false p q .q1Minus))) (tauShort p q) =
      shift T1s (offQ0 false q.rotate p.rotate .p1Minus) := piece_plain h2 (by simp only [rotate_eq_of_odd hp, rotate_eq_of_even hq, offP0, offQ0, coeffOff, altP0Coeff, altQ0Coeff, tF, tV, texV1Odd, texV1Even, texV2, mulI, tauShort]; ext <;> simp <;> omega)
  unfold oddStd evenStd
  simp only [rot_union, shift_union, e1, e2, e3, e4]
  ext x
  simp only [Finset.mem_union]
  tauto

theorem rot_evenStd_true (T1 T2 T1s T2s : Tile) (p q : Fraction) (hp : p.Odd) (hq : q.Even)
    (h1 : rot T1 = shift T2s (tF p)) (h2 : rot T2 = shift T1s (tF q)) :
    shift (rot (evenStd true T1 T2 p q)) (tauShort p q) = oddStd true T1s T2s q.rotate p.rotate := by
  have hp' : (p.num + p.den) % 2 = 1 := hp
  have hq' : (q.num + q.den) % 2 = 0 := hq
  have e1 : shift (rot (shift T1 (offQ0 true p q .p1Plus))) (tauShort p q) =
      shift T2s (offP0 true q.rotate p.rotate .q1Plus) := piece_plain h1 (by simp only [rotate_eq_of_odd hp, rotate_eq_of_even hq, offP0, offQ0, coeffOff, altP0Coeff, altQ0Coeff, tF, tV, texV1Odd, texV1Even, texV2, mulI, tauShort]; ext <;> simp <;> omega)
  have e2 : shift (rot (shift T1 (offQ0 true p q .p1Minus))) (tauShort p q) =
      shift T2s (offP0 true q.rotate p.rotate .q1Minus) := piece_plain h1 (by simp only [rotate_eq_of_odd hp, rotate_eq_of_even hq, offP0, offQ0, coeffOff, altP0Coeff, altQ0Coeff, tF, tV, texV1Odd, texV1Even, texV2, mulI, tauShort]; ext <;> simp <;> omega)
  have e3 : shift (rot (shift (doubled T2 (shQ true p q)) (offQ0 true p q .dsQ1Plus))) (tauShort p q) =
      shift (doubled T1s (shP true q.rotate p.rotate)) (offP0 true q.rotate p.rotate .dsP1Minus) :=
    piece_dbl h2 (by simp only [rotate_eq_of_odd hp, rotate_eq_of_even hq, shP, shQ, altShifts, texV1Even, texV2, mulI]; ext <;> simp <;> omega) (by simp only [rotate_eq_of_odd hp, rotate_eq_of_even hq, offP0, offQ0, coeffOff, altP0Coeff, altQ0Coeff, tF, tV, texV1Odd, texV1Even, texV2, mulI, tauShort]; ext <;> simp <;> omega)
  have e4 : shift (rot (shift (doubled T2 (shQ true p q)) (offQ0 true p q .dsQ1Minus))) (tauShort p q) =
      shift (doubled T1s (shP true q.rotate p.rotate)) (offP0 true q.rotate p.rotate .dsP1Plus) :=
    piece_dbl h2 (by simp only [rotate_eq_of_odd hp, rotate_eq_of_even hq, shP, shQ, altShifts, texV1Even, texV2, mulI]; ext <;> simp <;> omega) (by simp only [rotate_eq_of_odd hp, rotate_eq_of_even hq, offP0, offQ0, coeffOff, altP0Coeff, altQ0Coeff, tF, tV, texV1Odd, texV1Even, texV2, mulI, tauShort]; ext <;> simp <;> omega)
  unfold oddStd evenStd
  simp only [rot_union, shift_union, e1, e2, e3, e4]
  ext x
  simp only [Finset.mem_union]
  tauto

theorem rot_evenStd_false (T1 T2 T1s T2s : Tile) (p q : Fraction) (hp : p.Odd) (hq : q.Even)
    (h1 : rot T1 = shift T2s (tF p)) (h2 : rot T2 = shift T1s (tF q)) :
    shift (rot (evenStd false T1 T2 p q)) (tauLong p q) = oddStd false T1s T2s q.rotate p.rotate := by
  have hp' : (p.num + p.den) % 2 = 1 := hp
  have hq' : (q.num + q.den) % 2 = 0 := hq
  have e1 : shift (rot (shift T1 (offQ0 false p q .p1Plus))) (tauLong p q) =
      shift T2s (offP0 false q.rotate p.rotate .q1Minus) := piece_plain h1 (by simp only [rotate_eq_of_odd hp, rotate_eq_of_even hq, offP0, offQ0, coeffOff, altP0Coeff, altQ0Coeff, tF, tV, texV1Odd, texV1Even, texV2, mulI, tauLong]; ext <;> simp <;> omega)
  have e2 : shift (rot (shift T1 (offQ0 false p q .p1Minus))) (tauLong p q) =
      shift T2s (offP0 false q.rotate p.rotate .q1Plus) := piece_plain h1 (by simp only [rotate_eq_of_odd hp, rotate_eq_of_even hq, offP0, offQ0, coeffOff, altP0Coeff, altQ0Coeff, tF, tV, texV1Odd, texV1Even, texV2, mulI, tauLong]; ext <;> simp <;> omega)
  have e3 : shift (rot (shift (doubled T2 (shQ false p q)) (offQ0 false p q .dsQ1Plus))) (tauLong p q) =
      shift (doubled T1s (shP false q.rotate p.rotate)) (offP0 false q.rotate p.rotate .dsP1Plus) :=
    piece_dbl_flip h2 (by simp only [rotate_eq_of_odd hp, rotate_eq_of_even hq, shP, shQ, altShifts, texV1Even, texV2, mulI]; ext <;> simp <;> omega) (by simp only [rotate_eq_of_odd hp, rotate_eq_of_even hq, shP, offP0, offQ0, coeffOff, altP0Coeff, altQ0Coeff, altShifts, tF, tV, texV1Odd, texV1Even, texV2, mulI, tauLong]; ext <;> simp <;> omega)
  have e4 : shift (rot (shift (doubled T2 (shQ false p q)) (offQ0 false p q .dsQ1Minus))) (tauLong p q) =
      shift (doubled T1s (shP false q.rotate p.rotate)) (offP0 false q.rotate p.rotate .dsP1Minus) :=
    piece_dbl_flip h2 (by simp only [rotate_eq_of_odd hp, rotate_eq_of_even hq, shP, shQ, altShifts, texV1Even, texV2, mulI]; ext <;> simp <;> omega) (by simp only [rotate_eq_of_odd hp, rotate_eq_of_even hq, shP, offP0, offQ0, coeffOff, altP0Coeff, altQ0Coeff, altShifts, tF, tV, texV1Odd, texV1Even, texV2, mulI, tauLong]; ext <;> simp <;> omega)
  unfold oddStd evenStd
  simp only [rot_union, shift_union, e1, e2, e3, e4]
  ext x
  simp only [Finset.mem_union]
  tauto

/-! ### The registers of the alternate recursion -/

/-- The alternate tiles with the base alternates of `prop:base_cases`. -/
abbrev B : Word → Tile × Tile := FLatticePaper.Tiles.PaperAltBase.paperAltBaseTiles

theorem altRun_snoc (base : Word → Tile × Tile) (x : Digit) :
    ∀ (w pre : Word) (r : Tile × Tile), altRun base pre (w ++ [x]) r = altStep base (pre ++ w) (altRun base pre w r) x := by
  intro w
  induction w with
  | nil => intro pre r; simp [altRun]
  | cons d w ih =>
    intro pre r
    simp only [List.cons_append, altRun]
    rw [ih (pre ++ [d])]
    simp [List.append_assoc]

theorem altRegs_snoc (base : Word → Tile × Tile) (u : Word) (x : Digit) :
    altRegs base (u ++ [x]) = altStep base u (altRegs base u) x := by
  unfold altRegs
  rw [altRun_snoc]
  simp

theorem altOddTile_of_not_base (base : Word → Tile × Tile) {w : Word} (hw : ¬ IsBase w) :
    altOddTile base w = altOddPieces w (altRegs base w).2 := by
  unfold altOddTile altChild
  rw [if_neg hw]

theorem altEvenTile_of_not_base (base : Word → Tile × Tile) {w : Word} (hw : ¬ IsBase w) :
    altEvenTile base w = altEvenPieces w (altRegs base w).1 := by
  unfold altEvenTile altChild
  rw [if_neg hw]

theorem altOddTile_of_base (base : Word → Tile × Tile) {w : Word} (hw : IsBase w) : altOddTile base w = (base w).1 := by
  unfold altOddTile altChild
  rw [if_pos hw]

theorem altEvenTile_of_base (base : Word → Tile × Tile) {w : Word} (hw : IsBase w) : altEvenTile base w = (base w).2 := by
  unfold altEvenTile altChild
  rw [if_pos hw]

theorem phase_snoc_one (u : Word) : (phase (u ++ [.one]) == 1) = !(phase u == 1) := by
  unfold phase
  rw [List.count_append]
  rcases Nat.mod_two_eq_zero_or_one (u.count .one) with h | h <;> simp [Nat.add_mod, h]

theorem phase_snoc_two (u : Word) : (phase (u ++ [.two]) == 1) = (phase u == 1) := by
  unfold phase
  rw [List.count_append]
  simp

theorem phase_snoc_three (u : Word) : (phase (u ++ [.three]) == 1) = (phase u == 1) := by
  unfold phase
  rw [List.count_append]
  simp

/-! ### The base words -/

theorem B_nil : B [] = (shift (FLatticePaper.Tiles.PaperAltBase.nearStairAltF 3) (0, -1),
    FLatticePaper.Tiles.PaperAltBase.stairAltF 3) := by
  simp [B, FLatticePaper.Tiles.PaperAltBase.paperAltBaseTiles]

theorem B_three (k : ℕ) (hk : 1 ≤ k) : B (List.replicate k Digit.three) =
    (shift (FLatticePaper.Tiles.PaperAltBase.ladderAltF (2 * (k : ℤ) + 2)) (1, 1),
      FLatticePaper.Tiles.PaperAltBase.stairAltF (2 * (k : ℤ) + 3)) := by
  have hne : List.replicate k Digit.three ≠ [] := by
    intro h
    have := congrArg List.length h
    simp at this
    omega
  simp only [B, FLatticePaper.Tiles.PaperAltBase.paperAltBaseTiles, if_neg hne, List.length_replicate, if_true]

theorem B_two (k : ℕ) (hk : 1 ≤ k) : B (List.replicate k Digit.two) =
    (shift (FLatticePaper.Tiles.PaperAltBase.nearStairAltF (2 * (k : ℤ) + 3)) (0, -1),
      shift (FLatticePaper.Tiles.PaperAltBase.nearLadderAltF (2 * (k : ℤ) + 2)) (0, -1)) := by
  have hne : List.replicate k Digit.two ≠ [] := by
    intro h
    have := congrArg List.length h
    simp at this
    omega
  have hne3 : ¬ List.replicate k Digit.two = List.replicate k Digit.three := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp [List.replicate_succ]
  simp only [B, FLatticePaper.Tiles.PaperAltBase.paperAltBaseTiles, if_neg hne, if_neg hne3, List.length_replicate]

theorem phase_replicate_two (k : ℕ) : phase (List.replicate k Digit.two) = 0 := by
  simp [phase, List.count_replicate]

theorem phase_replicate_three (k : ℕ) : phase (List.replicate k Digit.three) = 0 := by
  simp [phase, List.count_replicate]

theorem swapW_replicate_two (k : ℕ) : swapW (List.replicate k Digit.two) = List.replicate k Digit.three := by
  simp [swapW, List.map_replicate, Digit.swapTwoThree]

theorem swapW_replicate_three (k : ℕ) : swapW (List.replicate k Digit.three) = List.replicate k Digit.two := by
  simp [swapW, List.map_replicate, Digit.swapTwoThree]

theorem isBase_replicate_two (k : ℕ) : IsBase (List.replicate k Digit.two) :=
  Or.inr (Or.inr fun _ hd => (List.eq_of_mem_replicate hd))

theorem isBase_replicate_three (k : ℕ) : IsBase (List.replicate k Digit.three) :=
  Or.inr (Or.inl fun _ hd => (List.eq_of_mem_replicate hd))

/-- The rotation identities of the alternate children of `w`, with the translations `tauO`, `tauE`. -/
def AltRotAt (w : Word) : Prop :=
  shift (rot (altOddTile B w)) (tauO w) = altEvenTile B (swapW w) ∧
    shift (rot (altEvenTile B w)) (tauE w) = altOddTile B (swapW w)

theorem altRot_nil : AltRotAt [] := by
  have hb : IsBase [] := Or.inl rfl
  unfold AltRotAt
  rw [show swapW [] = [] from rfl, altOddTile_of_base B hb, altEvenTile_of_base B hb, B_nil]
  have t1 : tauO [] = ((3 : ℤ), (0 : ℤ)) := by
    simp [tauO, tauOdd, tauShort, phase, parentsAt, root, Parents.walk]
  have t2 : tauE [] = ((3 : ℤ), 2 * 3 - 4) := by
    simp [tauE, tauEven, tauLong, phase, parentsAt, root, Parents.walk]
  rw [t1, t2]
  exact ⟨FLatticePaper.Tiles.AltRotBase.rot_nearStair_eq_stair 3 (by norm_num),
    FLatticePaper.Tiles.AltRotBase.rot_stair_eq_nearStair 3 (by norm_num)⟩

theorem altRot_three (k : ℕ) (hk : 1 ≤ k) : AltRotAt (List.replicate k Digit.three) := by
  unfold AltRotAt
  rw [swapW_replicate_three, altOddTile_of_base B (isBase_replicate_three k), altEvenTile_of_base B (isBase_replicate_three k),
    altOddTile_of_base B (isBase_replicate_two k), altEvenTile_of_base B (isBase_replicate_two k), B_three k hk, B_two k hk]
  have t1 : tauO (List.replicate k Digit.three) = (2 * (k : ℤ) + 2 + 1, 2 * (k : ℤ) + 2 - 2) := by
    simp only [tauO, tauOdd, tauShort, phase_replicate_three, FLatticePaper.Tiles.parentsAt_replicate_three]
    refine Prod.ext ?_ ?_
    · simp; ring
    · simp
  have t2 : tauE (List.replicate k Digit.three) = (2 * (k : ℤ) + 3, 2 * (2 * (k : ℤ) + 3) - 4) := by
    simp only [tauE, tauEven, tauLong, phase_replicate_three, FLatticePaper.Tiles.parentsAt_replicate_three]
    ext <;> simp <;> ring
  rw [t1, t2]
  exact ⟨FLatticePaper.Tiles.AltRotBase.rot_ladder_eq_nearLadder _,
    FLatticePaper.Tiles.AltRotBase.rot_stair_eq_nearStair _ (by omega)⟩

theorem altRot_two (k : ℕ) (hk : 1 ≤ k) : AltRotAt (List.replicate k Digit.two) := by
  unfold AltRotAt
  rw [swapW_replicate_two, altOddTile_of_base B (isBase_replicate_two k), altEvenTile_of_base B (isBase_replicate_two k),
    altOddTile_of_base B (isBase_replicate_three k), altEvenTile_of_base B (isBase_replicate_three k), B_two k hk,
    B_three k hk]
  have t1 : tauO (List.replicate k Digit.two) = (2 * (k : ℤ) + 3, 0) := by
    simp only [tauO, tauOdd, tauShort, phase_replicate_two, FLatticePaper.Tiles.parentsAt_replicate_two]
    refine Prod.ext ?_ ?_
    · simp; ring
    · simp
  have t2 : tauE (List.replicate k Digit.two) = (2 * (2 * (k : ℤ) + 2) - 1, 2) := by
    simp only [tauE, tauEven, tauLong, phase_replicate_two, FLatticePaper.Tiles.parentsAt_replicate_two]
    ext <;> simp <;> ring
  rw [t1, t2]
  exact ⟨FLatticePaper.Tiles.AltRotBase.rot_nearStair_eq_stair _ (by omega),
    FLatticePaper.Tiles.AltRotBase.rot_nearLadder_eq_ladder _⟩

theorem altRot_base (w : Word) (hb : IsBase w) : AltRotAt w := by
  by_cases h0 : w = []
  · subst h0
    exact altRot_nil
  rcases hb with h | h | h
  · exact absurd h h0
  · obtain ⟨k, rfl⟩ : ∃ k, w = List.replicate k Digit.three := ⟨w.length, List.eq_replicate_iff.mpr ⟨rfl, h⟩⟩
    have hk : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at h0
      · exact hk
    exact altRot_three k hk
  · obtain ⟨k, rfl⟩ : ∃ k, w = List.replicate k Digit.two := ⟨w.length, List.eq_replicate_iff.mpr ⟨rfl, h⟩⟩
    have hk : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at h0
      · exact hk
    exact altRot_two k hk

/-! ### The alternate parent piece -/

theorem altQ1Part_rot (o : Bool) (x : Digit) (A : Tile) (p q pt qt : Fraction) (tA τ : Site)
    (h : ∀ c c', altQ1Coeff o x = some c → altP1Coeff o x.swapTwoThree = some c' →
      mulI (coeffOff (texV1Odd p) (texV2 p) (texV1Even q) (texV2 q) c) + τ =
        tA + coeffOff (texV1Odd pt) (texV2 pt) (texV1Even qt) (texV2 qt) c') :
    shift (rot (altQ1Part o x A p q)) τ = altP1Part o x.swapTwoThree (shift (rot A) tA) pt qt := by
  unfold altQ1Part altP1Part
  cases hc : altQ1Coeff o x with
  | none =>
    have hc' : altP1Coeff o x.swapTwoThree = none := by
      cases o <;> cases x <;> simp_all [altQ1Coeff, altP1Coeff, Digit.swapTwoThree]
    rw [hc']
    simp only [rot_empty, shift_empty]
  | some c =>
    cases hc' : altP1Coeff o x.swapTwoThree with
    | none =>
      exfalso
      cases o <;> cases x <;> simp_all [altQ1Coeff, altP1Coeff, Digit.swapTwoThree]
    | some c' =>
      exact piece_alt rfl (h c c' hc hc')

theorem altP1Part_rot (o : Bool) (x : Digit) (A : Tile) (p q pt qt : Fraction) (tA τ : Site)
    (h : ∀ c c', altP1Coeff o x = some c → altQ1Coeff o x.swapTwoThree = some c' →
      mulI (coeffOff (texV1Odd p) (texV2 p) (texV1Even q) (texV2 q) c) + τ =
        tA + coeffOff (texV1Odd pt) (texV2 pt) (texV1Even qt) (texV2 qt) c') :
    shift (rot (altP1Part o x A p q)) τ = altQ1Part o x.swapTwoThree (shift (rot A) tA) pt qt := by
  unfold altQ1Part altP1Part
  cases hc : altP1Coeff o x with
  | none =>
    have hc' : altQ1Coeff o x.swapTwoThree = none := by
      cases o <;> cases x <;> simp_all [altQ1Coeff, altP1Coeff, Digit.swapTwoThree]
    rw [hc']
    simp only [rot_empty, shift_empty]
  | some c =>
    cases hc' : altQ1Coeff o x.swapTwoThree with
    | none =>
      exfalso
      cases o <;> cases x <;> simp_all [altQ1Coeff, altP1Coeff, Digit.swapTwoThree]
    | some c' =>
      exact piece_alt rfl (h c c' hc hc')

/-! ### The identities of the alternate parent piece -/

theorem identO (P : Parents) (hV : P.ValidFrame) (o : Bool) (x : Digit) (hx : x = .one ∨ x = .three) (o' : Bool)
    (ho' : o' = if x = .one then !o else o) (c c' : AltCoeff) (hc : altQ1Coeff o' x = some c)
    (hc' : altP1Coeff o' x.swapTwoThree = some c') :
    mulI (coeffOff (texV1Odd (P.step x).odd) (texV2 (P.step x).odd) (texV1Even (P.step x).even) (texV2 (P.step x).even) c) +
        tauOdd o' (P.step x).odd (P.step x).even =
      tauEven o P.odd P.even + coeffOff (texV1Odd (P.step x).even.rotate) (texV2 (P.step x).even.rotate)
        (texV1Even (P.step x).odd.rotate) (texV2 (P.step x).odd.rotate) c' := by
  have hp : (P.odd.num + P.odd.den) % 2 = 1 := hV.odd_parity
  have hq : (P.even.num + P.even.den) % 2 = 0 := hV.even_parity
  have hVs := hV.step x
  rw [rotate_eq_of_odd hVs.odd_parity, rotate_eq_of_even hVs.even_parity]
  subst ho'
  rcases hx with rfl | rfl <;> cases o <;> simp [altQ1Coeff, altP1Coeff, Digit.swapTwoThree] at hc hc' <;>
    subst hc hc' <;>
    simp only [Parents.step, Parents.current, Parents.combine, coeffOff, tauOdd, tauEven, tauLong, tauShort, texV1Odd,
      texV1Even, texV2, mulI] <;> ext <;> simp <;> omega

theorem identE (P : Parents) (hV : P.ValidFrame) (o : Bool) (x : Digit) (hx : x = .one ∨ x = .two) (o' : Bool)
    (ho' : o' = if x = .one then !o else o) (c c' : AltCoeff) (hc : altP1Coeff o' x = some c)
    (hc' : altQ1Coeff o' x.swapTwoThree = some c') :
    mulI (coeffOff (texV1Odd (P.step x).odd) (texV2 (P.step x).odd) (texV1Even (P.step x).even) (texV2 (P.step x).even) c) +
        tauEven o' (P.step x).odd (P.step x).even =
      tauOdd o P.odd P.even + coeffOff (texV1Odd (P.step x).even.rotate) (texV2 (P.step x).even.rotate)
        (texV1Even (P.step x).odd.rotate) (texV2 (P.step x).odd.rotate) c' := by
  have hp : (P.odd.num + P.odd.den) % 2 = 1 := hV.odd_parity
  have hq : (P.even.num + P.even.den) % 2 = 0 := hV.even_parity
  have hVs := hV.step x
  rw [rotate_eq_of_odd hVs.odd_parity, rotate_eq_of_even hVs.even_parity]
  subst ho'
  rcases hx with rfl | rfl <;> cases o <;> simp [altQ1Coeff, altP1Coeff, Digit.swapTwoThree] at hc hc' <;>
    subst hc hc' <;>
    simp only [Parents.step, Parents.current, Parents.combine, coeffOff, tauOdd, tauEven, tauLong, tauShort, texV1Odd,
      texV1Even, texV2, mulI] <;> ext <;> simp <;> omega

theorem altRot_step_one (u : Word) (hb : ¬ IsBase (u ++ [.one])) (ih : AltRotAt u) : AltRotAt (u ++ [.one]) := by
  have hsw' : swapW (u ++ [.one]) = swapW u ++ [.one] := FLatticePaper.Tiles.Standard.swapW_snoc_one u
  have hsw : ¬ IsBase (swapW u ++ [.one]) := hsw' ▸ FLatticePaper.Tiles.Standard.nonbase_swap hb
  have hG := FLatticePaper.Tiles.Standard.good_and_rot (u ++ [.one])
  have h3 : ¬ ∀ d ∈ u ++ [.one], d = Digit.three := fun h => hb (Or.inr (Or.inl h))
  have h2 : ¬ ∀ d ∈ u ++ [.one], d = Digit.two := fun h => hb (Or.inr (Or.inr h))
  have h1' := hG.2.1.resolve_left h3
  have h2' := hG.2.2.resolve_left h2
  rw [hsw'] at h1' h2'
  have hV := parentsAt_valid (u ++ [.one])
  have hpar : parentsAt (swapW u ++ [.one]) =
      ⟨(parentsAt (u ++ [.one])).even.rotate, (parentsAt (u ++ [.one])).odd.rotate⟩ := by
    rw [← hsw', FLatticePaper.Tiles.Standard.parentsAt_swapW]
    rfl
  have hph : phase (swapW u ++ [.one]) = phase (u ++ [.one]) := by
    rw [← hsw']
    exact FLatticePaper.Tiles.Standard.phase_swapW _
  unfold AltRotAt
  rw [hsw', altOddTile_of_not_base B hb, altEvenTile_of_not_base B hb, altOddTile_of_not_base B hsw,
    altEvenTile_of_not_base B hsw, altOddPieces_snoc, altOddPieces_snoc, altEvenPieces_snoc, altEvenPieces_snoc, hpar,
    hph]
  refine ⟨?_, ?_⟩
  · rw [rot_union, shift_union]
    congr 1
    · unfold tauO
      cases ho : (phase (u ++ [.one]) == 1)
      · exact rot_oddStd_false _ _ _ _ _ _ hV.odd_parity hV.even_parity h1' h2'
      · exact rot_oddStd_true _ _ _ _ _ _ hV.odd_parity hV.even_parity h1' h2'
    · rw [show (altRegs B (u ++ [.one])).2 = altEvenTile B u by rw [altRegs_snoc]; rfl,
        show (altRegs B (swapW u ++ [.one])).1 = altOddTile B (swapW u) by rw [altRegs_snoc]; rfl, ← ih.2]
      apply altQ1Part_rot
      intro c c' hc hc'
      unfold tauO tauE
      rw [phase_snoc_one] at hc hc' ⊢
      rw [parentsAt_append_singleton]
      exact identO (parentsAt u) (parentsAt_valid u) (phase u == 1) Digit.one (Or.inl rfl) _ (by simp) c c' hc hc'
  · rw [rot_union, shift_union]
    congr 1
    · unfold tauE
      cases ho : (phase (u ++ [.one]) == 1)
      · exact rot_evenStd_false _ _ _ _ _ _ hV.odd_parity hV.even_parity h1' h2'
      · exact rot_evenStd_true _ _ _ _ _ _ hV.odd_parity hV.even_parity h1' h2'
    · rw [show (altRegs B (u ++ [.one])).1 = altOddTile B u by rw [altRegs_snoc]; rfl,
        show (altRegs B (swapW u ++ [.one])).2 = altEvenTile B (swapW u) by rw [altRegs_snoc]; rfl, ← ih.1]
      apply altP1Part_rot
      intro c c' hc hc'
      unfold tauO tauE
      rw [phase_snoc_one] at hc hc' ⊢
      rw [parentsAt_append_singleton]
      exact identE (parentsAt u) (parentsAt_valid u) (phase u == 1) Digit.one (Or.inl rfl) _ (by simp) c c' hc hc'

theorem altRot_step_two (u : Word) (hb : ¬ IsBase (u ++ [.two])) (ih : AltRotAt u) : AltRotAt (u ++ [.two]) := by
  have hsw' : swapW (u ++ [.two]) = swapW u ++ [.three] := FLatticePaper.Tiles.Standard.swapW_snoc_two u
  have hsw : ¬ IsBase (swapW u ++ [.three]) := hsw' ▸ FLatticePaper.Tiles.Standard.nonbase_swap hb
  have hG := FLatticePaper.Tiles.Standard.good_and_rot (u ++ [.two])
  have h3 : ¬ ∀ d ∈ u ++ [.two], d = Digit.three := fun h => hb (Or.inr (Or.inl h))
  have h2 : ¬ ∀ d ∈ u ++ [.two], d = Digit.two := fun h => hb (Or.inr (Or.inr h))
  have h1' := hG.2.1.resolve_left h3
  have h2' := hG.2.2.resolve_left h2
  rw [hsw'] at h1' h2'
  have hV := parentsAt_valid (u ++ [.two])
  have hpar : parentsAt (swapW u ++ [.three]) =
      ⟨(parentsAt (u ++ [.two])).even.rotate, (parentsAt (u ++ [.two])).odd.rotate⟩ := by
    rw [← hsw', FLatticePaper.Tiles.Standard.parentsAt_swapW]
    rfl
  have hph : phase (swapW u ++ [.three]) = phase (u ++ [.two]) := by
    rw [← hsw']
    exact FLatticePaper.Tiles.Standard.phase_swapW _
  unfold AltRotAt
  rw [hsw', altOddTile_of_not_base B hb, altEvenTile_of_not_base B hb, altOddTile_of_not_base B hsw,
    altEvenTile_of_not_base B hsw, altOddPieces_snoc, altOddPieces_snoc, altEvenPieces_snoc, altEvenPieces_snoc, hpar,
    hph]
  refine ⟨?_, ?_⟩
  · rw [rot_union, shift_union]
    congr 1
    · unfold tauO
      cases ho : (phase (u ++ [.two]) == 1)
      · exact rot_oddStd_false _ _ _ _ _ _ hV.odd_parity hV.even_parity h1' h2'
      · exact rot_oddStd_true _ _ _ _ _ _ hV.odd_parity hV.even_parity h1' h2'
    · simp [altQ1Part, altP1Part, altQ1Coeff, altP1Coeff, rot_empty, shift_empty]
  · rw [rot_union, shift_union]
    congr 1
    · unfold tauE
      cases ho : (phase (u ++ [.two]) == 1)
      · exact rot_evenStd_false _ _ _ _ _ _ hV.odd_parity hV.even_parity h1' h2'
      · exact rot_evenStd_true _ _ _ _ _ _ hV.odd_parity hV.even_parity h1' h2'
    · rw [show (altRegs B (u ++ [.two])).1 = altOddTile B u by rw [altRegs_snoc]; rfl,
        show (altRegs B (swapW u ++ [.three])).2 = altEvenTile B (swapW u) by rw [altRegs_snoc]; rfl, ← ih.1]
      apply altP1Part_rot
      intro c c' hc hc'
      unfold tauO tauE
      rw [phase_snoc_two] at hc hc' ⊢
      rw [parentsAt_append_singleton]
      exact identE (parentsAt u) (parentsAt_valid u) (phase u == 1) Digit.two (Or.inr rfl) _ (by simp) c c' hc hc'

theorem altRot_step_three (u : Word) (hb : ¬ IsBase (u ++ [.three])) (ih : AltRotAt u) : AltRotAt (u ++ [.three]) := by
  have hsw' : swapW (u ++ [.three]) = swapW u ++ [.two] := FLatticePaper.Tiles.Standard.swapW_snoc_three u
  have hsw : ¬ IsBase (swapW u ++ [.two]) := hsw' ▸ FLatticePaper.Tiles.Standard.nonbase_swap hb
  have hG := FLatticePaper.Tiles.Standard.good_and_rot (u ++ [.three])
  have h3 : ¬ ∀ d ∈ u ++ [.three], d = Digit.three := fun h => hb (Or.inr (Or.inl h))
  have h2 : ¬ ∀ d ∈ u ++ [.three], d = Digit.two := fun h => hb (Or.inr (Or.inr h))
  have h1' := hG.2.1.resolve_left h3
  have h2' := hG.2.2.resolve_left h2
  rw [hsw'] at h1' h2'
  have hV := parentsAt_valid (u ++ [.three])
  have hpar : parentsAt (swapW u ++ [.two]) =
      ⟨(parentsAt (u ++ [.three])).even.rotate, (parentsAt (u ++ [.three])).odd.rotate⟩ := by
    rw [← hsw', FLatticePaper.Tiles.Standard.parentsAt_swapW]
    rfl
  have hph : phase (swapW u ++ [.two]) = phase (u ++ [.three]) := by
    rw [← hsw']
    exact FLatticePaper.Tiles.Standard.phase_swapW _
  unfold AltRotAt
  rw [hsw', altOddTile_of_not_base B hb, altEvenTile_of_not_base B hb, altOddTile_of_not_base B hsw,
    altEvenTile_of_not_base B hsw, altOddPieces_snoc, altOddPieces_snoc, altEvenPieces_snoc, altEvenPieces_snoc, hpar,
    hph]
  refine ⟨?_, ?_⟩
  · rw [rot_union, shift_union]
    congr 1
    · unfold tauO
      cases ho : (phase (u ++ [.three]) == 1)
      · exact rot_oddStd_false _ _ _ _ _ _ hV.odd_parity hV.even_parity h1' h2'
      · exact rot_oddStd_true _ _ _ _ _ _ hV.odd_parity hV.even_parity h1' h2'
    · rw [show (altRegs B (u ++ [.three])).2 = altEvenTile B u by rw [altRegs_snoc]; rfl,
        show (altRegs B (swapW u ++ [.two])).1 = altOddTile B (swapW u) by rw [altRegs_snoc]; rfl, ← ih.2]
      apply altQ1Part_rot
      intro c c' hc hc'
      unfold tauO tauE
      rw [phase_snoc_three] at hc hc' ⊢
      rw [parentsAt_append_singleton]
      exact identO (parentsAt u) (parentsAt_valid u) (phase u == 1) Digit.three (Or.inr rfl) _ (by simp) c c' hc hc'
  · rw [rot_union, shift_union]
    congr 1
    · unfold tauE
      cases ho : (phase (u ++ [.three]) == 1)
      · exact rot_evenStd_false _ _ _ _ _ _ hV.odd_parity hV.even_parity h1' h2'
      · exact rot_evenStd_true _ _ _ _ _ _ hV.odd_parity hV.even_parity h1' h2'
    · simp [altQ1Part, altP1Part, altQ1Coeff, altP1Coeff, rot_empty, shift_empty]

/-- **Item (1) of `lemma:alternate_tile_properties`, rotation, for every word.** The rotation of the alternate odd child of `w`,
translated by `tauO w`, is the alternate even child of the swapped word, and the rotation of the alternate even child,
translated by `tauE w`, is the alternate odd child of the swapped word. -/
theorem altRot (w : Word) : AltRotAt w := by
  induction w using List.reverseRecOn with
  | nil => exact altRot_nil
  | append_singleton u x ih =>
    by_cases hb : IsBase (u ++ [x])
    · exact altRot_base _ hb
    · cases x
      · exact altRot_step_one u hb ih
      · exact altRot_step_two u hb ih
      · exact altRot_step_three u hb ih

/-! ### Item (1) in the forms of `SurgicalAltTiles`: rotation with the lower-left translation, and symmetry -/

theorem isLowerLeftPt_unique {S : Set GInt} {a b : GInt} (ha : IsLowerLeftPt S a) (hb : IsLowerLeftPt S b) : a = b := by
  have h1 := ha.2 b hb.1
  have h2 := hb.2 a ha.1
  unfold lowerLexLe at h1 h2
  ext <;> omega

theorem isLowerLeftPt_shift {T : Tile} {c v : GInt} (h : IsLowerLeftPt {x | x ∈ T.toList} c) :
    IsLowerLeftPt {x | x ∈ (shift T v).toList} (c + v) := by
  obtain ⟨hc, hle⟩ := h
  simp only [Set.mem_setOf_eq, Finset.mem_toList] at hc hle ⊢
  refine ⟨mem_shift.2 (by simpa using hc), fun x hx => ?_⟩
  have := hle (x - v) (mem_shift.1 hx)
  unfold lowerLexLe at this ⊢
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at this ⊢
  omega

/-- The rotation identity with the translation fixed by the lower-left vertices, from an explicit translation. -/
theorem shift_lowerLeft_of_eq {A B : Tile} {τ : Site} (h : shift A τ = B) :
    ∀ c c' : GInt, lowerLeftList A.toList = some c → lowerLeftList B.toList = some c' → shift A (c' - c) = B := by
  intro c c' hc hc'
  have h1 := isLowerLeftPt_shift (v := τ) (lowerLeftList_isLowerLeft _ _ hc)
  rw [h] at h1
  have h2 := lowerLeftList_isLowerLeft _ _ hc'
  have e := isLowerLeftPt_unique h2 h1
  rw [e, add_sub_cancel_left]
  exact h

/-- **Item (1), rotation (`AltItem1Rotation`), for every word**, with the base alternates of the text. -/
theorem altItem1Rotation (w : Word) : AltItem1Rotation B w :=
  ⟨shift_lowerLeft_of_eq (altRot w).1, shift_lowerLeft_of_eq (altRot w).2⟩

theorem swapW_swapW (w : Word) : swapW (swapW w) = w := FLatticePaper.Farey.swapMap_swapMap w

theorem mem_rot_rot {T : Tile} {x : Site} : x ∈ rot (rot T) ↔ (-x.1, -x.2) ∈ T := by
  rw [FLatticePaper.Tiles.Standard.mem_rot, FLatticePaper.Tiles.Standard.mem_rot]

/-- A tile that is a translate of its double rotation is 180-degree symmetric. -/
theorem symmetric_of_rot_rot {T : Tile} {s : Site} (h : shift (rot (rot T)) s = T) : AltItem1Symmetric T := by
  refine ⟨s, fun y => ?_⟩
  conv_lhs => rw [← h]
  rw [mem_shift, mem_rot_rot]
  have e : ((-(y - s).1, -(y - s).2) : Site) = (s.1 - y.1, s.2 - y.2) := by
    ext <;> simp
  rw [e]

/-- **Item (1), symmetry, for every word**: both alternate children are 180-degree symmetric. -/
theorem altItem1Symmetric (w : Word) : AltItem1Symmetric (altOddTile B w) ∧ AltItem1Symmetric (altEvenTile B w) := by
  have h1 := altRot w
  have h2 := altRot (swapW w)
  unfold AltRotAt at h1 h2
  rw [swapW_swapW] at h2
  constructor
  · apply symmetric_of_rot_rot (s := mulI (tauO w) + tauE (swapW w))
    have e : shift (rot (shift (rot (altOddTile B w)) (tauO w))) (tauE (swapW w)) =
        shift (rot (altEvenTile B (swapW w))) (tauE (swapW w)) := by rw [h1.1]
    rw [h2.2, rot_shift, shift_shift] at e
    exact e
  · apply symmetric_of_rot_rot (s := mulI (tauE w) + tauO (swapW w))
    have e : shift (rot (shift (rot (altEvenTile B w)) (tauE w))) (tauO (swapW w)) =
        shift (rot (altOddTile B (swapW w))) (tauO (swapW w)) := by rw [h1.2]
    rw [h2.1, rot_shift, shift_shift] at e
    exact e

end FLatticePaper.Tiles.AltRotStep
