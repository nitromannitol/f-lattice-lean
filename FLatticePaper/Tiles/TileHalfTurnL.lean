import FLatticePaper.Tiles.TileHalfTurnAlt
import FLatticePaper.Tiles.ConnectedL

/-! # The half-turn of the L-corrected odometers (proof of (b) of `lemma:tile-odometer-existence`, Cases 2 and 4)

The half-turn `z ↦ C - z` about the centre `C` of the even child `T(q₀)` of a word `u = w₁ s 3^k` sends the pieces of the even
L-correction `o^{L,+}` to those of `o^{L,-}` (`evenLPieces`), piece by piece in the order of the lists: the stems (copies of
`T(p₂)`), the bridge (`T(q₂)`) and the heads (copies of the alternate `T̂(p₂)`). The offsets add up to `C - C_r` and the affine
factors to `a_{q₀,2} - a_r` for the parent `r` of each piece. With the half-turn identities of the parents,
`TileHalfTurnGlue.glue_halfTurn` gives `2(o^{L,-}(C - z) - o^{L,+}(z)) = -2 a_{q₀,2}ᵀz + K`. This file has the relations of the
offsets and affine factors at the prefixes `w₁ s` that are not `2^j`. -/

namespace FLatticePaper.Tiles.TileHalfTurnL

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.JointGlue (pieceVal goodPart)
open FLatticePaper.Tiles.SurgicalWeak (regOdo regsAt)
open FLatticePaper.Tiles.SurgicalDict (offsetP0 offsetQ0)
open FLatticePaper.Tiles.ConnectedAltL (eStemPos eHeadPos oStemPos oHeadPos)
open FLatticePaper.Tiles.TileHalfTurnStd (RawHT)

/-! ### The parents after the trailing `3`s -/

theorem parents_strip_three (u : Word) :
    parentsAt u = ⟨(parentsAt (stripTrailing Digit.three u)).odd,
      ⟨(parentsAt (stripTrailing Digit.three u)).even.num +
          2 * (trailingCount Digit.three u : ℤ) * (parentsAt (stripTrailing Digit.three u)).odd.num,
        (parentsAt (stripTrailing Digit.three u)).even.den +
          2 * (trailingCount Digit.three u : ℤ) * (parentsAt (stripTrailing Digit.three u)).odd.den⟩⟩ := by
  conv_lhs => rw [← JointRot.strip_append_replicate Digit.three u]
  exact JointRot.parents_append_threes _ _

theorem w1Odd_strip_three (u : Word) : W1Odd u = W1Odd (stripTrailing Digit.three u) := by
  conv_lhs => rw [← JointRot.strip_append_replicate Digit.three u]
  exact JointRot.W1Odd_append_replicate _ _ _ (by decide)

/-- The offset of the bridge of the even L-correction. -/
def eBridgePos (u : Word) (plus : Bool) : Site :=
  let K := evenKCoeff (W1Odd u) plus (decide ((stripTrailing Digit.three u).getLast? = some Digit.two))
  evenLInitOff u plus + altOff (stripTrailing Digit.three u) ((trailingCount Digit.three u : ℤ) • K.1 + K.2.1)

/-- The affine factor of a piece of the even L-correction at the coefficient vector `c`. -/
def eAffAt (u : Word) (plus : Bool) (c : SurgicalAlt.AltCoeff) : Site :=
  evenLInitAff u plus + altAff (stripTrailing Digit.three u) c

/-- The coefficient vector of the stem `j`. -/
def eStemC (u : Word) (plus : Bool) (j : ℕ) : SurgicalAlt.AltCoeff :=
  (j : ℤ) • (evenKCoeff (W1Odd u) plus (decide ((stripTrailing Digit.three u).getLast? = some Digit.two))).1

/-- The coefficient vector of the bridge. -/
def eBridgeC (u : Word) (plus : Bool) : SurgicalAlt.AltCoeff :=
  let K := evenKCoeff (W1Odd u) plus (decide ((stripTrailing Digit.three u).getLast? = some Digit.two))
  (trailingCount Digit.three u : ℤ) • K.1 + K.2.1

/-- The coefficient vector of the head `i`. -/
def eHeadC (u : Word) (plus : Bool) (i : ℕ) : SurgicalAlt.AltCoeff :=
  let K := evenKCoeff (W1Odd u) plus (decide ((stripTrailing Digit.three u).getLast? = some Digit.two))
  (trailingCount Digit.three u : ℤ) • K.1 + K.2.1 + K.2.2.1 + ((i : ℤ) + 1) • K.2.2.2

set_option hygiene false in
/-- Unfolds the offsets of the even L-correction into the parents of the prefix and closes the identity. -/
macro "eL_alg" : tactic => `(tactic| (
  rw [parents_strip_three u]
  rw [w1Odd_strip_three u] at *
  rcases Bool.eq_false_or_eq_true (W1Odd (stripTrailing Digit.three u)) with hW | hW <;>
  rcases Bool.eq_false_or_eq_true (decide ((stripTrailing Digit.three u).getLast? = some Digit.two)) with hs | hs <;>
  simp only [hW, hs, evenKCoeff, ↓reduceIte, Bool.false_eq_true] <;> ext <;>
  simp [SurgicalAlt.coeffOff, SurgicalAlt.coeffAffine, texV1Odd, texV1Even, texV2, offsetA, Parents.current,
    Parents.combine] <;> ring))

theorem eStem_rel (u : Word) (j : ℕ) :
    eStemPos u false j = TileHalfTurnStd.cEven ((parentsAt u).current .even) -
      TileHalfTurnStd.cOdd (parentsAt (stripTrailing Digit.three u)).odd - eStemPos u true j := by
  simp only [eStemPos, evenLInitOff, q0Off, offsetQ0, altOff, vP1, vP2, vQ1, vQ2, TileHalfTurnStd.cEven,
    TileHalfTurnStd.cOdd, if_true, if_false, Bool.false_eq_true]
  eL_alg

theorem eBridge_rel (u : Word) :
    eBridgePos u false = TileHalfTurnStd.cEven ((parentsAt u).current .even) -
      TileHalfTurnStd.cEven (parentsAt (stripTrailing Digit.three u)).even - eBridgePos u true := by
  simp only [eBridgePos, evenLInitOff, q0Off, offsetQ0, altOff, vP1, vP2, vQ1, vQ2, TileHalfTurnStd.cEven, if_true,
    if_false, Bool.false_eq_true]
  eL_alg

theorem eStemAff_rel (u : Word) (j : ℕ) :
    eAffAt u true (eStemC u true j) + eAffAt u false (eStemC u false j) =
      TileHalfTurnStd.aF ((parentsAt u).current .even) - TileHalfTurnStd.aF (parentsAt (stripTrailing Digit.three u)).odd := by
  simp only [eAffAt, eStemC, evenLInitAff, q0Aff, pairAffine, aP2, altAff, TileHalfTurnStd.aF, if_true, if_false,
    Bool.false_eq_true]
  eL_alg

theorem eBridgeAff_rel (u : Word) :
    eAffAt u true (eBridgeC u true) + eAffAt u false (eBridgeC u false) =
      TileHalfTurnStd.aF ((parentsAt u).current .even) -
        TileHalfTurnStd.aF (parentsAt (stripTrailing Digit.three u)).even := by
  simp only [eAffAt, eBridgeC, evenLInitAff, q0Aff, pairAffine, aP2, altAff, TileHalfTurnStd.aF, if_true, if_false,
    Bool.false_eq_true]
  eL_alg

set_option hygiene false in
/-- `eL_alg` for the heads: the prefix is `v d` with `d ≠ 3`, and the centre of the alternate parent is that of `v`. -/
macro "eL_alg_head" : tactic => `(tactic| (
  rw [parents_strip_three u]
  rw [w1Odd_strip_three u] at *
  rw [hpre]
  cases d with
  | three => exact absurd rfl hd
  | one =>
    simp only [W1Odd, JointRot.phase_snoc_one, CeilWords.parentsAt_snoc_one, List.getLast?_append,
      List.getLast?_singleton, Option.some_or, Option.some.injEq, reduceCtorEq, decide_false] at *
    rcases Bool.eq_false_or_eq_true (phase v == 1) with hW | hW <;>
    simp only [hW, evenKCoeff, ↓reduceIte, Bool.false_eq_true, Bool.not_true, Bool.not_false, beq_self_eq_true,
      Bool.true_eq_false] <;> ext <;>
    simp [SurgicalAlt.coeffOff, SurgicalAlt.coeffAffine, texV1Odd, texV1Even, texV2, offsetA, Parents.current,
      Parents.combine, W1Odd, hW] <;> ring
  | two =>
    simp only [W1Odd, JointRot.phase_snoc_two, CeilWords.parentsAt_snoc_two, List.getLast?_append,
      List.getLast?_singleton, Option.some_or, Option.some.injEq, decide_true] at *
    rcases Bool.eq_false_or_eq_true (phase v == 1) with hW | hW <;>
    simp only [hW, evenKCoeff, ↓reduceIte, Bool.false_eq_true, Bool.not_true, Bool.not_false, beq_self_eq_true,
      Bool.true_eq_false] <;> ext <;>
    simp [SurgicalAlt.coeffOff, SurgicalAlt.coeffAffine, texV1Odd, texV1Even, texV2, offsetA, Parents.current,
      Parents.combine, W1Odd, hW] <;> ring))

theorem eHead_rel (u v : Word) (d : Digit) (hd : d ≠ Digit.three) (hpre : stripTrailing Digit.three u = v ++ [d])
    (i : ℕ) :
    eHeadPos u false i = TileHalfTurnStd.cEven ((parentsAt u).current .even) - altD v true - eHeadPos u true i := by
  simp only [eHeadPos, evenLInitOff, q0Off, offsetQ0, altOff, altD, vP1, vP2, vQ1, vQ2, TileHalfTurnStd.cEven, if_true,
    if_false, Bool.false_eq_true]
  eL_alg_head

theorem eHeadAff_rel (u v : Word) (d : Digit) (hd : d ≠ Digit.three) (hpre : stripTrailing Digit.three u = v ++ [d])
    (i : ℕ) :
    eAffAt u true (eHeadC u true i) + eAffAt u false (eHeadC u false i) =
      TileHalfTurnStd.aF ((parentsAt u).current .even) - altE v := by
  simp only [eAffAt, eHeadC, evenLInitAff, q0Aff, pairAffine, aP2, aQ2, altAff, altE, TileHalfTurnStd.aF, if_true,
    if_false, Bool.false_eq_true]
  eL_alg_head

/-! ### The half-turn of the even L-corrected odometers -/

/-- The even L decomposition at a prefix that is not `2^j`: the stems, the bridge, the heads, with no exceptional point. -/
theorem eLP_eq (S : SurgicalWeak.WeakData) (pO pE aO aE : Word → PartialOdometer) (u : Word) (b elong : Bool)
    (hreg : (!(stripTrailing Digit.three u).isEmpty &&
      (stripTrailing Digit.three u).all (fun d => decide (d = Digit.two))) = false) :
    evenLPieces S pO pE aO aE u b elong =
      (List.range (trailingCount Digit.three u + 1)).map (fun j =>
        stdPiece (regOdo S pO pE (regsAt (stripTrailing Digit.three u)).1 true) (eStemPos u b j) (eAffAt u b (eStemC u b j))) ++
      [stdPiece (regOdo S pO pE (regsAt (stripTrailing Digit.three u)).2 false) (eBridgePos u b) (eAffAt u b (eBridgeC u b))] ++
      (List.range (2 * (trailingCount Digit.three u + 1) - (if elong then 0 else 1))).map (fun m =>
        stdPiece (regOdo S aO aE (regsAt (stripTrailing Digit.three u)).1 true) (eHeadPos u b m) (eAffAt u b (eHeadC u b m))) := by
  unfold evenLPieces
  simp only [hreg, Bool.false_and, Bool.false_eq_true, ↓reduceIte, List.append_nil]
  congr 1

theorem get_left {α : Type*} (l1 l3 : List α) (x : α) (i : ℕ) (h : i < l1.length) :
    (l1 ++ [x] ++ l3)[i]? = l1[i]? := by
  rw [List.append_assoc, List.getElem?_append_left h]

theorem get_mid {α : Type*} (l1 l3 : List α) (x : α) {n : ℕ} (h : l1.length = n) : (l1 ++ [x] ++ l3)[n]? = some x := by
  subst h
  rw [List.append_assoc, List.getElem?_append_right le_rfl]
  simp

theorem get_right {α : Type*} (l1 l3 : List α) (x : α) {n : ℕ} (h : l1.length = n) (m : ℕ) :
    (l1 ++ [x] ++ l3)[n + 1 + m]? = l3[m]? := by
  subst h
  rw [List.append_assoc, List.getElem?_append_right (by omega)]
  simp [show l1.length + 1 + m - l1.length = m + 1 by omega]

/-- **The half-turn of the even L-corrected odometers** at a prefix that is not `2^j`: `z ↦ C - z` about the centre of the even
child sends `o^{L,b}` to `o^{L,!b}` with slope `a_{q₀,2}`, up to a constant. -/
theorem lHalfTurn_even (S : SurgicalWeak.WeakData) (pO pE aO aE : Word → PartialOdometer) (u v : Word) (d : Digit)
    (hd : d ≠ Digit.three) (hpre : stripTrailing Digit.three u = v ++ [d])
    (hreg : (!(stripTrailing Digit.three u).isEmpty &&
      (stripTrailing Digit.three u).all (fun d => decide (d = Digit.two))) = false) (b elong : Bool)
    (Ls Lt : PartialOdometer) (hRs : RespectsPieces Ls (evenLPieces S pO pE aO aE u b elong))
    (hRt : RespectsPieces Lt (evenLPieces S pO pE aO aE u (!b) elong))
    (hconn : (overlapGraph (goodPart (evenLPieces S pO pE aO aE u b elong))).Connected)
    (hS : RawHT (regOdo S pO pE (regsAt (stripTrailing Digit.three u)).1 true)
      (TileHalfTurnStd.cOdd (parentsAt (stripTrailing Digit.three u)).odd)
      (TileHalfTurnStd.aF (parentsAt (stripTrailing Digit.three u)).odd))
    (hB : RawHT (regOdo S pO pE (regsAt (stripTrailing Digit.three u)).2 false)
      (TileHalfTurnStd.cEven (parentsAt (stripTrailing Digit.three u)).even)
      (TileHalfTurnStd.aF (parentsAt (stripTrailing Digit.three u)).even))
    (hH : RawHT (regOdo S aO aE (regsAt (stripTrailing Digit.three u)).1 true) (altD v true) (altE v)) :
    ∃ K : ℤ, ∀ z ∈ Ls.dom, TileHalfTurnStd.cEven ((parentsAt u).current .even) - z ∈ Lt.dom ∧
      2 * (Lt.val (TileHalfTurnStd.cEven ((parentsAt u).current .even) - z) - Ls.val z) =
        dotS (-(2 : ℤ) • TileHalfTurnStd.aF ((parentsAt u).current .even)) z + K := by
  refine TileHalfTurnGlue.glue_halfTurn _ _ Ls Lt hRs hRt (JointGlue.evenLPieces_covered _ _ _ _ _ _ _ _) hconn id _ _ ?_
  intro i p hp
  simp only [id]
  rw [eLP_eq S pO pE aO aE u b elong hreg] at hp
  rw [eLP_eq S pO pE aO aE u (!b) elong hreg]
  set k := trailingCount Digit.three u
  have hlen : ∀ c : Bool, ((List.range (k + 1)).map (fun j =>
      stdPiece (regOdo S pO pE (regsAt (stripTrailing Digit.three u)).1 true) (eStemPos u c j)
        (eAffAt u c (eStemC u c j)))).length = k + 1 := fun c => by simp
  rcases Nat.lt_or_ge i (k + 1) with hi | hi
  · rw [get_left _ _ _ i (by rw [hlen]; exact hi), List.getElem?_map, List.getElem?_range hi] at hp
    simp only [Option.map_some, Option.some.injEq] at hp
    subst hp
    refine ⟨_, by rw [get_left _ _ _ i (by rw [hlen]; exact hi), List.getElem?_map, List.getElem?_range hi]; rfl, ?_⟩
    refine TileHalfTurnGlue.std_pair _ _ _ hS _ _ _ _ _ _ ?_ ?_
    · cases b
      · exact TileHalfTurnAlt.flip_off (eStem_rel u i)
      · exact eStem_rel u i
    · cases b
      · exact (add_comm _ _).trans (eStemAff_rel u i)
      · exact eStemAff_rel u i
  rcases Nat.lt_or_ge i (k + 2) with hi2 | hi2
  · have hik : i = k + 1 := by omega
    subst hik
    rw [get_mid _ _ _ (hlen b), Option.some.injEq] at hp
    subst hp
    refine ⟨_, get_mid _ _ _ (hlen (!b)), ?_⟩
    refine TileHalfTurnGlue.std_pair _ _ _ hB _ _ _ _ _ _ ?_ ?_
    · cases b
      · exact TileHalfTurnAlt.flip_off (eBridge_rel u)
      · exact eBridge_rel u
    · cases b
      · exact (add_comm _ _).trans (eBridgeAff_rel u)
      · exact eBridgeAff_rel u
  · obtain ⟨m, rfl⟩ : ∃ m, i = k + 1 + 1 + m := ⟨i - (k + 2), by omega⟩
    rw [get_right _ _ _ (hlen b)] at hp
    rw [get_right _ _ _ (hlen (!b))]
    rcases Nat.lt_or_ge m (2 * (k + 1) - (if elong then 0 else 1)) with hm | hm
    · rw [List.getElem?_map, List.getElem?_range hm] at hp ⊢
      simp only [Option.map_some, Option.some.injEq] at hp
      subst hp
      refine ⟨_, rfl, ?_⟩
      refine TileHalfTurnGlue.std_pair _ _ _ hH _ _ _ _ _ _ ?_ ?_
      · cases b
        · exact TileHalfTurnAlt.flip_off (eHead_rel u v d hd hpre m)
        · exact eHead_rel u v d hd hpre m
      · cases b
        · exact (add_comm _ _).trans (eHeadAff_rel u v d hd hpre m)
        · exact eHeadAff_rel u v d hd hpre m
    · rw [List.getElem?_map, List.getElem?_eq_none_iff.2 (by simpa using hm)] at hp
      simp at hp

/-! ### The odd L-corrections -/

theorem parents_strip_two (u : Word) :
    parentsAt u = ⟨⟨(parentsAt (stripTrailing Digit.two u)).odd.num +
          (trailingCount Digit.two u : ℤ) * (parentsAt (stripTrailing Digit.two u)).even.num,
        (parentsAt (stripTrailing Digit.two u)).odd.den +
          (trailingCount Digit.two u : ℤ) * (parentsAt (stripTrailing Digit.two u)).even.den⟩,
      (parentsAt (stripTrailing Digit.two u)).even⟩ := by
  conv_lhs => rw [← JointRot.strip_append_replicate Digit.two u]
  exact JointRot.parents_append_twos _ _

theorem w1Odd_strip_two (u : Word) : W1Odd u = W1Odd (stripTrailing Digit.two u) := by
  conv_lhs => rw [← JointRot.strip_append_replicate Digit.two u]
  exact JointRot.W1Odd_append_replicate _ _ _ (by decide)

/-- The offset of the bridge of the odd L-correction (off the prefixes `3^j`). -/
def oBridgePos (u : Word) (plus : Bool) : Site :=
  let K := oddKCoeff (W1Odd u) plus
  oddLInitOff u plus + altOff (stripTrailing Digit.two u) ((trailingCount Digit.two u : ℤ) • K.1 + K.2.1)

/-- The affine factor of a piece of the odd L-correction at the coefficient vector `c`. -/
def oAffAt (u : Word) (plus : Bool) (c : SurgicalAlt.AltCoeff) : Site :=
  oddLInitAff u plus + altAff (stripTrailing Digit.two u) c

def oStemC (u : Word) (plus : Bool) (j : ℕ) : SurgicalAlt.AltCoeff := (j : ℤ) • (oddKCoeff (W1Odd u) plus).1

def oBridgeC (u : Word) (plus : Bool) : SurgicalAlt.AltCoeff :=
  let K := oddKCoeff (W1Odd u) plus
  (trailingCount Digit.two u : ℤ) • K.1 + K.2.1

def oHeadC (u : Word) (plus : Bool) (i : ℕ) : SurgicalAlt.AltCoeff :=
  let K := oddKCoeff (W1Odd u) plus
  (trailingCount Digit.two u : ℤ) • K.1 + K.2.1 + K.2.2.1 + ((i : ℤ) + 1) • K.2.2.2

set_option hygiene false in
/-- Unfolds the offsets of the odd L-correction into the parents of the prefix and closes the identity. -/
macro "oL_alg" : tactic => `(tactic| (
  rw [parents_strip_two u]
  rw [w1Odd_strip_two u] at *
  rcases Bool.eq_false_or_eq_true (W1Odd (stripTrailing Digit.two u)) with hW | hW <;>
  simp only [hW, oddKCoeff, ↓reduceIte, Bool.false_eq_true] <;> ext <;>
  simp [SurgicalAlt.coeffOff, SurgicalAlt.coeffAffine, texV1Odd, texV1Even, texV2, offsetA, Parents.current,
    Parents.combine] <;> ring))

theorem oStem_rel (u : Word) (j : ℕ) :
    oStemPos u false j = TileHalfTurnStd.cOdd ((parentsAt u).current .odd) -
      TileHalfTurnStd.cEven (parentsAt (stripTrailing Digit.two u)).even - oStemPos u true j := by
  simp only [oStemPos, oddLInitOff, p0Off, offsetP0, altOff, vP1, vP2, vQ1, vQ2, TileHalfTurnStd.cEven,
    TileHalfTurnStd.cOdd]
  oL_alg

theorem oBridge_rel (u : Word) :
    oBridgePos u false = TileHalfTurnStd.cOdd ((parentsAt u).current .odd) -
      TileHalfTurnStd.cOdd (parentsAt (stripTrailing Digit.two u)).odd - oBridgePos u true := by
  simp only [oBridgePos, oddLInitOff, p0Off, offsetP0, altOff, vP1, vP2, vQ1, vQ2, TileHalfTurnStd.cOdd]
  oL_alg

theorem oStemAff_rel (u : Word) (j : ℕ) :
    oAffAt u true (oStemC u true j) + oAffAt u false (oStemC u false j) =
      TileHalfTurnStd.aF ((parentsAt u).current .odd) - TileHalfTurnStd.aF (parentsAt (stripTrailing Digit.two u)).even := by
  simp only [oAffAt, oStemC, oddLInitAff, p0Aff, pairAffine, altAff, TileHalfTurnStd.aF, if_true, if_false,
    Bool.false_eq_true]
  oL_alg

theorem oBridgeAff_rel (u : Word) :
    oAffAt u true (oBridgeC u true) + oAffAt u false (oBridgeC u false) =
      TileHalfTurnStd.aF ((parentsAt u).current .odd) - TileHalfTurnStd.aF (parentsAt (stripTrailing Digit.two u)).odd := by
  simp only [oAffAt, oBridgeC, oddLInitAff, p0Aff, pairAffine, altAff, TileHalfTurnStd.aF, if_true, if_false,
    Bool.false_eq_true]
  oL_alg

set_option hygiene false in
/-- `oL_alg` for the heads: the prefix is `v d` with `d ≠ 2`. -/
macro "oL_alg_head" : tactic => `(tactic| (
  rw [parents_strip_two u]
  rw [w1Odd_strip_two u] at *
  rw [hpre]
  cases d with
  | two => exact absurd rfl hd
  | one =>
    simp only [W1Odd, JointRot.phase_snoc_one, CeilWords.parentsAt_snoc_one] at *
    rcases Bool.eq_false_or_eq_true (phase v == 1) with hW | hW <;>
    simp only [hW, oddKCoeff, ↓reduceIte, Bool.false_eq_true, Bool.not_true, Bool.not_false, beq_self_eq_true,
      Bool.true_eq_false] <;> ext <;>
    simp [SurgicalAlt.coeffOff, SurgicalAlt.coeffAffine, texV1Odd, texV1Even, texV2, offsetA, Parents.current,
      Parents.combine, W1Odd, hW] <;> ring
  | three =>
    simp only [W1Odd, JointRot.phase_snoc_three, CeilWords.parentsAt_snoc_three] at *
    rcases Bool.eq_false_or_eq_true (phase v == 1) with hW | hW <;>
    simp only [hW, oddKCoeff, ↓reduceIte, Bool.false_eq_true, Bool.not_true, Bool.not_false, beq_self_eq_true,
      Bool.true_eq_false] <;> ext <;>
    simp [SurgicalAlt.coeffOff, SurgicalAlt.coeffAffine, texV1Odd, texV1Even, texV2, offsetA, Parents.current,
      Parents.combine, W1Odd, hW] <;> ring))

theorem oHead_rel (u v : Word) (d : Digit) (hd : d ≠ Digit.two) (hpre : stripTrailing Digit.two u = v ++ [d]) (i : ℕ) :
    oHeadPos u false i = TileHalfTurnStd.cOdd ((parentsAt u).current .odd) - altD v false - oHeadPos u true i := by
  simp only [oHeadPos, oddLInitOff, p0Off, offsetP0, altOff, altD, vP1, vP2, vQ1, vQ2, TileHalfTurnStd.cOdd]
  oL_alg_head

theorem oHeadAff_rel (u v : Word) (d : Digit) (hd : d ≠ Digit.two) (hpre : stripTrailing Digit.two u = v ++ [d])
    (i : ℕ) :
    oAffAt u true (oHeadC u true i) + oAffAt u false (oHeadC u false i) =
      TileHalfTurnStd.aF ((parentsAt u).current .odd) - altE v := by
  simp only [oAffAt, oHeadC, oddLInitAff, p0Aff, pairAffine, aP2, aQ2, altAff, altE, TileHalfTurnStd.aF, if_true,
    if_false, Bool.false_eq_true]
  oL_alg_head

/-- The odd L decomposition at a prefix that is not `3^j`: the stems, the bridge, the heads, with no exceptional point. -/
theorem oLP_eq (S : SurgicalWeak.WeakData) (pO pE aO aE : Word → PartialOdometer) (u : Word) (b elong : Bool)
    (hreg : (!(stripTrailing Digit.two u).isEmpty &&
      (stripTrailing Digit.two u).all (fun d => decide (d = Digit.three))) = false) :
    oddLPieces S pO pE aO aE u b elong =
      (List.range (trailingCount Digit.two u + 1)).map (fun j =>
        stdPiece (regOdo S pO pE (regsAt (stripTrailing Digit.two u)).2 false) (oStemPos u b j) (oAffAt u b (oStemC u b j))) ++
      [stdPiece (regOdo S pO pE (regsAt (stripTrailing Digit.two u)).1 true) (oBridgePos u b) (oAffAt u b (oBridgeC u b))] ++
      (List.range (2 * (trailingCount Digit.two u + 1) - (if elong then 0 else 1))).map (fun m =>
        stdPiece (regOdo S aO aE (regsAt (stripTrailing Digit.two u)).2 false) (oHeadPos u b m) (oAffAt u b (oHeadC u b m))) := by
  unfold oddLPieces
  simp only [hreg, LCorrections.oddBridgeShift, Bool.false_and, Bool.false_eq_true, ↓reduceIte, add_zero]
  congr 1

/-- **The half-turn of the odd L-corrected odometers** at a prefix that is not `3^j`: `z ↦ C - z` about the centre of the odd
child sends `o^{L,b}` to `o^{L,!b}` with slope `a_{p₀,2}`, up to a constant. -/
theorem lHalfTurn_odd (S : SurgicalWeak.WeakData) (pO pE aO aE : Word → PartialOdometer) (u v : Word) (d : Digit)
    (hd : d ≠ Digit.two) (hpre : stripTrailing Digit.two u = v ++ [d])
    (hreg : (!(stripTrailing Digit.two u).isEmpty &&
      (stripTrailing Digit.two u).all (fun d => decide (d = Digit.three))) = false) (b elong : Bool)
    (Ls Lt : PartialOdometer) (hRs : RespectsPieces Ls (oddLPieces S pO pE aO aE u b elong))
    (hRt : RespectsPieces Lt (oddLPieces S pO pE aO aE u (!b) elong))
    (hconn : (overlapGraph (goodPart (oddLPieces S pO pE aO aE u b elong))).Connected)
    (hS : RawHT (regOdo S pO pE (regsAt (stripTrailing Digit.two u)).2 false)
      (TileHalfTurnStd.cEven (parentsAt (stripTrailing Digit.two u)).even)
      (TileHalfTurnStd.aF (parentsAt (stripTrailing Digit.two u)).even))
    (hB : RawHT (regOdo S pO pE (regsAt (stripTrailing Digit.two u)).1 true)
      (TileHalfTurnStd.cOdd (parentsAt (stripTrailing Digit.two u)).odd)
      (TileHalfTurnStd.aF (parentsAt (stripTrailing Digit.two u)).odd))
    (hH : RawHT (regOdo S aO aE (regsAt (stripTrailing Digit.two u)).2 false) (altD v false) (altE v)) :
    ∃ K : ℤ, ∀ z ∈ Ls.dom, TileHalfTurnStd.cOdd ((parentsAt u).current .odd) - z ∈ Lt.dom ∧
      2 * (Lt.val (TileHalfTurnStd.cOdd ((parentsAt u).current .odd) - z) - Ls.val z) =
        dotS (-(2 : ℤ) • TileHalfTurnStd.aF ((parentsAt u).current .odd)) z + K := by
  refine TileHalfTurnGlue.glue_halfTurn _ _ Ls Lt hRs hRt (JointGlue.oddLPieces_covered _ _ _ _ _ _ _ _) hconn id _ _ ?_
  intro i p hp
  simp only [id]
  rw [oLP_eq S pO pE aO aE u b elong hreg] at hp
  rw [oLP_eq S pO pE aO aE u (!b) elong hreg]
  set k := trailingCount Digit.two u
  have hlen : ∀ c : Bool, ((List.range (k + 1)).map (fun j =>
      stdPiece (regOdo S pO pE (regsAt (stripTrailing Digit.two u)).2 false) (oStemPos u c j)
        (oAffAt u c (oStemC u c j)))).length = k + 1 := fun c => by simp
  rcases Nat.lt_or_ge i (k + 1) with hi | hi
  · rw [get_left _ _ _ i (by rw [hlen]; exact hi), List.getElem?_map, List.getElem?_range hi] at hp
    simp only [Option.map_some, Option.some.injEq] at hp
    subst hp
    refine ⟨_, by rw [get_left _ _ _ i (by rw [hlen]; exact hi), List.getElem?_map, List.getElem?_range hi]; rfl, ?_⟩
    refine TileHalfTurnGlue.std_pair _ _ _ hS _ _ _ _ _ _ ?_ ?_
    · cases b
      · exact TileHalfTurnAlt.flip_off (oStem_rel u i)
      · exact oStem_rel u i
    · cases b
      · exact (add_comm _ _).trans (oStemAff_rel u i)
      · exact oStemAff_rel u i
  rcases Nat.lt_or_ge i (k + 2) with hi2 | hi2
  · have hik : i = k + 1 := by omega
    subst hik
    rw [get_mid _ _ _ (hlen b), Option.some.injEq] at hp
    subst hp
    refine ⟨_, get_mid _ _ _ (hlen (!b)), ?_⟩
    refine TileHalfTurnGlue.std_pair _ _ _ hB _ _ _ _ _ _ ?_ ?_
    · cases b
      · exact TileHalfTurnAlt.flip_off (oBridge_rel u)
      · exact oBridge_rel u
    · cases b
      · exact (add_comm _ _).trans (oBridgeAff_rel u)
      · exact oBridgeAff_rel u
  · obtain ⟨m, rfl⟩ : ∃ m, i = k + 1 + 1 + m := ⟨i - (k + 2), by omega⟩
    rw [get_right _ _ _ (hlen b)] at hp
    rw [get_right _ _ _ (hlen (!b))]
    rcases Nat.lt_or_ge m (2 * (k + 1) - (if elong then 0 else 1)) with hm | hm
    · rw [List.getElem?_map, List.getElem?_range hm] at hp ⊢
      simp only [Option.map_some, Option.some.injEq] at hp
      subst hp
      refine ⟨_, rfl, ?_⟩
      refine TileHalfTurnGlue.std_pair _ _ _ hH _ _ _ _ _ _ ?_ ?_
      · cases b
        · exact TileHalfTurnAlt.flip_off (oHead_rel u v d hd hpre m)
        · exact oHead_rel u v d hd hpre m
      · cases b
        · exact (add_comm _ _).trans (oHeadAff_rel u v d hd hpre m)
        · exact oHeadAff_rel u v d hd hpre m
    · rw [List.getElem?_map, List.getElem?_eq_none_iff.2 (by simpa using hm)] at hp
      simp at hp


end FLatticePaper.Tiles.TileHalfTurnL
