import FLatticePaper.Tiles.BinaryWords
import FLatticePaper.Tiles.BoundaryStrings

/-! Clause (d) of `lemma:standard_tile_properties`, at the level of letter-determined offsets.

The interface between a forward zero-one string (letters `F`) and a reversed one (letters `G`) is part of a stacked string
when the two agree on the letters `2, …, n` (`lemma:almost_palindrome` (3)). Then the offsets of the two strings are fixed by
the letter of the forward string: for `1 ≤ i < n`,
`plus i − minus i = s + (along F_i − rev-step (G_0, F_i))`, where `s = plus 0 − minus 0` is the initial offset.

The only algebra is the stacking identity `stacking_identity`, checked on the four letters. The positions are those of the
horizontal zero-one strings (`zeroOneHorizontalStep`, `zeroOneHorizontalReversedStep` of `BoundaryStrings`). -/

namespace FLatticePaper.Tiles.InterfaceStacked

open FLatticePaper.Tiles
open FLatticePaper.Farey

/-- The stacking identity: the forward step of `a` minus the reversed step from `e` to `a`, minus the reversed step from `a` to
`b`, plus the reversed step from `e` to `b`, vanishes for every triple of letters. -/
theorem stacking_identity (e a b : Letter) :
    zeroOneHorizontalStep a - zeroOneHorizontalReversedStep e a - zeroOneHorizontalReversedStep a b +
      zeroOneHorizontalReversedStep e b = 0 := by
  cases e <;> cases a <;> cases b <;> decide

/-- The interface offsets of a forward string `F` and a reversed string `G` agreeing on the letters `1 ≤ j < n` (0-based). -/
theorem interface_offsets (F G : BinaryWord) (s : Site) (plus minus : ℕ → Site) (n : ℕ)
    (hn : n ≤ F.length) (hn' : n ≤ G.length)
    (hplus : ∀ i, i + 1 < F.length → plus (i + 1) - plus i = zeroOneHorizontalStep (F.getD (i + 1) .p))
    (hminus : ∀ i, i + 1 < G.length →
      minus (i + 1) - minus i = zeroOneHorizontalReversedStep (G.getD i .p) (G.getD (i + 1) .p))
    (hstack : plus 0 - minus 0 = s)
    (hmatch : ∀ j, 1 ≤ j → j < n → F.getD j .p = G.getD j .p) :
    ∀ i, 1 ≤ i → i < n →
      plus i - minus i = s + (zeroOneHorizontalStep (F.getD i .p) -
        zeroOneHorizontalReversedStep (G.getD 0 .p) (F.getD i .p)) := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base =>
    intro h1n
    have hG1 : G.getD 1 .p = F.getD 1 .p := (hmatch 1 le_rfl h1n).symm
    have hp1 : plus 1 - plus 0 = zeroOneHorizontalStep (F.getD 1 .p) := hplus 0 (by omega)
    have hm1 : minus 1 - minus 0 = zeroOneHorizontalReversedStep (G.getD 0 .p) (G.getD 1 .p) :=
      hminus 0 (by omega)
    rw [hG1] at hm1
    have hp : plus 1 = plus 0 + zeroOneHorizontalStep (F.getD 1 .p) := by
      rw [← hp1]; abel
    have hm : minus 1 = minus 0 + zeroOneHorizontalReversedStep (G.getD 0 .p) (F.getD 1 .p) := by
      rw [← hm1]; abel
    rw [hp, hm, ← hstack]
    abel
  | succ i hi ih =>
    intro hin
    have hiN : i < n := by omega
    have ih' := ih hiN
    have hFi1 : i + 1 < F.length := by omega
    have hGi1 : i + 1 < G.length := by omega
    have hp1 : plus (i + 1) - plus i = zeroOneHorizontalStep (F.getD (i + 1) .p) := hplus i hFi1
    have hm1 : minus (i + 1) - minus i = zeroOneHorizontalReversedStep (G.getD i .p) (G.getD (i + 1) .p) :=
      hminus i hGi1
    have hGi : G.getD i .p = F.getD i .p := (hmatch i hi hiN).symm
    have hGi1 : G.getD (i + 1) .p = F.getD (i + 1) .p := (hmatch (i + 1) (by omega) hin).symm
    rw [hGi, hGi1] at hm1
    have hp : plus (i + 1) = plus i + zeroOneHorizontalStep (F.getD (i + 1) .p) := by
      rw [← hp1]; abel
    have hm : minus (i + 1) = minus i + zeroOneHorizontalReversedStep (F.getD i .p) (F.getD (i + 1) .p) := by
      rw [← hm1]; abel
    have key := stacking_identity (G.getD 0 .p) (F.getD i .p) (F.getD (i + 1) .p)
    rw [hp, hm]
    calc plus i + zeroOneHorizontalStep (F.getD (i + 1) .p) -
          (minus i + zeroOneHorizontalReversedStep (F.getD i .p) (F.getD (i + 1) .p))
        = (plus i - minus i) + (zeroOneHorizontalStep (F.getD (i + 1) .p) -
          zeroOneHorizontalReversedStep (F.getD i .p) (F.getD (i + 1) .p)) := by abel
      _ = (s + (zeroOneHorizontalStep (F.getD i .p) -
          zeroOneHorizontalReversedStep (G.getD 0 .p) (F.getD i .p))) +
          (zeroOneHorizontalStep (F.getD (i + 1) .p) -
          zeroOneHorizontalReversedStep (F.getD i .p) (F.getD (i + 1) .p)) := by rw [ih']
      _ = s + (zeroOneHorizontalStep (F.getD (i + 1) .p) -
          zeroOneHorizontalReversedStep (G.getD 0 .p) (F.getD (i + 1) .p)) := by
          have h2 : (zeroOneHorizontalStep (F.getD i .p) -
              zeroOneHorizontalReversedStep (G.getD 0 .p) (F.getD i .p)) +
              (zeroOneHorizontalStep (F.getD (i + 1) .p) -
              zeroOneHorizontalReversedStep (F.getD i .p) (F.getD (i + 1) .p)) =
              zeroOneHorizontalStep (F.getD (i + 1) .p) -
              zeroOneHorizontalReversedStep (G.getD 0 .p) (F.getD (i + 1) .p) := by
            have e1 : (zeroOneHorizontalStep (F.getD i .p) -
                zeroOneHorizontalReversedStep (G.getD 0 .p) (F.getD i .p)) +
                (zeroOneHorizontalStep (F.getD (i + 1) .p) -
                zeroOneHorizontalReversedStep (F.getD i .p) (F.getD (i + 1) .p)) =
                (zeroOneHorizontalStep (F.getD i .p) -
                zeroOneHorizontalReversedStep (G.getD 0 .p) (F.getD i .p) -
                zeroOneHorizontalReversedStep (F.getD i .p) (F.getD (i + 1) .p) +
                zeroOneHorizontalReversedStep (G.getD 0 .p) (F.getD (i + 1) .p)) +
                (zeroOneHorizontalStep (F.getD (i + 1) .p) -
                zeroOneHorizontalReversedStep (G.getD 0 .p) (F.getD (i + 1) .p)) := by abel
            rw [e1, key, zero_add]
          rw [add_assoc, h2]

/-- The letters of `slice2` are the letters of the word at the same index: `(slice2 w n)[j-1] = w[j]` for `1 ≤ j < n`. -/
theorem slice2_getD (w : BinaryWord) (n j : ℕ) (hj : 1 ≤ j) (hjn : j < n) :
    (slice2 w n).getD (j - 1) .p = w.getD j .p := by
  unfold slice2
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
  rw [if_pos (by omega), show 1 + (j - 1) = j by omega]

/-- The matching of `lemma:almost_palindrome` (3), read letter by letter for the quad words at the word `w0 ++ u`. -/
theorem quad_matching (w0 u : FLatticePaper.Farey.Word) :
    ((w0 ++ u).count .one % 2 = 0 → ∀ j, 1 ≤ j →
      j < min (quadAt w0 u).childP.length (quadAt w0 u).childQ.length →
        (quadAt w0 u).childP.getD j .p = (quadAt w0 u).childQ.reverse.getD j .p) ∧
    ((w0 ++ u).count .one % 2 = 1 → ∀ j, 1 ≤ j →
      j < min (quadAt w0 u).childP.length (quadAt w0 u).childQ.length →
        (quadAt w0 u).childQ.getD j .p = (quadAt w0 u).childP.reverse.getD j .p) := by
  have h3 := almost_palindrome_three w0 u
  dsimp only at h3
  constructor
  · intro hpar j hj hjn
    have h := (h3.1 hpar).1
    have e := congrArg (fun l => l.getD (j - 1) .p) h
    rw [slice2_getD _ _ j hj hjn, slice2_getD _ _ j hj hjn] at e
    exact e
  · intro hpar j hj hjn
    have h := (h3.2 hpar).1
    have e := congrArg (fun l => l.getD (j - 1) .p) h
    rw [slice2_getD _ _ j hj hjn, slice2_getD _ _ j hj hjn] at e
    exact e.symm

/-- Clause (d) for the even matching: the interface of the quad words `P = childP` (forward) and `Q` (reversed) is stacked,
with the offsets fixed by the letters of `P`, for any initial offset `s`. -/
theorem quad_stacked_even (w0 u : FLatticePaper.Farey.Word) (hpar : (w0 ++ u).count .one % 2 = 0)
    (s : Site) (plus minus : ℕ → Site)
    (hplus : ∀ i, i + 1 < (quadAt w0 u).childP.length →
      plus (i + 1) - plus i = zeroOneHorizontalStep ((quadAt w0 u).childP.getD (i + 1) .p))
    (hminus : ∀ i, i + 1 < (quadAt w0 u).childQ.reverse.length →
      minus (i + 1) - minus i = zeroOneHorizontalReversedStep ((quadAt w0 u).childQ.reverse.getD i .p)
        ((quadAt w0 u).childQ.reverse.getD (i + 1) .p))
    (hstack : plus 0 - minus 0 = s) :
    ∀ i, 1 ≤ i → i < min (quadAt w0 u).childP.length (quadAt w0 u).childQ.length →
      plus i - minus i = s + (zeroOneHorizontalStep ((quadAt w0 u).childP.getD i .p) -
        zeroOneHorizontalReversedStep ((quadAt w0 u).childQ.reverse.getD 0 .p)
          ((quadAt w0 u).childP.getD i .p)) := by
  have hn : min (quadAt w0 u).childP.length (quadAt w0 u).childQ.length ≤ (quadAt w0 u).childP.length :=
    min_le_left _ _
  have hn' : min (quadAt w0 u).childP.length (quadAt w0 u).childQ.length ≤
      (quadAt w0 u).childQ.reverse.length := by
    rw [List.length_reverse]; exact min_le_right _ _
  exact interface_offsets _ _ s plus minus _ hn hn' hplus hminus hstack ((quad_matching w0 u).1 hpar)

/-- Clause (d) for the odd matching: the interface of `Q` (forward) and the reversed `P` is stacked. -/
theorem quad_stacked_odd (w0 u : FLatticePaper.Farey.Word) (hpar : (w0 ++ u).count .one % 2 = 1)
    (s : Site) (plus minus : ℕ → Site)
    (hplus : ∀ i, i + 1 < (quadAt w0 u).childQ.length →
      plus (i + 1) - plus i = zeroOneHorizontalStep ((quadAt w0 u).childQ.getD (i + 1) .p))
    (hminus : ∀ i, i + 1 < (quadAt w0 u).childP.reverse.length →
      minus (i + 1) - minus i = zeroOneHorizontalReversedStep ((quadAt w0 u).childP.reverse.getD i .p)
        ((quadAt w0 u).childP.reverse.getD (i + 1) .p))
    (hstack : plus 0 - minus 0 = s) :
    ∀ i, 1 ≤ i → i < min (quadAt w0 u).childP.length (quadAt w0 u).childQ.length →
      plus i - minus i = s + (zeroOneHorizontalStep ((quadAt w0 u).childQ.getD i .p) -
        zeroOneHorizontalReversedStep ((quadAt w0 u).childP.reverse.getD 0 .p)
          ((quadAt w0 u).childQ.getD i .p)) := by
  have hn : min (quadAt w0 u).childP.length (quadAt w0 u).childQ.length ≤ (quadAt w0 u).childQ.length :=
    min_le_right _ _
  have hn' : min (quadAt w0 u).childP.length (quadAt w0 u).childQ.length ≤
      (quadAt w0 u).childP.reverse.length := by
    rw [List.length_reverse]; exact min_le_left _ _
  exact interface_offsets _ _ s plus minus _ hn hn' hplus hminus hstack ((quad_matching w0 u).2 hpar)

end FLatticePaper.Tiles.InterfaceStacked
