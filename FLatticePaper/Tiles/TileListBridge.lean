import FLatticePaper.Tiles.StackedMoreover
import FLatticePaper.Tiles.PseudoSquare
import FLatticePaper.Tiles.PseudoSquareSites
import FLatticePaper.Tiles.ZeroOneGeneral
import FLatticePaper.Tiles.BoundaryStrings

/-! The tile list of the forward horizontal zero-one string, in the two representations, agree:
`zoForwardE (lettersOf w false) w.length = hStringAt w 0`. The types come from the `tileSeq` rule (`hTt`), the positions from
the step `zeroOneHorizontalStep b = hOffset b` (the scan of `hOffset` over the tail of the word, `posF`). -/

namespace FLatticePaper.Tiles

/-- The previous letter of position `k` in a word started after the letter `x`. -/
def tlPrev (x : Letter) (xs : List Letter) (k : ℕ) : Letter := if k = 0 then x else xs.getD (k - 1) Letter.p

theorem tileSeqAux_length (prev : Option Letter) (w : BinaryWord) :
    (tileSeqAux prev w).length = w.length := by
  induction w generalizing prev with
  | nil => rfl
  | cons x xs ih => simp [tileSeqAux, ih]

/-- The tile type of position `k` of the doubled sequence, from the previous letter (`hTt`). -/
theorem tileSeqAux_getD (xs : BinaryWord) : ∀ (x : Letter) (k : ℕ), k < xs.length →
    (tileSeqAux (some x) xs).getD k ZTile.zero = hTt (tlPrev x xs k) (xs.getD k Letter.p) := by
  induction xs with
  | nil => intro x k hk; simp at hk
  | cons y ys ih =>
    intro x k hk
    cases k with
    | zero => cases x <;> cases y <;> rfl
    | succ k =>
      have hk' : k < ys.length := by simp at hk; omega
      have hI := ih y k hk'
      have hp : tlPrev x (y :: ys) (k + 1) = (y :: ys).getD k Letter.p := by
        simp [tlPrev]
      have hq : tlPrev y ys k = (y :: ys).getD k Letter.p := by
        cases k with
        | zero => simp [tlPrev]
        | succ k' => simp [tlPrev]
      show (tileSeqAux (some y) ys).getD k ZTile.zero = _
      rw [hI, hq, hp]
      simp

theorem stepOf_hor (a b : Letter) : stepOf Orientation.horizontal false a b = hOffset b := by
  cases b <;> rfl

theorem posF_succ_shift (ℓ : ℕ → Letter) : ∀ k : ℕ,
    posF Orientation.horizontal false ℓ (k + 1) =
      hOffset (ℓ 1) + posF Orientation.horizontal false (fun j => ℓ (j + 1)) k := by
  intro k
  induction k with
  | zero =>
    simp [posF, stepOf_hor]
  | succ k ih =>
    rw [posF, ih]
    simp only [posF, stepOf_hor, add_assoc]

theorem scanl_getD_tail : ∀ (k : ℕ) (w : BinaryWord) (c : GInt), k < w.length →
    (List.scanl (· + ·) c (w.tail.map hOffset)).getD k 0 =
      c + posF Orientation.horizontal false (fun j => w.getD j Letter.p) k := by
  intro k
  induction k with
  | zero =>
    intro w c hk
    cases w with
    | nil => simp at hk
    | cons x xs => simp [posF]
  | succ k ih =>
    intro w c hk
    cases w with
    | nil => simp at hk
    | cons x rest =>
      cases rest with
      | nil => simp at hk
      | cons y rest' =>
        have hk' : k < (y :: rest').length := by simp at hk; omega
        have hI := ih (y :: rest') (c + hOffset y) hk'
        have hs : (List.scanl (· + ·) c ((x :: y :: rest').tail.map hOffset)).getD (k + 1) 0 =
            (List.scanl (· + ·) (c + hOffset y) ((y :: rest').tail.map hOffset)).getD k 0 := by
          simp [List.scanl]
        rw [hs, hI, posF_succ_shift, add_assoc]
        try rfl

/-- **The tile list of the forward horizontal string, in the two representations.** -/
theorem zoForwardE_eq_hStringAt (w : BinaryWord) :
    zoForwardE (lettersOf w false) w.length = hStringAt w (0, 0) := by
  have hT : ∀ k, k < w.length →
      (tileSeqAux none w).getD k ZTile.zero = hTileAt (lettersOf w false) k := by
    intro k hk
    rw [tileSeqAux_none_eq, tileSeqAux_getD w Letter.p k hk]
    simp [hTileAt, hPrev, lettersOf, tlPrev]
  have hP : ∀ k, k < w.length →
      (List.scanl (· + ·) (0, 0) (w.tail.map hOffset)).getD k 0 =
        posF Orientation.horizontal false (lettersOf w false) k := by
    intro k hk
    have hl : (fun j => w.getD j Letter.p) = lettersOf w false := by
      funext j
      simp [lettersOf]
    rw [scanl_getD_tail k w (0, 0) hk, hl]
    simp
  cases w with
  | nil => rfl
  | cons x xs =>
    unfold zoForwardE hStringAt tileSeq
    refine List.ext_getElem ?_ ?_
    · simp [tileSeqAux_length]
    · intro k h1 h2
      have hk : k < (x :: xs).length := by simpa using h1
      have e1 := hT k hk
      have e2 := hP k hk
      rw [List.getD_eq_getElem _ _ (by simp [tileSeqAux_length]; omega)] at e1
      rw [List.getD_eq_getElem _ _ (by simp; omega)] at e2
      simp only [List.getElem_map, List.getElem_range, List.getElem_zip]
      rw [e1, e2]

end FLatticePaper.Tiles
