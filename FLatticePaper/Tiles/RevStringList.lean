import FLatticePaper.Tiles.TileListBridge
import FLatticePaper.Tiles.BoundaryStrings

/-! # The reversed horizontal string as an indexed list

For a word `u` and positions `P` starting at `c` and stepping by the reversed zero-one step of the letter pair (`hRevOffset`, which
equals `zeroOneHorizontalReversedStep`), the reversed horizontal string `hRevStringAt u c` is the indexed list of the enlarged tile
types `hTileAt` of `u` with the positions `P`. This is the list bridge for every reversed horizontal piece. -/

namespace FLatticePaper.Tiles

theorem hRevOffset_eq_step (a b : Letter) : hRevOffset a b = zeroOneHorizontalReversedStep a b := by
  cases a <;> cases b <;> rfl

/-- The positions of a scan of the reversed steps step by step. -/
theorem scanl_getD_succ : ∀ (L : List GInt) (c : GInt) (k : ℕ), k < L.length →
    (List.scanl (· + ·) c L).getD (k + 1) 0 = (List.scanl (· + ·) c L).getD k 0 + L.getD k 0
  | [], _, _, hk => by simp at hk
  | x :: L, c, k, hk => by
      cases k with
      | zero => simp [List.scanl_cons, add_comm]
      | succ k =>
        have hk' : k < L.length := by simp at hk; omega
        have ih := scanl_getD_succ L (c + x) k hk'
        simp only [List.scanl_cons, List.getD_cons_succ]
        rw [ih]

theorem hRevStringAt_eq_map (u : BinaryWord) (c : GInt) (P : ℕ → GInt) (hP0 : P 0 = c)
    (hstep : ∀ j, j + 1 < u.length →
      P (j + 1) = P j + zeroOneHorizontalReversedStep (u.getD j Letter.p) (u.getD (j + 1) Letter.p)) :
    hRevStringAt u c = (List.range u.length).map fun j => (hTileAt (lettersOf u false) j, P j) := by
  cases u with
  | nil => simp [hRevStringAt, tileSeq, tileSeqAux]
  | cons x xs =>
    have hlen : ∀ j, j < (x :: xs).length → ((x :: xs).getD j Letter.p) = (x :: xs).getD j Letter.p := fun _ _ => rfl
    have hscan : ∀ j, j < (x :: xs).length →
        (List.scanl (· + ·) c (((x :: xs).zip (x :: xs).tail).map fun ab => hRevOffset ab.1 ab.2)).getD j 0 = P j := by
      intro j
      induction j with
      | zero => intro _; simp [hP0]
      | succ j ih =>
        intro hj
        have hL : j < (((x :: xs).zip (x :: xs).tail).map fun ab => hRevOffset ab.1 ab.2).length := by
          simp at hj ⊢; omega
        rw [scanl_getD_succ _ _ _ hL, ih (by simp at hj ⊢; omega), hstep j (by simpa using hj)]
        congr 1
        have hz : (((x :: xs).zip (x :: xs).tail).map fun ab => hRevOffset ab.1 ab.2).getD j 0
            = hRevOffset ((x :: xs).getD j Letter.p) ((x :: xs).getD (j + 1) Letter.p) := by
          have ha : j < (x :: xs).length := by omega
          rw [List.getD_eq_getElem _ _ hL]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hj,
            Option.getD_some]
          simp [List.getElem_zip, List.getElem_cons_succ]
        rw [hz, hRevOffset_eq_step]
    unfold hRevStringAt
    refine List.ext_getElem ?_ ?_
    · simp [tileSeq, tileSeqAux_length, List.length_scanl, List.length_map, List.length_zip]
    · intro j h1 h2
      have hj : j < (x :: xs).length := by
        simp [tileSeq, tileSeqAux_length] at h1
        simp only [List.length_cons]
        omega
      have e1 : (tileSeqAux none (x :: xs)).getD j ZTile.zero = hTileAt (lettersOf (x :: xs) false) j := by
        rw [tileSeqAux_none_eq, tileSeqAux_getD (x :: xs) Letter.p j hj]
        simp [hTileAt, hPrev, lettersOf, tlPrev]
      have e2 := hscan j hj
      simp only [List.getElem_zip, List.getElem_map, List.getElem_range]
      rw [List.getD_eq_getElem _ _ (by simp [tileSeqAux_length]; omega)] at e1
      rw [List.getD_eq_getElem _ _ (by simp; omega)] at e2
      simp only [tileSeq] at *
      exact Prod.ext (by simpa using e1) (by simpa using e2)

end FLatticePaper.Tiles
