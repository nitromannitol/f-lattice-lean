import FLatticePaper.Tiles.ChildGlue
import FLatticePaper.Tiles.MarksIn

/-! The exact structure of the overlaps of mixed copies, as the sharpened form of claim (d).

The four marked strings of a standard tile `T` with words `wh`, `vw` are, in the order of `markedSites`: the forward
horizontal string `Sh` (index 0), the reversed vertical string `Sv` (index 1), and the half-turn images `Sh.map halfTurn`
(index 2, the reversed horizontal string) and `Sv.map halfTurn` (index 3, the vertical string).

Numerically (all words of length at most 4, both children, every pair of copies of different parents; the script
`verify_rule.py`), the overlap `X ∩ Y` of a copy `X` of the odd register at offset `a` and a copy `Y` of the even register at
offset `b` equals `S_k(X) ∩ S_{k'}(Y)` for the pair `(k, k')` given by `chooseOdd`/`chooseEven` below, which depend only on the
child, the parity flag `phase w = 1`, and the two piece indices.

What is proved here:
* the easy inclusion `S_k(X) ∩ S_{k'}(Y) ⊆ X ∩ Y` for every pair (`easy_odd`, `easy_even`), from the marks lying in the tile;
* the reduction of `MixedPiecesInMarksOdd`/`Even` to the sharpened statement `OverlapInStringsOdd`/`Even` (the hard
  inclusion, the packing across the interface). The hard inclusion is NOT proved: it is the open packing of (d), and it is
  named here. -/

namespace FLatticePaper.Tiles.MixedOverlapStrings

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
open FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.SiteInduction
open FLatticePaper.Tiles.MixedPiecesInMarks FLatticePaper.Tiles.ChildGlue FLatticePaper.Tiles.MarksIn

/-- The four marked strings of a tile as lists, in the order of `markedSites` (index 0 `Sh`, 1 `Sv`, 2 `Sh` half-turned,
3 `Sv` half-turned). -/
def strPart (T : Finset (ℤ × ℤ)) (wh vw : List Letter) (k : Fin 4) : List (ℤ × ℤ) :=
  let c := lowLeft T
  let Sh := (stringSites false false wh).map fun z => (z.1 + c.1, z.2 + c.2)
  let Sv := (stringSites true true vw.reverse).map fun z => (z.1 + c.1 - 1, z.2 + c.2 - 1)
  if k = 0 then Sh else if k = 1 then Sv else if k = 2 then Sh.map (halfTurn T) else Sv.map (halfTurn T)

theorem mem_markedSites_iff (T : Finset (ℤ × ℤ)) (wh vw : List Letter) (z : ℤ × ℤ) :
    z ∈ markedSites T wh vw ↔ ∃ k : Fin 4, z ∈ strPart T wh vw k := by
  constructor
  · intro h
    simp only [markedSites, List.mem_append] at h
    rcases h with ((h | h) | h) | h
    · exact ⟨0, by simpa [strPart] using h⟩
    · exact ⟨1, by simpa [strPart] using h⟩
    · exact ⟨2, by simpa [strPart] using h⟩
    · exact ⟨3, by simpa [strPart] using h⟩
  · rintro ⟨k, hk⟩
    simp only [markedSites, List.mem_append]
    fin_cases k
    · simp only [strPart] at hk
      simpa using Or.inl (Or.inl (Or.inl hk))
    · simp only [strPart] at hk
      simpa using Or.inl (Or.inl (Or.inr hk))
    · simp only [strPart] at hk
      simpa using Or.inl (Or.inr hk)
    · simp only [strPart] at hk
      simpa using Or.inr hk

/-- The string `k` of a tile, as a set of sites. -/
def strSet (T : Finset (ℤ × ℤ)) (wh vw : List Letter) (k : Fin 4) : Set (ℤ × ℤ) :=
  {z | z ∈ strPart T wh vw k}

/-- The string `k` of the odd standard tile of `u`. -/
def oddStr (u : Word) (k : Fin 4) : Set (ℤ × ℤ) :=
  strSet (oddTile u) (hWordOf u false) (vWordOf u false) k

/-- The string `k` of the even standard tile of `u`. -/
def evenStr (u : Word) (k : Fin 4) : Set (ℤ × ℤ) :=
  strSet (evenTile u) (hWordOf u true) (vWordOf u true) k

theorem oddStr_sub_marks (u : Word) (k : Fin 4) : oddStr u k ⊆ marksOdd u := by
  intro z hz
  exact (mem_markedSites_iff _ _ _ z).2 ⟨k, hz⟩

theorem evenStr_sub_marks (u : Word) (k : Fin 4) : evenStr u k ⊆ marksEven u := by
  intro z hz
  exact (mem_markedSites_iff _ _ _ z).2 ⟨k, hz⟩

theorem oddStr_sub_tile (u : Word) (k : Fin 4) :
    oddStr u k ⊆ ((oddTile u : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) :=
  (oddStr_sub_marks u k).trans (marksOdd_sub u)

theorem evenStr_sub_tile (u : Word) (k : Fin 4) :
    evenStr u k ⊆ ((evenTile u : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) :=
  (evenStr_sub_marks u k).trans (marksEven_sub u)

theorem shiftS_mono {S T : Set (ℤ × ℤ)} (h : S ⊆ T) (v : ℤ × ℤ) : shiftS S v ⊆ shiftS T v :=
  Set.image_mono h

/-- **The easy inclusion** (both children, since both pair the odd register with the even register): for every pair of
strings, their intersection lies in the overlap of the copies. -/
theorem easy_odd (u1 u2 : Word) (k k' : Fin 4) (a b : ℤ × ℤ) :
    shiftS (oddStr u1 k) a ∩ shiftS (evenStr u2 k') b ⊆
      shiftS (tOddSet u1) a ∩ shiftS (tEvenSet u2) b := by
  rintro z ⟨⟨s, hs, hsz⟩, ⟨t, ht, htz⟩⟩
  exact ⟨⟨s, oddStr_sub_tile u1 k hs, hsz⟩, ⟨t, evenStr_sub_tile u2 k' ht, htz⟩⟩

/-- The string pair `(k, k')` of the odd child, by the flag `phase w = 1` and the indices `i` (odd copies), `j` (even
copies). The table is the one checked on all words of length at most 4 (`verify_rule.py`). Pairs that do not overlap get the
value `(0, 0)`; for them the hard inclusion is trivial. Index 0 is the first entry of `oddP`, etc. -/
def chooseOdd (flag : Bool) (i j : ℕ) : Fin 4 × Fin 4 :=
  if flag then
    (if i = 0 ∧ j = 0 then (3, 2)
     else if i = 0 ∧ (j = 2 ∨ j = 3) then (1, 0)
     else if i = 1 ∧ (j = 0 ∨ j = 1) then (0, 1)
     else if i = 1 ∧ j = 3 then (2, 3)
     else (0, 0))
  else
    (if i = 0 ∧ j = 1 then (2, 3)
     else if i = 0 ∧ (j = 2 ∨ j = 3) then (1, 0)
     else if i = 1 ∧ (j = 0 ∨ j = 1) then (0, 1)
     else if i = 1 ∧ j = 2 then (3, 2)
     else (0, 0))

/-- The string pair `(k, k')` of the even child, same convention as `chooseOdd`. -/
def chooseEven (flag : Bool) (i j : ℕ) : Fin 4 × Fin 4 :=
  if flag then
    (if i = 0 ∧ j = 0 then (3, 2)
     else if i = 1 ∧ j = 0 then (3, 2)
     else if i = 1 ∧ j = 1 then (1, 0)
     else if i = 2 ∧ j = 0 then (0, 1)
     else if i = 2 ∧ j = 1 then (2, 3)
     else if i = 3 ∧ j = 1 then (2, 3)
     else (0, 0))
  else
    (if i = 0 ∧ j = 0 then (2, 3)
     else if i = 1 ∧ j = 0 then (2, 3)
     else if i = 1 ∧ j = 1 then (1, 0)
     else if i = 2 ∧ j = 0 then (0, 1)
     else if i = 2 ∧ j = 1 then (3, 2)
     else if i = 3 ∧ j = 1 then (3, 2)
     else (0, 0))

/-- **Sharpened claim (d), odd child, the hard inclusion (OPEN, the packing across the interface).** For the registers
`u1`, `u2` of `w`, the overlap of the copy of the odd register at the `i`-th odd offset and the copy of the even register at the
`j`-th even offset lies in the two strings `chooseOdd` gives. -/
def OverlapInStringsOdd (w : Word) : Prop :=
  ∀ u1 u2 : Word, (stateAt w).tOdd = oddTile u1 → (stateAt w).tEven = evenTile u2 →
    ∀ i j, i < (oddP w).length → j < (oddQ w).length →
      ∀ z : ℤ × ℤ,
        z ∈ shiftS (tOddSet u1) ((oddP w).getD i 0) → z ∈ shiftS (tEvenSet u2) ((oddQ w).getD j 0) →
          z ∈ shiftS (oddStr u1 (chooseOdd (phase w == 1) i j).1) ((oddP w).getD i 0) ∧
          z ∈ shiftS (evenStr u2 (chooseOdd (phase w == 1) i j).2) ((oddQ w).getD j 0)

/-- **Sharpened claim (d), even child (OPEN, the hard inclusion).** -/
def OverlapInStringsEven (w : Word) : Prop :=
  ∀ u1 u2 : Word, (stateAt w).tOdd = oddTile u1 → (stateAt w).tEven = evenTile u2 →
    ∀ i j, i < (evenP w).length → j < (evenQ w).length →
      ∀ z : ℤ × ℤ,
        z ∈ shiftS (tOddSet u1) ((evenP w).getD i 0) → z ∈ shiftS (tEvenSet u2) ((evenQ w).getD j 0) →
          z ∈ shiftS (oddStr u1 (chooseEven (phase w == 1) i j).1) ((evenP w).getD i 0) ∧
          z ∈ shiftS (evenStr u2 (chooseEven (phase w == 1) i j).2) ((evenQ w).getD j 0)

/-- An element of a list is the entry at some index (with the default `0`). -/
theorem exists_getD_of_mem (l : List (ℤ × ℤ)) {a : ℤ × ℤ} (ha : a ∈ l) :
    ∃ i, i < l.length ∧ l.getD i 0 = a := by
  obtain ⟨i, hi, hia⟩ := List.mem_iff_getElem.1 ha
  refine ⟨i, hi, ?_⟩
  simp [List.getD_eq_getElem?_getD, hi, hia]

/-- **Reduction of `MixedPiecesInMarksOdd` to the sharpened claim.** The hard inclusion gives the overlap in the two strings,
the strings lie in the marks, and the marks are shifted with the copies. -/
theorem mixed_odd_of_overlap (w : Word) (h : OverlapInStringsOdd w) : MixedPiecesInMarksOdd w := by
  intro u1 u2 hT1 hT2 a ha b hb z h1 h2
  obtain ⟨i, hi, ea⟩ := exists_getD_of_mem (oddP w) ha
  obtain ⟨j, hj, eb⟩ := exists_getD_of_mem (oddQ w) hb
  have h1' : z ∈ shiftS (tOddSet u1) ((oddP w).getD i 0) := by rw [ea]; exact h1
  have h2' : z ∈ shiftS (tEvenSet u2) ((oddQ w).getD j 0) := by rw [eb]; exact h2
  obtain ⟨g1, g2⟩ := h u1 u2 hT1 hT2 i j hi hj z h1' h2'
  rw [ea] at g1
  rw [eb] at g2
  exact ⟨shiftS_mono (oddStr_sub_marks u1 _) a g1, shiftS_mono (evenStr_sub_marks u2 _) b g2⟩

/-- **Reduction of `MixedPiecesInMarksEven` to the sharpened claim.** -/
theorem mixed_even_of_overlap (w : Word) (h : OverlapInStringsEven w) : MixedPiecesInMarksEven w := by
  intro u1 u2 hT1 hT2 a ha b hb z h1 h2
  obtain ⟨i, hi, ea⟩ := exists_getD_of_mem (evenP w) ha
  obtain ⟨j, hj, eb⟩ := exists_getD_of_mem (evenQ w) hb
  have h1' : z ∈ shiftS (tOddSet u1) ((evenP w).getD i 0) := by rw [ea]; exact h1
  have h2' : z ∈ shiftS (tEvenSet u2) ((evenQ w).getD j 0) := by rw [eb]; exact h2
  obtain ⟨g1, g2⟩ := h u1 u2 hT1 hT2 i j hi hj z h1' h2'
  rw [ea] at g1
  rw [eb] at g2
  exact ⟨shiftS_mono (oddStr_sub_marks u1 _) a g1, shiftS_mono (evenStr_sub_marks u2 _) b g2⟩

end FLatticePaper.Tiles.MixedOverlapStrings
