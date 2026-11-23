import FLatticePaper.Tiles.SiteJunction
import FLatticePaper.Tiles.StandardTiles
import FLatticePaper.Construction.OffsetTables

/-! Task 53, marksIn (horizontal gluing): the forward string of a child word lies in the child tile.

A child word is a concatenation of two or three blocks (`childWords`), each starting with `q` and ending with `p` (`jn` is the
junction offset of a block). The pieces of `oddChildB` and `evenChildB` are the registers `T1`, `T2` translated by the same
junction offsets, so the string of each block lies in its piece. The four lemmas below are the four parity cases. -/

namespace FLatticePaper.Tiles.HorizontalGlue

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.Standard FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Tiles.SiteJunction FLatticePaper.Construction

/-- The junction offset of a block `X` (the offset of the next block after it). -/
def jn (X : List Letter) : ℤ × ℤ := (2 * (X.length : ℤ) - (X.count Letter.q : ℤ), (X.count Letter.q : ℤ))

/-- Every site of the forward horizontal string of `X` lies in `T`. -/
def HC (X : List Letter) (T : Tile) : Prop := ∀ z ∈ stringSites false false X, z ∈ T

theorem mem_shift_add (T : Tile) (v w : ℤ × ℤ) (h : w ∈ T) : w + v ∈ shift T v := by
  rw [mem_shift]
  simpa using h

theorem stringSites_block' (X' Y' : List Letter) (hX : (Letter.q :: X').getLast? = some Letter.p) :
    stringSites false false ((Letter.q :: X') ++ (Letter.q :: Y')) =
      stringSites false false (Letter.q :: X') ++ (stringSites false false (Letter.q :: Y')).map fun z => z + jn (Letter.q :: X') :=
  stringSites_block X' Y' hX

/-- Membership in the string of a junction: a site of `q :: X'`, or a site of `q :: Y'` moved by the junction offset. -/
theorem mem_junction (X' Y' : List Letter) (hX : (Letter.q :: X').getLast? = some Letter.p) (z : ℤ × ℤ) :
    z ∈ stringSites false false ((Letter.q :: X') ++ (Letter.q :: Y')) ↔
      z ∈ stringSites false false (Letter.q :: X') ∨
        ∃ w ∈ stringSites false false (Letter.q :: Y'), w + jn (Letter.q :: X') = z := by
  rw [stringSites_block' X' Y' hX]
  simp only [List.mem_append, List.mem_map]

/-- The even-count child `B B A` of the odd tile (`oddChildB false`). -/
theorem glue_childP_false (B' A' : List Letter) (T1 T2 : Tile) (p q : Fraction)
    (hB : (Letter.q :: B').getLast? = some Letter.p) (hJB : jn (Letter.q :: B') = texV1Even q)
    (hB2 : HC (Letter.q :: B') T2) (hA1 : HC (Letter.q :: A') T1) :
    HC ((Letter.q :: B') ++ (Letter.q :: B') ++ (Letter.q :: A')) (oddChildB false T1 T2 p q) := by
  intro z hz
  rw [List.append_assoc] at hz
  rcases (mem_junction B' (B' ++ (Letter.q :: A')) hB z).1 hz with h | ⟨w, hw, rfl⟩
  · have h2 := hB2 z h
    unfold oddChildB
    simp only [Finset.mem_union]
    tauto
  · rcases (mem_junction B' A' hB w).1 hw with h | ⟨v, hv, rfl⟩
    · have h2 := mem_shift_add T2 (jn (Letter.q :: B')) w (hB2 w h)
      rw [hJB] at h2
      rw [hJB]
      unfold oddChildB
      simp only [Finset.mem_union]
      tauto
    · have h2 := mem_shift_add T1 (jn (Letter.q :: B') + jn (Letter.q :: B')) v (hA1 v hv)
      rw [hJB] at h2 ⊢
      have e : (v + texV1Even q) + texV1Even q = v + (texV1Even q + texV1Even q) := by abel
      rw [e]
      unfold oddChildB
      simp only [Finset.mem_union]
      tauto

/-- The odd-count child `A B B` of the odd tile (`oddChildB true`). -/
theorem glue_childP_true (A' B' : List Letter) (T1 T2 : Tile) (p q : Fraction)
    (hA : (Letter.q :: A').getLast? = some Letter.p) (hB : (Letter.q :: B').getLast? = some Letter.p)
    (hJA : jn (Letter.q :: A') = texV1Odd p) (hJB : jn (Letter.q :: B') = texV1Even q)
    (hA1 : HC (Letter.q :: A') T1) (hB2 : HC (Letter.q :: B') T2) :
    HC ((Letter.q :: A') ++ (Letter.q :: B') ++ (Letter.q :: B')) (oddChildB true T1 T2 p q) := by
  intro z hz
  rw [List.append_assoc] at hz
  rcases (mem_junction A' (B' ++ (Letter.q :: B')) hA z).1 hz with h | ⟨w, hw, rfl⟩
  · have h2 := hA1 z h
    unfold oddChildB
    simp only [Finset.mem_union]
    tauto
  · rcases (mem_junction B' B' hB w).1 hw with h | ⟨v, hv, rfl⟩
    · have h2 := mem_shift_add T2 (jn (Letter.q :: A')) w (hB2 w h)
      rw [hJA] at h2
      rw [hJA]
      unfold oddChildB
      simp only [Finset.mem_union]
      tauto
    · have h2 := mem_shift_add T2 (jn (Letter.q :: A') + jn (Letter.q :: B')) v (hB2 v hv)
      rw [hJA, hJB] at h2
      rw [hJA, hJB]
      have e : (v + texV1Even q) + texV1Odd p = v + (texV1Odd p + texV1Even q) := by abel
      rw [e]
      unfold oddChildB
      simp only [Finset.mem_union]
      tauto

/-- The even child `B A` of the even tile (`evenChildB false`). -/
theorem glue_childQ_false (B' A' : List Letter) (T1 T2 : Tile) (p q : Fraction)
    (hB : (Letter.q :: B').getLast? = some Letter.p) (hJB : jn (Letter.q :: B') = texV1Even q)
    (hB2 : HC (Letter.q :: B') T2) (hA1 : HC (Letter.q :: A') T1) :
    HC ((Letter.q :: B') ++ (Letter.q :: A')) (evenChildB false T1 T2 p q) := by
  intro z hz
  rcases (mem_junction B' A' hB z).1 hz with h | ⟨w, hw, rfl⟩
  · have h2 := hB2 z h
    unfold evenChildB
    simp only [Finset.mem_union]
    tauto
  · have h2 := mem_shift_add T1 (jn (Letter.q :: B')) w (hA1 w hw)
    rw [hJB] at h2
    rw [hJB]
    unfold evenChildB
    simp only [Finset.mem_union]
    tauto

/-- The odd-count child `A B` of the even tile (`evenChildB true`). -/
theorem glue_childQ_true (A' B' : List Letter) (T1 T2 : Tile) (p q : Fraction)
    (hA : (Letter.q :: A').getLast? = some Letter.p) (hJA : jn (Letter.q :: A') = texV1Odd p)
    (hA1 : HC (Letter.q :: A') T1) (hB2 : HC (Letter.q :: B') T2) :
    HC ((Letter.q :: A') ++ (Letter.q :: B')) (evenChildB true T1 T2 p q) := by
  intro z hz
  rcases (mem_junction A' B' hA z).1 hz with h | ⟨w, hw, rfl⟩
  · have h2 := hA1 z h
    unfold evenChildB
    simp only [Finset.mem_union]
    tauto
  · have h2 := mem_shift_add T2 (jn (Letter.q :: A')) w (hB2 w hw)
    rw [hJA] at h2
    rw [hJA]
    unfold evenChildB
    simp only [Finset.mem_union]
    tauto

end FLatticePaper.Tiles.HorizontalGlue
