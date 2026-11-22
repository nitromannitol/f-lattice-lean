import FLatticePaper.Tiles.NearLadderBoundary
import FLatticePaper.Tiles.RegisterTiles
import FLatticePaper.Tiles.BaseCellIdentities

/-! The lower-left vertex of every standard cell tile is `(0, 0)` (the `low` input of `BottomSeam`).

Two facts give it. (1) The origin cell `cellCorners (0, 0)` lies in the vertex tile: this holds for the base tiles
(their cell tiles contain `(0, 0)`), and it passes from the registers to the children, since every child contains one
of its two register tiles unshifted (`oddChildB`, `evenChildB`). (2) The tile is normalised (`IsNormalised`), so no
vertex of its cells is below or left of `(0, 0)`. -/

namespace FLatticePaper.Tiles.OriginCell

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
open FLatticePaper.Tiles.StandardClause FLatticePaper.Tiles.BaseCellIdentities FLatticePaper.Tiles.RecursionIdentity
open FLatticePaper.Tiles.RegisterTiles FLatticePaper.Tiles.NearStairBoundary FLatticePaper.Tiles.NearLadderBoundary
open FLatticePaper.Tiles.BoundaryWalks FLatticePaper.Tiles.BoundaryTransport

/-- The origin cell lies in a vertex tile whose cell tile contains `(0, 0)`. -/
theorem origin_of_mem (P : Finset Site) (h : ((0, 0) : GInt) ∈ cellTileOf P) : cellCorners (0, 0) ⊆ P :=
  ((mem_cellTileOf P _).1 h).2

theorem origin_stairF (d : ℤ) (hd : 3 ≤ d) : cellCorners (0, 0) ⊆ stairF d := by
  apply origin_of_mem
  rw [cellTileOf_stairF d hd, mem_stairCells d hd]
  exact Or.inr (Or.inl ⟨rfl, rfl⟩)

theorem origin_ladderF (d : ℤ) (hd : 4 ≤ d) : cellCorners (0, 0) ⊆ ladderF d := by
  apply origin_of_mem
  rw [cellTileOf_ladderF d hd, mem_ladderCells d hd]
  exact Or.inr (Or.inl ⟨rfl, rfl⟩)

theorem origin_nstairN (k : ℕ) : cellCorners (0, 0) ⊆ nstairN (2 * (k : ℤ) + 3) := by
  apply origin_of_mem
  rw [cellTileOf_nstairN k, mem_image_add_iff, mem_rotCells, mem_stairCells (2 * (k : ℤ) + 3) (by omega)]
  simp only [rotCInv, stairInT, Prod.fst_sub, Prod.snd_sub]
  omega

theorem origin_nladderN_pos (m : ℕ) : cellCorners (0, 0) ⊆ nladderN (2 * (m : ℤ) + 4) := by
  apply origin_of_mem
  rw [cellTileOf_nladderN m, mem_image_add_iff, mem_rotCells,
    mem_ladderCells (2 * (m : ℤ) + 4) (by omega)]
  simp only [rotCInv, ladderInT, Prod.fst_sub, Prod.snd_sub]
  omega

theorem origin_nladderN_two : cellCorners (0, 0) ⊆ nladderN 2 := by
  apply origin_of_mem
  decide

/-- The register sources are no longer than the word. -/
theorem srcOf_length_le (u : Word) : (srcOf u).1.length ≤ u.length ∧ (srcOf u).2.length ≤ u.length := by
  induction u using List.reverseRecOn with
  | nil => simp [srcOf, srcFrom]
  | append_singleton u x ih =>
    have hsrc : srcOf (u ++ [x]) =
        (if x = Digit.one ∨ x = Digit.two then u else (srcOf u).1,
          if x = Digit.one ∨ x = Digit.three then u else (srcOf u).2) := by
      have := srcFrom_snoc x [] u ([], [])
      simpa [srcOf] using this
    rw [hsrc]
    constructor
    · by_cases h1 : x = Digit.one ∨ x = Digit.two
      · rw [if_pos h1]; simp
      · rw [if_neg h1]; simp only [List.length_append, List.length_singleton]; omega
    · by_cases h2 : x = Digit.one ∨ x = Digit.three
      · rw [if_pos h2]; simp
      · rw [if_neg h2]; simp only [List.length_append, List.length_singleton]; omega

theorem srcOf_snoc_length_lt (u' : Word) (x : Digit) :
    (srcOf (u' ++ [x])).1.length < (u' ++ [x]).length ∧ (srcOf (u' ++ [x])).2.length < (u' ++ [x]).length := by
  have hsrc : srcOf (u' ++ [x]) =
      (if x = Digit.one ∨ x = Digit.two then u' else (srcOf u').1,
        if x = Digit.one ∨ x = Digit.three then u' else (srcOf u').2) := by
    have := srcFrom_snoc x [] u' ([], [])
    simpa [srcOf] using this
  have hl := srcOf_length_le u'
  rw [hsrc]
  simp only [List.length_append, List.length_singleton]
  constructor
  · by_cases h1 : x = Digit.one ∨ x = Digit.two
    · rw [if_pos h1]; omega
    · rw [if_neg h1]; omega
  · by_cases h2 : x = Digit.one ∨ x = Digit.three
    · rw [if_pos h2]; omega
    · rw [if_neg h2]; omega

/-- The register sources of a nonempty word are proper prefixes. -/
theorem srcOf_length_lt (u : Word) (hu : u ≠ []) :
    (srcOf u).1.length < u.length ∧ (srcOf u).2.length < u.length := by
  induction u using List.reverseRecOn with
  | nil => exact absurd rfl hu
  | append_singleton u' x _ => exact srcOf_snoc_length_lt u' x

theorem origin_oddChildB_true (T1 T2 : Tile) (p q : Fraction) :
    T1 ⊆ oddChildB true T1 T2 p q := by
  intro x hx
  unfold oddChildB
  simp only [Finset.mem_union]
  tauto

theorem origin_oddChildB_false (T1 T2 : Tile) (p q : Fraction) :
    T2 ⊆ oddChildB false T1 T2 p q := by
  intro x hx
  unfold oddChildB
  simp only [Finset.mem_union]
  tauto

theorem origin_evenChildB_true (T1 T2 : Tile) (p q : Fraction) :
    T1 ⊆ evenChildB true T1 T2 p q := by
  intro x hx
  unfold evenChildB
  simp only [Finset.mem_union]
  tauto

theorem origin_evenChildB_false (T1 T2 : Tile) (p q : Fraction) :
    T2 ⊆ evenChildB false T1 T2 p q := by
  intro x hx
  unfold evenChildB
  simp only [Finset.mem_union]
  tauto

/-- The base words: the origin cell lies in both tiles. -/
theorem origin_base (u : Word) (hb : IsBase u) :
    cellCorners (0, 0) ⊆ oddTile u ∧ cellCorners (0, 0) ⊆ evenTile u := by
  rcases hb with rfl | h3 | h2
  · unfold oddTile evenTile
    rw [childTiles_nil]
    exact ⟨origin_nstairN 0, origin_stairF 3 (by norm_num)⟩
  · have hu : u = List.replicate u.length Digit.three := List.eq_replicate_iff.mpr ⟨rfl, h3⟩
    cases hl : u.length with
    | zero =>
      have : u = [] := List.eq_nil_of_length_eq_zero hl
      subst this
      unfold oddTile evenTile
      rw [childTiles_nil]
      exact ⟨origin_nstairN 0, origin_stairF 3 (by norm_num)⟩
    | succ m =>
      rw [hl] at hu
      rw [hu]
      unfold oddTile evenTile
      rw [childTiles_three (k := m + 1) (by omega)]
      exact ⟨origin_ladderF _ (by omega), origin_stairF _ (by omega)⟩
  · have hu : u = List.replicate u.length Digit.two := List.eq_replicate_iff.mpr ⟨rfl, h2⟩
    cases hl : u.length with
    | zero =>
      have : u = [] := List.eq_nil_of_length_eq_zero hl
      subst this
      unfold oddTile evenTile
      rw [childTiles_nil]
      exact ⟨origin_nstairN 0, origin_stairF 3 (by norm_num)⟩
    | succ m =>
      rw [hl] at hu
      rw [hu]
      unfold oddTile evenTile
      rw [childTiles_two (k := m + 1) (by omega)]
      have e : (2 * ((m + 1 : ℕ) : ℤ) + 2) = 2 * (m : ℤ) + 4 := by
        push_cast
        ring
      refine ⟨origin_nstairN (m + 1), ?_⟩
      show cellCorners (0, 0) ⊆ nladderN (2 * ((m + 1 : ℕ) : ℤ) + 2)
      rw [e]
      exact origin_nladderN_pos m

/-- The origin cell of the odd and even children, from the origin cells of the two register tiles. -/
theorem origin_child (u : Word) (hb : ¬ IsBase u) (hT1 : cellCorners (0, 0) ⊆ (stateAt u).tOdd)
    (hT2 : cellCorners (0, 0) ⊆ (stateAt u).tEven) :
    cellCorners (0, 0) ⊆ oddTile u ∧ cellCorners (0, 0) ⊆ evenTile u := by
  unfold oddTile evenTile
  rw [childTiles_of_not_base hb (stateAt u)]
  constructor
  · cases hph : (phase u == 1)
    · exact Finset.Subset.trans hT2 (origin_oddChildB_false _ _ _ _)
    · exact Finset.Subset.trans hT1 (origin_oddChildB_true _ _ _ _)
  · cases hph : (phase u == 1)
    · exact Finset.Subset.trans hT2 (origin_evenChildB_false _ _ _ _)
    · exact Finset.Subset.trans hT1 (origin_evenChildB_true _ _ _ _)

/-- The origin cell lies in the odd and even tiles of every word (induction on the length). -/
theorem origin_all (n : ℕ) : ∀ u : Word, u.length ≤ n →
    cellCorners (0, 0) ⊆ oddTile u ∧ cellCorners (0, 0) ⊆ evenTile u := by
  induction n with
  | zero =>
    intro u hu
    have : u = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact origin_base [] (Or.inl rfl)
  | succ n ih =>
    intro u hu
    by_cases hb : IsBase u
    · exact origin_base u hb
    · have hT : allTwos u = false := by
        cases h : allTwos u with
        | false => rfl
        | true => exact absurd (Or.inr (Or.inr ((allTwos_iff u).1 h))) hb
      have hH : allThrees u = false := by
        cases h : allThrees u with
        | false => rfl
        | true => exact absurd (Or.inr (Or.inl ((allThrees_iff u).1 h).2)) hb
      have hne : u ≠ [] := fun h => hb (Or.inl h)
      obtain ⟨hlt1, hlt2⟩ := srcOf_length_lt u hne
      have hO := (ih (srcOf u).1 (by omega)).1
      have hE := (ih (srcOf u).2 (by omega)).2
      have hT1 : (stateAt u).tOdd = oddTile (srcOf u).1 :=
        tOdd_eq_oddTile u (exists_one_or_two u hT hH)
      have hT2 : (stateAt u).tEven = evenTile (srcOf u).2 :=
        tEven_eq_evenTile u (exists_one_or_three u hT)
      apply origin_child u hb
      · rw [hT1]; exact hO
      · rw [hT2]; exact hE

/-- A normalised tile whose origin cell is a cell has lower-left vertex `(0, 0)`. -/
theorem isLowerLeft_origin (P : Tile) (hQ : cellCorners (0, 0) ⊆ P) (hN : IsNormalised P) :
    IsLowerLeft (cellTileOf P) (0, 0) := by
  refine ⟨?_, ?_⟩
  · unfold CellTile.vertices
    rw [Finset.mem_biUnion]
    exact ⟨(0, 0), (mem_cellTileOf P _).2 ⟨hQ (by simp [cellCorners]), hQ⟩, by simp [cellCorners]⟩
  · intro v hv
    unfold CellTile.vertices at hv
    rw [Finset.mem_biUnion] at hv
    obtain ⟨c, hc, hvc⟩ := hv
    have hvP : v ∈ P := ((mem_cellTileOf P c).1 hc).2 hvc
    have hl := hN.2 v hvP
    unfold lexLE at hl
    obtain ⟨v1, v2⟩ := v
    simp only [Prod.fst_zero, Prod.snd_zero] at hl
    show (0 : ℤ) ≤ v2 ∧ (v2 = 0 → 0 ≤ v1)
    omega

/-- The lower-left vertex of the odd and even standard cell tiles of every word is `(0, 0)`. -/
theorem lowerLeft_origin (w : Word) :
    IsLowerLeft (cellTileOf (oddTile w)) (0, 0) ∧ IsLowerLeft (cellTileOf (evenTile w)) (0, 0) := by
  have h := origin_all w.length w le_rfl
  have hn := standard_tiles_normalised w
  exact ⟨isLowerLeft_origin _ h.1 hn.1, isLowerLeft_origin _ h.2 hn.2⟩

end FLatticePaper.Tiles.OriginCell
