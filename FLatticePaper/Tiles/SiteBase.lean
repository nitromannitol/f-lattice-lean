import FLatticePaper.Tiles.SiteInduction

/-! Task 53, item 1: the base words of the standard tiles (`baseEq`, `baseCov` of `SiteInduction.SourceHyps`).

The base words are `[]`, `3^k` and `2^k`. Their parents and current fractions have closed forms (`parentsAt_rep_three`,
`parentsAt_rep_two`), and their literal tiles are the four pure masks of `childTiles`: `stairF (2k+3)` and `ladderF (2k+2)` for
`3^k`, `nstairN (2k+3)` and `nladderN (2k+2)` for `2^k`, with `stairF 3`/`nstairN 3` at the empty word.

So `baseEq` and `baseCov` reduce to eight parametric statements, one per mask and one per cover (`MaskHyps`, `CoverHyps`). -/

namespace FLatticePaper.Tiles.SiteBase

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
open FLatticePaper.Tiles.SiteInduction

/-! ### The parents and the current fractions at the base words -/

theorem parentsAt_rep_three (k : ℕ) :
    parentsAt (List.replicate k Digit.three) = ⟨⟨0, 1⟩, ⟨1, 2 * (k : ℤ) + 1⟩⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ', parentsAt_append_singleton, ih]
    simp only [Parents.step, Parents.current, Parents.combine, Nat.cast_succ, Parents.mk.injEq, Fraction.mk.injEq, true_and]
    omega

theorem parentsAt_rep_two (k : ℕ) :
    parentsAt (List.replicate k Digit.two) = ⟨⟨(k : ℤ), (k : ℤ) + 1⟩, ⟨1, 1⟩⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ', parentsAt_append_singleton, ih]
    simp only [Parents.step, Parents.current, Parents.combine, Nat.cast_succ, Parents.mk.injEq, Fraction.mk.injEq, and_true]
    omega

theorem curO_rep_three (k : ℕ) :
    (parentsAt (List.replicate k Digit.three)).current .odd = ⟨1, 2 * (k : ℤ) + 2⟩ := by
  rw [parentsAt_rep_three]
  simp only [Parents.current, Parents.combine, Fraction.mk.injEq]
  omega

theorem curE_rep_three (k : ℕ) :
    (parentsAt (List.replicate k Digit.three)).current .even = ⟨1, 2 * (k : ℤ) + 3⟩ := by
  rw [parentsAt_rep_three]
  simp only [Parents.current, Parents.combine, Fraction.mk.injEq]
  omega

theorem curO_rep_two (k : ℕ) :
    (parentsAt (List.replicate k Digit.two)).current .odd = ⟨(k : ℤ) + 1, (k : ℤ) + 2⟩ := by
  rw [parentsAt_rep_two]
  simp only [Parents.current, Parents.combine, Fraction.mk.injEq]
  omega

theorem curE_rep_two (k : ℕ) :
    (parentsAt (List.replicate k Digit.two)).current .even = ⟨2 * (k : ℤ) + 1, 2 * (k : ℤ) + 3⟩ := by
  rw [parentsAt_rep_two]
  simp only [Parents.current, Parents.combine, Fraction.mk.injEq]
  omega

theorem curO_nil : (parentsAt []).current .odd = ⟨1, 2⟩ := rfl

theorem curE_nil : (parentsAt []).current .even = ⟨1, 3⟩ := rfl

/-! ### The base tiles as the pure masks -/

theorem ne_three_of_rep_two (k : ℕ) (hk : 1 ≤ k) :
    List.replicate k Digit.two ≠ List.replicate (List.replicate k Digit.two).length Digit.three := by
  intro h
  have hmem : Digit.two ∈ List.replicate k Digit.two := List.mem_replicate.2 ⟨by omega, rfl⟩
  rw [h] at hmem
  exact absurd (List.eq_of_mem_replicate hmem) (by decide)

theorem evenTile_rep_three (k : ℕ) : evenTile (List.replicate k Digit.three) = stairF (2 * (k : ℤ) + 3) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · show evenTile [] = stairF (2 * ((0 : ℕ) : ℤ) + 3)
    unfold evenTile childTiles
    simp
  · have hne : List.replicate k Digit.three ≠ [] := by
      intro h
      have : (List.replicate k Digit.three).length = 0 := by simp [h]
      simp at this
      omega
    have hc : List.replicate k Digit.three = List.replicate (List.replicate k Digit.three).length Digit.three := by
      simp
    unfold evenTile childTiles
    rw [if_neg hne, if_pos hc]
    simp

theorem oddTile_rep_three (k : ℕ) (hk : 1 ≤ k) :
    oddTile (List.replicate k Digit.three) = ladderF (2 * (k : ℤ) + 2) := by
  have hne : List.replicate k Digit.three ≠ [] := by
    intro h
    have : (List.replicate k Digit.three).length = 0 := by simp [h]
    simp at this
    omega
  have hc : List.replicate k Digit.three = List.replicate (List.replicate k Digit.three).length Digit.three := by
    simp
  unfold oddTile childTiles
  rw [if_neg hne, if_pos hc]
  simp

theorem oddTile_rep_two (k : ℕ) : oddTile (List.replicate k Digit.two) = nstairN (2 * (k : ℤ) + 3) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · show oddTile [] = nstairN (2 * ((0 : ℕ) : ℤ) + 3)
    unfold oddTile childTiles
    simp
  · have hne : List.replicate k Digit.two ≠ [] := by
      intro h
      have : (List.replicate k Digit.two).length = 0 := by simp [h]
      simp at this
      omega
    have hc3 := ne_three_of_rep_two k hk
    have hc2 : List.replicate k Digit.two = List.replicate (List.replicate k Digit.two).length Digit.two := by
      simp
    unfold oddTile childTiles
    rw [if_neg hne, if_neg hc3, if_pos hc2]
    simp

theorem evenTile_rep_two (k : ℕ) (hk : 1 ≤ k) :
    evenTile (List.replicate k Digit.two) = nladderN (2 * (k : ℤ) + 2) := by
  have hne : List.replicate k Digit.two ≠ [] := by
    intro h
    have : (List.replicate k Digit.two).length = 0 := by simp [h]
    simp at this
    omega
  have hc3 := ne_three_of_rep_two k hk
  have hc2 : List.replicate k Digit.two = List.replicate (List.replicate k Digit.two).length Digit.two := by
    simp
  unfold evenTile childTiles
  rw [if_neg hne, if_neg hc3, if_pos hc2]
  simp

/-- A base word is a power of `3` or of `2`. -/
theorem isBase_cases {w : Word} (h : IsBase w) :
    (∃ k : ℕ, w = List.replicate k Digit.three) ∨ (∃ k : ℕ, w = List.replicate k Digit.two) := by
  rcases h with h | h | h
  · exact Or.inl ⟨0, by simp [h]⟩
  · exact Or.inl ⟨w.length, List.eq_replicate_iff.2 ⟨rfl, h⟩⟩
  · exact Or.inr ⟨w.length, List.eq_replicate_iff.2 ⟨rfl, h⟩⟩

/-! ### The parametric statements: the masks and the covers -/

/-- The four pure masks, as `H_X` of their current fractions (`X = ⟨num, den⟩`). -/
structure MaskHyps : Prop where
  stair : ∀ k : ℕ, ((stairF (2 * (k : ℤ) + 3) : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) = HSet ⟨1, 2 * (k : ℤ) + 3⟩
  ladder : ∀ k : ℕ, 1 ≤ k →
    ((ladderF (2 * (k : ℤ) + 2) : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) = HSet ⟨1, 2 * (k : ℤ) + 2⟩
  nstair : ∀ k : ℕ, ((nstairN (2 * (k : ℤ) + 3) : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) = HSet ⟨(k : ℤ) + 1, (k : ℤ) + 2⟩
  nladder : ∀ k : ℕ, 1 ≤ k →
    ((nladderN (2 * (k : ℤ) + 2) : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) = HSet ⟨2 * (k : ℤ) + 1, 2 * (k : ℤ) + 3⟩

/-- The quotient covers of the four pure `H` sets. -/
structure CoverHyps : Prop where
  stair : ∀ k : ℕ, QuotientCover (HSet ⟨1, 2 * (k : ℤ) + 3⟩) (perU ⟨1, 2 * (k : ℤ) + 3⟩) (perV ⟨1, 2 * (k : ℤ) + 3⟩)
  ladder : ∀ k : ℕ, 1 ≤ k →
    QuotientCover (HSet ⟨1, 2 * (k : ℤ) + 2⟩) (perU ⟨1, 2 * (k : ℤ) + 2⟩) (perV ⟨1, 2 * (k : ℤ) + 2⟩)
  nstair : ∀ k : ℕ, QuotientCover (HSet ⟨(k : ℤ) + 1, (k : ℤ) + 2⟩) (perU ⟨(k : ℤ) + 1, (k : ℤ) + 2⟩)
    (perV ⟨(k : ℤ) + 1, (k : ℤ) + 2⟩)
  nladder : ∀ k : ℕ, 1 ≤ k →
    QuotientCover (HSet ⟨2 * (k : ℤ) + 1, 2 * (k : ℤ) + 3⟩) (perU ⟨2 * (k : ℤ) + 1, 2 * (k : ℤ) + 3⟩)
      (perV ⟨2 * (k : ℤ) + 1, 2 * (k : ℤ) + 3⟩)

/-! ### `baseEq` and `baseCov` from the parametric statements -/

theorem baseEq_nil (M : MaskHyps) :
    ((oddTile []) : Set (ℤ × ℤ)) = HSet (curO []) ∧ ((evenTile []) : Set (ℤ × ℤ)) = HSet (curE []) := by
  have h1 : oddTile [] = nstairN (2 * ((0 : ℕ) : ℤ) + 3) := oddTile_rep_two 0
  have h2 : evenTile [] = stairF (2 * ((0 : ℕ) : ℤ) + 3) := evenTile_rep_three 0
  unfold curO curE
  rw [h1, h2, curO_nil, curE_nil]
  exact ⟨M.nstair 0, M.stair 0⟩

theorem baseEq_three (M : MaskHyps) (k : ℕ) (hk : 1 ≤ k) :
    ((oddTile (List.replicate k Digit.three)) : Set (ℤ × ℤ)) = HSet (curO (List.replicate k Digit.three)) ∧
      ((evenTile (List.replicate k Digit.three)) : Set (ℤ × ℤ)) = HSet (curE (List.replicate k Digit.three)) := by
  unfold curO curE
  rw [oddTile_rep_three k hk, evenTile_rep_three k, curO_rep_three, curE_rep_three]
  exact ⟨M.ladder k hk, M.stair k⟩

theorem baseEq_two (M : MaskHyps) (k : ℕ) (hk : 1 ≤ k) :
    ((oddTile (List.replicate k Digit.two)) : Set (ℤ × ℤ)) = HSet (curO (List.replicate k Digit.two)) ∧
      ((evenTile (List.replicate k Digit.two)) : Set (ℤ × ℤ)) = HSet (curE (List.replicate k Digit.two)) := by
  unfold curO curE
  rw [oddTile_rep_two k, evenTile_rep_two k hk, curO_rep_two, curE_rep_two]
  exact ⟨M.nstair k, M.nladder k hk⟩

/-- `baseEq` of `SiteInduction.SourceHyps`, from the four masks. -/
theorem baseEq_of_masks (M : MaskHyps) (w : Word) (hb : IsBase w) :
    ((oddTile w : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) = HSet (curO w) ∧
      ((evenTile w : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) = HSet (curE w) := by
  rcases isBase_cases hb with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact baseEq_nil M
    · exact baseEq_three M k hk
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact baseEq_nil M
    · exact baseEq_two M k hk

theorem baseCov_nil (C : CoverHyps) :
    QuotientCover (HSet (curO [])) (perU (curO [])) (perV (curO [])) ∧
      QuotientCover (HSet (curE [])) (perU (curE [])) (perV (curE [])) := by
  unfold curO curE
  rw [curO_nil, curE_nil]
  exact ⟨C.nstair 0, C.stair 0⟩

theorem baseCov_three (C : CoverHyps) (k : ℕ) (hk : 1 ≤ k) :
    QuotientCover (HSet (curO (List.replicate k Digit.three))) (perU (curO (List.replicate k Digit.three)))
        (perV (curO (List.replicate k Digit.three))) ∧
      QuotientCover (HSet (curE (List.replicate k Digit.three))) (perU (curE (List.replicate k Digit.three)))
        (perV (curE (List.replicate k Digit.three))) := by
  unfold curO curE
  rw [curO_rep_three, curE_rep_three]
  exact ⟨C.ladder k hk, C.stair k⟩

theorem baseCov_two (C : CoverHyps) (k : ℕ) (hk : 1 ≤ k) :
    QuotientCover (HSet (curO (List.replicate k Digit.two))) (perU (curO (List.replicate k Digit.two)))
        (perV (curO (List.replicate k Digit.two))) ∧
      QuotientCover (HSet (curE (List.replicate k Digit.two))) (perU (curE (List.replicate k Digit.two)))
        (perV (curE (List.replicate k Digit.two))) := by
  unfold curO curE
  rw [curO_rep_two, curE_rep_two]
  exact ⟨C.nstair k, C.nladder k hk⟩

/-- `baseCov` of `SiteInduction.SourceHyps`, from the four covers. -/
theorem baseCov_of_covers (C : CoverHyps) (w : Word) (hb : IsBase w) :
    QuotientCover (HSet (curO w)) (perU (curO w)) (perV (curO w)) ∧
      QuotientCover (HSet (curE w)) (perU (curE w)) (perV (curE w)) := by
  rcases isBase_cases hb with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact baseCov_nil C
    · exact baseCov_three C k hk
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact baseCov_nil C
    · exact baseCov_two C k hk

end FLatticePaper.Tiles.SiteBase
