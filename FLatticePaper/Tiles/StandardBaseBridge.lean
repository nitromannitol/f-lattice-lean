import FLatticePaper.Tiles.StandardTiles
import FLatticePaper.Construction.BaseCaseRecurrence
import FLatticePaper.Construction.NearOneBaseCases

/-! # The base tiles of `StandardTiles` are the printed base tiles of `prop:base_cases`

`StandardTiles` takes the base tiles of the empty word and of the words `3^k` and `2^k` from the finite sets
`stairF`, `ladderF`, `nstairF`, `nladderF` (membership lemmas `mem_*F`). The printed tiles are the set-builder
definitions `paperStairTile`, `paperLadderTile`, `paperNearStairTile`, `paperNearLadderTile` of the Section 6
lemmas `basecase_3k_even_std`, `basecase_3k_odd_std`, `basecase_2k_odd_std`, `basecase_2k_even_std`.
The near-one tiles are used normalised by the translation `(0,-1)` (`nstairN`, `nladderN`), which moves the
lower-left point `(0,1)` to `(0,0)`; the other two are already normalised. -/

namespace FLatticePaper.Tiles.Standard

open FLatticePaper.Construction

/-- `stairF d` is the printed tile `paperStairTile d` (`lemma:basecase_3k_even_std`). -/
theorem mem_stairF_iff_paper {d : ℤ} (hd : 2 ≤ d) (x : Site) :
    x ∈ stairF d ↔ x ∈ paperStairTile d := by
  rw [mem_stairF hd]
  unfold paperStairTile
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]

/-- `ladderF d` is the printed tile `paperLadderTile d` (`lemma:basecase_3k_odd_std`). -/
theorem mem_ladderF_iff_paper {d : ℤ} (hd : 2 ≤ d) (x : Site) :
    x ∈ ladderF d ↔ x ∈ paperLadderTile d := by
  rw [mem_ladderF hd]
  unfold paperLadderTile paperLadderA paperLadderB paperLadderC paperLadderD
  simp only [Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq,
    Prod.ext_iff]
  constructor <;> intro h <;> omega

/-- `nstairF d` is the printed tile `paperNearStairTile d` before normalisation (`lemma:basecase_2k_odd_std`). -/
theorem mem_nstairF_iff_paper {d : ℤ} (hd : 2 ≤ d) (x : Site) :
    x ∈ nstairF d ↔ x ∈ paperNearStairTile d := by
  rw [mem_nstairF hd]
  unfold paperNearStairTile
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]

/-- `nladderF d` is the printed tile `paperNearLadderTile d` before normalisation (`lemma:basecase_2k_even_std`). -/
theorem mem_nladderF_iff_paper {d : ℤ} (hd : 2 ≤ d) (x : Site) :
    x ∈ nladderF d ↔ x ∈ paperNearLadderTile d := by
  rw [mem_nladderF hd]
  unfold paperNearLadderTile paperNearLadderA paperNearLadderB paperNearLadderC paperNearLadderD
  simp only [Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq,
    Prod.ext_iff]
  constructor <;> intro h <;> omega

/-- The translation `x ↦ x - (0,-1)` of the normalised near-one tiles: `x ∈ nstairN d` iff `(x.1, x.2+1) ∈ nstairF d`. -/
theorem mem_nstairN {d : ℤ} (x : Site) : x ∈ nstairN d ↔ (x.1, x.2 + 1) ∈ nstairF d := by
  unfold nstairN
  rw [mem_shift]
  have h : x - ((0 : ℤ), (-1 : ℤ)) = (x.1, x.2 + 1) := by
    ext <;> simp [sub_eq_add_neg]
  rw [h]

theorem mem_nladderN {d : ℤ} (x : Site) : x ∈ nladderN d ↔ (x.1, x.2 + 1) ∈ nladderF d := by
  unfold nladderN
  rw [mem_shift]
  have h : x - ((0 : ℤ), (-1 : ℤ)) = (x.1, x.2 + 1) := by
    ext <;> simp [sub_eq_add_neg]
  rw [h]

/-- The normalised near-one staircase equals the printed tile translated by `(0,-1)`. -/
theorem mem_nstairN_iff_paper {d : ℤ} (hd : 2 ≤ d) (x : Site) :
    x ∈ nstairN d ↔ (x.1, x.2 + 1) ∈ paperNearStairTile d := by
  rw [mem_nstairN, mem_nstairF_iff_paper hd]

/-- The normalised near-one ladder equals the printed tile translated by `(0,-1)`. -/
theorem mem_nladderN_iff_paper {d : ℤ} (hd : 2 ≤ d) (x : Site) :
    x ∈ nladderN d ↔ (x.1, x.2 + 1) ∈ paperNearLadderTile d := by
  rw [mem_nladderN, mem_nladderF_iff_paper hd]

/-- The four base tiles used by `StandardTiles` are normalised (`c = 0`, `IsNormalised`) for `d ≥ 2`. -/
theorem stairF_isNormalised {d : ℤ} (hd : 2 ≤ d) : IsNormalised (stairF d) := by
  refine ⟨?_, fun p hp => ?_⟩
  · rw [mem_stairF hd]
    exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · rw [mem_stairF hd] at hp
    simp only [lexLE, Prod.fst_zero, Prod.snd_zero]
    omega

theorem ladderF_isNormalised {d : ℤ} (hd : 2 ≤ d) : IsNormalised (ladderF d) := by
  refine ⟨?_, fun p hp => ?_⟩
  · rw [mem_ladderF hd]
    have h0 : ((0 : Site).1 = 0 ∧ (0 : Site).2 = 0) := ⟨rfl, rfl⟩
    exact ⟨Or.inl h0, by omega⟩
  · rw [mem_ladderF hd] at hp
    simp only [lexLE, Prod.fst_zero, Prod.snd_zero]
    omega

theorem nstairN_isNormalised {d : ℤ} (hd : 2 ≤ d) : IsNormalised (nstairN d) := by
  refine ⟨?_, fun p hp => ?_⟩
  · rw [mem_nstairN, mem_nstairF hd]
    simp only [Prod.fst_zero, Prod.snd_zero]
    omega
  · rw [mem_nstairN, mem_nstairF hd] at hp
    simp only [lexLE, Prod.fst_zero, Prod.snd_zero] at hp ⊢
    omega

theorem nladderN_isNormalised {d : ℤ} (hd : 2 ≤ d) : IsNormalised (nladderN d) := by
  refine ⟨?_, fun p hp => ?_⟩
  · rw [mem_nladderN, mem_nladderF hd]
    simp only [Prod.fst_zero, Prod.snd_zero]
    omega
  · rw [mem_nladderN, mem_nladderF hd] at hp
    simp only [lexLE, Prod.fst_zero, Prod.snd_zero] at hp ⊢
    omega

/-- The lower-left point of the printed near-one staircase `paperNearStairTile d` is `(0,1)` (for `d ≥ 2`). -/
theorem nstairF_lowerLeft {d : ℤ} (hd : 2 ≤ d) :
    (0, 1) ∈ nstairF d ∧ ∀ p ∈ nstairF d, lexLE (0, 1) p := by
  refine ⟨?_, fun p hp => ?_⟩
  · rw [mem_nstairF hd]
    dsimp only
    omega
  · rw [mem_nstairF hd] at hp
    simp only [lexLE]
    omega

/-- The lower-left point of the printed near-one ladder `paperNearLadderTile d` is `(0,1)` (for `d ≥ 2`). -/
theorem nladderF_lowerLeft {d : ℤ} (hd : 2 ≤ d) :
    (0, 1) ∈ nladderF d ∧ ∀ p ∈ nladderF d, lexLE (0, 1) p := by
  refine ⟨?_, fun p hp => ?_⟩
  · rw [mem_nladderF hd]
    dsimp only
    omega
  · rw [mem_nladderF hd] at hp
    simp only [lexLE]
    omega

end FLatticePaper.Tiles.Standard
