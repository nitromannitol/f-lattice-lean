import FLatticePaper.Tiles.SiteJunction
import FLatticePaper.Tiles.HorizontalGlue
import FLatticePaper.Tiles.StandardTiles

/-! Task 53, marksIn (base families): the horizontal strings of the words `3^k` and `2^k`, and of `q p^m`, lie in the base tiles.

The strings are runs: a run of `q`s advances by `(1,1)` per tile and a run of `p`s by `(2,0)`; a `qq` pair is enlarged. The
bounds below are proved by induction over the snoc recursion (`stringSites_snoc_mem`), and each base tile is a filter over a box,
so membership is linear arithmetic (`omega`). -/

namespace FLatticePaper.Tiles.BaseFamilies

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.Standard FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Tiles.SiteJunction FLatticePaper.Tiles.SiteConcat FLatticePaper.Tiles.HorizontalGlue

theorem sumStep_rep_q (k : ℕ) : sumStep (List.replicate k Letter.q) = ((k : ℤ), (k : ℤ)) := by
  induction k with
  | zero => simp [sumStep]
  | succ k ih =>
    rw [List.replicate_succ, sumStep, ih]
    refine Prod.ext ?_ ?_
    all_goals simp [stepH]
    all_goals ring

theorem sumStep_rep_p (k : ℕ) : sumStep (List.replicate k Letter.p) = ((2 * (k : ℤ)), 0) := by
  induction k with
  | zero => simp [sumStep]
  | succ k ih =>
    rw [List.replicate_succ, sumStep, ih]
    refine Prod.ext ?_ ?_
    all_goals simp [stepH]
    all_goals ring

theorem getLast?_rep_succ (k : ℕ) (a : Letter) : (List.replicate (k + 1) a).getLast? = some a := by
  simp [List.replicate_succ']

/-- Membership in the string of `A ++ [l]`: a site of `A`, or a site of the last tile, which is at `sumStep A.tail + stepH l`
from the origin, enlarged exactly when `A` ends with `q` and `l = q`. -/
theorem stringSites_snoc_mem (A : List Letter) (hA : A ≠ []) (l : Letter) (z : ℤ × ℤ) :
    z ∈ stringSites false false (A ++ [l]) ↔
      z ∈ stringSites false false A ∨
        ∃ b ∈ baseSites l (A.getLast? == some Letter.q && l == Letter.q),
          z = (sumStep A.tail + stepH l) + b := by
  obtain ⟨a, A', rfl⟩ := List.exists_cons_of_ne_nil hA
  obtain ⟨pr, hpr⟩ : ∃ pr, (a :: A').getLast? = some pr := by
    cases h : (a :: A').getLast? with
    | none => simp at h
    | some pr => exact ⟨pr, rfl⟩
  have hs : startPos false false = (0, 0) := rfl
  simp only [stringSites_eq_sitesFrom, hs]
  rw [sitesFrom_append false false a A' [l] none (0, 0), hpr, List.mem_append]
  apply or_congr Iff.rfl
  rw [endOrigin_none_cons a A' (0, 0)]
  simp [sitesFrom, origins, dxdy_false_false, stepH, baseSites]
  constructor
  · rintro ⟨x, y, hb, h⟩
    refine ⟨x, y, hb, ?_⟩
    rw [← h]
    refine Prod.ext ?_ ?_ <;> simp
  · rintro ⟨x, y, hb, h⟩
    refine ⟨x, y, hb, ?_⟩
    rw [h]
    refine Prod.ext ?_ ?_ <;> simp

/-! ### Bounds of the runs -/

/-- The `q`-run `q^{k+1}`: its sites lie in the box `[0, k+1]²` and near the diagonal, `-2 ≤ y - x ≤ 2`. -/
theorem qrun_bounds (k : ℕ) : ∀ z ∈ stringSites false false (List.replicate (k + 1) Letter.q),
    0 ≤ z.1 ∧ z.1 ≤ (k : ℤ) + 1 ∧ 0 ≤ z.2 ∧ z.2 ≤ (k : ℤ) + 1 ∧ -2 ≤ z.2 - z.1 ∧ z.2 - z.1 ≤ 2 := by
  induction k with
  | zero =>
    intro z hz
    simp [stringSites, origins, baseSites, startPos] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> norm_num
  | succ k ih =>
    intro z hz
    have e : List.replicate (k + 1 + 1) Letter.q = List.replicate (k + 1) Letter.q ++ [Letter.q] := by
      simp [List.replicate_succ']
    rw [e, stringSites_snoc_mem _ (by simp) Letter.q z] at hz
    rcases hz with h | ⟨b, hb, rfl⟩
    · have := ih z h
      push_cast
      omega
    · have ht : (List.replicate (k + 1) Letter.q).tail = List.replicate k Letter.q := rfl
      have hen : ((List.replicate (k + 1) Letter.q).getLast? == some Letter.q && Letter.q == Letter.q) = true := by
        rw [getLast?_rep_succ]
        simp
      rw [hen] at hb
      rw [ht, sumStep_rep_q]
      simp only [baseSites, List.mem_cons, List.not_mem_nil, or_false] at hb
      simp only [stepH]
      push_cast
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num <;> omega

/-- The `p`-run `q p^m`: its sites lie in `[0, 2m+1] × [0, 2]`, with `x + y ≤ 2m + 3`, and off the origin `x + y ≥ 1`. -/
theorem prun_bounds (m : ℕ) : ∀ z ∈ stringSites false false (Letter.q :: List.replicate m Letter.p),
    0 ≤ z.1 ∧ z.1 ≤ 2 * (m : ℤ) + 1 ∧ 0 ≤ z.2 ∧ z.2 ≤ 2 ∧ z.1 + z.2 ≤ 2 * (m : ℤ) + 3 ∧
      (1 ≤ z.1 + z.2 ∨ (z.1 = 0 ∧ z.2 = 0)) := by
  induction m with
  | zero =>
    intro z hz
    simp [stringSites, origins, baseSites, startPos] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> norm_num
  | succ m ih =>
    intro z hz
    have e : Letter.q :: List.replicate (m + 1) Letter.p = (Letter.q :: List.replicate m Letter.p) ++ [Letter.p] := by
      simp [List.replicate_succ']
    rw [e, stringSites_snoc_mem _ (by simp) Letter.p z] at hz
    rcases hz with h | ⟨b, hb, rfl⟩
    · have := ih z h
      push_cast
      omega
    · have ht : (Letter.q :: List.replicate m Letter.p).tail = List.replicate m Letter.p := rfl
      rw [ht, sumStep_rep_p]
      simp only [baseSites] at hb
      simp only [stepH]
      push_cast
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num <;> omega

/-! ### Membership in the base tiles -/

/-- `z ∈ stairF (2m+1)` for `m ≥ 1`, from the bounds of `prun_bounds`. -/
theorem stairF_mem (m : ℕ) (hm : 1 ≤ m) (z : ℤ × ℤ)
    (hz : 0 ≤ z.1 ∧ z.1 ≤ 2 * (m : ℤ) + 1 ∧ 0 ≤ z.2 ∧ z.2 ≤ 2 ∧ z.1 + z.2 ≤ 2 * (m : ℤ) + 3 ∧
      (1 ≤ z.1 + z.2 ∨ (z.1 = 0 ∧ z.2 = 0))) :
    z ∈ stairF (2 * (m : ℤ) + 1) := by
  obtain ⟨x, y⟩ := z
  unfold stairF
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  simp only at hz ⊢
  have hm' : (1 : ℤ) ≤ m := by exact_mod_cast hm
  omega

/-- `z ∈ nstairN (2m+1)` for `m ≥ 1`: the shift of `nstairF` by `(0,-1)`, so `(z.1, z.2 + 1) ∈ nstairF`. -/
theorem nstairN_mem (m : ℕ) (hm : 1 ≤ m) (z : ℤ × ℤ)
    (hz : (0 ≤ z.1 ∧ z.1 ≤ 2 * (m : ℤ) + 2 ∧ 1 ≤ z.2 + 1 ∧ z.2 + 1 ≤ 4 * (m : ℤ) + 1 ∧
        -1 ≤ (z.2 + 1) - z.1 ∧ (z.2 + 1) - z.1 ≤ 2 * (m : ℤ) + 1) ∨
      (z.1 = 0 ∧ z.2 + 1 = 2 * (m : ℤ) + 2) ∨ (z.1 = 2 * (m : ℤ) + 2 ∧ z.2 + 1 = 2 * (m : ℤ))) :
    z ∈ nstairN (2 * (m : ℤ) + 1) := by
  obtain ⟨x, y⟩ := z
  unfold nstairN
  rw [mem_shift]
  unfold nstairF
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  simp only [Prod.fst_sub, Prod.snd_sub] at hz ⊢
  have hm' : (1 : ℤ) ≤ m := by exact_mod_cast hm
  omega

/-- `z ∈ nladderN (2m+2)` for `m ≥ 1`: the shift of `nladderF` by `(0,-1)`. -/
theorem nladderN_mem (m : ℕ) (hm : 1 ≤ m) (z : ℤ × ℤ)
    (hz : (-1 ≤ z.1 ∧ z.1 ≤ 2 * (m : ℤ) + 3 ∧ 1 ≤ z.2 + 1 ∧ z.2 + 1 ≤ 6 * (m : ℤ) + 5 ∧
        -1 ≤ (z.2 + 1) - z.1 ∧ (z.2 + 1) - z.1 ≤ 4 * (m : ℤ) + 5 ∧ ¬(z.1 = -1 ∧ z.2 + 1 ≤ 2 * (m : ℤ) + 3) ∧
        ¬(z.1 = 2 * (m : ℤ) + 3 ∧ 4 * (m : ℤ) + 3 ≤ z.2 + 1)) ∨
      (z.1 = 2 * (m : ℤ) + 3 ∧ z.2 + 1 = 2 * (m : ℤ) + 1)) :
    z ∈ nladderN (2 * (m : ℤ) + 2) := by
  obtain ⟨x, y⟩ := z
  unfold nladderN
  rw [mem_shift]
  unfold nladderF
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  simp only [Prod.fst_sub, Prod.snd_sub] at hz ⊢
  have hm' : (1 : ℤ) ≤ m := by exact_mod_cast hm
  omega

/-- `z ∈ ladderF (2n+2)` for `n ≥ 0`, from the bounds of the two parts of `q p^n q p^{n+1}`. -/
theorem ladderF_mem (n : ℕ) (z : ℤ × ℤ)
    (hz : (0 ≤ z.1 ∧ z.1 ≤ 2 * (n : ℤ) + 1 ∧ 0 ≤ z.2 ∧ z.2 ≤ 2 ∧ z.1 + z.2 ≤ 2 * (n : ℤ) + 3 ∧
        (1 ≤ z.1 + z.2 ∨ (z.1 = 0 ∧ z.2 = 0))) ∨
      (2 * (n : ℤ) + 1 ≤ z.1 ∧ z.1 ≤ 4 * (n : ℤ) + 4 ∧ 1 ≤ z.2 ∧ z.2 ≤ 3 ∧
        z.1 + z.2 ≤ 4 * (n : ℤ) + 7)) :
    z ∈ ladderF (2 * (n : ℤ) + 2) := by
  obtain ⟨x, y⟩ := z
  unfold ladderF
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  simp only at hz ⊢
  omega

end FLatticePaper.Tiles.BaseFamilies
