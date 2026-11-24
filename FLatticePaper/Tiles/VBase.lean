import FLatticePaper.Tiles.VStep
import FLatticePaper.Tiles.BaseFamilies
import FLatticePaper.Tiles.BaseInvariant

/-! Task 53, marksIn (vertical base words): the vertical invariant of `[]`, `3^n` and `2^n` (`n ≥ 1`).

The vertical blocks of the base words are the column words `q p^m` (`vert (q :: rep m p) = rep m q ++ [p]`) and `q^k p`
(`vert (rep k q ++ [p]) = q :: rep k p`). Their vertical strings are bounded by induction over the snoc recursion (`vsnoc_mem`,
with the closed forms of the end origin from `VJunction.vend_some`), and the base tiles are filters over boxes. -/

namespace FLatticePaper.Tiles.VBase

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.Standard FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Tiles.SiteJunction FLatticePaper.Tiles.SiteConcat FLatticePaper.Tiles.HorizontalGlue
open FLatticePaper.Tiles.HorizontalStep FLatticePaper.Tiles.VJunction FLatticePaper.Tiles.VGlue
open FLatticePaper.Tiles.VStep FLatticePaper.Tiles.CeilWords FLatticePaper.Construction
open FLatticePaper.Tiles.BaseInvariant

/-! ### Words -/

theorem vert_q_p (m : ℕ) : vert (List.replicate m Letter.q ++ [Letter.p]) = Letter.q :: List.replicate m Letter.p := by
  unfold vert
  simp [List.reverse_append, List.map_replicate, swapLetter]

theorem vert_q_run (m : ℕ) : vert (Letter.q :: List.replicate m Letter.p) = List.replicate m Letter.q ++ [Letter.p] := by
  unfold vert
  simp [List.reverse_cons, List.map_replicate, swapLetter]

theorem dropLast_rep_succ (a : Letter) (n : ℕ) :
    (List.replicate (n + 1) a).dropLast = List.replicate n a := by
  rw [List.replicate_succ', List.dropLast_concat]

theorem getLast?_rep_succ' (n : ℕ) (a : Letter) : (List.replicate (n + 1) a).getLast? = some a := by
  rw [List.replicate_succ', List.getLast?_concat]

/-! ### Single letters appended -/

theorem sitesFrom_single (vt rv : Bool) (pr l : Letter) (E : ℤ × ℤ) :
    sitesFrom vt rv (some pr) E [l] =
      (baseSites l (!vt && pr == Letter.q && l == Letter.q)).map fun b => (E + dxdy vt rv pr l) + b := by
  unfold sitesFrom
  rw [origins_some_cons_gen, origins, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rfl

/-- Membership in the vertical string of `A ++ [l]`. -/
theorem vsnoc_mem (A : List Letter) (pr l : Letter) (hA : A ≠ []) (hpr : A.getLast? = some pr) (z : ℤ × ℤ) :
    z ∈ VS0 (A ++ [l]) ↔ z ∈ VS0 A ∨
      ∃ b ∈ baseSites l false, z = (endOrigin true true none (0, 0) A + dxdy true true pr l) + b := by
  obtain ⟨a, A', rfl⟩ := List.exists_cons_of_ne_nil hA
  unfold VS0
  rw [sitesFrom_append true true a A' [l] none (0, 0), hpr, List.mem_append]
  apply or_congr Iff.rfl
  rw [endOrigin_none_cons_gen, sitesFrom_single]
  simp only [Bool.not_true, Bool.false_and, List.mem_map]
  constructor
  · rintro ⟨b, hb, h⟩
    exact ⟨b, hb, by rw [← h]⟩
  · rintro ⟨b, hb, h⟩
    exact ⟨b, hb, by rw [h]⟩

/-! ### Closed forms of the end origins -/

theorem e_q_run (k : ℕ) : endOrigin true true none (0, 0) (Letter.q :: List.replicate k Letter.q) = (0, 2 * (k : ℤ)) := by
  rw [endOrigin_none_cons_gen, vend_some]
  have h1 : ((Letter.q :: List.replicate k Letter.q).dropLast).count Letter.p = 0 := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [List.replicate_succ, List.dropLast_cons_of_ne_nil (by simp)]
      simp [List.count_replicate]
  rw [h1]
  refine Prod.ext ?_ ?_ <;> simp [List.count_replicate]

theorem e_p_run (m : ℕ) :
    endOrigin true true none (0, 0) (Letter.q :: List.replicate (m + 1) Letter.p) = (-(m : ℤ), (m : ℤ) + 1) := by
  rw [endOrigin_none_cons_gen, vend_some]
  have h1 : ((Letter.q :: List.replicate (m + 1) Letter.p).dropLast) = Letter.q :: List.replicate m Letter.p := by
    rw [List.dropLast_cons_of_ne_nil (by simp), dropLast_rep_succ]
  rw [h1]
  refine Prod.ext ?_ ?_ <;> simp [List.count_replicate]

/-! ### The bounds of the families -/

/-- The column `q p^{m+1}`: its vertical sites lie in `-m ≤ x ≤ 1`, `0 ≤ y ≤ m+3`, and off the origin `x + y ≥ 1`. -/
theorem Pb (m : ℕ) : ∀ z ∈ VS0 (Letter.q :: List.replicate (m + 1) Letter.p),
    -(m : ℤ) ≤ z.1 ∧ z.1 ≤ 1 ∧ 0 ≤ z.2 ∧ z.2 ≤ (m : ℤ) + 3 ∧ (1 ≤ z.1 + z.2 ∨ (z.1 = 0 ∧ z.2 = 0)) := by
  induction m with
  | zero =>
    intro z hz
    have e : Letter.q :: List.replicate (0 + 1) Letter.p = [Letter.q] ++ [Letter.p] := by simp
    rw [e, vsnoc_mem [Letter.q] Letter.q Letter.p (by simp) rfl] at hz
    rcases hz with h | ⟨b, hb, rfl⟩
    · unfold VS0 at h
      simp [sitesFrom, origins, baseSites] at h
      rcases h with rfl | rfl | rfl | rfl <;> norm_num
    · have e0 : endOrigin true true none (0, 0) [Letter.q] = (0, 0) := by simp [endOrigin, origins]
      rw [e0]
      simp [baseSites, dxdy] at hb ⊢
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  | succ m ih =>
    intro z hz
    have e : Letter.q :: List.replicate (m + 1 + 1) Letter.p =
        (Letter.q :: List.replicate (m + 1) Letter.p) ++ [Letter.p] := by
      simp [List.replicate_succ']
    have hpr : (Letter.q :: List.replicate (m + 1) Letter.p).getLast? = some Letter.p := by
      rw [List.getLast?_cons_of_ne_nil (by simp), getLast?_rep_succ']
    rw [e, vsnoc_mem _ Letter.p Letter.p (by simp) hpr] at hz
    rcases hz with h | ⟨b, hb, rfl⟩
    · have := ih z h
      push_cast
      omega
    · rw [e_p_run]
      simp only [dxdy]
      simp [baseSites] at hb
      push_cast
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num <;> omega

/-- The column `q^{k} p` (`k ≥ 1`): its vertical sites lie in `0 ≤ x ≤ 1`, `0 ≤ y ≤ 2k+1`. -/
theorem Qb (k : ℕ) : ∀ z ∈ VS0 (List.replicate (k + 1) Letter.q),
    0 ≤ z.1 ∧ z.1 ≤ 1 ∧ 0 ≤ z.2 ∧ z.2 ≤ 2 * (k : ℤ) + 1 := by
  induction k with
  | zero =>
    intro z hz
    unfold VS0 at hz
    simp [sitesFrom, origins, baseSites] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> norm_num
  | succ k ih =>
    intro z hz
    have e : List.replicate (k + 1 + 1) Letter.q = List.replicate (k + 1) Letter.q ++ [Letter.q] := by
      simp [List.replicate_succ']
    rw [e, vsnoc_mem _ Letter.q Letter.q (by simp) (getLast?_rep_succ' k Letter.q)] at hz
    rcases hz with h | ⟨b, hb, rfl⟩
    · have := ih z h
      push_cast
      omega
    · have e' : List.replicate (k + 1) Letter.q = Letter.q :: List.replicate k Letter.q := rfl
      rw [e', e_q_run]
      simp only [dxdy]
      simp [baseSites] at hb
      push_cast
      rcases hb with rfl | rfl | rfl | rfl <;> norm_num <;> omega

/-- The word `q^{k+1} p`: its vertical sites lie in `0 ≤ x ≤ 1`, `0 ≤ y ≤ 2k+3`. -/
theorem Nb (k : ℕ) : ∀ z ∈ VS0 (List.replicate (k + 1) Letter.q ++ [Letter.p]),
    0 ≤ z.1 ∧ z.1 ≤ 1 ∧ 0 ≤ z.2 ∧ z.2 ≤ 2 * (k : ℤ) + 3 := by
  intro z hz
  rw [vsnoc_mem _ Letter.q Letter.p (by simp) (getLast?_rep_succ' k Letter.q)] at hz
  rcases hz with h | ⟨b, hb, rfl⟩
  · have := Qb k z h
    omega
  · have e' : List.replicate (k + 1) Letter.q = Letter.q :: List.replicate k Letter.q := rfl
    rw [e', e_q_run]
    simp only [dxdy]
    simp [baseSites] at hb
    push_cast
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num <;> omega


/-! ### The base tiles from bounds -/

theorem stairF_gen (d : ℤ) (z : ℤ × ℤ) (hd : 2 ≤ d)
    (h : (2 - d ≤ z.1 ∧ z.1 ≤ d ∧ 0 ≤ z.2 ∧ z.2 ≤ d + 1 ∧ 1 ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ d + 2) ∨
      (z.1 = 0 ∧ z.2 = 0)) : z ∈ stairF d := by
  obtain ⟨x, y⟩ := z
  unfold stairF
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  simp only at h ⊢
  omega

theorem ladderF_gen (d : ℤ) (z : ℤ × ℤ) (hd : 2 ≤ d)
    (h : (z.1 = 0 ∧ z.2 = 0) ∨ (2 - d ≤ z.1 ∧ z.1 ≤ 2 * d ∧ 0 ≤ z.2 ∧ z.2 ≤ d + 2 ∧ 1 ≤ z.1 + z.2 ∧
      z.1 + z.2 ≤ 2 * d + 3))
    (hn : ¬((d ≤ z.1 ∧ z.2 = 0) ∨ (z.1 ≤ 2 ∧ z.2 = d + 2))) : z ∈ ladderF d := by
  obtain ⟨x, y⟩ := z
  unfold ladderF
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  simp only at h hn ⊢
  omega

theorem nstairN_gen (d : ℤ) (z : ℤ × ℤ) (hd : 3 ≤ d)
    (h : (0 ≤ z.1 ∧ z.1 ≤ d + 1 ∧ 1 ≤ z.2 + 1 ∧ z.2 + 1 ≤ 2 * d - 1 ∧ -1 ≤ (z.2 + 1) - z.1 ∧
        (z.2 + 1) - z.1 ≤ d) ∨
      (z.1 = 0 ∧ z.2 + 1 = d + 1) ∨ (z.1 = d + 1 ∧ z.2 + 1 = d - 1)) : z ∈ nstairN d := by
  obtain ⟨x, y⟩ := z
  unfold nstairN
  rw [mem_shift]
  unfold nstairF
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  simp only [Prod.fst_sub, Prod.snd_sub] at h ⊢
  omega

theorem nladderN_gen (d : ℤ) (z : ℤ × ℤ) (hd : 2 ≤ d)
    (h : ((z.1 = -1 ∧ z.2 + 1 = 2 * d + 1) ∨ (z.1 = d + 1 ∧ z.2 + 1 = d - 1) ∨
        ((z.2 + 1) - z.1 = d ∧ 0 < z.1 ∧ z.1 < d) ∨
        (-1 ≤ z.1 ∧ z.1 ≤ d + 1 ∧ 1 ≤ z.2 + 1 ∧ z.2 + 1 ≤ 3 * d - 1 ∧ -1 ≤ (z.2 + 1) - z.1 ∧
          (z.2 + 1) - z.1 ≤ 2 * d + 1)) ∧
        ¬((z.1 = -1 ∧ z.2 + 1 ≤ d + 1) ∨ (z.1 = d + 1 ∧ 2 * d - 1 ≤ z.2 + 1))) : z ∈ nladderN d := by
  obtain ⟨x, y⟩ := z
  unfold nladderN
  rw [mem_shift]
  unfold nladderF
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  simp only [Prod.fst_sub, Prod.snd_sub] at h ⊢
  omega

/-! ### The families -/

/-- The column `q p^{m+1}` lies in `stairF (m+2)`. -/
theorem P_stair (m : ℕ) (d : ℤ) (hd : d = (m : ℤ) + 2) :
    ∀ z ∈ VS0 (Letter.q :: List.replicate (m + 1) Letter.p), z ∈ stairF d := by
  intro z hz
  have hb := Pb m z hz
  obtain ⟨h1, h2, h3, h4, h5⟩ := hb
  exact stairF_gen d z (by rw [hd]; omega) (by rw [hd]; omega)

/-- The column `q p^{m+1}` lies in `ladderF (m+2)`. -/
theorem P_ladder (m : ℕ) (d : ℤ) (hd : d = (m : ℤ) + 2) :
    ∀ z ∈ VS0 (Letter.q :: List.replicate (m + 1) Letter.p), z ∈ ladderF d := by
  intro z hz
  obtain ⟨h1, h2, h3, h4, h5⟩ := Pb m z hz
  exact ladderF_gen d z (by rw [hd]; omega) (by rw [hd]; omega) (by rw [hd]; omega)

/-- The column `q^{k+1} p` lies in `nstairN (2k+3)`. -/
theorem N_stair (k : ℕ) (d : ℤ) (hd : d = 2 * (k : ℤ) + 3) :
    ∀ z ∈ VS0 (List.replicate (k + 1) Letter.q ++ [Letter.p]), z ∈ nstairN d := by
  intro z hz
  obtain ⟨h1, h2, h3, h4⟩ := Nb k z hz
  exact nstairN_gen d z (by rw [hd]; omega) (by rw [hd]; omega)

/-- The composite `q^{n+1} p · q^n p` (`n ≥ 1`) lies in `nladderN (2n+2)`. -/
theorem C_comp (j : ℕ) (d : ℤ) (hd : d = 2 * ((j + 1 : ℕ) : ℤ) + 2) :
    ∀ z ∈ VS0 ((List.replicate (j + 2) Letter.q ++ [Letter.p]) ++ (List.replicate (j + 1) Letter.q ++ [Letter.p])),
      z ∈ nladderN d := by
  intro z hz
  have hA : ∃ Y', (List.replicate (j + 2) Letter.q ++ [Letter.p]) = Letter.q :: Y' :=
    ⟨List.replicate (j + 1) Letter.q ++ [Letter.p], rfl⟩
  have hB : ∃ Z', (List.replicate (j + 1) Letter.q ++ [Letter.p]) = Letter.q :: Z' :=
    ⟨List.replicate j Letter.q ++ [Letter.p], rfl⟩
  rw [vjunction_gen _ _ hA hB, List.mem_append] at hz
  have hjA : jv (List.replicate (j + 2) Letter.q ++ [Letter.p]) = (-1, 2 * (j : ℤ) + 5) := by
    refine Prod.ext ?_ ?_
    all_goals simp [jv, List.count_append, List.count_replicate]
    all_goals ring
  rw [hjA] at hz
  rcases hz with h | h
  swap
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 h
  · obtain ⟨h1, h2, h3, h4⟩ := Nb j w hw
    apply nladderN_gen d _ (by rw [hd]; omega)
    rw [hd]
    simp only [Prod.fst_add, Prod.snd_add]
    push_cast at h2 h4 ⊢
    omega
  · obtain ⟨h1, h2, h3, h4⟩ := Nb (j + 1) z h
    apply nladderN_gen d z (by rw [hd]; omega)
    rw [hd]
    push_cast at h2 h4 ⊢
    omega

/-! ### The base words -/

theorem hv_q_one : ∀ z ∈ VS0 [Letter.q], z ∈ oneTile := by
  intro z hz
  unfold VS0 at hz
  simp [sitesFrom, origins, baseSites] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> decide

theorem hv_p_zero : ∀ z ∈ VS0 [Letter.p], z ∈ zeroTile := by
  intro z hz
  unfold VS0 at hz
  simp [sitesFrom, origins, baseSites] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem VInv_nil : VInv [] := by
  unfold VInv
  have c1 : vert (quadAt [] (swapW [])).childP = Letter.q :: List.replicate 2 Letter.p := rfl
  have c2 : vert (quadAt [] (swapW [])).childQ = List.replicate 1 Letter.q ++ [Letter.p] := rfl
  have c3 : vert (quadAt [] (swapW [])).parentP = [Letter.q] := rfl
  have c4 : vert (quadAt [] (swapW [])).parentQ = [Letter.p] := rfl
  rw [c1, c2, c3, c4]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact P_stair 1 3 (by norm_num)
  · exact N_stair 0 3 (by norm_num)
  · exact hv_q_one
  · exact hv_p_zero

theorem VInv_three (j : ℕ) : VInv (List.replicate (j + 1) Digit.three) := by
  unfold VInv
  have hsw : swapW (List.replicate (j + 1) Digit.three) = List.replicate (j + 1) Digit.two := by
    unfold swapW
    rw [List.map_replicate]
    rfl
  rw [hsw, quad2 (j + 1)]
  simp only [vert_q_p]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [evenTile_three]
    exact P_stair (2 * (j + 1) + 1) _ (by push_cast; ring)
  · rw [oddTile_three (j + 1) (by omega)]
    exact P_ladder (2 * (j + 1)) _ (by push_cast; ring)
  · rw [tEven_state_three]
    exact P_stair (2 * j + 1) _ (by push_cast; ring)
  · rw [tOdd_state_three]
    exact hv_p_zero


theorem VInv_two (j : ℕ) : VInv (List.replicate (j + 1) Digit.two) := by
  unfold VInv
  have hsw : swapW (List.replicate (j + 1) Digit.two) = List.replicate (j + 1) Digit.three := by
    unfold swapW
    rw [List.map_replicate]
    rfl
  rw [hsw, quad3 (j + 1)]
  have hvp : vert [Letter.p] = [Letter.q] := rfl
  simp only [vert_append, vert_q_run, hvp]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [evenTile_two (j + 1) (by omega)]
    exact C_comp j _ rfl
  · rw [oddTile_two]
    exact N_stair (j + 1) _ rfl
  · rw [tEven_state_two]
    exact hv_q_one
  · rw [tOdd_state_two]
    exact N_stair j _ rfl

/-- The vertical invariant of every word, from the base words (the same induction as the horizontal one). -/
theorem vinv_all (w : Word) : VInv w := by
  induction w using List.reverseRecOn with
  | nil => exact VInv_nil
  | append_singleton v d ih =>
    cases d with
    | one => exact vinv_step_one v ih
    | two =>
      by_cases hv : ∀ x ∈ v, x = Digit.two
      · have e : v ++ [Digit.two] = List.replicate (v.length + 1) Digit.two := by
          refine List.eq_replicate_iff.2 ⟨by simp, fun x hx => ?_⟩
          rcases List.mem_append.1 hx with h | h
          · exact hv x h
          · simp at h
            exact h
        rw [e]
        exact VInv_two v.length
      · exact vinv_step_two v ih hv
    | three =>
      by_cases hv : ∀ x ∈ v, x = Digit.three
      · have e : v ++ [Digit.three] = List.replicate (v.length + 1) Digit.three := by
          refine List.eq_replicate_iff.2 ⟨by simp, fun x hx => ?_⟩
          rcases List.mem_append.1 hx with h | h
          · exact hv x h
          · simp at h
            exact h
        rw [e]
        exact VInv_three v.length
      · exact vinv_step_three v ih hv

/-- The vertical strings of the odd and even standard tiles lie in the tiles. -/
theorem vertical_marks (w : Word) :
    HV (vert (quadAt [] (swapW w)).childQ) (oddTile w) ∧ HV (vert (quadAt [] (swapW w)).childP) (evenTile w) :=
  ⟨(vinv_all w).2.1, (vinv_all w).1⟩

end FLatticePaper.Tiles.VBase

