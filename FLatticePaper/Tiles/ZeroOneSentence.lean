import FLatticePaper.Tiles.ZeroOneRespects

/-! The checks `respectsB` and `commonB` hold for every zero-one family of a letter sequence (task 16). -/

namespace FLatticePaper.Tiles
open Finset

theorem adjacentSites_iff (x y : Site) :
    adjacentSites x y = true ↔ (x - y).1.natAbs + (x - y).2.natAbs = 1 := by
  unfold adjacentSites
  simp only [beq_iff_eq, Prod.fst_sub, Prod.snd_sub]

theorem overlap_none_of_disjoint (o : Orientation) (rev : Bool) (ℓ : ℕ → Letter) (n k : ℕ)
    (hdis : ∀ x ∈ (familyF o rev ℓ n).dom k, x ∉ (familyF o rev ℓ n).dom (k + 1)) :
    overlapWitness (ℓ k) (ℓ (k + 1)) (stepOf o rev (ℓ k) (ℓ (k + 1))) = none := by
  cases h : overlapWitness (ℓ k) (ℓ (k + 1)) (stepOf o rev (ℓ k) (ℓ (k + 1))) with
  | none => rfl
  | some p =>
    exfalso
    have hw := h
    unfold overlapWitness at hw
    have hp : p ∈ tileSites (ℓ k) := List.mem_of_find?_eq_some hw
    have hq : p - stepOf o rev (ℓ k) (ℓ (k + 1)) ∈ tileSites (ℓ (k + 1)) := by
      have := List.find?_some hw
      simpa using this
    have hxk : p + posF o rev ℓ k ∈ (familyF o rev ℓ n).dom k := by
      rw [dom_eq_map]
      exact List.mem_map.mpr ⟨p, hp, rfl⟩
    have hxk1 : p + posF o rev ℓ k ∈ (familyF o rev ℓ n).dom (k + 1) := by
      rw [dom_eq_map]
      refine List.mem_map.mpr ⟨p - stepOf o rev (ℓ k) (ℓ (k + 1)), hq, ?_⟩
      show p - stepOf o rev (ℓ k) (ℓ (k + 1)) + posF o rev ℓ (k + 1) = p + posF o rev ℓ k
      rw [show posF o rev ℓ (k + 1) = posF o rev ℓ k + stepOf o rev (ℓ k) (ℓ (k + 1)) from rfl]
      abel
    exact hdis _ hxk hxk1

theorem respectsB_eq_true (o : Orientation) (rev : Bool) (ℓ : ℕ → Letter) (n : ℕ) :
    (familyF o rev ℓ n).respectsB o = true := by
  unfold ZOFamily.respectsB
  rw [List.all_eq_true]
  intro k _
  split
  · rw [Bool.and_eq_true]
    refine ⟨decide_eq_true (respects_slope o rev ℓ n k), ?_⟩
    split
    · rename_i hdis
      have hdis' : ∀ x ∈ (familyF o rev ℓ n).dom k, x ∉ (familyF o rev ℓ n).dom (k + 1) :=
        fun x hx => of_decide_eq_true (List.all_eq_true.mp hdis x hx)
      rw [List.all_eq_true]
      intro x hx
      rw [List.all_eq_true]
      intro y hy
      by_cases hadj : adjacentSites x y = true
      · rw [if_pos hadj]
        have hno := overlap_none_of_disjoint o rev ℓ n k hdis'
        rw [dom_eq_map] at hx hy
        obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hx
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
        have e : s0 + posF o rev ℓ k - (t + posF o rev ℓ (k + 1)) =
            s0 - t - stepOf o rev (ℓ k) (ℓ (k + 1)) := by
          rw [show posF o rev ℓ (k + 1) = posF o rev ℓ k + stepOf o rev (ℓ k) (ℓ (k + 1)) from rfl]
          abel
        have hadjl := (adjacentSites_iff _ _).mp hadj
        rw [e] at hadjl
        have key := odo_adjacent o rev ℓ n k s0 t hs0 ht hadjl hno
        cases o with
        | horizontal =>
          simp only [beq_iff_eq]
          have h0 : targetOf Orientation.horizontal = 0 := rfl
          rw [h0] at key
          exact (sub_eq_zero.mp key).symm
        | vertical =>
          simp only [beq_iff_eq]
          exact key
      · rw [if_neg hadj]
    · rfl
  · rfl

theorem commonB_eq_true (o : Orientation) (rev : Bool) (ℓ : ℕ → Letter) (n : ℕ) :
    (familyF o rev ℓ n).commonB = true := by
  unfold ZOFamily.commonB
  rw [List.all_eq_true]
  intro k _
  rw [List.all_eq_true]
  intro l _
  by_cases hkl : k = l
  · rw [if_pos hkl]
  · rw [if_neg hkl, List.all_eq_true]
    intro x hx
    rw [List.mem_filter] at hx
    obtain ⟨hxk, hxl⟩ := hx
    have hxl' : x ∈ (familyF o rev ℓ n).dom l := of_decide_eq_true hxl
    rw [beq_iff_eq]
    rcases (by omega : l = k + 1 ∨ k = l + 1 ∨ k + 2 ≤ l ∨ l + 2 ≤ k) with h | h | h | h
    · subst h
      exact odo_overlap o rev ℓ n k x hxk hxl'
    · subst h
      exact (odo_overlap o rev ℓ n l x hxl' hxk).symm
    · exact absurd rfl (dom_disjoint o rev ℓ n k l h x x hxk hxl')
    · exact absurd rfl (dom_disjoint o rev ℓ n l k h x x hxl' hxk)

/-- The zero-one family of a letter sequence on `n` tiles satisfies both checks, for every letter sequence. -/
theorem familyF_checks (o : Orientation) (rev : Bool) (ℓ : ℕ → Letter) (n : ℕ) :
    (familyF o rev ℓ n).respectsB o = true ∧ (familyF o rev ℓ n).commonB = true :=
  ⟨respectsB_eq_true o rev ℓ n, commonB_eq_true o rev ℓ n⟩

end FLatticePaper.Tiles
