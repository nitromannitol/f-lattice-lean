import FLatticePaper.Tiles.ZeroOneGeometry
import Mathlib.Tactic.LinearCombination

/-! The respect and common-extension conditions of the zero-one family, for every word (task 16). -/

namespace FLatticePaper.Tiles
open Finset

theorem dom_disjoint_two (o : Orientation) (rev : Bool) (ℓ : ℕ → Letter) (n k : ℕ) (x y : Site)
    (hx : x ∈ (familyF o rev ℓ n).dom k) (hy : y ∈ (familyF o rev ℓ n).dom (k + 2)) : x ≠ y := by
  unfold ZOFamily.dom familyF at hx hy
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hy
  dsimp only
  have hpos : posF o rev ℓ (k + 2) =
      posF o rev ℓ k + (stepOf o rev (ℓ k) (ℓ (k + 1)) + stepOf o rev (ℓ (k + 1)) (ℓ (k + 2))) := by
    simp only [posF, add_assoc]
  rw [hpos]
  intro h
  have h' : p + posF o rev ℓ k = (r + (stepOf o rev (ℓ k) (ℓ (k + 1)) + stepOf o rev (ℓ (k + 1)) (ℓ (k + 2))))
      + posF o rev ℓ k := by
    rw [h]
    abel
  exact distance_two_disjoint o (orientation_mem o) rev (bool_mem rev) (ℓ k) (letter_mem _) (ℓ (k + 1))
    (letter_mem _) (ℓ (k + 2)) (letter_mem _) p hp r hr (add_right_cancel h')

theorem dom_disjoint (o : Orientation) (rev : Bool) (ℓ : ℕ → Letter) (n k m : ℕ) (hkm : k + 2 ≤ m)
    (x y : Site) (hx : x ∈ (familyF o rev ℓ n).dom k) (hy : y ∈ (familyF o rev ℓ n).dom m) : x ≠ y := by
  rcases Nat.lt_or_ge (k + 2) m with h | h
  · exact dom_disjoint_far o rev ℓ n k m (by omega) x hx y hy
  · have hm : m = k + 2 := by omega
    subst hm
    exact dom_disjoint_two o rev ℓ n k x y hx hy

theorem overlapWitness_spec (a b : Letter) (s p0 : Site) (hp0 : p0 ∈ tileSites a)
    (hq0 : p0 - s ∈ tileSites b) :
    ∃ p, overlapWitness a b s = some p ∧ p ∈ tileSites a ∧ p - s ∈ tileSites b := by
  unfold overlapWitness
  cases h : (tileSites a).find? (fun p => decide (p - s ∈ tileSites b)) with
  | none =>
    have := (List.find?_eq_none.mp h) p0 hp0
    simp [hq0] at this
  | some p =>
    refine ⟨p, rfl, List.mem_of_find?_eq_some h, ?_⟩
    have := List.find?_some h
    simpa using this

theorem overlapWitness_none (a b : Letter) (s : Site) (h : overlapWitness a b s = none)
    (p : Site) (hp : p ∈ tileSites a) : p - s ∉ tileSites b := by
  unfold overlapWitness at h
  intro hq
  have := List.find?_eq_none.mp h p hp
  simp [hq] at this

/-- The constant increment of an overlap step. -/
theorem betaOf_overlap (o : Orientation) (rev : Bool) (ℓ : ℕ → Letter) (k : ℕ) (p : Site)
    (hw : overlapWitness (ℓ k) (ℓ (k + 1)) (stepOf o rev (ℓ k) (ℓ (k + 1))) = some p) :
    betaOf o rev ℓ k =
      (baseOdometer (ℓ k) p - baseOdometer (ℓ (k + 1)) (p - stepOf o rev (ℓ k) (ℓ (k + 1)))
        - dotS (deltaOf o (ℓ k) (ℓ (k + 1))) p) - dotS (deltaOf o (ℓ k) (ℓ (k + 1))) (posF o rev ℓ k) := by
  unfold betaOf
  simp only [hw]

theorem odo_overlap (o : Orientation) (rev : Bool) (ℓ : ℕ → Letter) (n k : ℕ) (x : Site)
    (hx0 : x ∈ (familyF o rev ℓ n).dom k) (hx1 : x ∈ (familyF o rev ℓ n).dom (k + 1)) :
    (familyF o rev ℓ n).odo k x = (familyF o rev ℓ n).odo (k + 1) x := by
  unfold ZOFamily.dom familyF at hx0 hx1
  dsimp only at hx0 hx1
  obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hx0
  obtain ⟨t, ht, ht'⟩ := List.mem_map.mp hx1
  have hpos : posF o rev ℓ (k + 1) = posF o rev ℓ k + stepOf o rev (ℓ k) (ℓ (k + 1)) := rfl
  rw [hpos] at ht'
  have hts : s0 - stepOf o rev (ℓ k) (ℓ (k + 1)) = t := by
    have h1 := congrArg Prod.fst ht'
    have h2 := congrArg Prod.snd ht'
    simp only [Prod.fst_add, Prod.snd_add] at h1 h2
    exact Prod.ext (by simp only [Prod.fst_sub]; omega) (by simp only [Prod.snd_sub]; omega)
  have ht2 : s0 - stepOf o rev (ℓ k) (ℓ (k + 1)) ∈ tileSites (ℓ (k + 1)) := by rw [hts]; exact ht
  obtain ⟨p, hw, hp, hpq⟩ :=
    overlapWitness_spec (ℓ k) (ℓ (k + 1)) (stepOf o rev (ℓ k) (ℓ (k + 1))) s0 hs0 ht2
  have hcons := overlap_consistent o (orientation_mem o) rev (bool_mem rev) (ℓ k) (letter_mem _)
    (ℓ (k + 1)) (letter_mem _) p hp s0 hs0 hpq ht2
  have hb := betaOf_overlap o rev ℓ k p hw
  have ha : aF o ℓ (k + 1) = aF o ℓ k + deltaOf o (ℓ k) (ℓ (k + 1)) := rfl
  have hbb : bF o rev ℓ (k + 1) = bF o rev ℓ k + betaOf o rev ℓ k := rfl
  have e : s0 + posF o rev ℓ k - (posF o rev ℓ k + stepOf o rev (ℓ k) (ℓ (k + 1))) =
      s0 - stepOf o rev (ℓ k) (ℓ (k + 1)) := by abel
  simp only [ZOFamily.odo, familyF, hpos, e, ha, hbb, hb, Prod.fst_add, Prod.snd_add, add_sub_cancel_right,
    dotS] at hcons ⊢
  linear_combination (-1 : ℤ) * hcons

theorem adjWitness_spec (a b : Letter) (s s0 t : Site) (hs0 : s0 ∈ tileSites a) (ht : t ∈ tileSites b)
    (hadj : (s0 - t - s).1.natAbs + (s0 - t - s).2.natAbs = 1) :
    ∃ p q, adjWitness a b s = some (p, q) ∧ p ∈ tileSites a ∧ q ∈ tileSites b ∧
      (p - q - s).1.natAbs + (p - q - s).2.natAbs = 1 := by
  unfold adjWitness
  cases h : ((tileSites a).flatMap fun p => (tileSites b).map fun q => (p, q)).find? (fun pq =>
      decide ((pq.1 - pq.2 - s).1.natAbs + (pq.1 - pq.2 - s).2.natAbs = 1)) with
  | none =>
    have hmem : (s0, t) ∈ (tileSites a).flatMap fun p => (tileSites b).map fun q => (p, q) := by
      rw [List.mem_flatMap]
      exact ⟨s0, hs0, List.mem_map.mpr ⟨t, ht, rfl⟩⟩
    exact absurd (decide_eq_true hadj) (List.find?_eq_none.mp h (s0, t) hmem)
  | some pq =>
    obtain ⟨p, q⟩ := pq
    have hpq := List.find?_some h
    have hmem := List.mem_of_find?_eq_some h
    rw [List.mem_flatMap] at hmem
    obtain ⟨p', hp', hq'⟩ := hmem
    obtain ⟨q', hq'', hpair⟩ := List.mem_map.mp hq'
    simp only [Prod.mk.injEq] at hpair
    obtain ⟨rfl, rfl⟩ := hpair
    refine ⟨p', q', rfl, hp', hq'', ?_⟩
    simpa using hpq

theorem odo_adjacent (o : Orientation) (rev : Bool) (ℓ : ℕ → Letter) (n k : ℕ) (s0 t : Site)
    (hs0 : s0 ∈ tileSites (ℓ k)) (ht : t ∈ tileSites (ℓ (k + 1)))
    (hadj : (s0 - t - stepOf o rev (ℓ k) (ℓ (k + 1))).1.natAbs +
      (s0 - t - stepOf o rev (ℓ k) (ℓ (k + 1))).2.natAbs = 1)
    (hno : overlapWitness (ℓ k) (ℓ (k + 1)) (stepOf o rev (ℓ k) (ℓ (k + 1))) = none) :
    (familyF o rev ℓ n).odo (k + 1) (t + posF o rev ℓ (k + 1)) -
        (familyF o rev ℓ n).odo k (s0 + posF o rev ℓ k) = targetOf o := by
  obtain ⟨p, q, hw, hp, hq, hadjpq⟩ := adjWitness_spec (ℓ k) (ℓ (k + 1))
    (stepOf o rev (ℓ k) (ℓ (k + 1))) s0 t hs0 ht hadj
  have hno' : ∀ p ∈ tileSites (ℓ k), p - stepOf o rev (ℓ k) (ℓ (k + 1)) ∉ tileSites (ℓ (k + 1)) :=
    fun p hp => overlapWitness_none _ _ _ hno p hp
  obtain ⟨hU, hG⟩ := adjacent_consistent o (orientation_mem o) rev (bool_mem rev) (ℓ k) (letter_mem _)
    (ℓ (k + 1)) (letter_mem _) hno' p hp q hq s0 hs0 t ht hadjpq hadj
  have hβ : betaOf o rev ℓ k = targetOf o + (baseOdometer (ℓ k) s0 - baseOdometer (ℓ (k + 1)) t
      - dotS (deltaOf o (ℓ k) (ℓ (k + 1))) t) + dotS (aF o ℓ k) (s0 - t - stepOf o rev (ℓ k) (ℓ (k + 1)))
      - dotS (deltaOf o (ℓ k) (ℓ (k + 1))) (posF o rev ℓ k + stepOf o rev (ℓ k) (ℓ (k + 1))) := by
    unfold betaOf
    simp only [hw, hno]
    rw [hU, hG]
  have hpos : posF o rev ℓ (k + 1) = posF o rev ℓ k + stepOf o rev (ℓ k) (ℓ (k + 1)) := rfl
  have ha : aF o ℓ (k + 1) = aF o ℓ k + deltaOf o (ℓ k) (ℓ (k + 1)) := rfl
  have hbb : bF o rev ℓ (k + 1) = bF o rev ℓ k + betaOf o rev ℓ k := rfl
  simp only [ZOFamily.odo, familyF, hpos, ha, hbb, hβ, Prod.fst_add, Prod.snd_add, Prod.fst_sub,
    Prod.snd_sub, add_sub_cancel_right, dotS]
  ring

end FLatticePaper.Tiles
