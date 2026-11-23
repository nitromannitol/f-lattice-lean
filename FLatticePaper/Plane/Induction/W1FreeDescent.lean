import FLatticePaper.Plane.Induction.W1FreeSquare
import FLatticePaper.Plane.Induction.DeckForced
import FLatticePaper.Plane.Induction.W1Phase
import FLatticePaper.Plane.Induction.W1HagreeNonfree

/-! # Task 83: the descent for free roots (identification (c) and the rank induction)

For a free white parent root `z` (not `Nonfree`, white for the earlier field `G`), the table row gives a unit square `Q ∋ z` with corners
`z, p0, p1, p2`, where `p0` is an input of `z` (the rejected input) and the return chain `p0 → p1 → p2 → z` is retained, each step going
to an input of the previous point (`W1FreeSquare`). The other input `o` of `z` lies outside `Q`.

* `other_input_outside`: the other input `o` is outside the square (the two inputs of a corner lie on opposite sides of it).
* `free_forced_of_descent`: by induction on the rank gap `B − rank z` (the rank strictly decreases along retained edges, so the chain points
  lie above `z`, and the rank is bounded above on `S` by `B`), every free white root `z` of `S` is forced, `ForcedEdge G z o`. The unit rule
  applies to `Q`: the corners `p0, p1, p2` are black, or white and forced to their chain step. A white chain point is nonfree (then
  `nonfree_root_forced_nonfree` gives its forced retained edge) or free (then the induction hypothesis gives a forced edge, and
  `forcedWhiteUnique` identifies its target with the retained chain step).

The table content (the rows and their retained chains) and the rank bound `B` on `S` are named inputs. The rank bound is the finiteness of
the rank values on the zero band (the note's descent), not proved here. -/

namespace FLatticePaper.W1FreeDescent

open FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank

/-- The other input of a square corner `z`, whose input `p0` lies in the square, is outside the square. -/
theorem other_input_outside {z p0 : Site} {a b : ℤ} (hz : z ∈ squareCorners a b) (hp0 : p0 ∈ squareCorners a b)
    (hin : p0 = incomingNeg z ∨ p0 = incomingPos z) :
    (if p0 = incomingNeg z then incomingPos z else incomingNeg z) ∉ squareCorners a b := by
  obtain ⟨z1, z2⟩ := z
  obtain ⟨q1, q2⟩ := p0
  simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hz hp0 ⊢
  unfold incomingNeg incomingPos EvenSite at hin ⊢
  split_ifs at hin ⊢ <;> simp only [Prod.mk.injEq] at * <;> omega

/-- **The descent for free roots** (task 83): every free white root `z` of `S` (on which the rank is bounded by `B`) has a forced input
`o`, `ForcedEdge G z o`, where `o` is the input of `z` outside its table square. -/
theorem free_forced_of_descent {η : ℤ} {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (P : FLatticePaper.W1Phase.OldPolicyRanked frame G seed η) (hP : frame.Packet G)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (S : Set Site) (B : ℤ) (hB : ∀ x ∈ S, P.rank x ≤ B)
    (hrow : ∀ z ∈ S, ¬ Nonfree frame z → laplacian G z = 0 → ∃ p0 p1 p2 : Site, ∃ a b : ℤ,
      z ∈ squareCorners a b ∧ p0 ∈ squareCorners a b ∧ p1 ∈ squareCorners a b ∧ p2 ∈ squareCorners a b ∧
      (∀ c' ∈ squareCorners a b, c' ≠ z → c' = p0 ∨ c' = p1 ∨ c' = p2) ∧
      p0 ≠ p1 ∧ p1 ≠ p2 ∧ p0 ≠ p2 ∧ (p0 = incomingNeg z ∨ p0 = incomingPos z) ∧
      (p0 ∈ S ∧ p1 ∈ S ∧ p2 ∈ S) ∧
      Edge p1 p0 ∧ Edge p2 p1 ∧ Edge z p2 ∧
      P.retained p0 p1 ∧ P.retained p1 p2 ∧ P.retained p2 z) :
    ∀ z ∈ S, ¬ Nonfree frame z → laplacian G z = 0 →
      ∃ o : Site, (o = incomingNeg z ∨ o = incomingPos z) ∧ ForcedEdge G (fun _ _ => False) z o := by
  have key : ∀ n : ℕ, ∀ z ∈ S, ¬ Nonfree frame z → laplacian G z = 0 → B - P.rank z < n →
      ∃ o : Site, (o = incomingNeg z ∨ o = incomingPos z) ∧ ForcedEdge G (fun _ _ => False) z o := by
    intro n
    induction n with
    | zero =>
      intro z hz _ _ hlt
      have := hB z hz
      push_cast at hlt
      omega
    | succ n ih =>
      intro z hzS hfree hw hlt
      obtain ⟨p0, p1, p2, a, b, hzc, hp0c, hp1c, hp2c, hcov, hne01, hne12, hne02, hp0in, hSs, hE1, hE2, hE3,
        hR0, hR1, hR2⟩ := hrow z hzS hfree hw
      push_cast at hlt
      -- ranks increase along the chain towards the bottom: rank z < rank p2 < rank p1 < rank p0
      have hz2 : P.rank z < P.rank p2 := P.rank_decr p2 z hR2
      have hz1 : P.rank z < P.rank p1 := lt_trans hz2 (P.rank_decr p1 p2 hR1)
      have hz0 : P.rank z < P.rank p0 := lt_trans hz1 (P.rank_decr p0 p1 hR0)
      -- a white chain point is forced to its retained chain step
      have C : ∀ x y : Site, x ∈ S → P.retained x y → laplacian G x = 0 → B - P.rank x < (n : ℤ) →
          ForcedEdge G (fun _ _ => False) x y := by
        intro x y hxS hr hxw hxlt
        by_cases hnf : Nonfree frame x
        · rcases nonfree_root_forced_nonfree P.toOldPolicyWitness.toOldPolicyData hP hW1 hnf hr with h | h
          · rw [hxw] at h
            norm_num at h
          · exact h
        · obtain ⟨o', _, hf⟩ := ih x hxS hnf hxw hxlt
          have heq := P.forcedWhiteUnique x y hr hxw o' hf
          rw [heq] at hf
          exact hf
      have hl0 : B - P.rank p0 < (n : ℤ) := by omega
      have hl1 : B - P.rank p1 < (n : ℤ) := by omega
      have hl2 : B - P.rank p2 < (n : ℤ) := by omega
      -- the other input of z is outside the square
      set o : Site := if p0 = incomingNeg z then incomingPos z else incomingNeg z with ho_def
      have ho : o = incomingNeg z ∨ o = incomingPos z := by
        rw [ho_def]
        split_ifs <;> simp
      have hout : o ∉ squareCorners a b := other_input_outside hzc hp0c hp0in
      refine ⟨o, ho, ?_⟩
      refine ForcedEdge.unit (fun c' => if c' = p0 then p1 else if c' = p1 then p2 else z) hzc hw ho hout ?_ ?_
      · intro c' hc' hne
        rcases hcov c' hc' hne with h | h | h
        · have hi : (if c' = p0 then p1 else if c' = p1 then p2 else z) = p1 := if_pos h
          rw [hi]
          rcases hP.binary c' with hb | hb
          · exact Or.inl hb
          · refine Or.inr ⟨hb, ?_, ?_⟩
            · exact hp1c
            · rw [h]
              exact hE1
        · have hne' : c' ≠ p0 := by
            rw [h]
            exact fun e => hne01 e.symm
          have hi : (if c' = p0 then p1 else if c' = p1 then p2 else z) = p2 := by
            rw [if_neg hne', if_pos h]
          rw [hi]
          rcases hP.binary c' with hb | hb
          · exact Or.inl hb
          · refine Or.inr ⟨hb, ?_, ?_⟩
            · exact hp2c
            · rw [h]
              exact hE2
        · have hne' : c' ≠ p0 := by
            rw [h]
            exact fun e => hne02 e.symm
          have hne'' : c' ≠ p1 := by
            rw [h]
            exact fun e => hne12 e.symm
          have hi : (if c' = p0 then p1 else if c' = p1 then p2 else z) = z := by
            rw [if_neg hne', if_neg hne'']
          rw [hi]
          rcases hP.binary c' with hb | hb
          · exact Or.inl hb
          · refine Or.inr ⟨hb, ?_, ?_⟩
            · exact hzc
            · rw [h]
              exact hE3
      · intro c' hc' hne hwc'
        rcases hcov c' hc' hne with h | h | h
        · have hi : (if c' = p0 then p1 else if c' = p1 then p2 else z) = p1 := if_pos h
          rw [hi]
          rw [h] at hwc' ⊢
          exact C p0 p1 hSs.1 hR0 hwc' hl0
        · have hne' : c' ≠ p0 := by
            rw [h]
            exact fun e => hne01 e.symm
          have hi : (if c' = p0 then p1 else if c' = p1 then p2 else z) = p2 := by
            rw [if_neg hne', if_pos h]
          rw [hi]
          rw [h] at hwc' ⊢
          exact C p1 p2 hSs.2.1 hR1 hwc' hl1
        · have hne' : c' ≠ p0 := by
            rw [h]
            exact fun e => hne02 e.symm
          have hne'' : c' ≠ p1 := by
            rw [h]
            exact fun e => hne12 e.symm
          have hi : (if c' = p0 then p1 else if c' = p1 then p2 else z) = z := by
            rw [if_neg hne', if_neg hne'']
          rw [hi]
          rw [h] at hwc' ⊢
          exact C p2 z hSs.2.2 hR2 hwc' hl2
  intro z hz hfree hw
  have h0 : 0 ≤ B - P.rank z := by
    have := hB z hz
    omega
  have hcast : ((B - P.rank z).toNat : ℤ) = B - P.rank z := Int.toNat_of_nonneg h0
  exact key ((B - P.rank z).toNat + 1) z hz hfree hw (by push_cast; omega)

/-- **`hagree` at a free sheet root** (task 83, identification (c)): for a sheet point `c` whose parent root `z = Z (c − lv)` is free and
white and lies in `S`, the C policy retains the A pointer. The descent gives the forced input `o` of `z`; the A policy retains the pointer's
parent image `w`, so `forcedWhiteUnique` gives `o = w`, and the reflection `sheetPolicyC_of_sheetPolicyA` (parent edge forced) applies. -/
theorem hagree_at_free_root {η : ℤ} {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (P : FLatticePaper.W1Phase.OldPolicyRanked frame G seed η) (hP : frame.Packet G)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (S : Set Site) (B : ℤ) (hB : ∀ x ∈ S, P.rank x ≤ B)
    (hrow : ∀ z ∈ S, ¬ Nonfree frame z → laplacian G z = 0 → ∃ p0 p1 p2 : Site, ∃ a b : ℤ,
      z ∈ squareCorners a b ∧ p0 ∈ squareCorners a b ∧ p1 ∈ squareCorners a b ∧ p2 ∈ squareCorners a b ∧
      (∀ c' ∈ squareCorners a b, c' ≠ z → c' = p0 ∨ c' = p1 ∨ c' = p2) ∧
      p0 ≠ p1 ∧ p1 ≠ p2 ∧ p0 ≠ p2 ∧ (p0 = incomingNeg z ∨ p0 = incomingPos z) ∧
      (p0 ∈ S ∧ p1 ∈ S ∧ p2 ∈ S) ∧
      Edge p1 p0 ∧ Edge p2 p1 ∧ Edge z p2 ∧
      P.retained p0 p1 ∧ P.retained p1 p2 ∧ P.retained p2 z)
    (lv c : Site) (hlv : EvenSite lv)
    (hzS : zTurn (c - lv) ∈ S) (hfree : ¬ Nonfree frame (zTurn (c - lv)))
    (hw : laplacian G (zTurn (c - lv)) = 0) :
    sheetPolicyC P.toOldPolicyWitness.toOldPolicyData lv (reflectionI + lv + lv) c
      (FLatticePaper.W1Pointers.pointerOf (sheetPolicyA P.toOldPolicyWitness.toOldPolicyData lv) c) := by
  have hA := FLatticePaper.W1HagreeNonfree.sheetPolicyA_pointer_retained P.toOldPolicyWitness.toOldPolicyData
    hP.binary lv hlv c
  obtain ⟨o, _, hF⟩ := free_forced_of_descent P hP hW1 S B hB hrow _ hzS hfree hw
  have hA' : P.retained (zTurn (c - lv))
      (zTurn (FLatticePaper.W1Pointers.pointerOf (sheetPolicyA P.toOldPolicyWitness.toOldPolicyData lv) c - lv)) := hA
  have heq := P.toOldPolicyWitness.toOldPolicyData.forcedWhiteUnique (zTurn (c - lv))
    (zTurn (FLatticePaper.W1Pointers.pointerOf (sheetPolicyA P.toOldPolicyWitness.toOldPolicyData lv) c - lv))
    hA' hw o hF
  have hroot : laplacian G (zTurn (c - lv)) = -1 ∨ SquareClauses.ForcedEdge G (fun _ _ => False) (zTurn (c - lv))
      (zTurn (FLatticePaper.W1Pointers.pointerOf (sheetPolicyA P.toOldPolicyWitness.toOldPolicyData lv) c - lv)) :=
    Or.inr (heq ▸ hF)
  exact FLatticePaper.W1Hagree.sheetPolicyC_of_sheetPolicyA P.toOldPolicyWitness.toOldPolicyData lv c _ hroot hA

end FLatticePaper.W1FreeDescent
