import FLatticePaper.Tiles.ZeroOneSlopes

/-! Geometry of the zero-one families (task 16): steps move the tiles monotonically, and tiles at distance at least
two are disjoint. -/

namespace FLatticePaper.Tiles
open Finset

theorem letter_mem (l : Letter) : l ∈ [Letter.p, Letter.q] := by
  cases l <;> simp

theorem orientation_mem (o : Orientation) : o ∈ [Orientation.horizontal, Orientation.vertical] := by
  cases o <;> simp

theorem bool_mem (r : Bool) : r ∈ [false, true] := by
  cases r <;> simp

theorem stepOf_h_ge (rev : Bool) (a b : Letter) : 1 ≤ (stepOf .horizontal rev a b).1 := by
  cases rev <;> cases a <;> cases b <;> decide

theorem stepOf_v_ge (rev : Bool) (a b : Letter) : 1 ≤ (stepOf .vertical rev a b).2 := by
  cases rev <;> cases a <;> cases b <;> decide

theorem tile_range : ∀ a ∈ [Letter.p, Letter.q], ∀ s ∈ tileSites a,
    0 ≤ s.1 ∧ s.1 ≤ 1 ∧ 0 ≤ s.2 ∧ s.2 ≤ 2 := by
  decide +kernel

theorem posF_h_ge (rev : Bool) (ℓ : ℕ → Letter) (k m : ℕ) (h : k ≤ m) :
    (posF .horizontal rev ℓ k).1 + ((m - k : ℕ) : ℤ) ≤ (posF .horizontal rev ℓ m).1 := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have h1 := stepOf_h_ge rev (ℓ m) (ℓ (m + 1))
    have e : ((m + 1 - k : ℕ) : ℤ) = ((m - k : ℕ) : ℤ) + 1 := by omega
    simp only [posF, Prod.fst_add]
    rw [e]
    omega

theorem posF_v_ge (rev : Bool) (ℓ : ℕ → Letter) (k m : ℕ) (h : k ≤ m) :
    (posF .vertical rev ℓ k).2 + ((m - k : ℕ) : ℤ) ≤ (posF .vertical rev ℓ m).2 := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have h1 := stepOf_v_ge rev (ℓ m) (ℓ (m + 1))
    have e : ((m + 1 - k : ℕ) : ℤ) = ((m - k : ℕ) : ℤ) + 1 := by omega
    simp only [posF, Prod.snd_add]
    rw [e]
    omega

/-- Sites of the `k`-th tile of a zero-one family lie in its box. -/
theorem dom_range (o : Orientation) (rev : Bool) (ℓ : ℕ → Letter) (n k : ℕ) (x : Site)
    (hx : x ∈ (familyF o rev ℓ n).dom k) :
    (posF o rev ℓ k).1 ≤ x.1 ∧ x.1 ≤ (posF o rev ℓ k).1 + 1 ∧
      (posF o rev ℓ k).2 ≤ x.2 ∧ x.2 ≤ (posF o rev ℓ k).2 + 2 := by
  unfold ZOFamily.dom familyF at hx
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
  have := tile_range (ℓ k) (letter_mem _) s hs
  simp only [Prod.fst_add, Prod.snd_add]
  omega

/-- Tiles at distance at least three are disjoint, in either orientation. -/
theorem dom_disjoint_far (o : Orientation) (rev : Bool) (ℓ : ℕ → Letter) (n k m : ℕ)
    (hkm : k + 3 ≤ m) (x : Site) (hx : x ∈ (familyF o rev ℓ n).dom k)
    (y : Site) (hy : y ∈ (familyF o rev ℓ n).dom m) : x ≠ y := by
  have hxr := dom_range o rev ℓ n k x hx
  have hyr := dom_range o rev ℓ n m y hy
  intro hxy
  cases o with
  | horizontal =>
    have := posF_h_ge rev ℓ k m (by omega)
    have h3 : ((m - k : ℕ) : ℤ) ≥ 3 := by
      have : (3 : ℕ) ≤ m - k := by omega
      exact_mod_cast this
    subst hxy
    omega
  | vertical =>
    have := posF_v_ge rev ℓ k m (by omega)
    have h3 : ((m - k : ℕ) : ℤ) ≥ 3 := by
      have : (3 : ℕ) ≤ m - k := by omega
      exact_mod_cast this
    subst hxy
    omega

end FLatticePaper.Tiles
