import FLatticePaper.Tiles.StackBridge

/-! The bridge: the summary of the union of `q + 2` letters is the transition of the summary of `q + 1` letters. -/

namespace FLatticePaper.Tiles

theorem rel_bounds (o : Orientation) (a : Letter) (ep : Bool) :
    ∀ r ∈ relCells o a ep, -2 ≤ r.1 ∧ r.1 ≤ 3 ∧ -3 ≤ r.2 ∧ r.2 ≤ 3 := by
  cases o <;> cases a <;> cases ep <;> decide

/-- The window bounds of the old union, orientation-free form. -/
theorem lamO_bounds' (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) (hq : 1 ≤ q) :
    ∀ x ∈ lamO o ℓ (q + 1),
      x.2 ≤ (posO o ℓ q).2 + 3 ∧
      (o = Orientation.horizontal → x.1 ≤ (posO o ℓ q).1 + 3) ∧
      (o = Orientation.vertical → (posO o ℓ q).1 ≤ x.1) := by
  intro x hx
  cases o with
  | horizontal =>
    obtain ⟨h1, h2⟩ := lamO_bounds_h ℓ q hq x hx
    exact ⟨h1, (fun _ => h2), (fun h => by cases h)⟩
  | vertical =>
    obtain ⟨h1, h2⟩ := lamO_bounds_v ℓ q hq x hx
    exact ⟨h1, (fun h => by cases h), (fun _ => h2)⟩

/-- The new anchor is the old one plus the plus step of the new letter. -/
theorem posO_new' (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) :
    posO o ℓ (q + 1) = posO o ℓ q + plusStepO o (ℓ (q + 1)) := rfl

theorem getD_map_range {β : Type} (f : ℕ → β) (n k : ℕ) (d : β) (hk : k < n) :
    ((List.range n).map f).getD k d = f k := by
  simp [List.getD_eq_getElem?_getD, hk]

/-- The row-nonempty flags of the actual summary. -/
theorem stateOf_ne_getD (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) (k : ℕ) (hk : k < 8) :
    (stateOf o ℓ (q + 1)).ne.getD k false =
      decide (((lamO o ℓ (q + 1)).filter (fun p => p.2 = (posO o ℓ q).2 + ((k : ℤ) - 4))).Nonempty) := by
  unfold stateOf
  simp only [Nat.add_sub_cancel]
  exact getD_map_range _ 8 k false hk

/-- The window bits of the actual summary. -/
theorem stateOf_bits_getD (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) (k l : ℕ) (hk : k < 8) (hl : l < 6) :
    ((stateOf o ℓ (q + 1)).bits.getD k []).getD l false =
      decide (((posO o ℓ q).1 + ((l : ℤ) - 2), (posO o ℓ q).2 + ((k : ℤ) - 4)) ∈ lamO o ℓ (q + 1)) := by
  unfold stateOf
  simp only [Nat.add_sub_cancel]
  rw [getD_map_range _ 8 k [] hk]
  exact getD_map_range _ 6 l false hl

/-- The pair flags of the actual summary. -/
theorem stateOf_sh_getD (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) (k : ℕ) (hk : k < 7) :
    (stateOf o ℓ (q + 1)).sh.getD k false =
      decide ((((lamO o ℓ (q + 1)).image Prod.fst).filter (fun x =>
        (x, (posO o ℓ q).2 + ((k : ℤ) - 4)) ∈ lamO o ℓ (q + 1) ∧
        (x, (posO o ℓ q).2 + ((k : ℤ) - 4) + 1) ∈ lamO o ℓ (q + 1))).Nonempty) := by
  unfold stateOf
  simp only [Nat.add_sub_cancel]
  exact getD_map_range _ 7 k false hk

end FLatticePaper.Tiles
