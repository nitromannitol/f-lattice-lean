import FLatticePaper.Tiles.CellConnectivity
import FLatticePaper.Tiles.CheckerFree

/-! Task 53, step 1: the row-chain property of a cell set gives edge-connectivity and the absence of checkerboard
vertices at once.

A cell set `C` is a row chain when (1) each row `{x | (x, y) ∈ C}` is an interval, (2) two consecutive rows that are
both nonempty share a column, and (3) the nonempty rows form a contiguous range of heights. Then `C` is edge-connected
(move along rows, then up or down through a shared column), and no vertex is a checkerboard vertex (the two rows of a
checkerboard cannot overlap). -/

namespace FLatticePaper.Tiles

/-- Each row of `C` is an interval. -/
def CellRowConvex (C : CellTile) : Prop :=
  ∀ (y x₁ x₂ x₃ : ℤ), (x₁, y) ∈ C → (x₃, y) ∈ C → x₁ ≤ x₂ → x₂ ≤ x₃ → (x₂, y) ∈ C

/-- Consecutive nonempty rows share a column. -/
def CellRowOverlap (C : CellTile) : Prop :=
  ∀ y : ℤ, (∃ x, (x, y) ∈ C) → (∃ x, (x, y + 1) ∈ C) → ∃ x, (x, y) ∈ C ∧ (x, y + 1) ∈ C

/-- The nonempty rows are contiguous. -/
def CellRowContig (C : CellTile) : Prop :=
  ∀ y₁ y₂ y : ℤ, (∃ x, (x, y₁) ∈ C) → (∃ x, (x, y₂) ∈ C) → y₁ ≤ y → y ≤ y₂ → ∃ x, (x, y) ∈ C

/-- `C` is a row chain. -/
def CellRowChain (C : CellTile) : Prop := CellRowConvex C ∧ CellRowOverlap C ∧ CellRowContig C

theorem cellRow_gOne_eq : gOne = ((1 : ℤ), (0 : ℤ)) := rfl

theorem cellRow_gI_eq : gI = ((0 : ℤ), (1 : ℤ)) := rfl

/-- Horizontal chains inside a row. -/
theorem cellRow_horiz_chain {C : CellTile} (hC : CellRowConvex C) (y : ℤ) : ∀ (n : ℕ) (x₁ : ℤ),
    (x₁, y) ∈ C → (x₁ + n, y) ∈ C → Relation.ReflTransGen (CellRel C) (x₁, y) (x₁ + n, y) := by
  intro n
  induction n with
  | zero =>
    intro x₁ _ _
    simp only [Nat.cast_zero, add_zero]
    exact Relation.ReflTransGen.refl
  | succ n ih =>
    intro x₁ h₁ h₃
    have e : x₁ + ((n + 1 : ℕ) : ℤ) = (x₁ + n) + 1 := by push_cast; ring
    rw [e] at h₃ ⊢
    have hmid : (x₁ + n, y) ∈ C := hC y x₁ (x₁ + n) (x₁ + n + 1) h₁ h₃ (by omega) (by omega)
    refine (ih x₁ h₁ hmid).tail ⟨hmid, h₃, Or.inl ?_⟩
    rw [cellRow_gOne_eq]
    simp

/-- Horizontal chains between two cells of a row, in either order. -/
theorem cellRow_horiz_chain' {C : CellTile} (hC : CellRowConvex C) {y a c : ℤ} (ha : (a, y) ∈ C) (hc : (c, y) ∈ C) :
    Relation.ReflTransGen (CellRel C) (a, y) (c, y) := by
  rcases le_total a c with h | h
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, c = a + n := ⟨(c - a).toNat, by omega⟩
    subst hn
    exact cellRow_horiz_chain hC y n a ha hc
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, a = c + n := ⟨(a - c).toNat, by omega⟩
    subst hn
    exact cellRel_rtg_symm (cellRel_symm C) (cellRow_horiz_chain hC y n c hc ha)

/-- Vertical chains: from a cell in row `y` to a cell in row `y + n`. -/
theorem cellRow_vert_chain {C : CellTile} (hC : CellRowConvex C) (hO : CellRowOverlap C) (hK : CellRowContig C) :
    ∀ (n : ℕ) (a c y : ℤ), (a, y) ∈ C → (c, y + n) ∈ C →
      Relation.ReflTransGen (CellRel C) (a, y) (c, y + n) := by
  intro n
  induction n with
  | zero =>
    intro a c y ha hc
    simp only [Nat.cast_zero, add_zero] at hc ⊢
    exact cellRow_horiz_chain' hC ha hc
  | succ n ih =>
    intro a c y ha hc
    have e : y + ((n + 1 : ℕ) : ℤ) = (y + n) + 1 := by push_cast; ring
    rw [e] at hc ⊢
    obtain ⟨d, hd⟩ := hK y (y + n + 1) (y + n) ⟨a, ha⟩ ⟨c, hc⟩ (by omega) (by omega)
    obtain ⟨e', he1, he2⟩ := hO (y + n) ⟨d, hd⟩ ⟨c, hc⟩
    have hd' := ih a d y ha hd
    have h1 := cellRow_horiz_chain' hC hd he1
    have h2 : CellRel C (e', y + n) (e', y + n + 1) :=
      ⟨he1, he2, Or.inr (Or.inr (Or.inl (by rw [cellRow_gI_eq]; simp)))⟩
    exact ((hd'.trans h1).tail h2).trans (cellRow_horiz_chain' hC he2 hc)

/-- A row chain is edge-connected. -/
theorem cellRowChain_edgeConnected {C : CellTile} (hC : CellRowChain C) : EdgeConnectedIn C := by
  obtain ⟨hR, hO, hK⟩ := hC
  rintro ⟨a, y₁⟩ ha ⟨c, y₂⟩ hc
  rcases le_total y₁ y₂ with h | h
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, y₂ = y₁ + n := ⟨(y₂ - y₁).toNat, by omega⟩
    subst hn
    exact cellRow_vert_chain hR hO hK n a c y₁ ha hc
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, y₁ = y₂ + n := ⟨(y₁ - y₂).toNat, by omega⟩
    subst hn
    exact cellRel_rtg_symm (cellRel_symm C) (cellRow_vert_chain hR hO hK n c a y₂ hc ha)

/-- A row chain has no checkerboard vertex. -/
theorem cellRowChain_no_checker {C : CellTile} (hC : CellRowChain C) (v : GInt) : ¬ CheckerboardAt C v := by
  obtain ⟨hR, hO, -⟩ := hC
  obtain ⟨x, y⟩ := v
  have hsub1 : (x, y) - gOne - gI = (x - 1, y - 1) := by simp [gOne, gI]
  have hsub2 : (x, y) - gOne = (x - 1, y) := by simp [gOne]
  have hsub3 : (x, y) - gI = (x, y - 1) := by simp [gI]
  unfold CheckerboardAt
  rw [hsub1, hsub2, hsub3]
  rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
  · -- (x,y), (x-1,y-1) in C; (x-1,y), (x,y-1) not in C
    obtain ⟨z, hz1, hz2⟩ := hO (y - 1) ⟨x - 1, h2⟩ ⟨x, by rw [sub_add_cancel]; exact h1⟩
    rw [sub_add_cancel] at hz2
    by_cases hxz : x ≤ z
    · exact h4 (hR (y - 1) (x - 1) x z h2 hz1 (by omega) hxz)
    · exact h3 (hR y z (x - 1) x hz2 h1 (by omega) (by omega))
  · -- (x-1,y), (x,y-1) in C; (x,y), (x-1,y-1) not in C
    obtain ⟨z, hz1, hz2⟩ := hO (y - 1) ⟨x, h2⟩ ⟨x - 1, by rw [sub_add_cancel]; exact h1⟩
    rw [sub_add_cancel] at hz2
    by_cases hxz : x ≤ z
    · exact h3 (hR y (x - 1) x z h1 hz2 (by omega) hxz)
    · exact h4 (hR (y - 1) z (x - 1) x hz1 h2 (by omega) (by omega))

/-- A cell set whose cells are described by a predicate `P` (in the coordinates `(column, row)`) is a row chain when
the rows of `P` lie in a range `[Y₀, Y₁]`, the rows are convex, and each row `b` of the range has a witness column
`w b` in row `b` (and in row `b + 1` when `b < Y₁`). -/
theorem cellRowChain_of_witness (C : CellTile) (P : ℤ → ℤ → Prop) (hP : ∀ a b, (a, b) ∈ C ↔ P a b)
    (Y₀ Y₁ : ℤ) (w : ℤ → ℤ)
    (hrange : ∀ a b, P a b → Y₀ ≤ b ∧ b ≤ Y₁)
    (hconv : ∀ b a₁ a₂ a₃, P a₁ b → P a₃ b → a₁ ≤ a₂ → a₂ ≤ a₃ → P a₂ b)
    (hwit : ∀ b, Y₀ ≤ b → b ≤ Y₁ → P (w b) b ∧ (b < Y₁ → P (w b) (b + 1))) :
    CellRowChain C := by
  refine ⟨?_, ?_, ?_⟩
  · intro b x₁ x₂ x₃ h₁ h₃ hle₁ hle₂
    rw [hP] at h₁ h₃ ⊢
    exact hconv b x₁ x₂ x₃ h₁ h₃ hle₁ hle₂
  · rintro b ⟨x, hx⟩ ⟨x', hx'⟩
    rw [hP] at hx hx'
    obtain ⟨h0, h1⟩ := hrange x b hx
    obtain ⟨h0', h1'⟩ := hrange x' (b + 1) hx'
    obtain ⟨hw1, hw2⟩ := hwit b h0 (by omega)
    exact ⟨w b, (hP _ _).2 hw1, (hP _ _).2 (hw2 (by omega))⟩
  · rintro b₁ b₂ b ⟨x₁, h₁⟩ ⟨x₂, h₂⟩ hb₁ hb₂
    rw [hP] at h₁ h₂
    obtain ⟨g0, g1⟩ := hrange x₁ b₁ h₁
    obtain ⟨g0', g1'⟩ := hrange x₂ b₂ h₂
    exact ⟨w b, (hP _ _).2 (hwit b (by omega) (by omega)).1⟩

end FLatticePaper.Tiles
