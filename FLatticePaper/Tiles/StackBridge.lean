import FLatticePaper.Tiles.StackWindow

/-! Membership and geometric bounds for the local union, in coordinates relative to the anchor. The bridge from the
actual union to the Boolean summary `transWS` is built from these facts. -/

namespace FLatticePaper.Tiles

theorem piece_mem_iff (l : Letter) (e : Bool) (p x : Site) :
    x ∈ pieceAt l e p ↔ x - p ∈ tileSitesOf l e := by
  unfold pieceAt
  simp only [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨t, ht, rfl⟩
    simpa using ht
  · intro h
    exact ⟨x - p, h, by simp⟩

theorem relCells_mem_iff (o : Orientation) (a : Letter) (ep : Bool) (r : Site) :
    r ∈ relCells o a ep ↔ r ∈ tileSitesOf a ep ∨ ∃ t ∈ tileSitesOf a ep, t + shadowO o a = r := by
  unfold relCells
  simp only [List.mem_append, List.mem_map]

/-- The new tile's cells, relative to the new anchor. -/
theorem mem_newPieces_iff (o : Orientation) (a : Letter) (ep : Bool) (A x : Site) :
    (x ∈ pieceAt a ep A ∨ x ∈ pieceAt a ep (A + shadowO o a)) ↔ x - A ∈ relCells o a ep := by
  rw [piece_mem_iff, piece_mem_iff, relCells_mem_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right
      refine ⟨x - (A + shadowO o a), h, ?_⟩
      abel
  · rintro (h | ⟨t, ht, h⟩)
    · exact Or.inl h
    · right
      have e : x - (A + shadowO o a) = t := by
        rw [show x - (A + shadowO o a) = (x - A) - shadowO o a from by abel, ← h]
        abel
      rw [e]
      exact ht

/-- Adding the new tile: membership in the union of `q + 2` letters, relative to the old anchor. -/
theorem mem_lamO_succ (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) (hq : 1 ≤ q) (x : Site) :
    x ∈ lamO o ℓ (q + 2) ↔
      x ∈ lamO o ℓ (q + 1) ∨ x - posO o ℓ (q + 1) ∈ relCells o (ℓ (q + 1)) (flagO o ℓ (q + 1)) := by
  rw [lamO_succ o ℓ (show 2 ≤ q + 1 by omega), Finset.mem_union, Finset.mem_union, or_assoc,
    mem_newPieces_iff]

/-- The new plus position is the old one plus the plus step of the new letter. -/
theorem posO_new (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) :
    posO o ℓ (q + 1) = posO o ℓ q + plusStepO o (ℓ (q + 1)) := rfl

theorem piece_upper {l : Letter} {e : Bool} {p x : Site} (hx : x ∈ pieceAt l e p) :
    x.1 ≤ p.1 + 1 ∧ x.2 ≤ p.2 + 2 := by
  have h := tile_bound l e (x - p) ((piece_mem_iff l e p x).1 hx)
  simp only [Prod.fst_sub, Prod.snd_sub] at h
  omega

theorem stack_piece_lower {l : Letter} {p x : Site} (hx : x ∈ pieceAt l false p) : p.1 ≤ x.1 ∧ p.2 ≤ x.2 := by
  have h := tile_bound_plain l (x - p) ((piece_mem_iff l false p x).1 hx)
  simp only [Prod.fst_sub, Prod.snd_sub] at h
  omega

theorem shadowO_h (l : Letter) : (shadowO .horizontal l).1 ≤ 2 ∧ (shadowO .horizontal l).2 = -2 := by
  cases l <;> decide

theorem shadowO_v (l : Letter) : 1 ≤ (shadowO .vertical l).1 ∧ (shadowO .vertical l).2 = 1 := by
  cases l <;> decide

theorem flagO_vertical (ℓ : ℕ → Letter) (j : ℕ) : flagO .vertical ℓ j = false := by
  cases j <;> simp [flagO]

/-- The cells of the first `k + 1` letters come from the plus tiles, the shadows, or the two minus tiles at the start. -/
theorem mem_lamO_cases (o : Orientation) (ℓ : ℕ → Letter) (k : ℕ) (hk : 1 ≤ k) (x : Site)
    (hx : x ∈ lamO o ℓ (k + 1)) :
    (∃ j, j ≤ k ∧ x ∈ pieceAt (ℓ j) (flagO o ℓ j) (posO o ℓ j)) ∨
    (∃ j, 2 ≤ j ∧ j ≤ k ∧ x ∈ pieceAt (ℓ j) (flagO o ℓ j) (posO o ℓ j + shadowO o (ℓ j))) ∨
    x ∈ m0Piece o ∨
    x ∈ pieceAt (ℓ 1) false (posO o ℓ 1 + shadowO o (ℓ 1)) := by
  unfold lamO at hx
  have h1 : 1 ≤ k + 1 := by omega
  have h2 : 2 ≤ k + 1 := by omega
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_range, Finset.mem_Ico, if_pos h1, if_pos h2]
    at hx
  rcases hx with ((⟨j, hj, hxj⟩ | ⟨j, ⟨hj2, hjk⟩, hxj⟩) | hm0) | hm1
  · exact Or.inl ⟨j, by omega, hxj⟩
  · exact Or.inr (Or.inl ⟨j, hj2, by omega, hxj⟩)
  · exact Or.inr (Or.inr (Or.inl hm0))
  · exact Or.inr (Or.inr (Or.inr hm1))

theorem lamO_bounds_h (ℓ : ℕ → Letter) (k : ℕ) (hk : 1 ≤ k) :
    ∀ x ∈ lamO .horizontal ℓ (k + 1),
      x.2 ≤ (posO .horizontal ℓ k).2 + 3 ∧ x.1 ≤ (posO .horizontal ℓ k).1 + 3 := by
  intro x hx
  rcases mem_lamO_cases .horizontal ℓ k hk x hx with ⟨j, hj, h⟩ | ⟨j, hj2, hjk, h⟩ | h | h
  · obtain ⟨u1, u2⟩ := piece_upper h
    have m1 := posO_fst_mono_h ℓ hj
    have m2 := posO_snd_mono .horizontal ℓ hj
    constructor <;> omega
  · obtain ⟨u1, u2⟩ := piece_upper h
    simp only [Prod.fst_add, Prod.snd_add] at u1 u2
    obtain ⟨s1, s2⟩ := shadowO_h (ℓ j)
    have m1 := posO_fst_mono_h ℓ hjk
    have m2 := posO_snd_mono .horizontal ℓ hjk
    constructor <;> omega
  · have hm : m0Piece .horizontal = pieceAt .p false (1, -2) := rfl
    rw [hm] at h
    obtain ⟨u1, u2⟩ := piece_upper h
    have n1 := posO_fst_nonneg_h ℓ k
    have n2 := posO_snd_nonneg .horizontal ℓ k
    constructor <;> simp only at u1 u2 <;> omega
  · obtain ⟨u1, u2⟩ := piece_upper h
    simp only [Prod.fst_add, Prod.snd_add] at u1 u2
    obtain ⟨s1, s2⟩ := shadowO_h (ℓ 1)
    have m1 := posO_fst_mono_h ℓ hk
    have m2 := posO_snd_mono .horizontal ℓ hk
    constructor <;> omega

theorem lamO_bounds_v (ℓ : ℕ → Letter) (k : ℕ) (hk : 1 ≤ k) :
    ∀ x ∈ lamO .vertical ℓ (k + 1),
      x.2 ≤ (posO .vertical ℓ k).2 + 3 ∧ (posO .vertical ℓ k).1 ≤ x.1 := by
  intro x hx
  rcases mem_lamO_cases .vertical ℓ k hk x hx with ⟨j, hj, h⟩ | ⟨j, hj2, hjk, h⟩ | h | h
  · rw [flagO_vertical] at h
    obtain ⟨l1, l2⟩ := stack_piece_lower h
    obtain ⟨u1, u2⟩ := piece_upper h
    have m1 := posO_fst_anti_v ℓ hj
    have m2 := posO_snd_mono .vertical ℓ hj
    constructor <;> omega
  · rw [flagO_vertical] at h
    obtain ⟨l1, l2⟩ := stack_piece_lower h
    obtain ⟨u1, u2⟩ := piece_upper h
    simp only [Prod.fst_add, Prod.snd_add] at l1 l2 u1 u2
    obtain ⟨s1, s2⟩ := shadowO_v (ℓ j)
    have m1 := posO_fst_anti_v ℓ hjk
    have m2 := posO_snd_mono .vertical ℓ hjk
    constructor <;> omega
  · have hm : m0Piece .vertical = pieceAt .q false (1, 1) := rfl
    rw [hm] at h
    obtain ⟨l1, l2⟩ := stack_piece_lower h
    obtain ⟨u1, u2⟩ := piece_upper h
    have n1 := posO_fst_nonpos_v ℓ k
    have n2 := posO_snd_nonneg .vertical ℓ k
    constructor <;> simp only at l1 l2 u1 u2 <;> omega
  · obtain ⟨l1, l2⟩ := stack_piece_lower h
    obtain ⟨u1, u2⟩ := piece_upper h
    simp only [Prod.fst_add, Prod.snd_add] at l1 l2 u1 u2
    obtain ⟨s1, s2⟩ := shadowO_v (ℓ 1)
    have m1 := posO_fst_anti_v ℓ hk
    have m2 := posO_snd_mono .vertical ℓ hk
    constructor <;> omega

end FLatticePaper.Tiles
