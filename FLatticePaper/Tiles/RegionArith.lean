import Mathlib.Tactic.Linarith

/-! Task 55 (R2): the integer identities behind the region boundary. `F` is the north-column function of the walk
(`F j` for `0 ≤ j < H`), with `F (-1) = 0`, `F H = c` and `F (H-1) = c`. The region's row at height `k` is
`[c - F (H-k-1), F k)`. The walk's edges of the four types are read off `F`; the half-turn of an east edge is a west edge
at the reflected height, and the half-turn of a north edge is a south edge. Each identity below compares one edge type. -/

namespace FLatticePaper.Tiles.RegionArith

/-- The interval identity: the union of the east run `[A, B)` and the reflected run `[Lk, Lp)` is exactly the region's
difference `[Lk, B) \ [Lp, A)`, given the two overlaps `Lk < A` and `Lp < B`. -/
theorem interval_identity (q A B Lk Lp : ℤ) (hLkA : Lk < A) (hLpB : Lp < B) :
    ((A ≤ q ∧ q < B) ∨ (Lk ≤ q ∧ q < Lp)) ↔ ((Lk ≤ q ∧ q < B) ∧ ¬ (Lp ≤ q ∧ q < A)) := by
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · refine ⟨⟨by omega, h2⟩, ?_⟩
      rintro ⟨_, h4⟩
      omega
    · refine ⟨⟨h1, by omega⟩, ?_⟩
      rintro ⟨h3, _⟩
      omega
  · rintro ⟨⟨h1, h2⟩, hn⟩
    by_cases hq : A ≤ q
    · exact Or.inl ⟨hq, h2⟩
    · right
      refine ⟨h1, ?_⟩
      by_contra hc
      exact hn ⟨by omega, by omega⟩

/-- The arc data of a walk: the north columns and the endpoint, with the facts of the arc lemmas. -/
structure ArcData (F : ℤ → ℤ) (H c : ℤ) : Prop where
  hH : 1 ≤ H
  hFneg : F (-1) = 0
  hFH : F H = c
  hF1 : F (H - 1) = c
  hF0 : ∀ j, 0 ≤ j → j < H → 0 ≤ F j
  hkey : ∀ q r, 0 ≤ q → q < H → 0 ≤ r → r < H → H - 2 ≤ q + r → q + r ≤ H → c + 1 ≤ F q + F r

namespace ArcData

variable {F : ℤ → ℤ} {H c : ℤ}

/-- A row is nonempty: `c - F (H-k-1) < F k` for `0 ≤ k < H`. -/
theorem nonempty (D : ArcData F H c) (k : ℤ) (h0 : 0 ≤ k) (hk : k < H) :
    c - F (H - k - 1) < F k := by
  have := D.hkey k (H - k - 1) h0 hk (by omega) (by omega) (by omega) (by omega)
  omega

/-- The previous row is nonempty: `c - F (H-k) < F (k-1)` for `1 ≤ k ≤ H`. -/
theorem nonempty_prev (D : ArcData F H c) (k : ℤ) (h1 : 1 ≤ k) (hk : k ≤ H) :
    c - F (H - k) < F (k - 1) := by
  have := D.hkey (k - 1) (H - k) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

/-- The overlap `c - F (H-k-1) < F (k-1)` for `1 ≤ k < H`. -/
theorem overlap_lo (D : ArcData F H c) (k : ℤ) (h1 : 1 ≤ k) (hk : k < H) :
    c - F (H - k - 1) < F (k - 1) := by
  have := D.hkey (k - 1) (H - k - 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

/-- The overlap `c - F (H-k) < F k` for `1 ≤ k < H`. -/
theorem overlap_hi (D : ArcData F H c) (k : ℤ) (h1 : 1 ≤ k) (hk : k < H) :
    c - F (H - k) < F k := by
  have := D.hkey k (H - k) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

/-- The east edges: the walk's `(q,k) → (q+1,k)` is a run of the word (`F (k-1) ≤ q < F k`) or the half-turn of a west
run at the reflected height; together they are the region's bottom edge at height `k`. -/
theorem east_iff (D : ArcData F H c) (q k : ℤ) :
    ((0 ≤ k ∧ k ≤ H ∧ F (k - 1) ≤ q ∧ q < F k) ∨
        (0 ≤ H - k ∧ H - k ≤ H ∧ F (H - k) ≤ c - q - 1 ∧ c - q - 1 < F (H - k - 1))) ↔
      ((0 ≤ k ∧ k < H ∧ c - F (H - k - 1) ≤ q ∧ q < F k) ∧
        ¬ (0 ≤ k - 1 ∧ k - 1 < H ∧ c - F (H - k) ≤ q ∧ q < F (k - 1))) := by
  have hH := D.hH
  have hH0 := D.hF0 0 (le_refl 0) (by omega)
  have hFm : F (0 - 1) = 0 := by
    rw [zero_sub]
    exact D.hFneg
  rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
  · constructor <;> intro h <;> omega
  · subst hk0
    have i2 : F (H - 0) = c := by
      rw [sub_zero]
      exact D.hFH
    have i3 : F (H - 0 - 1) = c := by
      rw [sub_zero]
      exact D.hF1
    rw [hFm, i2, i3]
    constructor <;> intro h <;> omega
  · rcases lt_trichotomy k H with hkH | hkH | hkH
    · have e1 : (0 ≤ k ∧ k ≤ H ∧ F (k - 1) ≤ q ∧ q < F k) ↔ (F (k - 1) ≤ q ∧ q < F k) := by
        constructor <;> intro h <;> omega
      have e2 : (0 ≤ H - k ∧ H - k ≤ H ∧ F (H - k) ≤ c - q - 1 ∧ c - q - 1 < F (H - k - 1)) ↔
          (c - F (H - k - 1) ≤ q ∧ q < c - F (H - k)) := by
        constructor <;> intro h <;> omega
      have e3 : (0 ≤ k ∧ k < H ∧ c - F (H - k - 1) ≤ q ∧ q < F k) ↔
          (c - F (H - k - 1) ≤ q ∧ q < F k) := by
        constructor <;> intro h <;> omega
      have e4 : (0 ≤ k - 1 ∧ k - 1 < H ∧ c - F (H - k) ≤ q ∧ q < F (k - 1)) ↔
          (c - F (H - k) ≤ q ∧ q < F (k - 1)) := by
        constructor <;> intro h <;> omega
      rw [e1, e2, e3, e4]
      exact interval_identity q _ _ _ _ (D.overlap_lo k (by omega) hkH) (D.overlap_hi k (by omega) hkH)
    · rw [hkH, sub_self, hFm, D.hF1, D.hFH]
      constructor <;> intro h <;> omega
    · constructor <;> intro h <;> omega

/-- The west edges: the walk's `(q+1,k) → (q,k)` is a run of the word (`F k ≤ q < F (k-1)`) or the half-turn of an east
run at the reflected height; together they are the region's top edge of the row `k-1`. -/
theorem west_iff (D : ArcData F H c) (q k : ℤ) :
    ((0 ≤ k ∧ k ≤ H ∧ F k ≤ q ∧ q < F (k - 1)) ∨
        (0 ≤ H - k ∧ H - k ≤ H ∧ F (H - k - 1) ≤ c - q - 1 ∧ c - q - 1 < F (H - k))) ↔
      ((0 ≤ k - 1 ∧ k - 1 < H ∧ c - F (H - k) ≤ q ∧ q < F (k - 1)) ∧
        ¬ (0 ≤ k ∧ k < H ∧ c - F (H - k - 1) ≤ q ∧ q < F k)) := by
  have hH := D.hH
  have hH0 := D.hF0 0 (le_refl 0) (by omega)
  have hFm : F (0 - 1) = 0 := by
    rw [zero_sub]
    exact D.hFneg
  rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
  · constructor <;> intro h <;> omega
  · subst hk0
    have i2 : F (H - 0) = c := by
      rw [sub_zero]
      exact D.hFH
    have i3 : F (H - 0 - 1) = c := by
      rw [sub_zero]
      exact D.hF1
    rw [hFm, i2, i3]
    constructor <;> intro h <;> omega
  · rcases lt_trichotomy k H with hkH | hkH | hkH
    · have e1 : (0 ≤ k ∧ k ≤ H ∧ F k ≤ q ∧ q < F (k - 1)) ↔ (F k ≤ q ∧ q < F (k - 1)) := by
        constructor <;> intro h <;> omega
      have e2 : (0 ≤ H - k ∧ H - k ≤ H ∧ F (H - k - 1) ≤ c - q - 1 ∧ c - q - 1 < F (H - k)) ↔
          (c - F (H - k) ≤ q ∧ q < c - F (H - k - 1)) := by
        constructor <;> intro h <;> omega
      have e3 : (0 ≤ k - 1 ∧ k - 1 < H ∧ c - F (H - k) ≤ q ∧ q < F (k - 1)) ↔
          (c - F (H - k) ≤ q ∧ q < F (k - 1)) := by
        constructor <;> intro h <;> omega
      have e4 : (0 ≤ k ∧ k < H ∧ c - F (H - k - 1) ≤ q ∧ q < F k) ↔
          (c - F (H - k - 1) ≤ q ∧ q < F k) := by
        constructor <;> intro h <;> omega
      rw [e1, e2, e3, e4]
      exact interval_identity q _ _ _ _ (D.overlap_hi k (by omega) hkH) (D.overlap_lo k (by omega) hkH)
    · rw [hkH, sub_self, hFm, D.hF1, D.hFH]
      constructor <;> intro h <;> omega
    · constructor <;> intro h <;> omega

/-- The north edges: the walk's `(x,k) → (x,k+1)` is the north step at height `k` (`x = F k`); the region's right
edge is the same set, since the half-turn of a north step is a south step, which the word does not contain. -/
theorem north_iff (D : ArcData F H c) (x k : ℤ) :
    (0 ≤ k ∧ k < H ∧ x = F k) ↔
      ((0 ≤ k ∧ k < H ∧ c - F (H - k - 1) ≤ x - 1 ∧ x - 1 < F k) ∧
        ¬ (0 ≤ k ∧ k < H ∧ c - F (H - k - 1) ≤ x ∧ x < F k)) := by
  constructor
  · rintro ⟨h0, hk, hx⟩
    have hne := D.nonempty k h0 hk
    subst hx
    refine ⟨⟨h0, hk, by omega, by omega⟩, ?_⟩
    rintro ⟨_, _, _, h4⟩
    omega
  · rintro ⟨⟨h0, hk, h1, h2⟩, hn⟩
    have hne := D.nonempty k h0 hk
    refine ⟨h0, hk, ?_⟩
    by_contra hx
    exact hn ⟨h0, hk, by omega, by omega⟩

/-- The south edges: the walk's `(x,k+1) → (x,k)` is the half-turn of the north step at height `H-k-1`; the region's
left edge. -/
theorem south_iff (D : ArcData F H c) (x k : ℤ) :
    (0 ≤ H - k - 1 ∧ H - k - 1 < H ∧ c - x = F (H - k - 1)) ↔
      ((0 ≤ k ∧ k < H ∧ c - F (H - k - 1) ≤ x ∧ x < F k) ∧
        ¬ (0 ≤ k ∧ k < H ∧ c - F (H - k - 1) ≤ x - 1 ∧ x - 1 < F k)) := by
  constructor
  · rintro ⟨h0, hk, hx⟩
    have hk0 : 0 ≤ k := by omega
    have hkH : k < H := by omega
    have hne := D.nonempty k hk0 hkH
    have hxe : x = c - F (H - k - 1) := by omega
    refine ⟨⟨hk0, hkH, by omega, by omega⟩, ?_⟩
    rintro ⟨_, _, h3, _⟩
    omega
  · rintro ⟨⟨h0, hk, h1, h2⟩, hn⟩
    have hne := D.nonempty k h0 hk
    have hxe : c - x = F (H - k - 1) := by
      by_contra hx
      exact hn ⟨h0, hk, by omega, by omega⟩
    exact ⟨by omega, by omega, hxe⟩

end ArcData

end FLatticePaper.Tiles.RegionArith
