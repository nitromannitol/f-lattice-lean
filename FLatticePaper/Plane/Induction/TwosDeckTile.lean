import FLatticePaper.Plane.Induction.TwosTileRange
import FLatticePaper.Plane.Induction.TwosTileUnique

/-! The deck value (sign +1) at the tile points.

`deckAt a 1 p` is the first true offer among the nine aliases of `p` (free offers, then bulk offers). At a free point the value is
`freeH` (H) or `freeV` (V) of `p` itself. At a non-free tile point, the aliases that can be free are `p−V` (excluded by the tile)
and `p−U` (excluded unless `p = (a, 2a−1)`); the other aliases are never free for a native point, so the value is `bulkR p`. -/

namespace FLatticePaper.TwosEPolicy

open FLatticePaper
open scoped Classical

/-- A point of the box with the strips removed is native. -/
theorem nat_of_box {a x y : ℤ} (h1 : -1 ≤ x) (h2 : x ≤ a + 1) (h3 : 1 ≤ y + 1) (h4 : y + 1 ≤ 3 * a - 1)
    (h5 : -1 ≤ y + 1 - x) (h6 : y + 1 - x ≤ 2 * a + 1)
    (hs : ¬((x = -1 ∧ y + 1 ≤ a + 1) ∨ (x = a + 1 ∧ 2 * a - 1 ≤ y + 1))) : NativeT a x y :=
  Or.inl ⟨⟨h1, h2, h3, h4, h5, h6⟩, hs⟩

/-- Transport a non-freeness along equal sites. -/
theorem alias_of_eq {a A B A' B' : ℤ} (h : ¬ FreeSite a A' B') (hA : A = A') (hB : B = B') :
    ¬ FreeSite a A B := by
  subst hA
  subst hB
  exact h

theorem deck_freeH {a X Y : ℤ} (hF : FreeHSite a X Y) : deckAt a 1 X Y = freeH a 1 X Y := by
  unfold deckAt
  dsimp only
  simp [aliasAddrs, pickFirst, hF]

theorem deck_freeV {a X Y : ℤ} (hnH : ¬ FreeHSite a X Y) (hV : FreeVSite a X Y) :
    deckAt a 1 X Y = freeV a 1 X Y := by
  unfold deckAt
  dsimp only
  simp [aliasAddrs, pickFirst, hnH, hV]

theorem deck_of_nofree {a X Y : ℤ} (hN : NativeT a X Y)
    (hnone : ∀ u ∈ aliasAddrs a X Y, ¬ FreeSite a u.1 u.2) : deckAt a 1 X Y = bulkR a 1 X Y := by
  unfold deckAt
  dsimp only
  rw [tr_pickFirst_append]
  have hbulk : pickFirst ((aliasAddrs a X Y).map (fun u => (NativeT a u.1 u.2, bulkR a 1 u.1 u.2)))
      (-1000) = bulkR a 1 X Y := by
    simp [aliasAddrs, pickFirst, hN]
  rw [hbulk]
  apply tr_pickFirst_none
  intro x hx hxg
  obtain ⟨w, hw, hwx⟩ := List.mem_flatMap.mp hx
  apply hnone w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwx
  rcases hwx with rfl | rfl
  · exact Or.inl hxg
  · exact Or.inr hxg

/-- The aliases `p+V`, `p+U`, `p+U+V`, `p+U−V`, `p−U+V`, `p−U−V` of a native point are not free. -/
theorem nofree_i1 {a X Y : ℤ} (ha : 4 ≤ a) (hN : NativeT a X Y) :
    ¬ FreeSite a (X - 2) (Y + 2 * a) := by
  unfold NativeT at hN
  unfold FreeSite FreeHSite FreeVSite
  rcases hN with ⟨⟨h1, h2, h3, h4, h5, h6⟩, hs⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

theorem nofree_i3 {a X Y : ℤ} (ha : 4 ≤ a) (hN : NativeT a X Y) :
    ¬ FreeSite a (X + (a + 1)) (Y + (a - 1)) := by
  unfold NativeT at hN
  unfold FreeSite FreeHSite FreeVSite
  rcases hN with ⟨⟨h1, h2, h3, h4, h5, h6⟩, hs⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

theorem nofree_i4 {a X Y : ℤ} (ha : 4 ≤ a) (hN : NativeT a X Y) :
    ¬ FreeSite a (X + (a - 1)) (Y + (3 * a - 1)) := by
  unfold NativeT at hN
  unfold FreeSite FreeHSite FreeVSite
  rcases hN with ⟨⟨h1, h2, h3, h4, h5, h6⟩, hs⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

theorem nofree_i5 {a X Y : ℤ} (ha : 4 ≤ a) (hN : NativeT a X Y) :
    ¬ FreeSite a (X + (a + 3)) (Y - (a + 1)) := by
  unfold NativeT at hN
  unfold FreeSite FreeHSite FreeVSite
  rcases hN with ⟨⟨h1, h2, h3, h4, h5, h6⟩, hs⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

theorem nofree_i7 {a X Y : ℤ} (ha : 4 ≤ a) (hN : NativeT a X Y) :
    ¬ FreeSite a (X - (a + 3)) (Y + (a + 1)) := by
  unfold NativeT at hN
  unfold FreeSite FreeHSite FreeVSite
  rcases hN with ⟨⟨h1, h2, h3, h4, h5, h6⟩, hs⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

theorem nofree_i8 {a X Y : ℤ} (ha : 4 ≤ a) (hN : NativeT a X Y) :
    ¬ FreeSite a (X - (a - 1)) (Y - (3 * a - 1)) := by
  unfold NativeT at hN
  unfold FreeSite FreeHSite FreeVSite
  rcases hN with ⟨⟨h1, h2, h3, h4, h5, h6⟩, hs⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-- The alias `p − V` of a native point, when free, is native. -/
theorem nat_idx2 {a X Y : ℤ} (ha : 4 ≤ a) (hN : NativeT a X Y) (hf : FreeSite a (X + 2) (Y - 2 * a)) :
    NativeT a (X + 2) (Y - 2 * a) := by
  unfold FreeSite FreeHSite FreeVSite at hf
  unfold NativeT at hN
  rcases hN with ⟨⟨h1, h2, h3, h4, h5, h6⟩, hs⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases hf with (⟨e1, e2⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2⟩) | (⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩) <;>
    first
    | (exfalso; omega)
    | (refine nat_of_box ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> omega)
    | (refine Or.inr (Or.inr ⟨?_, ?_⟩) <;> omega)

/-- The alias `p − U` of a native point, when free and not native, is the special point `(a, 2a−1)`. -/
theorem nat_idx6 {a X Y : ℤ} (ha : 4 ≤ a) (hN : NativeT a X Y)
    (hf : FreeSite a (X - (a + 1)) (Y - (a - 1))) :
    NativeT a (X - (a + 1)) (Y - (a - 1)) ∨ (X = a ∧ Y = 2 * a - 1) := by
  by_cases hsp : X = a ∧ Y = 2 * a - 1
  · exact Or.inr hsp
  left
  unfold FreeSite FreeHSite FreeVSite at hf
  unfold NativeT at hN ⊢
  rcases hN with ⟨⟨h1, h2, h3, h4, h5, h6⟩, hs⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases hf with (⟨e1, e2⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2⟩) | (⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩) <;>
    first
    | (exfalso; omega)
    | exact nat_of_box (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-- An alias `p − V` of a non-free tile point is not free (the tile excludes `p = (p−V)+V`). -/
theorem tile_nofree_idx2 {a X Y : ℤ} (ha : 4 ≤ a) (hp : TwosTile a (X, Y)) (hF : ¬ FreeSite a X Y) :
    ¬ FreeSite a (X + 2) (Y - 2 * a) := by
  intro hf
  exact hp.2 ⟨⟨(X + 2, Y - 2 * a), hf, nat_idx2 ha hp.1 hf, Or.inr (by ext <;> simp)⟩, hF⟩

/-- The tile excludes the alias `p − U` of a non-free tile point, except at `(a, 2a−1)`. -/
theorem tile_nofree_idx6 {a X Y : ℤ} (ha : 4 ≤ a) (hp : TwosTile a (X, Y)) (hF : ¬ FreeSite a X Y)
    (hsp : ¬ (X = a ∧ Y = 2 * a - 1)) : ¬ FreeSite a (X - (a + 1)) (Y - (a - 1)) := by
  intro hf
  rcases nat_idx6 ha hp.1 hf with hn | hs
  · exact hp.2 ⟨⟨(X - (a + 1), Y - (a - 1)), hf, hn, Or.inl (by ext <;> simp)⟩, hF⟩
  · exact hsp hs

/-- The deck value at a non-free tile point (sign +1), away from `(a, 2a−1)`, is the bulk value. -/
theorem tile_deck_bulk {a X Y : ℤ} (ha : 4 ≤ a) (hp : TwosTile a (X, Y))
    (hF : ¬ FreeSite a X Y) (hsp : ¬ (X = a ∧ Y = 2 * a - 1)) :
    deckAt a 1 X Y = bulkR a 1 X Y := by
  have hN : NativeT a X Y := hp.1
  have h2 := tile_nofree_idx2 ha hp hF
  have h6 := tile_nofree_idx6 ha hp hF hsp
  have n1 := nofree_i1 ha hN
  have n3 := nofree_i3 ha hN
  have n4 := nofree_i4 ha hN
  have n5 := nofree_i5 ha hN
  have n7 := nofree_i7 ha hN
  have n8 := nofree_i8 ha hN
  apply deck_of_nofree hN
  intro u hu
  simp only [aliasAddrs, List.map, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;>
    first
    | exact alias_of_eq hF (by ring1) (by ring1)
    | exact alias_of_eq h2 (by ring1) (by ring1)
    | exact alias_of_eq h6 (by ring1) (by ring1)
    | exact alias_of_eq n1 (by ring1) (by ring1)
    | exact alias_of_eq n3 (by ring1) (by ring1)
    | exact alias_of_eq n4 (by ring1) (by ring1)
    | exact alias_of_eq n5 (by ring1) (by ring1)
    | exact alias_of_eq n7 (by ring1) (by ring1)
    | exact alias_of_eq n8 (by ring1) (by ring1)

end FLatticePaper.TwosEPolicy
