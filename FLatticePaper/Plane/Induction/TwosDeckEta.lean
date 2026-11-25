import FLatticePaper.Plane.Induction.TwosDeckTile

/-! The deck value at the tile points for every sign `η`.

`deck_freeH_eta`, `deck_freeV_eta`, `deck_of_nofree_eta` and `tile_deck_bulk_eta` are the sign-general versions of the sign `+1`
lemmas `deck_freeH`, `deck_freeV`, `deck_of_nofree` and `tile_deck_bulk` of `TwosDeckTile`. The proofs are the same: the sign only
enters as the parameter `η` of `freeH`, `freeV`, `bulkR`, which the unfolding leaves as it is. The sign-free lemmas
(`nat_of_box`, `alias_of_eq`, `nofree_i*`, `tile_nofree_idx*`) are reused from `TwosDeckTile`. -/

namespace FLatticePaper.TwosEPolicy

open FLatticePaper
open scoped Classical

theorem deck_freeH_eta (η : ℤ) {a X Y : ℤ} (hF : FreeHSite a X Y) : deckAt a η X Y = freeH a η X Y := by
  unfold deckAt
  dsimp only
  simp [aliasAddrs, pickFirst, hF]

theorem deck_freeV_eta (η : ℤ) {a X Y : ℤ} (hnH : ¬ FreeHSite a X Y) (hV : FreeVSite a X Y) :
    deckAt a η X Y = freeV a η X Y := by
  unfold deckAt
  dsimp only
  simp [aliasAddrs, pickFirst, hnH, hV]

theorem deck_of_nofree_eta (η : ℤ) {a X Y : ℤ} (hN : NativeT a X Y)
    (hnone : ∀ u ∈ aliasAddrs a X Y, ¬ FreeSite a u.1 u.2) : deckAt a η X Y = bulkR a η X Y := by
  unfold deckAt
  dsimp only
  rw [tr_pickFirst_append]
  have hbulk : pickFirst ((aliasAddrs a X Y).map (fun u => (NativeT a u.1 u.2, bulkR a η u.1 u.2)))
      (-1000) = bulkR a η X Y := by
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

theorem tile_deck_bulk_eta (η : ℤ) {a X Y : ℤ} (ha : 4 ≤ a) (hp : TwosTile a (X, Y))
    (hF : ¬ FreeSite a X Y) (hsp : ¬ (X = a ∧ Y = 2 * a - 1)) :
    deckAt a η X Y = bulkR a η X Y := by
  have hN : NativeT a X Y := hp.1
  have h2 := tile_nofree_idx2 ha hp hF
  have h6 := tile_nofree_idx6 ha hp hF hsp
  have n1 := nofree_i1 ha hN
  have n3 := nofree_i3 ha hN
  have n4 := nofree_i4 ha hN
  have n5 := nofree_i5 ha hN
  have n7 := nofree_i7 ha hN
  have n8 := nofree_i8 ha hN
  apply deck_of_nofree_eta η hN
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
