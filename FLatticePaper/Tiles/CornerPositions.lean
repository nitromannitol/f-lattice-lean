import FLatticePaper.Tiles.StringBridge
import FLatticePaper.Tiles.StringCorners
import FLatticePaper.Tiles.SurgicalAffineChain

/-! The last position of the forward horizontal tile list of a register, in the tile-list representation.

`clauseB_forward_last` (origins representation) gives the last origin of `hWordOf w par`; `StringBridge` identifies it with the last
position of `hStringAt`. The register's forward string at `0` therefore ends at `almostV₁ (bottom) - (1,1)`, the position used by
the junction offsets of the standard steps. -/

namespace FLatticePaper.Tiles.CornerPositions

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings
  FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.StringBridge

theorem lastPos_hWordOf_false (w : Word) :
    lastPosOf (hStringAt (hWordOf w false) (0, 0)) = almostV₁ (oddBottom w) - (1, 1) := by
  have hB := FLatticePaper.Tiles.StringCorners.clauseB_forward_last w
  obtain ⟨hhead, -⟩ := FLatticePaper.Tiles.hWordOf_head_last w false
  obtain ⟨l, ls, hw⟩ : ∃ l ls, hWordOf w false = l :: ls := by
    cases h : hWordOf w false with
    | nil => rw [h] at hhead; simp at hhead
    | cons l ls => exact ⟨l, ls, rfl⟩
  rw [hw, lastOrigin_eq_hStringAt] at hB
  unfold lastPosOf
  rw [hw, hB]
  rfl

theorem lastPos_hWordOf_true (w : Word) :
    lastPosOf (hStringAt (hWordOf w true) (0, 0)) = almostV₁ (evenBottom w) - (1, 1) := by
  have hB := FLatticePaper.Tiles.StringCorners.clauseB_forward_last_even w
  obtain ⟨hhead, -⟩ := FLatticePaper.Tiles.hWordOf_head_last w true
  obtain ⟨l, ls, hw⟩ : ∃ l ls, hWordOf w true = l :: ls := by
    cases h : hWordOf w true with
    | nil => rw [h] at hhead; simp at hhead
    | cons l ls => exact ⟨l, ls, rfl⟩
  rw [hw, lastOrigin_eq_hStringAt] at hB
  unfold lastPosOf
  rw [hw, hB]
  rfl

end FLatticePaper.Tiles.CornerPositions
