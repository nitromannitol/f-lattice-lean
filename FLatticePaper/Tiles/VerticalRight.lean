import FLatticePaper.Tiles.RegisterLink
import FLatticePaper.Tiles.StandardBoundary
import FLatticePaper.Tiles.SiteStrings
import FLatticePaper.Tiles.BottomEdges
import FLatticePaper.Tiles.WalkDecomp

/-! The right edges of the standard tiles are `i`-multiples of horizontal words: `oddRight w = gV (vWordOf w false)` and
`evenRight w = gV (vWordOf w true)`, where `gV u = i · gH (flipW u)` (`PseudoSquare.gV`). The walk of an `i`-multiple of a word is
the rotation of the walk of the word (`walk_zero_map_mulI`, `walk_map_mulI_shift`), so the right side of the boundary walk is a
rotated horizontal walk. The vertical string of the marks is then identified with the rotated horizontal walk in a later step. -/

namespace FLatticePaper.Tiles.VerticalRight

open FLatticePaper.Tiles FLatticePaper.Farey FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.Standard
open FLatticePaper.Tiles.StandardBoundary

theorem flipLetter_swapLetter (x : Letter) : flipLetter (swapLetter x) = x := by
  cases x <;> rfl

theorem flipW_map_swapLetter (X : BinaryWord) : flipW (X.map swapLetter) = X := by
  simp [flipW, List.map_map, Function.comp_def, flipLetter_swapLetter]

/-- The flip of the vertical word of an odd tile is the horizontal word of the swapped word with the even parity. -/
theorem flipW_vWordOf (w : Word) (par : Bool) :
    flipW (vWordOf w par) = hWordOf (swapW w) (!par) := by
  cases par <;> unfold vWordOf <;> rw [flipW_map_swapLetter] <;> rfl

/-- The odd right edge is `i` times the horizontal word of the swapped word with the even parity: `gV` of the vertical word. -/
theorem oddRight_eq_gV (w : Word) : oddRight w = gV (vWordOf w false) := by
  have h1 : oddRight w = (gH (hWordOf (swapW w) true)).map Unit4.mulI :=
    congrArg (fun x => x.map Unit4.mulI) (RegisterLink.evenBottom_eq_gH (swapW w))
  rw [h1, gV, flipW_vWordOf]
  rfl

/-- The even right edge is `i` times the horizontal word of the swapped word with the odd parity: `gV` of the vertical word. -/
theorem evenRight_eq_gV (w : Word) : evenRight w = gV (vWordOf w true) := by
  have h1 : evenRight w = (gH (hWordOf (swapW w) false)).map Unit4.mulI :=
    congrArg (fun x => x.map Unit4.mulI) (RegisterLink.oddBottom_eq_gH (swapW w))
  rw [h1, gV, flipW_vWordOf]
  rfl

theorem walk_zero_map_mulI (u : F2Word) :
    F2Word.walk 0 (u.map Unit4.mulI) = (F2Word.walk 0 u).map rotI := by
  induction u with
  | nil =>
    simp [WalkDecomp.walk_nil, rotI]
    rfl
  | cons x u ih =>
    have key : ∀ z : GInt, (0 : GInt) + rotI (Unit4.vec x) + rotI z = rotI (0 + Unit4.vec x + z) := by
      intro z
      simp only [zero_add, rotI_add]
    rw [List.map_cons, WalkDecomp.walk_cons, WalkDecomp.walk_cons, vec_mulI,
      WalkDecomp.walk_translate (0 + rotI (Unit4.vec x)) (u.map Unit4.mulI), ih,
      List.map_cons, WalkDecomp.walk_translate (0 + Unit4.vec x) u, List.map_map, List.map_map]
    exact congrArg₂ List.cons rfl (List.map_congr_left fun z _ => key z)

/-- The walk of an `i`-multiple of a word from `c` is the rotated walk of the word, translated by `c`. -/
theorem walk_map_mulI_shift (c : GInt) (u : F2Word) :
    F2Word.walk c (u.map Unit4.mulI) = (F2Word.walk 0 u).map (fun z => c + rotI z) := by
  rw [WalkDecomp.walk_translate c (u.map Unit4.mulI), walk_zero_map_mulI, List.map_map]
  rfl

end FLatticePaper.Tiles.VerticalRight
