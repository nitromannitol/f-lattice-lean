import FLatticePaper.Tiles.VerticalReflect
import FLatticePaper.Tiles.VerticalRevBridge
import FLatticePaper.Tiles.ReflectedCover

/-! # The vertical reflection of the zero-one strings, as a list identity

For a word `v` and a last letter `x`, the reversed vertical string of `(v ++ [x]).reverse` from `c` is the reflection of the forward
vertical string of `v ++ [x]` from `a`, about the constant `K = a + lastPos(vStringAt (v ++ [x]) 0) + shR x`, with the tiles in the
reverse order: each placed tile `(t, P)` goes to `(t, K - P - shR t)`, where `shR t` is the shift of the letter of the tile
(`(1,2)` for `zero`, `(1,1)` for `one`). This holds for every word, with no hypothesis on its letters (checked numerically on all
binary words up to length 5, `scratchpad/halfturn_vert_uniform.py`). -/

namespace FLatticePaper.Tiles.VertStringReflect

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.ReflectedCover
open FLatticePaper.Tiles.VerticalReflect FLatticePaper.Tiles.VerticalRevBridge

/-- The reflection shift of a tile of a vertical string: `(1,2)` for the `zero` tile (`p`), `(1,1)` for the `one` tile (`q`). -/
def sT : ZTile → GInt
  | .zero => (1, 2)
  | .one => (1, 1)
  | .oneD => (1, 1)

theorem sT_letter (x : Letter) : sT (letterZTile x) = shR x := by
  cases x <;> rfl

theorem vRev_reflect_gen (v : BinaryWord) : ∀ (x : Letter) (a c : GInt),
    vRevStringAt (v ++ [x]).reverse c =
      ((vStringAt (v ++ [x]) a).map
        (fun t => (t.1, a + lastPosOf (vStringAt (v ++ [x]) (0, 0)) + shR x + c - t.2 - sT t.1))).reverse := by
  induction v using List.reverseRecOn with
  | nil =>
    intro x a c
    rw [List.nil_append, List.reverse_singleton, vRev_single]
    simp [vStr_single, lastPosOf, sT_letter]
    abel
  | append_singleton l y ih =>
    intro x a c
    have hne : l ++ [y] ≠ [] := by simp
    have hrev : (l ++ [y] ++ [x]).reverse = x :: y :: l.reverse := by simp
    have hrev2 : (l ++ [y]).reverse = y :: l.reverse := by simp
    rw [hrev, vRevStringAt_cons2]
    have hin := ih y a (c + vRevOffset x y)
    rw [hrev2] at hin
    rw [hin, vStr_append (l ++ [y]) a x hne, vStr_append (l ++ [y]) (0, 0) x hne]
    have hLa : lastPosOf (vStringAt (l ++ [y]) a) = a + lastPosOf (vStringAt (l ++ [y]) (0, 0)) := by
      rw [vStr_lastPos _ a hne, vStr_lastPos _ (0, 0) hne]
      ext <;> simp
    rw [hLa]
    simp only [List.map_append, List.reverse_append, List.map_cons, List.map_nil, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.singleton_append]
    have hLx : lastPosOf (vStringAt (l ++ [y]) (0, 0) ++ [(letterZTile x, lastPosOf (vStringAt (l ++ [y]) (0, 0)) + vOffset x)]) =
        lastPosOf (vStringAt (l ++ [y]) (0, 0)) + vOffset x := by
      simp [lastPosOf]
    rw [hLx]
    congr 1
    · rw [sT_letter]
      congr 1
      abel
    · congr 1
      apply List.map_congr_left
      intro t _
      rw [vrev_offset_identity x y]
      congr 1
      abel

end FLatticePaper.Tiles.VertStringReflect
