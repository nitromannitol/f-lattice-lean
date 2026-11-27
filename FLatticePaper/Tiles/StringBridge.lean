import FLatticePaper.Tiles.StringCorners
import FLatticePaper.Tiles.StringJoin

/-! The bridge between the origin representation of the forward horizontal string (`SiteStrings.origins`, used for the corner
positions of `StringCorners`) and the tile-list representation (`hStringAt`, used by the respect and the corner affine
statements). For a forward word the two positions agree, since the origin step `dxdy false false _ l` is the offset `hOffset l`. -/

namespace FLatticePaper.Tiles.StringBridge

open FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings

theorem dxdy_fwd (x l : Letter) : dxdy false false x l = hOffset l := by
  cases l <;> rfl

theorem scanl_cons_tail (a : GInt) (L : List GInt) :
    List.scanl (· + ·) a L = a :: (List.scanl (· + ·) a L).tail := by
  cases L <;> simp

theorem origins_some_pos (x : Letter) (pos : GInt) (ls : BinaryWord) :
    (origins false false (some x) pos ls).map (·.1) = (List.scanl (· + ·) pos (ls.map hOffset)).tail := by
  induction ls generalizing x pos with
  | nil => simp [origins]
  | cons l ls ih =>
    have hp : (pos.1 + (dxdy false false x l).1, pos.2 + (dxdy false false x l).2) = pos + hOffset l := by
      rw [dxdy_fwd]
      rfl
    simp only [origins, hp, List.map_cons, List.scanl_cons, List.tail_cons]
    rw [ih]
    exact (scanl_cons_tail _ _).symm

theorem origins_none_pos (pos : GInt) (l : Letter) (ls : BinaryWord) :
    (origins false false none pos (l :: ls)).map (·.1) = List.scanl (· + ·) pos (ls.map hOffset) := by
  simp only [origins, List.map_cons]
  rw [origins_some_pos]
  exact (scanl_cons_tail _ _).symm

/-- The last origin of a nonempty forward word is the last position of its tile list. -/
theorem lastOrigin_eq_hStringAt (l : Letter) (ls : BinaryWord) :
    lastOrigin false false (l :: ls) = (hStringAt (l :: ls) (0, 0)).getLast?.map (·.2) := by
  unfold lastOrigin
  have hs : startPos false false = (0, 0) := rfl
  have hlen : (tileSeq (l :: ls)).length = (List.scanl (· + ·) (0, 0) ((l :: ls).tail.map hOffset)).length := by
    unfold tileSeq
    rw [FLatticePaper.Tiles.StringJoin.tileSeqAux_length, List.length_scanl, List.length_map, List.length_tail]
    simp
  have h2 : (hStringAt (l :: ls) (0, 0)).map (·.2) = List.scanl (· + ·) (0, 0) ((l :: ls).tail.map hOffset) := by
    unfold hStringAt
    rw [List.map_snd_zip]
    all_goals simp [hlen]
  rw [hs, ← List.getLast?_map, origins_none_pos, ← List.getLast?_map, h2]
  rfl

end FLatticePaper.Tiles.StringBridge
