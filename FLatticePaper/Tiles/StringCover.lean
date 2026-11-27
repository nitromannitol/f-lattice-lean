import FLatticePaper.Tiles.StringBridge
import FLatticePaper.Tiles.ClosedWalkVertical

/-! The forward horizontal string as a tile list: a point lies in the sites `stringSites false false h` of the string exactly when
the tile list `hStringAt h (0,0)` covers it (`tileCovers`: the point lies in the domain of one of its tiles).

The origins of `origins false false` are the positions of `hStringAt` (`StringBridge.origins_none_pos`), and each origin entry
(letter, enlargement flag) is the tile `tileOfEntry` of `tileSeq`, whose shape is `baseSites`. -/

namespace FLatticePaper.Tiles.StringCover

open FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings FLatticePaper.Farey FLatticePaper.Tiles.StringBridge

/-- The tile of an origin entry: the letter and its enlargement flag (`zero` for `p`, `oneD` for an enlarged `q`). -/
def tileOfEntry (l : Letter) (f : Bool) : ZTile :=
  match l, f with
  | .p, _ => .zero
  | .q, false => .one
  | .q, true => .oneD

theorem tileOfEntry_shape (l : Letter) (f : Bool) : tileShape (tileOfEntry l f) = baseSites l f := by
  cases l <;> cases f <;> rfl

theorem tileSeqAux_cons_some (pr l : Letter) (ls : BinaryWord) :
    tileSeqAux (some pr) (l :: ls) = tileOfEntry l (pr == .q && l == .q) :: tileSeqAux (some l) ls := by
  cases pr <;> cases l <;> rfl

theorem origins_tiles (pr : Letter) (pos : GInt) (ls : BinaryWord) :
    (origins false false (some pr) pos ls).map (fun e => tileOfEntry e.2.1 e.2.2) = tileSeqAux (some pr) ls := by
  induction ls generalizing pr pos with
  | nil => simp [origins, tileSeqAux]
  | cons l ls ih =>
    simp only [origins, List.map_cons, Bool.not_false, Bool.true_and]
    rw [tileSeqAux_cons_some, ih l]

/-- The horizontal tile list of a nonempty word is the list of its origin entries with their tiles and origins. -/
theorem hStringAt_eq_origins (l : Letter) (ls : BinaryWord) :
    hStringAt (l :: ls) (0, 0) =
      (origins false false none (0, 0) (l :: ls)).map (fun e => (tileOfEntry e.2.1 e.2.2, e.1)) := by
  have hT : (origins false false none (0, 0) (l :: ls)).map (fun e => tileOfEntry e.2.1 e.2.2) = tileSeq (l :: ls) := by
    simp only [origins, List.map_cons]
    rw [origins_tiles]
    unfold tileSeq
    cases l <;> rfl
  have hP : (origins false false none (0, 0) (l :: ls)).map (·.1) = List.scanl (· + ·) (0, 0) (ls.map hOffset) :=
    origins_none_pos (0, 0) l ls
  unfold hStringAt
  rw [List.tail_cons, ← hT, ← hP, List.zip_map']

theorem tileCovers_map {α : Type} (O : List α) (F : α → ZTile × GInt) (z : GInt) :
    tileCovers (O.map F) z ↔ ∃ e ∈ O, z ∈ (tileShape (F e).1).map (· + (F e).2) := by
  unfold tileCovers
  constructor
  · rintro ⟨k, hk, hz⟩
    have hk' : k < O.length := by simpa using hk
    refine ⟨O[k], List.getElem_mem hk', ?_⟩
    have hget : (O.map F).getD k (ZTile.zero, (0 : GInt)) = F (O[k]) := by
      simp [List.getD_eq_getElem?_getD, hk']
    rw [hget] at hz
    exact hz
  · rintro ⟨e, he, hz⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 he
    refine ⟨k, by simpa using hk, ?_⟩
    have hget : (O.map F).getD k (ZTile.zero, (0 : GInt)) = F (O[k]) := by
      simp [List.getD_eq_getElem?_getD, hk]
    rw [hget]
    exact hz

theorem shift_point (e b : GInt) : b + e = (e.1 + b.1, e.2 + b.2) := by
  ext <;> simp [add_comm]

/-- **The string sites are the tile covers.** A point lies in the sites of the forward horizontal string `h` (from the origin
`(0,0)`) exactly when the tile list `hStringAt h (0,0)` covers it. -/
theorem covers_iff_stringSites (h : BinaryWord) (z : GInt) :
    tileCovers (hStringAt h (0, 0)) z ↔ z ∈ stringSites false false h := by
  cases h with
  | nil => simp [hStringAt, tileCovers, stringSites, origins, tileSeq, tileSeqAux]
  | cons l ls =>
    rw [hStringAt_eq_origins, tileCovers_map]
    have hs : startPos false false = (0, 0) := rfl
    unfold stringSites
    rw [hs, List.mem_flatMap]
    constructor
    · rintro ⟨e, he, hz⟩
      refine ⟨e, he, ?_⟩
      rw [tileOfEntry_shape] at hz
      simp only [List.mem_map] at hz ⊢
      obtain ⟨b, hb, hbz⟩ := hz
      exact ⟨b, hb, by rw [← shift_point]; exact hbz⟩
    · rintro ⟨e, he, hz⟩
      refine ⟨e, he, ?_⟩
      rw [tileOfEntry_shape]
      simp only [List.mem_map] at hz ⊢
      obtain ⟨b, hb, hbz⟩ := hz
      exact ⟨b, hb, by rw [shift_point]; exact hbz⟩

end FLatticePaper.Tiles.StringCover
