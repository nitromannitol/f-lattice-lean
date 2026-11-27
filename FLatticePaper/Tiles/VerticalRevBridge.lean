import FLatticePaper.Tiles.ReflectedCover
import FLatticePaper.Tiles.VerticalRight

/-! The reversed vertical string covers exactly the vertical sites of the marks: `tileCovers (vRevStringAt u c) z` holds exactly
when `z - c` lies in `Mv u 0`, the base sites of the origins `origins true true` from `0`; the marked vertical sites of a tile
with lower-left point `0` are the sites `stringSites true true u` shifted by `-(1,1)`, which is `Mv u 0`. -/

namespace FLatticePaper.Tiles.VerticalRevBridge

open FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.ReflectedCover FLatticePaper.Farey

/-- The sites of one origin entry: the base sites of its letter, from its origin. -/
def ent0 (e : GInt × Letter × Bool) : List GInt :=
  (baseSites e.2.1 e.2.2).map fun b => (e.1.1 + b.1, e.1.2 + b.2)

/-- The sites of a vertical word from an origin. -/
def Mv (u : BinaryWord) (pos : GInt) : List GInt :=
  (origins true true none pos u).flatMap ent0

theorem vRevOffset_eq_dxdy (a b : Letter) : vRevOffset a b = dxdy true true a b := by
  cases a <;> cases b <;> rfl

theorem letterZTile_shape (l : Letter) : tileShape (letterZTile l) = baseSites l false := by
  cases l <;> rfl

theorem vRevStringAt_cons2 (x y : Letter) (r : BinaryWord) (c : GInt) :
    vRevStringAt (x :: y :: r) c = (letterZTile x, c) :: vRevStringAt (y :: r) (c + vRevOffset x y) := by
  unfold vRevStringAt
  simp [List.scanl_cons]

theorem vRevStringAt_single (x : Letter) (c : GInt) : vRevStringAt [x] c = [(letterZTile x, c)] := by
  simp [vRevStringAt]

/-- Translating the origins translates the entries. -/
theorem origins_shift (pr : Option Letter) (pos d : GInt) : ∀ ls : BinaryWord,
    origins true true pr (pos + d) ls = (origins true true pr pos ls).map (fun e => (e.1 + d, e.2)) := by
  intro ls
  induction ls generalizing pr pos with
  | nil => simp [origins]
  | cons l ls ih =>
    cases pr with
    | none =>
      simp only [origins, List.map_cons]
      rw [ih (some l)]
    | some a =>
      simp only [origins, List.map_cons]
      have e : ((pos + d).1 + (dxdy true true a l).1, (pos + d).2 + (dxdy true true a l).2) =
          (pos.1 + (dxdy true true a l).1, pos.2 + (dxdy true true a l).2) + d := by
        ext <;> simp <;> ring
      rw [e, ih (some l)]

theorem Mv_cons2 (x y : Letter) (r : BinaryWord) (pos : GInt) :
    Mv (x :: y :: r) pos = ent0 (pos, x, false) ++ Mv (y :: r) (pos + dxdy true true x y) := by
  unfold Mv
  simp [origins, List.flatMap_cons]
  rfl

theorem mem_Mv_translate (u : BinaryWord) (pos d z : GInt) : z ∈ Mv u (pos + d) ↔ z - d ∈ Mv u pos := by
  unfold Mv
  rw [origins_shift none pos d u, List.mem_flatMap, List.mem_flatMap]
  constructor
  · rintro ⟨a, ha, hz⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
    refine ⟨e, he, ?_⟩
    simp only [ent0, List.mem_map] at hz ⊢
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨b, hb, ?_⟩
    rw [← hbz]
    ext <;> simp <;> ring
  · rintro ⟨e, he, hz⟩
    refine ⟨(e.1 + d, e.2), List.mem_map.2 ⟨e, he, rfl⟩, ?_⟩
    simp only [ent0, List.mem_map] at hz ⊢
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨b, hb, ?_⟩
    rw [show z = (e.1.1 + b.1, e.1.2 + b.2) + d by rw [hbz]; abel]
    ext <;> simp <;> ring

/-- The first tile of a reversed string covers exactly the first entry of `Mv`. -/
theorem shape_iff_ent0 (x : Letter) (c z : GInt) :
    z ∈ (tileShape (letterZTile x, c).1).map (· + (letterZTile x, c).2) ↔ z - c ∈ ent0 ((0 : GInt), x, false) := by
  rw [letterZTile_shape]
  simp only [ent0, List.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, by ext <;> simp⟩
  · rintro ⟨b, hb, hbz⟩
    refine ⟨b, hb, ?_⟩
    show b + c = z
    rw [show z = (z - c) + c by abel, ← hbz]
    ext <;> simp

/-- **The reversed vertical string covers exactly `Mv u 0`.** -/
theorem covers_iff_Mv (u : BinaryWord) : ∀ (c z : GInt), tileCovers (vRevStringAt u c) z ↔ z - c ∈ Mv u 0 := by
  induction u with
  | nil => intro c z; simp [vRevStringAt, Mv, origins, tileCovers_nil']
  | cons x rest ih =>
    intro c z
    cases rest with
    | nil =>
      rw [vRevStringAt_single, tileCovers_cons']
      simp only [tileCovers_nil', or_false]
      rw [shape_iff_ent0]
      simp only [Mv, origins, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    | cons y r =>
      have key := mem_Mv_translate (y :: r) 0 (vRevOffset x y) (z - c)
      rw [zero_add] at key
      rw [vRevStringAt_cons2, tileCovers_cons', shape_iff_ent0, ih (c + vRevOffset x y) z]
      rw [Mv_cons2 x y r 0, List.mem_append, zero_add, ← vRevOffset_eq_dxdy, key,
        show z - (c + vRevOffset x y) = z - c - vRevOffset x y by abel]

/-- **The marked vertical sites are the reversed vertical covers.** The vertical part of the marks of a tile with lower-left point
`0` is `stringSites true true u` shifted by `(-1,-1)`; it is the cover of the reversed vertical string from `0`. -/
theorem mem_marked_vert_iff (u : BinaryWord) (x : GInt) :
    x ∈ (stringSites true true u).map (fun z => (z.1 + ((0 : GInt).1) - 1, z.2 + ((0 : GInt).2) - 1)) ↔
      tileCovers (vRevStringAt u (0, 0)) x := by
  rw [covers_iff_Mv, Prod.mk_zero_zero, sub_zero]
  have hs : stringSites true true u = Mv u ((0 : GInt) + ((1 : ℤ), (1 : ℤ))) := by
    simp [stringSites, Mv, startPos]
    rfl
  rw [hs, List.mem_map]
  constructor
  · rintro ⟨s, hs', hsx⟩
    rw [mem_Mv_translate] at hs'
    have e : s - ((1 : ℤ), (1 : ℤ)) = x := by
      rw [← hsx]
      ext <;> simp
    rw [← e]
    exact hs'
  · intro hx
    refine ⟨x + ((1 : ℤ), (1 : ℤ)), ?_, ?_⟩
    · rw [mem_Mv_translate]
      simpa using hx
    · ext <;> simp

end FLatticePaper.Tiles.VerticalRevBridge
