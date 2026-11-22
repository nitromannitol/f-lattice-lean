import FLatticePaper.Tiles.BoundaryTransport
import FLatticePaper.Tiles.WalkRows

/-! Boundary walks under cyclic shifts, the quarter turn and translations.

`IsBoundaryFrom T c w` is the boundary-walk property of `IsBoundaryWordAt T c w` without the lower-left condition on the
start `c`. It is preserved by cyclic shifts of the word (the start moves along the walk), by the quarter turn of the tile
(letters multiplied by `i`), and by translations. -/

namespace FLatticePaper.Tiles.BoundaryWalks

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.BoundaryTransport

/-- The boundary-walk property of `w` from `c` on `T`, without the lower-left condition. -/
def IsBoundaryFrom (T : CellTile) (c : GInt) (w : F2Word) : Prop :=
  F2Word.sum w = 0 ∧ (edgesFrom c w).Nodup ∧ (edgesFrom c w).toFinset = T.boundaryEdges

/-- `IsBoundaryWordAt` is the lower-left condition together with `IsBoundaryFrom`. -/
theorem isBoundaryWordAt_iff (T : CellTile) (c : GInt) (w : F2Word) :
    IsBoundaryWordAt T c w ↔ IsLowerLeft T c ∧ IsBoundaryFrom T c w := by
  unfold IsBoundaryWordAt IsBoundaryFrom
  rw [zip_walk_eq]

/-- A cyclic shift of a boundary walk, starting at the vertex reached after `k` letters, is a boundary walk. -/
theorem isBoundaryFrom_rotate (T : CellTile) (c : GInt) (w : F2Word) (h : IsBoundaryFrom T c w)
    (k : ℕ) (hk : k ≤ w.length) :
    IsBoundaryFrom T (c + F2Word.sum (w.take k)) (w.rotate k) := by
  obtain ⟨hs, hnd, hfs⟩ := h
  have hw : w = w.take k ++ w.drop k := (List.take_append_drop k w).symm
  have hrot : w.rotate k = w.drop k ++ w.take k := List.rotate_eq_drop_append_take hk
  set u := w.take k with hu
  set v := w.drop k with hv
  have hsum_uv : F2Word.sum v + F2Word.sum u = 0 := by
    rw [add_comm, ← F2Word_sum_append, ← hw]
    exact hs
  have E1 : edgesFrom c w = edgesFrom c u ++ edgesFrom (c + F2Word.sum u) v := by
    conv_lhs => rw [hw]
    exact edgesFrom_append c u v
  have hc : c + F2Word.sum u + F2Word.sum v = c := by
    rw [add_assoc, add_comm (F2Word.sum u) (F2Word.sum v), hsum_uv, add_zero]
  have E2 : edgesFrom (c + F2Word.sum u) (v ++ u) =
      edgesFrom (c + F2Word.sum u) v ++ edgesFrom c u := by
    rw [edgesFrom_append, hc]
  have hperm : (edgesFrom c u ++ edgesFrom (c + F2Word.sum u) v).Perm
      (edgesFrom (c + F2Word.sum u) v ++ edgesFrom c u) := List.perm_append_comm
  refine ⟨?_, ?_, ?_⟩
  · rw [hrot, F2Word_sum_append]
    exact hsum_uv
  · rw [hrot, E2]
    rw [E1] at hnd
    exact hperm.nodup_iff.mp hnd
  · rw [hrot, E2]
    rw [E1] at hfs
    rw [← hfs, List.toFinset_append, List.toFinset_append, Finset.union_comm]

/-- The walk of the letters multiplied by `i`, from the turned start, is the turned walk. -/
theorem edgesFrom_rotI (c : GInt) (w : F2Word) :
    edgesFrom (rotI c) (w.map Unit4.mulI) = (edgesFrom c w).map rotE := by
  induction w generalizing c with
  | nil => simp [edgesFrom]
  | cons x w ih =>
    simp only [List.map_cons, edgesFrom, vec_mulI, ih, rotE, ← rotI_add]

theorem rotI_zero : rotI 0 = 0 := by
  ext <;> simp [rotI]

theorem rotI_injective : Function.Injective rotI := by
  intro a b h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [rotI] at h1 h2
  ext <;> omega

theorem rotE_injective : Function.Injective rotE := by
  intro e f h
  obtain ⟨e1, e2⟩ := e
  obtain ⟨f1, f2⟩ := f
  simp only [rotE, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  rw [rotI_injective h1, rotI_injective h2]

/-- The quarter turn of a boundary walk is a boundary walk of the turned tile, from the turned start. -/
theorem isBoundaryFrom_rotCells (T : CellTile) (c : GInt) (w : F2Word) (h : IsBoundaryFrom T c w) :
    IsBoundaryFrom (rotCells T) (rotI c) (w.map Unit4.mulI) := by
  obtain ⟨hs, hnd, hfs⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [F2Word_sum_map_mulI, hs, rotI_zero]
  · rw [edgesFrom_rotI]
    exact hnd.map rotE_injective
  · rw [edgesFrom_rotI, boundaryEdges_rotCells]
    ext x
    rw [List.mem_toFinset, List.mem_map, Finset.mem_image]
    have key : ∀ y, y ∈ edgesFrom c w ↔ y ∈ T.boundaryEdges := fun y => by
      rw [← List.mem_toFinset, hfs]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, (key y).1 hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, (key y).2 hy, rfl⟩


/-- The translation of an edge by `v`. -/
def transE (v : GInt) (e : GInt × GInt) : GInt × GInt := (e.1 + v, e.2 + v)

theorem transE_injective (v : GInt) : Function.Injective (transE v) := by
  intro e f h
  obtain ⟨e1, e2⟩ := e
  obtain ⟨f1, f2⟩ := f
  simp only [transE, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  rw [add_left_inj] at h1 h2
  rw [h1, h2]

theorem transE_transE_neg (v : GInt) (x : GInt × GInt) : transE v (transE (-v) x) = x := by
  obtain ⟨⟨x1, x2⟩, ⟨y1, y2⟩⟩ := x
  simp [transE]

theorem mem_image_add_iff (T : CellTile) (v p : GInt) : p ∈ T.image (· + v) ↔ p - v ∈ T := by
  constructor
  · rintro h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 h
    simpa using ha
  · intro h
    exact Finset.mem_image.2 ⟨p - v, h, by simp⟩

theorem image_add_neg (T : CellTile) (v : GInt) : (T.image (· + v)).image (· + -v) = T := by
  rw [Finset.image_image]
  have h : ((fun x => x + -v) ∘ fun x => x + v) = id := funext fun x => by simp
  rw [h, Finset.image_id]

/-- A boundary edge of `T` translates into a boundary edge of the translated tile. -/
theorem bShape_translate_of (T : CellTile) (v : GInt) (e : GInt × GInt) (h : BShape T e) :
    BShape (T.image (· + v)) (transE v e) := by
  obtain ⟨a, b, h⟩ := h
  rcases h with ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩
  · refine ⟨a + v.1, b + v.2, Or.inl ⟨?_, ?_, ?_⟩⟩
    · refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
      all_goals simp [transE]
      all_goals omega
    · rw [mem_image_add_iff]
      convert h1 using 1
      simp only [Prod.ext_iff, Prod.fst_sub, Prod.snd_sub]
      omega
    · intro hh
      apply h2
      rw [mem_image_add_iff] at hh
      convert hh using 1
      simp only [Prod.ext_iff, Prod.fst_sub, Prod.snd_sub]
      omega
  · refine ⟨a + v.1, b + v.2, Or.inr (Or.inl ⟨?_, ?_, ?_⟩)⟩
    · refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
      all_goals simp [transE]
      all_goals omega
    · rw [mem_image_add_iff]
      convert h1 using 1
      simp only [Prod.ext_iff, Prod.fst_sub, Prod.snd_sub]
      omega
    · intro hh
      apply h2
      rw [mem_image_add_iff] at hh
      convert hh using 1
      simp only [Prod.ext_iff, Prod.fst_sub, Prod.snd_sub]
      omega
  · refine ⟨a + v.1, b + v.2, Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩))⟩
    · refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
      all_goals simp [transE]
      all_goals omega
    · rw [mem_image_add_iff]
      convert h1 using 1
      simp only [Prod.ext_iff, Prod.fst_sub, Prod.snd_sub]
      omega
    · intro hh
      apply h2
      rw [mem_image_add_iff] at hh
      convert hh using 1
      simp only [Prod.ext_iff, Prod.fst_sub, Prod.snd_sub]
      omega
  · refine ⟨a + v.1, b + v.2, Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩))⟩
    · refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
      all_goals simp [transE]
      all_goals omega
    · rw [mem_image_add_iff]
      convert h1 using 1
      simp only [Prod.ext_iff, Prod.fst_sub, Prod.snd_sub]
      omega
    · intro hh
      apply h2
      rw [mem_image_add_iff] at hh
      convert hh using 1
      simp only [Prod.ext_iff, Prod.fst_sub, Prod.snd_sub]
      omega

/-- The boundary edges of a translated tile are the translated boundary edges. -/
theorem boundaryEdges_translate (T : CellTile) (v : GInt) :
    CellTile.boundaryEdges (T.image (· + v)) = T.boundaryEdges.image (transE v) := by
  ext x
  rw [mem_boundaryEdges_iff_shape, Finset.mem_image]
  constructor
  · intro hx
    refine ⟨transE (-v) x, ?_, transE_transE_neg v x⟩
    rw [mem_boundaryEdges_iff_shape]
    have h := bShape_translate_of (T.image (· + v)) (-v) x hx
    rw [image_add_neg] at h
    exact h
  · rintro ⟨y, hy, rfl⟩
    rw [mem_boundaryEdges_iff_shape] at hy
    exact bShape_translate_of T v y hy

/-- The walk of a translated word, from the translated start, is the translated walk. -/
theorem edgesFrom_translate (c v : GInt) (w : F2Word) :
    edgesFrom (c + v) w = (edgesFrom c w).map (transE v) := by
  induction w generalizing c with
  | nil => simp [edgesFrom]
  | cons x w ih =>
    have h1 : c + v + x.vec = c + x.vec + v := add_right_comm c v x.vec
    rw [edgesFrom, edgesFrom, List.map_cons, h1, ih]
    rfl

/-- A translation of a boundary walk is a boundary walk of the translated tile, from the translated start. -/
theorem isBoundaryFrom_translate (T : CellTile) (c v : GInt) (w : F2Word) (h : IsBoundaryFrom T c w) :
    IsBoundaryFrom (T.image (· + v)) (c + v) w := by
  obtain ⟨hs, hnd, hfs⟩ := h
  refine ⟨hs, ?_, ?_⟩
  · rw [edgesFrom_translate]
    exact hnd.map (transE_injective v)
  · rw [edgesFrom_translate, boundaryEdges_translate]
    ext x
    rw [List.mem_toFinset, List.mem_map, Finset.mem_image]
    have key : ∀ y, y ∈ edgesFrom c w ↔ y ∈ T.boundaryEdges := fun y => by
      rw [← List.mem_toFinset, hfs]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, (key y).1 hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, (key y).2 hy, rfl⟩


end FLatticePaper.Tiles.BoundaryWalks
