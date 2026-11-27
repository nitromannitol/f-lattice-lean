import FLatticePaper.Tiles.CommonExtensionStandard
import FLatticePaper.Tiles.StringCorners
import FLatticePaper.Tiles.BaseInvariant
import FLatticePaper.Tiles.VBase
import FLatticePaper.Tiles.MarksIn
import FLatticePaper.Tiles.SurgicalAffineChain

/-! Shared points of the translates of the odd standard tile: the neighbour overlaps `hA1h` and `hA1v` of the
closed-walk theorem `CommonExtFamily.family_closed_walks_zero`. The points come from the origin list of the horizontal
string (last origin `almostV₁ - (1,1)`, `clauseB_forward_last`) and of the reversed vertical string (last origin
`almostV₂ + (2,-1)`, `clauseB_vertical_last`), through the marks of the standard tile (`horizontal_marks`, `vertical_marks`). -/

namespace FLatticePaper.Tiles.CommonExtWitness

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
  FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.StandardClause
  FLatticePaper.Tiles.CommonExtFamily FLatticePaper.Tiles.Standard

/-- The last letter of the origin list of a string is the last letter of the word. -/
theorem origins_getLast_letter (vert rev : Bool) (ls : List Letter) :
    ∀ (pre : Option Letter) (pos : ℤ × ℤ),
      ((origins vert rev pre pos ls).getLast?).map (fun e => e.2.1) = ls.getLast? := by
  induction ls with
  | nil => intro pre pos; simp [origins]
  | cons l ls ih =>
    have key : ∀ (e : (ℤ × ℤ) × Letter × Bool) (L : List ((ℤ × ℤ) × Letter × Bool)),
        e.2.1 = l → (L.getLast?).map (fun e => e.2.1) = ls.getLast? →
        ((e :: L).getLast?).map (fun e => e.2.1) = (l :: ls).getLast? := by
      intro e L he hL
      rw [List.getLast?_cons, List.getLast?_cons]
      cases hLl : L.getLast? with
      | none =>
        rw [hLl] at hL
        simp only [Option.map_none] at hL
        simp only [Option.getD_none, Option.map_some, ← hL, he]
      | some x =>
        rw [hLl] at hL
        simp only [Option.map_some] at hL
        simp only [Option.getD_some, Option.map_some, ← hL]
    intro pre pos
    cases pre with
    | none => simp only [origins]; exact key _ _ rfl (ih _ _)
    | some pr => simp only [origins]; exact key _ _ rfl (ih _ _)

/-- A base point at the last origin of a string whose last letter is `l` is a site of the string. -/
theorem mem_stringSites_last (vert rev : Bool) (ls : List Letter) (o : ℤ × ℤ) (l : Letter)
    (hlo : lastOrigin vert rev ls = some o) (hll : ls.getLast? = some l) (b : ℤ × ℤ)
    (hb : ∀ f : Bool, b ∈ baseSites l f) : (o.1 + b.1, o.2 + b.2) ∈ stringSites vert rev ls := by
  have hmap := origins_getLast_letter vert rev ls none (startPos vert rev)
  rw [hll] at hmap
  obtain ⟨e, he⟩ : ∃ e, (origins vert rev none (startPos vert rev) ls).getLast? = some e := by
    cases h : (origins vert rev none (startPos vert rev) ls).getLast? with
    | none => rw [h] at hmap; simp at hmap
    | some e => exact ⟨e, rfl⟩
  have he1 : e.2.1 = l := by
    rw [he] at hmap
    simpa using hmap
  have heo : e.1 = o := by
    unfold lastOrigin at hlo
    rw [he] at hlo
    simpa using hlo
  have hmem := List.mem_of_getLast? he
  unfold stringSites
  rw [List.mem_flatMap]
  refine ⟨e, hmem, ?_⟩
  rw [he1, List.mem_map]
  refine ⟨b, hb e.2.2, ?_⟩
  rw [heo]

/-- A base point at the first origin of a string `l :: ls` (the origin `startPos`) is a site of the string. -/
theorem mem_stringSites_first (vert rev : Bool) (l : Letter) (ls : List Letter) (b : ℤ × ℤ)
    (hb : ∀ f : Bool, b ∈ baseSites l f) :
    ((startPos vert rev).1 + b.1, (startPos vert rev).2 + b.2) ∈ stringSites vert rev (l :: ls) := by
  unfold stringSites
  rw [List.mem_flatMap]
  refine ⟨(startPos vert rev, l, false), ?_, ?_⟩
  · simp [origins]
  · rw [List.mem_map]
    exact ⟨b, hb false, rfl⟩

theorem mem_base_00 (l : Letter) (f : Bool) : ((0 : ℤ), (0 : ℤ)) ∈ baseSites l f := by
  cases l <;> cases f <;> simp [baseSites]

theorem mem_base_10 (l : Letter) (f : Bool) : ((1 : ℤ), (0 : ℤ)) ∈ baseSites l f := by
  cases l <;> cases f <;> simp [baseSites]

theorem mem_base_11 (l : Letter) (f : Bool) : ((1 : ℤ), (1 : ℤ)) ∈ baseSites l f := by
  cases l <;> cases f <;> simp [baseSites]

theorem mem_base_02 (f : Bool) : ((0 : ℤ), (2 : ℤ)) ∈ baseSites Letter.p f := by
  cases f <;> simp [baseSites]

/-- `(0,0)` is a point of the odd standard tile (the first origin of the horizontal string). -/
theorem zero_mem_oddTile (w : Word) : ((0 : ℤ), (0 : ℤ)) ∈ oddTile w := by
  obtain ⟨hh, -⟩ := FLatticePaper.Tiles.hWordOf_head_last w false
  obtain ⟨l, ls, hw⟩ : ∃ l ls, hWordOf w false = l :: ls := by
    cases h : hWordOf w false with
    | nil => rw [h] at hh; simp at hh
    | cons l ls => exact ⟨l, ls, rfl⟩
  have h2 := mem_stringSites_first false false l ls (0, 0) (fun f => mem_base_00 l f)
  rw [← hw] at h2
  have h3 := (FLatticePaper.Tiles.BaseInvariant.horizontal_marks w).1 _ h2
  have e : ((startPos false false).1 + ((0 : ℤ), (0 : ℤ)).1, (startPos false false).2 + ((0 : ℤ), (0 : ℤ)).2) =
      ((0 : ℤ), (0 : ℤ)) := by
    simp [startPos]
  rw [e] at h3
  exact h3

/-- `(1,0)` is a point of the odd standard tile (the first origin of the horizontal string). -/
theorem one_zero_mem_oddTile (w : Word) : ((1 : ℤ), (0 : ℤ)) ∈ oddTile w := by
  obtain ⟨hh, -⟩ := FLatticePaper.Tiles.hWordOf_head_last w false
  obtain ⟨l, ls, hw⟩ : ∃ l ls, hWordOf w false = l :: ls := by
    cases h : hWordOf w false with
    | nil => rw [h] at hh; simp at hh
    | cons l ls => exact ⟨l, ls, rfl⟩
  have h2 := mem_stringSites_first false false l ls (1, 0) (fun f => mem_base_10 l f)
  rw [← hw] at h2
  have h3 := (FLatticePaper.Tiles.BaseInvariant.horizontal_marks w).1 _ h2
  have e : ((startPos false false).1 + ((1 : ℤ), (0 : ℤ)).1, (startPos false false).2 + ((1 : ℤ), (0 : ℤ)).2) =
      ((1 : ℤ), (0 : ℤ)) := by
    simp [startPos]
  rw [e] at h3
  exact h3

/-- The vector `v₁ = almostV₁ (oddBottom w)` is a point of the odd standard tile. -/
theorem texV1_mem_oddTile (w : Word) : texV1Odd (fracOdd w) ∈ oddTile w := by
  obtain ⟨-, hll⟩ := FLatticePaper.Tiles.hWordOf_head_last w false
  have hlo := FLatticePaper.Tiles.StringCorners.clauseB_forward_last w
  have h2 := mem_stringSites_last false false (hWordOf w false) (almostV₁ (oddBottom w) - (1, 1)) Letter.p
    hlo hll (1, 1) (fun f => mem_base_11 Letter.p f)
  have e : ((almostV₁ (oddBottom w) - (1, 1)).1 + ((1 : ℤ), (1 : ℤ)).1,
      (almostV₁ (oddBottom w) - (1, 1)).2 + ((1 : ℤ), (1 : ℤ)).2) = almostV₁ (oddBottom w) :=
    Prod.ext (by simp) (by simp)
  rw [e] at h2
  have h3 := (FLatticePaper.Tiles.BaseInvariant.horizontal_marks w).1 _ h2
  rw [← sum_oddBottom w]
  exact h3

/-- The vector `v₂ + (1,0)` is a point of the odd standard tile (the last vertical tile, letter `p`). -/
theorem vtwo_mem_oddTile (w : Word) : texV2 (fracOdd w) + (1, 0) ∈ oddTile w := by
  have hvw : vWordOf w false = vertWord w := rfl
  have hh := FLatticePaper.Tiles.StringCorners.vertWord_head_last w
  have hll : (vWordOf w false).reverse.getLast? = some Letter.p := by
    rw [hvw, List.getLast?_reverse]
    exact hh.1
  have hlo := FLatticePaper.Tiles.StringCorners.clauseB_vertical_last w
  have h2 := mem_stringSites_last true true (vWordOf w false).reverse (almostV₂ (oddRight w) + (2, -1)) Letter.p
    hlo hll (0, 2) (fun f => mem_base_02 f)
  have h3 := (FLatticePaper.Tiles.VBase.vertical_marks w).1 _ ((FLatticePaper.Tiles.MarksIn.stringSites_true_iff _ _).1 h2)
  have h4 : almostV₂ (oddRight w) + (1, 0) ∈ oddTile w := by
    convert h3 using 1
    exact Prod.ext (by simp; ring) (by simp; ring)
  rw [← sum_oddRight w]
  exact h4

/-- The even standard tile contains `(0,0)`, `(1,0)` and the first-tile points of the horizontal string. -/
theorem zero_mem_evenTile (w : Word) : ((0 : ℤ), (0 : ℤ)) ∈ evenTile w := by
  obtain ⟨hh, -⟩ := FLatticePaper.Tiles.hWordOf_head_last w true
  obtain ⟨l, ls, hw⟩ : ∃ l ls, hWordOf w true = l :: ls := by
    cases h : hWordOf w true with
    | nil => rw [h] at hh; simp at hh
    | cons l ls => exact ⟨l, ls, rfl⟩
  have h2 := mem_stringSites_first false false l ls (0, 0) (fun f => mem_base_00 l f)
  rw [← hw] at h2
  have h3 := (FLatticePaper.Tiles.BaseInvariant.horizontal_marks w).2 _ h2
  have e : ((startPos false false).1 + ((0 : ℤ), (0 : ℤ)).1, (startPos false false).2 + ((0 : ℤ), (0 : ℤ)).2) =
      ((0 : ℤ), (0 : ℤ)) := by
    simp [startPos]
  rw [e] at h3
  exact h3

theorem one_zero_mem_evenTile (w : Word) : ((1 : ℤ), (0 : ℤ)) ∈ evenTile w := by
  obtain ⟨hh, -⟩ := FLatticePaper.Tiles.hWordOf_head_last w true
  obtain ⟨l, ls, hw⟩ : ∃ l ls, hWordOf w true = l :: ls := by
    cases h : hWordOf w true with
    | nil => rw [h] at hh; simp at hh
    | cons l ls => exact ⟨l, ls, rfl⟩
  have h2 := mem_stringSites_first false false l ls (1, 0) (fun f => mem_base_10 l f)
  rw [← hw] at h2
  have h3 := (FLatticePaper.Tiles.BaseInvariant.horizontal_marks w).2 _ h2
  have e : ((startPos false false).1 + ((1 : ℤ), (0 : ℤ)).1, (startPos false false).2 + ((1 : ℤ), (0 : ℤ)).2) =
      ((1 : ℤ), (0 : ℤ)) := by
    simp [startPos]
  rw [e] at h3
  exact h3

/-- The vector `v₁ = almostV₁ (evenBottom w)` is a point of the even standard tile. -/
theorem texV1_mem_evenTile (w : Word) : texV1Even (fracEven w) ∈ evenTile w := by
  obtain ⟨-, hll⟩ := FLatticePaper.Tiles.hWordOf_head_last w true
  have hlo := FLatticePaper.Tiles.StringCorners.clauseB_forward_last_even w
  have h2 := mem_stringSites_last false false (hWordOf w true) (almostV₁ (evenBottom w) - (1, 1)) Letter.p
    hlo hll (1, 1) (fun f => mem_base_11 Letter.p f)
  have e : ((almostV₁ (evenBottom w) - (1, 1)).1 + ((1 : ℤ), (1 : ℤ)).1,
      (almostV₁ (evenBottom w) - (1, 1)).2 + ((1 : ℤ), (1 : ℤ)).2) = almostV₁ (evenBottom w) :=
    Prod.ext (by simp) (by simp)
  rw [e] at h2
  have h3 := (FLatticePaper.Tiles.BaseInvariant.horizontal_marks w).2 _ h2
  rw [← sum_evenBottom w]
  exact h3

/-- The vector `v₂ + (1,0)` is a point of the even standard tile (the last vertical tile, letter `p`). -/
theorem vtwo_mem_evenTile (w : Word) : texV2 (fracEven w) + (1, 0) ∈ evenTile w := by
  have hll : (vWordOf w true).reverse.getLast? = some Letter.p := by
    rw [List.getLast?_reverse]
    exact (FLatticePaper.Tiles.StringCorners.vWord_even_head_last w).1
  have hlo := FLatticePaper.Tiles.StringCorners.clauseB_vertical_last_even w
  have h2 := mem_stringSites_last true true (vWordOf w true).reverse (almostV₂ (evenRight w) + (2, -1)) Letter.p
    hlo hll (0, 2) (fun f => mem_base_02 f)
  have h3 := (FLatticePaper.Tiles.VBase.vertical_marks w).2 _ ((FLatticePaper.Tiles.MarksIn.stringSites_true_iff _ _).1 h2)
  have h4 : almostV₂ (evenRight w) + (1, 0) ∈ evenTile w := by
    convert h3 using 1
    exact Prod.ext (by simp; ring) (by simp; ring)
  rw [← sum_evenRight w]
  exact h4

/-- Neighbour overlaps from two shared points: `0 ∈ T` and `v₁ ∈ T` give `T + v_p` and `T + v_{p+e₁}` a common point. -/
theorem hA1h_of_witness {T : Set (ℤ × ℤ)} {v1 v2 : ℤ × ℤ} (h0 : ((0 : ℤ), (0 : ℤ)) ∈ T) (h1 : v1 ∈ T) :
    ∀ i j : ℤ, ∃ x, x ∈ dom T v1 v2 (i, j) ∧ x ∈ dom T v1 v2 (i + 1, j) := by
  intro i j
  refine ⟨vP v1 v2 (i, j) + v1, ?_, ?_⟩
  · show vP v1 v2 (i, j) + v1 - vP v1 v2 (i, j) ∈ T
    rw [add_sub_cancel_left]
    exact h1
  · show vP v1 v2 (i, j) + v1 - vP v1 v2 (i + 1, j) ∈ T
    rw [vP_shift1, sub_self]
    exact h0

/-- Neighbour overlaps in the vertical direction: `(1,0) ∈ T` and `v₂ + (1,0) ∈ T`. -/
theorem hA1v_of_witness {T : Set (ℤ × ℤ)} {v1 v2 : ℤ × ℤ} (h0 : ((1 : ℤ), (0 : ℤ)) ∈ T)
    (h1 : v2 + (1, 0) ∈ T) : ∀ i j : ℤ, ∃ x, x ∈ dom T v1 v2 (i, j) ∧ x ∈ dom T v1 v2 (i, j + 1) := by
  intro i j
  refine ⟨vP v1 v2 (i, j) + (v2 + (1, 0)), ?_, ?_⟩
  · show vP v1 v2 (i, j) + (v2 + (1, 0)) - vP v1 v2 (i, j) ∈ T
    rw [add_sub_cancel_left]
    exact h1
  · show vP v1 v2 (i, j) + (v2 + (1, 0)) - vP v1 v2 (i, j + 1) ∈ T
    have e : vP v1 v2 (i, j) + (v2 + (1, 0)) - (vP v1 v2 (i, j) + v2) = (1, 0) :=
      Prod.ext (by simp only [Prod.fst_sub, Prod.fst_add]; ring) (by simp only [Prod.snd_sub, Prod.snd_add]; ring)
    rw [vP_shift2, e]
    exact h0

/-- `hA1h` for the odd standard family. -/
theorem oddTile_hA1h (w : Word) : ∀ i j : ℤ,
    ∃ x, x ∈ dom (↑(oddTile w) : Set (ℤ × ℤ)) (texV1Odd (fracOdd w)) (texV2 (fracOdd w)) (i, j) ∧
      x ∈ dom (↑(oddTile w) : Set (ℤ × ℤ)) (texV1Odd (fracOdd w)) (texV2 (fracOdd w)) (i + 1, j) :=
  hA1h_of_witness (Finset.mem_coe.2 (zero_mem_oddTile w)) (Finset.mem_coe.2 (texV1_mem_oddTile w))

/-- `hA1v` for the odd standard family. -/
theorem oddTile_hA1v (w : Word) : ∀ i j : ℤ,
    ∃ x, x ∈ dom (↑(oddTile w) : Set (ℤ × ℤ)) (texV1Odd (fracOdd w)) (texV2 (fracOdd w)) (i, j) ∧
      x ∈ dom (↑(oddTile w) : Set (ℤ × ℤ)) (texV1Odd (fracOdd w)) (texV2 (fracOdd w)) (i, j + 1) :=
  hA1v_of_witness (Finset.mem_coe.2 (one_zero_mem_oddTile w)) (Finset.mem_coe.2 (vtwo_mem_oddTile w))

/-- `hA1h` for the even standard family. -/
theorem evenTile_hA1h (w : Word) : ∀ i j : ℤ,
    ∃ x, x ∈ dom (↑(evenTile w) : Set (ℤ × ℤ)) (texV1Even (fracEven w)) (texV2 (fracEven w)) (i, j) ∧
      x ∈ dom (↑(evenTile w) : Set (ℤ × ℤ)) (texV1Even (fracEven w)) (texV2 (fracEven w)) (i + 1, j) :=
  hA1h_of_witness (Finset.mem_coe.2 (zero_mem_evenTile w)) (Finset.mem_coe.2 (texV1_mem_evenTile w))

/-- `hA1v` for the even standard family. -/
theorem evenTile_hA1v (w : Word) : ∀ i j : ℤ,
    ∃ x, x ∈ dom (↑(evenTile w) : Set (ℤ × ℤ)) (texV1Even (fracEven w)) (texV2 (fracEven w)) (i, j) ∧
      x ∈ dom (↑(evenTile w) : Set (ℤ × ℤ)) (texV1Even (fracEven w)) (texV2 (fracEven w)) (i, j + 1) :=
  hA1v_of_witness (Finset.mem_coe.2 (one_zero_mem_evenTile w)) (Finset.mem_coe.2 (vtwo_mem_evenTile w))

end FLatticePaper.Tiles.CommonExtWitness
