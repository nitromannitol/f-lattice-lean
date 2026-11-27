import FLatticePaper.Tiles.ClosedPathSum
import FLatticePaper.Tiles.SiteHullOdd
import FLatticePaper.Tiles.SiteHullEven
import FLatticePaper.Tiles.MarksIn
import FLatticePaper.Tiles.TexVPositions
import FLatticePaper.Tiles.StringCorners

/-! # Condition (C): the contact points lie in the marks of both copies

The closed path of `ClosedPathSum` reads each mixed interface at a point which, relative to each of the two copies, is one of
the eight corner points of a standard tile with vectors `X = v_{n/d,1}`, `Y = v_{n/d,2}`:

* on the bottom string: `0`, `e₁` (first tile `T_{1/1}` at `0`), `X - e₂`, `X` (last tile `T_{0/1}` at `X - 1 - i`);
* on the top string, their images under the half-turn `z ↦ X + Y + 1 - i - z` of the tile: `X + Y + e₁ - e₂`, `X + Y - e₂`,
  `Y + e₁`, `Y + e₁ - e₂`.

`corner_marks_odd` and `corner_marks_even` show that the eight points lie in the marked strings `marksOdd`, `marksEven` of every
standard tile (and hence in the tile, `MarksIn.marksOdd_sub`). The bottom points are read off the first and last origins of the
forward horizontal string (`clauseB_forward_last`), the top points through the half-turn centre (`centre_odd`, `centre_even`). -/

namespace FLatticePaper.Tiles.ClosedPathContacts

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.ClosedPathSum FLatticePaper.Tiles.StandardClause

/-- The letters of the origins of a string are the letters of the string. -/
theorem origins_letters (vert rev : Bool) : ∀ (o : Option Letter) (pos : ℤ × ℤ) (ls : List Letter),
    (origins vert rev o pos ls).map (fun e => e.2.1) = ls
  | _, _, [] => rfl
  | none, pos, l :: ls => by
    simp only [origins, List.map_cons]
    rw [origins_letters vert rev (some l) pos ls]
  | some pr, pos, l :: ls => by
    simp only [origins, List.map_cons]
    rw [origins_letters vert rev (some l) _ ls]

/-- The four bottom corner points of a forward horizontal string from `q` to `p` whose last origin is `c`. -/
theorem bottom_corner_sites (wh : List Letter) (c : ℤ × ℤ) (hhead : wh.head? = some .q)
    (hlast : wh.getLast? = some .p) (hc : lastOrigin false false wh = some c) :
    (0, 0) ∈ stringSites false false wh ∧ (1, 0) ∈ stringSites false false wh ∧
      (c.1 + 1, c.2) ∈ stringSites false false wh ∧ (c.1 + 1, c.2 + 1) ∈ stringSites false false wh := by
  have hmem : ∀ e ∈ origins false false none (startPos false false) wh, ∀ b ∈ baseSites e.2.1 e.2.2,
      (e.1.1 + b.1, e.1.2 + b.2) ∈ stringSites false false wh := by
    intro e he b hb
    unfold stringSites
    exact List.mem_flatMap.2 ⟨e, he, List.mem_map.2 ⟨b, hb, rfl⟩⟩
  obtain ⟨t, rfl⟩ : ∃ t, wh = Letter.q :: t := by
    cases wh with
    | nil => simp at hhead
    | cons a t =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      exact ⟨t, by rw [hhead]⟩
  have hfirst : ((0, 0), Letter.q, false) ∈ origins false false none (startPos false false) (Letter.q :: t) := by
    simp [origins, startPos]
  obtain ⟨e, he⟩ : ∃ e, (origins false false none (startPos false false) (Letter.q :: t)).getLast? = some e := by
    cases h : (origins false false none (startPos false false) (Letter.q :: t)).getLast? with
    | none =>
      rw [List.getLast?_eq_none_iff] at h
      rw [h] at hfirst
      simp at hfirst
    | some e => exact ⟨e, rfl⟩
  have he1 : e.1 = c := by
    unfold lastOrigin at hc
    rw [he] at hc
    simpa using hc
  have he2 : e.2.1 = Letter.p := by
    have h := congrArg List.getLast? (origins_letters false false none (startPos false false) (Letter.q :: t))
    rw [List.getLast?_map, he, hlast] at h
    simpa using h
  have hemem : e ∈ origins false false none (startPos false false) (Letter.q :: t) :=
    List.mem_of_getLast? he
  have hbp : ∀ f : Bool, (1, 0) ∈ baseSites Letter.p f ∧ (1, 1) ∈ baseSites Letter.p f := by
    intro f
    cases f <;> decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := hmem _ hfirst (0, 0) (by decide)
    simpa using this
  · have := hmem _ hfirst (1, 0) (by decide)
    simpa using this
  · have hb : (1, 0) ∈ baseSites e.2.1 e.2.2 := by rw [he2]; exact (hbp _).1
    have := hmem e hemem (1, 0) hb
    rw [he1] at this
    simpa using this
  · have hb : (1, 1) ∈ baseSites e.2.1 e.2.2 := by rw [he2]; exact (hbp _).2
    have := hmem e hemem (1, 1) hb
    rw [he1] at this
    simpa using this

/-- **The eight corner points of the odd standard tile lie in its marks**, with `X = v_{n/d,1}`, `Y = v_{n/d,2}` of the odd
fraction of `u`. -/
theorem corner_marks_odd (u : Word) :
    (0 : ℤ × ℤ) ∈ marksOdd u ∧ e₁ ∈ marksOdd u ∧
      texV1Odd (fracOdd u) - e₂ ∈ marksOdd u ∧ texV1Odd (fracOdd u) ∈ marksOdd u ∧
      texV2 (fracOdd u) + e₁ ∈ marksOdd u ∧ texV2 (fracOdd u) + e₁ - e₂ ∈ marksOdd u ∧
      texV1Odd (fracOdd u) + texV2 (fracOdd u) + e₁ - e₂ ∈ marksOdd u ∧
      texV1Odd (fracOdd u) + texV2 (fracOdd u) - e₂ ∈ marksOdd u := by
  have hc := StringCorners.clauseB_forward_last u
  rw [TexVPositions.almostV1_oddBottom_eq] at hc
  obtain ⟨hh, hl⟩ := hWordOf_head_last u false
  obtain ⟨b0, b1, bX', bX⟩ := bottom_corner_sites _ _ hh hl hc
  have hcu : curO u = fracOdd u := rfl
  have refl : ∀ z r : ℤ × ℤ, r ∈ stringSites false false (hWordOf u false) →
      ((curO u).den + (curO u).num + 1 - z.1, 3 * (curO u).num + (curO u).den - 1 - z.2) = r → z ∈ marksOdd u := by
    intro z r hr hz
    apply SiteHullOdd.mem_marksOdd_of_sh_refl
    rw [hz]
    exact hr
  refine ⟨SiteHullOdd.mem_marksOdd_of_sh u _ b0, SiteHullOdd.mem_marksOdd_of_sh u _ b1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply SiteHullOdd.mem_marksOdd_of_sh
    convert bX' using 1
    ext <;> simp
  · apply SiteHullOdd.mem_marksOdd_of_sh
    convert bX using 1
    ext <;> simp
  · refine refl _ _ bX' ?_
    rw [hcu]
    ext <;> simp [texV1Odd, texV2] <;> ring
  · refine refl _ _ bX ?_
    rw [hcu]
    ext <;> simp [texV1Odd, texV2] <;> ring
  · refine refl _ _ b0 ?_
    rw [hcu]
    ext <;> simp [texV1Odd, texV2] <;> ring
  · refine refl _ _ b1 ?_
    rw [hcu]
    ext <;> simp [texV1Odd, texV2] <;> ring

/-- **The eight corner points of the even standard tile lie in its marks**, with `X = v_{n/d,1}`, `Y = v_{n/d,2}` of the even
fraction of `u`. -/
theorem corner_marks_even (u : Word) :
    (0 : ℤ × ℤ) ∈ marksEven u ∧ e₁ ∈ marksEven u ∧
      texV1Even (fracEven u) - e₂ ∈ marksEven u ∧ texV1Even (fracEven u) ∈ marksEven u ∧
      texV2 (fracEven u) + e₁ ∈ marksEven u ∧ texV2 (fracEven u) + e₁ - e₂ ∈ marksEven u ∧
      texV1Even (fracEven u) + texV2 (fracEven u) + e₁ - e₂ ∈ marksEven u ∧
      texV1Even (fracEven u) + texV2 (fracEven u) - e₂ ∈ marksEven u := by
  have hc := StringCorners.clauseB_forward_last_even u
  rw [TexVPositions.almostV1_evenBottom_eq] at hc
  obtain ⟨hh, hl⟩ := hWordOf_head_last u true
  obtain ⟨b0, b1, bX', bX⟩ := bottom_corner_sites _ _ hh hl hc
  have hcu : curE u = fracEven u := rfl
  have refl : ∀ z r : ℤ × ℤ, r ∈ stringSites false false (hWordOf u true) →
      ((curE u).num + 1 - z.1, 2 * (curE u).num + (curE u).den - 1 - z.2) = r → z ∈ marksEven u := by
    intro z r hr hz
    apply SiteHullEven.mem_marksEven_of_sh_refl
    rw [hz]
    exact hr
  refine ⟨SiteHullEven.mem_marksEven_of_sh u _ b0, SiteHullEven.mem_marksEven_of_sh u _ b1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply SiteHullEven.mem_marksEven_of_sh
    convert bX' using 1
    ext <;> simp
  · apply SiteHullEven.mem_marksEven_of_sh
    convert bX using 1
    ext <;> simp
  · refine refl _ _ bX' ?_
    rw [hcu]
    ext <;> (simp [texV1Even, texV2]; try ring)
  · refine refl _ _ bX ?_
    rw [hcu]
    ext <;> (simp [texV1Even, texV2]; try ring)
  · refine refl _ _ b0 ?_
    rw [hcu]
    ext <;> (simp [texV1Even, texV2]; try ring)
  · refine refl _ _ b1 ?_
    rw [hcu]
    ext <;> (simp [texV1Even, texV2]; try ring)

end FLatticePaper.Tiles.ClosedPathContacts
