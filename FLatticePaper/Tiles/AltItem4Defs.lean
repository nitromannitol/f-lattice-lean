import FLatticePaper.Tiles.AltBounds
import FLatticePaper.Tiles.PointNonNeighbour

/-! # Item (4) of `lemma:alternate_tile_properties`: the statement and the tools of the pair analysis

Surgical edition 3243bef, `lemma:alternate_tile_properties` (4), restated at 3243bef: for a tile `T' = T̂(n/d) + v`, `v ≠ 0`,
of the surrounding of `T̂(n/d)` with respect to `(v_{n/d,1}, v_{n/d,2})`, every `x ∈ T̂(n/d) ∩ T'` lies in a stacked zero-one
boundary string of the surrounding, or the two translates overlap completely on a subtile `T` with `x ∈ T`.

The proof of the text decomposes the intersection into the pairs of pieces of the two translates. Here:
* `Concl copies v x`: either `x` lies in a standard copy `J` of the decomposition of `T̂` such that `J - v` is also one of its
  copies (so `J` is a subtile of both `T̂` and `T̂ + v`: the complete overlap), or `StackedAt x`;
* `StackedAt x`: `x` lies in two lattice-adjacent translates `E + a`, `E + a + e` (`e = ±v₁, ±v₂` of `E`) of a standard tile
  `E` (the enclosure form; by (c) of `lemma:standard_tile_properties` the common points of the two translates lie on the
  stacked zero-one strings of the surrounding of `E + a`).
The tools below give each kind of certificate of a pair: a copy of a parent inside a translate of a standard tile, two
copies in translates at a non-neighbour lattice vector (no common point, `PointNonNeighbour`), the midpoint of two copies of
the same tile (the closed form is convex along a vector of even coordinate sum), and the boxes of the parents. -/

namespace FLatticePaper.Tiles.AltItem4

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (Tile shift mem_shift stateAt IsBase oddTile evenTile oddChildB evenChildB)
open FLatticePaper.Tiles.SurgicalAltTiles (altOddTile altEvenTile)
open FLatticePaper.Tiles.AltPieces
open FLatticePaper.Tiles.SiteInduction (InH)

/-! ### The statement -/

/-- The fraction of the standard tile of `u` with parity `par` (`false`: odd, `true`: even). -/
def fracOf (u : Word) (par : Bool) : Fraction := if par then SiteInduction.curE u else SiteInduction.curO u

/-- The first lattice vector of the standard tile of `u` with parity `par`. -/
def latV1 (u : Word) (par : Bool) : Site := if par then texV1Even (fracOf u par) else texV1Odd (fracOf u par)

/-- The lattice vector `i v₁ + j v₂` of the standard tile of `u` with parity `par`. -/
def latV (u : Word) (par : Bool) (i j : ℤ) : Site :=
  (i * (latV1 u par).1 + j * (texV2 (fracOf u par)).1, i * (latV1 u par).2 + j * (texV2 (fracOf u par)).2)

/-- The four neighbour indices `±(1, 0)`, `±(0, 1)`. -/
def Nbr (i j : ℤ) : Prop := (i = 1 ∧ j = 0) ∨ (i = -1 ∧ j = 0) ∨ (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = -1)

/-- `x` lies in two lattice-adjacent translates of a standard tile. -/
def StackedAt (x : Site) : Prop :=
  ∃ (u : Word) (par : Bool) (a : Site) (i j : ℤ), Nbr i j ∧
    x ∈ shift (SiteStrings.tileOf u par) a ∧ x ∈ shift (SiteStrings.tileOf u par) (a + latV u par i j)

/-- The standard copies of the even alternate child `T̂(q₀)`. -/
def evenCopies (w : Word) : List Tile :=
  (evenPOffs (phase w == 1) (parentsAt w).odd (parentsAt w).even).map (shift (stateAt w).tOdd) ++
    (evenQOffs (phase w == 1) (parentsAt w).odd (parentsAt w).even).map (shift (stateAt w).tEven)

/-- The standard copies of the odd alternate child `T̂(p₀)`. -/
def oddCopies (w : Word) : List Tile :=
  (oddPOffs (phase w == 1) (parentsAt w).odd (parentsAt w).even).map (shift (stateAt w).tOdd) ++
    (oddQOffs (phase w == 1) (parentsAt w).odd (parentsAt w).even).map (shift (stateAt w).tEven)

/-- The conclusion of item (4) at a point `x` of `T̂ ∩ (T̂ + v)`. -/
def Concl (copies : List Tile) (v x : Site) : Prop :=
  (∃ J ∈ copies, x ∈ J ∧ shift J (-v) ∈ copies) ∨ StackedAt x

/-! ### Shift arithmetic -/

theorem mem_shift_shift_iff (T : Tile) (a b z : Site) : z ∈ shift T (a + b) ↔ z - b ∈ shift T a := by
  rw [mem_shift, mem_shift, sub_sub, add_comm b a]

theorem shift_shift' (T : Tile) (a b : Site) : shift (shift T a) b = shift T (a + b) := Standard.shift_shift T a b

/-- A copy `T + e` inside `Y` gives `T + a ⊆ Y + b` whenever `a - b = e`. -/
theorem mem_of_copy {T Y : Tile} {e : Site} (hc : ∀ y, y ∈ shift T e → y ∈ Y) {z a b : Site} (hz : z ∈ shift T a)
    (he : a - b = e) : z ∈ shift Y b := by
  rw [mem_shift]
  apply hc
  rw [mem_shift] at hz ⊢
  convert hz using 1
  rw [← he]
  abel

/-! ### The standard children of `w`, `w 1`, `w 3` through their copies -/

theorem oddTile_eq {w : Word} (hw : ¬ IsBase w) :
    oddTile w = oddChildB (phase w == 1) (stateAt w).tOdd (stateAt w).tEven (parentsAt w).odd (parentsAt w).even :=
  (HorizontalStep.tiles_nonbase w hw).1

theorem evenTile_eq {w : Word} (hw : ¬ IsBase w) :
    evenTile w = evenChildB (phase w == 1) (stateAt w).tOdd (stateAt w).tEven (parentsAt w).odd (parentsAt w).even :=
  (HorizontalStep.tiles_nonbase w hw).2

theorem not_base_snoc_one (w : Word) : ¬ IsBase (w ++ [Digit.one]) := by
  rintro (h | h | h)
  · simp at h
  · exact absurd (h Digit.one (by simp)) (by decide)
  · exact absurd (h Digit.one (by simp)) (by decide)

theorem not_base_snoc_three {w : Word} (hw : ¬ IsBase w) : ¬ IsBase (w ++ [Digit.three]) := by
  rintro (h | h | h)
  · simp at h
  · exact hw (Or.inr (Or.inl fun x hx => h x (by simp [hx])))
  · exact absurd (h Digit.three (by simp)) (by decide)

theorem oddTile_one (w : Word) :
    oddTile (w ++ [Digit.one]) = oddChildB (phase (w ++ [Digit.one]) == 1) (oddTile w) (evenTile w)
      (SiteInduction.curO w) (SiteInduction.curE w) := by
  rw [oddTile_eq (not_base_snoc_one w), (HorizontalStep.reg_one w).1, (HorizontalStep.reg_one w).2,
    (HorizontalStep.par_one w).1, (HorizontalStep.par_one w).2]

theorem evenTile_one (w : Word) :
    evenTile (w ++ [Digit.one]) = evenChildB (phase (w ++ [Digit.one]) == 1) (oddTile w) (evenTile w)
      (SiteInduction.curO w) (SiteInduction.curE w) := by
  rw [evenTile_eq (not_base_snoc_one w), (HorizontalStep.reg_one w).1, (HorizontalStep.reg_one w).2,
    (HorizontalStep.par_one w).1, (HorizontalStep.par_one w).2]

theorem oddTile_three {w : Word} (hw : ¬ IsBase w) :
    oddTile (w ++ [Digit.three]) = oddChildB (phase (w ++ [Digit.three]) == 1) (stateAt w).tOdd (evenTile w)
      (parentsAt w).odd (SiteInduction.curE w) := by
  rw [oddTile_eq (not_base_snoc_three hw), (HorizontalStep.reg_three w).1, (HorizontalStep.reg_three w).2,
    (HorizontalStep.par_three w).1, (HorizontalStep.par_three w).2]

theorem phase_snoc_one (w : Word) : (phase (w ++ [Digit.one]) == 1) = !(phase w == 1) := by
  unfold phase
  rw [count_snoc_one]
  rcases Nat.mod_two_eq_zero_or_one (w.count Digit.one) with h | h <;> simp [Nat.add_mod, h]

theorem phase_snoc_three (w : Word) : (phase (w ++ [Digit.three]) == 1) = (phase w == 1) := by
  unfold phase
  simp

/-! ### Packing: copies in translates at a non-neighbour lattice vector -/

/-- Two translates of the odd standard tile of `u` at a lattice vector `i v₁ + j v₂` that is neither `0` nor a neighbour vector
have no common point. -/
theorem odd_far (u : Word) (i j : ℤ) (hf : ¬ (i = 0 ∧ j = 0) ∧ ¬ Nbr i j) (a z : Site)
    (h1 : z ∈ shift (oddTile u) a) (h2 : z ∈ shift (oddTile u) (a + latV u false i j)) : False := by
  rw [mem_shift] at h1 h2
  simp only [latV, latV1, fracOf, if_false, Bool.false_eq_true] at h2
  by_cases hns : 2 ≤ |i| ∨ 2 ≤ |j|
  · apply PointNonNeighbour.oddTile_nonneighbour u i j hns (z - a) h1
    convert h2 using 1
    ext <;> simp [StandardClause.fracOdd] <;> ring
  · push Not at hns
    have hi := abs_lt.1 hns.1
    have hj := abs_lt.1 hns.2
    obtain ⟨d1, d2, d3, d4⟩ := PointNonNeighbour.oddTile_diagonal_disjoint u
    simp only [Nbr, not_or, not_and] at hf
    obtain ⟨h0, hn1, hn2, hn3, hn4⟩ := hf
    have hij : (i = 1 ∨ i = -1) ∧ (j = 1 ∨ j = -1) := by omega
    rcases hij with ⟨rfl | rfl, rfl | rfl⟩
    · exact d1 (z - a) h1 (by convert h2 using 1; ext <;> simp [StandardClause.fracOdd] <;> ring)
    · exact d3 (z - a) h1 (by convert h2 using 1; ext <;> simp [StandardClause.fracOdd] <;> ring)
    · exact d4 (z - a) h1 (by convert h2 using 1; ext <;> simp [StandardClause.fracOdd] <;> ring)
    · exact d2 (z - a) h1 (by convert h2 using 1; ext <;> simp [StandardClause.fracOdd] <;> ring)

/-- The even analogue of `odd_far`. -/
theorem even_far (u : Word) (i j : ℤ) (hf : ¬ (i = 0 ∧ j = 0) ∧ ¬ Nbr i j) (a z : Site)
    (h1 : z ∈ shift (evenTile u) a) (h2 : z ∈ shift (evenTile u) (a + latV u true i j)) : False := by
  rw [mem_shift] at h1 h2
  simp only [latV, latV1, fracOf, if_true] at h2
  by_cases hns : 2 ≤ |i| ∨ 2 ≤ |j|
  · apply PointNonNeighbour.evenTile_nonneighbour u i j hns (z - a) h1
    convert h2 using 1
    ext <;> simp [StandardClause.fracEven] <;> ring
  · push Not at hns
    have hi := abs_lt.1 hns.1
    have hj := abs_lt.1 hns.2
    obtain ⟨d1, d2, d3, d4⟩ := PointNonNeighbour.evenTile_diagonal_disjoint u
    simp only [Nbr, not_or, not_and] at hf
    obtain ⟨h0, hn1, hn2, hn3, hn4⟩ := hf
    have hij : (i = 1 ∨ i = -1) ∧ (j = 1 ∨ j = -1) := by omega
    rcases hij with ⟨rfl | rfl, rfl | rfl⟩
    · exact d1 (z - a) h1 (by convert h2 using 1; ext <;> simp [StandardClause.fracEven] <;> ring)
    · exact d3 (z - a) h1 (by convert h2 using 1; ext <;> simp [StandardClause.fracEven] <;> ring)
    · exact d4 (z - a) h1 (by convert h2 using 1; ext <;> simp [StandardClause.fracEven] <;> ring)
    · exact d2 (z - a) h1 (by convert h2 using 1; ext <;> simp [StandardClause.fracEven] <;> ring)

/-! ### The midpoint of two copies of a parent -/

/-- The closed form is convex along a vector `D` of even coordinate sum: the three points `y - D`, `y`, `y + D` are of the
same kind, and the four bounds of `H_f` average. -/
theorem inH_mid (f : Fraction) (y D : Site) (hD : (D.1 + D.2) % 2 = 0) (h1 : InH f (y + D)) (h2 : InH f (y - D)) :
    InH f y := by
  have e1 : ((y + D).1 + (y + D).2) % 2 = (y.1 + y.2) % 2 := by simp only [Prod.fst_add, Prod.snd_add]; omega
  have e2 : ((y - D).1 + (y - D).2) % 2 = (y.1 + y.2) % 2 := by simp only [Prod.fst_sub, Prod.snd_sub]; omega
  obtain ⟨a1, a2, a3, a4⟩ := h1
  obtain ⟨b1, b2, b3, b4⟩ := h2
  rw [e1] at a1 a2 a3 a4
  rw [e2] at b1 b2 b3 b4
  simp only [SiteInduction.tCo, SiteInduction.sCo, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
    at a1 a2 a3 a4 b1 b2 b3 b4
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [SiteInduction.tCo, SiteInduction.sCo] <;> nlinarith

/-! ### The boxes of the two parents at a point of two copies -/

theorem boxes_pp (p : Fraction) (hp : 0 < p.num ∧ p.num < p.den) (hmp : SiteInduction.muOf p = 2) (a b z : Site)
    (h1 : InH p (z - a)) (h2 : InH p (z - b)) :
    p.num - p.den ≤ z.1 - a.1 ∧ z.1 - a.1 ≤ 2 * p.den + 1 ∧
      -1 ≤ z.2 - a.2 ∧ z.2 - a.2 ≤ 2 * p.num + p.num + p.den ∧
      -1 ≤ z.1 - a.1 + (z.2 - a.2) ∧ z.1 - a.1 + (z.2 - a.2) ≤ 2 * (p.den + p.num) + 2 * p.num + 1 ∧
      -2 * p.den ≤ z.1 - a.1 - (z.2 - a.2) ∧ z.1 - a.1 - (z.2 - a.2) ≤ 2 * (p.den - p.num) + 2 ∧
    p.num - p.den ≤ z.1 - b.1 ∧ z.1 - b.1 ≤ 2 * p.den + 1 ∧
      -1 ≤ z.2 - b.2 ∧ z.2 - b.2 ≤ 2 * p.num + p.num + p.den ∧
      -1 ≤ z.1 - b.1 + (z.2 - b.2) ∧ z.1 - b.1 + (z.2 - b.2) ≤ 2 * (p.den + p.num) + 2 * p.num + 1 ∧
      -2 * p.den ≤ z.1 - b.1 - (z.2 - b.2) ∧ z.1 - b.1 - (z.2 - b.2) ≤ 2 * (p.den - p.num) + 2 := by
  have b1 := inH_box p hp.1 hp.2 _ h1
  have b2 := inH_box p hp.1 hp.2 _ h2
  rw [hmp] at b1 b2
  simp only [Prod.fst_sub, Prod.snd_sub] at b1 b2
  exact ⟨b1.1, b1.2.1, b1.2.2.1, b1.2.2.2.1, b1.2.2.2.2.1, b1.2.2.2.2.2.1, b1.2.2.2.2.2.2.1, b1.2.2.2.2.2.2.2,
    b2.1, b2.2.1, b2.2.2.1, b2.2.2.2.1, b2.2.2.2.2.1, b2.2.2.2.2.2.1, b2.2.2.2.2.2.2.1, b2.2.2.2.2.2.2.2⟩

theorem boxes_qq (q : Fraction) (hq : 0 < q.num ∧ q.num < q.den) (hmq : SiteInduction.muOf q = 1) (a b z : Site)
    (h1 : InH q (z - a)) (h2 : InH q (z - b)) :
    q.num - q.den ≤ z.1 - a.1 ∧ z.1 - a.1 ≤ q.den + 1 ∧
      -1 ≤ z.2 - a.2 ∧ z.2 - a.2 ≤ q.num + q.num + q.den ∧
      -1 ≤ z.1 - a.1 + (z.2 - a.2) ∧ z.1 - a.1 + (z.2 - a.2) ≤ (q.den + q.num) + 2 * q.num + 1 ∧
      -2 * q.den ≤ z.1 - a.1 - (z.2 - a.2) ∧ z.1 - a.1 - (z.2 - a.2) ≤ (q.den - q.num) + 2 ∧
    q.num - q.den ≤ z.1 - b.1 ∧ z.1 - b.1 ≤ q.den + 1 ∧
      -1 ≤ z.2 - b.2 ∧ z.2 - b.2 ≤ q.num + q.num + q.den ∧
      -1 ≤ z.1 - b.1 + (z.2 - b.2) ∧ z.1 - b.1 + (z.2 - b.2) ≤ (q.den + q.num) + 2 * q.num + 1 ∧
      -2 * q.den ≤ z.1 - b.1 - (z.2 - b.2) ∧ z.1 - b.1 - (z.2 - b.2) ≤ (q.den - q.num) + 2 := by
  have b1 := inH_box q hq.1 hq.2 _ h1
  have b2 := inH_box q hq.1 hq.2 _ h2
  rw [hmq] at b1 b2
  simp only [Prod.fst_sub, Prod.snd_sub, one_mul] at b1 b2
  exact ⟨b1.1, b1.2.1, b1.2.2.1, b1.2.2.2.1, b1.2.2.2.2.1, b1.2.2.2.2.2.1, b1.2.2.2.2.2.2.1, b1.2.2.2.2.2.2.2,
    b2.1, b2.2.1, b2.2.2.1, b2.2.2.2.1, b2.2.2.2.2.1, b2.2.2.2.2.2.1, b2.2.2.2.2.2.2.1, b2.2.2.2.2.2.2.2⟩

end FLatticePaper.Tiles.AltItem4
