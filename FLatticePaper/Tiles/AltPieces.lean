import FLatticePaper.Tiles.AltRotStep
import FLatticePaper.Tiles.H3Data
import FLatticePaper.Tiles.RegisterTiles

/-! # The standard subtiles of the alternate tiles as placed copies (`def:alternate_tiles`, `eq:alt_decomp`)

For a non-base word `w` with parents `p₁ = p`, `q₁ = q` (`parentsAt w`) and `o = (phase w == 1)` (`W₁` odd), the alternate
odd child `T̂(p₀)` is the union of four copies of `T(p₁)` (the two copies of each doubled tile `T^{ds}(p₁)^±`), two copies of
`T(q₁)` and the alternate parent piece; the alternate even child `T̂(q₀)` is the union of two copies of `T(p₁)`, four copies of
`T(q₁)` and the alternate parent piece. The offsets of the copies are listed here (`oddPOffs`, `oddQOffs`, `evenPOffs`,
`evenQOffs`), in the order of `eq:alt_offsets_w1_odd` and `eq:alt_offsets_w1_even` with the second copy of a doubled tile
after the first.

The copies of `T(p₁)` and `T(q₁)` are copies of the standard tiles of the source words of the registers, which are the closed
sets `H_X` of the parents (`SubOddCopy.mem_oddTile_iff`, `SubEvenCopy.mem_evenTile_iff`): a point `z` lies in the copy at `a`
exactly when `InH p (z - a)` (`mem_pCopy_iff`, `mem_qCopy_iff`). The frame is that of `SurgicalAltTiles`: `c(T̂) = 0` is the
lower-left vertex of the piece at offset `0`. -/

namespace FLatticePaper.Tiles.AltPieces

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (Tile shift rot mem_shift shift_shift shift_union stateAt IsBase swapW)
open FLatticePaper.Tiles.SurgicalDict (doubled altShifts AltP0Piece AltQ0Piece)
open FLatticePaper.Tiles.SurgicalAlt (coeffOff altP0Coeff altQ0Coeff altQ1Coeff altP1Coeff altTypeOf)
open FLatticePaper.Tiles.SurgicalAltTiles
open FLatticePaper.Tiles.AltRotStep
open FLatticePaper.Tiles.SiteInduction (InH)

/-! ### The offsets of the copies -/

/-- The offsets of the four copies of `T(p₁)` in `T̂(p₀)`: `T(p₁)^{+,1}, T(p₁)^{+,2}, T(p₁)^{-,1}, T(p₁)^{-,2}`. -/
def oddPOffs (o : Bool) (p q : Fraction) : List Site :=
  [offP0 o p q .dsP1Plus, shP o p q + offP0 o p q .dsP1Plus, offP0 o p q .dsP1Minus, shP o p q + offP0 o p q .dsP1Minus]

/-- The offsets of the two copies of `T(q₁)` in `T̂(p₀)`: `T(q₁)^+, T(q₁)^-`. -/
def oddQOffs (o : Bool) (p q : Fraction) : List Site :=
  [offP0 o p q .q1Plus, offP0 o p q .q1Minus]

/-- The offsets of the two copies of `T(p₁)` in `T̂(q₀)`: `T(p₁)^+, T(p₁)^-`. -/
def evenPOffs (o : Bool) (p q : Fraction) : List Site :=
  [offQ0 o p q .p1Plus, offQ0 o p q .p1Minus]

/-- The offsets of the four copies of `T(q₁)` in `T̂(q₀)`: `T(q₁)^{+,1}, T(q₁)^{+,2}, T(q₁)^{-,1}, T(q₁)^{-,2}`. -/
def evenQOffs (o : Bool) (p q : Fraction) : List Site :=
  [offQ0 o p q .dsQ1Plus, shQ o p q + offQ0 o p q .dsQ1Plus, offQ0 o p q .dsQ1Minus, shQ o p q + offQ0 o p q .dsQ1Minus]

theorem mem_shift_doubled (T : Tile) (S c z : Site) :
    z ∈ shift (doubled T S) c ↔ z ∈ shift T c ∨ z ∈ shift T (S + c) := by
  unfold doubled
  rw [shift_union, shift_shift, Finset.mem_union]

/-- The standard pieces of `T̂(p₀)` are the copies of `T₁ = T(p₁)` at `oddPOffs` and of `T₂ = T(q₁)` at `oddQOffs`. -/
theorem mem_oddStd_iff (o : Bool) (T1 T2 : Tile) (p q : Fraction) (z : Site) :
    z ∈ oddStd o T1 T2 p q ↔ (∃ a ∈ oddPOffs o p q, z ∈ shift T1 a) ∨ (∃ b ∈ oddQOffs o p q, z ∈ shift T2 b) := by
  unfold oddStd oddPOffs oddQOffs
  simp only [Finset.mem_union, mem_shift_doubled, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
    exists_eq_left]
  tauto

/-- The standard pieces of `T̂(q₀)` are the copies of `T₁ = T(p₁)` at `evenPOffs` and of `T₂ = T(q₁)` at `evenQOffs`. -/
theorem mem_evenStd_iff (o : Bool) (T1 T2 : Tile) (p q : Fraction) (z : Site) :
    z ∈ evenStd o T1 T2 p q ↔ (∃ a ∈ evenPOffs o p q, z ∈ shift T1 a) ∨ (∃ b ∈ evenQOffs o p q, z ∈ shift T2 b) := by
  unfold evenStd evenPOffs evenQOffs
  simp only [Finset.mem_union, mem_shift_doubled, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
    exists_eq_left]
  tauto

/-! ### The alternate children of a non-base word -/

/-- A non-base word is a word followed by a letter. -/
theorem exists_snoc_of_not_base {w : Word} (hw : ¬ IsBase w) : ∃ u x, w = u ++ [x] := by
  rcases List.eq_nil_or_concat w with h | ⟨u, x, h⟩
  · exact absurd (h ▸ Or.inl rfl) hw
  · exact ⟨u, x, by rw [h, List.concat_eq_append]⟩

/-- The alternate odd child of a non-base word: the standard pieces and the alternate parent piece of its type. -/
theorem altOddTile_eq (base : Word → Tile × Tile) {w : Word} (hw : ¬ IsBase w) :
    ∃ x : Digit, altTypeOf w = some x ∧
      altOddTile base w = oddStd (phase w == 1) (stateAt w).tOdd (stateAt w).tEven (parentsAt w).odd
          (parentsAt w).even ∪ altQ1Part (phase w == 1) x (altRegs base w).2 (parentsAt w).odd (parentsAt w).even := by
  obtain ⟨u, x, rfl⟩ := exists_snoc_of_not_base hw
  exact ⟨x, altTypeOf_snoc u x, by rw [altOddTile_of_not_base base hw, altOddPieces_snoc]⟩

/-- The alternate even child of a non-base word. -/
theorem altEvenTile_eq (base : Word → Tile × Tile) {w : Word} (hw : ¬ IsBase w) :
    ∃ x : Digit, altTypeOf w = some x ∧
      altEvenTile base w = evenStd (phase w == 1) (stateAt w).tOdd (stateAt w).tEven (parentsAt w).odd
          (parentsAt w).even ∪ altP1Part (phase w == 1) x (altRegs base w).1 (parentsAt w).odd (parentsAt w).even := by
  obtain ⟨u, x, rfl⟩ := exists_snoc_of_not_base hw
  exact ⟨x, altTypeOf_snoc u x, by rw [altEvenTile_of_not_base base hw, altEvenPieces_snoc]⟩

/-! ### The copies through the closed form of the parents -/

/-- A point lies in a copy of `T(p₁)` at `a` exactly when `z - a` lies in `H_{p₁}`. -/
theorem mem_pCopy_iff {w : Word} (hw : ¬ IsBase w) (a z : Site) :
    z ∈ shift (stateAt w).tOdd a ↔ InH (parentsAt w).odd (z - a) := by
  have h := H3Data.nonbase_one_two hw
  rw [mem_shift, RegisterTiles.tOdd_eq_oddTile w h, SubOddCopy.mem_oddTile_iff, H3Data.src_odd_frac w h]

/-- A point lies in a copy of `T(q₁)` at `b` exactly when `z - b` lies in `H_{q₁}`. -/
theorem mem_qCopy_iff {w : Word} (hw : ¬ IsBase w) (b z : Site) :
    z ∈ shift (stateAt w).tEven b ↔ InH (parentsAt w).even (z - b) := by
  have h := H3Data.nonbase_one_three hw
  rw [mem_shift, RegisterTiles.tEven_eq_evenTile w h, SubEvenCopy.mem_evenTile_iff, H3Data.src_even_frac w h]

/-! ### The parents of a non-base word -/

/-- The parents of a non-base word lie in `(0, 1)`, have the parities odd and even, and determinant `±1` with the sign of the
orientation. -/
theorem parents_facts {w : Word} (hw : ¬ IsBase w) :
    0 < (parentsAt w).odd.num ∧ (parentsAt w).odd.num < (parentsAt w).odd.den ∧
      0 < (parentsAt w).even.num ∧ (parentsAt w).even.num < (parentsAt w).even.den ∧
      ((parentsAt w).odd.num + (parentsAt w).odd.den) % 2 = 1 ∧
      ((parentsAt w).even.num + (parentsAt w).even.den) % 2 = 0 ∧
      (parentsAt w).odd.num * (parentsAt w).even.den - (parentsAt w).even.num * (parentsAt w).odd.den =
        (if phase w = 1 then 1 else -1) := by
  have h1 := H3Data.odd_parent_interior w (H3Data.nonbase_one_two hw)
  have h2 := H3Data.even_parent_interior w (H3Data.nonbase_one_three hw)
  have hv := parentsAt_valid w
  exact ⟨h1.1, h1.2, h2.1, h2.2, hv.odd_parity, hv.even_parity, H3Data.eps_det w⟩

/-! ### A box around the closed set `H_f`

From the four bounds of `H_f` (`SiteInduction.InH`) and the identities `T x = C t + D s`, `T y = N s - L t`,
`T (x + y) = -2N t + L s`, `T (x - y) = 2D t + C s` (`T = D² + 2DN - N²`, `C = D - N`, `L = D + N`, `t = N x - D y`,
`s = L x + C y`), the coordinates `x`, `y`, `x + y`, `x - y` of a point of `H_f` lie in intervals that exceed the extremes over
the tile by at most one at each end (the extremes are `1 + N - D ≤ x ≤ μD`, `0 ≤ y ≤ μN + L - 1`, `0 ≤ x + y ≤ μL + 2N`,
`1 - 2D ≤ x - y ≤ μC + 1`). These are the coordinate bounds that separate the pairs of copies of the alternate decomposition
that do not meet. -/

/-- The two kinds of sites: at an even site `a = min (2N) C`, `l = 0`; at an odd site `a = N`, `l = min C (3N - D)`. -/
def SiteConsts (N D a l : ℤ) : Prop :=
  (l = 0 ∧ (a = 2 * N ∨ a = D - N)) ∨ (a = N ∧ (l = D - N ∨ l = 3 * N - D))

theorem kx1_fact (N D μ a l : ℤ) (hN : 1 ≤ N) (hND : N < D) (hal : SiteConsts N D a l) :
    (D - N) * (D + N - a) + D * (μ * (D ^ 2 + 2 * D * N - N ^ 2) + 2 * N - l) < (D ^ 2 + 2 * D * N - N ^ 2) * (μ * D + 2) := by
  have pDN : 0 < (D - N) * N := mul_pos (by omega) (by omega)
  have pNN : 0 < N * N := mul_pos (by omega) (by omega)
  have pCC : 0 < (D - N) * (D - N) := mul_pos (by omega) (by omega)
  rcases hal with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ <;> nlinarith [pDN, pNN, pCC]

theorem kx0_fact (N D a l : ℤ) (hN : 1 ≤ N) (hND : N < D) (hal : SiteConsts N D a l) :
    (D ^ 2 + 2 * D * N - N ^ 2) * (N - D - 1) < (D - N) * (a - (D ^ 2 + 2 * D * N - N ^ 2)) + D * l := by
  have pDN : 0 < (D - N) * N := mul_pos (by omega) (by omega)
  have pNN : 0 < N * N := mul_pos (by omega) (by omega)
  have pCC : 0 < (D - N) * (D - N) := mul_pos (by omega) (by omega)
  rcases hal with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ <;> nlinarith [pDN, pNN, pCC]

theorem ky1_fact (N D μ a l : ℤ) (hN : 1 ≤ N) (hND : N < D) (hal : SiteConsts N D a l) :
    N * (μ * (D ^ 2 + 2 * D * N - N ^ 2) + 2 * N - l) - (D + N) * (a - (D ^ 2 + 2 * D * N - N ^ 2)) < (D ^ 2 + 2 * D * N - N ^ 2) * (μ * N + N + D + 1) := by
  have pDN : 0 < (D - N) * N := mul_pos (by omega) (by omega)
  have pNN : 0 < N * N := mul_pos (by omega) (by omega)
  have pCC : 0 < (D - N) * (D - N) := mul_pos (by omega) (by omega)
  rcases hal with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ <;> nlinarith [pDN, pNN, pCC]

theorem ky0_fact (N D a l : ℤ) (hN : 1 ≤ N) (hND : N < D) (hal : SiteConsts N D a l) :
    (D ^ 2 + 2 * D * N - N ^ 2) * (-2) < N * l - (D + N) * (D + N - a) := by
  have pDN : 0 < (D - N) * N := mul_pos (by omega) (by omega)
  have pNN : 0 < N * N := mul_pos (by omega) (by omega)
  have pCC : 0 < (D - N) * (D - N) := mul_pos (by omega) (by omega)
  rcases hal with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ <;> nlinarith [pDN, pNN, pCC]

theorem kp1_fact (N D μ a l : ℤ) (hN : 1 ≤ N) (hND : N < D) (hal : SiteConsts N D a l) :
    -(2 * N) * (a - (D ^ 2 + 2 * D * N - N ^ 2)) + (D + N) * (μ * (D ^ 2 + 2 * D * N - N ^ 2) + 2 * N - l) < (D ^ 2 + 2 * D * N - N ^ 2) * (μ * (D + N) + 2 * N + 2) := by
  have pDN : 0 < (D - N) * N := mul_pos (by omega) (by omega)
  have pNN : 0 < N * N := mul_pos (by omega) (by omega)
  have pCC : 0 < (D - N) * (D - N) := mul_pos (by omega) (by omega)
  rcases hal with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ <;> nlinarith [pDN, pNN, pCC]

theorem kp0_fact (N D a l : ℤ) (hN : 1 ≤ N) (hND : N < D) (hal : SiteConsts N D a l) :
    (D ^ 2 + 2 * D * N - N ^ 2) * (-2) < -(2 * N) * (D + N - a) + (D + N) * l := by
  have pDN : 0 < (D - N) * N := mul_pos (by omega) (by omega)
  have pNN : 0 < N * N := mul_pos (by omega) (by omega)
  have pCC : 0 < (D - N) * (D - N) := mul_pos (by omega) (by omega)
  rcases hal with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ <;> nlinarith [pDN, pNN, pCC]

theorem km1_fact (N D μ a l : ℤ) (hN : 1 ≤ N) (hND : N < D) (hal : SiteConsts N D a l) :
    2 * D * (D + N - a) + (D - N) * (μ * (D ^ 2 + 2 * D * N - N ^ 2) + 2 * N - l) < (D ^ 2 + 2 * D * N - N ^ 2) * (μ * (D - N) + 3) := by
  have pDN : 0 < (D - N) * N := mul_pos (by omega) (by omega)
  have pNN : 0 < N * N := mul_pos (by omega) (by omega)
  have pCC : 0 < (D - N) * (D - N) := mul_pos (by omega) (by omega)
  rcases hal with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ <;> nlinarith [pDN, pNN, pCC]

theorem km0_fact (N D a l : ℤ) (hN : 1 ≤ N) (hND : N < D) (hal : SiteConsts N D a l) :
    (D ^ 2 + 2 * D * N - N ^ 2) * (-2 * D - 1) < 2 * D * (a - (D ^ 2 + 2 * D * N - N ^ 2)) + (D - N) * l := by
  have pDN : 0 < (D - N) * N := mul_pos (by omega) (by omega)
  have pNN : 0 < N * N := mul_pos (by omega) (by omega)
  have pCC : 0 < (D - N) * (D - N) := mul_pos (by omega) (by omega)
  rcases hal with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ <;> nlinarith [pDN, pNN, pCC]

theorem bx1_fact (N D μ x y a l : ℤ) (hN : 1 ≤ N) (hND : N < D) (_hA : a - (D ^ 2 + 2 * D * N - N ^ 2) ≤ N * x - D * y) (hB : N * x - D * y ≤ D + N - a)
    (_hC : l ≤ (D + N) * x + (D - N) * y)
    (hD : (D + N) * x + (D - N) * y ≤ μ * (D ^ 2 + 2 * D * N - N ^ 2) + 2 * N - l) :
    (D ^ 2 + 2 * D * N - N ^ 2) * x ≤ (D - N) * (D + N - a) + D * (μ * (D ^ 2 + 2 * D * N - N ^ 2) + 2 * N - l) := by
  have hC0 : (0 : ℤ) ≤ D - N := by omega
  have hD0 : (0 : ℤ) ≤ D := by omega
  have hN0 : (0 : ℤ) ≤ N := by omega
  have hL0 : (0 : ℤ) ≤ D + N := by omega
  have hN2 : (0 : ℤ) ≤ 2 * N := by omega
  have hD2 : (0 : ℤ) ≤ 2 * D := by omega
  nlinarith [mul_le_mul_of_nonneg_left hB hC0, mul_le_mul_of_nonneg_left hD hD0]

theorem bx0_fact (N D μ x y a l : ℤ) (hN : 1 ≤ N) (hND : N < D) (hA : a - (D ^ 2 + 2 * D * N - N ^ 2) ≤ N * x - D * y) (_hB : N * x - D * y ≤ D + N - a)
    (hC : l ≤ (D + N) * x + (D - N) * y)
    (_hD : (D + N) * x + (D - N) * y ≤ μ * (D ^ 2 + 2 * D * N - N ^ 2) + 2 * N - l) :
    (D - N) * (a - (D ^ 2 + 2 * D * N - N ^ 2)) + D * l ≤ (D ^ 2 + 2 * D * N - N ^ 2) * x := by
  have hC0 : (0 : ℤ) ≤ D - N := by omega
  have hD0 : (0 : ℤ) ≤ D := by omega
  have hN0 : (0 : ℤ) ≤ N := by omega
  have hL0 : (0 : ℤ) ≤ D + N := by omega
  have hN2 : (0 : ℤ) ≤ 2 * N := by omega
  have hD2 : (0 : ℤ) ≤ 2 * D := by omega
  nlinarith [mul_le_mul_of_nonneg_left hA hC0, mul_le_mul_of_nonneg_left hC hD0]

theorem by1_fact (N D μ x y a l : ℤ) (hN : 1 ≤ N) (hND : N < D) (hA : a - (D ^ 2 + 2 * D * N - N ^ 2) ≤ N * x - D * y) (_hB : N * x - D * y ≤ D + N - a)
    (_hC : l ≤ (D + N) * x + (D - N) * y)
    (hD : (D + N) * x + (D - N) * y ≤ μ * (D ^ 2 + 2 * D * N - N ^ 2) + 2 * N - l) :
    (D ^ 2 + 2 * D * N - N ^ 2) * y ≤ N * (μ * (D ^ 2 + 2 * D * N - N ^ 2) + 2 * N - l) - (D + N) * (a - (D ^ 2 + 2 * D * N - N ^ 2)) := by
  have hC0 : (0 : ℤ) ≤ D - N := by omega
  have hD0 : (0 : ℤ) ≤ D := by omega
  have hN0 : (0 : ℤ) ≤ N := by omega
  have hL0 : (0 : ℤ) ≤ D + N := by omega
  have hN2 : (0 : ℤ) ≤ 2 * N := by omega
  have hD2 : (0 : ℤ) ≤ 2 * D := by omega
  nlinarith [mul_le_mul_of_nonneg_left hD hN0, mul_le_mul_of_nonneg_left hA hL0]

theorem by0_fact (N D μ x y a l : ℤ) (hN : 1 ≤ N) (hND : N < D) (_hA : a - (D ^ 2 + 2 * D * N - N ^ 2) ≤ N * x - D * y) (hB : N * x - D * y ≤ D + N - a)
    (hC : l ≤ (D + N) * x + (D - N) * y)
    (_hD : (D + N) * x + (D - N) * y ≤ μ * (D ^ 2 + 2 * D * N - N ^ 2) + 2 * N - l) :
    N * l - (D + N) * (D + N - a) ≤ (D ^ 2 + 2 * D * N - N ^ 2) * y := by
  have hC0 : (0 : ℤ) ≤ D - N := by omega
  have hD0 : (0 : ℤ) ≤ D := by omega
  have hN0 : (0 : ℤ) ≤ N := by omega
  have hL0 : (0 : ℤ) ≤ D + N := by omega
  have hN2 : (0 : ℤ) ≤ 2 * N := by omega
  have hD2 : (0 : ℤ) ≤ 2 * D := by omega
  nlinarith [mul_le_mul_of_nonneg_left hC hN0, mul_le_mul_of_nonneg_left hB hL0]

theorem bp1_fact (N D μ x y a l : ℤ) (hN : 1 ≤ N) (hND : N < D) (hA : a - (D ^ 2 + 2 * D * N - N ^ 2) ≤ N * x - D * y) (_hB : N * x - D * y ≤ D + N - a)
    (_hC : l ≤ (D + N) * x + (D - N) * y)
    (hD : (D + N) * x + (D - N) * y ≤ μ * (D ^ 2 + 2 * D * N - N ^ 2) + 2 * N - l) :
    (D ^ 2 + 2 * D * N - N ^ 2) * (x + y) ≤ -(2 * N) * (a - (D ^ 2 + 2 * D * N - N ^ 2)) + (D + N) * (μ * (D ^ 2 + 2 * D * N - N ^ 2) + 2 * N - l) := by
  have hC0 : (0 : ℤ) ≤ D - N := by omega
  have hD0 : (0 : ℤ) ≤ D := by omega
  have hN0 : (0 : ℤ) ≤ N := by omega
  have hL0 : (0 : ℤ) ≤ D + N := by omega
  have hN2 : (0 : ℤ) ≤ 2 * N := by omega
  have hD2 : (0 : ℤ) ≤ 2 * D := by omega
  nlinarith [mul_le_mul_of_nonneg_left hA hN2, mul_le_mul_of_nonneg_left hD hL0]

theorem bp0_fact (N D μ x y a l : ℤ) (hN : 1 ≤ N) (hND : N < D) (_hA : a - (D ^ 2 + 2 * D * N - N ^ 2) ≤ N * x - D * y) (hB : N * x - D * y ≤ D + N - a)
    (hC : l ≤ (D + N) * x + (D - N) * y)
    (_hD : (D + N) * x + (D - N) * y ≤ μ * (D ^ 2 + 2 * D * N - N ^ 2) + 2 * N - l) :
    -(2 * N) * (D + N - a) + (D + N) * l ≤ (D ^ 2 + 2 * D * N - N ^ 2) * (x + y) := by
  have hC0 : (0 : ℤ) ≤ D - N := by omega
  have hD0 : (0 : ℤ) ≤ D := by omega
  have hN0 : (0 : ℤ) ≤ N := by omega
  have hL0 : (0 : ℤ) ≤ D + N := by omega
  have hN2 : (0 : ℤ) ≤ 2 * N := by omega
  have hD2 : (0 : ℤ) ≤ 2 * D := by omega
  nlinarith [mul_le_mul_of_nonneg_left hB hN2, mul_le_mul_of_nonneg_left hC hL0]

theorem bm1_fact (N D μ x y a l : ℤ) (hN : 1 ≤ N) (hND : N < D) (_hA : a - (D ^ 2 + 2 * D * N - N ^ 2) ≤ N * x - D * y) (hB : N * x - D * y ≤ D + N - a)
    (_hC : l ≤ (D + N) * x + (D - N) * y)
    (hD : (D + N) * x + (D - N) * y ≤ μ * (D ^ 2 + 2 * D * N - N ^ 2) + 2 * N - l) :
    (D ^ 2 + 2 * D * N - N ^ 2) * (x - y) ≤ 2 * D * (D + N - a) + (D - N) * (μ * (D ^ 2 + 2 * D * N - N ^ 2) + 2 * N - l) := by
  have hC0 : (0 : ℤ) ≤ D - N := by omega
  have hD0 : (0 : ℤ) ≤ D := by omega
  have hN0 : (0 : ℤ) ≤ N := by omega
  have hL0 : (0 : ℤ) ≤ D + N := by omega
  have hN2 : (0 : ℤ) ≤ 2 * N := by omega
  have hD2 : (0 : ℤ) ≤ 2 * D := by omega
  nlinarith [mul_le_mul_of_nonneg_left hB hD2, mul_le_mul_of_nonneg_left hD hC0]

theorem bm0_fact (N D μ x y a l : ℤ) (hN : 1 ≤ N) (hND : N < D) (hA : a - (D ^ 2 + 2 * D * N - N ^ 2) ≤ N * x - D * y) (_hB : N * x - D * y ≤ D + N - a)
    (hC : l ≤ (D + N) * x + (D - N) * y)
    (_hD : (D + N) * x + (D - N) * y ≤ μ * (D ^ 2 + 2 * D * N - N ^ 2) + 2 * N - l) :
    2 * D * (a - (D ^ 2 + 2 * D * N - N ^ 2)) + (D - N) * l ≤ (D ^ 2 + 2 * D * N - N ^ 2) * (x - y) := by
  have hC0 : (0 : ℤ) ≤ D - N := by omega
  have hD0 : (0 : ℤ) ≤ D := by omega
  have hN0 : (0 : ℤ) ≤ N := by omega
  have hL0 : (0 : ℤ) ≤ D + N := by omega
  have hN2 : (0 : ℤ) ≤ 2 * N := by omega
  have hD2 : (0 : ℤ) ≤ 2 * D := by omega
  nlinarith [mul_le_mul_of_nonneg_left hA hD2, mul_le_mul_of_nonneg_left hC hC0]

theorem box_core (N D μ x y a l : ℤ) (hN : 1 ≤ N) (hND : N < D) (hA : a - (D ^ 2 + 2 * D * N - N ^ 2) ≤ N * x - D * y) (hB : N * x - D * y ≤ D + N - a)
    (hC : l ≤ (D + N) * x + (D - N) * y)
    (hD : (D + N) * x + (D - N) * y ≤ μ * (D ^ 2 + 2 * D * N - N ^ 2) + 2 * N - l)
    (hal : SiteConsts N D a l) :
    N - D ≤ x ∧ x ≤ μ * D + 1 ∧ -1 ≤ y ∧ y ≤ μ * N + N + D ∧
      -1 ≤ x + y ∧ x + y ≤ μ * (D + N) + 2 * N + 1 ∧ -2 * D ≤ x - y ∧ x - y ≤ μ * (D - N) + 2 := by
  have hT : 0 < (D ^ 2 + 2 * D * N - N ^ 2) := by nlinarith
  have ex1 := lt_of_mul_lt_mul_left ((bx1_fact N D μ x y a l hN hND hA hB hC hD).trans_lt
    (kx1_fact N D μ a l hN hND hal)) hT.le
  have ex0 := lt_of_mul_lt_mul_left ((kx0_fact N D a l hN hND hal).trans_le
    (bx0_fact N D μ x y a l hN hND hA hB hC hD)) hT.le
  have ey1 := lt_of_mul_lt_mul_left ((by1_fact N D μ x y a l hN hND hA hB hC hD).trans_lt
    (ky1_fact N D μ a l hN hND hal)) hT.le
  have ey0 := lt_of_mul_lt_mul_left ((ky0_fact N D a l hN hND hal).trans_le
    (by0_fact N D μ x y a l hN hND hA hB hC hD)) hT.le
  have ep1 := lt_of_mul_lt_mul_left ((bp1_fact N D μ x y a l hN hND hA hB hC hD).trans_lt
    (kp1_fact N D μ a l hN hND hal)) hT.le
  have ep0 := lt_of_mul_lt_mul_left ((kp0_fact N D a l hN hND hal).trans_le
    (bp0_fact N D μ x y a l hN hND hA hB hC hD)) hT.le
  have em1 := lt_of_mul_lt_mul_left ((bm1_fact N D μ x y a l hN hND hA hB hC hD).trans_lt
    (km1_fact N D μ a l hN hND hal)) hT.le
  have em0 := lt_of_mul_lt_mul_left ((km0_fact N D a l hN hND hal).trans_le
    (bm0_fact N D μ x y a l hN hND hA hB hC hD)) hT.le
  omega

/-- **The box of `H_f`** for `0 < n < d`, with `μ = muOf f`. -/
theorem inH_box (f : Fraction) (hn : 0 < f.num) (hnd : f.num < f.den) (z : GInt) (hz : InH f z) :
    f.num - f.den ≤ z.1 ∧ z.1 ≤ SiteInduction.muOf f * f.den + 1 ∧
      -1 ≤ z.2 ∧ z.2 ≤ SiteInduction.muOf f * f.num + f.num + f.den ∧
      -1 ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ SiteInduction.muOf f * (f.den + f.num) + 2 * f.num + 1 ∧
      -2 * f.den ≤ z.1 - z.2 ∧ z.1 - z.2 ≤ SiteInduction.muOf f * (f.den - f.num) + 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  unfold SiteInduction.tCo SiteInduction.sCo SiteInduction.tOf at *
  obtain ⟨hodd, heven⟩ := SiteHullOdd.site_ab f z
  by_cases hp : (z.1 + z.2) % 2 = 0
  · obtain ⟨ha, hl⟩ := heven hp
    simp only [ha, hl] at h1 h2 h3 h4
    refine box_core f.num f.den _ z.1 z.2 (min (2 * f.num) (f.den - f.num)) 0 (by omega) hnd
      (by linarith) (by linarith) (by linarith) (by linarith) (Or.inl ⟨rfl, ?_⟩)
    rcases min_choice (2 * f.num) (f.den - f.num) with h | h <;> rw [h] <;> simp
  · obtain ⟨ha, hl⟩ := hodd (by omega)
    simp only [ha, hl] at h1 h2 h3 h4
    refine box_core f.num f.den _ z.1 z.2 f.num (min (f.den - f.num) (3 * f.num - f.den)) (by omega) hnd
      (by linarith) (by linarith) (by linarith) (by linarith) (Or.inr ⟨rfl, ?_⟩)
    rcases min_choice (f.den - f.num) (3 * f.num - f.den) with h | h <;> rw [h] <;> simp

/-! ### The half-turn of the alternate children (item (1)), with its centre

Item (1) of `lemma:alternate_tile_properties` (`AltRotStep.altRot`) at `w` and at the swapped word gives `T̂ = D - T̂` for the
alternate children of the paper base: composing the two rotations, `T̂(q₀) ↦ T̂(R(q₀))` and back, is `z ↦ τ₂ + i τ₁ - z`. In the
frame `c(T̂) = 0` the centres are those of the proof of the text (Step 2): `D = A + 2B + V + 1 - i` for `T̂(q₀)` in the even-first
orientation and `D = A + 2B + V + 2U + 1 - i` in the odd-first one; for `T̂(p₀)` the other way round. Here
`(A, B, U, V) = (v_{p₁,1}, v_{p₁,2}, v_{q₁,1}, v_{q₁,2})`. -/

/-- The centre of the half-turn of `T̂(q₀)`: `A + 2B + V + 1 - i`, plus `2U` when `W₁` is odd. -/
def centreEven (o : Bool) (p q : Fraction) : Site :=
  (2 * p.num + q.num - q.den + 1 + (if o then 2 * q.den else 0),
    4 * p.num + 2 * p.den + q.num + q.den - 1 + (if o then 2 * q.num else 0))

/-- The centre of the half-turn of `T̂(p₀)`: `A + 2B + V + 1 - i`, plus `2U` when `W₁` is even. -/
def centreOdd (o : Bool) (p q : Fraction) : Site :=
  (2 * p.num + q.num - q.den + 1 + (if o then 0 else 2 * q.den),
    4 * p.num + 2 * p.den + q.num + q.den - 1 + (if o then 0 else 2 * q.num))

theorem mem_shift_rot (S : Tile) (t x : Site) : x ∈ shift (rot S) t ↔ ((x - t).2, -(x - t).1) ∈ S := by
  rw [mem_shift, Standard.mem_rot]

/-- Two rotations, each followed by a translation, are a half-turn. -/
theorem halfTurn_of_rots (S S' : Tile) (t1 t2 : Site) (h1 : shift (rot S) t1 = S') (h2 : shift (rot S') t2 = S) (z : Site) :
    z ∈ S ↔ (t2.1 - t1.2 - z.1, t2.2 + t1.1 - z.2) ∈ S := by
  have key : ∀ y : Site, y ∈ S ↔ (t2.1 - t1.2 - y.1, t2.2 + t1.1 - y.2) ∈ S := by
    intro y
    conv_lhs => rw [← h2]
    rw [mem_shift_rot, ← h1, mem_shift_rot]
    constructor <;> intro h <;> convert h using 2 <;> simp <;> ring
  exact key z

theorem parents_swapW (w : Word) :
    (parentsAt (swapW w)).odd = (parentsAt w).even.rotate ∧ (parentsAt (swapW w)).even = (parentsAt w).odd.rotate := by
  have h1 := VStep.rot_parent_even_swap (swapW w)
  have h2 := VStep.rot_parent_odd_swap (swapW w)
  rw [AltRotStep.swapW_swapW] at h1 h2
  exact ⟨h1.symm, h2.symm⟩

/-- **The half-turn of `T̂(q₀)`** about `centreEven` (non-base words, the paper base). -/
theorem altEven_halfTurn {w : Word} (hw : ¬ IsBase w) (z : Site) :
    z ∈ altEvenTile AltRotStep.B w ↔
      centreEven (phase w == 1) (parentsAt w).odd (parentsAt w).even - z ∈ altEvenTile AltRotStep.B w := by
  have h1 := (AltRotStep.altRot w).2
  have h2 := (AltRotStep.altRot (swapW w)).1
  rw [AltRotStep.swapW_swapW] at h2
  rw [halfTurn_of_rots _ _ _ _ h1 h2 z]
  obtain ⟨hp1, hp2, hq1, hq2, hpo, hqe, -⟩ := parents_facts hw
  obtain ⟨hs1, hs2⟩ := parents_swapW w
  have hph : phase (swapW w) = phase w := Standard.phase_swapW w
  unfold AltRotStep.tauO AltRotStep.tauE AltRotStep.tauOdd AltRotStep.tauEven AltRotStep.tauShort AltRotStep.tauLong
  rw [hs1, hs2, hph, Fraction.rotate_of_odd hpo, Fraction.rotate_of_even hqe]
  unfold centreEven
  constructor <;> intro h <;> convert h using 2 <;> cases (phase w == 1) <;> simp <;> omega

/-- **The half-turn of `T̂(p₀)`** about `centreOdd` (non-base words, the paper base). -/
theorem altOdd_halfTurn {w : Word} (hw : ¬ IsBase w) (z : Site) :
    z ∈ altOddTile AltRotStep.B w ↔
      centreOdd (phase w == 1) (parentsAt w).odd (parentsAt w).even - z ∈ altOddTile AltRotStep.B w := by
  have h1 := (AltRotStep.altRot w).1
  have h2 := (AltRotStep.altRot (swapW w)).2
  rw [AltRotStep.swapW_swapW] at h2
  rw [halfTurn_of_rots _ _ _ _ h1 h2 z]
  obtain ⟨hp1, hp2, hq1, hq2, hpo, hqe, -⟩ := parents_facts hw
  obtain ⟨hs1, hs2⟩ := parents_swapW w
  have hph : phase (swapW w) = phase w := Standard.phase_swapW w
  unfold AltRotStep.tauO AltRotStep.tauE AltRotStep.tauOdd AltRotStep.tauEven AltRotStep.tauShort AltRotStep.tauLong
  rw [hs1, hs2, hph, Fraction.rotate_of_odd hpo, Fraction.rotate_of_even hqe]
  unfold centreOdd
  constructor <;> intro h <;> convert h using 2 <;> cases (phase w == 1) <;> simp <;> omega

end FLatticePaper.Tiles.AltPieces
