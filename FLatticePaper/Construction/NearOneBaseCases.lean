import FLatticePaper.Construction.BaseCaseRecurrence

/-! The four near-one base cases of Section 6 of `paper/farey_recursion.tex`, transcribed literally from the TeX
for review: `lemma:basecase_2k_odd_std` (lines 2180–2192), `lemma:basecase_2k_odd_alt` (lines 2261–2280),
`lemma:basecase_2k_even_std` (lines 2402–2420) and `lemma:basecase_2k_even_alt` (lines 2478–2500). The fraction is
`Fraction.rotate ⟨1, d⟩`. The sets are written as the TeX writes them; points written `(a,b)` are single sites. -/

namespace FLatticePaper.Construction

open Farey

/-! ### Standard odd near-one staircase, `lemma:basecase_2k_odd_std` (lines 2180–2192) -/

/-- The tile `T_{p_1}` of `lemma:basecase_2k_odd_std`. -/
def paperNearStairTile (d : ℤ) : Set Site :=
  {x | 0 ≤ x.1 ∧ x.1 ≤ d + 1 ∧ 1 ≤ x.2 ∧ x.2 ≤ 2 * d - 1 ∧ -1 ≤ x.2 - x.1 ∧ x.2 - x.1 ≤ d} ∪
    {(0, d + 1), (d + 1, d - 1)}

/-- The height `g_{p_1}` of `lemma:basecase_2k_odd_std`. -/
def paperNearStairValue (d : ℤ) (x : Site) : ℤ :=
  -((x.2 - x.1) ^ 2 / 4) + min (d - x.2) 0 + if x = (0, d + 1) ∨ x = (d + 1, d - 1) then 1 else 0

/-! ### Alternate odd near-one staircase, `lemma:basecase_2k_odd_alt` (lines 2261–2280) -/

/-- `A = [-1,0] × {2d} ∪ [d,d+1] × {d-2}` of `lemma:basecase_2k_odd_alt`. -/
def paperNearStairAltA (d : ℤ) : Set Site :=
  {x : Site | -1 ≤ x.1 ∧ x.1 ≤ 0 ∧ x.2 = 2 * d} ∪ {x : Site | d ≤ x.1 ∧ x.1 ≤ d + 1 ∧ x.2 = d - 2}

/-- `B = {(x_1, x_2) : x_2 - x_1 = d - 1 and 0 < x_1 < d}` of `lemma:basecase_2k_odd_alt`. -/
def paperNearStairAltB (d : ℤ) : Set Site :=
  {x : Site | x.2 - x.1 = d - 1 ∧ 0 < x.1 ∧ x.1 < d}

/-- `C = {-1} × [d+1,2d] ∪ {d+1} × [d-2,2d-3]` of `lemma:basecase_2k_odd_alt`. -/
def paperNearStairAltC (d : ℤ) : Set Site :=
  {x : Site | x.1 = -1 ∧ d + 1 ≤ x.2 ∧ x.2 ≤ 2 * d} ∪
    {x : Site | x.1 = d + 1 ∧ d - 2 ≤ x.2 ∧ x.2 ≤ 2 * d - 3}

/-- `D = {(x_1, x_2) ∈ [0, d] × [1, 3d-3] : -1 ≤ x_2 - x_1 ≤ 2d-1}` of `lemma:basecase_2k_odd_alt`. -/
def paperNearStairAltD (d : ℤ) : Set Site :=
  {x : Site | 0 ≤ x.1 ∧ x.1 ≤ d ∧ 1 ≤ x.2 ∧ x.2 ≤ 3 * d - 3 ∧ -1 ≤ x.2 - x.1 ∧ x.2 - x.1 ≤ 2 * d - 1}

/-- The tile `\hat T_{p_1} = A ∪ B ∪ C ∪ D` of `lemma:basecase_2k_odd_alt`. -/
def paperNearStairAltTile (d : ℤ) : Set Site :=
  paperNearStairAltA d ∪ paperNearStairAltB d ∪ paperNearStairAltC d ∪ paperNearStairAltD d

/-- The height `\hat g_{p_1}` on `\hat T_{p_1}` in `lemma:basecase_2k_odd_alt`, with `1_{A ∪ B}`. -/
noncomputable def paperNearStairAltValue (d : ℤ) (x : Site) : ℤ :=
  -((x.2 - x.1) ^ 2 / 4) + min (d - x.2 - 1) 0 + min ((2 * d - 1) - x.2) 0 +
    max ((x.2 - x.1) - d + 1) 0 + (paperNearStairAltA d ∪ paperNearStairAltB d).indicator (fun _ => (1 : ℤ)) x

/-! ### Standard even near-one doubled staircase, `lemma:basecase_2k_even_std` (lines 2402–2420) -/

/-- `A = (-1, 2d+1) ∪ (d+1, d-1)` of `lemma:basecase_2k_even_std`, as two sites. -/
def paperNearLadderA (d : ℤ) : Set Site := {(-1, 2 * d + 1), (d + 1, d - 1)}

/-- `B = {(x_1, x_2) : x_2 - x_1 = d and 0 < x_1 < d}` of `lemma:basecase_2k_even_std`. -/
def paperNearLadderB (d : ℤ) : Set Site :=
  {x : Site | x.2 - x.1 = d ∧ 0 < x.1 ∧ x.1 < d}

/-- `C = {(x_1, x_2) ∈ [-1, d+1] × [1, 3d-1] : -1 ≤ x_2 - x_1 ≤ 2d+1}` of `lemma:basecase_2k_even_std`. -/
def paperNearLadderC (d : ℤ) : Set Site :=
  {x : Site | -1 ≤ x.1 ∧ x.1 ≤ d + 1 ∧ 1 ≤ x.2 ∧ x.2 ≤ 3 * d - 1 ∧ -1 ≤ x.2 - x.1 ∧ x.2 - x.1 ≤ 2 * d + 1}

/-- `D = {x_1 = -1 and x_2 ≤ d+1, or x_1 = d+1 and x_2 ≥ 2d-1}` of `lemma:basecase_2k_even_std`. -/
def paperNearLadderD (d : ℤ) : Set Site :=
  {x : Site | (x.1 = -1 ∧ x.2 ≤ d + 1) ∨ (x.1 = d + 1 ∧ 2 * d - 1 ≤ x.2)}

/-- The tile `T_{q_1} = (A ∪ B ∪ C) \ D` of `lemma:basecase_2k_even_std`. -/
def paperNearLadderTile (d : ℤ) : Set Site :=
  (paperNearLadderA d ∪ paperNearLadderB d ∪ paperNearLadderC d) \ paperNearLadderD d

/-- The height `g_{q_1}` of `lemma:basecase_2k_even_std`, with `1_{A ∪ B}`. -/
noncomputable def paperNearLadderValue (d : ℤ) (x : Site) : ℤ :=
  -((x.2 - x.1) ^ 2 / 4) + min 0 (d - x.2) + min 0 (2 * d - x.2) + max ((x.2 - x.1) - d) 0 +
    (paperNearLadderA d ∪ paperNearLadderB d).indicator (fun _ => (1 : ℤ)) x

/-! ### Alternate even near-one doubled staircase, `lemma:basecase_2k_even_alt` (lines 2478–2500) -/

/-- `A = (-2, 2d) ∪ (d+1, d-1)` of `lemma:basecase_2k_even_alt`, as two sites. -/
def paperNearLadderAltA (d : ℤ) : Set Site := {(-2, 2 * d), (d + 1, d - 1)}

/-- `B = {(x_1, x_2) : x_2 - x_1 = d and 0 < x_1 < d-1}` of `lemma:basecase_2k_even_alt`. -/
def paperNearLadderAltB (d : ℤ) : Set Site :=
  {x : Site | x.2 - x.1 = d ∧ 0 < x.1 ∧ x.1 < d - 1}

/-- `C = {(x_1, x_2) ∈ [-2, d+1] × [1, 3d-2] : -1 ≤ x_2 - x_1 ≤ 2d+1}` of `lemma:basecase_2k_even_alt`. -/
def paperNearLadderAltC (d : ℤ) : Set Site :=
  {x : Site | -2 ≤ x.1 ∧ x.1 ≤ d + 1 ∧ 1 ≤ x.2 ∧ x.2 ≤ 3 * d - 2 ∧ -1 ≤ x.2 - x.1 ∧ x.2 - x.1 ≤ 2 * d + 1}

/-- `D = {x_1 ≤ -1 and x_2 ≤ d-1, or x_1 ≥ d and x_2 ≥ 2d}` of `lemma:basecase_2k_even_alt`. -/
def paperNearLadderAltD (d : ℤ) : Set Site :=
  {x : Site | (x.1 ≤ -1 ∧ x.2 ≤ d - 1) ∨ (d ≤ x.1 ∧ 2 * d ≤ x.2)}

/-- The tile `\hat T_{q_1} = (A ∪ B ∪ C) \ D` of `lemma:basecase_2k_even_alt`. -/
def paperNearLadderAltTile (d : ℤ) : Set Site :=
  (paperNearLadderAltA d ∪ paperNearLadderAltB d ∪ paperNearLadderAltC d) \ paperNearLadderAltD d

/-- The height `\hat g_{q_1}` on `\hat T_{q_1}` in `lemma:basecase_2k_even_alt`, with `1_{A ∪ B}`. -/
noncomputable def paperNearLadderAltValue (d : ℤ) (x : Site) : ℤ :=
  -((x.2 - x.1) ^ 2 / 4) + min 0 (d - x.2) + min 0 (2 * d - 1 - x.2) + max 0 (x.2 - x.1 - d) +
    (paperNearLadderAltA d ∪ paperNearLadderAltB d).indicator (fun _ => (1 : ℤ)) x

end FLatticePaper.Construction
