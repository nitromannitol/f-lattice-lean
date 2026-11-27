import FLatticePaper.Tiles.SurgicalAffineChain
import FLatticePaper.Tiles.SurgicalSlopes
import FLatticePaper.Tiles.SurgicalOdometerStep

/-! The 24 junction (seam) identities of the odd and even standard steps.

At a junction the child's string passes from the last tile `t` of one placed piece to the first tile `t'` of the next. The
slope difference across it is `(slope of t') - (slope of t)`, and each side is the base slope of the tile type plus the
affine factor of the register at its corner plus the placement factor of the piece (`pairAffine`). The register corner
factors are, by (b) with the normalisation `a(A) = 0`: `a(A) = a(B) = 0`, `a(C) = (n-1, 1-d)`, `a(D) = (n, 1-d)` for the
register of fraction `n/d`. The corner tile types are fixed: `A` and `C` are `one`, `B` and `D` are `zero`.

`seam_identity` reduces a junction to an integer identity `aY - aX = κ` between the affine factors, where `κ` is the table
value minus the base slope difference. Each of the 24 junctions below is one instance; the identity `aY - aX = κ` is a ring
identity in the four Farey parameters `np dp nq dq`. -/

namespace FLatticePaper.Tiles.SeamIdentities

open FLatticePaper.Tiles

/-- The corners of a register tile (`cornerTiles`): `A` the first tile of `w_h`, `B` its last tile, `C` the last tile of
`rev(w_h)`, `D` its first tile. -/
inductive Corner
  | A | B | C | D

/-- The tile type of a corner (`A`, `C`: `one`; `B`, `D`: `zero`; from the first and last letters of `w_h`). -/
def cornerTile : Corner → ZTile
  | .A => .one
  | .B => .zero
  | .C => .one
  | .D => .zero

/-- The normalised affine factor of a corner of the register of fraction `n/d` (`(b)` with `a(A) = 0`). -/
def cornerAff : Corner → ℤ → ℤ → ℤ × ℤ
  | .A, _, _ => (0, 0)
  | .B, _, _ => (0, 0)
  | .C, n, d => (n - 1, 1 - d)
  | .D, n, d => (n, 1 - d)

/-- The slope difference across a junction, from the base slopes and the affine factors of the two sides. -/
def seamLHS (tX tY : ZTile) (aX aY : ℤ × ℤ) : ℚ × ℚ :=
  (zTileBaseSlope tY + ((aY.1 : ℚ), (aY.2 : ℚ))) - (zTileBaseSlope tX + ((aX.1 : ℚ), (aX.2 : ℚ)))

/-- **The seam identity.** If the affine factors differ by `κ` and the table value is the base difference plus `κ`, the slope
difference across the junction is the surgical table value. -/
theorem seam_identity (o : Orientation) (rev : Bool) (tX tY : ZTile) (aX aY κ : ℤ × ℤ)
    (hκ : aY.1 - aX.1 = κ.1 ∧ aY.2 - aX.2 = κ.2)
    (htab : surgicalSlopeDiff o rev (zTileLetter tX) (zTileLetter tY) =
      (zTileBaseSlope tY - zTileBaseSlope tX) + ((κ.1 : ℚ), (κ.2 : ℚ))) :
    seamLHS tX tY aX aY = surgicalSlopeDiff o rev (zTileLetter tX) (zTileLetter tY) := by
  rw [htab]
  obtain ⟨h1, h2⟩ := hκ
  have e1 : ((aY.1 : ℤ) : ℚ) - ((aX.1 : ℤ) : ℚ) = ((κ.1 : ℤ) : ℚ) := by exact_mod_cast h1
  have e2 : ((aY.2 : ℤ) : ℚ) - ((aX.2 : ℤ) : ℚ) = ((κ.2 : ℤ) : ℚ) := by exact_mod_cast h2
  unfold seamLHS
  apply Prod.ext
  · simp only [Prod.fst_add, Prod.fst_sub]
    linarith
  · simp only [Prod.snd_add, Prod.snd_sub]
    linarith

/-! ### The 24 junctions. `pa n d c1 c2` is `pairAffine n d c1 c2`, the placement factor `c1 a_{·,1} + c2 a_{·,2}`. -/

variable (np dp nq dq : ℤ)

/-- Junction `odd_T_wh_1`: `P.B -> Q.A`. -/
theorem seam_odd_T_wh_1 :
    seamLHS .zero .one (cornerAff .B np dp) (cornerAff .A nq dq) =
      surgicalSlopeDiff .horizontal false (zTileLetter .zero) (zTileLetter .one) := by
  apply seam_identity .horizontal false .zero .one _ _ (0, 0)
  · simp only [cornerAff]
    constructor <;> ring
  · norm_num [surgicalSlopeDiff, zTileLetter, zTileBaseSlope_zero, zTileBaseSlope_one]

/-- Junction `odd_T_rwh_3`: `Q.C -> Q.D`. -/
theorem seam_odd_T_rwh_3 :
    seamLHS .one .zero (cornerAff .C nq dq + (pairAffine np dp 0 1)) (cornerAff .D nq dq + (pairAffine np dp 0 1)) =
      surgicalSlopeDiff .horizontal true (zTileLetter .one) (zTileLetter .zero) := by
  apply seam_identity .horizontal true .one .zero _ _ (1, 0)
  · simp only [cornerAff, pairAffine, offsetA, Prod.fst_add, Prod.snd_add]
    constructor <;> ring
  · norm_num [surgicalSlopeDiff, zTileLetter, zTileBaseSlope_zero, zTileBaseSlope_one]

/-- Junction `odd_T_rwh_4`: `Q.C -> P.D`. -/
theorem seam_odd_T_rwh_4 :
    seamLHS .one .zero (cornerAff .C nq dq + (pairAffine np dp 0 1)) (cornerAff .D np dp + (pairAffine nq dq 2 1)) =
      surgicalSlopeDiff .horizontal true (zTileLetter .one) (zTileLetter .zero) := by
  apply seam_identity .horizontal true .one .zero _ _ (1, 0)
  · simp only [cornerAff, pairAffine, offsetA, Prod.fst_add, Prod.snd_add]
    constructor <;> ring
  · norm_num [surgicalSlopeDiff, zTileLetter, zTileBaseSlope_zero, zTileBaseSlope_one]

/-- Junction `odd_T_rwv_5`: `P.D -> Q.A`. -/
theorem seam_odd_T_rwv_5 :
    seamLHS .zero .one (cornerAff .D np dp) (cornerAff .A nq dq + (pairAffine np dp 0 1)) =
      surgicalSlopeDiff .vertical true (zTileLetter .zero) (zTileLetter .one) := by
  apply seam_identity .vertical true .zero .one _ _ (0, -1)
  · simp only [cornerAff, pairAffine, offsetA, Prod.fst_add, Prod.snd_add]
    constructor <;> ring
  · norm_num [surgicalSlopeDiff, zTileLetter, zTileBaseSlope_zero, zTileBaseSlope_one]

/-- Junction `odd_T_wv_6`: `Q.C -> P.B`. -/
theorem seam_odd_T_wv_6 :
    seamLHS .one .zero (cornerAff .C nq dq) (cornerAff .B np dp + (pairAffine nq dq 2 1)) =
      surgicalSlopeDiff .vertical false (zTileLetter .one) (zTileLetter .zero) := by
  apply seam_identity .vertical false .one .zero _ _ (1, -1)
  · simp only [cornerAff, pairAffine, offsetA, Prod.fst_add, Prod.snd_add]
    constructor <;> ring
  · norm_num [surgicalSlopeDiff, zTileLetter, zTileBaseSlope_zero, zTileBaseSlope_one]

/-- Junction `odd_T_wh_2`: `Q.B -> Q.A`. -/
theorem seam_odd_T_wh_2 :
    seamLHS .zero .one (cornerAff .B nq dq) (cornerAff .A nq dq) =
      surgicalSlopeDiff .horizontal false (zTileLetter .zero) (zTileLetter .one) := by
  apply seam_identity .horizontal false .zero .one _ _ (0, 0)
  · simp only [cornerAff]
    constructor <;> ring
  · norm_num [surgicalSlopeDiff, zTileLetter, zTileBaseSlope_zero, zTileBaseSlope_one]

/-- Junction `odd_F_wh_7`: `Q.B -> P.A`. -/
theorem seam_odd_F_wh_7 :
    seamLHS .zero .one (cornerAff .B nq dq) (cornerAff .A np dp + (pairAffine nq dq 2 0)) =
      surgicalSlopeDiff .horizontal false (zTileLetter .zero) (zTileLetter .one) := by
  apply seam_identity .horizontal false .zero .one _ _ (0, 0)
  · simp only [cornerAff, pairAffine, offsetA, Prod.fst_add, Prod.snd_add]
    constructor <;> ring
  · norm_num [surgicalSlopeDiff, zTileLetter, zTileBaseSlope_zero, zTileBaseSlope_one]

/-- Junction `odd_F_rwh_8`: `P.C -> Q.D`. -/
theorem seam_odd_F_rwh_8 :
    seamLHS .one .zero (cornerAff .C np dp + (pairAffine nq dq 0 1)) (cornerAff .D nq dq + (pairAffine np dp 1 1)) =
      surgicalSlopeDiff .horizontal true (zTileLetter .one) (zTileLetter .zero) := by
  apply seam_identity .horizontal true .one .zero _ _ (1, 0)
  · simp only [cornerAff, pairAffine, offsetA, Prod.fst_add, Prod.snd_add]
    constructor <;> ring
  · norm_num [surgicalSlopeDiff, zTileLetter, zTileBaseSlope_zero, zTileBaseSlope_one]

/-- Junction `odd_F_rwh_9`: `Q.C -> Q.D`. -/
theorem seam_odd_F_rwh_9 :
    seamLHS .one .zero (cornerAff .C nq dq + (pairAffine np dp 1 1)) (cornerAff .D nq dq + (pairAffine np dp 1 1)) =
      surgicalSlopeDiff .horizontal true (zTileLetter .one) (zTileLetter .zero) := by
  apply seam_identity .horizontal true .one .zero _ _ (1, 0)
  · simp only [cornerAff, pairAffine, offsetA, Prod.fst_add, Prod.snd_add]
    constructor <;> ring
  · norm_num [surgicalSlopeDiff, zTileLetter, zTileBaseSlope_zero, zTileBaseSlope_one]

/-- Junction `odd_F_rwv_10`: `Q.D -> P.A`. -/
theorem seam_odd_F_rwv_10 :
    seamLHS .zero .one (cornerAff .D nq dq + (pairAffine np dp 0 0)) (cornerAff .A np dp + (pairAffine nq dq 0 1)) =
      surgicalSlopeDiff .vertical true (zTileLetter .zero) (zTileLetter .one) := by
  apply seam_identity .vertical true .zero .one _ _ (0, -1)
  · simp only [cornerAff, pairAffine, offsetA, Prod.fst_add, Prod.snd_add]
    constructor <;> ring
  · norm_num [surgicalSlopeDiff, zTileLetter, zTileBaseSlope_zero, zTileBaseSlope_one]

/-- Junction `odd_F_wv_11`: `P.C -> Q.B`. -/
theorem seam_odd_F_wv_11 :
    seamLHS .one .zero (cornerAff .C np dp + (pairAffine nq dq 2 0)) (cornerAff .B nq dq + (pairAffine np dp 1 1)) =
      surgicalSlopeDiff .vertical false (zTileLetter .one) (zTileLetter .zero) := by
  apply seam_identity .vertical false .one .zero _ _ (1, -1)
  · simp only [cornerAff, pairAffine, offsetA, Prod.fst_add, Prod.snd_add]
    constructor <;> ring
  · norm_num [surgicalSlopeDiff, zTileLetter, zTileBaseSlope_zero, zTileBaseSlope_one]

/-- Junction `odd_F_wh_12`: `Q.B -> Q.A`. -/
theorem seam_odd_F_wh_12 :
    seamLHS .zero .one (cornerAff .B nq dq + (pairAffine np dp 0 0)) (cornerAff .A nq dq + (pairAffine nq dq 1 0)) =
      surgicalSlopeDiff .horizontal false (zTileLetter .zero) (zTileLetter .one) := by
  apply seam_identity .horizontal false .zero .one _ _ (0, 0)
  · simp only [cornerAff, pairAffine, offsetA, Prod.fst_add, Prod.snd_add]
    constructor <;> ring
  · norm_num [surgicalSlopeDiff, zTileLetter, zTileBaseSlope_zero, zTileBaseSlope_one]

/-- Junction `even_T_wh_13`: `P.B -> Q.A`. -/
theorem seam_even_T_wh_13 :
    seamLHS .zero .one (cornerAff .B np dp) (cornerAff .A nq dq + (pairAffine np dp 1 0)) =
      surgicalSlopeDiff .horizontal false (zTileLetter .zero) (zTileLetter .one) := by
  apply seam_identity .horizontal false .zero .one _ _ (0, 0)
  · simp only [cornerAff, pairAffine, offsetA, Prod.fst_add, Prod.snd_add]
    constructor <;> ring
  · norm_num [surgicalSlopeDiff, zTileLetter, zTileBaseSlope_zero, zTileBaseSlope_one]

/-- Junction `even_T_rwh_14`: `Q.C -> P.D`. -/
theorem seam_even_T_rwh_14 :
    seamLHS .one .zero (cornerAff .C nq dq + (pairAffine np dp 0 2)) (cornerAff .D np dp + (pairAffine nq dq 1 1 + pairAffine np dp 0 1)) =
      surgicalSlopeDiff .horizontal true (zTileLetter .one) (zTileLetter .zero) := by
  apply seam_identity .horizontal true .one .zero _ _ (1, 0)
  · simp only [cornerAff, pairAffine, offsetA, Prod.fst_add, Prod.snd_add]
    constructor <;> ring
  · norm_num [surgicalSlopeDiff, zTileLetter, zTileBaseSlope_zero, zTileBaseSlope_one]

/-- Junction `even_T_rwv_15`: `P.D -> P.A`. -/
theorem seam_even_T_rwv_15 :
    seamLHS .zero .one (cornerAff .D np dp) (cornerAff .A np dp + (pairAffine np dp 0 1)) =
      surgicalSlopeDiff .vertical true (zTileLetter .zero) (zTileLetter .one) := by
  apply seam_identity .vertical true .zero .one _ _ (0, -1)
  · simp only [cornerAff, pairAffine, offsetA, Prod.fst_add, Prod.snd_add]
    constructor <;> ring
  · norm_num [surgicalSlopeDiff, zTileLetter, zTileBaseSlope_zero, zTileBaseSlope_one]

/-- Junction `even_T_rwv_16`: `P.D -> Q.A`. -/
theorem seam_even_T_rwv_16 :
    seamLHS .zero .one (cornerAff .D np dp + (pairAffine np dp 0 1)) (cornerAff .A nq dq + (pairAffine np dp 0 2)) =
      surgicalSlopeDiff .vertical true (zTileLetter .zero) (zTileLetter .one) := by
  apply seam_identity .vertical true .zero .one _ _ (0, -1)
  · simp only [cornerAff, pairAffine, offsetA, Prod.fst_add, Prod.snd_add]
    constructor <;> ring
  · norm_num [surgicalSlopeDiff, zTileLetter, zTileBaseSlope_zero, zTileBaseSlope_one]

/-- Junction `even_T_wv_17`: `Q.C -> P.B`. -/
theorem seam_even_T_wv_17 :
    seamLHS .one .zero (cornerAff .C nq dq + (pairAffine np dp 1 0)) (cornerAff .B np dp + (pairAffine nq dq 1 1)) =
      surgicalSlopeDiff .vertical false (zTileLetter .one) (zTileLetter .zero) := by
  apply seam_identity .vertical false .one .zero _ _ (1, -1)
  · simp only [cornerAff, pairAffine, offsetA, Prod.fst_add, Prod.snd_add]
    constructor <;> ring
  · norm_num [surgicalSlopeDiff, zTileLetter, zTileBaseSlope_zero, zTileBaseSlope_one]

/-- Junction `even_T_wv_18`: `P.C -> P.B`. -/
theorem seam_even_T_wv_18 :
    seamLHS .one .zero (cornerAff .C np dp + (pairAffine nq dq 1 1)) (cornerAff .B np dp + (pairAffine nq dq 1 1 + pairAffine np dp 0 1)) =
      surgicalSlopeDiff .vertical false (zTileLetter .one) (zTileLetter .zero) := by
  apply seam_identity .vertical false .one .zero _ _ (1, -1)
  · simp only [cornerAff, pairAffine, offsetA, Prod.fst_add, Prod.snd_add]
    constructor <;> ring
  · norm_num [surgicalSlopeDiff, zTileLetter, zTileBaseSlope_zero, zTileBaseSlope_one]

/-- Junction `even_F_wh_19`: `Q.B -> P.A`. -/
theorem seam_even_F_wh_19 :
    seamLHS .zero .one (cornerAff .B nq dq + (pairAffine np dp 0 0)) (cornerAff .A np dp + (pairAffine nq dq 1 0)) =
      surgicalSlopeDiff .horizontal false (zTileLetter .zero) (zTileLetter .one) := by
  apply seam_identity .horizontal false .zero .one _ _ (0, 0)
  · simp only [cornerAff, pairAffine, offsetA, Prod.fst_add, Prod.snd_add]
    constructor <;> ring
  · norm_num [surgicalSlopeDiff, zTileLetter, zTileBaseSlope_zero, zTileBaseSlope_one]

/-- Junction `even_F_rwh_20`: `P.C -> Q.D`. -/
theorem seam_even_F_rwh_20 :
    seamLHS .one .zero (cornerAff .C np dp + (pairAffine nq dq 1 1 + pairAffine np dp 0 1)) (cornerAff .D nq dq + (pairAffine np dp 1 0 + pairAffine np dp 0 2)) =
      surgicalSlopeDiff .horizontal true (zTileLetter .one) (zTileLetter .zero) := by
  apply seam_identity .horizontal true .one .zero _ _ (1, 0)
  · simp only [cornerAff, pairAffine, offsetA, Prod.fst_add, Prod.snd_add]
    constructor <;> ring
  · norm_num [surgicalSlopeDiff, zTileLetter, zTileBaseSlope_zero, zTileBaseSlope_one]

/-- Junction `even_F_rwv_21`: `Q.D -> P.A`. -/
theorem seam_even_F_rwv_21 :
    seamLHS .zero .one (cornerAff .D nq dq + (pairAffine np dp 0 0)) (cornerAff .A np dp + (pairAffine nq dq 0 1)) =
      surgicalSlopeDiff .vertical true (zTileLetter .zero) (zTileLetter .one) := by
  apply seam_identity .vertical true .zero .one _ _ (0, -1)
  · simp only [cornerAff, pairAffine, offsetA, Prod.fst_add, Prod.snd_add]
    constructor <;> ring
  · norm_num [surgicalSlopeDiff, zTileLetter, zTileBaseSlope_zero, zTileBaseSlope_one]

/-- Junction `even_F_rwv_22`: `P.D -> P.A`. -/
theorem seam_even_F_rwv_22 :
    seamLHS .zero .one (cornerAff .D np dp + (pairAffine nq dq 0 1)) (cornerAff .A np dp + (pairAffine nq dq 0 1 + pairAffine np dp 0 1)) =
      surgicalSlopeDiff .vertical true (zTileLetter .zero) (zTileLetter .one) := by
  apply seam_identity .vertical true .zero .one _ _ (0, -1)
  · simp only [cornerAff, pairAffine, offsetA, Prod.fst_add, Prod.snd_add]
    constructor <;> ring
  · norm_num [surgicalSlopeDiff, zTileLetter, zTileBaseSlope_zero, zTileBaseSlope_one]

/-- Junction `even_F_wv_23`: `P.C -> P.B`. -/
theorem seam_even_F_wv_23 :
    seamLHS .one .zero (cornerAff .C np dp + (pairAffine nq dq 1 0)) (cornerAff .B np dp + (pairAffine np dp 0 1)) =
      surgicalSlopeDiff .vertical false (zTileLetter .one) (zTileLetter .zero) := by
  apply seam_identity .vertical false .one .zero _ _ (1, -1)
  · simp only [cornerAff, pairAffine, offsetA, Prod.fst_add, Prod.snd_add]
    constructor <;> ring
  · norm_num [surgicalSlopeDiff, zTileLetter, zTileBaseSlope_zero, zTileBaseSlope_one]

/-- Junction `even_F_wv_24`: `P.C -> Q.B`. -/
theorem seam_even_F_wv_24 :
    seamLHS .one .zero (cornerAff .C np dp + (pairAffine nq dq 1 0 + pairAffine np dp 0 1)) (cornerAff .B nq dq + (pairAffine np dp 1 0 + pairAffine np dp 0 2)) =
      surgicalSlopeDiff .vertical false (zTileLetter .one) (zTileLetter .zero) := by
  apply seam_identity .vertical false .one .zero _ _ (1, -1)
  · simp only [cornerAff, pairAffine, offsetA, Prod.fst_add, Prod.snd_add]
    constructor <;> ring
  · norm_num [surgicalSlopeDiff, zTileLetter, zTileBaseSlope_zero, zTileBaseSlope_one]

end FLatticePaper.Tiles.SeamIdentities
