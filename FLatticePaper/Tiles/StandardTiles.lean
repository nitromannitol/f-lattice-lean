import FLatticePaper.Farey.RecursionLemmas
import FLatticePaper.Farey.RotationLattice
import FLatticePaper.Construction.BaseCases
import FLatticePaper.Construction.OffsetTables
import FLatticePaper.Construction.BaseCaseRecurrence
import FLatticePaper.Construction.NearOneBaseCases

/-! # Standard tiles and rotation invariance

`def:standard_tiles` of the paper: a standard tile pair is attached to each word of the Farey recursion.

Convention. A tile is a finite set of cells of `Z^2` (`Tile`). `c(T)` is the lower-left vertex: the least height, then
the least abscissa (`lexLE`). A tile is normalised when `c(T) = 0` (`IsNormalised`). The rotation is `R(x) = i·x`
(`mulI`), and on normalised tiles `R(T)` is `i·T` translated back to `c = 0`; this is the convention `c(R T) = c(T)`
of the paper.

Base words. The empty word and the words `3^k`, `2^k` (`k ≥ 1`) take the base tiles of `prop:base_cases`
(`paperStairTile`, `paperLadderTile`, `paperNearStairTile`, `paperNearLadderTile`), normalised to `c = 0` by the
translation `(0, -1)` of the two near-one tiles. Every other word takes the standard decomposition
`eq:standard_decompositions`, with the offsets `eq:offsets_w1_odd` and `eq:offsets_w1_even` in the order of the paper.

Registers. A word is read letter by letter. Each step keeps the pair of parent fractions of the Farey recursion
(`Parents`) together with the tiles of those two parents. The starting tiles `T_{0/1}` and `T_{1/1}` are the zero-one
tiles of the paper. -/

namespace FLatticePaper.Tiles.Standard

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction

/-- A tile: a finite set of cells of `Z^2`. -/
abbrev Tile := Finset Site

/-- The translate of a tile by a vector. -/
def shift (T : Tile) (v : Site) : Tile := T.image (· + v)

/-- The rotation of a tile: `R(x) = i·x = (-y, x)`. -/
def rot (T : Tile) : Tile := T.image mulI

theorem mem_shift {T : Tile} {v x : Site} : x ∈ shift T v ↔ x - v ∈ T := by
  unfold shift
  constructor
  · intro h
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp h
    simpa using hy
  · intro h
    exact Finset.mem_image.mpr ⟨x - v, h, sub_add_cancel x v⟩

theorem mem_rot {T : Tile} {x : Site} : x ∈ rot T ↔ (x.2, -x.1) ∈ T := by
  unfold rot
  constructor
  · intro h
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp h
    simpa [mulI] using hy
  · intro h
    refine Finset.mem_image.mpr ⟨(x.2, -x.1), h, ?_⟩
    simp [mulI]

theorem rot_shift (T : Tile) (v : Site) : rot (shift T v) = shift (rot T) (mulI v) := by
  ext x
  simp only [mem_rot, mem_shift]
  have e : (x.2, -x.1) - v = ((x - mulI v).2, -(x - mulI v).1) := by
    ext
    · simp [mulI]
    · simp [mulI]; ring
  rw [e]

theorem shift_shift (T : Tile) (v w : Site) : shift (shift T v) w = shift T (v + w) := by
  ext x
  simp only [mem_shift]
  rw [sub_sub, add_comm w v]

theorem shift_union (A B : Tile) (v : Site) : shift (A ∪ B) v = shift A v ∪ shift B v := by
  simp [shift, Finset.image_union]

theorem rot_union (A B : Tile) : rot (A ∪ B) = rot A ∪ rot B := by
  simp [rot, Finset.image_union]

/-- The lexicographic order on cells used for the lower-left vertex: height first, then abscissa. -/
def lexLE (p q : Site) : Prop := p.2 < q.2 ∨ (p.2 = q.2 ∧ p.1 ≤ q.1)

/-- A tile is normalised when `c(T) = 0`: the origin is a cell and no cell is below or left of it. -/
def IsNormalised (T : Tile) : Prop := (0 : Site) ∈ T ∧ ∀ p ∈ T, lexLE 0 p

/-- The translation `t(n/d) = c(i·T(n/d))` of the rotation of a normalised tile. -/
def tV (n d : ℤ) : Site := (-(n + d), n + 1 - d)

/-- The rotation translation of a fraction. -/
def tF (f : Fraction) : Site := tV f.num f.den

/-! ### Base tiles of `prop:base_cases` as finite sets

Each base tile is the set of lattice points of the paper's description inside a bounding box. The membership
lemmas below state that the finite set is exactly the paper's set (for `d ≥ 2`). -/

/-- `T_{1/d}` of `lemma:basecase_3k_even_std` (`paperStairTile d`). -/
def stairF (d : ℤ) : Tile :=
  (Finset.Icc (2 - d) d ×ˢ Finset.Icc 0 (d + 1)).filter fun x : Site =>
    (2 - d ≤ x.1 ∧ x.1 ≤ d ∧ 0 ≤ x.2 ∧ x.2 ≤ d + 1 ∧ 1 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ d + 2) ∨
      (x.1 = 0 ∧ x.2 = 0) ∨ (x.1 = 2 ∧ x.2 = d + 1)

/-- `T_{p_1}` of `lemma:basecase_2k_odd_std` (`paperNearStairTile d`), before normalisation. -/
def nstairF (d : ℤ) : Tile :=
  (Finset.Icc 0 (d + 1) ×ˢ Finset.Icc 1 (2 * d - 1)).filter fun x : Site =>
    (0 ≤ x.1 ∧ x.1 ≤ d + 1 ∧ 1 ≤ x.2 ∧ x.2 ≤ 2 * d - 1 ∧ -1 ≤ x.2 - x.1 ∧ x.2 - x.1 ≤ d) ∨
      (x.1 = 0 ∧ x.2 = d + 1) ∨ (x.1 = d + 1 ∧ x.2 = d - 1)

/-- `T_{1/d}` of `lemma:basecase_3k_odd_std` (`paperLadderTile d`). -/
def ladderF (d : ℤ) : Tile :=
  (Finset.Icc (2 - d) (2 * d) ×ˢ Finset.Icc 0 (d + 2)).filter fun x : Site =>
    ((x.1 = 0 ∧ x.2 = 0) ∨ (x.1 = d + 2 ∧ x.2 = d + 2) ∨ (x.1 + x.2 = d + 2 ∧ 1 < x.2 ∧ x.2 < d + 1) ∨
      (2 - d ≤ x.1 ∧ x.1 ≤ 2 * d ∧ 0 ≤ x.2 ∧ x.2 ≤ d + 2 ∧ 1 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ 2 * d + 3)) ∧
    ¬((d ≤ x.1 ∧ x.2 = 0) ∨ (x.1 ≤ 2 ∧ x.2 = d + 2))

/-- `T_{q_1}` of `lemma:basecase_2k_even_std` (`paperNearLadderTile d`), before normalisation. -/
def nladderF (d : ℤ) : Tile :=
  (Finset.Icc (-1) (d + 1) ×ˢ Finset.Icc 1 (3 * d - 1)).filter fun x : Site =>
    ((x.1 = -1 ∧ x.2 = 2 * d + 1) ∨ (x.1 = d + 1 ∧ x.2 = d - 1) ∨ (x.2 - x.1 = d ∧ 0 < x.1 ∧ x.1 < d) ∨
      (-1 ≤ x.1 ∧ x.1 ≤ d + 1 ∧ 1 ≤ x.2 ∧ x.2 ≤ 3 * d - 1 ∧ -1 ≤ x.2 - x.1 ∧ x.2 - x.1 ≤ 2 * d + 1)) ∧
    ¬((x.1 = -1 ∧ x.2 ≤ d + 1) ∨ (x.1 = d + 1 ∧ 2 * d - 1 ≤ x.2))

/-- The near-one staircase of the base word `2^k`, normalised: `c = (0, 1) ↦ (0, 0)`. -/
def nstairN (d : ℤ) : Tile := shift (nstairF d) (0, -1)

/-- The near-one ladder of the base word `2^k`, normalised: `c = (0, 1) ↦ (0, 0)`. -/
def nladderN (d : ℤ) : Tile := shift (nladderF d) (0, -1)

theorem mem_stairF {d : ℤ} (hd : 2 ≤ d) (x : Site) : x ∈ stairF d ↔
    (2 - d ≤ x.1 ∧ x.1 ≤ d ∧ 0 ≤ x.2 ∧ x.2 ≤ d + 1 ∧ 1 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ d + 2) ∨
      (x.1 = 0 ∧ x.2 = 0) ∨ (x.1 = 2 ∧ x.2 = d + 1) := by
  unfold stairF
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    omega

theorem mem_nstairF {d : ℤ} (hd : 2 ≤ d) (x : Site) : x ∈ nstairF d ↔
    (0 ≤ x.1 ∧ x.1 ≤ d + 1 ∧ 1 ≤ x.2 ∧ x.2 ≤ 2 * d - 1 ∧ -1 ≤ x.2 - x.1 ∧ x.2 - x.1 ≤ d) ∨
      (x.1 = 0 ∧ x.2 = d + 1) ∨ (x.1 = d + 1 ∧ x.2 = d - 1) := by
  unfold nstairF
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    omega

theorem mem_ladderF {d : ℤ} (hd : 2 ≤ d) (x : Site) : x ∈ ladderF d ↔
    (((x.1 = 0 ∧ x.2 = 0) ∨ (x.1 = d + 2 ∧ x.2 = d + 2) ∨ (x.1 + x.2 = d + 2 ∧ 1 < x.2 ∧ x.2 < d + 1) ∨
      (2 - d ≤ x.1 ∧ x.1 ≤ 2 * d ∧ 0 ≤ x.2 ∧ x.2 ≤ d + 2 ∧ 1 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ 2 * d + 3)) ∧
    ¬((d ≤ x.1 ∧ x.2 = 0) ∨ (x.1 ≤ 2 ∧ x.2 = d + 2))) := by
  unfold ladderF
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    omega

theorem mem_nladderF {d : ℤ} (hd : 2 ≤ d) (x : Site) : x ∈ nladderF d ↔
    (((x.1 = -1 ∧ x.2 = 2 * d + 1) ∨ (x.1 = d + 1 ∧ x.2 = d - 1) ∨ (x.2 - x.1 = d ∧ 0 < x.1 ∧ x.1 < d) ∨
      (-1 ≤ x.1 ∧ x.1 ≤ d + 1 ∧ 1 ≤ x.2 ∧ x.2 ≤ 3 * d - 1 ∧ -1 ≤ x.2 - x.1 ∧ x.2 - x.1 ≤ 2 * d + 1)) ∧
    ¬((x.1 = -1 ∧ x.2 ≤ d + 1) ∨ (x.1 = d + 1 ∧ 2 * d - 1 ≤ x.2))) := by
  unfold nladderF
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    omega

/-! ### Base-family rotation identities

For each base tile `T` of the paper, `R(T)` is the translate of the complementary base tile by `t(n/d)`. These are the
identities behind the base words `2^k`, `3^k` and the empty word. -/

theorem base_stair_nstair {d : ℤ} (hd : 2 ≤ d) : rot (stairF d) = shift (nstairN d) (tV 1 d) := by
  ext x
  simp only [mem_rot, mem_shift, nstairN, mem_stairF hd, mem_nstairF hd, tV, Prod.fst_sub, Prod.snd_sub]
  constructor <;> intro h <;> omega

theorem base_nstair_stair {d : ℤ} (hd : 2 ≤ d) : rot (nstairN d) = shift (stairF d) (-d, 0) := by
  ext x
  simp only [mem_rot, mem_shift, nstairN, mem_stairF hd, mem_nstairF hd, Prod.fst_sub, Prod.snd_sub]
  constructor <;> intro h <;> omega

theorem base_ladder_nladder {d : ℤ} (hd : 2 ≤ d) : rot (ladderF d) = shift (nladderN d) (tV 1 d) := by
  ext x
  simp only [mem_rot, mem_shift, nladderN, mem_ladderF hd, mem_nladderF hd, tV, Prod.fst_sub, Prod.snd_sub]
  constructor <;> intro h <;> omega

theorem base_nladder_ladder {d : ℤ} (hd : 2 ≤ d) :
    rot (nladderN d) = shift (ladderF d) (tV (d - 1) (d + 1)) := by
  ext x
  simp only [mem_rot, mem_shift, nladderN, mem_ladderF hd, mem_nladderF hd, tV, Prod.fst_sub, Prod.snd_sub]
  constructor <;> intro h <;> omega

/-! ### The standard decomposition (`eq:standard_decompositions`) -/

/-- The odd child `T(p_0)`. The first argument is `true` when the number of `1`s of the word is odd, which selects
`eq:offsets_w1_odd`; `false` selects `eq:offsets_w1_even`. `T1` and `T2` are the tiles of the parents `p` and `q`;
`T^d(q)` is `T(q) ∪ (T(q) + v_{q,1})`, the doubled tile of `eq:doubled_tiles`. -/
def oddChildB : Bool → Tile → Tile → Fraction → Fraction → Tile
  | true, T1, T2, p, q =>
      shift T2 (texV1Odd p) ∪ shift T2 (texV1Odd p + texV1Even q) ∪ shift T2 (texV2 p) ∪
        shift T2 (texV2 p + texV1Even q) ∪ T1 ∪ shift T1 (texV1Even q + texV1Even q + texV2 q)
  | false, T1, T2, p, q =>
      T2 ∪ shift T2 (texV1Even q) ∪ shift T2 (texV1Odd p + texV2 p) ∪
        shift T2 (texV1Odd p + texV2 p + texV1Even q) ∪ shift T1 (texV1Even q + texV1Even q) ∪ shift T1 (texV2 q)

/-- The even child `T(q_0)`, with the same convention as `oddChildB`; `T^d(p) = T(p) ∪ (T(p) + v_{p,2})`. -/
def evenChildB : Bool → Tile → Tile → Fraction → Fraction → Tile
  | true, T1, T2, p, q =>
      shift T2 (texV1Odd p) ∪ shift T2 (texV2 p + texV2 p) ∪ T1 ∪ shift T1 (texV2 p) ∪
        shift T1 (texV1Even q + texV2 q) ∪ shift T1 (texV1Even q + texV2 q + texV2 p)
  | false, T1, T2, p, q =>
      T2 ∪ shift T2 (texV1Odd p + (texV2 p + texV2 p)) ∪ shift T1 (texV1Even q) ∪
        shift T1 (texV1Even q + texV2 p) ∪ shift T1 (texV2 q) ∪ shift T1 (texV2 q + texV2 p)

theorem rotate_eq_of_odd {p : Fraction} (hp : p.Odd) : p.rotate = ⟨p.den - p.num, p.den + p.num⟩ :=
  Fraction.rotate_of_odd hp

theorem rotate_eq_of_even {q : Fraction} (hq : q.Even) :
    q.rotate = ⟨(q.den - q.num) / 2, (q.den + q.num) / 2⟩ :=
  Fraction.rotate_of_even hq

/-! ### Rotation of the decomposition

Each identity below pairs a translate of a parent tile on one side with a translate of a parent tile of the rotated
word on the other side. The pairing is the one used by the paper's offset tables; each offset identity is an
identity of integer linear forms in the entries of the parents (with the parity of the parents). -/

theorem rot_oddChild_true (T1 T2 T1s T2s : Tile) (p q : Fraction) (hp : p.Odd) (hq : q.Even)
    (h1 : rot T1 = shift T2s (tF p)) (h2 : rot T2 = shift T1s (tF q)) :
    rot (oddChildB true T1 T2 p q) =
      shift (evenChildB true T1s T2s q.rotate p.rotate) (tF ⟨p.num + q.num, p.den + q.den⟩) := by
  have hp' : (p.num + p.den) % 2 = 1 := hp
  have hq' : (q.num + q.den) % 2 = 0 := hq
  have e6 : tF p + mulI (texV1Even q + texV1Even q + texV2 q) =
      texV2 q.rotate + texV2 q.rotate + tF ⟨p.num + q.num, p.den + q.den⟩ := by
    simp only [rotate_eq_of_even hq, tF, tV, texV1Even, texV2, mulI, Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> omega
  have e5 : tF p = texV1Odd q.rotate + tF ⟨p.num + q.num, p.den + q.den⟩ := by
    simp only [rotate_eq_of_even hq, tF, tV, texV1Odd, Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> omega
  have e1 : tF q + mulI (texV1Odd p) =
      texV1Even p.rotate + texV2 p.rotate + tF ⟨p.num + q.num, p.den + q.den⟩ := by
    simp only [rotate_eq_of_odd hp, tF, tV, texV1Even, texV2, texV1Odd, mulI, Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> omega
  have e2 : tF q + mulI (texV1Odd p + texV1Even q) =
      texV1Even p.rotate + texV2 p.rotate + texV2 q.rotate + tF ⟨p.num + q.num, p.den + q.den⟩ := by
    simp only [rotate_eq_of_odd hp, rotate_eq_of_even hq, tF, tV, texV1Even, texV2, texV1Odd, mulI,
      Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> omega
  have e3 : tF q + mulI (texV2 p) = tF ⟨p.num + q.num, p.den + q.den⟩ := by
    simp only [tF, tV, texV2, mulI, Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> omega
  have e4 : tF q + mulI (texV2 p + texV1Even q) = texV2 q.rotate + tF ⟨p.num + q.num, p.den + q.den⟩ := by
    simp only [rotate_eq_of_even hq, tF, tV, texV1Even, texV2, mulI, Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> omega
  simp only [oddChildB, evenChildB, rot_union, rot_shift, h1, h2, shift_union, shift_shift]
  rw [e6, e5, e1, e2, e3, e4]
  ext x
  simp only [Finset.mem_union, mem_shift]
  tauto

theorem rot_oddChild_false (T1 T2 T1s T2s : Tile) (p q : Fraction) (hp : p.Odd) (hq : q.Even)
    (h1 : rot T1 = shift T2s (tF p)) (h2 : rot T2 = shift T1s (tF q)) :
    rot (oddChildB false T1 T2 p q) =
      shift (evenChildB false T1s T2s q.rotate p.rotate) (tF ⟨p.num + q.num, p.den + q.den⟩) := by
  have hp' : (p.num + p.den) % 2 = 1 := hp
  have hq' : (q.num + q.den) % 2 = 0 := hq
  have f5 : tF p + mulI (texV1Even q + texV1Even q) =
      texV1Odd q.rotate + (texV2 q.rotate + texV2 q.rotate) + tF ⟨p.num + q.num, p.den + q.den⟩ := by
    simp only [rotate_eq_of_even hq, tF, tV, texV1Even, texV1Odd, texV2, mulI, Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> omega
  have f6 : tF p + mulI (texV2 q) = tF ⟨p.num + q.num, p.den + q.den⟩ := by
    simp only [tF, tV, texV2, mulI, Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> omega
  have f4 : tF q + mulI (texV1Odd p + texV2 p + texV1Even q) =
      texV2 p.rotate + texV2 q.rotate + tF ⟨p.num + q.num, p.den + q.den⟩ := by
    simp only [rotate_eq_of_odd hp, rotate_eq_of_even hq, tF, tV, texV1Even, texV2, texV1Odd, mulI,
      Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> omega
  have f3 : tF q + mulI (texV1Odd p + texV2 p) = texV2 p.rotate + tF ⟨p.num + q.num, p.den + q.den⟩ := by
    simp only [rotate_eq_of_odd hp, tF, tV, texV2, texV1Odd, mulI, Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> omega
  have f2 : tF q + mulI (texV1Even q) =
      texV1Even p.rotate + texV2 q.rotate + tF ⟨p.num + q.num, p.den + q.den⟩ := by
    simp only [rotate_eq_of_odd hp, rotate_eq_of_even hq, tF, tV, texV1Even, texV2, mulI, Prod.mk_add_mk,
      Prod.mk.injEq]
    constructor <;> omega
  have f1 : tF q = texV1Even p.rotate + tF ⟨p.num + q.num, p.den + q.den⟩ := by
    simp only [rotate_eq_of_odd hp, tF, tV, texV1Even, Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> omega
  simp only [oddChildB, evenChildB, rot_union, rot_shift, h1, h2, shift_union, shift_shift]
  rw [f5, f6, f4, f3, f2, f1]
  ext x
  simp only [Finset.mem_union, mem_shift]
  tauto

theorem rot_evenChild_true (T1 T2 T1s T2s : Tile) (p q : Fraction) (hp : p.Odd) (hq : q.Even)
    (h1 : rot T1 = shift T2s (tF p)) (h2 : rot T2 = shift T1s (tF q)) :
    rot (evenChildB true T1 T2 p q) =
      shift (oddChildB true T1s T2s q.rotate p.rotate) (tF ⟨2 * p.num + q.num, 2 * p.den + q.den⟩) := by
  have hp' : (p.num + p.den) % 2 = 1 := hp
  have hq' : (q.num + q.den) % 2 = 0 := hq
  have q4 : tF p + mulI (texV2 p) = texV1Odd q.rotate + tF ⟨2 * p.num + q.num, 2 * p.den + q.den⟩ := by
    simp only [rotate_eq_of_even hq, tF, tV, texV1Odd, texV2, mulI, Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> omega
  have q5 : tF p + mulI (texV1Even q + texV2 q) =
      texV2 q.rotate + texV1Even p.rotate + tF ⟨2 * p.num + q.num, 2 * p.den + q.den⟩ := by
    simp only [rotate_eq_of_even hq, rotate_eq_of_odd hp, tF, tV, texV1Even, texV2, mulI, Prod.mk_add_mk,
      Prod.mk.injEq]
    constructor <;> omega
  have q6 : tF p + mulI (texV1Even q + texV2 q + texV2 p) =
      texV2 q.rotate + tF ⟨2 * p.num + q.num, 2 * p.den + q.den⟩ := by
    simp only [rotate_eq_of_even hq, tF, tV, texV1Even, texV2, mulI, Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> omega
  have q3 : tF p = texV1Odd q.rotate + texV1Even p.rotate + tF ⟨2 * p.num + q.num, 2 * p.den + q.den⟩ := by
    simp only [rotate_eq_of_even hq, rotate_eq_of_odd hp, tF, tV, texV1Odd, texV1Even, Prod.mk_add_mk,
      Prod.mk.injEq]
    constructor <;> omega
  have q1 : tF q + mulI (texV1Odd p) =
      texV1Even p.rotate + texV1Even p.rotate + texV2 p.rotate + tF ⟨2 * p.num + q.num, 2 * p.den + q.den⟩ := by
    simp only [rotate_eq_of_odd hp, tF, tV, texV1Even, texV2, texV1Odd, mulI, Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> omega
  have q2 : tF q + mulI (texV2 p + texV2 p) = tF ⟨2 * p.num + q.num, 2 * p.den + q.den⟩ := by
    simp only [tF, tV, texV2, mulI, Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> omega
  simp only [oddChildB, evenChildB, rot_union, rot_shift, h1, h2, shift_union, shift_shift]
  rw [q4, q5, q6, q3, q1, q2]
  ext x
  simp only [Finset.mem_union, mem_shift]
  tauto

theorem rot_evenChild_false (T1 T2 T1s T2s : Tile) (p q : Fraction) (hp : p.Odd) (hq : q.Even)
    (h1 : rot T1 = shift T2s (tF p)) (h2 : rot T2 = shift T1s (tF q)) :
    rot (evenChildB false T1 T2 p q) =
      shift (oddChildB false T1s T2s q.rotate p.rotate) (tF ⟨2 * p.num + q.num, 2 * p.den + q.den⟩) := by
  have hp' : (p.num + p.den) % 2 = 1 := hp
  have hq' : (q.num + q.den) % 2 = 0 := hq
  have j2 : tF q + mulI (texV1Odd p + (texV2 p + texV2 p)) =
      texV2 p.rotate + tF ⟨2 * p.num + q.num, 2 * p.den + q.den⟩ := by
    simp only [rotate_eq_of_odd hp, tF, tV, texV1Odd, texV2, mulI, Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> omega
  have j3 : tF p + mulI (texV1Even q) =
      texV1Odd q.rotate + texV2 q.rotate + texV1Even p.rotate + tF ⟨2 * p.num + q.num, 2 * p.den + q.den⟩ := by
    simp only [rotate_eq_of_odd hp, rotate_eq_of_even hq, tF, tV, texV1Even, texV1Odd, texV2, mulI,
      Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> omega
  have j4 : tF p + mulI (texV1Even q + texV2 p) =
      texV1Odd q.rotate + texV2 q.rotate + tF ⟨2 * p.num + q.num, 2 * p.den + q.den⟩ := by
    simp only [rotate_eq_of_even hq, tF, tV, texV1Even, texV1Odd, texV2, mulI, Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> omega
  have j5 : tF p + mulI (texV2 q) = texV1Even p.rotate + tF ⟨2 * p.num + q.num, 2 * p.den + q.den⟩ := by
    simp only [rotate_eq_of_odd hp, tF, tV, texV1Even, texV2, mulI, Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> omega
  have j6 : tF p + mulI (texV2 q + texV2 p) = tF ⟨2 * p.num + q.num, 2 * p.den + q.den⟩ := by
    simp only [tF, tV, texV2, mulI, Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> omega
  have j1 : tF q = texV1Even p.rotate + texV1Even p.rotate + tF ⟨2 * p.num + q.num, 2 * p.den + q.den⟩ := by
    simp only [rotate_eq_of_odd hp, tF, tV, texV1Even, Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> omega
  simp only [oddChildB, evenChildB, rot_union, rot_shift, h1, h2, shift_union, shift_shift]
  rw [j2, j3, j4, j5, j6, j1]
  ext x
  simp only [Finset.mem_union, mem_shift]
  tauto

/-- The rotation of the odd child, for either parity of the number of `1`s. -/
theorem rot_oddChild (b : Bool) (T1 T2 T1s T2s : Tile) (p q : Fraction) (hp : p.Odd) (hq : q.Even)
    (h1 : rot T1 = shift T2s (tF p)) (h2 : rot T2 = shift T1s (tF q)) :
    rot (oddChildB b T1 T2 p q) =
      shift (evenChildB b T1s T2s q.rotate p.rotate) (tF ⟨p.num + q.num, p.den + q.den⟩) := by
  cases b
  · exact rot_oddChild_false T1 T2 T1s T2s p q hp hq h1 h2
  · exact rot_oddChild_true T1 T2 T1s T2s p q hp hq h1 h2

/-- The rotation of the even child, for either parity of the number of `1`s. -/
theorem rot_evenChild (b : Bool) (T1 T2 T1s T2s : Tile) (p q : Fraction) (hp : p.Odd) (hq : q.Even)
    (h1 : rot T1 = shift T2s (tF p)) (h2 : rot T2 = shift T1s (tF q)) :
    rot (evenChildB b T1 T2 p q) =
      shift (oddChildB b T1s T2s q.rotate p.rotate) (tF ⟨2 * p.num + q.num, 2 * p.den + q.den⟩) := by
  cases b
  · exact rot_evenChild_false T1 T2 T1s T2s p q hp hq h1 h2
  · exact rot_evenChild_true T1 T2 T1s T2s p q hp hq h1 h2

/-! ### Registers, states and the standard tiles of a word -/

/-- The state of a word: its parent pair (`Parents`) and the tiles of its two parents. -/
structure TState where
  par : Parents
  tOdd : Tile
  tEven : Tile

/-- The zero-one tile `T_{0/1}` of `subsec:zero-one-tiles`; it initialises the registers only. -/
def zeroTile : Tile := {(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)}

/-- The zero-one tile `T_{1/1}` of `subsec:zero-one-tiles`; it initialises the registers only. -/
def oneTile : Tile := {(0, 0), (0, 1), (1, 0), (1, 1)}

/-- The state of the empty word: the parents `0/1`, `1/1` with their zero-one tiles. -/
def initState : TState := ⟨root, zeroTile, oneTile⟩

/-- The base words of `prop:base_cases`: the empty word, and the words `3^k` and `2^k` (`k ≥ 1`). -/
abbrev IsBase (w : Word) : Prop :=
  w = [] ∨ (∀ d ∈ w, d = Digit.three) ∨ (∀ d ∈ w, d = Digit.two)

/-- The standard tiles of the two children of the parent pair of `w`, from the state `s` of `w`. -/
def childTiles (w : Word) (s : TState) : Tile × Tile :=
  if w = [] then (nstairN 3, stairF 3)
  else if w = List.replicate w.length Digit.three then
    (ladderF (2 * (w.length : ℤ) + 2), stairF (2 * (w.length : ℤ) + 3))
  else if w = List.replicate w.length Digit.two then
    (nstairN (2 * (w.length : ℤ) + 3), nladderN (2 * (w.length : ℤ) + 2))
  else
    (oddChildB (phase w == 1) s.tOdd s.tEven s.par.odd s.par.even,
      evenChildB (phase w == 1) s.tOdd s.tEven s.par.odd s.par.even)

/-- One letter: the parent pair advances by `Parents.step`; the register of each replaced parent receives the
corresponding child tile. -/
def stepState (pre : Word) (s : TState) (d : Digit) : TState :=
  match d with
  | .one => ⟨s.par.step .one, (childTiles pre s).1, (childTiles pre s).2⟩
  | .two => ⟨s.par.step .two, (childTiles pre s).1, s.tEven⟩
  | .three => ⟨s.par.step .three, s.tOdd, (childTiles pre s).2⟩

/-- Reads the letters of a word after the prefix `pre`. -/
def runFrom (pre : Word) : Word → TState → TState
  | [], s => s
  | d :: rest, s => runFrom (pre ++ [d]) rest (stepState pre s d)

/-- The state after reading a word. -/
def stateAt (w : Word) : TState := runFrom [] w initState

/-- The standard tile of the odd child of the parent pair of `w`. -/
def oddTile (w : Word) : Tile := (childTiles w (stateAt w)).1

/-- The standard tile of the even child of the parent pair of `w`. -/
def evenTile (w : Word) : Tile := (childTiles w (stateAt w)).2

/-- The word with `2` and `3` exchanged (the rotation of the Farey recursion). -/
def swapW (w : Word) : Word := w.map Digit.swapTwoThree

/-- The rotation identities of the two children of `w`: `R` of the odd child is the even child of `swapW w`,
and `R` of the even child is the odd child of `swapW w`, each translated by `t(n/d)`. -/
abbrev ChildRot (w : Word) : Prop :=
  rot (oddTile w) = shift (evenTile (swapW w)) (tF ((parentsAt w).current .odd)) ∧
    rot (evenTile w) = shift (oddTile (swapW w)) (tF ((parentsAt w).current .even))

/-- The register identity of the odd parent of `w` (vacuous when `w` consists of threes). -/
abbrev GoodOdd (w : Word) : Prop :=
  (∀ d ∈ w, d = Digit.three) ∨
    rot (stateAt w).tOdd = shift (stateAt (swapW w)).tEven (tF (parentsAt w).odd)

/-- The register identity of the even parent of `w` (vacuous when `w` consists of twos). -/
abbrev GoodEven (w : Word) : Prop :=
  (∀ d ∈ w, d = Digit.two) ∨
    rot (stateAt w).tEven = shift (stateAt (swapW w)).tOdd (tF (parentsAt w).even)

theorem runFrom_snoc (pre : Word) (s : TState) (rest : Word) (d : Digit) :
    runFrom pre (rest ++ [d]) s = stepState (pre ++ rest) (runFrom pre rest s) d := by
  induction rest generalizing pre s with
  | nil => simp [runFrom]
  | cons e rest ih =>
    show runFrom (pre ++ [e]) (rest ++ [d]) (stepState pre s e) =
      stepState (pre ++ (e :: rest)) (runFrom (pre ++ [e]) rest (stepState pre s e)) d
    rw [ih]
    simp [List.append_assoc]

theorem stateAt_snoc (u : Word) (d : Digit) : stateAt (u ++ [d]) = stepState u (stateAt u) d := by
  unfold stateAt
  rw [runFrom_snoc]
  simp

theorem runFrom_par (pre : Word) (s : TState) (rest : Word) :
    (runFrom pre rest s).par = s.par.walk rest := by
  induction rest generalizing pre s with
  | nil => rfl
  | cons d rest ih =>
    show (runFrom (pre ++ [d]) rest (stepState pre s d)).par = s.par.walk (d :: rest)
    rw [ih, Parents.walk_cons]
    cases d <;> rfl

theorem stateAt_par (w : Word) : (stateAt w).par = parentsAt w := by
  unfold stateAt parentsAt
  rw [runFrom_par]
  rfl

theorem tOdd_snoc_one (u : Word) : (stateAt (u ++ [.one])).tOdd = oddTile u := by
  rw [stateAt_snoc]; rfl

theorem tEven_snoc_one (u : Word) : (stateAt (u ++ [.one])).tEven = evenTile u := by
  rw [stateAt_snoc]; rfl

theorem tOdd_snoc_two (u : Word) : (stateAt (u ++ [.two])).tOdd = oddTile u := by
  rw [stateAt_snoc]; rfl

theorem tEven_snoc_two (u : Word) : (stateAt (u ++ [.two])).tEven = (stateAt u).tEven := by
  rw [stateAt_snoc]; rfl

theorem tOdd_snoc_three (u : Word) : (stateAt (u ++ [.three])).tOdd = (stateAt u).tOdd := by
  rw [stateAt_snoc]; rfl

theorem tEven_snoc_three (u : Word) : (stateAt (u ++ [.three])).tEven = evenTile u := by
  rw [stateAt_snoc]; rfl

theorem swapW_snoc_one (u : Word) : swapW (u ++ [.one]) = swapW u ++ [.one] := by
  simp [swapW, Digit.swapTwoThree]

theorem swapW_snoc_two (u : Word) : swapW (u ++ [.two]) = swapW u ++ [.three] := by
  simp [swapW, Digit.swapTwoThree]

theorem swapW_snoc_three (u : Word) : swapW (u ++ [.three]) = swapW u ++ [.two] := by
  simp [swapW, Digit.swapTwoThree]

theorem goodOdd_snoc_one {u : Word} (hC : ChildRot u) : GoodOdd (u ++ [.one]) := by
  refine Or.inr ?_
  rw [tOdd_snoc_one, swapW_snoc_one, tEven_snoc_one, parentsAt_append_singleton]
  exact hC.1

theorem goodEven_snoc_one {u : Word} (hC : ChildRot u) : GoodEven (u ++ [.one]) := by
  refine Or.inr ?_
  rw [tEven_snoc_one, swapW_snoc_one, tOdd_snoc_one, parentsAt_append_singleton]
  exact hC.2

theorem goodOdd_snoc_two {u : Word} (hC : ChildRot u) : GoodOdd (u ++ [.two]) := by
  refine Or.inr ?_
  rw [tOdd_snoc_two, swapW_snoc_two, tEven_snoc_three, parentsAt_append_singleton]
  exact hC.1

theorem goodEven_snoc_two {u : Word} (hG : GoodEven u) : GoodEven (u ++ [.two]) := by
  rcases hG with h | h
  · refine Or.inl ?_
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact h d hd
    · rw [List.mem_singleton.mp hd]
  · refine Or.inr ?_
    rw [tEven_snoc_two, swapW_snoc_two, tOdd_snoc_three, parentsAt_append_singleton]
    exact h

theorem goodOdd_snoc_three {u : Word} (hG : GoodOdd u) : GoodOdd (u ++ [.three]) := by
  rcases hG with h | h
  · refine Or.inl ?_
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact h d hd
    · rw [List.mem_singleton.mp hd]
  · refine Or.inr ?_
    rw [tOdd_snoc_three, swapW_snoc_three, tEven_snoc_two, parentsAt_append_singleton]
    exact h

theorem goodEven_snoc_three {u : Word} (hC : ChildRot u) : GoodEven (u ++ [.three]) := by
  refine Or.inr ?_
  rw [tEven_snoc_three, swapW_snoc_three, tOdd_snoc_two, parentsAt_append_singleton]
  exact hC.2

/-! ### Tiles of the base words and of the non-base words -/

theorem childTiles_nil (s : TState) : childTiles [] s = (nstairN 3, stairF 3) := by
  simp [childTiles]

theorem childTiles_of_not_base {w : Word} (hw : ¬ IsBase w) (s : TState) :
    childTiles w s = (oddChildB (phase w == 1) s.tOdd s.tEven s.par.odd s.par.even,
      evenChildB (phase w == 1) s.tOdd s.tEven s.par.odd s.par.even) := by
  have h0 : w ≠ [] := fun h => hw (Or.inl h)
  have h3 : w ≠ List.replicate w.length Digit.three := fun h =>
    hw (Or.inr (Or.inl fun d hd => (List.eq_replicate_iff.mp h).2 d hd))
  have h2 : w ≠ List.replicate w.length Digit.two := fun h =>
    hw (Or.inr (Or.inr fun d hd => (List.eq_replicate_iff.mp h).2 d hd))
  unfold childTiles
  rw [if_neg h0, if_neg h3, if_neg h2]

theorem childTiles_three {k : ℕ} (hk : 1 ≤ k) (s : TState) :
    childTiles (List.replicate k Digit.three) s =
      (ladderF (2 * (k : ℤ) + 2), stairF (2 * (k : ℤ) + 3)) := by
  have h0 : List.replicate k Digit.three ≠ [] := by
    intro h
    have := congrArg List.length h
    simp at this
    omega
  unfold childTiles
  rw [if_neg h0]
  simp

theorem childTiles_two {k : ℕ} (hk : 1 ≤ k) (s : TState) :
    childTiles (List.replicate k Digit.two) s =
      (nstairN (2 * (k : ℤ) + 3), nladderN (2 * (k : ℤ) + 2)) := by
  have h0 : List.replicate k Digit.two ≠ [] := by
    intro h
    have := congrArg List.length h
    simp at this
    omega
  have h3 : List.replicate k Digit.two ≠ List.replicate k Digit.three := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    simp [List.replicate_succ]
  unfold childTiles
  rw [if_neg h0, List.length_replicate, if_neg h3]
  simp

theorem oddTile_eq_of_not_base {u : Word} (hu : ¬ IsBase u) :
    oddTile u = oddChildB (phase u == 1) (stateAt u).tOdd (stateAt u).tEven (parentsAt u).odd (parentsAt u).even := by
  unfold oddTile
  rw [childTiles_of_not_base hu, stateAt_par]

theorem evenTile_eq_of_not_base {u : Word} (hu : ¬ IsBase u) :
    evenTile u = evenChildB (phase u == 1) (stateAt u).tOdd (stateAt u).tEven (parentsAt u).odd (parentsAt u).even := by
  unfold evenTile
  rw [childTiles_of_not_base hu, stateAt_par]

theorem nonbase_swap {w : Word} (hw : ¬ IsBase w) : ¬ IsBase (swapW w) := by
  rintro (h | h | h)
  · exact hw (Or.inl (List.map_eq_nil_iff.mp h))
  · refine hw (Or.inr (Or.inr fun d hd => ?_))
    have := h _ (List.mem_map_of_mem (f := Digit.swapTwoThree) hd)
    cases d <;> simp_all [Digit.swapTwoThree]
  · refine hw (Or.inr (Or.inl fun d hd => ?_))
    have := h _ (List.mem_map_of_mem (f := Digit.swapTwoThree) hd)
    cases d <;> simp_all [Digit.swapTwoThree]

theorem parentsAt_swapW (w : Word) : parentsAt (swapW w) = (parentsAt w).rotate :=
  (rotate_parentsAt w).symm

theorem phase_swapW (w : Word) : phase (swapW w) = phase w :=
  phase_rotate_word w

/-- The tile of the odd child of the swapped word, in the form used by the rotation identity. -/
theorem oddTile_swapW {w : Word} (hsw : ¬ IsBase (swapW w)) :
    oddTile (swapW w) = oddChildB (phase w == 1) (stateAt (swapW w)).tOdd (stateAt (swapW w)).tEven
      (parentsAt w).even.rotate (parentsAt w).odd.rotate := by
  rw [oddTile_eq_of_not_base hsw, phase_swapW, parentsAt_swapW]
  rfl

theorem evenTile_swapW {w : Word} (hsw : ¬ IsBase (swapW w)) :
    evenTile (swapW w) = evenChildB (phase w == 1) (stateAt (swapW w)).tOdd (stateAt (swapW w)).tEven
      (parentsAt w).even.rotate (parentsAt w).odd.rotate := by
  rw [evenTile_eq_of_not_base hsw, phase_swapW, parentsAt_swapW]
  rfl

theorem current_odd_eq (P : Parents) :
    P.current .odd = ⟨P.odd.num + P.even.num, P.odd.den + P.even.den⟩ := by
  simp [Parents.current, Parents.combine]

theorem current_even_eq (P : Parents) :
    P.current .even = ⟨2 * P.odd.num + P.even.num, 2 * P.odd.den + P.even.den⟩ := by
  simp [Parents.current, Parents.combine]

/-- The rotation identities for a word that is not a base word, from the register identities. -/
theorem childRot_of_not_base {w : Word} (hw : ¬ IsBase w) (hO : GoodOdd w) (hE : GoodEven w) : ChildRot w := by
  have h3 : ¬ ∀ d ∈ w, d = Digit.three := fun h => hw (Or.inr (Or.inl h))
  have h2 : ¬ ∀ d ∈ w, d = Digit.two := fun h => hw (Or.inr (Or.inr h))
  have hO' := hO.resolve_left h3
  have hE' := hE.resolve_left h2
  have hV := parentsAt_valid w
  have hsw : ¬ IsBase (swapW w) := nonbase_swap hw
  unfold ChildRot
  refine ⟨?_, ?_⟩
  · rw [oddTile_eq_of_not_base hw, evenTile_swapW hsw, current_odd_eq]
    exact rot_oddChild _ _ _ _ _ _ _ hV.odd_parity hV.even_parity hO' hE'
  · rw [evenTile_eq_of_not_base hw, oddTile_swapW hsw, current_even_eq]
    exact rot_evenChild _ _ _ _ _ _ _ hV.odd_parity hV.even_parity hO' hE'

/-! ### The base words -/

theorem tF_rotate_odd_one {d : ℤ} (hd : d % 2 = 1) : tF ((⟨1, d⟩ : Fraction).rotate) = (-d, 0) := by
  have h : ((⟨1, d⟩ : Fraction).num + (⟨1, d⟩ : Fraction).den) % 2 = 0 := by
    show (1 + d) % 2 = 0
    omega
  rw [Fraction.rotate_of_even h]
  simp only [tF, tV, Prod.mk.injEq]
  constructor <;> omega

theorem tF_rotate_even_one {d : ℤ} (hd : d % 2 = 0) :
    tF ((⟨1, d⟩ : Fraction).rotate) = tV (d - 1) (d + 1) := by
  have h : ((⟨1, d⟩ : Fraction).num + (⟨1, d⟩ : Fraction).den) % 2 = 1 := by
    show (1 + d) % 2 = 1
    omega
  rw [Fraction.rotate_of_odd h]
  rfl

theorem childRot_nil : ChildRot [] := by
  have hc1 : (parentsAt []).current .odd = ⟨1, 2⟩ := rfl
  have hc2 : (parentsAt []).current .even = ⟨1, 3⟩ := rfl
  have ho : oddTile [] = nstairN 3 := by
    unfold oddTile; rw [childTiles_nil]
  have he : evenTile [] = stairF 3 := by
    unfold evenTile; rw [childTiles_nil]
  unfold ChildRot
  rw [show swapW [] = [] from rfl, ho, he, hc1, hc2]
  refine ⟨?_, ?_⟩
  · have ht : tF ⟨1, 2⟩ = (-3, 0) := by norm_num [tF, tV]
    rw [ht, base_nstair_stair (d := 3) (by norm_num)]
  · exact base_stair_nstair (d := 3) (by norm_num)

theorem childRot_three {k : ℕ} (hk : 1 ≤ k) : ChildRot (List.replicate k Digit.three) := by
  have hs : swapW (List.replicate k Digit.three) = List.replicate k Digit.two := by
    simp [swapW, Digit.swapTwoThree, List.map_replicate]
  have ho : oddTile (List.replicate k Digit.three) = ladderF (2 * (k : ℤ) + 2) := by
    unfold oddTile; rw [childTiles_three hk]
  have he : evenTile (List.replicate k Digit.three) = stairF (2 * (k : ℤ) + 3) := by
    unfold evenTile; rw [childTiles_three hk]
  have ho' : oddTile (List.replicate k Digit.two) = nstairN (2 * (k : ℤ) + 3) := by
    unfold oddTile; rw [childTiles_two hk]
  have he' : evenTile (List.replicate k Digit.two) = nladderN (2 * (k : ℤ) + 2) := by
    unfold evenTile; rw [childTiles_two hk]
  have hc1 : (parentsAt (List.replicate k Digit.three)).current .odd = ⟨1, 2 * (k : ℤ) + 2⟩ :=
    (baseChildren_threes k).2
  have hc2 : (parentsAt (List.replicate k Digit.three)).current .even = ⟨1, 2 * (k : ℤ) + 3⟩ :=
    (baseChildren_threes k).1
  unfold ChildRot
  rw [hs, ho, he, ho', he', hc1, hc2]
  exact ⟨base_ladder_nladder (d := 2 * (k : ℤ) + 2) (by omega),
    base_stair_nstair (d := 2 * (k : ℤ) + 3) (by omega)⟩

theorem childRot_two {k : ℕ} (hk : 1 ≤ k) : ChildRot (List.replicate k Digit.two) := by
  have hs : swapW (List.replicate k Digit.two) = List.replicate k Digit.three := by
    simp [swapW, Digit.swapTwoThree, List.map_replicate]
  have ho : oddTile (List.replicate k Digit.two) = nstairN (2 * (k : ℤ) + 3) := by
    unfold oddTile; rw [childTiles_two hk]
  have he : evenTile (List.replicate k Digit.two) = nladderN (2 * (k : ℤ) + 2) := by
    unfold evenTile; rw [childTiles_two hk]
  have ho' : oddTile (List.replicate k Digit.three) = ladderF (2 * (k : ℤ) + 2) := by
    unfold oddTile; rw [childTiles_three hk]
  have he' : evenTile (List.replicate k Digit.three) = stairF (2 * (k : ℤ) + 3) := by
    unfold evenTile; rw [childTiles_three hk]
  have hc1 : (parentsAt (List.replicate k Digit.two)).current .odd = Fraction.rotate ⟨1, 2 * (k : ℤ) + 3⟩ :=
    (baseChildren_twos k).1
  have hc2 : (parentsAt (List.replicate k Digit.two)).current .even = Fraction.rotate ⟨1, 2 * (k : ℤ) + 2⟩ :=
    (baseChildren_twos k).2
  unfold ChildRot
  rw [hs, ho, he, ho', he', hc1, hc2]
  refine ⟨?_, ?_⟩
  · rw [base_nstair_stair (d := 2 * (k : ℤ) + 3) (by omega),
      tF_rotate_odd_one (d := 2 * (k : ℤ) + 3) (by omega)]
  · rw [base_nladder_ladder (d := 2 * (k : ℤ) + 2) (by omega),
      tF_rotate_even_one (d := 2 * (k : ℤ) + 2) (by omega)]

theorem childRot_of_good (w : Word) (hO : GoodOdd w) (hE : GoodEven w) : ChildRot w := by
  by_cases h0 : w = []
  · subst h0
    exact childRot_nil
  by_cases h3 : ∀ d ∈ w, d = Digit.three
  · obtain ⟨k, rfl⟩ : ∃ k, w = List.replicate k Digit.three :=
      ⟨w.length, List.eq_replicate_iff.mpr ⟨rfl, h3⟩⟩
    have hk : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at h0
      · exact hk
    exact childRot_three hk
  by_cases h2 : ∀ d ∈ w, d = Digit.two
  · obtain ⟨k, rfl⟩ : ∃ k, w = List.replicate k Digit.two :=
      ⟨w.length, List.eq_replicate_iff.mpr ⟨rfl, h2⟩⟩
    have hk : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at h0
      · exact hk
    exact childRot_two hk
  have hw : ¬ IsBase w := by
    rintro (h | h | h)
    · exact h0 h
    · exact h3 h
    · exact h2 h
  exact childRot_of_not_base hw hO hE

/-- Rotation invariance of the standard tiles, with the induction over the letters of the word: the register
identities of a word follow from the rotation identities of its prefix, and the rotation identities of a word follow
from its register identities. -/
theorem good_and_rot (w : Word) : ChildRot w ∧ GoodOdd w ∧ GoodEven w := by
  induction w using List.reverseRecOn with
  | nil => exact ⟨childRot_nil, Or.inl (by simp), Or.inl (by simp)⟩
  | append_singleton u d ih =>
    obtain ⟨hC, hO, hE⟩ := ih
    have hG : GoodOdd (u ++ [d]) ∧ GoodEven (u ++ [d]) := by
      cases d
      · exact ⟨goodOdd_snoc_one hC, goodEven_snoc_one hC⟩
      · exact ⟨goodOdd_snoc_two hC, goodEven_snoc_two hE⟩
      · exact ⟨goodOdd_snoc_three hO, goodEven_snoc_three hC⟩
    exact ⟨childRot_of_good _ hG.1 hG.2, hG.1, hG.2⟩

/-- **Rotation invariance of the standard tiles** (`lemma:standard_boundary_word_recursion`, part 1), for every word:
the rotation of the odd standard tile of `w` is the even standard tile of the swapped word, translated by the
lower-left vertex `t(n/d) = c(i·T(n/d))`, and symmetrically for the even tile. -/
theorem rot_standard_tiles (w : Word) :
    rot (oddTile w) = shift (evenTile (swapW w)) (tF ((parentsAt w).current .odd)) ∧
      rot (evenTile w) = shift (oddTile (swapW w)) (tF ((parentsAt w).current .even)) :=
  (good_and_rot w).1

/-! ### Normalisation: the lower-left vertex of every standard tile is the origin (`c(T) = 0`) -/

theorem lexLE_add {p q : Site} (hp : lexLE 0 p) (hq : lexLE 0 q) : lexLE 0 (p + q) := by
  unfold lexLE at *
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero] at *
  omega

theorem forall_union {P : Site → Prop} {A B : Tile} (hA : ∀ x ∈ A, P x) (hB : ∀ x ∈ B, P x) :
    ∀ x ∈ A ∪ B, P x := by
  intro x hx
  rcases Finset.mem_union.mp hx with h | h
  · exact hA x h
  · exact hB x h

theorem forall_shift {T : Tile} {v : Site} (hT : ∀ y ∈ T, lexLE 0 y) (hv : lexLE 0 v) :
    ∀ x ∈ shift T v, lexLE 0 x := by
  intro x hx
  rw [mem_shift] at hx
  simpa using lexLE_add (hT _ hx) hv

theorem norm_stairF {d : ℤ} (hd : 2 ≤ d) : IsNormalised (stairF d) := by
  refine ⟨?_, ?_⟩
  · rw [mem_stairF hd]
    exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · intro p hp
    rw [mem_stairF hd] at hp
    unfold lexLE
    simp only [Prod.fst_zero, Prod.snd_zero]
    omega

theorem norm_ladderF {d : ℤ} (hd : 2 ≤ d) : IsNormalised (ladderF d) := by
  refine ⟨?_, ?_⟩
  · rw [mem_ladderF hd]
    refine ⟨Or.inl ⟨rfl, rfl⟩, ?_⟩
    simp only [Prod.fst_zero, Prod.snd_zero]
    omega
  · intro p hp
    rw [mem_ladderF hd] at hp
    unfold lexLE
    simp only [Prod.fst_zero, Prod.snd_zero]
    omega

theorem norm_nstairN {d : ℤ} (hd : 2 ≤ d) : IsNormalised (nstairN d) := by
  refine ⟨?_, ?_⟩
  · unfold nstairN
    rw [mem_shift, mem_nstairF hd]
    simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero]
    omega
  · intro p hp
    unfold nstairN at hp
    rw [mem_shift, mem_nstairF hd] at hp
    unfold lexLE
    simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero] at hp ⊢
    omega

theorem norm_nladderN {d : ℤ} (hd : 2 ≤ d) : IsNormalised (nladderN d) := by
  refine ⟨?_, ?_⟩
  · unfold nladderN
    rw [mem_shift, mem_nladderF hd]
    simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero]
    omega
  · intro p hp
    unfold nladderN at hp
    rw [mem_shift, mem_nladderF hd] at hp
    unfold lexLE
    simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero] at hp ⊢
    omega

theorem lexLE0_texV1Odd {p : Fraction} (hden : 0 < p.den) (hnum : 0 ≤ p.num) :
    lexLE 0 (texV1Odd p) := by
  unfold lexLE texV1Odd
  simp only [Prod.fst_zero, Prod.snd_zero]
  omega

theorem lexLE0_texV1Even {q : Fraction} (hden : 0 < q.den) (hnum : 0 ≤ q.num) :
    lexLE 0 (texV1Even q) := by
  unfold lexLE texV1Even
  simp only [Prod.fst_zero, Prod.snd_zero]
  omega

theorem lexLE0_texV2 {f : Fraction} (hden : 0 < f.den) (hnum : 0 ≤ f.num) : lexLE 0 (texV2 f) := by
  unfold lexLE texV2
  simp only [Prod.fst_zero, Prod.snd_zero]
  omega

theorem norm_oddChild (b : Bool) {T1 T2 : Tile} {p q : Fraction} (hpd : 0 < p.den) (hpn : 0 ≤ p.num)
    (hqd : 0 < q.den) (hqn : 0 ≤ q.num) (hT1 : IsNormalised T1) (hT2 : IsNormalised T2) :
    IsNormalised (oddChildB b T1 T2 p q) := by
  have z1 := hT1.1
  have z2 := hT2.1
  have h1 : ∀ y ∈ T1, lexLE 0 y := hT1.2
  have h2 : ∀ y ∈ T2, lexLE 0 y := hT2.2
  have l1 := lexLE0_texV1Odd hpd hpn
  have l2 := lexLE0_texV1Even hqd hqn
  have l3 := lexLE0_texV2 hpd hpn
  have l4 := lexLE0_texV2 hqd hqn
  refine ⟨?_, ?_⟩
  · cases b <;> simp only [oddChildB, Finset.mem_union] <;> tauto
  · cases b
    · exact forall_union (forall_union (forall_union (forall_union (forall_union h2
        (forall_shift h2 l2)) (forall_shift h2 (lexLE_add l1 l3)))
        (forall_shift h2 (lexLE_add (lexLE_add l1 l3) l2))) (forall_shift h1 (lexLE_add l2 l2)))
        (forall_shift h1 l4)
    · exact forall_union (forall_union (forall_union (forall_union (forall_union
        (forall_shift h2 l1) (forall_shift h2 (lexLE_add l1 l2))) (forall_shift h2 l3))
        (forall_shift h2 (lexLE_add l3 l2))) h1) (forall_shift h1 (lexLE_add (lexLE_add l2 l2) l4))

theorem norm_evenChild (b : Bool) {T1 T2 : Tile} {p q : Fraction} (hpd : 0 < p.den) (hpn : 0 ≤ p.num)
    (hqd : 0 < q.den) (hqn : 0 ≤ q.num) (hT1 : IsNormalised T1) (hT2 : IsNormalised T2) :
    IsNormalised (evenChildB b T1 T2 p q) := by
  have z1 := hT1.1
  have z2 := hT2.1
  have h1 : ∀ y ∈ T1, lexLE 0 y := hT1.2
  have h2 : ∀ y ∈ T2, lexLE 0 y := hT2.2
  have l1 := lexLE0_texV1Odd hpd hpn
  have l2 := lexLE0_texV1Even hqd hqn
  have l3 := lexLE0_texV2 hpd hpn
  have l4 := lexLE0_texV2 hqd hqn
  refine ⟨?_, ?_⟩
  · cases b <;> simp only [evenChildB, Finset.mem_union] <;> tauto
  · cases b
    · exact forall_union (forall_union (forall_union (forall_union (forall_union h2
        (forall_shift h2 (lexLE_add l1 (lexLE_add l3 l3)))) (forall_shift h1 l2))
        (forall_shift h1 (lexLE_add l2 l3))) (forall_shift h1 l4)) (forall_shift h1 (lexLE_add l4 l3))
    · exact forall_union (forall_union (forall_union (forall_union (forall_union
        (forall_shift h2 l1) (forall_shift h2 (lexLE_add l3 l3))) h1) (forall_shift h1 l3))
        (forall_shift h1 (lexLE_add l2 l4))) (forall_shift h1 (lexLE_add (lexLE_add l2 l4) l3))

/-- The normalisation of a non-base word, from the normalisation of the two registers. -/
theorem norm_child_of_not_base {w : Word} (hw : ¬ IsBase w) (hO : IsNormalised (stateAt w).tOdd)
    (hE : IsNormalised (stateAt w).tEven) : IsNormalised (oddTile w) ∧ IsNormalised (evenTile w) := by
  have hV := parentsAt_valid w
  obtain ⟨hpd, hpn, -⟩ := hV.odd_bounds
  obtain ⟨hqd, hqn, -⟩ := hV.even_bounds
  rw [oddTile_eq_of_not_base hw, evenTile_eq_of_not_base hw]
  exact ⟨norm_oddChild _ hpd hpn hqd hqn hO hE, norm_evenChild _ hpd hpn hqd hqn hO hE⟩

abbrev NormOdd (w : Word) : Prop := (∀ d ∈ w, d = Digit.three) ∨ IsNormalised (stateAt w).tOdd

abbrev NormEven (w : Word) : Prop := (∀ d ∈ w, d = Digit.two) ∨ IsNormalised (stateAt w).tEven

abbrev NormChild (w : Word) : Prop := IsNormalised (oddTile w) ∧ IsNormalised (evenTile w)

theorem normChild_of_good (w : Word) (hO : NormOdd w) (hE : NormEven w) : NormChild w := by
  by_cases h0 : w = []
  · subst h0
    unfold NormChild oddTile evenTile
    rw [childTiles_nil]
    exact ⟨norm_nstairN (by norm_num), norm_stairF (by norm_num)⟩
  by_cases h3 : ∀ d ∈ w, d = Digit.three
  · obtain ⟨k, rfl⟩ : ∃ k, w = List.replicate k Digit.three :=
      ⟨w.length, List.eq_replicate_iff.mpr ⟨rfl, h3⟩⟩
    have hk : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at h0
      · exact hk
    unfold NormChild oddTile evenTile
    rw [childTiles_three hk]
    exact ⟨norm_ladderF (by omega), norm_stairF (by omega)⟩
  by_cases h2 : ∀ d ∈ w, d = Digit.two
  · obtain ⟨k, rfl⟩ : ∃ k, w = List.replicate k Digit.two :=
      ⟨w.length, List.eq_replicate_iff.mpr ⟨rfl, h2⟩⟩
    have hk : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at h0
      · exact hk
    unfold NormChild oddTile evenTile
    rw [childTiles_two hk]
    exact ⟨norm_nstairN (by omega), norm_nladderN (by omega)⟩
  have hw : ¬ IsBase w := by
    rintro (h | h | h)
    · exact h0 h
    · exact h3 h
    · exact h2 h
  exact norm_child_of_not_base hw (hO.resolve_left h3) (hE.resolve_left h2)

theorem normOdd_snoc_one {u : Word} (hC : NormChild u) : NormOdd (u ++ [.one]) := by
  refine Or.inr ?_
  rw [tOdd_snoc_one]
  exact hC.1

theorem normEven_snoc_one {u : Word} (hC : NormChild u) : NormEven (u ++ [.one]) := by
  refine Or.inr ?_
  rw [tEven_snoc_one]
  exact hC.2

theorem normOdd_snoc_two {u : Word} (hC : NormChild u) : NormOdd (u ++ [.two]) := by
  refine Or.inr ?_
  rw [tOdd_snoc_two]
  exact hC.1

theorem normEven_snoc_two {u : Word} (hE : NormEven u) : NormEven (u ++ [.two]) := by
  rcases hE with h | h
  · refine Or.inl ?_
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact h d hd
    · rw [List.mem_singleton.mp hd]
  · refine Or.inr ?_
    rw [tEven_snoc_two]
    exact h

theorem normOdd_snoc_three {u : Word} (hO : NormOdd u) : NormOdd (u ++ [.three]) := by
  rcases hO with h | h
  · refine Or.inl ?_
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact h d hd
    · rw [List.mem_singleton.mp hd]
  · refine Or.inr ?_
    rw [tOdd_snoc_three]
    exact h

theorem normEven_snoc_three {u : Word} (hC : NormChild u) : NormEven (u ++ [.three]) := by
  refine Or.inr ?_
  rw [tEven_snoc_three]
  exact hC.2

theorem norm_all (w : Word) : NormChild w ∧ NormOdd w ∧ NormEven w := by
  induction w using List.reverseRecOn with
  | nil =>
    exact ⟨normChild_of_good [] (Or.inl (by simp)) (Or.inl (by simp)), Or.inl (by simp), Or.inl (by simp)⟩
  | append_singleton u d ih =>
    obtain ⟨hC, hO, hE⟩ := ih
    have hG : NormOdd (u ++ [d]) ∧ NormEven (u ++ [d]) := by
      cases d
      · exact ⟨normOdd_snoc_one hC, normEven_snoc_one hC⟩
      · exact ⟨normOdd_snoc_two hC, normEven_snoc_two hE⟩
      · exact ⟨normOdd_snoc_three hO, normEven_snoc_three hC⟩
    exact ⟨normChild_of_good _ hG.1 hG.2, hG.1, hG.2⟩

/-- **Normalisation of the standard tiles**: the lower-left vertex of the odd and the even standard tile of every word
is the origin, so `c(T) = 0` holds for every standard tile of the convention of `def:standard_tiles`. -/
theorem standard_tiles_normalised (w : Word) : IsNormalised (oddTile w) ∧ IsNormalised (evenTile w) :=
  (norm_all w).1

end FLatticePaper.Tiles.Standard
