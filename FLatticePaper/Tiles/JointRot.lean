import FLatticePaper.Tiles.JointGlue
import FLatticePaper.Tiles.TileTranslationStd
import FLatticePaper.Tiles.BaseTileProps
import FLatticePaper.Tiles.WeakStepPaper

/-! # The rotation step of the joint induction ((c) of `lemma:tile-odometer-existence`)

Surgical edition 274ad18, proof of `lemma:tile-odometer-existence`, paragraph "Rotations" (and (c) of
`lemma:weak_standard_odometer_properties`). The text defines the rotated odometers by rotating the decomposition. Here every tile
odometer is given by its own decomposition (`RespectsPieces`), so the rotation is proved by comparing the two decompositions piece
by piece. This file holds the generic part.

* `RawRot o oR c γ`: `oR(x) = o(i x + c) - h_0(x) + γ^T x + C` on the domain of `oR`, for one constant `C`, with `i x + c` in the
  domain of `o`.
* `piece_transport`: a piece of `oR` and a piece of `o` whose odometers satisfy a raw rotation with `(c_r, γ_r)`, with the offset
  rule `i u_R = u + c_r - c` and the affine rule `η_R = R η + H u_R + γ - γ_r` (`R = -i`, `H u = ((u_1 + u_2)/2, (u_1 - u_2)/2)`,
  `u_R` of even coordinate sum), give the raw rotation of `(o, oR)` on that piece up to its own constant. The computation is
  `eq:h0_identities` (`centeredQuarterTurnCorrection_add`).
* `rawRot_of_pieces`: the constants of the pieces of `oR` agree when the overlap graph of its pieces is connected
  (`compatible_unique`).
* `rawRot_of_tileRotation`, `rawRot_of_altRotation` and `tileRotation_of_rawRot`, `altRotation_of_rawRot`: passage between the
  normalised identities of `JointFamily` and the raw ones when the normalisations have slope `α = 0`; the standard one uses the
  corner value `N(v_1 - i) = 0` (`eq:std_corner_values`) to fix the constant.

The comparison of the decompositions (`tileOdd_rawRot`, `tileEven_rawRot`, `tileAltOdd_rawRot`, `tileAltEven_rawRot`): the pieces of
the child of `swapW w` and of the child of `w` pair by a fixed permutation for each phase (an involution on the six copies; the
alternate parent piece with the alternate parent piece), the L-corrected copies with the L-corrected copies with the signs of
`LRotProps`. Each pair satisfies the offset and affine rules, so the raw rotation of the parents (from the induction) gives the raw
rotation of the children. The rotation `(c_r, γ_r)` of the alternate parent is `altCf` of the register word, written in the vectors
of `w` (`altParQ`, `altParP`, `altCf_even_reg`, `altCf_odd_reg`).

Slopes (`family_slopes`): every tile and alternate tile odometer of the family is normalised on its first tile with `α = 0`. The
first tile lies in a parent placed at offset `0` with affine factor `0` (for the even alternate child after a `3` at `W_1` even, in
the bridge of the elongated L-correction, `slope_evenL`), and the base odometers have slope `0` (`BaseSlopes`; for the paper data
`baseSlopes_paper` from `BaseTileProps.base_slopes`). With slopes `0` the normalised identities of the induction hypothesis are raw
ones, and conversely.

The step at one level (`rotProps_step`): `RotProps` at every word of length `n`, from the family below `n`, the slices at level `n`,
the base rotations (`BaseRot`; `base_rotProps` for the paper data) and the connectivity of the overlap graphs of the decompositions
(`Connected4`, a named input).

The L-rotation (`evenL_rawRot`, `oddL_rawRot`, `lRotProps_step`): when the prefix of `w` before its trailing letters is not `2^j`
(even L) or `3^j` (odd L), the stems, the bridge and the heads of the L decompositions of `w` and `swapW w` pair index by index,
with the same offset and affine rules (the heads with `altCf` of the register, `altParP`, `altParQ`). The special prefixes are a
named input (`SpecialLRot`), as is the connectivity of the overlap graphs of the L decompositions (`ConnectedL`).

The step (`rotStepInput_of`): `RotStepInput D` from `BaseSlopes D`, `BaseRot D`, the connectivity and the special prefixes.

Connectivity of the standard decompositions (`std_connected`): the six copies are joined by a spanning tree of overlaps, each
witnessed by a common corner point (`eq:std_corner_values`) of the two copies; the parents have all eight corner points in their
domains (`TileTranslationStd.stdCorners_odd`, `_even`), and an L-corrected copy has the end points of its kept side
(`LSidesAgree` with `paperLSides`; `side_hPlus`, `side_hMinus`, `side_vMinus`, `side_vPlus`). With it, `rotStepInput_of_alt`
leaves the connectivity of the alternate decompositions (`ConnectedAlt`) and of the L decompositions (`ConnectedL`) named.

The special prefixes (`evenL_special_rawRot`, `oddL_special_rawRot`, `specialLRot_of_cells`): at the prefixes `2^j` (even L) and
`3^j` (odd L) the stems and heads still pair (the pieces named `eStem`, `eMid`, `eHead`, `oStem`, `oBridge`, `oHead`), while the
middle pieces of the rotated L-correction (the bridge `T_{0/1}`, or the bridge `T_{1/1}` and the copy of `T^d_{1/1}`) lie across
several pieces of the other side. Their points lie on the kept sides of both L-corrections, where each agrees with its child
(`LSidesAgree`) and the children rotate (`RotProps` at the same level), so they carry the constant of the sides
(`good_of_sides`); a tip in the short odd case lies in a head that has such a point (`rawRot_of_splitL`). The cell facts are the
named input `SpecialCells`. `rotStepInput_of_cells` is the step with these inputs. -/

namespace FLatticePaper.Tiles.JointRot

open FLatticePaper.Farey
open FLatticePaper.Construction
open FLatticePaper.Tiles
open FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.JointGlue

/-- `R = -i`. -/
def rotR (v : Site) : Site := (v.2, -v.1)

/-- `H u = ((u_1 + u_2)/2, (u_1 - u_2)/2)`. -/
def hHalf (u : Site) : Site := ((u.1 + u.2) / 2, (u.1 - u.2) / 2)

/-- The raw rotation: `oR(x) = o(i x + c) - h_0(x) + γ^T x + C`, with `i x + c` in the domain of `o`. -/
def RawRot (o oR : PartialOdometer) (c γ : Site) : Prop :=
  ∃ C : ℤ, ∀ x ∈ oR.dom, mulI x + c ∈ o.dom ∧ oR.val x = o.val (mulI x + c) - h0 x + dotS γ x + C

theorem dotS_add (a u v : Site) : dotS a (u + v) = dotS a u + dotS a v := by
  simp only [dotS, Prod.fst_add, Prod.snd_add]; ring

theorem dotS_mulI (a x : Site) : dotS a (mulI x) = dotS (rotR a) x := by
  simp only [dotS, mulI, rotR]; ring

/-- `eq:h0_identities`: `h_0(x) - h_0(x - u) = -(H u)^T x + (H u)^T u - K(u)` for `u` of even coordinate sum. -/
theorem h0_sub (x u : Site) (hu : EvenSite u) :
    h0 x - h0 (x - u) = -dotS (hHalf u) x + dotS (hHalf u) u - centeredQuarterTurnCorrection u := by
  have h := centeredQuarterTurnCorrection_add (x - u) hu
  rw [sub_add_cancel] at h
  simp only [h0, h, hHalf, dotS, Prod.fst_sub, Prod.snd_sub]
  ring

theorem mem_placed {p : Piece} {x : Site} : x ∈ p.placed ↔ x - p.off ∈ p.odo.dom := by
  simp only [Piece.placed, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨x - p.off, h, by simp⟩

/-- One piece: from the raw rotation of the two piece odometers and the offset and affine rules, the raw rotation of `(o, oR)`
holds on the piece of `oR`, up to a constant of the piece. -/
theorem piece_transport (o oR : PartialOdometer) (p pR : Piece) (c γ cr γr : Site) (b bR : ℤ)
    (hval : ∀ y ∈ p.placed, y ∉ p.exc → o.val y = p.odo.val (y - p.off) + dotS p.aff y + b)
    (hvalR : ∀ x ∈ pR.placed, x ∉ pR.exc → oR.val x = pR.odo.val (x - pR.off) + dotS pR.aff x + bR)
    (hpar : RawRot p.odo pR.odo cr γr)
    (hoff : mulI pR.off = p.off + cr - c) (heven : EvenSite pR.off)
    (haff : pR.aff = rotR p.aff + hHalf pR.off + γ - γr)
    (hexc : ∀ x ∈ pR.placed, x ∉ pR.exc → mulI x + c ∉ p.exc) :
    ∃ C : ℤ, ∀ x ∈ pR.placed, x ∉ pR.exc →
      mulI x + c ∈ p.placed ∧ oR.val x = o.val (mulI x + c) - h0 x + dotS γ x + C := by
  obtain ⟨Cp, hCp⟩ := hpar
  refine ⟨bR - b + Cp - dotS p.aff c - dotS γr pR.off + dotS (hHalf pR.off) pR.off -
    centeredQuarterTurnCorrection pR.off, fun x hx hxe => ?_⟩
  have hx' : x - pR.off ∈ pR.odo.dom := mem_placed.mp hx
  obtain ⟨hzd, hzv⟩ := hCp _ hx'
  have hz : mulI x + c - p.off = mulI (x - pR.off) + cr := by
    have : mulI x = mulI (x - pR.off) + mulI pR.off := by
      simp only [mulI, Prod.fst_sub, Prod.snd_sub, Prod.mk_add_mk, Prod.mk.injEq]; constructor <;> ring
    rw [this, hoff]; abel
  have hzp : mulI x + c ∈ p.placed := by rw [mem_placed, hz]; exact hzd
  refine ⟨hzp, ?_⟩
  rw [hvalR x hx hxe, hval _ hzp (hexc x hx hxe), hz, hzv, haff]
  have hh := h0_sub x pR.off heven
  have e1 : dotS p.aff (mulI x + c) = dotS (rotR p.aff) x + dotS p.aff c := by rw [dotS_add, dotS_mulI]
  have e2 : dotS γr (x - pR.off) = dotS γr x - dotS γr pR.off := by
    simp only [dotS, Prod.fst_sub, Prod.snd_sub]; ring
  have e3 : dotS (rotR p.aff + hHalf pR.off + γ - γr) x =
      dotS (rotR p.aff) x + dotS (hHalf pR.off) x + dotS γ x - dotS γr x := by
    simp only [dotS, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; ring
  rw [e1, e2, e3]
  linarith

/-- The pieces of `oR` glue: if each piece of `oR` (outside its exceptional points) carries the raw rotation with its own
constant, and the overlap graph of the pieces is connected, the raw rotation holds with one constant. -/
theorem rawRot_of_pieces (o oR : PartialOdometer) (psR : List Piece) (c γ : Site)
    (hdom : oR.dom = pieceUnion psR) (hcov : PiecesCovered psR)
    (hconn : (overlapGraph (goodPart psR)).Connected)
    (hpiece : ∀ (i : ℕ) (pR : Piece), psR[i]? = some pR → ∃ C : ℤ, ∀ x ∈ pR.placed, x ∉ pR.exc →
      mulI x + c ∈ o.dom ∧ oR.val x = o.val (mulI x + c) - h0 x + dotS γ x + C) :
    RawRot o oR c γ := by
  have hpc : ∀ i : Fin psR.length, ∃ C : ℤ, ∀ x ∈ (psR.get i).placed, x ∉ (psR.get i).exc →
      mulI x + c ∈ o.dom ∧ oR.val x = o.val (mulI x + c) - h0 x + dotS γ x + C :=
    fun i => hpiece i.1 (psR.get i) (by simp)
  choose C hC using hpc
  have hcover : ∀ x : UnionPt psR, ∃ i, x ∈ goodPart psR i := by
    intro x
    obtain ⟨i, p, hi, hx, hxe⟩ := hcov x.1 x.2
    have hlt : i < psR.length := (List.getElem?_eq_some_iff.mp hi).1
    have hget : psR.get ⟨i, hlt⟩ = p := by
      have := (List.getElem?_eq_some_iff.mp hi).2
      simpa using this
    exact ⟨⟨i, hlt⟩, by simp only [goodPart, Set.mem_setOf_eq, hget]; exact ⟨hx, hxe⟩⟩
  let Δ : UnionPt psR → ℤ := fun x => oR.val x.1 - o.val (mulI x.1 + c) + h0 x.1 - dotS γ x.1
  have hf : ∀ i, CompatibleWith Δ (goodPart psR i) (fun _ => 0) := by
    intro i
    refine ⟨C i, fun x hx => ?_⟩
    have := (hC i x.1 hx.1 hx.2).2
    simp only [Δ]
    linarith
  have hg : ∀ i, CompatibleWith (fun _ : UnionPt psR => (0 : ℤ)) (goodPart psR i) (fun _ => 0) :=
    fun _ => ⟨0, fun _ _ => by simp⟩
  obtain ⟨K, hK⟩ := compatible_unique (goodPart psR) (fun _ _ => 0) hcover hconn hf hg
  refine ⟨K, fun x hx => ?_⟩
  have hxu : x ∈ pieceUnion psR := hdom ▸ hx
  obtain ⟨i, hi⟩ := hcover ⟨x, hxu⟩
  refine ⟨(hC i x hi.1 hi.2).1, ?_⟩
  have := hK ⟨x, hxu⟩
  simp only [Δ] at this
  linarith

/-! ### Normalised and raw identities -/

theorem tileShape_one_zero : ((0 : ℤ), (0 : ℤ)) ∈ tileShape ZTile.one := by simp [tileShape]

theorem zTileOdo_one_zero : zTileOdo ZTile.one ((0 : ℤ), (0 : ℤ)) = 0 := by simp [zTileOdo, oneOdometer]

/-- A normalised standard rotation is a raw rotation, with `γ = α' - R α`. -/
theorem rawRot_of_tileRotation (o oR : PartialOdometer) (v1 α α' : Site) (β β' : ℤ)
    (h : ∀ x ∈ oR.dom, mulI x + v1 - ((0 : ℤ), (1 : ℤ)) ∈ o.dom ∧
      normed oR α' β' x = normed o α β (mulI x + v1 - ((0 : ℤ), (1 : ℤ))) - h0 x) :
    RawRot o oR (v1 - ((0 : ℤ), (1 : ℤ))) (α' - rotR α) := by
  refine ⟨β' - β - dotS α (v1 - ((0 : ℤ), (1 : ℤ))), fun x hx => ?_⟩
  obtain ⟨hm, hv⟩ := h x hx
  rw [add_sub_assoc] at hm hv
  refine ⟨hm, ?_⟩
  simp only [normed] at hv
  rw [dotS_add, dotS_mulI] at hv
  have e : dotS (α' - rotR α) x = dotS α' x - dotS (rotR α) x := by
    simp only [dotS, Prod.fst_sub, Prod.snd_sub]; ring
  rw [e]
  linarith

/-- A normalised alternate rotation is a raw rotation, with `γ + α' - R α`. -/
theorem rawRot_of_altRotation (o oR : PartialOdometer) (cf γ α α' : Site) (β β' c0 : ℤ)
    (h : ∀ x ∈ oR.dom, mulI x + cf ∈ o.dom ∧
      normed oR α' β' x = normed o α β (mulI x + cf) - h0 x + dotS γ x + c0) :
    RawRot o oR cf (γ + α' - rotR α) := by
  refine ⟨β' - β - dotS α cf + c0, fun x hx => ?_⟩
  obtain ⟨hm, hv⟩ := h x hx
  refine ⟨hm, ?_⟩
  simp only [normed] at hv
  rw [dotS_add, dotS_mulI] at hv
  have e : dotS (γ + α' - rotR α) x = dotS γ x + dotS α' x - dotS (rotR α) x := by
    simp only [dotS, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; ring
  rw [e]
  linarith

/-- With slopes `0` and the corner value `N(v_1 - i) = 0` of `o`, a raw rotation with `γ = 0` is the normalised standard
rotation. -/
theorem tileRotation_of_rawRot (o oR : PartialOdometer) (v1 : Site) (β β' : ℤ)
    (hN : FirstTileNormal o 0 β) (hNR : FirstTileNormal oR 0 β')
    (hcorner : normed o 0 β (v1 - ((0 : ℤ), (1 : ℤ))) = 0)
    (h : RawRot o oR (v1 - ((0 : ℤ), (1 : ℤ))) 0) : TileRotation o oR v1 := by
  obtain ⟨C, hC⟩ := h
  refine ⟨0, β, 0, β', hN, hNR, fun x hx => ?_⟩
  obtain ⟨h0m, h0v⟩ := hNR _ tileShape_one_zero
  obtain ⟨-, hz⟩ := hC _ h0m
  have hzero : mulI ((0 : ℤ), (0 : ℤ)) + (v1 - ((0 : ℤ), (1 : ℤ))) = v1 - ((0 : ℤ), (1 : ℤ)) := by
    simp [mulI]
  rw [hzero] at hz
  rw [zTileOdo_one_zero] at h0v
  have hz0 : h0 ((0 : ℤ), (0 : ℤ)) = 0 := by decide
  have hd0 : dotS (0 : Site) ((0 : ℤ), (0 : ℤ)) = 0 := by simp [dotS]
  simp only [normed, dotS, Prod.fst_zero, Prod.snd_zero, zero_mul, add_zero] at h0v hcorner
  obtain ⟨hm, hv⟩ := hC x hx
  rw [← add_sub_assoc] at hm hv
  refine ⟨hm, ?_⟩
  simp only [normed, dotS, Prod.fst_zero, Prod.snd_zero, zero_mul, add_zero] at hv hz ⊢
  rw [hz0] at hz
  rw [hv]
  linarith

/-- With slopes `0`, a raw rotation with `γ` is the normalised alternate rotation. -/
theorem altRotation_of_rawRot (o oR : PartialOdometer) (cf γ : Site) (β β' : ℤ)
    (hN : FirstTileNormal o 0 β) (hNR : FirstTileNormal oR 0 β') (h : RawRot o oR cf γ) :
    AltRotation o oR cf γ := by
  obtain ⟨C, hC⟩ := h
  refine ⟨0, β, 0, β', C + β - β', hN, hNR, fun x hx => ?_⟩
  obtain ⟨hm, hv⟩ := hC x hx
  refine ⟨hm, ?_⟩
  simp only [normed, dotS, Prod.fst_zero, Prod.snd_zero, zero_mul, add_zero] at hv ⊢
  rw [hv]
  ring

/-- The normalisation is unique: two normalisations of one odometer on the first tile agree. -/
theorem firstTileNormal_unique (o : PartialOdometer) (α α' : Site) (β β' : ℤ)
    (h : FirstTileNormal o α β) (h' : FirstTileNormal o α' β') : α = α' ∧ β = β' := by
  have key : ∀ x ∈ tileShape ZTile.one, dotS α x + β = dotS α' x + β' := by
    intro x hx
    have a := (h x hx).2
    have b := (h' x hx).2
    simp only [normed] at a b
    linarith
  have k00 := key (0, 0) (by simp [tileShape])
  have k10 := key (1, 0) (by simp [tileShape])
  have k01 := key (0, 1) (by simp [tileShape])
  simp only [dotS] at k00 k10 k01
  obtain ⟨a1, a2⟩ := α
  obtain ⟨b1, b2⟩ := α'
  simp only [Prod.mk.injEq]
  refine ⟨⟨by linarith, by linarith⟩, by linarith⟩

/-! ### Comparing two decompositions -/

/-- Two decompositions: if every piece of the decomposition of `oR` is matched by a piece of the decomposition of `o` with the
raw rotation of the piece odometers and the offset and affine rules, and the overlap graph of the pieces of `oR` is connected, the
raw rotation holds. -/
theorem rawRot_of_pairing (o oR : PartialOdometer) (ps psR : List Piece) (c γ : Site)
    (ho : RespectsPieces o ps) (hoR : RespectsPieces oR psR) (hcov : PiecesCovered psR)
    (hconn : (overlapGraph (goodPart psR)).Connected)
    (hpair : ∀ (i : ℕ) (pR : Piece), psR[i]? = some pR → ∃ p ∈ ps, ∃ cr γr : Site,
      RawRot p.odo pR.odo cr γr ∧ mulI pR.off = p.off + cr - c ∧ EvenSite pR.off ∧
      pR.aff = rotR p.aff + hHalf pR.off + γ - γr ∧ (∀ x ∈ pR.placed, x ∉ pR.exc → mulI x + c ∉ p.exc)) :
    RawRot o oR c γ := by
  refine rawRot_of_pieces o oR psR c γ hoR.1 hcov hconn (fun i pR hi => ?_)
  obtain ⟨p, hp, cr, γr, hpar, hoff, hev, haff, hexc⟩ := hpair i pR hi
  obtain ⟨b, hb⟩ := ho.2 p hp
  obtain ⟨bR, hbR⟩ := hoR.2 pR (List.mem_of_getElem? hi)
  obtain ⟨C, hC⟩ := piece_transport o oR p pR c γ cr γr b bR hb hbR hpar hoff hev haff hexc
  refine ⟨C, fun x hx hxe => ⟨?_, (hC x hx hxe).2⟩⟩
  rw [ho.1]
  exact mem_pieceUnion.mpr ⟨p, hp, (hC x hx hxe).1⟩

/-! ### The parents and the registers of the swapped word -/

open FLatticePaper.Tiles.Standard (swapW IsBase)
open FLatticePaper.Tiles.SurgicalWeak (regsAt regRun regStep regOdo WeakData)

theorem swapW_append (u v : Word) : swapW (u ++ v) = swapW u ++ swapW v := by simp [swapW]

theorem W1Odd_swapW (w : Word) : W1Odd (swapW w) = W1Odd w := by
  unfold W1Odd
  rw [FLatticePaper.Tiles.Standard.phase_swapW]

theorem regRun_append (pre rest : Word) (d : Digit) (r : Option Word × Option Word) :
    regRun pre (rest ++ [d]) r = regStep (pre ++ rest) (regRun pre rest r) d := by
  induction rest generalizing pre r with
  | nil => simp [regRun]
  | cons a rest ih =>
    show regRun (pre ++ [a]) (rest ++ [d]) (regStep pre r a) = _
    rw [ih]
    simp [regRun, List.append_assoc]

theorem regsAt_append_singleton (u : Word) (d : Digit) : regsAt (u ++ [d]) = regStep u (regsAt u) d := by
  unfold regsAt
  rw [regRun_append]
  rfl

/-- The registers of the swapped word are the swapped registers, exchanged. -/
theorem regsAt_swapW (w : Word) :
    regsAt (swapW w) = ((regsAt w).2.map swapW, (regsAt w).1.map swapW) := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton v d ih =>
    rw [swapW_append, show swapW [d] = [d.swapTwoThree] from rfl, regsAt_append_singleton, regsAt_append_singleton, ih]
    cases d <;> rfl

/-- The register words carry the parents: the odd child of the odd register is the odd parent, and so on. -/
theorem parents_of_regs (w : Word) :
    (∀ u, (regsAt w).1 = some u → (parentsAt u).current .odd = (parentsAt w).odd) ∧
      (∀ u, (regsAt w).2 = some u → (parentsAt u).current .even = (parentsAt w).even) := by
  induction w using List.reverseRecOn with
  | nil => exact ⟨fun u h => by simp [regsAt, regRun] at h, fun u h => by simp [regsAt, regRun] at h⟩
  | append_singleton v d ih =>
    rw [regsAt_append_singleton, parentsAt_append_singleton]
    cases d
    · exact ⟨fun u h => by simp only [regStep, Option.some.injEq] at h; subst h; rfl,
        fun u h => by simp only [regStep, Option.some.injEq] at h; subst h; rfl⟩
    · exact ⟨fun u h => by simp only [regStep, Option.some.injEq] at h; subst h; rfl, fun u h => ih.2 u h⟩
    · exact ⟨fun u h => ih.1 u h, fun u h => by simp only [regStep, Option.some.injEq] at h; subst h; rfl⟩

/-- A word that is not a base word has both registers. -/
theorem regs_some (w : Word) (hw : ¬ IsBase w) : (∃ u, (regsAt w).1 = some u) ∧ (∃ u, (regsAt w).2 = some u) := by
  have key : ∀ w : Word, ((regsAt w).1 = none → ∀ d ∈ w, d = Digit.three) ∧
      ((regsAt w).2 = none → ∀ d ∈ w, d = Digit.two) := by
    intro w
    induction w using List.reverseRecOn with
    | nil => exact ⟨fun _ d hd => by simp at hd, fun _ d hd => by simp at hd⟩
    | append_singleton v d ih =>
      rw [regsAt_append_singleton]
      cases d
      · exact ⟨fun h => by simp [regStep] at h, fun h => by simp [regStep] at h⟩
      · refine ⟨fun h => by simp [regStep] at h, fun h e he => ?_⟩
        simp only [List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact ih.2 h e he
        · rfl
      · refine ⟨fun h e he => ?_, fun h => by simp [regStep] at h⟩
        simp only [List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact ih.1 h e he
        · rfl
  obtain ⟨k1, k2⟩ := key w
  refine ⟨?_, ?_⟩
  · cases h : (regsAt w).1 with
    | none => exact absurd (Or.inr (Or.inl (k1 h))) hw
    | some u => exact ⟨u, rfl⟩
  · cases h : (regsAt w).2 with
    | none => exact absurd (Or.inr (Or.inr (k2 h))) hw
    | some u => exact ⟨u, rfl⟩

theorem getLast_swapW (w : Word) : (swapW w).getLast? = w.getLast?.map Digit.swapTwoThree := by
  simp [swapW, List.getLast?_map]

theorem dropLast_swapW (w : Word) : (swapW w).dropLast = swapW w.dropLast := by
  simp [swapW, List.map_dropLast]

/-- The vectors of the parents of the swapped word, from the parents `p = (n_p, d_p)` (odd) and `q = (n_q, d_q)` (even) of `w`. -/
theorem vecs_swapW (w : Word) :
    vP1 (swapW w) = ((parentsAt w).even.den + (parentsAt w).even.num, (parentsAt w).even.den - (parentsAt w).even.num) ∧
      vP2 (swapW w) = (-(parentsAt w).even.num, (parentsAt w).even.den) ∧
      vQ1 (swapW w) = ((parentsAt w).odd.den + (parentsAt w).odd.num, (parentsAt w).odd.den - (parentsAt w).odd.num) ∧
      vQ2 (swapW w) = (-2 * (parentsAt w).odd.num, 2 * (parentsAt w).odd.den) ∧
      (parentsAt (swapW w)).odd =
        ⟨((parentsAt w).even.den - (parentsAt w).even.num) / 2, ((parentsAt w).even.den + (parentsAt w).even.num) / 2⟩ ∧
      (parentsAt (swapW w)).even = ⟨(parentsAt w).odd.den - (parentsAt w).odd.num, (parentsAt w).odd.den + (parentsAt w).odd.num⟩ := by
  have hV := parentsAt_valid w
  have hq : ((parentsAt w).even.num + (parentsAt w).even.den) % 2 = 0 := hV.even_parity
  have ho : (parentsAt (swapW w)).odd =
      ⟨((parentsAt w).even.den - (parentsAt w).even.num) / 2, ((parentsAt w).even.den + (parentsAt w).even.num) / 2⟩ := by
    rw [FLatticePaper.Tiles.Standard.parentsAt_swapW]
    exact Fraction.rotate_of_even hV.even_parity
  have he : (parentsAt (swapW w)).even =
      ⟨(parentsAt w).odd.den - (parentsAt w).odd.num, (parentsAt w).odd.den + (parentsAt w).odd.num⟩ := by
    rw [FLatticePaper.Tiles.Standard.parentsAt_swapW]
    exact Fraction.rotate_of_odd hV.odd_parity
  refine ⟨?_, ?_, ?_, ?_, ho, he⟩
  · simp only [vP1, ho, texV1Odd, Prod.mk.injEq]; omega
  · simp only [vP2, ho, texV2, Prod.mk.injEq]; omega
  · simp only [vQ1, he, texV1Even]
  · simp only [vQ2, he, texV2, Prod.mk.injEq]; omega

theorem corr_swapW_two (w : Word) :
    decide ((swapW w).getLast? = some Digit.two) = decide (w.getLast? = some Digit.three) := by
  rw [getLast_swapW]
  cases w.getLast? with
  | none => rfl
  | some d => cases d <;> rfl

theorem corr_swapW_three (w : Word) :
    decide ((swapW w).getLast? = some Digit.three) = decide (w.getLast? = some Digit.two) := by
  rw [getLast_swapW]
  cases w.getLast? with
  | none => rfl
  | some d => cases d <;> rfl

open FLatticePaper.Tiles.SurgicalDict (offsetP0 offsetQ0)

set_option hygiene false in
/-- The piece odometers of a pairing: a register parent or an L-correction of the parent word. -/
macro "rot_par" : tactic => `(tactic| (
  simp only [tileOddPieces, tileEvenPieces, List.getElem_cons_succ, List.getElem_cons_zero, stdPiece, corr_swapW_two,
    corr_swapW_three, W1Odd_swapW, dropLast_swapW]
  by_cases hc : w.getLast? = some Digit.three <;> by_cases hc2 : w.getLast? = some Digit.two <;>
    (try simp only [hc, hc2, hWo, decide_true, decide_false, Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and,
      Bool.not_true, Bool.not_false, ↓reduceIte, Bool.false_eq_true]) <;>
    first
    | exact hP
    | exact hQ
    | simpa [hWo] using hL hc true
    | simpa [hWo] using hL hc false
    | simpa [hWo] using hL hc2 true
    | simpa [hWo] using hL hc2 false))

set_option hygiene false in
/-- The offset, parity and affine identities of a pairing. -/
macro "rot_id" : tactic => `(tactic| (
  simp only [tileOddPieces, tileEvenPieces, tileAltOddPieces, tileAltEvenPieces, List.getElem_cons_succ,
    List.getElem_cons_zero, List.getElem_append_left, List.getElem_append_right, stdPiece, p0Off, q0Off, p0Aff, q0Aff, aP2, aQ2,
    altOff, altAff, offsetP0, offsetQ0, W1Odd_swapW, hWo, ↓reduceIte, Bool.false_eq_true]
  try simp only [e1, e2, e3, e4, e5, e6]
  try simp only [vP1, vP2, vQ1, vQ2, texV1Odd, texV1Even, texV2, Parents.current, Parents.combine, pairAffine, offsetA, mulI,
    rotR, hHalf, EvenSite]
  all_goals first
  | omega
  | (refine Prod.ext ?_ ?_ <;> simp <;> omega)
  | (simp <;> omega)))

/-! ### The standard children -/


/-- (c) of `lemma:tile-odometer-existence`, odd standard child, raw form: the even child of `swapW w` (decomposition at `swapW w`)
against the odd child of `w`, under `z(x) = i x + v_{p_0,1} - i`. The pieces pair as `0 1 2 3 4 5 ↦ 3 2 5 4 1 0` (`W_1` odd) and
`5 4 3 2 0 1` (`W_1` even); the L-corrected pieces after a `3` pair with the L-rotation of the parents. -/
theorem tileOdd_rawRot (S : WeakData) (pO pE : Word → PartialOdometer) (lE lO : Word → Bool → Bool → PartialOdometer)
    (w : Word) (o oR : PartialOdometer)
    (ho : RespectsPieces o (tileOddPieces S pO pE lE w))
    (hoR : RespectsPieces oR (tileEvenPieces S pO pE lO (swapW w)))
    (hconn : (overlapGraph (goodPart (tileEvenPieces S pO pE lO (swapW w)))).Connected)
    (hP : RawRot (regOdo S pO pE (regsAt w).1 true) (regOdo S pO pE (regsAt (swapW w)).2 false) (vP1 w - ((0 : ℤ), (1 : ℤ))) 0)
    (hQ : RawRot (regOdo S pO pE (regsAt w).2 false) (regOdo S pO pE (regsAt (swapW w)).1 true) (vQ1 w - ((0 : ℤ), (1 : ℤ))) 0)
    (hL : w.getLast? = some Digit.three → ∀ plus : Bool,
      RawRot (lE w.dropLast plus false) (lO (swapW w.dropLast) (plus != W1Odd w) false) (vQ1 w - ((0 : ℤ), (1 : ℤ))) 0) :
    RawRot o oR (texV1Odd ((parentsAt w).current .odd) - ((0 : ℤ), (1 : ℤ))) 0 := by
  refine rawRot_of_pairing o oR _ _ _ _ ho hoR (tileEvenPieces_covered _ _ _ _ _) hconn ?_
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := vecs_swapW w
  have hV := parentsAt_valid w
  have hp : ((parentsAt w).odd.num + (parentsAt w).odd.den) % 2 = 1 := hV.odd_parity
  have hq : ((parentsAt w).even.num + (parentsAt w).even.den) % 2 = 0 := hV.even_parity
  intro i pR hi
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hi
  have hlt' : i < 6 := by simpa [tileEvenPieces] using hlt
  cases hWo : W1Odd w <;> rcases i with _ | _ | _ | _ | _ | _ | i
  · refine ⟨(tileOddPieces S pO pE lE w)[5]'(by simp [tileOddPieces]), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par
    · rot_id
    · rot_id
    · rot_id
    · intro x _ _; simp [tileOddPieces, stdPiece]
  · refine ⟨(tileOddPieces S pO pE lE w)[4]'(by simp [tileOddPieces]), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par
    · rot_id
    · rot_id
    · rot_id
    · intro x _ _; simp [tileOddPieces, stdPiece]
  · refine ⟨(tileOddPieces S pO pE lE w)[3]'(by simp [tileOddPieces]), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par
    · rot_id
    · rot_id
    · rot_id
    · intro x _ _; simp [tileOddPieces, stdPiece]
  · refine ⟨(tileOddPieces S pO pE lE w)[2]'(by simp [tileOddPieces]), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par
    · rot_id
    · rot_id
    · rot_id
    · intro x _ _; simp [tileOddPieces, stdPiece]
  · refine ⟨(tileOddPieces S pO pE lE w)[0]'(by simp [tileOddPieces]), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par
    · rot_id
    · rot_id
    · rot_id
    · intro x _ _; simp [tileOddPieces, stdPiece]
  · refine ⟨(tileOddPieces S pO pE lE w)[1]'(by simp [tileOddPieces]), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par
    · rot_id
    · rot_id
    · rot_id
    · intro x _ _; simp [tileOddPieces, stdPiece]
  · omega
  · refine ⟨(tileOddPieces S pO pE lE w)[3]'(by simp [tileOddPieces]), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par
    · rot_id
    · rot_id
    · rot_id
    · intro x _ _; simp [tileOddPieces, stdPiece]
  · refine ⟨(tileOddPieces S pO pE lE w)[2]'(by simp [tileOddPieces]), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par
    · rot_id
    · rot_id
    · rot_id
    · intro x _ _; simp [tileOddPieces, stdPiece]
  · refine ⟨(tileOddPieces S pO pE lE w)[5]'(by simp [tileOddPieces]), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par
    · rot_id
    · rot_id
    · rot_id
    · intro x _ _; simp [tileOddPieces, stdPiece]
  · refine ⟨(tileOddPieces S pO pE lE w)[4]'(by simp [tileOddPieces]), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par
    · rot_id
    · rot_id
    · rot_id
    · intro x _ _; simp [tileOddPieces, stdPiece]
  · refine ⟨(tileOddPieces S pO pE lE w)[1]'(by simp [tileOddPieces]), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par
    · rot_id
    · rot_id
    · rot_id
    · intro x _ _; simp [tileOddPieces, stdPiece]
  · refine ⟨(tileOddPieces S pO pE lE w)[0]'(by simp [tileOddPieces]), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par
    · rot_id
    · rot_id
    · rot_id
    · intro x _ _; simp [tileOddPieces, stdPiece]
  · omega

/-- (c) of `lemma:tile-odometer-existence`, even standard child, raw form: the odd child of `swapW w` against the even child of
`w`, under `z(x) = i x + v_{q_0,1} - i`. The pieces pair as `0 1 2 3 4 5 ↦ 4 5 2 3 0 1` (`W_1` odd) and `5 4 0 1 2 3` (`W_1` even);
the L-corrected pieces after a `2` pair with the L-rotation of the parents. -/
theorem tileEven_rawRot (S : WeakData) (pO pE : Word → PartialOdometer) (lE lO : Word → Bool → Bool → PartialOdometer)
    (w : Word) (o oR : PartialOdometer)
    (ho : RespectsPieces o (tileEvenPieces S pO pE lO w))
    (hoR : RespectsPieces oR (tileOddPieces S pO pE lE (swapW w)))
    (hconn : (overlapGraph (goodPart (tileOddPieces S pO pE lE (swapW w)))).Connected)
    (hP : RawRot (regOdo S pO pE (regsAt w).1 true) (regOdo S pO pE (regsAt (swapW w)).2 false) (vP1 w - ((0 : ℤ), (1 : ℤ))) 0)
    (hQ : RawRot (regOdo S pO pE (regsAt w).2 false) (regOdo S pO pE (regsAt (swapW w)).1 true) (vQ1 w - ((0 : ℤ), (1 : ℤ))) 0)
    (hL : w.getLast? = some Digit.two → ∀ plus : Bool,
      RawRot (lO w.dropLast plus false) (lE (swapW w.dropLast) (plus == W1Odd w) false) (vP1 w - ((0 : ℤ), (1 : ℤ))) 0) :
    RawRot o oR (texV1Even ((parentsAt w).current .even) - ((0 : ℤ), (1 : ℤ))) 0 := by
  refine rawRot_of_pairing o oR _ _ _ _ ho hoR (tileOddPieces_covered _ _ _ _ _) hconn ?_
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := vecs_swapW w
  have hV := parentsAt_valid w
  have hp : ((parentsAt w).odd.num + (parentsAt w).odd.den) % 2 = 1 := hV.odd_parity
  have hq : ((parentsAt w).even.num + (parentsAt w).even.den) % 2 = 0 := hV.even_parity
  intro i pR hi
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hi
  have hlt' : i < 6 := by simpa [tileOddPieces] using hlt
  cases hWo : W1Odd w <;> rcases i with _ | _ | _ | _ | _ | _ | i
  · refine ⟨(tileEvenPieces S pO pE lO w)[5]'(by simp [tileEvenPieces]), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par
    · rot_id
    · rot_id
    · rot_id
    · intro x _ _; simp [tileEvenPieces, stdPiece]
  · refine ⟨(tileEvenPieces S pO pE lO w)[4]'(by simp [tileEvenPieces]), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par
    · rot_id
    · rot_id
    · rot_id
    · intro x _ _; simp [tileEvenPieces, stdPiece]
  · refine ⟨(tileEvenPieces S pO pE lO w)[0]'(by simp [tileEvenPieces]), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par
    · rot_id
    · rot_id
    · rot_id
    · intro x _ _; simp [tileEvenPieces, stdPiece]
  · refine ⟨(tileEvenPieces S pO pE lO w)[1]'(by simp [tileEvenPieces]), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par
    · rot_id
    · rot_id
    · rot_id
    · intro x _ _; simp [tileEvenPieces, stdPiece]
  · refine ⟨(tileEvenPieces S pO pE lO w)[2]'(by simp [tileEvenPieces]), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par
    · rot_id
    · rot_id
    · rot_id
    · intro x _ _; simp [tileEvenPieces, stdPiece]
  · refine ⟨(tileEvenPieces S pO pE lO w)[3]'(by simp [tileEvenPieces]), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par
    · rot_id
    · rot_id
    · rot_id
    · intro x _ _; simp [tileEvenPieces, stdPiece]
  · omega
  · refine ⟨(tileEvenPieces S pO pE lO w)[4]'(by simp [tileEvenPieces]), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par
    · rot_id
    · rot_id
    · rot_id
    · intro x _ _; simp [tileEvenPieces, stdPiece]
  · refine ⟨(tileEvenPieces S pO pE lO w)[5]'(by simp [tileEvenPieces]), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par
    · rot_id
    · rot_id
    · rot_id
    · intro x _ _; simp [tileEvenPieces, stdPiece]
  · refine ⟨(tileEvenPieces S pO pE lO w)[2]'(by simp [tileEvenPieces]), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par
    · rot_id
    · rot_id
    · rot_id
    · intro x _ _; simp [tileEvenPieces, stdPiece]
  · refine ⟨(tileEvenPieces S pO pE lO w)[3]'(by simp [tileEvenPieces]), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par
    · rot_id
    · rot_id
    · rot_id
    · intro x _ _; simp [tileEvenPieces, stdPiece]
  · refine ⟨(tileEvenPieces S pO pE lO w)[0]'(by simp [tileEvenPieces]), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par
    · rot_id
    · rot_id
    · rot_id
    · intro x _ _; simp [tileEvenPieces, stdPiece]
  · refine ⟨(tileEvenPieces S pO pE lO w)[1]'(by simp [tileEvenPieces]), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par
    · rot_id
    · rot_id
    · rot_id
    · intro x _ _; simp [tileEvenPieces, stdPiece]
  · omega

/-! ### The alternate children -/

open FLatticePaper.Tiles.SurgicalAlt (AltCoeff altTypeOf altQ1Coeff altP1Coeff altP0Coeff altQ0Coeff coeffOff coeffAffine)
open FLatticePaper.Tiles.SurgicalDict (altShifts)

theorem phase_snoc_one (u : Word) : (phase (u ++ [.one]) == 1) = !(phase u == 1) := by
  unfold phase
  rw [List.count_append]
  rcases Nat.mod_two_eq_zero_or_one (u.count .one) with h | h <;> simp [Nat.add_mod, h]

theorem phase_snoc_two (u : Word) : (phase (u ++ [.two]) == 1) = (phase u == 1) := by
  unfold phase
  rw [List.count_append]
  simp

theorem phase_snoc_three (u : Word) : (phase (u ++ [.three]) == 1) = (phase u == 1) := by
  unfold phase
  rw [List.count_append]
  simp

/-- The rotation `(c_r, γ_r)` of the alternate even parent `ô(q_1)` of `w` (the piece kept after a `1` or a `3`), in the vectors of
the parents of `w`: `altCf` of the even register (`altCf_even_reg`). -/
def altParQ (w : Word) : Site × Site :=
  match w.getLast? with
  | some .three => if W1Odd w then ((2 : ℤ) • vQ1 w + vP2 w - vP1 w - ((0 : ℤ), (1 : ℤ)), mulI (aP2 w)) else (vQ1 w - ((0 : ℤ), (1 : ℤ)), 0)
  | some .one => if W1Odd w then (vQ1 w - ((0 : ℤ), (1 : ℤ)), 0) else (vP1 w + vQ2 w - vP2 w - ((0 : ℤ), (1 : ℤ)), mulI (aQ2 w - aP2 w))
  | _ => (0, 0)

/-- The rotation of the alternate odd parent `ô(p_1)` of `w` (kept after a `1` or a `2`): `altCf` of the odd register
(`altCf_odd_reg`). -/
def altParP (w : Word) : Site × Site :=
  match w.getLast? with
  | some .two => if W1Odd w then (vP1 w - vQ1 w - ((0 : ℤ), (1 : ℤ)), 0) else (vP1 w + vP2 w - vQ2 w - ((0 : ℤ), (1 : ℤ)), mulI (aP2 w - aQ2 w))
  | some .one => if W1Odd w then (vP1 w + vQ2 w - vP2 w - ((0 : ℤ), (1 : ℤ)), mulI (aQ2 w - aP2 w)) else (vQ1 w - ((0 : ℤ), (1 : ℤ)), 0)
  | _ => (0, 0)

set_option hygiene false in
/-- `altCf` of a register word against `altParQ`, `altParP`. -/
macro "reg_cf" : tactic => `(tactic| (
  rcases Bool.eq_false_or_eq_true (phase u == 1) with h | h <;> simp only [h] <;>
    simp only [vP1, vP2, vQ1, vQ2, aP2, aQ2, parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine,
      texV1Odd, texV1Even, texV2, offsetA, mulI, Bool.not_true, Bool.not_false, ↓reduceIte, Bool.false_eq_true] <;>
    refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;> simp <;> ring))

theorem altCf_even_reg (u : Word) (d : Digit) (hd : d = .one ∨ d = .three) :
    altCf u false = altParQ (u ++ [d]) := by
  rcases hd with rfl | rfl
  · have hph := phase_snoc_one u
    unfold altParQ altCf
    simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, W1Odd, hph]
    reg_cf
  · have hph := phase_snoc_three u
    unfold altParQ altCf
    simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, W1Odd, hph]
    reg_cf

theorem altCf_odd_reg (u : Word) (d : Digit) (hd : d = .one ∨ d = .two) :
    altCf u true = altParP (u ++ [d]) := by
  rcases hd with rfl | rfl
  · have hph := phase_snoc_one u
    unfold altParP altCf
    simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, W1Odd, hph]
    reg_cf
  · have hph := phase_snoc_two u
    unfold altParP altCf
    simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, W1Odd, hph]
    reg_cf

/-- The matching condition of `rawRot_of_pairing`. -/
def PairingOK (ps psR : List Piece) (c γ : Site) : Prop :=
  ∀ (i : ℕ) (pR : Piece), psR[i]? = some pR → ∃ p ∈ ps, ∃ cr γr : Site,
    RawRot p.odo pR.odo cr γr ∧ mulI pR.off = p.off + cr - c ∧ EvenSite pR.off ∧
    pR.aff = rotR p.aff + hHalf pR.off + γ - γr ∧ (∀ x ∈ pR.placed, x ∉ pR.exc → mulI x + c ∉ p.exc)

set_option hygiene false in
/-- The list simplification of the alternate decompositions once `W_1` and the last letter are fixed. -/
macro "alt_lists" : tactic => `(tactic| (
  simp only [tileAltOddPieces, tileAltEvenPieces, altTypeOf, getLast_swapW, hl, Option.map_some, Option.map_none,
    Option.bind_some, Option.bind_none, altQ1Coeff, altP1Coeff, Digit.swapTwoThree, List.cons_append, List.nil_append,
    List.getElem_cons_succ, List.getElem_cons_zero, stdPiece, corr_swapW_two, corr_swapW_three, W1Odd_swapW, dropLast_swapW,
    hWo, reduceCtorEq, ↓reduceIte, Bool.false_eq_true, decide_true, decide_false, Option.some.injEq, List.length_cons,
    List.length_nil, Piece.placed]))

set_option hygiene false in
/-- The same simplification at the bound `hlt`. -/
macro "alt_lists_hlt" : tactic => `(tactic| (
  simp only [tileAltOddPieces, tileAltEvenPieces, altTypeOf, getLast_swapW, hl, Option.map_some, Option.map_none,
    Option.bind_some, Option.bind_none, altQ1Coeff, altP1Coeff, Digit.swapTwoThree, List.cons_append, List.nil_append,
    W1Odd_swapW, hWo, reduceCtorEq, ↓reduceIte, Bool.false_eq_true, List.length_cons, List.length_nil, List.length_append,
    List.length_singleton] at hlt))

set_option hygiene false in
/-- The piece odometers of an alternate pairing. -/
macro "rot_par_alt" : tactic => `(tactic| (
  alt_lists
  first
  | exact hP
  | exact hQ
  | exact hA
  | simpa [hWo] using hL hl true
  | simpa [hWo] using hL hl false))

set_option hygiene false in
/-- The offset, parity and affine identities of an alternate pairing. -/
macro "rot_id_alt" : tactic => `(tactic| (
  alt_lists
  try simp only [altOff, altAff, coeffOff, coeffAffine, altP0Coeff, altQ0Coeff, altShifts, altCf, altParQ, altParP, aP2, aQ2, hl,
    W1Odd_swapW, hWo, reduceCtorEq, ↓reduceIte, Bool.false_eq_true]
  try simp only [e1, e2, e3, e4, e5, e6]
  try simp only [vP1, vP2, vQ1, vQ2, texV1Odd, texV1Even, texV2, Parents.current, Parents.combine, offsetA, mulI, rotR, hHalf,
    EvenSite, Prod.smul_mk, smul_eq_mul]
  all_goals first
  | omega
  | (refine Prod.ext ?_ ?_ <;> simp <;> omega)
  | (simp <;> omega)))

set_option hygiene false in
/-- The exceptional sets of standard pieces are empty. -/
macro "rot_exc_alt" : tactic => `(tactic| (intro x _ _; alt_lists; simp))

theorem tileAltOdd_rawRot_even_none (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (lE lO : Word → Bool → Bool → PartialOdometer)
    (w : Word) (hWo : W1Odd w = false) (hl : w.getLast? = none)
    (hP : RawRot (regOdo S pO pE (regsAt w).1 true) (regOdo S pO pE (regsAt (swapW w)).2 false) (vP1 w - ((0 : ℤ), (1 : ℤ))) 0)
    (hQ : RawRot (regOdo S pO pE (regsAt w).2 false) (regOdo S pO pE (regsAt (swapW w)).1 true) (vQ1 w - ((0 : ℤ), (1 : ℤ))) 0) :
    PairingOK (tileAltOddPieces S pO pE aO aE lO w) (tileAltEvenPieces S pO pE aO aE lE (swapW w)) (altCf w true).1 (altCf w true).2 := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := vecs_swapW w
  have hV := parentsAt_valid w
  have hp : ((parentsAt w).odd.num + (parentsAt w).odd.den) % 2 = 1 := hV.odd_parity
  have hq : ((parentsAt w).even.num + (parentsAt w).even.den) % 2 = 0 := hV.even_parity
  intro i pR hi
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hi
  have hlt' : i < 6 := by alt_lists_hlt; omega
  rcases i with _ | _ | _ | _ | _ | _ | _
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[1]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[0]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[3]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[2]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[5]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[4]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · omega

theorem tileAltOdd_rawRot_even_one (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (lE lO : Word → Bool → Bool → PartialOdometer)
    (w : Word) (hWo : W1Odd w = false) (hl : w.getLast? = some Digit.one)
    (hP : RawRot (regOdo S pO pE (regsAt w).1 true) (regOdo S pO pE (regsAt (swapW w)).2 false) (vP1 w - ((0 : ℤ), (1 : ℤ))) 0)
    (hQ : RawRot (regOdo S pO pE (regsAt w).2 false) (regOdo S pO pE (regsAt (swapW w)).1 true) (vQ1 w - ((0 : ℤ), (1 : ℤ))) 0)
    (hA : RawRot (regOdo S aO aE (regsAt w).2 false) (regOdo S aO aE (regsAt (swapW w)).1 true) (altParQ w).1 (altParQ w).2) :
    PairingOK (tileAltOddPieces S pO pE aO aE lO w) (tileAltEvenPieces S pO pE aO aE lE (swapW w)) (altCf w true).1 (altCf w true).2 := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := vecs_swapW w
  have hV := parentsAt_valid w
  have hp : ((parentsAt w).odd.num + (parentsAt w).odd.den) % 2 = 1 := hV.odd_parity
  have hq : ((parentsAt w).even.num + (parentsAt w).even.den) % 2 = 0 := hV.even_parity
  intro i pR hi
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hi
  have hlt' : i < 7 := by alt_lists_hlt; omega
  rcases i with _ | _ | _ | _ | _ | _ | _ | _
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[1]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[0]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[3]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[2]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[5]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[4]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[6]'(by alt_lists; simp), List.getElem_mem _, (altParQ w).1, (altParQ w).2, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · omega

theorem tileAltOdd_rawRot_even_two (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (lE lO : Word → Bool → Bool → PartialOdometer)
    (w : Word) (hWo : W1Odd w = false) (hl : w.getLast? = some Digit.two)
    (hP : RawRot (regOdo S pO pE (regsAt w).1 true) (regOdo S pO pE (regsAt (swapW w)).2 false) (vP1 w - ((0 : ℤ), (1 : ℤ))) 0)
    (hQ : RawRot (regOdo S pO pE (regsAt w).2 false) (regOdo S pO pE (regsAt (swapW w)).1 true) (vQ1 w - ((0 : ℤ), (1 : ℤ))) 0)
    (hL : w.getLast? = some Digit.two → ∀ plus : Bool,
      RawRot (lO w.dropLast plus true) (lE (swapW w.dropLast) (plus == W1Odd w) true) (vP1 w - ((0 : ℤ), (1 : ℤ))) 0) :
    PairingOK (tileAltOddPieces S pO pE aO aE lO w) (tileAltEvenPieces S pO pE aO aE lE (swapW w)) (altCf w true).1 (altCf w true).2 := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := vecs_swapW w
  have hV := parentsAt_valid w
  have hp : ((parentsAt w).odd.num + (parentsAt w).odd.den) % 2 = 1 := hV.odd_parity
  have hq : ((parentsAt w).even.num + (parentsAt w).even.den) % 2 = 0 := hV.even_parity
  intro i pR hi
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hi
  have hlt' : i < 6 := by alt_lists_hlt; omega
  rcases i with _ | _ | _ | _ | _ | _ | _
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[1]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[0]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[3]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[2]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[5]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[4]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · omega

theorem tileAltOdd_rawRot_even_three (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (lE lO : Word → Bool → Bool → PartialOdometer)
    (w : Word) (hWo : W1Odd w = false) (hl : w.getLast? = some Digit.three)
    (hP : RawRot (regOdo S pO pE (regsAt w).1 true) (regOdo S pO pE (regsAt (swapW w)).2 false) (vP1 w - ((0 : ℤ), (1 : ℤ))) 0)
    (hQ : RawRot (regOdo S pO pE (regsAt w).2 false) (regOdo S pO pE (regsAt (swapW w)).1 true) (vQ1 w - ((0 : ℤ), (1 : ℤ))) 0)
    (hA : RawRot (regOdo S aO aE (regsAt w).2 false) (regOdo S aO aE (regsAt (swapW w)).1 true) (altParQ w).1 (altParQ w).2) :
    PairingOK (tileAltOddPieces S pO pE aO aE lO w) (tileAltEvenPieces S pO pE aO aE lE (swapW w)) (altCf w true).1 (altCf w true).2 := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := vecs_swapW w
  have hV := parentsAt_valid w
  have hp : ((parentsAt w).odd.num + (parentsAt w).odd.den) % 2 = 1 := hV.odd_parity
  have hq : ((parentsAt w).even.num + (parentsAt w).even.den) % 2 = 0 := hV.even_parity
  intro i pR hi
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hi
  have hlt' : i < 7 := by alt_lists_hlt; omega
  rcases i with _ | _ | _ | _ | _ | _ | _ | _
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[1]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[0]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[3]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[2]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[5]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[4]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[6]'(by alt_lists; simp), List.getElem_mem _, (altParQ w).1, (altParQ w).2, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · omega

theorem tileAltOdd_rawRot_odd_none (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (lE lO : Word → Bool → Bool → PartialOdometer)
    (w : Word) (hWo : W1Odd w = true) (hl : w.getLast? = none)
    (hP : RawRot (regOdo S pO pE (regsAt w).1 true) (regOdo S pO pE (regsAt (swapW w)).2 false) (vP1 w - ((0 : ℤ), (1 : ℤ))) 0)
    (hQ : RawRot (regOdo S pO pE (regsAt w).2 false) (regOdo S pO pE (regsAt (swapW w)).1 true) (vQ1 w - ((0 : ℤ), (1 : ℤ))) 0) :
    PairingOK (tileAltOddPieces S pO pE aO aE lO w) (tileAltEvenPieces S pO pE aO aE lE (swapW w)) (altCf w true).1 (altCf w true).2 := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := vecs_swapW w
  have hV := parentsAt_valid w
  have hp : ((parentsAt w).odd.num + (parentsAt w).odd.den) % 2 = 1 := hV.odd_parity
  have hq : ((parentsAt w).even.num + (parentsAt w).even.den) % 2 = 0 := hV.even_parity
  intro i pR hi
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hi
  have hlt' : i < 6 := by alt_lists_hlt; omega
  rcases i with _ | _ | _ | _ | _ | _ | _
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[2]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[3]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[0]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[1]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[4]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[5]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · omega

theorem tileAltOdd_rawRot_odd_one (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (lE lO : Word → Bool → Bool → PartialOdometer)
    (w : Word) (hWo : W1Odd w = true) (hl : w.getLast? = some Digit.one)
    (hP : RawRot (regOdo S pO pE (regsAt w).1 true) (regOdo S pO pE (regsAt (swapW w)).2 false) (vP1 w - ((0 : ℤ), (1 : ℤ))) 0)
    (hQ : RawRot (regOdo S pO pE (regsAt w).2 false) (regOdo S pO pE (regsAt (swapW w)).1 true) (vQ1 w - ((0 : ℤ), (1 : ℤ))) 0)
    (hA : RawRot (regOdo S aO aE (regsAt w).2 false) (regOdo S aO aE (regsAt (swapW w)).1 true) (altParQ w).1 (altParQ w).2) :
    PairingOK (tileAltOddPieces S pO pE aO aE lO w) (tileAltEvenPieces S pO pE aO aE lE (swapW w)) (altCf w true).1 (altCf w true).2 := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := vecs_swapW w
  have hV := parentsAt_valid w
  have hp : ((parentsAt w).odd.num + (parentsAt w).odd.den) % 2 = 1 := hV.odd_parity
  have hq : ((parentsAt w).even.num + (parentsAt w).even.den) % 2 = 0 := hV.even_parity
  intro i pR hi
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hi
  have hlt' : i < 7 := by alt_lists_hlt; omega
  rcases i with _ | _ | _ | _ | _ | _ | _ | _
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[2]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[3]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[0]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[1]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[4]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[5]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[6]'(by alt_lists; simp), List.getElem_mem _, (altParQ w).1, (altParQ w).2, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · omega

theorem tileAltOdd_rawRot_odd_two (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (lE lO : Word → Bool → Bool → PartialOdometer)
    (w : Word) (hWo : W1Odd w = true) (hl : w.getLast? = some Digit.two)
    (hP : RawRot (regOdo S pO pE (regsAt w).1 true) (regOdo S pO pE (regsAt (swapW w)).2 false) (vP1 w - ((0 : ℤ), (1 : ℤ))) 0)
    (hQ : RawRot (regOdo S pO pE (regsAt w).2 false) (regOdo S pO pE (regsAt (swapW w)).1 true) (vQ1 w - ((0 : ℤ), (1 : ℤ))) 0)
    (hL : w.getLast? = some Digit.two → ∀ plus : Bool,
      RawRot (lO w.dropLast plus true) (lE (swapW w.dropLast) (plus == W1Odd w) true) (vP1 w - ((0 : ℤ), (1 : ℤ))) 0) :
    PairingOK (tileAltOddPieces S pO pE aO aE lO w) (tileAltEvenPieces S pO pE aO aE lE (swapW w)) (altCf w true).1 (altCf w true).2 := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := vecs_swapW w
  have hV := parentsAt_valid w
  have hp : ((parentsAt w).odd.num + (parentsAt w).odd.den) % 2 = 1 := hV.odd_parity
  have hq : ((parentsAt w).even.num + (parentsAt w).even.den) % 2 = 0 := hV.even_parity
  intro i pR hi
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hi
  have hlt' : i < 6 := by alt_lists_hlt; omega
  rcases i with _ | _ | _ | _ | _ | _ | _
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[2]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[3]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[0]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[1]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[4]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[5]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · omega

theorem tileAltOdd_rawRot_odd_three (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (lE lO : Word → Bool → Bool → PartialOdometer)
    (w : Word) (hWo : W1Odd w = true) (hl : w.getLast? = some Digit.three)
    (hP : RawRot (regOdo S pO pE (regsAt w).1 true) (regOdo S pO pE (regsAt (swapW w)).2 false) (vP1 w - ((0 : ℤ), (1 : ℤ))) 0)
    (hQ : RawRot (regOdo S pO pE (regsAt w).2 false) (regOdo S pO pE (regsAt (swapW w)).1 true) (vQ1 w - ((0 : ℤ), (1 : ℤ))) 0)
    (hA : RawRot (regOdo S aO aE (regsAt w).2 false) (regOdo S aO aE (regsAt (swapW w)).1 true) (altParQ w).1 (altParQ w).2) :
    PairingOK (tileAltOddPieces S pO pE aO aE lO w) (tileAltEvenPieces S pO pE aO aE lE (swapW w)) (altCf w true).1 (altCf w true).2 := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := vecs_swapW w
  have hV := parentsAt_valid w
  have hp : ((parentsAt w).odd.num + (parentsAt w).odd.den) % 2 = 1 := hV.odd_parity
  have hq : ((parentsAt w).even.num + (parentsAt w).even.den) % 2 = 0 := hV.even_parity
  intro i pR hi
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hi
  have hlt' : i < 7 := by alt_lists_hlt; omega
  rcases i with _ | _ | _ | _ | _ | _ | _ | _
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[2]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[3]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[0]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[1]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[4]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[5]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltOddPieces S pO pE aO aE lO w)[6]'(by alt_lists; simp), List.getElem_mem _, (altParQ w).1, (altParQ w).2, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · omega

/-- (c) of `lemma:tile-odometer-existence` for the odd alternate child, raw form: the six copies pair by an
involution and the alternate parent piece with the alternate parent piece, under `z(x) = i x + c_f` with `γ` (`altCf`). -/
theorem tileAltOdd_rawRot (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (lE lO : Word → Bool → Bool → PartialOdometer)
    (w : Word) (o oR : PartialOdometer)
    (ho : RespectsPieces o (tileAltOddPieces S pO pE aO aE lO w))
    (hoR : RespectsPieces oR (tileAltEvenPieces S pO pE aO aE lE (swapW w)))
    (hcov : PiecesCovered (tileAltEvenPieces S pO pE aO aE lE (swapW w)))
    (hconn : (overlapGraph (goodPart (tileAltEvenPieces S pO pE aO aE lE (swapW w)))).Connected)
    (hP : RawRot (regOdo S pO pE (regsAt w).1 true) (regOdo S pO pE (regsAt (swapW w)).2 false) (vP1 w - ((0 : ℤ), (1 : ℤ))) 0)
    (hQ : RawRot (regOdo S pO pE (regsAt w).2 false) (regOdo S pO pE (regsAt (swapW w)).1 true) (vQ1 w - ((0 : ℤ), (1 : ℤ))) 0)
    (hA : (w.getLast? = some Digit.one ∨ w.getLast? = some Digit.three) → RawRot (regOdo S aO aE (regsAt w).2 false) (regOdo S aO aE (regsAt (swapW w)).1 true) (altParQ w).1 (altParQ w).2)
    (hL : w.getLast? = some Digit.two → ∀ plus : Bool,
      RawRot (lO w.dropLast plus true) (lE (swapW w.dropLast) (plus == W1Odd w) true) (vP1 w - ((0 : ℤ), (1 : ℤ))) 0) :
    RawRot o oR (altCf w true).1 (altCf w true).2 := by
  refine rawRot_of_pairing o oR _ _ _ _ ho hoR hcov hconn ?_
  cases hWo : W1Odd w <;> rcases hl : w.getLast? with _ | d
  · exact tileAltOdd_rawRot_even_none S pO pE aO aE lE lO w hWo hl hP hQ
  · cases d
    · exact tileAltOdd_rawRot_even_one S pO pE aO aE lE lO w hWo hl hP hQ (hA (Or.inl hl))
    · exact tileAltOdd_rawRot_even_two S pO pE aO aE lE lO w hWo hl hP hQ hL
    · exact tileAltOdd_rawRot_even_three S pO pE aO aE lE lO w hWo hl hP hQ (hA (Or.inr hl))
  · exact tileAltOdd_rawRot_odd_none S pO pE aO aE lE lO w hWo hl hP hQ
  · cases d
    · exact tileAltOdd_rawRot_odd_one S pO pE aO aE lE lO w hWo hl hP hQ (hA (Or.inl hl))
    · exact tileAltOdd_rawRot_odd_two S pO pE aO aE lE lO w hWo hl hP hQ hL
    · exact tileAltOdd_rawRot_odd_three S pO pE aO aE lE lO w hWo hl hP hQ (hA (Or.inr hl))

theorem tileAltEven_rawRot_even_none (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (lE lO : Word → Bool → Bool → PartialOdometer)
    (w : Word) (hWo : W1Odd w = false) (hl : w.getLast? = none)
    (hP : RawRot (regOdo S pO pE (regsAt w).1 true) (regOdo S pO pE (regsAt (swapW w)).2 false) (vP1 w - ((0 : ℤ), (1 : ℤ))) 0)
    (hQ : RawRot (regOdo S pO pE (regsAt w).2 false) (regOdo S pO pE (regsAt (swapW w)).1 true) (vQ1 w - ((0 : ℤ), (1 : ℤ))) 0) :
    PairingOK (tileAltEvenPieces S pO pE aO aE lE w) (tileAltOddPieces S pO pE aO aE lO (swapW w)) (altCf w false).1 (altCf w false).2 := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := vecs_swapW w
  have hV := parentsAt_valid w
  have hp : ((parentsAt w).odd.num + (parentsAt w).odd.den) % 2 = 1 := hV.odd_parity
  have hq : ((parentsAt w).even.num + (parentsAt w).even.den) % 2 = 0 := hV.even_parity
  intro i pR hi
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hi
  have hlt' : i < 6 := by alt_lists_hlt; omega
  rcases i with _ | _ | _ | _ | _ | _ | _
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[2]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[3]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[0]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[1]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[4]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[5]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · omega

theorem tileAltEven_rawRot_even_one (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (lE lO : Word → Bool → Bool → PartialOdometer)
    (w : Word) (hWo : W1Odd w = false) (hl : w.getLast? = some Digit.one)
    (hP : RawRot (regOdo S pO pE (regsAt w).1 true) (regOdo S pO pE (regsAt (swapW w)).2 false) (vP1 w - ((0 : ℤ), (1 : ℤ))) 0)
    (hQ : RawRot (regOdo S pO pE (regsAt w).2 false) (regOdo S pO pE (regsAt (swapW w)).1 true) (vQ1 w - ((0 : ℤ), (1 : ℤ))) 0)
    (hA : RawRot (regOdo S aO aE (regsAt w).1 true) (regOdo S aO aE (regsAt (swapW w)).2 false) (altParP w).1 (altParP w).2) :
    PairingOK (tileAltEvenPieces S pO pE aO aE lE w) (tileAltOddPieces S pO pE aO aE lO (swapW w)) (altCf w false).1 (altCf w false).2 := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := vecs_swapW w
  have hV := parentsAt_valid w
  have hp : ((parentsAt w).odd.num + (parentsAt w).odd.den) % 2 = 1 := hV.odd_parity
  have hq : ((parentsAt w).even.num + (parentsAt w).even.den) % 2 = 0 := hV.even_parity
  intro i pR hi
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hi
  have hlt' : i < 7 := by alt_lists_hlt; omega
  rcases i with _ | _ | _ | _ | _ | _ | _ | _
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[2]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[3]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[0]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[1]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[4]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[5]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[6]'(by alt_lists; simp), List.getElem_mem _, (altParP w).1, (altParP w).2, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · omega

theorem tileAltEven_rawRot_even_two (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (lE lO : Word → Bool → Bool → PartialOdometer)
    (w : Word) (hWo : W1Odd w = false) (hl : w.getLast? = some Digit.two)
    (hP : RawRot (regOdo S pO pE (regsAt w).1 true) (regOdo S pO pE (regsAt (swapW w)).2 false) (vP1 w - ((0 : ℤ), (1 : ℤ))) 0)
    (hQ : RawRot (regOdo S pO pE (regsAt w).2 false) (regOdo S pO pE (regsAt (swapW w)).1 true) (vQ1 w - ((0 : ℤ), (1 : ℤ))) 0)
    (hA : RawRot (regOdo S aO aE (regsAt w).1 true) (regOdo S aO aE (regsAt (swapW w)).2 false) (altParP w).1 (altParP w).2) :
    PairingOK (tileAltEvenPieces S pO pE aO aE lE w) (tileAltOddPieces S pO pE aO aE lO (swapW w)) (altCf w false).1 (altCf w false).2 := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := vecs_swapW w
  have hV := parentsAt_valid w
  have hp : ((parentsAt w).odd.num + (parentsAt w).odd.den) % 2 = 1 := hV.odd_parity
  have hq : ((parentsAt w).even.num + (parentsAt w).even.den) % 2 = 0 := hV.even_parity
  intro i pR hi
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hi
  have hlt' : i < 7 := by alt_lists_hlt; omega
  rcases i with _ | _ | _ | _ | _ | _ | _ | _
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[2]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[3]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[0]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[1]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[4]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[5]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[6]'(by alt_lists; simp), List.getElem_mem _, (altParP w).1, (altParP w).2, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · omega

theorem tileAltEven_rawRot_even_three (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (lE lO : Word → Bool → Bool → PartialOdometer)
    (w : Word) (hWo : W1Odd w = false) (hl : w.getLast? = some Digit.three)
    (hP : RawRot (regOdo S pO pE (regsAt w).1 true) (regOdo S pO pE (regsAt (swapW w)).2 false) (vP1 w - ((0 : ℤ), (1 : ℤ))) 0)
    (hQ : RawRot (regOdo S pO pE (regsAt w).2 false) (regOdo S pO pE (regsAt (swapW w)).1 true) (vQ1 w - ((0 : ℤ), (1 : ℤ))) 0)
    (hL : w.getLast? = some Digit.three → ∀ plus : Bool,
      RawRot (lE w.dropLast plus true) (lO (swapW w.dropLast) (plus != W1Odd w) true) (vQ1 w - ((0 : ℤ), (1 : ℤ))) 0) :
    PairingOK (tileAltEvenPieces S pO pE aO aE lE w) (tileAltOddPieces S pO pE aO aE lO (swapW w)) (altCf w false).1 (altCf w false).2 := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := vecs_swapW w
  have hV := parentsAt_valid w
  have hp : ((parentsAt w).odd.num + (parentsAt w).odd.den) % 2 = 1 := hV.odd_parity
  have hq : ((parentsAt w).even.num + (parentsAt w).even.den) % 2 = 0 := hV.even_parity
  intro i pR hi
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hi
  have hlt' : i < 6 := by alt_lists_hlt; omega
  rcases i with _ | _ | _ | _ | _ | _ | _
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[2]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[3]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[0]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[1]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[4]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[5]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · omega

theorem tileAltEven_rawRot_odd_none (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (lE lO : Word → Bool → Bool → PartialOdometer)
    (w : Word) (hWo : W1Odd w = true) (hl : w.getLast? = none)
    (hP : RawRot (regOdo S pO pE (regsAt w).1 true) (regOdo S pO pE (regsAt (swapW w)).2 false) (vP1 w - ((0 : ℤ), (1 : ℤ))) 0)
    (hQ : RawRot (regOdo S pO pE (regsAt w).2 false) (regOdo S pO pE (regsAt (swapW w)).1 true) (vQ1 w - ((0 : ℤ), (1 : ℤ))) 0) :
    PairingOK (tileAltEvenPieces S pO pE aO aE lE w) (tileAltOddPieces S pO pE aO aE lO (swapW w)) (altCf w false).1 (altCf w false).2 := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := vecs_swapW w
  have hV := parentsAt_valid w
  have hp : ((parentsAt w).odd.num + (parentsAt w).odd.den) % 2 = 1 := hV.odd_parity
  have hq : ((parentsAt w).even.num + (parentsAt w).even.den) % 2 = 0 := hV.even_parity
  intro i pR hi
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hi
  have hlt' : i < 6 := by alt_lists_hlt; omega
  rcases i with _ | _ | _ | _ | _ | _ | _
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[1]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[0]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[3]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[2]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[5]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[4]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · omega

theorem tileAltEven_rawRot_odd_one (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (lE lO : Word → Bool → Bool → PartialOdometer)
    (w : Word) (hWo : W1Odd w = true) (hl : w.getLast? = some Digit.one)
    (hP : RawRot (regOdo S pO pE (regsAt w).1 true) (regOdo S pO pE (regsAt (swapW w)).2 false) (vP1 w - ((0 : ℤ), (1 : ℤ))) 0)
    (hQ : RawRot (regOdo S pO pE (regsAt w).2 false) (regOdo S pO pE (regsAt (swapW w)).1 true) (vQ1 w - ((0 : ℤ), (1 : ℤ))) 0)
    (hA : RawRot (regOdo S aO aE (regsAt w).1 true) (regOdo S aO aE (regsAt (swapW w)).2 false) (altParP w).1 (altParP w).2) :
    PairingOK (tileAltEvenPieces S pO pE aO aE lE w) (tileAltOddPieces S pO pE aO aE lO (swapW w)) (altCf w false).1 (altCf w false).2 := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := vecs_swapW w
  have hV := parentsAt_valid w
  have hp : ((parentsAt w).odd.num + (parentsAt w).odd.den) % 2 = 1 := hV.odd_parity
  have hq : ((parentsAt w).even.num + (parentsAt w).even.den) % 2 = 0 := hV.even_parity
  intro i pR hi
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hi
  have hlt' : i < 7 := by alt_lists_hlt; omega
  rcases i with _ | _ | _ | _ | _ | _ | _ | _
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[1]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[0]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[3]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[2]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[5]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[4]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[6]'(by alt_lists; simp), List.getElem_mem _, (altParP w).1, (altParP w).2, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · omega

theorem tileAltEven_rawRot_odd_two (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (lE lO : Word → Bool → Bool → PartialOdometer)
    (w : Word) (hWo : W1Odd w = true) (hl : w.getLast? = some Digit.two)
    (hP : RawRot (regOdo S pO pE (regsAt w).1 true) (regOdo S pO pE (regsAt (swapW w)).2 false) (vP1 w - ((0 : ℤ), (1 : ℤ))) 0)
    (hQ : RawRot (regOdo S pO pE (regsAt w).2 false) (regOdo S pO pE (regsAt (swapW w)).1 true) (vQ1 w - ((0 : ℤ), (1 : ℤ))) 0)
    (hA : RawRot (regOdo S aO aE (regsAt w).1 true) (regOdo S aO aE (regsAt (swapW w)).2 false) (altParP w).1 (altParP w).2) :
    PairingOK (tileAltEvenPieces S pO pE aO aE lE w) (tileAltOddPieces S pO pE aO aE lO (swapW w)) (altCf w false).1 (altCf w false).2 := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := vecs_swapW w
  have hV := parentsAt_valid w
  have hp : ((parentsAt w).odd.num + (parentsAt w).odd.den) % 2 = 1 := hV.odd_parity
  have hq : ((parentsAt w).even.num + (parentsAt w).even.den) % 2 = 0 := hV.even_parity
  intro i pR hi
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hi
  have hlt' : i < 7 := by alt_lists_hlt; omega
  rcases i with _ | _ | _ | _ | _ | _ | _ | _
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[1]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[0]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[3]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[2]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[5]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[4]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[6]'(by alt_lists; simp), List.getElem_mem _, (altParP w).1, (altParP w).2, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · omega

theorem tileAltEven_rawRot_odd_three (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (lE lO : Word → Bool → Bool → PartialOdometer)
    (w : Word) (hWo : W1Odd w = true) (hl : w.getLast? = some Digit.three)
    (hP : RawRot (regOdo S pO pE (regsAt w).1 true) (regOdo S pO pE (regsAt (swapW w)).2 false) (vP1 w - ((0 : ℤ), (1 : ℤ))) 0)
    (hQ : RawRot (regOdo S pO pE (regsAt w).2 false) (regOdo S pO pE (regsAt (swapW w)).1 true) (vQ1 w - ((0 : ℤ), (1 : ℤ))) 0)
    (hL : w.getLast? = some Digit.three → ∀ plus : Bool,
      RawRot (lE w.dropLast plus true) (lO (swapW w.dropLast) (plus != W1Odd w) true) (vQ1 w - ((0 : ℤ), (1 : ℤ))) 0) :
    PairingOK (tileAltEvenPieces S pO pE aO aE lE w) (tileAltOddPieces S pO pE aO aE lO (swapW w)) (altCf w false).1 (altCf w false).2 := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := vecs_swapW w
  have hV := parentsAt_valid w
  have hp : ((parentsAt w).odd.num + (parentsAt w).odd.den) % 2 = 1 := hV.odd_parity
  have hq : ((parentsAt w).even.num + (parentsAt w).even.den) % 2 = 0 := hV.even_parity
  intro i pR hi
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hi
  have hlt' : i < 6 := by alt_lists_hlt; omega
  rcases i with _ | _ | _ | _ | _ | _ | _
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[1]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[0]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[3]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[2]'(by alt_lists; simp), List.getElem_mem _, vQ1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[5]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · refine ⟨(tileAltEvenPieces S pO pE aO aE lE w)[4]'(by alt_lists; simp), List.getElem_mem _, vP1 w - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, ?_⟩
    · rot_par_alt
    · rot_id_alt
    · rot_id_alt
    · rot_id_alt
    · rot_exc_alt
  · omega

/-- (c) of `lemma:tile-odometer-existence` for the even alternate child, raw form: the six copies pair by an
involution and the alternate parent piece with the alternate parent piece, under `z(x) = i x + c_f` with `γ` (`altCf`). -/
theorem tileAltEven_rawRot (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (lE lO : Word → Bool → Bool → PartialOdometer)
    (w : Word) (o oR : PartialOdometer)
    (ho : RespectsPieces o (tileAltEvenPieces S pO pE aO aE lE w))
    (hoR : RespectsPieces oR (tileAltOddPieces S pO pE aO aE lO (swapW w)))
    (hcov : PiecesCovered (tileAltOddPieces S pO pE aO aE lO (swapW w)))
    (hconn : (overlapGraph (goodPart (tileAltOddPieces S pO pE aO aE lO (swapW w)))).Connected)
    (hP : RawRot (regOdo S pO pE (regsAt w).1 true) (regOdo S pO pE (regsAt (swapW w)).2 false) (vP1 w - ((0 : ℤ), (1 : ℤ))) 0)
    (hQ : RawRot (regOdo S pO pE (regsAt w).2 false) (regOdo S pO pE (regsAt (swapW w)).1 true) (vQ1 w - ((0 : ℤ), (1 : ℤ))) 0)
    (hA : (w.getLast? = some Digit.one ∨ w.getLast? = some Digit.two) → RawRot (regOdo S aO aE (regsAt w).1 true) (regOdo S aO aE (regsAt (swapW w)).2 false) (altParP w).1 (altParP w).2)
    (hL : w.getLast? = some Digit.three → ∀ plus : Bool,
      RawRot (lE w.dropLast plus true) (lO (swapW w.dropLast) (plus != W1Odd w) true) (vQ1 w - ((0 : ℤ), (1 : ℤ))) 0) :
    RawRot o oR (altCf w false).1 (altCf w false).2 := by
  refine rawRot_of_pairing o oR _ _ _ _ ho hoR hcov hconn ?_
  cases hWo : W1Odd w <;> rcases hl : w.getLast? with _ | d
  · exact tileAltEven_rawRot_even_none S pO pE aO aE lE lO w hWo hl hP hQ
  · cases d
    · exact tileAltEven_rawRot_even_one S pO pE aO aE lE lO w hWo hl hP hQ (hA (Or.inl hl))
    · exact tileAltEven_rawRot_even_two S pO pE aO aE lE lO w hWo hl hP hQ (hA (Or.inr hl))
    · exact tileAltEven_rawRot_even_three S pO pE aO aE lE lO w hWo hl hP hQ hL
  · exact tileAltEven_rawRot_odd_none S pO pE aO aE lE lO w hWo hl hP hQ
  · cases d
    · exact tileAltEven_rawRot_odd_one S pO pE aO aE lE lO w hWo hl hP hQ (hA (Or.inl hl))
    · exact tileAltEven_rawRot_odd_two S pO pE aO aE lE lO w hWo hl hP hQ (hA (Or.inr hl))
    · exact tileAltEven_rawRot_odd_three S pO pE aO aE lE lO w hWo hl hP hQ hL

/-! ### Slopes: every tile odometer is normalised with `α = 0`

The first piece of each decomposition that contains the first tile `A = T_{1/1}` at the origin is a parent placed at offset `0` with
affine factor `0`, so the normalisation of the child has the slope of that parent. From the base words, all slopes are `0`. -/

/-- The normalisation of `o` on the first tile has slope `0`. -/
def SlopeZero (o : PartialOdometer) : Prop := ∃ β : ℤ, FirstTileNormal o 0 β

theorem slopeZero_of_piece (o : PartialOdometer) (ps : List Piece) (ho : RespectsPieces o ps) (p : Piece) (hp : p ∈ ps)
    (hoff : p.off = 0) (haff : p.aff = 0) (hexc : p.exc = ∅) (hs : SlopeZero p.odo) : SlopeZero o := by
  obtain ⟨β, hβ⟩ := hs
  obtain ⟨b, hb⟩ := ho.2 p hp
  refine ⟨β + b, fun x hx => ?_⟩
  obtain ⟨hxd, hxv⟩ := hβ x hx
  have hxp : x ∈ p.placed := by rw [mem_placed, hoff, sub_zero]; exact hxd
  have hv := hb x hxp (by rw [hexc]; exact Set.notMem_empty x)
  rw [hoff, sub_zero, haff] at hv
  refine ⟨by rw [ho.1]; exact mem_pieceUnion.mpr ⟨p, hp, hxp⟩, ?_⟩
  simp only [normed, dotS, Prod.fst_zero, Prod.snd_zero, zero_mul, add_zero] at hxv hv ⊢
  linarith

set_option hygiene false in
/-- The first piece of a decomposition: offset `0`, affine factor `0`, no exceptional point. -/
macro "first_piece" : tactic => `(tactic| (
  simp only [tileOddPieces, tileEvenPieces, tileAltOddPieces, tileAltEvenPieces, List.getElem_cons_succ,
    List.getElem_cons_zero, List.getElem_append_left, stdPiece, p0Off, q0Off, p0Aff, q0Aff, offsetP0, offsetQ0, altOff, altAff,
    coeffOff, coeffAffine, altP0Coeff, altQ0Coeff, pairAffine, offsetA, hW, ↓reduceIte, Bool.false_eq_true, Bool.and_false,
    Bool.false_and, Bool.not_false, Bool.not_true, Bool.and_true, Bool.true_and, decide_true, decide_false]
  all_goals first
  | rfl
  | (ext <;> simp)
  | simp
  | skip))

theorem slope_tileOdd (S : WeakData) (pO pE : Word → PartialOdometer) (lE : Word → Bool → Bool → PartialOdometer) (w : Word)
    (o : PartialOdometer) (ho : RespectsPieces o (tileOddPieces S pO pE lE w))
    (hP : SlopeZero (regOdo S pO pE (regsAt w).1 true)) (hQ : SlopeZero (regOdo S pO pE (regsAt w).2 false)) :
    SlopeZero o := by
  cases hW : W1Odd w
  · refine slopeZero_of_piece o _ ho ((tileOddPieces S pO pE lE w)[2]'(by simp [tileOddPieces])) (List.getElem_mem _)
      ?_ ?_ ?_ ?_ <;> first_piece
    exact hQ
  · refine slopeZero_of_piece o _ ho ((tileOddPieces S pO pE lE w)[0]'(by simp [tileOddPieces])) (List.getElem_mem _)
      ?_ ?_ ?_ ?_ <;> first_piece
    exact hP

theorem slope_tileEven (S : WeakData) (pO pE : Word → PartialOdometer) (lO : Word → Bool → Bool → PartialOdometer) (w : Word)
    (o : PartialOdometer) (ho : RespectsPieces o (tileEvenPieces S pO pE lO w))
    (hP : SlopeZero (regOdo S pO pE (regsAt w).1 true)) (hQ : SlopeZero (regOdo S pO pE (regsAt w).2 false)) :
    SlopeZero o := by
  cases hW : W1Odd w
  · refine slopeZero_of_piece o _ ho ((tileEvenPieces S pO pE lO w)[4]'(by simp [tileEvenPieces])) (List.getElem_mem _)
      ?_ ?_ ?_ ?_ <;> first_piece
    exact hQ
  · refine slopeZero_of_piece o _ ho ((tileEvenPieces S pO pE lO w)[0]'(by simp [tileEvenPieces])) (List.getElem_mem _)
      ?_ ?_ ?_ ?_ <;> first_piece
    exact hP

theorem slope_tileAltOdd (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (lO : Word → Bool → Bool → PartialOdometer)
    (w : Word) (o : PartialOdometer) (ho : RespectsPieces o (tileAltOddPieces S pO pE aO aE lO w))
    (hP : SlopeZero (regOdo S pO pE (regsAt w).1 true)) (hQ : SlopeZero (regOdo S pO pE (regsAt w).2 false)) :
    SlopeZero o := by
  cases hW : W1Odd w
  · refine slopeZero_of_piece o _ ho ((tileAltOddPieces S pO pE aO aE lO w)[4]'(by simp [tileAltOddPieces]))
      (List.getElem_mem _) ?_ ?_ ?_ ?_ <;> first_piece
    exact hQ
  · refine slopeZero_of_piece o _ ho ((tileAltOddPieces S pO pE aO aE lO w)[0]'(by simp [tileAltOddPieces]))
      (List.getElem_mem _) ?_ ?_ ?_ ?_ <;> first_piece
    exact hP

theorem slope_tileAltEven (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (lE : Word → Bool → Bool → PartialOdometer)
    (w : Word) (o : PartialOdometer) (ho : RespectsPieces o (tileAltEvenPieces S pO pE aO aE lE w))
    (hP : SlopeZero (regOdo S pO pE (regsAt w).1 true)) (hQ : SlopeZero (regOdo S pO pE (regsAt w).2 false))
    (hL : W1Odd w = false → w.getLast? = some Digit.three → SlopeZero (lE w.dropLast true true)) :
    SlopeZero o := by
  cases hW : W1Odd w
  · refine slopeZero_of_piece o _ ho ((tileAltEvenPieces S pO pE aO aE lE w)[0]'(by simp [tileAltEvenPieces]))
      (List.getElem_mem _) ?_ ?_ ?_ ?_ <;> first_piece
    by_cases hc : w.getLast? = some Digit.three
    · simp only [hc, ↓reduceIte]
      exact hL hW hc
    · simp only [hc, ↓reduceIte]
      exact hQ
  · refine slopeZero_of_piece o _ ho ((tileAltEvenPieces S pO pE aO aE lE w)[4]'(by simp [tileAltEvenPieces]))
      (List.getElem_mem _) ?_ ?_ ?_ ?_ <;> first_piece
    exact hP

/-! ### The trailing letters -/

theorem trailingCount_snoc (d e : Digit) (u : Word) :
    trailingCount d (u ++ [e]) = if e = d then trailingCount d u + 1 else 0 := by
  unfold trailingCount
  rw [List.reverse_append, List.reverse_singleton, List.singleton_append, List.takeWhile_cons]
  by_cases h : e = d <;> simp [h]

theorem stripTrailing_snoc (d e : Digit) (u : Word) :
    stripTrailing d (u ++ [e]) = if e = d then stripTrailing d u else u ++ [e] := by
  unfold stripTrailing
  rw [trailingCount_snoc]
  by_cases h : e = d
  · simp only [h, ↓reduceIte, List.length_append, List.length_singleton]
    rw [show u.length + 1 - (trailingCount d u + 1) = u.length - trailingCount d u by omega]
    exact List.take_append_of_le_length (by omega)
  · simp [h]

theorem stripTrailing_length_le (d : Digit) (u : Word) : (stripTrailing d u).length ≤ u.length := by
  unfold stripTrailing
  simp

/-- After the trailing `3`s the odd parent is that of the prefix and `v_{q,1}` has grown by `k v_{p,1}`. -/
theorem vecs_strip_three (u : Word) :
    vP1 u = vP1 (stripTrailing Digit.three u) ∧
      vQ1 u = vQ1 (stripTrailing Digit.three u) + (trailingCount Digit.three u : ℤ) • vP1 (stripTrailing Digit.three u) := by
  induction u using List.reverseRecOn with
  | nil => simp [stripTrailing, trailingCount]
  | append_singleton v e ih =>
    rw [stripTrailing_snoc, trailingCount_snoc]
    by_cases h : e = Digit.three
    · subst h
      simp only [↓reduceIte]
      obtain ⟨h1, h2⟩ := ih
      have e1 : vP1 (v ++ [Digit.three]) = vP1 v := by
        simp [vP1, parentsAt_append_singleton, Parents.step]
      have e2 : vQ1 (v ++ [Digit.three]) = vQ1 v + vP1 v := by
        simp only [vQ1, vP1, parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine, texV1Even,
          texV1Odd, Prod.mk_add_mk, Prod.mk.injEq]
        constructor <;> ring
      refine ⟨by rw [e1, h1], ?_⟩
      rw [e2, h2, ← h1]
      push_cast
      rw [add_smul, one_smul]
      abel
    · simp [h]

/-- A word with a letter other than `3` has its even L-correction defined. -/
theorem evenLDefined_of_mem (u : Word) (h : ∃ d ∈ u, d ≠ Digit.three) : EvenLDefined u := by
  induction u using List.reverseRecOn with
  | nil => obtain ⟨d, hd, -⟩ := h; simp at hd
  | append_singleton v e ih =>
    by_cases he : e = Digit.three
    · subst he
      obtain ⟨d, hd, hne⟩ := h
      simp only [List.mem_append, List.mem_singleton] at hd
      rcases hd with hd | rfl
      · obtain ⟨w1, s, k, hs, rfl⟩ := ih ⟨d, hd, hne⟩
        exact ⟨w1, s, k + 1, hs, by simp [List.replicate_succ', List.append_assoc]⟩
      · exact absurd rfl hne
    · exact ⟨v, e, 0, he, by simp⟩

/-- The elongated `+` even L-correction at `W_1` even contains the first tile in its bridge, at offset `0` with affine factor `0`:
its slope is that of the even register of the prefix. -/
theorem slope_evenL (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (u : Word) (L : PartialOdometer)
    (hL : RespectsPieces L (evenLPieces S pO pE aO aE u true true)) (hW : W1Odd u = false)
    (hB : SlopeZero (regOdo S pO pE (regsAt (stripTrailing Digit.three u)).2 false)) : SlopeZero L := by
  obtain ⟨-, hq⟩ := vecs_strip_three u
  refine slopeZero_of_piece L _ hL (stdPiece (regOdo S pO pE (regsAt (stripTrailing Digit.three u)).2 false)
    (evenLInitOff u true + altOff (stripTrailing Digit.three u)
      ((trailingCount Digit.three u : ℤ) • (evenKCoeff (W1Odd u) true
        (decide ((stripTrailing Digit.three u).getLast? = some Digit.two))).1 +
        (evenKCoeff (W1Odd u) true (decide ((stripTrailing Digit.three u).getLast? = some Digit.two))).2.1))
    (evenLInitAff u true + altAff (stripTrailing Digit.three u)
      ((trailingCount Digit.three u : ℤ) • (evenKCoeff (W1Odd u) true
        (decide ((stripTrailing Digit.three u).getLast? = some Digit.two))).1 +
        (evenKCoeff (W1Odd u) true (decide ((stripTrailing Digit.three u).getLast? = some Digit.two))).2.1))) ?_ ?_ ?_ rfl hB
  · simp only [evenLPieces, hW, Bool.not_false, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
      List.mem_append, List.mem_singleton]
    simp
  · simp only [stdPiece, evenLInitOff, q0Off, offsetQ0, hW, ↓reduceIte, Bool.false_eq_true, evenKCoeff, altOff, coeffOff]
    rw [hq]
    ext <;> simp
  · simp only [stdPiece, evenLInitAff, q0Aff, hW, ↓reduceIte, Bool.false_eq_true, evenKCoeff, altAff, coeffAffine, pairAffine,
      offsetA]
    ext <;> simp

/-! ### The slopes of the family -/

/-- The base odometers have slope `0` (for the paper data: `BaseTileProps.base_slopes`), and so has the initial odometer
`o_{1/1}` (it is the bridge of the even L-correction when the prefix is `2^j`). -/
def BaseSlopes (D : JointData) : Prop :=
  (∀ w : Word, IsBase w → ∀ O E aO aE : PartialOdometer, D.S.base w O E → D.altBase w aO aE →
    SlopeZero O ∧ SlopeZero E ∧ SlopeZero aO ∧ SlopeZero aE) ∧ SlopeZero D.S.oneO

theorem below_of_lt (f : Word → JSlice) (w u : Word) (h : u.length < w.length) : below f w u = f u := by
  simp [below, h]

theorem word_induction (P : Word → Prop) (h : ∀ u, (∀ v : Word, v.length < u.length → P v) → P u) : ∀ u, P u :=
  fun u => (measure List.length).wf.induction u (fun u ih => h u (fun v hv => ih v hv))

/-- Every tile and alternate tile odometer of the family, up to length `n`, is normalised with slope `0`. -/
theorem family_slopes (D : JointData) (f : Word → JSlice) (n : ℕ)
    (hJ : ∀ u : Word, u.length ≤ n → IsJointSlice D f u) (hB : BaseSlopes D) :
    ∀ u : Word, u.length ≤ n →
      SlopeZero (f u).tOdd ∧ SlopeZero (f u).tEven ∧ SlopeZero (f u).aOdd ∧ SlopeZero (f u).aEven := by
  refine word_induction _ (fun u ih hu => ?_)
  obtain ⟨hWk, hWA, hT, hLp⟩ := hJ u hu
  by_cases hb : IsBase u
  · obtain ⟨e1, e2, e3, e4⟩ := hT.1 hb
    rw [e1, e2, e3, e4]
    exact hB.1 u hb _ _ _ _ (hWk.2.2.1 hb) (hWA.2.2.1 hb)
  obtain ⟨hto, hte, hao, hae⟩ := hT.2.1 hb
  obtain ⟨⟨u1, h1⟩, ⟨u2, h2⟩⟩ := regs_some u hb
  have l1 := FLatticePaper.Tiles.JointInduction.regsAt_lt u u1 (Or.inl h1)
  have l2 := FLatticePaper.Tiles.JointInduction.regsAt_lt u u2 (Or.inr h2)
  have s1 := ih u1 l1 (by omega)
  have s2 := ih u2 l2 (by omega)
  have hP : SlopeZero (regOdo D.S (fun v => (below f u v).tOdd) (fun v => (below f u v).tEven) (regsAt u).1 true) := by
    rw [h1]
    show SlopeZero (below f u u1).tOdd
    rw [below_of_lt f u u1 l1]
    exact s1.1
  have hQ : SlopeZero (regOdo D.S (fun v => (below f u v).tOdd) (fun v => (below f u v).tEven) (regsAt u).2 false) := by
    rw [h2]
    show SlopeZero (below f u u2).tEven
    rw [below_of_lt f u u2 l2]
    exact s2.2.1
  refine ⟨slope_tileOdd _ _ _ _ u _ hto hP hQ, slope_tileEven _ _ _ _ u _ hte hP hQ,
    slope_tileAltOdd _ _ _ _ _ _ u _ hao hP hQ, slope_tileAltEven _ _ _ _ _ _ u _ hae hP hQ (fun hW hl => ?_)⟩
  have hu' : u = u.dropLast ++ [Digit.three] := (List.dropLast_append_getLast? _ hl).symm
  have hlen : u.dropLast.length < u.length := by
    rw [List.length_dropLast]
    have : u ≠ [] := fun h => by simp [h] at hl
    have := List.length_pos_of_ne_nil this
    omega
  rw [below_of_lt f u _ hlen]
  have hdef : EvenLDefined u.dropLast := by
    refine evenLDefined_of_mem _ ?_
    by_contra hc
    refine hb (Or.inr (Or.inl fun d hd => ?_))
    rw [hu'] at hd
    simp only [List.mem_append, List.mem_singleton] at hd
    rcases hd with hd | rfl
    · by_contra hne
      exact hc ⟨d, hd, hne⟩
    · rfl
  have hRL := ((hJ u.dropLast (by omega)).2.2.2.2 true true hdef).1
  have hW' : W1Odd u.dropLast = false := by
    have hph := phase_snoc_three u.dropLast
    rw [← hu'] at hph
    unfold W1Odd at hW ⊢
    rw [← hph]
    exact hW
  refine slope_evenL _ _ _ _ _ u.dropLast _ hRL hW' ?_
  cases h : (regsAt (stripTrailing Digit.three u.dropLast)).2 with
  | none => exact hB.2
  | some v =>
    have lv := FLatticePaper.Tiles.JointInduction.regsAt_lt _ v (Or.inr h)
    have lp := stripTrailing_length_le Digit.three u.dropLast
    show SlopeZero (below f u.dropLast v).tEven
    rw [below_of_lt f u.dropLast v (by omega)]
    exact (ih v (by omega) (by omega)).2.1

/-! ### The rotation step at one level -/

open FLatticePaper.Tiles.JointInduction (GoodBelow RotStepInput)

theorem swapW_swapW' (w : Word) : swapW (swapW w) = w := FLatticePaper.Farey.swapMap_swapMap w

theorem length_swapW (w : Word) : (swapW w).length = w.length := by simp [swapW]

theorem isBase_swapW {w : Word} (hw : IsBase w) : IsBase (swapW w) := by
  by_contra h
  exact FLatticePaper.Tiles.Standard.nonbase_swap h (by rwa [swapW_swapW'])

theorem below_swapW (f : Word → JSlice) (w : Word) : below f (swapW w) = below f w := by
  funext u
  simp [below, length_swapW]

theorem zero_sub_rotR_zero : (0 : Site) - rotR 0 = 0 := by
  ext <;> simp [rotR]

theorem rawRot_of_tileRotation_slopes (o oR : PartialOdometer) (v1 : Site) (h : TileRotation o oR v1)
    (hs : SlopeZero o) (hsR : SlopeZero oR) : RawRot o oR (v1 - ((0 : ℤ), (1 : ℤ))) 0 := by
  obtain ⟨α, β, α', β', hN, hNR, hv⟩ := h
  obtain ⟨b, hb⟩ := hs
  obtain ⟨b', hb'⟩ := hsR
  obtain ⟨rfl, -⟩ := firstTileNormal_unique o α 0 β b hN hb
  obtain ⟨rfl, -⟩ := firstTileNormal_unique oR α' 0 β' b' hNR hb'
  have := rawRot_of_tileRotation o oR v1 0 0 β β' hv
  rwa [zero_sub_rotR_zero] at this

theorem rawRot_of_altRotation_slopes (o oR : PartialOdometer) (cf γ : Site) (h : AltRotation o oR cf γ)
    (hs : SlopeZero o) (hsR : SlopeZero oR) : RawRot o oR cf γ := by
  obtain ⟨α, β, α', β', c0, hN, hNR, hv⟩ := h
  obtain ⟨b, hb⟩ := hs
  obtain ⟨b', hb'⟩ := hsR
  obtain ⟨rfl, -⟩ := firstTileNormal_unique o α 0 β b hN hb
  obtain ⟨rfl, -⟩ := firstTileNormal_unique oR α' 0 β' b' hNR hb'
  have := rawRot_of_altRotation o oR cf γ 0 0 β β' c0 hv
  rwa [add_sub_assoc, zero_sub_rotR_zero, add_zero] at this

theorem rawRot_of_lRotation (o oR : PartialOdometer) (v1 : Site) (h : LRotation o oR v1) :
    RawRot o oR (v1 - ((0 : ℤ), (1 : ℤ))) 0 := by
  obtain ⟨c0, hc⟩ := h
  refine ⟨c0, fun y hy => ?_⟩
  obtain ⟨hm, hv⟩ := hc y hy
  rw [← add_sub_assoc]
  refine ⟨hm, ?_⟩
  rw [hv]
  simp [dotS]

/-- The base rotations: (c) at the base words (for the paper data, `base_rotProps`). -/
def BaseRot (D : JointData) : Prop :=
  ∀ w : Word, IsBase w → ∀ x r : JSlice, D.S.base w x.tOdd x.tEven → D.altBase w x.aOdd x.aEven →
    D.S.base (swapW w) r.tOdd r.tEven → D.altBase (swapW w) r.aOdd r.aEven → RotProps w x r

/-- The overlap graphs of the four decompositions of the children of `w` are connected. -/
def Connected4 (D : JointData) (g : Word → JSlice) (w : Word) : Prop :=
  (overlapGraph (goodPart (tileOddPieces D.S (fun u => (g u).tOdd) (fun u => (g u).tEven) (fun u => (g u).lEven) w))).Connected ∧
  (overlapGraph (goodPart (tileEvenPieces D.S (fun u => (g u).tOdd) (fun u => (g u).tEven) (fun u => (g u).lOdd) w))).Connected ∧
  (overlapGraph (goodPart (tileAltOddPieces D.S (fun u => (g u).tOdd) (fun u => (g u).tEven) (fun u => (g u).aOdd)
    (fun u => (g u).aEven) (fun u => (g u).lOdd) w))).Connected ∧
  (overlapGraph (goodPart (tileAltEvenPieces D.S (fun u => (g u).tOdd) (fun u => (g u).tEven) (fun u => (g u).aOdd)
    (fun u => (g u).aEven) (fun u => (g u).lEven) w))).Connected

theorem tileAltOddPieces_covered' (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (lO : Word → Bool → Bool → PartialOdometer)
    (w : Word) : PiecesCovered (tileAltOddPieces S pO pE aO aE lO w) := by
  refine covered_of_no_exc _ (fun p hp => ?_)
  simp only [tileAltOddPieces] at hp
  rw [List.mem_append] at hp
  rcases hp with hp | hp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · split at hp
    · simp at hp
    · simp only [List.mem_singleton] at hp
      subst hp
      rfl

theorem tileAltEvenPieces_covered' (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (lE : Word → Bool → Bool → PartialOdometer)
    (w : Word) : PiecesCovered (tileAltEvenPieces S pO pE aO aE lE w) := by
  refine covered_of_no_exc _ (fun p hp => ?_)
  simp only [tileAltEvenPieces] at hp
  rw [List.mem_append] at hp
  rcases hp with hp | hp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · split at hp
    · simp at hp
    · simp only [List.mem_singleton] at hp
      subst hp
      rfl

/-- The word without its last letter `d`. -/
theorem eq_dropLast_append {w : Word} {d : Digit} (hl : w.getLast? = some d) : w = w.dropLast ++ [d] :=
  (List.dropLast_append_getLast? _ hl).symm

theorem dropLast_length_lt {w : Word} {d : Digit} (hl : w.getLast? = some d) : w.dropLast.length < w.length := by
  rw [List.length_dropLast]
  have : w ≠ [] := fun h => by simp [h] at hl
  have := List.length_pos_of_ne_nil this
  omega

/-- A word with a letter other than `2` has its odd L-correction defined. -/
theorem oddLDefined_of_mem (u : Word) (h : ∃ d ∈ u, d ≠ Digit.two) : OddLDefined u := by
  induction u using List.reverseRecOn with
  | nil => obtain ⟨d, hd, -⟩ := h; simp at hd
  | append_singleton v e ih =>
    by_cases he : e = Digit.two
    · subst he
      obtain ⟨d, hd, hne⟩ := h
      simp only [List.mem_append, List.mem_singleton] at hd
      rcases hd with hd | rfl
      · obtain ⟨w1, s, k, hs, rfl⟩ := ih ⟨d, hd, hne⟩
        exact ⟨w1, s, k + 1, hs, by simp [List.replicate_succ', List.append_assoc]⟩
      · exact absurd rfl hne
    · exact ⟨v, e, 0, he, by simp⟩

theorem evenLDefined_dropLast {w : Word} (hb : ¬ IsBase w) (hl : w.getLast? = some Digit.three) :
    EvenLDefined w.dropLast := by
  refine evenLDefined_of_mem _ ?_
  by_contra hc
  refine hb (Or.inr (Or.inl fun d hd => ?_))
  rw [eq_dropLast_append hl] at hd
  simp only [List.mem_append, List.mem_singleton] at hd
  rcases hd with hd | rfl
  · by_contra hne
    exact hc ⟨d, hd, hne⟩
  · rfl

theorem oddLDefined_dropLast {w : Word} (hb : ¬ IsBase w) (hl : w.getLast? = some Digit.two) :
    OddLDefined w.dropLast := by
  refine oddLDefined_of_mem _ ?_
  by_contra hc
  refine hb (Or.inr (Or.inr fun d hd => ?_))
  rw [eq_dropLast_append hl] at hd
  simp only [List.mem_append, List.mem_singleton] at hd
  rcases hd with hd | rfl
  · by_contra hne
    exact hc ⟨d, hd, hne⟩
  · rfl

/-- The L-rotation of the even parent, after a `3`. -/
theorem lrot_three (f : Word → JSlice) (w : Word) (hb : ¬ IsBase w) (hl : w.getLast? = some Digit.three)
    (hJP : LRotProps w.dropLast (f w.dropLast) (f (swapW w.dropLast))) (elong : Bool) (plus : Bool) :
    RawRot ((f w.dropLast).lEven plus elong) ((f (swapW w.dropLast)).lOdd (plus != W1Odd w) elong) (vQ1 w - ((0 : ℤ), (1 : ℤ))) 0 := by
  have h := hJP.1 (evenLDefined_dropLast hb hl) plus elong
  have hw := eq_dropLast_append hl
  have hph : W1Odd w.dropLast = W1Odd w := by
    unfold W1Odd
    conv_rhs => rw [hw]
    rw [phase_snoc_three]
  have hq : texV1Even ((parentsAt w.dropLast).current .even) = vQ1 w := by
    unfold vQ1
    conv_rhs => rw [hw]
    rw [parentsAt_append_singleton]
    rfl
  rw [hph, hq] at h
  exact rawRot_of_lRotation _ _ _ h

/-- The L-rotation of the odd parent, after a `2`. -/
theorem lrot_two (f : Word → JSlice) (w : Word) (hb : ¬ IsBase w) (hl : w.getLast? = some Digit.two)
    (hJP : LRotProps w.dropLast (f w.dropLast) (f (swapW w.dropLast))) (elong : Bool) (plus : Bool) :
    RawRot ((f w.dropLast).lOdd plus elong) ((f (swapW w.dropLast)).lEven (plus == W1Odd w) elong) (vP1 w - ((0 : ℤ), (1 : ℤ))) 0 := by
  have h := hJP.2 (oddLDefined_dropLast hb hl) plus elong
  have hw := eq_dropLast_append hl
  have hph : W1Odd w.dropLast = W1Odd w := by
    unfold W1Odd
    conv_rhs => rw [hw]
    rw [phase_snoc_two]
  have hq : texV1Odd ((parentsAt w.dropLast).current .odd) = vP1 w := by
    unfold vP1
    conv_rhs => rw [hw]
    rw [parentsAt_append_singleton]
    rfl
  rw [hph, hq] at h
  exact rawRot_of_lRotation _ _ _ h

/-- For the paper data (`WeakStepPaper.paperS`, `PaperAltBaseCond`) the base slopes are those of `BaseTileProps.base_slopes`. -/
theorem baseSlopes_paper (D : JointData) (hS : D.S = WeakStepPaper.paperS)
    (hA : D.altBase = SurgicalAlt.PaperAltBaseCond) : BaseSlopes D := by
  refine ⟨fun w hw O E aO aE hO haO => ?_, ⟨0, fun x hx => ?_⟩⟩
  · rw [hS] at hO
    rw [hA] at haO
    exact BaseTileProps.base_slopes w hw O E aO aE hO haO
  · rw [hS]
    simp only [tileShape, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, by simp [normed, dotS, zTileOdo, WeakStepPaper.paperS]⟩

/-- (c) of `lemma:tile-odometer-existence` at the level `n`: from the family below `n` (with the rotations of the parents and of
their L-corrections), the slices at level `n`, the slopes of the base odometers, the base rotations and the connectivity of the
overlap graphs of the decompositions, the rotation identities of the tile and alternate tile odometers hold at every word of length
`n`. The standard ones are normalised with the corner value `N(v_1 - i) = 0` (`TileTranslationStd.stdCorners_odd`, `_even`). -/
theorem rotProps_step (D : JointData) (f : Word → JSlice) (n : ℕ) (hgood : GoodBelow D f n)
    (hlev : ∀ w : Word, w.length = n → IsJointSlice D f w)
    (hB : BaseSlopes D) (hBR : BaseRot D)
    (hconn : ∀ w : Word, w.length = n → ¬ IsBase w → Connected4 D (below f w) w)
    (w : Word) (hw : w.length = n) : RotProps w (f w) (f (swapW w)) := by
  have hJ : ∀ u : Word, u.length ≤ n → IsJointSlice D f u := fun u hu => by
    rcases lt_or_eq_of_le hu with h | h
    · exact (hgood u h).1
    · exact hlev u h
  have hsl := family_slopes D f n hJ hB
  have hsw : (swapW w).length = n := by rw [length_swapW, hw]
  obtain ⟨hWk, hWA, hT, -⟩ := hlev w hw
  obtain ⟨hWk', hWA', hT', -⟩ := hlev (swapW w) hsw
  by_cases hb : IsBase w
  · have hb' := isBase_swapW hb
    obtain ⟨e1, e2, e3, e4⟩ := hT.1 hb
    obtain ⟨e1', e2', e3', e4'⟩ := hT'.1 hb'
    refine hBR w hb _ _ ?_ ?_ ?_ ?_
    · rw [e1, e2]; exact hWk.2.2.1 hb
    · rw [e3, e4]; exact hWA.2.2.1 hb
    · rw [e1', e2']; exact hWk'.2.2.1 hb'
    · rw [e3', e4']; exact hWA'.2.2.1 hb'
  have hb' := FLatticePaper.Tiles.Standard.nonbase_swap hb
  obtain ⟨hto, hte, hao, hae⟩ := hT.2.1 hb
  obtain ⟨hto', hte', hao', hae'⟩ := hT'.2.1 hb'
  rw [below_swapW] at hto' hte' hao' hae'
  obtain ⟨hc1, hc2, hc3, hc4⟩ := hconn (swapW w) hsw hb'
  rw [below_swapW] at hc1 hc2 hc3 hc4
  obtain ⟨⟨u1, h1⟩, ⟨u2, h2⟩⟩ := regs_some w hb
  have l1 := FLatticePaper.Tiles.JointInduction.regsAt_lt w u1 (Or.inl h1)
  have l2 := FLatticePaper.Tiles.JointInduction.regsAt_lt w u2 (Or.inr h2)
  have l1' : (swapW u1).length < w.length := by rw [length_swapW]; exact l1
  have l2' : (swapW u2).length < w.length := by rw [length_swapW]; exact l2
  have hr1 : (regsAt (swapW w)).2 = some (swapW u1) := by rw [regsAt_swapW, h1]; rfl
  have hr2 : (regsAt (swapW w)).1 = some (swapW u2) := by rw [regsAt_swapW, h2]; rfl
  have J1 := (hgood u1 (by omega)).2
  have J2 := (hgood u2 (by omega)).2
  obtain ⟨pr1, pr2⟩ := parents_of_regs w
  have s1 := hsl u1 (by omega)
  have s2 := hsl u2 (by omega)
  have s1' := hsl (swapW u1) (by rw [length_swapW]; omega)
  have s2' := hsl (swapW u2) (by rw [length_swapW]; omega)
  have sw0 := hsl w (by omega)
  have sw1 := hsl (swapW w) (by omega)
  -- the register parents
  have hP : RawRot (regOdo D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven) (regsAt w).1 true)
      (regOdo D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven) (regsAt (swapW w)).2 false)
      (vP1 w - ((0 : ℤ), (1 : ℤ))) 0 := by
    rw [h1, hr1]
    show RawRot (below f w u1).tOdd (below f w (swapW u1)).tEven _ _
    rw [below_of_lt f w u1 l1, below_of_lt f w (swapW u1) l1']
    have h := J1.2.2.1.1
    rw [pr1 u1 h1] at h
    exact rawRot_of_tileRotation_slopes _ _ _ h s1.1 s1'.2.1
  have hQ : RawRot (regOdo D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven) (regsAt w).2 false)
      (regOdo D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven) (regsAt (swapW w)).1 true)
      (vQ1 w - ((0 : ℤ), (1 : ℤ))) 0 := by
    rw [h2, hr2]
    show RawRot (below f w u2).tEven (below f w (swapW u2)).tOdd _ _
    rw [below_of_lt f w u2 l2, below_of_lt f w (swapW u2) l2']
    have h := J2.2.2.1.2.1
    rw [pr2 u2 h2] at h
    exact rawRot_of_tileRotation_slopes _ _ _ h s2.2.1 s2'.1
  -- the alternate parents
  have hAq : (w.getLast? = some Digit.one ∨ w.getLast? = some Digit.three) →
      RawRot (regOdo D.S (fun u => (below f w u).aOdd) (fun u => (below f w u).aEven) (regsAt w).2 false)
        (regOdo D.S (fun u => (below f w u).aOdd) (fun u => (below f w u).aEven) (regsAt (swapW w)).1 true)
        (altParQ w).1 (altParQ w).2 := by
    intro hd
    obtain ⟨d, hl, hd⟩ : ∃ d, w.getLast? = some d ∧ (d = Digit.one ∨ d = Digit.three) := by
      rcases hd with h | h
      · exact ⟨_, h, Or.inl rfl⟩
      · exact ⟨_, h, Or.inr rfl⟩
    have hw' := eq_dropLast_append hl
    have hu2 : u2 = w.dropLast := by
      have := regsAt_append_singleton w.dropLast d
      rw [← hw'] at this
      rw [this] at h2
      rcases hd with rfl | rfl <;> simp only [regStep, Option.some.injEq] at h2 <;> exact h2.symm
    rw [h2, hr2]
    show RawRot (below f w u2).aEven (below f w (swapW u2)).aOdd _ _
    rw [below_of_lt f w u2 l2, below_of_lt f w (swapW u2) l2']
    have h := J2.2.2.1.2.2.2
    have hcf := altCf_even_reg w.dropLast d hd
    rw [← hw', ← hu2] at hcf
    rw [hcf] at h
    exact rawRot_of_altRotation_slopes _ _ _ _ h s2.2.2.2 s2'.2.2.1
  have hAp : (w.getLast? = some Digit.one ∨ w.getLast? = some Digit.two) →
      RawRot (regOdo D.S (fun u => (below f w u).aOdd) (fun u => (below f w u).aEven) (regsAt w).1 true)
        (regOdo D.S (fun u => (below f w u).aOdd) (fun u => (below f w u).aEven) (regsAt (swapW w)).2 false)
        (altParP w).1 (altParP w).2 := by
    intro hd
    obtain ⟨d, hl, hd⟩ : ∃ d, w.getLast? = some d ∧ (d = Digit.one ∨ d = Digit.two) := by
      rcases hd with h | h
      · exact ⟨_, h, Or.inl rfl⟩
      · exact ⟨_, h, Or.inr rfl⟩
    have hw' := eq_dropLast_append hl
    have hu1 : u1 = w.dropLast := by
      have := regsAt_append_singleton w.dropLast d
      rw [← hw'] at this
      rw [this] at h1
      rcases hd with rfl | rfl <;> simp only [regStep, Option.some.injEq] at h1 <;> exact h1.symm
    rw [h1, hr1]
    show RawRot (below f w u1).aOdd (below f w (swapW u1)).aEven _ _
    rw [below_of_lt f w u1 l1, below_of_lt f w (swapW u1) l1']
    have h := J1.2.2.1.2.2.1
    have hcf := altCf_odd_reg w.dropLast d hd
    rw [← hw', ← hu1] at hcf
    rw [hcf] at h
    exact rawRot_of_altRotation_slopes _ _ _ _ h s1.2.2.1 s1'.2.2.2
  -- the L-corrected parents
  have hL3 : ∀ elong : Bool, w.getLast? = some Digit.three → ∀ plus : Bool,
      RawRot ((below f w w.dropLast).lEven plus elong) ((below f w (swapW w.dropLast)).lOdd (plus != W1Odd w) elong)
        (vQ1 w - ((0 : ℤ), (1 : ℤ))) 0 := by
    intro elong hl plus
    have hlen := dropLast_length_lt hl
    rw [below_of_lt f w _ hlen, below_of_lt f w _ (by rw [length_swapW]; exact hlen)]
    exact lrot_three f w hb hl (hgood w.dropLast (by omega)).2.2.2.2.1 elong plus
  have hL2 : ∀ elong : Bool, w.getLast? = some Digit.two → ∀ plus : Bool,
      RawRot ((below f w w.dropLast).lOdd plus elong) ((below f w (swapW w.dropLast)).lEven (plus == W1Odd w) elong)
        (vP1 w - ((0 : ℤ), (1 : ℤ))) 0 := by
    intro elong hl plus
    have hlen := dropLast_length_lt hl
    rw [below_of_lt f w _ hlen, below_of_lt f w _ (by rw [length_swapW]; exact hlen)]
    exact lrot_two f w hb hl (hgood w.dropLast (by omega)).2.2.2.2.1 elong plus
  -- the four children
  have R1 := tileOdd_rawRot D.S _ _ _ _ w _ _ hto hte' hc2 hP hQ (hL3 false)
  have R2 := tileEven_rawRot D.S _ _ _ _ w _ _ hte hto' hc1 hP hQ (hL2 false)
  have R3 := tileAltOdd_rawRot D.S _ _ _ _ _ _ w _ _ hao hae' (tileAltEvenPieces_covered' _ _ _ _ _ _ _) hc4 hP hQ hAq
    (hL2 true)
  have R4 := tileAltEven_rawRot D.S _ _ _ _ _ _ w _ _ hae hao' (tileAltOddPieces_covered' _ _ _ _ _ _ _) hc3 hP hQ hAp
    (hL3 true)
  obtain ⟨⟨b1, hb1⟩, ⟨b2, hb2⟩, ⟨b3, hb3⟩, ⟨b4, hb4⟩⟩ := sw0
  obtain ⟨⟨b1', hb1'⟩, ⟨b2', hb2'⟩, ⟨b3', hb3'⟩, ⟨b4', hb4'⟩⟩ := sw1
  obtain ⟨α1, β1, hN1, hV1⟩ := TileTranslationStd.stdCorners_odd w (f w).tOdd hT.2.2.2.2.1
  obtain ⟨rfl, rfl⟩ := firstTileNormal_unique _ α1 0 β1 b1 hN1 hb1
  obtain ⟨α2, β2, hN2, hV2⟩ := TileTranslationStd.stdCorners_even w (f w).tEven hT.2.2.2.2.2.1
  obtain ⟨rfl, rfl⟩ := firstTileNormal_unique _ α2 0 β2 b2 hN2 hb2
  exact ⟨tileRotation_of_rawRot _ _ _ _ _ hb1 hb2' hV1.2.2.1.2 R1, tileRotation_of_rawRot _ _ _ _ _ hb2 hb1' hV2.2.2.1.2 R2,
    altRotation_of_rawRot _ _ _ _ _ _ hb3 hb4' R3, altRotation_of_rawRot _ _ _ _ _ _ hb4 hb3' R4⟩

/-! ### The L-corrections: words with trailing letters -/

theorem strip_append_replicate (d : Digit) (w : Word) :
    stripTrailing d w ++ List.replicate (trailingCount d w) d = w := by
  induction w using List.reverseRecOn with
  | nil => simp [stripTrailing, trailingCount]
  | append_singleton v e ih =>
    rw [stripTrailing_snoc, trailingCount_snoc]
    by_cases h : e = d
    · subst h
      simp only [↓reduceIte, List.replicate_succ', ← List.append_assoc, ih]
    · simp [h]

theorem swapW_strip_three (w : Word) :
    stripTrailing Digit.two (swapW w) = swapW (stripTrailing Digit.three w) ∧
      trailingCount Digit.two (swapW w) = trailingCount Digit.three w := by
  induction w using List.reverseRecOn with
  | nil => simp [stripTrailing, trailingCount, swapW]
  | append_singleton v e ih =>
    rw [swapW_append, show swapW [e] = [e.swapTwoThree] from rfl, stripTrailing_snoc, trailingCount_snoc,
      stripTrailing_snoc, trailingCount_snoc]
    cases e <;> simp [Digit.swapTwoThree, ih.1, ih.2, swapW_append] <;> rfl

theorem swapW_strip_two (w : Word) :
    stripTrailing Digit.three (swapW w) = swapW (stripTrailing Digit.two w) ∧
      trailingCount Digit.three (swapW w) = trailingCount Digit.two w := by
  induction w using List.reverseRecOn with
  | nil => simp [stripTrailing, trailingCount, swapW]
  | append_singleton v e ih =>
    rw [swapW_append, show swapW [e] = [e.swapTwoThree] from rfl, stripTrailing_snoc, trailingCount_snoc,
      stripTrailing_snoc, trailingCount_snoc]
    cases e <;> simp [Digit.swapTwoThree, ih.1, ih.2, swapW_append] <;> rfl

theorem parents_append_threes (v : Word) (k : ℕ) :
    parentsAt (v ++ List.replicate k Digit.three) =
      ⟨(parentsAt v).odd, ⟨(parentsAt v).even.num + 2 * k * (parentsAt v).odd.num,
        (parentsAt v).even.den + 2 * k * (parentsAt v).odd.den⟩⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ', ← List.append_assoc, parentsAt_append_singleton, ih]
    simp only [Parents.step, Parents.current, Parents.combine, Parents.mk.injEq, Fraction.mk.injEq, true_and]
    push_cast
    constructor <;> ring

theorem parents_append_twos (v : Word) (k : ℕ) :
    parentsAt (v ++ List.replicate k Digit.two) =
      ⟨⟨(parentsAt v).odd.num + k * (parentsAt v).even.num, (parentsAt v).odd.den + k * (parentsAt v).even.den⟩,
        (parentsAt v).even⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ', ← List.append_assoc, parentsAt_append_singleton, ih]
    simp only [Parents.step, Parents.current, Parents.combine, Parents.mk.injEq, Fraction.mk.injEq, and_true]
    push_cast
    constructor <;> ring

theorem phase_append_replicate (v : Word) (k : ℕ) (d : Digit) (hd : d ≠ Digit.one) :
    phase (v ++ List.replicate k d) = phase v := by
  unfold phase
  rw [List.count_append, List.count_replicate]
  simp [hd]

theorem W1Odd_append_replicate (v : Word) (k : ℕ) (d : Digit) (hd : d ≠ Digit.one) :
    W1Odd (v ++ List.replicate k d) = W1Odd v := by
  unfold W1Odd
  rw [phase_append_replicate v k d hd]

/-- The condition of one pair of pieces in `rawRot_of_pairing`, with the affine rule doubled (no division). -/
def PairCond (c γ : Site) (pR p : Piece) : Prop :=
  ∃ cr γr : Site, RawRot p.odo pR.odo cr γr ∧ mulI pR.off = p.off + cr - c ∧
    2 * (pR.aff - rotR p.aff - γ + γr).1 = pR.off.1 + pR.off.2 ∧
    2 * (pR.aff - rotR p.aff - γ + γr).2 = pR.off.1 - pR.off.2 ∧
    (∀ x ∈ pR.placed, x ∉ pR.exc → mulI x + c ∉ p.exc)

theorem pairingOK_of_forall₂ (ps psR : List Piece) (c γ : Site) (h : List.Forall₂ (PairCond c γ) psR ps) :
    PairingOK ps psR c γ := by
  intro i pR hi
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hi
  have hlen := h.length_eq
  have hlt' : i < ps.length := hlen ▸ hlt
  obtain ⟨cr, γr, hpar, hoff, h1, h2, hexc⟩ := h.get hlt hlt'
  refine ⟨ps[i], List.getElem_mem hlt', cr, γr, hpar, hoff, ?_, ?_, hexc⟩
  · show ((psR[i]).off.1 + (psR[i]).off.2) % 2 = 0
    simp only [List.get_eq_getElem] at h1
    omega
  · simp only [List.get_eq_getElem] at h1 h2 ⊢
    refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, hHalf] at h1 h2 ⊢ <;> omega

/-! ### The L-rotation, generic prefixes -/

set_option hygiene false in
/-- The tables of the L-corrections, unfolded to the parents of the prefix. -/
macro "l_unfold" : tactic => `(tactic| (
  simp only [stdPiece, evenLInitOff, evenLInitAff, oddLInitOff, oddLInitAff, q0Off, q0Aff, p0Off, p0Aff, offsetQ0, offsetP0,
    altOff, altAff, coeffOff, coeffAffine, evenKCoeff, oddKCoeff, LCorrections.oddBridgeShift, altParP, altParQ, aP2, aQ2,
    hWo, hWs, hWw, hl, ↓reduceIte, Bool.false_eq_true, Bool.and_false, Bool.false_and, Bool.not_true, Bool.not_false,
    reduceCtorEq, Option.some.injEq, decide_true, decide_false, bne_self_eq_false, Bool.bne_true, Bool.bne_false,
    Bool.true_bne, Bool.false_bne, Bool.true_beq, Bool.false_beq, beq_true, beq_false, getLast_swapW,
    Option.map_some, Digit.swapTwoThree]
  simp only [vP1, vP2, vQ1, vQ2, hpw, hpsw, e5, e6, texV1Odd, texV1Even, texV2, pairAffine, offsetA, Parents.current,
    Parents.combine, mulI, rotR, Prod.smul_mk, smul_eq_mul, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
    Prod.mk_add_mk, Prod.mk_sub_mk, Prod.fst_zero, Prod.snd_zero, Prod.mk.injEq, hA, hB']))

set_option hygiene false in
macro "l_ring" : tactic => `(tactic| (
  all_goals first
  | (refine ⟨?_, ?_⟩ <;> (try push_cast) <;> ring)
  | (refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero,
      Prod.snd_zero] <;> (try push_cast) <;>
      ring)
  | ((try push_cast) <;> ring)))

theorem all_swapW_three (v : Word) :
    (swapW v).all (fun d => decide (d = Digit.three)) = v.all (fun d => decide (d = Digit.two)) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    rw [show swapW (a :: v) = a.swapTwoThree :: swapW v from rfl, List.all_cons, List.all_cons, ih]
    cases a <;> rfl

theorem all_swapW_two (v : Word) :
    (swapW v).all (fun d => decide (d = Digit.two)) = v.all (fun d => decide (d = Digit.three)) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    rw [show swapW (a :: v) = a.swapTwoThree :: swapW v from rfl, List.all_cons, List.all_cons, ih]
    cases a <;> rfl

theorem isEmpty_swapW (v : Word) : (swapW v).isEmpty = v.isEmpty := by cases v <;> rfl

theorem swapW_replicate (k : ℕ) (d : Digit) : swapW (List.replicate k d) = List.replicate k d.swapTwoThree := by
  simp [swapW, List.map_replicate]

/-- The even L-correction of `w` against the odd L-correction of `swapW w` (`lemma:l_correc_properties` (1), odometers), when the
prefix `w_1 s` (before the trailing `3`s) is not `2^j`: stems, bridge and heads pair index by index. -/
theorem evenL_rawRot (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w : Word) (plus elong : Bool)
    (o oR : PartialOdometer)
    (ho : RespectsPieces o (evenLPieces S pO pE aO aE w plus elong))
    (hoR : RespectsPieces oR (oddLPieces S pO pE aO aE (swapW w) (plus != W1Odd w) elong))
    (hconn : (overlapGraph (goodPart (oddLPieces S pO pE aO aE (swapW w) (plus != W1Odd w) elong))).Connected)
    (hd : (!(stripTrailing Digit.three w).isEmpty && (stripTrailing Digit.three w).all (fun d => decide (d = Digit.two))) = false)
    (hlast : (stripTrailing Digit.three w).getLast? = some Digit.one ∨ (stripTrailing Digit.three w).getLast? = some Digit.two)
    (hS : RawRot (regOdo S pO pE (regsAt (stripTrailing Digit.three w)).1 true) (regOdo S pO pE (regsAt (swapW (stripTrailing Digit.three w))).2 false)
      (vP1 (stripTrailing Digit.three w) - ((0 : ℤ), (1 : ℤ))) 0)
    (hB : RawRot (regOdo S pO pE (regsAt (stripTrailing Digit.three w)).2 false) (regOdo S pO pE (regsAt (swapW (stripTrailing Digit.three w))).1 true)
      (vQ1 (stripTrailing Digit.three w) - ((0 : ℤ), (1 : ℤ))) 0)
    (hH : RawRot (regOdo S aO aE (regsAt (stripTrailing Digit.three w)).1 true) (regOdo S aO aE (regsAt (swapW (stripTrailing Digit.three w))).2 false)
      (altParP (stripTrailing Digit.three w)).1 (altParP (stripTrailing Digit.three w)).2) :
    RawRot o oR (texV1Even ((parentsAt w).current .even) - ((0 : ℤ), (1 : ℤ))) 0 := by
  refine rawRot_of_pairing o oR _ _ _ _ ho hoR (oddLPieces_covered _ _ _ _ _ _ _ _) hconn
    (pairingOK_of_forall₂ _ _ _ _ ?_)
  obtain ⟨hsw1, hsw2⟩ := swapW_strip_three w
  have hWw := W1Odd_swapW w
  have htrip : (!(swapW (stripTrailing Digit.three w)).isEmpty && (swapW (stripTrailing Digit.three w)).all (fun d => decide (d = Digit.three))) = false := by
    rw [isEmpty_swapW, all_swapW_three]; exact hd
  have hpw : parentsAt w = ⟨(parentsAt (stripTrailing Digit.three w)).odd, ⟨(parentsAt (stripTrailing Digit.three w)).even.num +
      2 * (trailingCount Digit.three w : ℕ) * (parentsAt (stripTrailing Digit.three w)).odd.num,
      (parentsAt (stripTrailing Digit.three w)).even.den + 2 * (trailingCount Digit.three w : ℕ) * (parentsAt (stripTrailing Digit.three w)).odd.den⟩⟩ := by
    conv_lhs => rw [← strip_append_replicate Digit.three w]
    exact parents_append_threes _ _
  have hpsw : parentsAt (swapW w) = ⟨⟨(parentsAt (swapW (stripTrailing Digit.three w))).odd.num +
      (trailingCount Digit.three w : ℕ) * (parentsAt (swapW (stripTrailing Digit.three w))).even.num,
      (parentsAt (swapW (stripTrailing Digit.three w))).odd.den + (trailingCount Digit.three w : ℕ) * (parentsAt (swapW (stripTrailing Digit.three w))).even.den⟩,
      (parentsAt (swapW (stripTrailing Digit.three w))).even⟩ := by
    conv_lhs => rw [← strip_append_replicate Digit.three w, swapW_append, swapW_replicate]
    exact parents_append_twos _ _
  have hWo : W1Odd w = W1Odd (stripTrailing Digit.three w) := by
    conv_lhs => rw [← strip_append_replicate Digit.three w]
    exact W1Odd_append_replicate _ _ _ (by decide)
  obtain ⟨-, -, -, -, e5, e6⟩ := vecs_swapW (stripTrailing Digit.three w)
  have hq : ((parentsAt (stripTrailing Digit.three w)).even.num + (parentsAt (stripTrailing Digit.three w)).even.den) % 2 = 0 := (parentsAt_valid _).even_parity
  obtain ⟨a, hdq⟩ : ∃ a : ℤ, (parentsAt (stripTrailing Digit.three w)).even.den = 2 * a + (parentsAt (stripTrailing Digit.three w)).even.num :=
    ⟨((parentsAt (stripTrailing Digit.three w)).even.den - (parentsAt (stripTrailing Digit.three w)).even.num) / 2, by omega⟩
  have hA : (2 * a + (parentsAt (stripTrailing Digit.three w)).even.num - (parentsAt (stripTrailing Digit.three w)).even.num) / 2 = a := by omega
  have hB' : (2 * a + (parentsAt (stripTrailing Digit.three w)).even.num + (parentsAt (stripTrailing Digit.three w)).even.num) / 2 = a + (parentsAt (stripTrailing Digit.three w)).even.num := by omega
  simp only [evenLPieces, oddLPieces, hsw1, hsw2, hWw, hd, htrip, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    List.append_nil]
  refine List.rel_append (List.rel_append ?_ (List.Forall₂.cons ?_ List.Forall₂.nil)) ?_
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
    intro j _
    refine ⟨vP1 (stripTrailing Digit.three w) - ((0 : ℤ), (1 : ℤ)), 0, hS, ?_, ?_, ?_, fun x _ _ => by simp [stdPiece]⟩ <;>
    rcases hlast with hl | hl <;> cases hWs : W1Odd (stripTrailing Digit.three w) <;> cases plus <;> l_unfold <;> simp only [hdq] <;>
      simp only [hA, hB'] <;> l_ring
  · refine ⟨vQ1 (stripTrailing Digit.three w) - ((0 : ℤ), (1 : ℤ)), 0, hB, ?_, ?_, ?_, fun x _ _ => by simp [stdPiece]⟩ <;>
    rcases hlast with hl | hl <;> cases hWs : W1Odd (stripTrailing Digit.three w) <;> cases plus <;> l_unfold <;> simp only [hdq] <;>
      simp only [hA, hB'] <;> l_ring
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
    intro i _
    refine ⟨(altParP (stripTrailing Digit.three w)).1, (altParP (stripTrailing Digit.three w)).2, hH, ?_, ?_, ?_, fun x _ _ => by simp⟩ <;>
    rcases hlast with hl | hl <;> cases hWs : W1Odd (stripTrailing Digit.three w) <;> cases plus <;> l_unfold <;> simp only [hdq] <;>
      simp only [hA, hB'] <;> l_ring

set_option maxHeartbeats 400000 in
/-- The odd L-correction of `w` against the even L-correction of `swapW w`, when the prefix (before the trailing `2`s) is not
`3^j`: stems, bridge and heads pair index by index. -/
theorem oddL_rawRot (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w : Word) (plus elong : Bool)
    (o oR : PartialOdometer)
    (ho : RespectsPieces o (oddLPieces S pO pE aO aE w plus elong))
    (hoR : RespectsPieces oR (evenLPieces S pO pE aO aE (swapW w) (plus == W1Odd w) elong))
    (hconn : (overlapGraph (goodPart (evenLPieces S pO pE aO aE (swapW w) (plus == W1Odd w) elong))).Connected)
    (hd : (!(stripTrailing Digit.two w).isEmpty && (stripTrailing Digit.two w).all (fun d => decide (d = Digit.three))) = false)
    (hlast : (stripTrailing Digit.two w).getLast? = some Digit.one ∨ (stripTrailing Digit.two w).getLast? = some Digit.three)
    (hS : RawRot (regOdo S pO pE (regsAt (stripTrailing Digit.two w)).2 false) (regOdo S pO pE (regsAt (swapW (stripTrailing Digit.two w))).1 true)
      (vQ1 (stripTrailing Digit.two w) - ((0 : ℤ), (1 : ℤ))) 0)
    (hB : RawRot (regOdo S pO pE (regsAt (stripTrailing Digit.two w)).1 true) (regOdo S pO pE (regsAt (swapW (stripTrailing Digit.two w))).2 false)
      (vP1 (stripTrailing Digit.two w) - ((0 : ℤ), (1 : ℤ))) 0)
    (hH : RawRot (regOdo S aO aE (regsAt (stripTrailing Digit.two w)).2 false) (regOdo S aO aE (regsAt (swapW (stripTrailing Digit.two w))).1 true)
      (altParQ (stripTrailing Digit.two w)).1 (altParQ (stripTrailing Digit.two w)).2) :
    RawRot o oR (texV1Odd ((parentsAt w).current .odd) - ((0 : ℤ), (1 : ℤ))) 0 := by
  refine rawRot_of_pairing o oR _ _ _ _ ho hoR (evenLPieces_covered _ _ _ _ _ _ _ _) hconn
    (pairingOK_of_forall₂ _ _ _ _ ?_)
  obtain ⟨hsw1, hsw2⟩ := swapW_strip_two w
  have hWw := W1Odd_swapW w
  have hdbl : (!(swapW (stripTrailing Digit.two w)).isEmpty && (swapW (stripTrailing Digit.two w)).all (fun d => decide (d = Digit.two))) = false := by
    rw [isEmpty_swapW, all_swapW_two]; exact hd
  have hpw : parentsAt w = ⟨⟨(parentsAt (stripTrailing Digit.two w)).odd.num + (trailingCount Digit.two w : ℕ) * (parentsAt (stripTrailing Digit.two w)).even.num,
      (parentsAt (stripTrailing Digit.two w)).odd.den + (trailingCount Digit.two w : ℕ) * (parentsAt (stripTrailing Digit.two w)).even.den⟩, (parentsAt (stripTrailing Digit.two w)).even⟩ := by
    conv_lhs => rw [← strip_append_replicate Digit.two w]
    exact parents_append_twos _ _
  have hpsw : parentsAt (swapW w) = ⟨(parentsAt (swapW (stripTrailing Digit.two w))).odd, ⟨(parentsAt (swapW (stripTrailing Digit.two w))).even.num +
      2 * (trailingCount Digit.two w : ℕ) * (parentsAt (swapW (stripTrailing Digit.two w))).odd.num,
      (parentsAt (swapW (stripTrailing Digit.two w))).even.den + 2 * (trailingCount Digit.two w : ℕ) * (parentsAt (swapW (stripTrailing Digit.two w))).odd.den⟩⟩ := by
    conv_lhs => rw [← strip_append_replicate Digit.two w, swapW_append, swapW_replicate]
    exact parents_append_threes _ _
  have hWo : W1Odd w = W1Odd (stripTrailing Digit.two w) := by
    conv_lhs => rw [← strip_append_replicate Digit.two w]
    exact W1Odd_append_replicate _ _ _ (by decide)
  obtain ⟨-, -, -, -, e5, e6⟩ := vecs_swapW (stripTrailing Digit.two w)
  have hq : ((parentsAt (stripTrailing Digit.two w)).even.num + (parentsAt (stripTrailing Digit.two w)).even.den) % 2 = 0 := (parentsAt_valid _).even_parity
  obtain ⟨a, hdq⟩ : ∃ a : ℤ, (parentsAt (stripTrailing Digit.two w)).even.den = 2 * a + (parentsAt (stripTrailing Digit.two w)).even.num :=
    ⟨((parentsAt (stripTrailing Digit.two w)).even.den - (parentsAt (stripTrailing Digit.two w)).even.num) / 2, by omega⟩
  have hA : (2 * a + (parentsAt (stripTrailing Digit.two w)).even.num - (parentsAt (stripTrailing Digit.two w)).even.num) / 2 = a := by omega
  have hB' : (2 * a + (parentsAt (stripTrailing Digit.two w)).even.num + (parentsAt (stripTrailing Digit.two w)).even.num) / 2 = a + (parentsAt (stripTrailing Digit.two w)).even.num := by omega
  simp only [evenLPieces, oddLPieces, hsw1, hsw2, hWw, hd, hdbl, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    List.append_nil]
  refine List.rel_append (List.rel_append ?_ (List.Forall₂.cons ?_ List.Forall₂.nil)) ?_
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
    intro j _
    refine ⟨vQ1 (stripTrailing Digit.two w) - ((0 : ℤ), (1 : ℤ)), 0, hS, ?_, ?_, ?_, fun x _ _ => by simp [stdPiece]⟩ <;>
    rcases hlast with hl | hl <;> cases hWs : W1Odd (stripTrailing Digit.two w) <;> cases plus <;> l_unfold <;> simp only [hdq] <;>
      simp only [hA, hB'] <;> l_ring
  · refine ⟨vP1 (stripTrailing Digit.two w) - ((0 : ℤ), (1 : ℤ)), 0, hB, ?_, ?_, ?_, fun x _ _ => by simp [stdPiece]⟩ <;>
    rcases hlast with hl | hl <;> cases hWs : W1Odd (stripTrailing Digit.two w) <;> cases plus <;> l_unfold <;> simp only [hdq] <;>
      simp only [hA, hB'] <;> l_ring
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
    intro i _
    refine ⟨(altParQ (stripTrailing Digit.two w)).1, (altParQ (stripTrailing Digit.two w)).2, hH, ?_, ?_, ?_, fun x _ _ => by simp⟩ <;>
    rcases hlast with hl | hl <;> cases hWs : W1Odd (stripTrailing Digit.two w) <;> cases plus <;> l_unfold <;> simp only [hdq] <;>
      simp only [hA, hB'] <;> l_ring

/-! ### The L-rotation at one level -/

theorem lRotation_of_rawRot (o oR : PartialOdometer) (v1 : Site) (h : RawRot o oR (v1 - ((0 : ℤ), (1 : ℤ))) 0) :
    LRotation o oR v1 := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun y hy => ?_⟩
  obtain ⟨hm, hv⟩ := hC y hy
  rw [← add_sub_assoc] at hm hv
  refine ⟨hm, ?_⟩
  rw [hv]
  simp [dotS]

theorem regs_none (w : Word) : ((regsAt w).1 = none → ∀ d ∈ w, d = Digit.three) ∧
    ((regsAt w).2 = none → ∀ d ∈ w, d = Digit.two) := by
  induction w using List.reverseRecOn with
  | nil => exact ⟨fun _ d hd => by simp at hd, fun _ d hd => by simp at hd⟩
  | append_singleton v d ih =>
    rw [regsAt_append_singleton]
    cases d
    · exact ⟨fun h => by simp [regStep] at h, fun h => by simp [regStep] at h⟩
    · refine ⟨fun h => by simp [regStep] at h, fun h e he => ?_⟩
      simp only [List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · exact ih.2 h e he
      · rfl
    · refine ⟨fun h e he => ?_, fun h => by simp [regStep] at h⟩
      simp only [List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · exact ih.1 h e he
      · rfl

theorem strip_of_defined (d s : Digit) (hs : s ≠ d) (v : Word) (k : ℕ) :
    stripTrailing d (v ++ [s] ++ List.replicate k d) = v ++ [s] := by
  induction k with
  | zero => simp [stripTrailing_snoc, hs]
  | succ k ih => rw [List.replicate_succ', ← List.append_assoc, stripTrailing_snoc, if_pos rfl, ih]

theorem oddLDefined_swapW {w : Word} (h : EvenLDefined w) : OddLDefined (swapW w) := by
  obtain ⟨v, s, k, hs, rfl⟩ := h
  refine ⟨swapW v, s.swapTwoThree, k, by cases s <;> simp_all [Digit.swapTwoThree], ?_⟩
  rw [swapW_append, swapW_append, swapW_replicate]
  rfl

theorem evenLDefined_swapW {w : Word} (h : OddLDefined w) : EvenLDefined (swapW w) := by
  obtain ⟨v, s, k, hs, rfl⟩ := h
  refine ⟨swapW v, s.swapTwoThree, k, by cases s <;> simp_all [Digit.swapTwoThree], ?_⟩
  rw [swapW_append, swapW_append, swapW_replicate]
  rfl

/-- The overlap graphs of the L decompositions of `w` are connected. -/
def ConnectedL (D : JointData) (g : Word → JSlice) (w : Word) : Prop :=
  (∀ plus elong : Bool, OddLDefined w →
    (overlapGraph (goodPart (oddLPieces D.S (fun u => (g u).tOdd) (fun u => (g u).tEven) (fun u => (g u).aOdd)
      (fun u => (g u).aEven) w plus elong))).Connected) ∧
  (∀ plus elong : Bool, EvenLDefined w →
    (overlapGraph (goodPart (evenLPieces D.S (fun u => (g u).tOdd) (fun u => (g u).tEven) (fun u => (g u).aOdd)
      (fun u => (g u).aEven) w plus elong))).Connected)

/-- The L-rotation at the words of length `n` whose prefix is `2^j` (even L) or `3^j` (odd L): a named input (the zero-one
odometers and the exceptional points of the first heads). -/
def SpecialLRot (f : Word → JSlice) (n : ℕ) : Prop :=
  ∀ w : Word, w.length = n →
    (EvenLDefined w → (stripTrailing Digit.three w ≠ [] ∧ ∀ d ∈ stripTrailing Digit.three w, d = Digit.two) →
      ∀ plus elong : Bool, LRotation ((f w).lEven plus elong) ((f (swapW w)).lOdd (plus != W1Odd w) elong)
        (texV1Even ((parentsAt w).current .even))) ∧
    (OddLDefined w → (stripTrailing Digit.two w ≠ [] ∧ ∀ d ∈ stripTrailing Digit.two w, d = Digit.three) →
      ∀ plus elong : Bool, LRotation ((f w).lOdd plus elong) ((f (swapW w)).lEven (plus == W1Odd w) elong)
        (texV1Odd ((parentsAt w).current .odd)))

/-- `lemma:l_correc_properties` (1) for the L-corrected odometers at the level `n`, from the family below `n`, the slices at level
`n`, the base slopes, the connectivity of the overlap graphs of the L decompositions, and the special prefixes. -/
theorem lRotProps_step (D : JointData) (f : Word → JSlice) (n : ℕ) (hgood : GoodBelow D f n)
    (hlev : ∀ w : Word, w.length = n → IsJointSlice D f w) (hB : BaseSlopes D)
    (hconn : ∀ w : Word, w.length = n → ConnectedL D (below f w) w) (hspec : SpecialLRot f n)
    (w : Word) (hw : w.length = n) : LRotProps w (f w) (f (swapW w)) := by
  have hJ : ∀ u : Word, u.length ≤ n → IsJointSlice D f u := fun u hu => by
    rcases lt_or_eq_of_le hu with h | h
    · exact (hgood u h).1
    · exact hlev u h
  have hsl := family_slopes D f n hJ hB
  have hsw : (swapW w).length = n := by rw [length_swapW, hw]
  obtain ⟨-, -, -, hLp⟩ := hlev w hw
  obtain ⟨-, -, -, hLp'⟩ := hlev (swapW w) hsw
  obtain ⟨hcO, hcE⟩ := hconn (swapW w) hsw
  rw [below_swapW] at hLp' hcO hcE
  refine ⟨fun hdef plus elong => ?_, fun hdef plus elong => ?_⟩
  · -- the even L-correction
    by_cases hsp : stripTrailing Digit.three w ≠ [] ∧ ∀ d ∈ stripTrailing Digit.three w, d = Digit.two
    · exact (hspec w hw).1 hdef hsp plus elong
    have hd : (!(stripTrailing Digit.three w).isEmpty &&
        (stripTrailing Digit.three w).all (fun d => decide (d = Digit.two))) = false := by
      by_contra hc
      simp only [Bool.not_eq_false, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_eq_false_iff,
        List.all_eq_true, decide_eq_true_eq] at hc
      exact hsp hc
    obtain ⟨v, s, k, hs, hwv⟩ := hdef
    have hpre : stripTrailing Digit.three w = v ++ [s] := by rw [hwv]; exact strip_of_defined _ _ hs v k
    have hlen : (v ++ [s]).length ≤ w.length := by
      rw [← hpre]; exact stripTrailing_length_le _ _
    have hvlen : v.length < w.length := by simp at hlen; omega
    have hlast : (stripTrailing Digit.three w).getLast? = some Digit.one ∨
        (stripTrailing Digit.three w).getLast? = some Digit.two := by
      rw [hpre]; cases s <;> simp_all
    have hr1 : (regsAt (stripTrailing Digit.three w)).1 = some v := by
      rw [hpre, regsAt_append_singleton]; cases s <;> simp_all [regStep]
    obtain ⟨u2, hr2⟩ : ∃ u2, (regsAt (stripTrailing Digit.three w)).2 = some u2 := by
      cases h : (regsAt (stripTrailing Digit.three w)).2 with
      | none => exact absurd ⟨by rw [hpre]; simp, (regs_none _).2 h⟩ hsp
      | some u2 => exact ⟨u2, rfl⟩
    have l2 := FLatticePaper.Tiles.JointInduction.regsAt_lt _ u2 (Or.inr hr2)
    have l2' : u2.length < w.length := by have := stripTrailing_length_le Digit.three w; omega
    obtain ⟨pr1, pr2⟩ := parents_of_regs (stripTrailing Digit.three w)
    have J1 := (hgood v (by omega)).2.2.2.1
    have J2 := (hgood u2 (by omega)).2.2.2.1
    have hS : RawRot (regOdo D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven)
        (regsAt (stripTrailing Digit.three w)).1 true) (regOdo D.S (fun u => (below f w u).tOdd)
        (fun u => (below f w u).tEven) (regsAt (swapW (stripTrailing Digit.three w))).2 false)
        (vP1 (stripTrailing Digit.three w) - ((0 : ℤ), (1 : ℤ))) 0 := by
      rw [regsAt_swapW, hr1]
      show RawRot (below f w v).tOdd (below f w (swapW v)).tEven _ _
      rw [below_of_lt f w v hvlen, below_of_lt f w (swapW v) (by rw [length_swapW]; exact hvlen)]
      have h := J1.1
      rw [pr1 v hr1] at h
      exact rawRot_of_tileRotation_slopes _ _ _ h (hsl v (by omega)).1 (hsl (swapW v) (by rw [length_swapW]; omega)).2.1
    have hBr : RawRot (regOdo D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven)
        (regsAt (stripTrailing Digit.three w)).2 false) (regOdo D.S (fun u => (below f w u).tOdd)
        (fun u => (below f w u).tEven) (regsAt (swapW (stripTrailing Digit.three w))).1 true)
        (vQ1 (stripTrailing Digit.three w) - ((0 : ℤ), (1 : ℤ))) 0 := by
      rw [regsAt_swapW, hr2]
      show RawRot (below f w u2).tEven (below f w (swapW u2)).tOdd _ _
      rw [below_of_lt f w u2 l2', below_of_lt f w (swapW u2) (by rw [length_swapW]; exact l2')]
      have h := J2.2.1
      rw [pr2 u2 hr2] at h
      exact rawRot_of_tileRotation_slopes _ _ _ h (hsl u2 (by omega)).2.1 (hsl (swapW u2) (by rw [length_swapW]; omega)).1
    have hH : RawRot (regOdo D.S (fun u => (below f w u).aOdd) (fun u => (below f w u).aEven)
        (regsAt (stripTrailing Digit.three w)).1 true) (regOdo D.S (fun u => (below f w u).aOdd)
        (fun u => (below f w u).aEven) (regsAt (swapW (stripTrailing Digit.three w))).2 false)
        (altParP (stripTrailing Digit.three w)).1 (altParP (stripTrailing Digit.three w)).2 := by
      rw [regsAt_swapW, hr1]
      show RawRot (below f w v).aOdd (below f w (swapW v)).aEven _ _
      rw [below_of_lt f w v hvlen, below_of_lt f w (swapW v) (by rw [length_swapW]; exact hvlen)]
      have h := J1.2.2.1
      have hcf := altCf_odd_reg v s (by cases s <;> simp_all)
      rw [← hpre] at hcf
      rw [hcf] at h
      exact rawRot_of_altRotation_slopes _ _ _ _ h (hsl v (by omega)).2.2.1
        (hsl (swapW v) (by rw [length_swapW]; omega)).2.2.2
    have hdef' : EvenLDefined w := ⟨v, s, k, hs, hwv⟩
    have ho := (hLp.2 plus elong hdef').1
    have hoR := (hLp'.1 (plus != W1Odd w) elong (oddLDefined_swapW hdef')).1
    exact lRotation_of_rawRot _ _ _ (evenL_rawRot D.S _ _ _ _ w plus elong _ _ ho hoR
      (hcO (plus != W1Odd w) elong (oddLDefined_swapW hdef')) hd hlast hS hBr hH)
  · -- the odd L-correction
    by_cases hsp : stripTrailing Digit.two w ≠ [] ∧ ∀ d ∈ stripTrailing Digit.two w, d = Digit.three
    · exact (hspec w hw).2 hdef hsp plus elong
    have hd : (!(stripTrailing Digit.two w).isEmpty &&
        (stripTrailing Digit.two w).all (fun d => decide (d = Digit.three))) = false := by
      by_contra hc
      simp only [Bool.not_eq_false, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_eq_false_iff,
        List.all_eq_true, decide_eq_true_eq] at hc
      exact hsp hc
    obtain ⟨v, s, k, hs, hwv⟩ := hdef
    have hpre : stripTrailing Digit.two w = v ++ [s] := by rw [hwv]; exact strip_of_defined _ _ hs v k
    have hlen : (v ++ [s]).length ≤ w.length := by
      rw [← hpre]; exact stripTrailing_length_le _ _
    have hvlen : v.length < w.length := by simp at hlen; omega
    have hlast : (stripTrailing Digit.two w).getLast? = some Digit.one ∨
        (stripTrailing Digit.two w).getLast? = some Digit.three := by
      rw [hpre]; cases s <;> simp_all
    have hr2 : (regsAt (stripTrailing Digit.two w)).2 = some v := by
      rw [hpre, regsAt_append_singleton]; cases s <;> simp_all [regStep]
    obtain ⟨u1, hr1⟩ : ∃ u1, (regsAt (stripTrailing Digit.two w)).1 = some u1 := by
      cases h : (regsAt (stripTrailing Digit.two w)).1 with
      | none => exact absurd ⟨by rw [hpre]; simp, (regs_none _).1 h⟩ hsp
      | some u1 => exact ⟨u1, rfl⟩
    have l1 := FLatticePaper.Tiles.JointInduction.regsAt_lt _ u1 (Or.inl hr1)
    have l1' : u1.length < w.length := by have := stripTrailing_length_le Digit.two w; omega
    obtain ⟨pr1, pr2⟩ := parents_of_regs (stripTrailing Digit.two w)
    have J1 := (hgood u1 (by omega)).2.2.2.1
    have J2 := (hgood v (by omega)).2.2.2.1
    have hS : RawRot (regOdo D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven)
        (regsAt (stripTrailing Digit.two w)).2 false) (regOdo D.S (fun u => (below f w u).tOdd)
        (fun u => (below f w u).tEven) (regsAt (swapW (stripTrailing Digit.two w))).1 true)
        (vQ1 (stripTrailing Digit.two w) - ((0 : ℤ), (1 : ℤ))) 0 := by
      rw [regsAt_swapW, hr2]
      show RawRot (below f w v).tEven (below f w (swapW v)).tOdd _ _
      rw [below_of_lt f w v hvlen, below_of_lt f w (swapW v) (by rw [length_swapW]; exact hvlen)]
      have h := J2.2.1
      rw [pr2 v hr2] at h
      exact rawRot_of_tileRotation_slopes _ _ _ h (hsl v (by omega)).2.1 (hsl (swapW v) (by rw [length_swapW]; omega)).1
    have hBr : RawRot (regOdo D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven)
        (regsAt (stripTrailing Digit.two w)).1 true) (regOdo D.S (fun u => (below f w u).tOdd)
        (fun u => (below f w u).tEven) (regsAt (swapW (stripTrailing Digit.two w))).2 false)
        (vP1 (stripTrailing Digit.two w) - ((0 : ℤ), (1 : ℤ))) 0 := by
      rw [regsAt_swapW, hr1]
      show RawRot (below f w u1).tOdd (below f w (swapW u1)).tEven _ _
      rw [below_of_lt f w u1 l1', below_of_lt f w (swapW u1) (by rw [length_swapW]; exact l1')]
      have h := J1.1
      rw [pr1 u1 hr1] at h
      exact rawRot_of_tileRotation_slopes _ _ _ h (hsl u1 (by omega)).1 (hsl (swapW u1) (by rw [length_swapW]; omega)).2.1
    have hH : RawRot (regOdo D.S (fun u => (below f w u).aOdd) (fun u => (below f w u).aEven)
        (regsAt (stripTrailing Digit.two w)).2 false) (regOdo D.S (fun u => (below f w u).aOdd)
        (fun u => (below f w u).aEven) (regsAt (swapW (stripTrailing Digit.two w))).1 true)
        (altParQ (stripTrailing Digit.two w)).1 (altParQ (stripTrailing Digit.two w)).2 := by
      rw [regsAt_swapW, hr2]
      show RawRot (below f w v).aEven (below f w (swapW v)).aOdd _ _
      rw [below_of_lt f w v hvlen, below_of_lt f w (swapW v) (by rw [length_swapW]; exact hvlen)]
      have h := J2.2.2.2
      have hcf := altCf_even_reg v s (by cases s <;> simp_all)
      rw [← hpre] at hcf
      rw [hcf] at h
      exact rawRot_of_altRotation_slopes _ _ _ _ h (hsl v (by omega)).2.2.2
        (hsl (swapW v) (by rw [length_swapW]; omega)).2.2.1
    have hdef' : OddLDefined w := ⟨v, s, k, hs, hwv⟩
    have ho := (hLp.1 plus elong hdef').1
    have hoR := (hLp'.2 (plus == W1Odd w) elong (evenLDefined_swapW hdef')).1
    exact lRotation_of_rawRot _ _ _ (oddL_rawRot D.S _ _ _ _ w plus elong _ _ ho hoR
      (hcE (plus == W1Odd w) elong (evenLDefined_swapW hdef')) hd hlast hS hBr hH)

/-! ### The rotation step -/

/-- The hypothesis of the rotation step at level `n`: the family below `n` and the slices, (c) of the weak odometers and (a), (b)
of the tile odometers at level `n`. -/
def LevelHyp (D : JointData) (f : Word → JSlice) (n : ℕ) : Prop :=
  GoodBelow D f n ∧ ∀ w : Word, w.length = n →
    IsJointSlice D f w ∧ WeakPropsU w (f w).wOdd (f w).wEven ∧ TileProps w (f w).tOdd (f w).tEven (f w).aOdd (f w).aEven

/-- The rotation step of the joint induction ((c) of `lemma:tile-odometer-existence` and `lemma:l_correc_properties` (1) for the
odometers), from the named inputs: the base slopes and base rotations (`baseSlopes_paper`, `base_rotProps` for the paper data),
the connectivity of the overlap graphs of the decompositions, and the L-rotation at the special prefixes `2^j`, `3^j`. -/
theorem rotStepInput_of (D : JointData) (hB : BaseSlopes D) (hBR : BaseRot D)
    (hconn : ∀ (f : Word → JSlice) (n : ℕ), LevelHyp D f n →
      ∀ w : Word, w.length = n → ¬ IsBase w → Connected4 D (below f w) w)
    (hconnL : ∀ (f : Word → JSlice) (n : ℕ), LevelHyp D f n → ∀ w : Word, w.length = n → ConnectedL D (below f w) w)
    (hspec : ∀ (f : Word → JSlice) (n : ℕ), LevelHyp D f n → SpecialLRot f n) :
    RotStepInput D := by
  intro f n hg hlev w hw
  have hL : LevelHyp D f n := ⟨hg, hlev⟩
  exact ⟨rotProps_step D f n hg (fun w hw => (hlev w hw).1) hB hBR (hconn f n hL) w hw,
    lRotProps_step D f n hg (fun w hw => (hlev w hw).1) hB (hconnL f n hL) (hspec f n hL) w hw⟩

/-! ### Connectivity of the standard decompositions -/

/-- The eight corner points of `eq:std_corner_values` lie in the domain. -/
structure StdCorners (o : PartialOdometer) (X Y : Site) : Prop where
  c0 : ((0 : ℤ), (0 : ℤ)) ∈ o.dom
  c1 : ((1 : ℤ), (0 : ℤ)) ∈ o.dom
  cXi : X - ((0 : ℤ), (1 : ℤ)) ∈ o.dom
  cX : X ∈ o.dom
  cY1 : Y + ((1 : ℤ), (0 : ℤ)) ∈ o.dom
  cY1i : Y + ((1 : ℤ), (-1 : ℤ)) ∈ o.dom
  cD : X + Y + ((1 : ℤ), (-1 : ℤ)) ∈ o.dom
  cD1 : X + Y + ((0 : ℤ), (-1 : ℤ)) ∈ o.dom

theorem adj_of_mem (ps : List Piece) (i j : Fin ps.length) (hij : i.1 ≠ j.1) (x : Site)
    (hi : x ∈ (ps.get i).placed) (hj : x ∈ (ps.get j).placed) (hei : x ∉ (ps.get i).exc) (hej : x ∉ (ps.get j).exc) :
    (overlapGraph (goodPart ps)).Adj i j :=
  ⟨fun h => hij (by rw [h]), ⟨⟨x, mem_pieceUnion.mpr ⟨_, List.get_mem _ _, hi⟩⟩, ⟨hi, hei⟩, ⟨hj, hej⟩⟩⟩

theorem connected_of_reach (ps : List Piece) (h0 : 0 < ps.length)
    (h : ∀ k : Fin ps.length, (overlapGraph (goodPart ps)).Reachable ⟨0, h0⟩ k) :
    (overlapGraph (goodPart ps)).Connected := by
  haveI : Nonempty (Fin ps.length) := ⟨⟨0, h0⟩⟩
  exact ⟨fun u v => (h u).symm.trans (h v)⟩

set_option hygiene false in
/-- The odometer of a piece of a standard decomposition, with the phase and the last letter fixed. -/
macro "conn_odo" : tactic => `(tactic| (
  simp only [tileOddPieces, tileEvenPieces, List.get_eq_getElem, List.getElem_cons_succ, List.getElem_cons_zero, stdPiece,
    hWo, hc, decide_true, decide_false, Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and, Bool.not_true,
    Bool.not_false, ↓reduceIte, Bool.false_eq_true]))

set_option hygiene false in
/-- The offset identity of a witness. -/
macro "conn_id" : tactic => `(tactic| (
  simp only [tileOddPieces, tileEvenPieces, List.get_eq_getElem, List.getElem_cons_succ, List.getElem_cons_zero, stdPiece,
    p0Off, q0Off, offsetP0, offsetQ0, hWo, ↓reduceIte, Bool.false_eq_true]
  refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero,
    Prod.snd_zero, vP1, vP2, vQ1, vQ2, texV1Odd, texV1Even, texV2] <;> omega))

set_option hygiene false in
macro "conn_exc" : tactic => `(tactic| (simp [tileOddPieces, tileEvenPieces, stdPiece]))

/-- The overlap graph of the odd standard decomposition is connected: a spanning tree of overlaps witnessed by corner points of
the parents (`StdCorners`) and, for the L-corrected copies, by points of the kept side of the child of the parent word. -/
theorem tileOddPieces_connected (S : WeakData) (pO pE : Word → PartialOdometer) (lE : Word → Bool → Bool → PartialOdometer)
    (w : Word)
    (hP : StdCorners (regOdo S pO pE (regsAt w).1 true) (vP1 w) (vP2 w))
    (hQ : StdCorners (regOdo S pO pE (regsAt w).2 false) (vQ1 w) (vQ2 w))
    (hL : w.getLast? = some Digit.three →
      ((((0 : ℤ), (0 : ℤ)) ∈ (lE w.dropLast true false).dom ∧ vQ1 w ∈ (lE w.dropLast true false).dom) ∧
        vQ2 w + ((1 : ℤ), (-1 : ℤ)) ∈ (lE w.dropLast false false).dom)) :
    (overlapGraph (goodPart (tileOddPieces S pO pE lE w))).Connected := by
  have h0 : 0 < (tileOddPieces S pO pE lE w).length := by simp [tileOddPieces]
  refine connected_of_reach _ h0 (fun k => ?_)
  cases hWo : W1Odd w <;> by_cases hc : w.getLast? = some Digit.three
  · -- W1Odd = False, corrected = True
    have a03 : (overlapGraph (goodPart (tileOddPieces S pO pE lE w))).Adj ⟨0, by simp [tileOddPieces]⟩ ⟨3, by simp [tileOddPieces]⟩ := by
      refine adj_of_mem _ _ _ (by simp) (((tileOddPieces S pO pE lE w).get ⟨0, by simp [tileOddPieces]⟩).off + (((0 : ℤ), (0 : ℤ)))) ?_ ?_ ?_ ?_
      · rw [mem_placed, add_sub_cancel_left]
        conn_odo
        exact hP.c0
      · rw [mem_placed, show (((tileOddPieces S pO pE lE w).get ⟨0, by simp [tileOddPieces]⟩).off + (((0 : ℤ), (0 : ℤ)))) - ((tileOddPieces S pO pE lE w).get ⟨3, by simp [tileOddPieces]⟩).off = vQ1 w by conn_id]
        conn_odo
        exact (hL hc).1.2
      · conn_exc
      · conn_exc
    have a05 : (overlapGraph (goodPart (tileOddPieces S pO pE lE w))).Adj ⟨0, by simp [tileOddPieces]⟩ ⟨5, by simp [tileOddPieces]⟩ := by
      refine adj_of_mem _ _ _ (by simp) (((tileOddPieces S pO pE lE w).get ⟨0, by simp [tileOddPieces]⟩).off + (vP1 w + vP2 w + ((0 : ℤ), (-1 : ℤ)))) ?_ ?_ ?_ ?_
      · rw [mem_placed, add_sub_cancel_left]
        conn_odo
        exact hP.cD1
      · rw [mem_placed, show (((tileOddPieces S pO pE lE w).get ⟨0, by simp [tileOddPieces]⟩).off + (vP1 w + vP2 w + ((0 : ℤ), (-1 : ℤ)))) - ((tileOddPieces S pO pE lE w).get ⟨5, by simp [tileOddPieces]⟩).off = vQ1 w - ((0 : ℤ), (1 : ℤ)) by conn_id]
        conn_odo
        exact hQ.cXi
      · conn_exc
      · conn_exc
    have a23 : (overlapGraph (goodPart (tileOddPieces S pO pE lE w))).Adj ⟨2, by simp [tileOddPieces]⟩ ⟨3, by simp [tileOddPieces]⟩ := by
      refine adj_of_mem _ _ _ (by simp) (((tileOddPieces S pO pE lE w).get ⟨2, by simp [tileOddPieces]⟩).off + (vQ1 w)) ?_ ?_ ?_ ?_
      · rw [mem_placed, add_sub_cancel_left]
        conn_odo
        exact hQ.cX
      · rw [mem_placed, show (((tileOddPieces S pO pE lE w).get ⟨2, by simp [tileOddPieces]⟩).off + (vQ1 w)) - ((tileOddPieces S pO pE lE w).get ⟨3, by simp [tileOddPieces]⟩).off = ((0 : ℤ), (0 : ℤ)) by conn_id]
        conn_odo
        exact (hL hc).1.1
      · conn_exc
      · conn_exc
    have a12 : (overlapGraph (goodPart (tileOddPieces S pO pE lE w))).Adj ⟨1, by simp [tileOddPieces]⟩ ⟨2, by simp [tileOddPieces]⟩ := by
      refine adj_of_mem _ _ _ (by simp) (((tileOddPieces S pO pE lE w).get ⟨1, by simp [tileOddPieces]⟩).off + (((1 : ℤ), (0 : ℤ)))) ?_ ?_ ?_ ?_
      · rw [mem_placed, add_sub_cancel_left]
        conn_odo
        exact hP.c1
      · rw [mem_placed, show (((tileOddPieces S pO pE lE w).get ⟨1, by simp [tileOddPieces]⟩).off + (((1 : ℤ), (0 : ℤ)))) - ((tileOddPieces S pO pE lE w).get ⟨2, by simp [tileOddPieces]⟩).off = vQ2 w + ((1 : ℤ), (0 : ℤ)) by conn_id]
        conn_odo
        exact hQ.cY1
      · conn_exc
      · conn_exc
    have a14 : (overlapGraph (goodPart (tileOddPieces S pO pE lE w))).Adj ⟨1, by simp [tileOddPieces]⟩ ⟨4, by simp [tileOddPieces]⟩ := by
      refine adj_of_mem _ _ _ (by simp) (((tileOddPieces S pO pE lE w).get ⟨1, by simp [tileOddPieces]⟩).off + (vP1 w + vP2 w + ((1 : ℤ), (-1 : ℤ)))) ?_ ?_ ?_ ?_
      · rw [mem_placed, add_sub_cancel_left]
        conn_odo
        exact hP.cD
      · rw [mem_placed, show (((tileOddPieces S pO pE lE w).get ⟨1, by simp [tileOddPieces]⟩).off + (vP1 w + vP2 w + ((1 : ℤ), (-1 : ℤ)))) - ((tileOddPieces S pO pE lE w).get ⟨4, by simp [tileOddPieces]⟩).off = vQ2 w + ((1 : ℤ), (-1 : ℤ)) by conn_id]
        conn_odo
        exact (hL hc).2
      · conn_exc
      · conn_exc
    obtain ⟨kv, hk⟩ := k
    rcases kv with _ | _ | _ | _ | _ | _ | kv
    · exact SimpleGraph.Reachable.refl _
    · exact (((SimpleGraph.Reachable.refl _).trans (a03).reachable).trans (a23.symm).reachable).trans (a12.symm).reachable
    · exact ((SimpleGraph.Reachable.refl _).trans (a03).reachable).trans (a23.symm).reachable
    · exact (SimpleGraph.Reachable.refl _).trans (a03).reachable
    · exact ((((SimpleGraph.Reachable.refl _).trans (a03).reachable).trans (a23.symm).reachable).trans (a12.symm).reachable).trans (a14).reachable
    · exact (SimpleGraph.Reachable.refl _).trans (a05).reachable
    · simp [tileOddPieces] at hk; omega
  · -- W1Odd = False, corrected = False
    have a03 : (overlapGraph (goodPart (tileOddPieces S pO pE lE w))).Adj ⟨0, by simp [tileOddPieces]⟩ ⟨3, by simp [tileOddPieces]⟩ := by
      refine adj_of_mem _ _ _ (by simp) (((tileOddPieces S pO pE lE w).get ⟨0, by simp [tileOddPieces]⟩).off + (((0 : ℤ), (0 : ℤ)))) ?_ ?_ ?_ ?_
      · rw [mem_placed, add_sub_cancel_left]
        conn_odo
        exact hP.c0
      · rw [mem_placed, show (((tileOddPieces S pO pE lE w).get ⟨0, by simp [tileOddPieces]⟩).off + (((0 : ℤ), (0 : ℤ)))) - ((tileOddPieces S pO pE lE w).get ⟨3, by simp [tileOddPieces]⟩).off = vQ1 w by conn_id]
        conn_odo
        exact hQ.cX
      · conn_exc
      · conn_exc
    have a05 : (overlapGraph (goodPart (tileOddPieces S pO pE lE w))).Adj ⟨0, by simp [tileOddPieces]⟩ ⟨5, by simp [tileOddPieces]⟩ := by
      refine adj_of_mem _ _ _ (by simp) (((tileOddPieces S pO pE lE w).get ⟨0, by simp [tileOddPieces]⟩).off + (vP1 w + vP2 w + ((0 : ℤ), (-1 : ℤ)))) ?_ ?_ ?_ ?_
      · rw [mem_placed, add_sub_cancel_left]
        conn_odo
        exact hP.cD1
      · rw [mem_placed, show (((tileOddPieces S pO pE lE w).get ⟨0, by simp [tileOddPieces]⟩).off + (vP1 w + vP2 w + ((0 : ℤ), (-1 : ℤ)))) - ((tileOddPieces S pO pE lE w).get ⟨5, by simp [tileOddPieces]⟩).off = vQ1 w - ((0 : ℤ), (1 : ℤ)) by conn_id]
        conn_odo
        exact hQ.cXi
      · conn_exc
      · conn_exc
    have a23 : (overlapGraph (goodPart (tileOddPieces S pO pE lE w))).Adj ⟨2, by simp [tileOddPieces]⟩ ⟨3, by simp [tileOddPieces]⟩ := by
      refine adj_of_mem _ _ _ (by simp) (((tileOddPieces S pO pE lE w).get ⟨2, by simp [tileOddPieces]⟩).off + (vQ1 w + vQ2 w + ((1 : ℤ), (-1 : ℤ)))) ?_ ?_ ?_ ?_
      · rw [mem_placed, add_sub_cancel_left]
        conn_odo
        exact hQ.cD
      · rw [mem_placed, show (((tileOddPieces S pO pE lE w).get ⟨2, by simp [tileOddPieces]⟩).off + (vQ1 w + vQ2 w + ((1 : ℤ), (-1 : ℤ)))) - ((tileOddPieces S pO pE lE w).get ⟨3, by simp [tileOddPieces]⟩).off = vQ2 w + ((1 : ℤ), (-1 : ℤ)) by conn_id]
        conn_odo
        exact hQ.cY1i
      · conn_exc
      · conn_exc
    have a45 : (overlapGraph (goodPart (tileOddPieces S pO pE lE w))).Adj ⟨4, by simp [tileOddPieces]⟩ ⟨5, by simp [tileOddPieces]⟩ := by
      refine adj_of_mem _ _ _ (by simp) (((tileOddPieces S pO pE lE w).get ⟨4, by simp [tileOddPieces]⟩).off + (vQ1 w + vQ2 w + ((1 : ℤ), (-1 : ℤ)))) ?_ ?_ ?_ ?_
      · rw [mem_placed, add_sub_cancel_left]
        conn_odo
        exact hQ.cD
      · rw [mem_placed, show (((tileOddPieces S pO pE lE w).get ⟨4, by simp [tileOddPieces]⟩).off + (vQ1 w + vQ2 w + ((1 : ℤ), (-1 : ℤ)))) - ((tileOddPieces S pO pE lE w).get ⟨5, by simp [tileOddPieces]⟩).off = vQ2 w + ((1 : ℤ), (-1 : ℤ)) by conn_id]
        conn_odo
        exact hQ.cY1i
      · conn_exc
      · conn_exc
    have a12 : (overlapGraph (goodPart (tileOddPieces S pO pE lE w))).Adj ⟨1, by simp [tileOddPieces]⟩ ⟨2, by simp [tileOddPieces]⟩ := by
      refine adj_of_mem _ _ _ (by simp) (((tileOddPieces S pO pE lE w).get ⟨1, by simp [tileOddPieces]⟩).off + (((1 : ℤ), (0 : ℤ)))) ?_ ?_ ?_ ?_
      · rw [mem_placed, add_sub_cancel_left]
        conn_odo
        exact hP.c1
      · rw [mem_placed, show (((tileOddPieces S pO pE lE w).get ⟨1, by simp [tileOddPieces]⟩).off + (((1 : ℤ), (0 : ℤ)))) - ((tileOddPieces S pO pE lE w).get ⟨2, by simp [tileOddPieces]⟩).off = vQ2 w + ((1 : ℤ), (0 : ℤ)) by conn_id]
        conn_odo
        exact hQ.cY1
      · conn_exc
      · conn_exc
    obtain ⟨kv, hk⟩ := k
    rcases kv with _ | _ | _ | _ | _ | _ | kv
    · exact SimpleGraph.Reachable.refl _
    · exact (((SimpleGraph.Reachable.refl _).trans (a03).reachable).trans (a23.symm).reachable).trans (a12.symm).reachable
    · exact ((SimpleGraph.Reachable.refl _).trans (a03).reachable).trans (a23.symm).reachable
    · exact (SimpleGraph.Reachable.refl _).trans (a03).reachable
    · exact ((SimpleGraph.Reachable.refl _).trans (a05).reachable).trans (a45.symm).reachable
    · exact (SimpleGraph.Reachable.refl _).trans (a05).reachable
    · simp [tileOddPieces] at hk; omega
  · -- W1Odd = True, corrected = True
    have a02 : (overlapGraph (goodPart (tileOddPieces S pO pE lE w))).Adj ⟨0, by simp [tileOddPieces]⟩ ⟨2, by simp [tileOddPieces]⟩ := by
      refine adj_of_mem _ _ _ (by simp) (((tileOddPieces S pO pE lE w).get ⟨0, by simp [tileOddPieces]⟩).off + (vP1 w)) ?_ ?_ ?_ ?_
      · rw [mem_placed, add_sub_cancel_left]
        conn_odo
        exact hP.cX
      · rw [mem_placed, show (((tileOddPieces S pO pE lE w).get ⟨0, by simp [tileOddPieces]⟩).off + (vP1 w)) - ((tileOddPieces S pO pE lE w).get ⟨2, by simp [tileOddPieces]⟩).off = ((0 : ℤ), (0 : ℤ)) by conn_id]
        conn_odo
        exact (hL hc).1.1
      · conn_exc
      · conn_exc
    have a04 : (overlapGraph (goodPart (tileOddPieces S pO pE lE w))).Adj ⟨0, by simp [tileOddPieces]⟩ ⟨4, by simp [tileOddPieces]⟩ := by
      refine adj_of_mem _ _ _ (by simp) (((tileOddPieces S pO pE lE w).get ⟨0, by simp [tileOddPieces]⟩).off + (vP2 w + ((1 : ℤ), (0 : ℤ)))) ?_ ?_ ?_ ?_
      · rw [mem_placed, add_sub_cancel_left]
        conn_odo
        exact hP.cY1
      · rw [mem_placed, show (((tileOddPieces S pO pE lE w).get ⟨0, by simp [tileOddPieces]⟩).off + (vP2 w + ((1 : ℤ), (0 : ℤ)))) - ((tileOddPieces S pO pE lE w).get ⟨4, by simp [tileOddPieces]⟩).off = ((1 : ℤ), (0 : ℤ)) by conn_id]
        conn_odo
        exact hQ.c1
      · conn_exc
      · conn_exc
    have a23 : (overlapGraph (goodPart (tileOddPieces S pO pE lE w))).Adj ⟨2, by simp [tileOddPieces]⟩ ⟨3, by simp [tileOddPieces]⟩ := by
      refine adj_of_mem _ _ _ (by simp) (((tileOddPieces S pO pE lE w).get ⟨2, by simp [tileOddPieces]⟩).off + (vQ1 w)) ?_ ?_ ?_ ?_
      · rw [mem_placed, add_sub_cancel_left]
        conn_odo
        exact (hL hc).1.2
      · rw [mem_placed, show (((tileOddPieces S pO pE lE w).get ⟨2, by simp [tileOddPieces]⟩).off + (vQ1 w)) - ((tileOddPieces S pO pE lE w).get ⟨3, by simp [tileOddPieces]⟩).off = ((0 : ℤ), (0 : ℤ)) by conn_id]
        conn_odo
        exact hQ.c0
      · conn_exc
      · conn_exc
    have a45 : (overlapGraph (goodPart (tileOddPieces S pO pE lE w))).Adj ⟨4, by simp [tileOddPieces]⟩ ⟨5, by simp [tileOddPieces]⟩ := by
      refine adj_of_mem _ _ _ (by simp) (((tileOddPieces S pO pE lE w).get ⟨4, by simp [tileOddPieces]⟩).off + (vQ1 w + vQ2 w + ((1 : ℤ), (-1 : ℤ)))) ?_ ?_ ?_ ?_
      · rw [mem_placed, add_sub_cancel_left]
        conn_odo
        exact hQ.cD
      · rw [mem_placed, show (((tileOddPieces S pO pE lE w).get ⟨4, by simp [tileOddPieces]⟩).off + (vQ1 w + vQ2 w + ((1 : ℤ), (-1 : ℤ)))) - ((tileOddPieces S pO pE lE w).get ⟨5, by simp [tileOddPieces]⟩).off = vQ2 w + ((1 : ℤ), (-1 : ℤ)) by conn_id]
        conn_odo
        exact (hL hc).2
      · conn_exc
      · conn_exc
    have a13 : (overlapGraph (goodPart (tileOddPieces S pO pE lE w))).Adj ⟨1, by simp [tileOddPieces]⟩ ⟨3, by simp [tileOddPieces]⟩ := by
      refine adj_of_mem _ _ _ (by simp) (((tileOddPieces S pO pE lE w).get ⟨1, by simp [tileOddPieces]⟩).off + (vP1 w - ((0 : ℤ), (1 : ℤ)))) ?_ ?_ ?_ ?_
      · rw [mem_placed, add_sub_cancel_left]
        conn_odo
        exact hP.cXi
      · rw [mem_placed, show (((tileOddPieces S pO pE lE w).get ⟨1, by simp [tileOddPieces]⟩).off + (vP1 w - ((0 : ℤ), (1 : ℤ)))) - ((tileOddPieces S pO pE lE w).get ⟨3, by simp [tileOddPieces]⟩).off = vQ1 w + vQ2 w + ((0 : ℤ), (-1 : ℤ)) by conn_id]
        conn_odo
        exact hQ.cD1
      · conn_exc
      · conn_exc
    obtain ⟨kv, hk⟩ := k
    rcases kv with _ | _ | _ | _ | _ | _ | kv
    · exact SimpleGraph.Reachable.refl _
    · exact (((SimpleGraph.Reachable.refl _).trans (a02).reachable).trans (a23).reachable).trans (a13.symm).reachable
    · exact (SimpleGraph.Reachable.refl _).trans (a02).reachable
    · exact ((SimpleGraph.Reachable.refl _).trans (a02).reachable).trans (a23).reachable
    · exact (SimpleGraph.Reachable.refl _).trans (a04).reachable
    · exact ((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a45).reachable
    · simp [tileOddPieces] at hk; omega
  · -- W1Odd = True, corrected = False
    have a02 : (overlapGraph (goodPart (tileOddPieces S pO pE lE w))).Adj ⟨0, by simp [tileOddPieces]⟩ ⟨2, by simp [tileOddPieces]⟩ := by
      refine adj_of_mem _ _ _ (by simp) (((tileOddPieces S pO pE lE w).get ⟨0, by simp [tileOddPieces]⟩).off + (vP1 w)) ?_ ?_ ?_ ?_
      · rw [mem_placed, add_sub_cancel_left]
        conn_odo
        exact hP.cX
      · rw [mem_placed, show (((tileOddPieces S pO pE lE w).get ⟨0, by simp [tileOddPieces]⟩).off + (vP1 w)) - ((tileOddPieces S pO pE lE w).get ⟨2, by simp [tileOddPieces]⟩).off = ((0 : ℤ), (0 : ℤ)) by conn_id]
        conn_odo
        exact hQ.c0
      · conn_exc
      · conn_exc
    have a04 : (overlapGraph (goodPart (tileOddPieces S pO pE lE w))).Adj ⟨0, by simp [tileOddPieces]⟩ ⟨4, by simp [tileOddPieces]⟩ := by
      refine adj_of_mem _ _ _ (by simp) (((tileOddPieces S pO pE lE w).get ⟨0, by simp [tileOddPieces]⟩).off + (vP2 w + ((1 : ℤ), (0 : ℤ)))) ?_ ?_ ?_ ?_
      · rw [mem_placed, add_sub_cancel_left]
        conn_odo
        exact hP.cY1
      · rw [mem_placed, show (((tileOddPieces S pO pE lE w).get ⟨0, by simp [tileOddPieces]⟩).off + (vP2 w + ((1 : ℤ), (0 : ℤ)))) - ((tileOddPieces S pO pE lE w).get ⟨4, by simp [tileOddPieces]⟩).off = ((1 : ℤ), (0 : ℤ)) by conn_id]
        conn_odo
        exact hQ.c1
      · conn_exc
      · conn_exc
    have a23 : (overlapGraph (goodPart (tileOddPieces S pO pE lE w))).Adj ⟨2, by simp [tileOddPieces]⟩ ⟨3, by simp [tileOddPieces]⟩ := by
      refine adj_of_mem _ _ _ (by simp) (((tileOddPieces S pO pE lE w).get ⟨2, by simp [tileOddPieces]⟩).off + (vQ1 w + vQ2 w + ((1 : ℤ), (-1 : ℤ)))) ?_ ?_ ?_ ?_
      · rw [mem_placed, add_sub_cancel_left]
        conn_odo
        exact hQ.cD
      · rw [mem_placed, show (((tileOddPieces S pO pE lE w).get ⟨2, by simp [tileOddPieces]⟩).off + (vQ1 w + vQ2 w + ((1 : ℤ), (-1 : ℤ)))) - ((tileOddPieces S pO pE lE w).get ⟨3, by simp [tileOddPieces]⟩).off = vQ2 w + ((1 : ℤ), (-1 : ℤ)) by conn_id]
        conn_odo
        exact hQ.cY1i
      · conn_exc
      · conn_exc
    have a45 : (overlapGraph (goodPart (tileOddPieces S pO pE lE w))).Adj ⟨4, by simp [tileOddPieces]⟩ ⟨5, by simp [tileOddPieces]⟩ := by
      refine adj_of_mem _ _ _ (by simp) (((tileOddPieces S pO pE lE w).get ⟨4, by simp [tileOddPieces]⟩).off + (vQ1 w + vQ2 w + ((1 : ℤ), (-1 : ℤ)))) ?_ ?_ ?_ ?_
      · rw [mem_placed, add_sub_cancel_left]
        conn_odo
        exact hQ.cD
      · rw [mem_placed, show (((tileOddPieces S pO pE lE w).get ⟨4, by simp [tileOddPieces]⟩).off + (vQ1 w + vQ2 w + ((1 : ℤ), (-1 : ℤ)))) - ((tileOddPieces S pO pE lE w).get ⟨5, by simp [tileOddPieces]⟩).off = vQ2 w + ((1 : ℤ), (-1 : ℤ)) by conn_id]
        conn_odo
        exact hQ.cY1i
      · conn_exc
      · conn_exc
    have a13 : (overlapGraph (goodPart (tileOddPieces S pO pE lE w))).Adj ⟨1, by simp [tileOddPieces]⟩ ⟨3, by simp [tileOddPieces]⟩ := by
      refine adj_of_mem _ _ _ (by simp) (((tileOddPieces S pO pE lE w).get ⟨1, by simp [tileOddPieces]⟩).off + (vP1 w - ((0 : ℤ), (1 : ℤ)))) ?_ ?_ ?_ ?_
      · rw [mem_placed, add_sub_cancel_left]
        conn_odo
        exact hP.cXi
      · rw [mem_placed, show (((tileOddPieces S pO pE lE w).get ⟨1, by simp [tileOddPieces]⟩).off + (vP1 w - ((0 : ℤ), (1 : ℤ)))) - ((tileOddPieces S pO pE lE w).get ⟨3, by simp [tileOddPieces]⟩).off = vQ1 w + vQ2 w + ((0 : ℤ), (-1 : ℤ)) by conn_id]
        conn_odo
        exact hQ.cD1
      · conn_exc
      · conn_exc
    obtain ⟨kv, hk⟩ := k
    rcases kv with _ | _ | _ | _ | _ | _ | kv
    · exact SimpleGraph.Reachable.refl _
    · exact (((SimpleGraph.Reachable.refl _).trans (a02).reachable).trans (a23).reachable).trans (a13.symm).reachable
    · exact (SimpleGraph.Reachable.refl _).trans (a02).reachable
    · exact ((SimpleGraph.Reachable.refl _).trans (a02).reachable).trans (a23).reachable
    · exact (SimpleGraph.Reachable.refl _).trans (a04).reachable
    · exact ((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a45).reachable
    · simp [tileOddPieces] at hk; omega

/-- The overlap graph of the even standard decomposition is connected: a spanning tree of overlaps witnessed by corner points of
the parents (`StdCorners`) and, for the L-corrected copies, by points of the kept side of the child of the parent word. -/
theorem tileEvenPieces_connected (S : WeakData) (pO pE : Word → PartialOdometer) (lO : Word → Bool → Bool → PartialOdometer)
    (w : Word)
    (hP : StdCorners (regOdo S pO pE (regsAt w).1 true) (vP1 w) (vP2 w))
    (hQ : StdCorners (regOdo S pO pE (regsAt w).2 false) (vQ1 w) (vQ2 w))
    (hL : w.getLast? = some Digit.two → ∀ plus : Bool,
      (((plus == W1Odd w) = false) → ((1 : ℤ), (0 : ℤ)) ∈ (lO w.dropLast plus false).dom ∧
        vP2 w + ((1 : ℤ), (0 : ℤ)) ∈ (lO w.dropLast plus false).dom) ∧
      (((plus == W1Odd w) = true) → vP1 w - ((0 : ℤ), (1 : ℤ)) ∈ (lO w.dropLast plus false).dom)) :
    (overlapGraph (goodPart (tileEvenPieces S pO pE lO w))).Connected := by
  have h0 : 0 < (tileEvenPieces S pO pE lO w).length := by simp [tileEvenPieces]
  refine connected_of_reach _ h0 (fun k => ?_)
  cases hWo : W1Odd w <;> by_cases hc : w.getLast? = some Digit.two
  · -- W1Odd = False, corrected = True
    have a04 : (overlapGraph (goodPart (tileEvenPieces S pO pE lO w))).Adj ⟨0, by simp [tileEvenPieces]⟩ ⟨4, by simp [tileEvenPieces]⟩ := by
      refine adj_of_mem _ _ _ (by simp) (((tileEvenPieces S pO pE lO w).get ⟨0, by simp [tileEvenPieces]⟩).off + (((0 : ℤ), (0 : ℤ)))) ?_ ?_ ?_ ?_
      · rw [mem_placed, add_sub_cancel_left]
        conn_odo
        exact hP.c0
      · rw [mem_placed, show (((tileEvenPieces S pO pE lO w).get ⟨0, by simp [tileEvenPieces]⟩).off + (((0 : ℤ), (0 : ℤ)))) - ((tileEvenPieces S pO pE lO w).get ⟨4, by simp [tileEvenPieces]⟩).off = vQ1 w by conn_id]
        conn_odo
        exact hQ.cX
      · conn_exc
      · conn_exc
    have a01 : (overlapGraph (goodPart (tileEvenPieces S pO pE lO w))).Adj ⟨0, by simp [tileEvenPieces]⟩ ⟨1, by simp [tileEvenPieces]⟩ := by
      refine adj_of_mem _ _ _ (by simp) (((tileEvenPieces S pO pE lO w).get ⟨0, by simp [tileEvenPieces]⟩).off + (vP1 w + vP2 w + ((0 : ℤ), (-1 : ℤ)))) ?_ ?_ ?_ ?_
      · rw [mem_placed, add_sub_cancel_left]
        conn_odo
        exact hP.cD1
      · rw [mem_placed, show (((tileEvenPieces S pO pE lO w).get ⟨0, by simp [tileEvenPieces]⟩).off + (vP1 w + vP2 w + ((0 : ℤ), (-1 : ℤ)))) - ((tileEvenPieces S pO pE lO w).get ⟨1, by simp [tileEvenPieces]⟩).off = vP1 w - ((0 : ℤ), (1 : ℤ)) by conn_id]
        conn_odo
        exact ((hL hc false).2 (by simp [hWo]))
      · conn_exc
      · conn_exc
    have a24 : (overlapGraph (goodPart (tileEvenPieces S pO pE lO w))).Adj ⟨2, by simp [tileEvenPieces]⟩ ⟨4, by simp [tileEvenPieces]⟩ := by
      refine adj_of_mem _ _ _ (by simp) (((tileEvenPieces S pO pE lO w).get ⟨2, by simp [tileEvenPieces]⟩).off + (((1 : ℤ), (0 : ℤ)))) ?_ ?_ ?_ ?_
      · rw [mem_placed, add_sub_cancel_left]
        conn_odo
        exact (((hL hc true).1 (by simp [hWo])).1)
      · rw [mem_placed, show (((tileEvenPieces S pO pE lO w).get ⟨2, by simp [tileEvenPieces]⟩).off + (((1 : ℤ), (0 : ℤ)))) - ((tileEvenPieces S pO pE lO w).get ⟨4, by simp [tileEvenPieces]⟩).off = vQ2 w + ((1 : ℤ), (0 : ℤ)) by conn_id]
        conn_odo
        exact hQ.cY1
      · conn_exc
      · conn_exc
    have a23 : (overlapGraph (goodPart (tileEvenPieces S pO pE lO w))).Adj ⟨2, by simp [tileEvenPieces]⟩ ⟨3, by simp [tileEvenPieces]⟩ := by
      refine adj_of_mem _ _ _ (by simp) (((tileEvenPieces S pO pE lO w).get ⟨2, by simp [tileEvenPieces]⟩).off + (vP2 w + ((1 : ℤ), (0 : ℤ)))) ?_ ?_ ?_ ?_
      · rw [mem_placed, add_sub_cancel_left]
        conn_odo
        exact (((hL hc true).1 (by simp [hWo])).2)
      · rw [mem_placed, show (((tileEvenPieces S pO pE lO w).get ⟨2, by simp [tileEvenPieces]⟩).off + (vP2 w + ((1 : ℤ), (0 : ℤ)))) - ((tileEvenPieces S pO pE lO w).get ⟨3, by simp [tileEvenPieces]⟩).off = ((1 : ℤ), (0 : ℤ)) by conn_id]
        conn_odo
        exact hP.c1
      · conn_exc
      · conn_exc
    have a35 : (overlapGraph (goodPart (tileEvenPieces S pO pE lO w))).Adj ⟨3, by simp [tileEvenPieces]⟩ ⟨5, by simp [tileEvenPieces]⟩ := by
      refine adj_of_mem _ _ _ (by simp) (((tileEvenPieces S pO pE lO w).get ⟨3, by simp [tileEvenPieces]⟩).off + (vP1 w + vP2 w + ((1 : ℤ), (-1 : ℤ)))) ?_ ?_ ?_ ?_
      · rw [mem_placed, add_sub_cancel_left]
        conn_odo
        exact hP.cD
      · rw [mem_placed, show (((tileEvenPieces S pO pE lO w).get ⟨3, by simp [tileEvenPieces]⟩).off + (vP1 w + vP2 w + ((1 : ℤ), (-1 : ℤ)))) - ((tileEvenPieces S pO pE lO w).get ⟨5, by simp [tileEvenPieces]⟩).off = vQ2 w + ((1 : ℤ), (-1 : ℤ)) by conn_id]
        conn_odo
        exact hQ.cY1i
      · conn_exc
      · conn_exc
    obtain ⟨kv, hk⟩ := k
    rcases kv with _ | _ | _ | _ | _ | _ | kv
    · exact SimpleGraph.Reachable.refl _
    · exact (SimpleGraph.Reachable.refl _).trans (a01).reachable
    · exact ((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a24.symm).reachable
    · exact (((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a24.symm).reachable).trans (a23).reachable
    · exact (SimpleGraph.Reachable.refl _).trans (a04).reachable
    · exact ((((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a24.symm).reachable).trans (a23).reachable).trans (a35).reachable
    · simp [tileEvenPieces] at hk; omega
  · -- W1Odd = False, corrected = False
    have a04 : (overlapGraph (goodPart (tileEvenPieces S pO pE lO w))).Adj ⟨0, by simp [tileEvenPieces]⟩ ⟨4, by simp [tileEvenPieces]⟩ := by
      refine adj_of_mem _ _ _ (by simp) (((tileEvenPieces S pO pE lO w).get ⟨0, by simp [tileEvenPieces]⟩).off + (((0 : ℤ), (0 : ℤ)))) ?_ ?_ ?_ ?_
      · rw [mem_placed, add_sub_cancel_left]
        conn_odo
        exact hP.c0
      · rw [mem_placed, show (((tileEvenPieces S pO pE lO w).get ⟨0, by simp [tileEvenPieces]⟩).off + (((0 : ℤ), (0 : ℤ)))) - ((tileEvenPieces S pO pE lO w).get ⟨4, by simp [tileEvenPieces]⟩).off = vQ1 w by conn_id]
        conn_odo
        exact hQ.cX
      · conn_exc
      · conn_exc
    have a01 : (overlapGraph (goodPart (tileEvenPieces S pO pE lO w))).Adj ⟨0, by simp [tileEvenPieces]⟩ ⟨1, by simp [tileEvenPieces]⟩ := by
      refine adj_of_mem _ _ _ (by simp) (((tileEvenPieces S pO pE lO w).get ⟨0, by simp [tileEvenPieces]⟩).off + (vP1 w + vP2 w + ((0 : ℤ), (-1 : ℤ)))) ?_ ?_ ?_ ?_
      · rw [mem_placed, add_sub_cancel_left]
        conn_odo
        exact hP.cD1
      · rw [mem_placed, show (((tileEvenPieces S pO pE lO w).get ⟨0, by simp [tileEvenPieces]⟩).off + (vP1 w + vP2 w + ((0 : ℤ), (-1 : ℤ)))) - ((tileEvenPieces S pO pE lO w).get ⟨1, by simp [tileEvenPieces]⟩).off = vP1 w - ((0 : ℤ), (1 : ℤ)) by conn_id]
        conn_odo
        exact hP.cXi
      · conn_exc
      · conn_exc
    have a15 : (overlapGraph (goodPart (tileEvenPieces S pO pE lO w))).Adj ⟨1, by simp [tileEvenPieces]⟩ ⟨5, by simp [tileEvenPieces]⟩ := by
      refine adj_of_mem _ _ _ (by simp) (((tileEvenPieces S pO pE lO w).get ⟨1, by simp [tileEvenPieces]⟩).off + (vP1 w + vP2 w + ((0 : ℤ), (-1 : ℤ)))) ?_ ?_ ?_ ?_
      · rw [mem_placed, add_sub_cancel_left]
        conn_odo
        exact hP.cD1
      · rw [mem_placed, show (((tileEvenPieces S pO pE lO w).get ⟨1, by simp [tileEvenPieces]⟩).off + (vP1 w + vP2 w + ((0 : ℤ), (-1 : ℤ)))) - ((tileEvenPieces S pO pE lO w).get ⟨5, by simp [tileEvenPieces]⟩).off = vQ1 w - ((0 : ℤ), (1 : ℤ)) by conn_id]
        conn_odo
        exact hQ.cXi
      · conn_exc
      · conn_exc
    have a24 : (overlapGraph (goodPart (tileEvenPieces S pO pE lO w))).Adj ⟨2, by simp [tileEvenPieces]⟩ ⟨4, by simp [tileEvenPieces]⟩ := by
      refine adj_of_mem _ _ _ (by simp) (((tileEvenPieces S pO pE lO w).get ⟨2, by simp [tileEvenPieces]⟩).off + (((1 : ℤ), (0 : ℤ)))) ?_ ?_ ?_ ?_
      · rw [mem_placed, add_sub_cancel_left]
        conn_odo
        exact hP.c1
      · rw [mem_placed, show (((tileEvenPieces S pO pE lO w).get ⟨2, by simp [tileEvenPieces]⟩).off + (((1 : ℤ), (0 : ℤ)))) - ((tileEvenPieces S pO pE lO w).get ⟨4, by simp [tileEvenPieces]⟩).off = vQ2 w + ((1 : ℤ), (0 : ℤ)) by conn_id]
        conn_odo
        exact hQ.cY1
      · conn_exc
      · conn_exc
    have a23 : (overlapGraph (goodPart (tileEvenPieces S pO pE lO w))).Adj ⟨2, by simp [tileEvenPieces]⟩ ⟨3, by simp [tileEvenPieces]⟩ := by
      refine adj_of_mem _ _ _ (by simp) (((tileEvenPieces S pO pE lO w).get ⟨2, by simp [tileEvenPieces]⟩).off + (vP1 w + vP2 w + ((0 : ℤ), (-1 : ℤ)))) ?_ ?_ ?_ ?_
      · rw [mem_placed, add_sub_cancel_left]
        conn_odo
        exact hP.cD1
      · rw [mem_placed, show (((tileEvenPieces S pO pE lO w).get ⟨2, by simp [tileEvenPieces]⟩).off + (vP1 w + vP2 w + ((0 : ℤ), (-1 : ℤ)))) - ((tileEvenPieces S pO pE lO w).get ⟨3, by simp [tileEvenPieces]⟩).off = vP1 w - ((0 : ℤ), (1 : ℤ)) by conn_id]
        conn_odo
        exact hP.cXi
      · conn_exc
      · conn_exc
    obtain ⟨kv, hk⟩ := k
    rcases kv with _ | _ | _ | _ | _ | _ | kv
    · exact SimpleGraph.Reachable.refl _
    · exact (SimpleGraph.Reachable.refl _).trans (a01).reachable
    · exact ((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a24.symm).reachable
    · exact (((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a24.symm).reachable).trans (a23).reachable
    · exact (SimpleGraph.Reachable.refl _).trans (a04).reachable
    · exact ((SimpleGraph.Reachable.refl _).trans (a01).reachable).trans (a15).reachable
    · simp [tileEvenPieces] at hk; omega
  · -- W1Odd = True, corrected = True
    have a04 : (overlapGraph (goodPart (tileEvenPieces S pO pE lO w))).Adj ⟨0, by simp [tileEvenPieces]⟩ ⟨4, by simp [tileEvenPieces]⟩ := by
      refine adj_of_mem _ _ _ (by simp) (((tileEvenPieces S pO pE lO w).get ⟨0, by simp [tileEvenPieces]⟩).off + (vP1 w)) ?_ ?_ ?_ ?_
      · rw [mem_placed, add_sub_cancel_left]
        conn_odo
        exact hP.cX
      · rw [mem_placed, show (((tileEvenPieces S pO pE lO w).get ⟨0, by simp [tileEvenPieces]⟩).off + (vP1 w)) - ((tileEvenPieces S pO pE lO w).get ⟨4, by simp [tileEvenPieces]⟩).off = ((0 : ℤ), (0 : ℤ)) by conn_id]
        conn_odo
        exact hQ.c0
      · conn_exc
      · conn_exc
    have a01 : (overlapGraph (goodPart (tileEvenPieces S pO pE lO w))).Adj ⟨0, by simp [tileEvenPieces]⟩ ⟨1, by simp [tileEvenPieces]⟩ := by
      refine adj_of_mem _ _ _ (by simp) (((tileEvenPieces S pO pE lO w).get ⟨0, by simp [tileEvenPieces]⟩).off + (vP2 w + ((1 : ℤ), (0 : ℤ)))) ?_ ?_ ?_ ?_
      · rw [mem_placed, add_sub_cancel_left]
        conn_odo
        exact hP.cY1
      · rw [mem_placed, show (((tileEvenPieces S pO pE lO w).get ⟨0, by simp [tileEvenPieces]⟩).off + (vP2 w + ((1 : ℤ), (0 : ℤ)))) - ((tileEvenPieces S pO pE lO w).get ⟨1, by simp [tileEvenPieces]⟩).off = ((1 : ℤ), (0 : ℤ)) by conn_id]
        conn_odo
        exact (((hL hc false).1 (by simp [hWo])).1)
      · conn_exc
      · conn_exc
    have a15 : (overlapGraph (goodPart (tileEvenPieces S pO pE lO w))).Adj ⟨1, by simp [tileEvenPieces]⟩ ⟨5, by simp [tileEvenPieces]⟩ := by
      refine adj_of_mem _ _ _ (by simp) (((tileEvenPieces S pO pE lO w).get ⟨1, by simp [tileEvenPieces]⟩).off + (vP2 w + ((1 : ℤ), (0 : ℤ)))) ?_ ?_ ?_ ?_
      · rw [mem_placed, add_sub_cancel_left]
        conn_odo
        exact (((hL hc false).1 (by simp [hWo])).2)
      · rw [mem_placed, show (((tileEvenPieces S pO pE lO w).get ⟨1, by simp [tileEvenPieces]⟩).off + (vP2 w + ((1 : ℤ), (0 : ℤ)))) - ((tileEvenPieces S pO pE lO w).get ⟨5, by simp [tileEvenPieces]⟩).off = ((1 : ℤ), (0 : ℤ)) by conn_id]
        conn_odo
        exact hQ.c1
      · conn_exc
      · conn_exc
    have a24 : (overlapGraph (goodPart (tileEvenPieces S pO pE lO w))).Adj ⟨2, by simp [tileEvenPieces]⟩ ⟨4, by simp [tileEvenPieces]⟩ := by
      refine adj_of_mem _ _ _ (by simp) (((tileEvenPieces S pO pE lO w).get ⟨2, by simp [tileEvenPieces]⟩).off + (vP1 w - ((0 : ℤ), (1 : ℤ)))) ?_ ?_ ?_ ?_
      · rw [mem_placed, add_sub_cancel_left]
        conn_odo
        exact ((hL hc true).2 (by simp [hWo]))
      · rw [mem_placed, show (((tileEvenPieces S pO pE lO w).get ⟨2, by simp [tileEvenPieces]⟩).off + (vP1 w - ((0 : ℤ), (1 : ℤ)))) - ((tileEvenPieces S pO pE lO w).get ⟨4, by simp [tileEvenPieces]⟩).off = vQ1 w + vQ2 w + ((0 : ℤ), (-1 : ℤ)) by conn_id]
        conn_odo
        exact hQ.cD1
      · conn_exc
      · conn_exc
    have a35 : (overlapGraph (goodPart (tileEvenPieces S pO pE lO w))).Adj ⟨3, by simp [tileEvenPieces]⟩ ⟨5, by simp [tileEvenPieces]⟩ := by
      refine adj_of_mem _ _ _ (by simp) (((tileEvenPieces S pO pE lO w).get ⟨3, by simp [tileEvenPieces]⟩).off + (vP2 w + ((1 : ℤ), (-1 : ℤ)))) ?_ ?_ ?_ ?_
      · rw [mem_placed, add_sub_cancel_left]
        conn_odo
        exact hP.cY1i
      · rw [mem_placed, show (((tileEvenPieces S pO pE lO w).get ⟨3, by simp [tileEvenPieces]⟩).off + (vP2 w + ((1 : ℤ), (-1 : ℤ)))) - ((tileEvenPieces S pO pE lO w).get ⟨5, by simp [tileEvenPieces]⟩).off = vQ1 w + vQ2 w + ((1 : ℤ), (-1 : ℤ)) by conn_id]
        conn_odo
        exact hQ.cD
      · conn_exc
      · conn_exc
    obtain ⟨kv, hk⟩ := k
    rcases kv with _ | _ | _ | _ | _ | _ | kv
    · exact SimpleGraph.Reachable.refl _
    · exact (SimpleGraph.Reachable.refl _).trans (a01).reachable
    · exact ((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a24.symm).reachable
    · exact (((SimpleGraph.Reachable.refl _).trans (a01).reachable).trans (a15).reachable).trans (a35.symm).reachable
    · exact (SimpleGraph.Reachable.refl _).trans (a04).reachable
    · exact ((SimpleGraph.Reachable.refl _).trans (a01).reachable).trans (a15).reachable
    · simp [tileEvenPieces] at hk; omega
  · -- W1Odd = True, corrected = False
    have a01 : (overlapGraph (goodPart (tileEvenPieces S pO pE lO w))).Adj ⟨0, by simp [tileEvenPieces]⟩ ⟨1, by simp [tileEvenPieces]⟩ := by
      refine adj_of_mem _ _ _ (by simp) (((tileEvenPieces S pO pE lO w).get ⟨0, by simp [tileEvenPieces]⟩).off + (vP1 w + vP2 w + ((0 : ℤ), (-1 : ℤ)))) ?_ ?_ ?_ ?_
      · rw [mem_placed, add_sub_cancel_left]
        conn_odo
        exact hP.cD1
      · rw [mem_placed, show (((tileEvenPieces S pO pE lO w).get ⟨0, by simp [tileEvenPieces]⟩).off + (vP1 w + vP2 w + ((0 : ℤ), (-1 : ℤ)))) - ((tileEvenPieces S pO pE lO w).get ⟨1, by simp [tileEvenPieces]⟩).off = vP1 w - ((0 : ℤ), (1 : ℤ)) by conn_id]
        conn_odo
        exact hP.cXi
      · conn_exc
      · conn_exc
    have a04 : (overlapGraph (goodPart (tileEvenPieces S pO pE lO w))).Adj ⟨0, by simp [tileEvenPieces]⟩ ⟨4, by simp [tileEvenPieces]⟩ := by
      refine adj_of_mem _ _ _ (by simp) (((tileEvenPieces S pO pE lO w).get ⟨0, by simp [tileEvenPieces]⟩).off + (vP1 w)) ?_ ?_ ?_ ?_
      · rw [mem_placed, add_sub_cancel_left]
        conn_odo
        exact hP.cX
      · rw [mem_placed, show (((tileEvenPieces S pO pE lO w).get ⟨0, by simp [tileEvenPieces]⟩).off + (vP1 w)) - ((tileEvenPieces S pO pE lO w).get ⟨4, by simp [tileEvenPieces]⟩).off = ((0 : ℤ), (0 : ℤ)) by conn_id]
        conn_odo
        exact hQ.c0
      · conn_exc
      · conn_exc
    have a15 : (overlapGraph (goodPart (tileEvenPieces S pO pE lO w))).Adj ⟨1, by simp [tileEvenPieces]⟩ ⟨5, by simp [tileEvenPieces]⟩ := by
      refine adj_of_mem _ _ _ (by simp) (((tileEvenPieces S pO pE lO w).get ⟨1, by simp [tileEvenPieces]⟩).off + (vP2 w + ((1 : ℤ), (0 : ℤ)))) ?_ ?_ ?_ ?_
      · rw [mem_placed, add_sub_cancel_left]
        conn_odo
        exact hP.cY1
      · rw [mem_placed, show (((tileEvenPieces S pO pE lO w).get ⟨1, by simp [tileEvenPieces]⟩).off + (vP2 w + ((1 : ℤ), (0 : ℤ)))) - ((tileEvenPieces S pO pE lO w).get ⟨5, by simp [tileEvenPieces]⟩).off = ((1 : ℤ), (0 : ℤ)) by conn_id]
        conn_odo
        exact hQ.c1
      · conn_exc
      · conn_exc
    have a24 : (overlapGraph (goodPart (tileEvenPieces S pO pE lO w))).Adj ⟨2, by simp [tileEvenPieces]⟩ ⟨4, by simp [tileEvenPieces]⟩ := by
      refine adj_of_mem _ _ _ (by simp) (((tileEvenPieces S pO pE lO w).get ⟨2, by simp [tileEvenPieces]⟩).off + (vP1 w - ((0 : ℤ), (1 : ℤ)))) ?_ ?_ ?_ ?_
      · rw [mem_placed, add_sub_cancel_left]
        conn_odo
        exact hP.cXi
      · rw [mem_placed, show (((tileEvenPieces S pO pE lO w).get ⟨2, by simp [tileEvenPieces]⟩).off + (vP1 w - ((0 : ℤ), (1 : ℤ)))) - ((tileEvenPieces S pO pE lO w).get ⟨4, by simp [tileEvenPieces]⟩).off = vQ1 w + vQ2 w + ((0 : ℤ), (-1 : ℤ)) by conn_id]
        conn_odo
        exact hQ.cD1
      · conn_exc
      · conn_exc
    have a23 : (overlapGraph (goodPart (tileEvenPieces S pO pE lO w))).Adj ⟨2, by simp [tileEvenPieces]⟩ ⟨3, by simp [tileEvenPieces]⟩ := by
      refine adj_of_mem _ _ _ (by simp) (((tileEvenPieces S pO pE lO w).get ⟨2, by simp [tileEvenPieces]⟩).off + (vP2 w + ((1 : ℤ), (0 : ℤ)))) ?_ ?_ ?_ ?_
      · rw [mem_placed, add_sub_cancel_left]
        conn_odo
        exact hP.cY1
      · rw [mem_placed, show (((tileEvenPieces S pO pE lO w).get ⟨2, by simp [tileEvenPieces]⟩).off + (vP2 w + ((1 : ℤ), (0 : ℤ)))) - ((tileEvenPieces S pO pE lO w).get ⟨3, by simp [tileEvenPieces]⟩).off = ((1 : ℤ), (0 : ℤ)) by conn_id]
        conn_odo
        exact hP.c1
      · conn_exc
      · conn_exc
    obtain ⟨kv, hk⟩ := k
    rcases kv with _ | _ | _ | _ | _ | _ | kv
    · exact SimpleGraph.Reachable.refl _
    · exact (SimpleGraph.Reachable.refl _).trans (a01).reachable
    · exact ((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a24.symm).reachable
    · exact (((SimpleGraph.Reachable.refl _).trans (a04).reachable).trans (a24.symm).reachable).trans (a23).reachable
    · exact (SimpleGraph.Reachable.refl _).trans (a04).reachable
    · exact ((SimpleGraph.Reachable.refl _).trans (a01).reachable).trans (a15).reachable
    · simp [tileEvenPieces] at hk; omega

/-! ### The corner points from the family -/

open FLatticePaper.Tiles.SiteStrings (hWordOf vWordOf)
open FLatticePaper.Tiles.StandardClause (fracOdd fracEven)

theorem stdCorners_of_values (o : PartialOdometer) (α : Site) (β : ℤ) (X Y e : Site)
    (h : TileTranslation.StdCornerValues o α β X Y e) : StdCorners o X Y := by
  obtain ⟨⟨h0, -⟩, ⟨h1, -⟩, ⟨hXi, -⟩, ⟨hX, -⟩, ⟨hY1, -⟩, ⟨hY1i, -⟩, ⟨hD, -⟩, ⟨hD1, -⟩⟩ := h
  refine ⟨h0, h1, hXi, hX, hY1, hY1i, hD, ?_⟩
  have e : X + Y + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ)) = X + Y + ((0 : ℤ), (-1 : ℤ)) := by
    refine Prod.ext ?_ ?_ <;> simp
  rw [← e]
  exact hD1

theorem mem_placedSites_of {ts : List (ZTile × GInt)} {t : ZTile × GInt} (ht : t ∈ ts) {u : GInt}
    (hu : u ∈ tileShape t.1) : t.2 + u ∈ placedSites ts := by
  unfold placedSites
  simp only [List.mem_flatMap, List.mem_map]
  exact ⟨t, ht, u, hu, add_comm u t.2⟩

theorem shape_00 (t : ZTile) : ((0 : ℤ), (0 : ℤ)) ∈ tileShape t := by cases t <;> simp [tileShape]
theorem shape_10 (t : ZTile) : ((1 : ℤ), (0 : ℤ)) ∈ tileShape t := by cases t <;> simp [tileShape]
theorem shape_01 (t : ZTile) : ((0 : ℤ), (1 : ℤ)) ∈ tileShape t := by cases t <;> simp [tileShape]

theorem last_mem_lastPos (L : List (ZTile × GInt)) (t : ZTile) (ht : L.getLast?.map (·.1) = some t) :
    (t, lastPosOf L) ∈ L := by
  cases he : L.getLast? with
  | none => rw [he] at ht; simp at ht
  | some e =>
    rw [he] at ht
    simp only [Option.map_some, Option.some.injEq] at ht
    have hl : lastPosOf L = e.2 := by unfold lastPosOf; rw [he]; rfl
    rw [hl, ← ht]
    exact List.mem_of_getLast? he

/-- The forward horizontal string contains `0` (first tile) and `X` (last tile `T_{0/1}` at `X - 1 - i`). -/
theorem side_hPlus (wh : BinaryWord) (X : GInt) (hhh : wh.head? = some Letter.q) (hhl : wh.getLast? = some Letter.p)
    (hX : lastPosOf (hStringAt wh 0) = X - (1, 1)) :
    ((0 : ℤ), (0 : ℤ)) ∈ placedSites (hStringAt wh 0) ∧ X ∈ placedSites (hStringAt wh 0) := by
  obtain ⟨rest, rfl⟩ : ∃ rest, wh = Letter.q :: rest := by
    cases wh with
    | nil => simp at hhh
    | cons a rest => simp only [List.head?_cons, Option.some.injEq] at hhh; exact ⟨rest, by rw [hhh]⟩
  refine ⟨?_, ?_⟩
  · have hm : (HorizontalStepOne.tileFor none Letter.q, (0 : GInt)) ∈ hStringAt (Letter.q :: rest) 0 := by
      rw [HorizontalStepOne.hStringAt_eq]
      cases rest <;> simp [HorizontalStepOne.hAuxG]
    have := mem_placedSites_of hm (shape_00 _)
    simpa using this
  · have hlast := HorizontalStepOne.hAuxG_last_fst HorizontalStepOne.fwdStr none (Letter.q :: rest) 0 hhl
    rw [← HorizontalStepOne.hStringAt_eq] at hlast
    have hm := last_mem_lastPos _ _ hlast
    rw [hX] at hm
    have := mem_placedSites_of hm (u := ((1 : ℤ), (1 : ℤ))) (by simp [tileShape])
    simpa using this

/-- The reversed horizontal string at `c` contains `c + i` (first tile). -/
theorem side_hMinus (u : BinaryWord) (hne : u ≠ []) (c : GInt) :
    c + ((0 : ℤ), (1 : ℤ)) ∈ placedSites (hRevStringAt u c) := by
  obtain ⟨a, rest, rfl⟩ : ∃ a rest, u = a :: rest := by
    cases u with
    | nil => exact absurd rfl hne
    | cons a rest => exact ⟨a, rest, rfl⟩
  have hm : (HorizontalStepOne.tileFor none a, c) ∈ hRevStringAt (a :: rest) c := by
    rw [HorizontalStepOne.hRevStringAt_eq]
    cases rest <;> simp [HorizontalStepOne.hAuxG]
  exact mem_placedSites_of hm (shape_01 _)

/-- The reversed vertical string at `0` contains `1` (first tile) and `Y + 1` (last tile `T_{0/1}` at `Y + 1 - 2i`). -/
theorem side_vMinus (wv : BinaryWord) (Y : GInt) (hvh : wv.head? = some Letter.p) (hvl : wv.getLast? = some Letter.q)
    (hY : lastPosOf (vRevStringAt wv.reverse 0) = Y + (1, -2)) :
    ((1 : ℤ), (0 : ℤ)) ∈ placedSites (vRevStringAt wv.reverse 0) ∧
      Y + ((1 : ℤ), (0 : ℤ)) ∈ placedSites (vRevStringAt wv.reverse 0) := by
  have hne : wv.reverse ≠ [] := by intro h; rw [List.reverse_eq_nil_iff] at h; subst h; simp at hvh
  obtain ⟨a, rest, hr⟩ : ∃ a rest, wv.reverse = a :: rest := by
    cases h : wv.reverse with
    | nil => exact absurd h hne
    | cons a rest => exact ⟨a, rest, rfl⟩
  refine ⟨?_, ?_⟩
  · have hm : (letterZTile a, (0 : GInt)) ∈ vRevStringAt wv.reverse 0 := by
      rw [hr, VerticalStepOne.vRevStringAt_eq]
      cases rest <;> simp [VerticalStepOne.vAux]
    have := mem_placedSites_of hm (shape_10 _)
    simpa using this
  · have hlast := CornerValues.vAux_last_fst true wv.reverse 0
    rw [← VerticalStepOne.vRevStringAt_eq, List.getLast?_reverse, hvh] at hlast
    have hm := last_mem_lastPos _ _ hlast
    rw [hY] at hm
    have := mem_placedSites_of hm (u := ((0 : ℤ), (2 : ℤ))) (by simp [letterZTile, tileShape])
    have e : Y + ((1 : ℤ), (-2 : ℤ)) + ((0 : ℤ), (2 : ℤ)) = Y + ((1 : ℤ), (0 : ℤ)) := by
      refine Prod.ext ?_ ?_ <;> simp
    rw [e] at this
    exact this

/-- The forward vertical string at `c` contains `c + 1` (first tile). -/
theorem side_vPlus (wv : BinaryWord) (hne : wv ≠ []) (c : GInt) :
    c + ((1 : ℤ), (0 : ℤ)) ∈ placedSites (vStringAt wv c) := by
  obtain ⟨a, rest, rfl⟩ : ∃ a rest, wv = a :: rest := by
    cases wv with
    | nil => exact absurd rfl hne
    | cons a rest => exact ⟨a, rest, rfl⟩
  have hm : (letterZTile a, c) ∈ vStringAt (a :: rest) c := by
    rw [VerticalStepOne.vStringAt_eq]
    cases rest <;> simp [VerticalStepOne.vAux]
  exact mem_placedSites_of hm (shape_10 _)

theorem beq_comm_bool (a b : Bool) : (a == b) = (b == a) := by cases a <;> cases b <;> rfl

/-- The standard tile odometer of a register word has the eight corner points of its fraction in its domain. -/
theorem stdCorners_reg (D : JointData) (f : Word → JSlice) (w : Word) (hb : ¬ IsBase w)
    (hJ : ∀ u : Word, u.length < w.length → IsJointSlice D f u) :
    StdCorners (regOdo D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven) (regsAt w).1 true) (vP1 w) (vP2 w) ∧
    StdCorners (regOdo D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven) (regsAt w).2 false) (vQ1 w) (vQ2 w) := by
  obtain ⟨⟨u1, h1⟩, ⟨u2, h2⟩⟩ := regs_some w hb
  have l1 := FLatticePaper.Tiles.JointInduction.regsAt_lt w u1 (Or.inl h1)
  have l2 := FLatticePaper.Tiles.JointInduction.regsAt_lt w u2 (Or.inr h2)
  obtain ⟨pr1, pr2⟩ := parents_of_regs w
  refine ⟨?_, ?_⟩
  · rw [h1]
    show StdCorners (below f w u1).tOdd _ _
    rw [below_of_lt f w u1 l1]
    obtain ⟨α, β, -, hV⟩ := TileTranslationStd.stdCorners_odd u1 (f u1).tOdd (hJ u1 l1).2.2.1.2.2.2.2.1
    have h := stdCorners_of_values _ _ _ _ _ _ hV
    rw [pr1 u1 h1] at h
    exact h
  · rw [h2]
    show StdCorners (below f w u2).tEven _ _
    rw [below_of_lt f w u2 l2]
    obtain ⟨α, β, -, hV⟩ := TileTranslationStd.stdCorners_even u2 (f u2).tEven (hJ u2 l2).2.2.1.2.2.2.2.2.1
    have h := stdCorners_of_values _ _ _ _ _ _ hV
    rw [pr2 u2 h2] at h
    exact h

/-- The kept sides of the short even L-corrections of the even parent (after a `3`): `0` and `X` on `h+`, `Y + 1 - i` on `h-`. -/
theorem lPoints_three (D : JointData) (hlS : D.lSides = paperLSides) (f : Word → JSlice) (w : Word) (hb : ¬ IsBase w)
    (hJ : ∀ u : Word, u.length < w.length → IsJointSlice D f u) (hl : w.getLast? = some Digit.three) :
    ((((0 : ℤ), (0 : ℤ)) ∈ (((below f w) w.dropLast).lEven true false).dom ∧
      vQ1 w ∈ (((below f w) w.dropLast).lEven true false).dom) ∧
      vQ2 w + ((1 : ℤ), (-1 : ℤ)) ∈ (((below f w) w.dropLast).lEven false false).dom) := by
  have hlen := dropLast_length_lt hl
  rw [below_of_lt f w _ hlen]
  have hdef := evenLDefined_dropLast hb hl
  have hw := eq_dropLast_append hl
  have hLP := (hJ _ hlen).2.2.2
  have hX : texV1Even (fracEven w.dropLast) = vQ1 w := by
    unfold vQ1 fracEven
    conv_rhs => rw [hw]
    rw [parentsAt_append_singleton]
    rfl
  have hY : texV2 (fracEven w.dropLast) = vQ2 w := by
    unfold vQ2 fracEven
    conv_rhs => rw [hw]
    rw [parentsAt_append_singleton]
    rfl
  obtain ⟨-, c, hc⟩ := (hLP.2 true false hdef).2
  obtain ⟨-, c', hc'⟩ := (hLP.2 false false hdef).2
  rw [hlS] at hc hc'
  have hP := side_hPlus (hWordOf w.dropLast true) (texV1Even (fracEven w.dropLast))
    (hWordOf_head_last w.dropLast true).1 (hWordOf_head_last w.dropLast true).2
    (StdCornerAnchors.stdAnchorX_even w.dropLast)
  have hM := side_hMinus (hWordOf w.dropLast true).reverse (by
      intro h; rw [List.reverse_eq_nil_iff] at h; have := (hWordOf_head_last w.dropLast true).1; rw [h] at this
      simp at this)
    (lastPosOf (vRevStringAt (vWordOf w.dropLast true).reverse 0))
  rw [hX] at hP
  refine ⟨⟨(hc .hPlus (by simp [paperLSides]) _ hP.1).1, (hc .hPlus (by simp [paperLSides]) _ hP.2).1⟩, ?_⟩
  have e : lastPosOf (vRevStringAt (vWordOf w.dropLast true).reverse 0) + ((0 : ℤ), (1 : ℤ)) =
      vQ2 w + ((1 : ℤ), (-1 : ℤ)) := by
    rw [StdCornerAnchors.stdAnchorY_even w.dropLast, hY]; refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega
  rw [e] at hM
  exact (hc' .hMinus (by simp [paperLSides]) _ hM).1

/-- The kept sides of the short odd L-corrections of the odd parent (after a `2`): `1` and `Y + 1` on `v-`, `X - i` on `v+`. -/
theorem lPoints_two (D : JointData) (hlS : D.lSides = paperLSides) (f : Word → JSlice) (w : Word) (hb : ¬ IsBase w)
    (hJ : ∀ u : Word, u.length < w.length → IsJointSlice D f u) (hl : w.getLast? = some Digit.two) (plus : Bool) :
    (((plus == W1Odd w) = false) → ((1 : ℤ), (0 : ℤ)) ∈ (((below f w) w.dropLast).lOdd plus false).dom ∧
        vP2 w + ((1 : ℤ), (0 : ℤ)) ∈ (((below f w) w.dropLast).lOdd plus false).dom) ∧
      (((plus == W1Odd w) = true) → vP1 w - ((0 : ℤ), (1 : ℤ)) ∈ (((below f w) w.dropLast).lOdd plus false).dom) := by
  have hlen := dropLast_length_lt hl
  rw [below_of_lt f w _ hlen]
  have hdef := oddLDefined_dropLast hb hl
  have hw := eq_dropLast_append hl
  have hLP := (hJ _ hlen).2.2.2
  have hph : W1Odd w.dropLast = W1Odd w := by
    unfold W1Odd
    conv_rhs => rw [hw]
    rw [phase_snoc_two]
  have hX : texV1Odd (fracOdd w.dropLast) = vP1 w := by
    unfold vP1 fracOdd
    conv_rhs => rw [hw]
    rw [parentsAt_append_singleton]
    rfl
  have hY : texV2 (fracOdd w.dropLast) = vP2 w := by
    unfold vP2 fracOdd
    conv_rhs => rw [hw]
    rw [parentsAt_append_singleton]
    rfl
  obtain ⟨-, c, hc⟩ := (hLP.1 plus false hdef).2
  rw [hlS] at hc
  simp only [paperLSides, ↓reduceIte, Bool.false_eq_true, List.nil_append, List.mem_singleton, hph,
    beq_comm_bool (W1Odd w) plus] at hc
  refine ⟨fun hpf => ?_, fun hpt => ?_⟩
  · rw [hpf] at hc
    simp only [Bool.false_eq_true, ↓reduceIte, forall_eq] at hc
    have hV := side_vMinus (vWordOf w.dropLast false) (texV2 (fracOdd w.dropLast))
      (StringCorners.vertWord_head_last w.dropLast).1 (StringCorners.vertWord_head_last w.dropLast).2
      (StdCornerAnchors.stdAnchorY_odd w.dropLast)
    rw [hY] at hV
    exact ⟨(hc _ hV.1).1, (hc _ hV.2).1⟩
  · rw [hpt] at hc
    simp only [↓reduceIte, forall_eq] at hc
    have hV := side_vPlus (vWordOf w.dropLast false) (by
        intro h; have := (StringCorners.vertWord_head_last w.dropLast).1
        change (vWordOf w.dropLast false).head? = some Letter.p at this
        rw [h] at this; simp at this)
      (lastPosOf (hStringAt (hWordOf w.dropLast false) 0))
    have hA := StdCornerAnchors.stdAnchorX_odd w.dropLast
    have e : lastPosOf (hStringAt (hWordOf w.dropLast false) 0) + ((1 : ℤ), (0 : ℤ)) = vP1 w - ((0 : ℤ), (1 : ℤ)) := by
      rw [show (0 : GInt) = ((0 : ℤ), (0 : ℤ)) from rfl, hA, hX]; refine Prod.ext ?_ ?_ <;> simp
    rw [e] at hV
    exact (hc _ hV).1

/-- The two standard decompositions of a word that is not a base word have connected overlap graphs. -/
theorem std_connected (D : JointData) (hlS : D.lSides = paperLSides) (f : Word → JSlice) (w : Word) (hb : ¬ IsBase w)
    (hJ : ∀ u : Word, u.length < w.length → IsJointSlice D f u) :
    (overlapGraph (goodPart (tileOddPieces D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven)
      (fun u => (below f w u).lEven) w))).Connected ∧
    (overlapGraph (goodPart (tileEvenPieces D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven)
      (fun u => (below f w u).lOdd) w))).Connected := by
  obtain ⟨hP, hQ⟩ := stdCorners_reg D f w hb hJ
  exact ⟨tileOddPieces_connected D.S _ _ _ w hP hQ (lPoints_three D hlS f w hb hJ),
    tileEvenPieces_connected D.S _ _ _ w hP hQ (lPoints_two D hlS f w hb hJ)⟩

/-- The overlap graphs of the two alternate decompositions of the children of `w` are connected. -/
def ConnectedAlt (D : JointData) (g : Word → JSlice) (w : Word) : Prop :=
  (overlapGraph (goodPart (tileAltOddPieces D.S (fun u => (g u).tOdd) (fun u => (g u).tEven) (fun u => (g u).aOdd)
    (fun u => (g u).aEven) (fun u => (g u).lOdd) w))).Connected ∧
  (overlapGraph (goodPart (tileAltEvenPieces D.S (fun u => (g u).tOdd) (fun u => (g u).tEven) (fun u => (g u).aOdd)
    (fun u => (g u).aEven) (fun u => (g u).lEven) w))).Connected

/-- With the paper sides of the L-corrections, the standard half of `Connected4` holds (`std_connected`). -/
theorem connected4_of (D : JointData) (hlS : D.lSides = paperLSides) (f : Word → JSlice) (n : ℕ) (hgood : GoodBelow D f n)
    (w : Word) (hw : w.length = n) (hb : ¬ IsBase w) (hA : ConnectedAlt D (below f w) w) : Connected4 D (below f w) w := by
  have hs := std_connected D hlS f w hb (fun u hu => (hgood u (by omega)).1)
  exact ⟨hs.1, hs.2, hA.1, hA.2⟩

/-- The rotation step with the standard connectivity proved: the named inputs left are the base slopes and rotations, the
connectivity of the alternate and L decompositions, and the special prefixes. -/
theorem rotStepInput_of_alt (D : JointData) (hB : BaseSlopes D) (hBR : BaseRot D) (hlS : D.lSides = paperLSides)
    (hconnA : ∀ (f : Word → JSlice) (n : ℕ), LevelHyp D f n →
      ∀ w : Word, w.length = n → ¬ IsBase w → ConnectedAlt D (below f w) w)
    (hconnL : ∀ (f : Word → JSlice) (n : ℕ), LevelHyp D f n → ∀ w : Word, w.length = n → ConnectedL D (below f w) w)
    (hspec : ∀ (f : Word → JSlice) (n : ℕ), LevelHyp D f n → SpecialLRot f n) :
    RotStepInput D :=
  rotStepInput_of D hB hBR (fun f n hL w hw hb => connected4_of D hlS f n hL.1 w hw hb (hconnA f n hL w hw hb)) hconnL hspec

/-! ### The L-rotation at the special prefixes -/

/-- `rawRot_of_pieces` with the pieces given by membership. -/
theorem rawRot_of_mem (o oR : PartialOdometer) (psR : List Piece) (c γ : Site)
    (hdom : oR.dom = pieceUnion psR) (hcov : PiecesCovered psR)
    (hconn : (overlapGraph (goodPart psR)).Connected)
    (hpiece : ∀ pR ∈ psR, ∃ C : ℤ, ∀ x ∈ pR.placed, x ∉ pR.exc →
      mulI x + c ∈ o.dom ∧ oR.val x = o.val (mulI x + c) - h0 x + dotS γ x + C) :
    RawRot o oR c γ :=
  rawRot_of_pieces o oR psR c γ hdom hcov hconn (fun _ pR hi => hpiece pR (List.mem_of_getElem? hi))

/-- One pair of pieces from its `PairCond`. -/
theorem piece_of_pairCond (o oR : PartialOdometer) (ps psR : List Piece) (c γ : Site)
    (ho : RespectsPieces o ps) (hoR : RespectsPieces oR psR) (p pR : Piece) (hp : p ∈ ps) (hpR : pR ∈ psR)
    (h : PairCond c γ pR p) :
    ∃ C : ℤ, ∀ x ∈ pR.placed, x ∉ pR.exc →
      mulI x + c ∈ o.dom ∧ oR.val x = o.val (mulI x + c) - h0 x + dotS γ x + C := by
  obtain ⟨cr, γr, hpar, hoff, h1, h2, hexc⟩ := h
  have hev : EvenSite pR.off := by show (pR.off.1 + pR.off.2) % 2 = 0; omega
  have haff : pR.aff = rotR p.aff + hHalf pR.off + γ - γr := by
    refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, hHalf] at h1 h2 ⊢ <;> omega
  obtain ⟨b, hb⟩ := ho.2 p hp
  obtain ⟨bR, hbR⟩ := hoR.2 pR hpR
  obtain ⟨C, hC⟩ := piece_transport o oR p pR c γ cr γr b bR hb hbR hpar hoff hev haff hexc
  refine ⟨C, fun x hx hxe => ⟨?_, (hC x hx hxe).2⟩⟩
  rw [ho.1]
  exact mem_pieceUnion.mpr ⟨p, hp, (hC x hx hxe).1⟩

/-- A piece of `oR` on which the two L-corrections agree with their children (`LSidesAgree`): the raw rotation of the children
gives the raw rotation of the L-corrections there, with one constant. -/
theorem piece_of_sides (o oR T TR : PartialOdometer) (c : Site) (P : Set Site)
    (hT : RawRot T TR c 0) (cO cR : ℤ)
    (hO : ∀ y, y ∈ P → mulI y + c ∈ o.dom ∧ mulI y + c ∈ T.dom ∧ o.val (mulI y + c) = T.val (mulI y + c) + cO)
    (hR : ∀ y, y ∈ P → y ∈ oR.dom ∧ y ∈ TR.dom ∧ oR.val y = TR.val y + cR) :
    ∃ C : ℤ, ∀ y ∈ P, mulI y + c ∈ o.dom ∧ oR.val y = o.val (mulI y + c) - h0 y + dotS 0 y + C := by
  obtain ⟨CT, hCT⟩ := hT
  refine ⟨CT + cR - cO, fun y hy => ⟨(hO y hy).1, ?_⟩⟩
  obtain ⟨-, -, hv⟩ := hR y hy
  obtain ⟨-, -, hv'⟩ := hO y hy
  obtain ⟨-, ht⟩ := hCT y (hR y hy).2.1
  rw [hv, ht, hv']
  simp [dotS]
  ring

/-- Two decompositions `A ++ X ++ H` (of `o`) and `AR ++ [B] ++ HR` (of `oR`), the outer parts pairing piece by piece and the
middle piece `B` of `oR` with its own constant. -/
theorem rawRot_of_split (o oR : PartialOdometer) (A X H AR HR : List Piece) (B : Piece) (c γ : Site)
    (ho : RespectsPieces o (A ++ X ++ H)) (hoR : RespectsPieces oR (AR ++ [B] ++ HR))
    (hcov : PiecesCovered (AR ++ [B] ++ HR)) (hconn : (overlapGraph (goodPart (AR ++ [B] ++ HR))).Connected)
    (hA : List.Forall₂ (PairCond c γ) AR A) (hH : List.Forall₂ (PairCond c γ) HR H)
    (hB : ∃ C : ℤ, ∀ x ∈ B.placed, x ∉ B.exc →
      mulI x + c ∈ o.dom ∧ oR.val x = o.val (mulI x + c) - h0 x + dotS γ x + C) :
    RawRot o oR c γ := by
  refine rawRot_of_mem o oR _ c γ hoR.1 hcov hconn (fun pR hpR => ?_)
  simp only [List.mem_append, List.mem_singleton] at hpR
  rcases hpR with (h | rfl) | h
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
    have hi' : i < A.length := hA.length_eq ▸ hi
    exact piece_of_pairCond o oR _ _ c γ ho hoR A[i] AR[i] (by simp [List.getElem_mem])
      (by simp [List.getElem_mem]) (hA.get hi hi')
  · exact hB
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
    have hi' : i < H.length := hH.length_eq ▸ hi
    exact piece_of_pairCond o oR _ _ c γ ho hoR H[i] HR[i] (by simp [List.getElem_mem])
      (by simp [List.getElem_mem]) (hH.get hi hi')

/-! ### The pieces of the L-corrections, named -/

section LPiecesNamed
variable (S : WeakData) (pO pE aO aE : Word → PartialOdometer)

/-- The coefficients `K_1, ..., K_4` of the even L-correction of `w`. -/
def eK (w : Word) (plus : Bool) : AltCoeff × AltCoeff × AltCoeff × AltCoeff :=
  evenKCoeff (W1Odd w) plus (decide ((stripTrailing Digit.three w).getLast? = some Digit.two))

/-- The coefficients of the odd L-correction of `w`. -/
def oK (w : Word) (plus : Bool) : AltCoeff × AltCoeff × AltCoeff × AltCoeff := oddKCoeff (W1Odd w) plus

/-- The stem `j` of the even L-correction. -/
def eStem (w : Word) (plus : Bool) (j : ℕ) : Piece :=
  stdPiece (regOdo S pO pE (regsAt (stripTrailing Digit.three w)).1 true)
    (evenLInitOff w plus + altOff (stripTrailing Digit.three w) ((j : ℤ) • (eK w plus).1))
    (evenLInitAff w plus + altAff (stripTrailing Digit.three w) ((j : ℤ) • (eK w plus).1))

/-- The middle of the even L-correction: the bridge (unless case `01` at `2^j`) and the copy of `T^d_{1/1}` (at `2^j`). -/
def eMid (w : Word) (plus : Bool) : List Piece :=
  let pre := stripTrailing Digit.three w
  let k := trailingCount Digit.three w
  let double : Bool := !pre.isEmpty && pre.all (fun d => decide (d = Digit.two))
  let case01 : Bool := !W1Odd w && !plus
  let cB : AltCoeff := (k : ℤ) • (eK w plus).1 + (eK w plus).2.1
  (if double && case01 then [] else
    [stdPiece (regOdo S pO pE (regsAt pre).2 false) (evenLInitOff w plus + altOff pre cB) (evenLInitAff w plus + altAff pre cB)]) ++
  (if double then [stdPiece enlOdo (evenLInitOff w plus + altOff pre cB + ((1 : ℤ), (1 : ℤ))) (evenLInitAff w plus + altAff pre cB)]
    else [])

/-- The head `i` of the even L-correction. -/
def eHead (w : Word) (plus : Bool) (i : ℕ) : Piece :=
  let pre := stripTrailing Digit.three w
  let k := trailingCount Digit.three w
  let K := eK w plus
  let o0 := evenLInitOff w plus
  let double : Bool := !pre.isEmpty && pre.all (fun d => decide (d = Digit.two))
  let stemK : Finset Site := (regOdo S pO pE (regsAt pre).1 true).dom.image (· + (o0 + altOff pre ((k : ℤ) • K.1)))
  let hc : ℕ → AltCoeff := fun i => (k : ℤ) • K.1 + K.2.1 + K.2.2.1 + ((i : ℤ) + 1) • K.2.2.2
  { odo := regOdo S aO aE (regsAt pre).1 true, off := o0 + altOff pre (hc i), aff := evenLInitAff w plus + altAff pre (hc i),
    exc := if double && i == 0 then
      {x | x - (o0 + altOff pre (hc 0)) + ((0 : ℤ), (1 : ℤ)) ∈ paperNearStairAltA (2 * (pre.length : ℤ) + 1) ∧
        x ∈ stemK} else ∅ }

theorem evenLPieces_split (w : Word) (plus elong : Bool) :
    evenLPieces S pO pE aO aE w plus elong =
      (List.range (trailingCount Digit.three w + 1)).map (eStem S pO pE w plus) ++ eMid S pO pE w plus ++
        (List.range (2 * (trailingCount Digit.three w + 1) - (if elong then 0 else 1))).map (eHead S pO pE aO aE w plus) := by
  unfold evenLPieces eMid eStem eHead eK
  simp only [List.append_assoc]

/-- The stem `j` of the odd L-correction. -/
def oStem (w : Word) (plus : Bool) (j : ℕ) : Piece :=
  stdPiece (regOdo S pO pE (regsAt (stripTrailing Digit.two w)).2 false)
    (oddLInitOff w plus + altOff (stripTrailing Digit.two w) ((j : ℤ) • (oK w plus).1))
    (oddLInitAff w plus + altAff (stripTrailing Digit.two w) ((j : ℤ) • (oK w plus).1))

/-- The bridge of the odd L-correction (shifted at `3^j`). -/
def oBridge (w : Word) (plus : Bool) : Piece :=
  let pre := stripTrailing Digit.two w
  let k := trailingCount Digit.two w
  let triple : Bool := !pre.isEmpty && pre.all (fun d => decide (d = Digit.three))
  let cB : AltCoeff := (k : ℤ) • (oK w plus).1 + (oK w plus).2.1
  stdPiece (regOdo S pO pE (regsAt pre).1 true)
    (oddLInitOff w plus + altOff pre cB + LCorrections.oddBridgeShift triple (W1Odd w) plus) (oddLInitAff w plus + altAff pre cB)

/-- The head `i` of the odd L-correction. -/
def oHead (w : Word) (plus : Bool) (i : ℕ) : Piece :=
  let pre := stripTrailing Digit.two w
  let k := trailingCount Digit.two w
  let K := oK w plus
  let o0 := oddLInitOff w plus
  let triple : Bool := !pre.isEmpty && pre.all (fun d => decide (d = Digit.three))
  let stemK : Finset Site := (regOdo S pO pE (regsAt pre).2 false).dom.image (· + (o0 + altOff pre ((k : ℤ) • K.1)))
  let hc : ℕ → AltCoeff := fun i => (k : ℤ) • K.1 + K.2.1 + K.2.2.1 + ((i : ℤ) + 1) • K.2.2.2
  { odo := regOdo S aO aE (regsAt pre).2 false, off := o0 + altOff pre (hc i), aff := oddLInitAff w plus + altAff pre (hc i),
    exc := if triple && i == 0 then
      {x | x - (o0 + altOff pre (hc 0)) ∈ paperStairAltA (2 * (pre.length : ℤ) + 1) ∧ x ∈ stemK} else ∅ }

theorem oddLPieces_split (w : Word) (plus elong : Bool) :
    oddLPieces S pO pE aO aE w plus elong =
      (List.range (trailingCount Digit.two w + 1)).map (oStem S pO pE w plus) ++ [oBridge S pO pE w plus] ++
        (List.range (2 * (trailingCount Digit.two w + 1) - (if elong then 0 else 1))).map (oHead S pO pE aO aE w plus) := by
  unfold oddLPieces oBridge oStem oHead oK
  rfl

end LPiecesNamed

set_option maxHeartbeats 400000 in
/-- The even L-correction of `w` against the odd L-correction of `swapW w` when the prefix is `2^j`: the stems and the heads pair
index by index as for the other prefixes; the bridge `T_{0/1}` of the rotated odd L-correction carries its own constant (`hside`,
from the sides), and the exceptional points of the first heads correspond (`hexc0`). -/
theorem evenL_special_rawRot (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w : Word) (plus elong : Bool)
    (o oR : PartialOdometer)
    (ho : RespectsPieces o (evenLPieces S pO pE aO aE w plus elong))
    (hoR : RespectsPieces oR (oddLPieces S pO pE aO aE (swapW w) (plus != W1Odd w) elong))
    (hconn : (overlapGraph (goodPart (oddLPieces S pO pE aO aE (swapW w) (plus != W1Odd w) elong))).Connected)
    (hd : (!(stripTrailing Digit.three w).isEmpty && (stripTrailing Digit.three w).all (fun d => decide (d = Digit.two))) = true)
    (hS : RawRot (regOdo S pO pE (regsAt (stripTrailing Digit.three w)).1 true) (regOdo S pO pE (regsAt (swapW (stripTrailing Digit.three w))).2 false)
      (vP1 (stripTrailing Digit.three w) - ((0 : ℤ), (1 : ℤ))) 0)
    (hH : RawRot (regOdo S aO aE (regsAt (stripTrailing Digit.three w)).1 true) (regOdo S aO aE (regsAt (swapW (stripTrailing Digit.three w))).2 false)
      (altParP (stripTrailing Digit.three w)).1 (altParP (stripTrailing Digit.three w)).2)
    (hside : ∃ C : ℤ, ∀ x ∈ (oBridge S pO pE (swapW w) (plus != W1Odd w)).placed,
      x ∉ (oBridge S pO pE (swapW w) (plus != W1Odd w)).exc →
      mulI x + (texV1Even ((parentsAt w).current .even) - ((0 : ℤ), (1 : ℤ))) ∈ o.dom ∧ oR.val x = o.val (mulI x + (texV1Even ((parentsAt w).current .even) - ((0 : ℤ), (1 : ℤ)))) - h0 x + dotS 0 x + C)
    (hexc0 : ∀ x ∈ (oHead S pO pE aO aE (swapW w) (plus != W1Odd w) 0).placed,
      x ∉ (oHead S pO pE aO aE (swapW w) (plus != W1Odd w) 0).exc → mulI x + (texV1Even ((parentsAt w).current .even) - ((0 : ℤ), (1 : ℤ))) ∉ (eHead S pO pE aO aE w plus 0).exc) :
    RawRot o oR (texV1Even ((parentsAt w).current .even) - ((0 : ℤ), (1 : ℤ))) 0 := by
  obtain ⟨hsw1, hsw2⟩ := swapW_strip_three w
  have hWw := W1Odd_swapW w
  have hall : ∀ d ∈ (stripTrailing Digit.three w), d = Digit.two := by
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true, decide_eq_true_eq] at hd
    exact hd.2
  have hne : (stripTrailing Digit.three w) ≠ [] := by
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hd
    exact hd.1
  have hl : (stripTrailing Digit.three w).getLast? = some Digit.two := by
    obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp (by simpa using hne : (stripTrailing Digit.three w).getLast? ≠ none)
    rw [hx, hall x (List.mem_of_getLast? hx)]
  have hWs : W1Odd (stripTrailing Digit.three w) = false := by
    have h0 : (stripTrailing Digit.three w).count Digit.one = 0 := List.count_eq_zero.mpr (fun h => by have := hall _ h; cases this)
    unfold W1Odd phase; rw [h0]; rfl
  have hpw : parentsAt w = ⟨(parentsAt (stripTrailing Digit.three w)).odd, ⟨(parentsAt (stripTrailing Digit.three w)).even.num +
      2 * (trailingCount Digit.three w : ℕ) * (parentsAt (stripTrailing Digit.three w)).odd.num,
      (parentsAt (stripTrailing Digit.three w)).even.den + 2 * (trailingCount Digit.three w : ℕ) * (parentsAt (stripTrailing Digit.three w)).odd.den⟩⟩ := by
    conv_lhs => rw [← strip_append_replicate Digit.three w]
    exact parents_append_threes _ _
  have hpsw : parentsAt (swapW w) = ⟨⟨(parentsAt (swapW (stripTrailing Digit.three w))).odd.num +
      (trailingCount Digit.three w : ℕ) * (parentsAt (swapW (stripTrailing Digit.three w))).even.num,
      (parentsAt (swapW (stripTrailing Digit.three w))).odd.den + (trailingCount Digit.three w : ℕ) * (parentsAt (swapW (stripTrailing Digit.three w))).even.den⟩,
      (parentsAt (swapW (stripTrailing Digit.three w))).even⟩ := by
    conv_lhs => rw [← strip_append_replicate Digit.three w, swapW_append, swapW_replicate]
    exact parents_append_twos _ _
  have hWo : W1Odd w = W1Odd (stripTrailing Digit.three w) := by
    conv_lhs => rw [← strip_append_replicate Digit.three w]
    exact W1Odd_append_replicate _ _ _ (by decide)
  obtain ⟨-, -, -, -, e5, e6⟩ := vecs_swapW (stripTrailing Digit.three w)
  have hq : ((parentsAt (stripTrailing Digit.three w)).even.num + (parentsAt (stripTrailing Digit.three w)).even.den) % 2 = 0 := (parentsAt_valid _).even_parity
  obtain ⟨a, hdq⟩ : ∃ a : ℤ, (parentsAt (stripTrailing Digit.three w)).even.den = 2 * a + (parentsAt (stripTrailing Digit.three w)).even.num :=
    ⟨((parentsAt (stripTrailing Digit.three w)).even.den - (parentsAt (stripTrailing Digit.three w)).even.num) / 2, by omega⟩
  have hA : (2 * a + (parentsAt (stripTrailing Digit.three w)).even.num - (parentsAt (stripTrailing Digit.three w)).even.num) / 2 = a := by omega
  have hB' : (2 * a + (parentsAt (stripTrailing Digit.three w)).even.num + (parentsAt (stripTrailing Digit.three w)).even.num) / 2 = a + (parentsAt (stripTrailing Digit.three w)).even.num := by omega
  have hcov := oddLPieces_covered S pO pE aO aE (swapW w) (plus != W1Odd w) elong
  rw [evenLPieces_split] at ho
  rw [oddLPieces_split, hsw2] at hoR hconn hcov
  refine rawRot_of_split o oR _ _ _ _ _ _ _ 0 ho hoR hcov hconn ?_ ?_ hside
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
    intro j _
    refine ⟨vP1 (stripTrailing Digit.three w) - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, fun x _ _ => by simp [eStem, stdPiece]⟩
    · simp only [eStem, oStem, stdPiece]; rw [hsw1]; exact hS
    all_goals unfold oStem eStem oK eK; simp only [hsw1]
    all_goals cases plus <;> l_unfold <;> simp only [hdq] <;> simp only [hA, hB'] <;> l_ring
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
    intro i _
    refine ⟨(altParP (stripTrailing Digit.three w)).1, (altParP (stripTrailing Digit.three w)).2,
      by simp only [eHead, oHead]; rw [hsw1]; exact hH, ?_, ?_, ?_, ?_⟩
    rotate_left 3
    · by_cases hi0 : i = 0
      · subst hi0; exact hexc0
      · intro x _ _
        simp [eHead, hi0]
    all_goals unfold oHead eHead oK eK; simp only [hsw1, hsw2]
    all_goals cases plus <;> l_unfold <;> simp only [hdq] <;> simp only [hA, hB'] <;> l_ring

/-- `rawRot_of_split` with a list of middle pieces of `oR` and one constant `C` for all of them: each point of a middle piece has the
raw rotation with `C`, or lies in a piece of `HR` that has a point with the raw rotation with `C`. -/
theorem rawRot_of_splitL (o oR : PartialOdometer) (A X H AR Bs HR : List Piece) (c γ : Site)
    (ho : RespectsPieces o (A ++ X ++ H)) (hoR : RespectsPieces oR (AR ++ Bs ++ HR))
    (hcov : PiecesCovered (AR ++ Bs ++ HR)) (hconn : (overlapGraph (goodPart (AR ++ Bs ++ HR))).Connected)
    (hA : List.Forall₂ (PairCond c γ) AR A) (hH : List.Forall₂ (PairCond c γ) HR H)
    (hB : ∃ C : ℤ, ∀ B ∈ Bs, ∀ x ∈ B.placed, x ∉ B.exc →
      (mulI x + c ∈ o.dom ∧ oR.val x = o.val (mulI x + c) - h0 x + dotS γ x + C) ∨
      ∃ r ∈ HR, x ∈ r.placed ∧ x ∉ r.exc ∧ ∃ y ∈ r.placed, y ∉ r.exc ∧
        mulI y + c ∈ o.dom ∧ oR.val y = o.val (mulI y + c) - h0 y + dotS γ y + C) :
    RawRot o oR c γ := by
  have hHp : ∀ r ∈ HR, ∃ C : ℤ, ∀ x ∈ r.placed, x ∉ r.exc →
      mulI x + c ∈ o.dom ∧ oR.val x = o.val (mulI x + c) - h0 x + dotS γ x + C := by
    intro r hr
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
    have hi' : i < H.length := hH.length_eq ▸ hi
    exact piece_of_pairCond o oR _ _ c γ ho hoR H[i] HR[i] (by simp [List.getElem_mem])
      (by simp [List.getElem_mem]) (hH.get hi hi')
  refine rawRot_of_mem o oR _ c γ hoR.1 hcov hconn (fun pR hpR => ?_)
  simp only [List.mem_append] at hpR
  rcases hpR with (h | h) | h
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
    have hi' : i < A.length := hA.length_eq ▸ hi
    exact piece_of_pairCond o oR _ _ c γ ho hoR A[i] AR[i] (by simp [List.getElem_mem])
      (by simp [List.getElem_mem]) (hA.get hi hi')
  · obtain ⟨C, hC⟩ := hB
    refine ⟨C, fun x hx hxe => ?_⟩
    rcases hC pR h x hx hxe with k | ⟨r, hr, hxr, hxre, y, hyr, hyre, hyd, hyv⟩
    · exact k
    · obtain ⟨Cr, hCr⟩ := hHp r hr
      have e1 := (hCr y hyr hyre).2
      have e2 := hCr x hxr hxre
      refine ⟨e2.1, ?_⟩
      rw [e2.2]
      linarith
  · exact hHp pR h

set_option maxHeartbeats 400000 in
/-- The odd L-correction of `w` against the even L-correction of `swapW w` when the prefix is `3^j`: the stems and the heads pair
index by index; the middle pieces of the rotated even L-correction (its bridge `T_{1/1}` and its copy of `T^d_{1/1}`) carry their
own constants (`hside`), and the exceptional points of the first heads correspond (`hexc0`). -/
theorem oddL_special_rawRot (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w : Word) (plus elong : Bool)
    (o oR : PartialOdometer)
    (ho : RespectsPieces o (oddLPieces S pO pE aO aE w plus elong))
    (hoR : RespectsPieces oR (evenLPieces S pO pE aO aE (swapW w) (plus == W1Odd w) elong))
    (hconn : (overlapGraph (goodPart (evenLPieces S pO pE aO aE (swapW w) (plus == W1Odd w) elong))).Connected)
    (hd : (!(stripTrailing Digit.two w).isEmpty && (stripTrailing Digit.two w).all (fun d => decide (d = Digit.three))) = true)
    (hS : RawRot (regOdo S pO pE (regsAt (stripTrailing Digit.two w)).2 false) (regOdo S pO pE (regsAt (swapW (stripTrailing Digit.two w))).1 true)
      (vQ1 (stripTrailing Digit.two w) - ((0 : ℤ), (1 : ℤ))) 0)
    (hH : RawRot (regOdo S aO aE (regsAt (stripTrailing Digit.two w)).2 false) (regOdo S aO aE (regsAt (swapW (stripTrailing Digit.two w))).1 true)
      (altParQ (stripTrailing Digit.two w)).1 (altParQ (stripTrailing Digit.two w)).2)
    (hside : ∃ C : ℤ, ∀ B ∈ eMid S pO pE (swapW w) (plus == W1Odd w), ∀ x ∈ B.placed, x ∉ B.exc →
      (mulI x + (texV1Odd ((parentsAt w).current .odd) - ((0 : ℤ), (1 : ℤ))) ∈ o.dom ∧
        oR.val x = o.val (mulI x + (texV1Odd ((parentsAt w).current .odd) - ((0 : ℤ), (1 : ℤ)))) - h0 x + dotS 0 x + C) ∨
      ∃ r ∈ (List.range (2 * (trailingCount Digit.two w + 1) - (if elong then 0 else 1))).map
          (eHead S pO pE aO aE (swapW w) (plus == W1Odd w)),
        x ∈ r.placed ∧ x ∉ r.exc ∧ ∃ y ∈ r.placed, y ∉ r.exc ∧
          mulI y + (texV1Odd ((parentsAt w).current .odd) - ((0 : ℤ), (1 : ℤ))) ∈ o.dom ∧
          oR.val y = o.val (mulI y + (texV1Odd ((parentsAt w).current .odd) - ((0 : ℤ), (1 : ℤ)))) - h0 y + dotS 0 y + C)
    (hexc0 : ∀ x ∈ (eHead S pO pE aO aE (swapW w) (plus == W1Odd w) 0).placed,
      x ∉ (eHead S pO pE aO aE (swapW w) (plus == W1Odd w) 0).exc → mulI x + (texV1Odd ((parentsAt w).current .odd) - ((0 : ℤ), (1 : ℤ))) ∉ (oHead S pO pE aO aE w plus 0).exc) :
    RawRot o oR (texV1Odd ((parentsAt w).current .odd) - ((0 : ℤ), (1 : ℤ))) 0 := by
  obtain ⟨hsw1, hsw2⟩ := swapW_strip_two w
  have hWw := W1Odd_swapW w
  have hall : ∀ d ∈ (stripTrailing Digit.two w), d = Digit.three := by
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true, decide_eq_true_eq] at hd
    exact hd.2
  have hne : (stripTrailing Digit.two w) ≠ [] := by
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hd
    exact hd.1
  have hl : (stripTrailing Digit.two w).getLast? = some Digit.three := by
    obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp (by simpa using hne : (stripTrailing Digit.two w).getLast? ≠ none)
    rw [hx, hall x (List.mem_of_getLast? hx)]
  have hWs : W1Odd (stripTrailing Digit.two w) = false := by
    have h0 : (stripTrailing Digit.two w).count Digit.one = 0 := List.count_eq_zero.mpr (fun h => by have := hall _ h; cases this)
    unfold W1Odd phase; rw [h0]; rfl
  have hpw : parentsAt w = ⟨⟨(parentsAt (stripTrailing Digit.two w)).odd.num + (trailingCount Digit.two w : ℕ) * (parentsAt (stripTrailing Digit.two w)).even.num,
      (parentsAt (stripTrailing Digit.two w)).odd.den + (trailingCount Digit.two w : ℕ) * (parentsAt (stripTrailing Digit.two w)).even.den⟩, (parentsAt (stripTrailing Digit.two w)).even⟩ := by
    conv_lhs => rw [← strip_append_replicate Digit.two w]
    exact parents_append_twos _ _
  have hpsw : parentsAt (swapW w) = ⟨(parentsAt (swapW (stripTrailing Digit.two w))).odd, ⟨(parentsAt (swapW (stripTrailing Digit.two w))).even.num +
      2 * (trailingCount Digit.two w : ℕ) * (parentsAt (swapW (stripTrailing Digit.two w))).odd.num,
      (parentsAt (swapW (stripTrailing Digit.two w))).even.den + 2 * (trailingCount Digit.two w : ℕ) * (parentsAt (swapW (stripTrailing Digit.two w))).odd.den⟩⟩ := by
    conv_lhs => rw [← strip_append_replicate Digit.two w, swapW_append, swapW_replicate]
    exact parents_append_threes _ _
  have hWo : W1Odd w = W1Odd (stripTrailing Digit.two w) := by
    conv_lhs => rw [← strip_append_replicate Digit.two w]
    exact W1Odd_append_replicate _ _ _ (by decide)
  obtain ⟨-, -, -, -, e5, e6⟩ := vecs_swapW (stripTrailing Digit.two w)
  have hq : ((parentsAt (stripTrailing Digit.two w)).even.num + (parentsAt (stripTrailing Digit.two w)).even.den) % 2 = 0 := (parentsAt_valid _).even_parity
  obtain ⟨a, hdq⟩ : ∃ a : ℤ, (parentsAt (stripTrailing Digit.two w)).even.den = 2 * a + (parentsAt (stripTrailing Digit.two w)).even.num :=
    ⟨((parentsAt (stripTrailing Digit.two w)).even.den - (parentsAt (stripTrailing Digit.two w)).even.num) / 2, by omega⟩
  have hA : (2 * a + (parentsAt (stripTrailing Digit.two w)).even.num - (parentsAt (stripTrailing Digit.two w)).even.num) / 2 = a := by omega
  have hB' : (2 * a + (parentsAt (stripTrailing Digit.two w)).even.num + (parentsAt (stripTrailing Digit.two w)).even.num) / 2 = a + (parentsAt (stripTrailing Digit.two w)).even.num := by omega
  have hcov := evenLPieces_covered S pO pE aO aE (swapW w) (plus == W1Odd w) elong
  rw [oddLPieces_split] at ho
  rw [evenLPieces_split, hsw2] at hoR hconn hcov
  refine rawRot_of_splitL o oR _ _ _ _ _ _ _ 0 ho hoR hcov hconn ?_ ?_ hside
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
    intro j _
    refine ⟨vQ1 (stripTrailing Digit.two w) - ((0 : ℤ), (1 : ℤ)), 0, ?_, ?_, ?_, ?_, fun x _ _ => by simp [oStem, stdPiece]⟩
    · simp only [eStem, oStem, stdPiece]; rw [hsw1]; exact hS
    all_goals unfold oStem eStem oK eK; simp only [hsw1]
    all_goals cases plus <;> l_unfold <;> simp only [hdq] <;> simp only [hA, hB'] <;> l_ring
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
    intro i _
    refine ⟨(altParQ (stripTrailing Digit.two w)).1, (altParQ (stripTrailing Digit.two w)).2,
      by simp only [eHead, oHead]; rw [hsw1]; exact hH, ?_, ?_, ?_, ?_⟩
    rotate_left 3
    · by_cases hi0 : i = 0
      · subst hi0; exact hexc0
      · intro x _ _
        simp [oHead, hi0]
    all_goals unfold oHead eHead oK eK; simp only [hsw1, hsw2]
    all_goals cases plus <;> l_unfold <;> simp only [hdq] <;> simp only [hA, hB'] <;> l_ring

/-! ### The special prefixes from their cells -/

/-- A point lies on one of the given side strings of the child (anchored at `c(T) = 0`). -/
def OnSides (wh wv : BinaryWord) (sides : List Side) (x : Site) : Prop :=
  ∃ sd ∈ sides, x ∈ placedSites (sideString wh wv 0 sd)

/-- **The cells of the special prefixes** (a named input, numerically `tmp-w5/special_sides2.py`, `special_bad.py`,
`special_exc.py`). For a word of length `n` whose prefix is `2^j` (even L) or `3^j` (odd L): every point of a middle piece of the
rotated L-correction lies on its kept sides and its image under `z` on the kept sides of the L-correction of `w`, or (a tip in the
short odd case) lies in a head of the rotated L-correction that has such a point; and the exceptional points of the first heads
correspond. -/
def SpecialCells (D : JointData) (f : Word → JSlice) (n : ℕ) : Prop :=
  ∀ w : Word, w.length = n →
    (EvenLDefined w → (stripTrailing Digit.three w ≠ [] ∧ ∀ d ∈ stripTrailing Digit.three w, d = Digit.two) →
      ∀ plus elong : Bool,
      let g := below f w
      let c := texV1Even ((parentsAt w).current .even) - ((0 : ℤ), (1 : ℤ))
      let s := plus != W1Odd w
      (∀ x ∈ (oBridge D.S (fun u => (g u).tOdd) (fun u => (g u).tEven) (swapW w) s).placed,
        OnSides (hWordOf (swapW w) false) (vWordOf (swapW w) false) (D.lSides true (W1Odd (swapW w)) s elong) x ∧
        OnSides (hWordOf w true) (vWordOf w true) (D.lSides false (W1Odd w) plus elong) (mulI x + c)) ∧
      (∀ x ∈ (oHead D.S (fun u => (g u).tOdd) (fun u => (g u).tEven) (fun u => (g u).aOdd) (fun u => (g u).aEven)
          (swapW w) s 0).placed,
        x ∉ (oHead D.S (fun u => (g u).tOdd) (fun u => (g u).tEven) (fun u => (g u).aOdd) (fun u => (g u).aEven)
          (swapW w) s 0).exc →
        mulI x + c ∉ (eHead D.S (fun u => (g u).tOdd) (fun u => (g u).tEven) (fun u => (g u).aOdd) (fun u => (g u).aEven)
          w plus 0).exc)) ∧
    (OddLDefined w → (stripTrailing Digit.two w ≠ [] ∧ ∀ d ∈ stripTrailing Digit.two w, d = Digit.three) →
      ∀ plus elong : Bool,
      let g := below f w
      let c := texV1Odd ((parentsAt w).current .odd) - ((0 : ℤ), (1 : ℤ))
      let s := plus == W1Odd w
      let Rs := hWordOf (swapW w) true
      let Rv := vWordOf (swapW w) true
      let sR := D.lSides false (W1Odd (swapW w)) s elong
      let sO := D.lSides true (W1Odd w) plus elong
      (∀ B ∈ eMid D.S (fun u => (g u).tOdd) (fun u => (g u).tEven) (swapW w) s, ∀ x ∈ B.placed, x ∉ B.exc →
        (OnSides Rs Rv sR x ∧ OnSides (hWordOf w false) (vWordOf w false) sO (mulI x + c)) ∨
        ∃ r ∈ (List.range (2 * (trailingCount Digit.two w + 1) - (if elong then 0 else 1))).map
            (eHead D.S (fun u => (g u).tOdd) (fun u => (g u).tEven) (fun u => (g u).aOdd) (fun u => (g u).aEven)
              (swapW w) s),
          x ∈ r.placed ∧ x ∉ r.exc ∧ ∃ y ∈ r.placed, y ∉ r.exc ∧
            OnSides Rs Rv sR y ∧ OnSides (hWordOf w false) (vWordOf w false) sO (mulI y + c)) ∧
      (∀ x ∈ (eHead D.S (fun u => (g u).tOdd) (fun u => (g u).tEven) (fun u => (g u).aOdd) (fun u => (g u).aEven)
          (swapW w) s 0).placed,
        x ∉ (eHead D.S (fun u => (g u).tOdd) (fun u => (g u).tEven) (fun u => (g u).aOdd) (fun u => (g u).aEven)
          (swapW w) s 0).exc →
        mulI x + c ∉ (oHead D.S (fun u => (g u).tOdd) (fun u => (g u).tEven) (fun u => (g u).aOdd) (fun u => (g u).aEven)
          w plus 0).exc))

/-- On the kept sides of both L-corrections, the rotation of the L-corrections is that of the children. -/
theorem good_of_sides (o oR T TR : PartialOdometer) (c : Site) (whO wvO whR wvR : BinaryWord) (sO sR : List Side)
    (hT : RawRot T TR c 0) (hLO : LSidesAgree o T whO wvO sO) (hLR : LSidesAgree oR TR whR wvR sR) :
    ∃ C : ℤ, ∀ x, OnSides whR wvR sR x → OnSides whO wvO sO (mulI x + c) →
      mulI x + c ∈ o.dom ∧ oR.val x = o.val (mulI x + c) - h0 x + dotS 0 x + C := by
  obtain ⟨-, cO, hcO⟩ := hLO
  obtain ⟨-, cR, hcR⟩ := hLR
  obtain ⟨CT, hCT⟩ := hT
  refine ⟨CT + cR - cO, fun x ⟨sd, hsd, hx⟩ ⟨sd', hsd', hx'⟩ => ?_⟩
  obtain ⟨-, hxT, hv⟩ := hcR sd hsd x hx
  obtain ⟨hzo, -, hv'⟩ := hcO sd' hsd' _ hx'
  obtain ⟨-, ht⟩ := hCT x hxT
  refine ⟨hzo, ?_⟩
  rw [hv, ht, hv']
  simp [dotS]
  ring

/-- The L-rotation at the special prefixes from their cells (`SpecialCells`), the rotation of the children at the same level, the
sides of the L-corrections and the connectivity of the L decompositions. -/
theorem specialLRot_of_cells (D : JointData) (f : Word → JSlice) (n : ℕ) (hgood : GoodBelow D f n)
    (hlev : ∀ w : Word, w.length = n → IsJointSlice D f w) (hB : BaseSlopes D)
    (hconn : ∀ w : Word, w.length = n → ConnectedL D (below f w) w) (hcells : SpecialCells D f n)
    (hrot : ∀ w : Word, w.length = n → RotProps w (f w) (f (swapW w))) : SpecialLRot f n := by
  have hJ : ∀ u : Word, u.length ≤ n → IsJointSlice D f u := fun u hu => by
    rcases lt_or_eq_of_le hu with h | h
    · exact (hgood u h).1
    · exact hlev u h
  have hsl := family_slopes D f n hJ hB
  intro w hw
  have hsw : (swapW w).length = n := by rw [length_swapW, hw]
  obtain ⟨-, -, -, hLp⟩ := hlev w hw
  obtain ⟨-, -, -, hLp'⟩ := hlev (swapW w) hsw
  obtain ⟨hcO, hcE⟩ := hconn (swapW w) hsw
  rw [below_swapW] at hLp' hcO hcE
  refine ⟨fun hdef hsp plus elong => ?_, fun hdef hsp plus elong => ?_⟩
  · -- the even L-correction at a prefix `2^j`
    obtain ⟨hB1, hE1⟩ := (hcells w hw).1 hdef hsp plus elong
    have hd : (!(stripTrailing Digit.three w).isEmpty &&
        (stripTrailing Digit.three w).all (fun d => decide (d = Digit.two))) = true := by
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true, decide_eq_true_eq]
      exact hsp
    obtain ⟨v, sd, k, hs, hwv⟩ := hdef
    have hdef' : EvenLDefined w := ⟨v, sd, k, hs, hwv⟩
    have hpre : stripTrailing Digit.three w = v ++ [sd] := by rw [hwv]; exact strip_of_defined _ _ hs v k
    have hsd : sd = Digit.two := hsp.2 sd (by rw [hpre]; simp)
    subst hsd
    have hlen : (v ++ [Digit.two]).length ≤ w.length := by rw [← hpre]; exact stripTrailing_length_le _ _
    have hvlen : v.length < w.length := by simp at hlen; omega
    have hr1 : (regsAt (stripTrailing Digit.three w)).1 = some v := by
      rw [hpre, regsAt_append_singleton]; rfl
    obtain ⟨pr1, -⟩ := parents_of_regs (stripTrailing Digit.three w)
    have J1 := (hgood v (by omega)).2.2.2.1
    have hS : RawRot (regOdo D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven)
        (regsAt (stripTrailing Digit.three w)).1 true) (regOdo D.S (fun u => (below f w u).tOdd)
        (fun u => (below f w u).tEven) (regsAt (swapW (stripTrailing Digit.three w))).2 false)
        (vP1 (stripTrailing Digit.three w) - ((0 : ℤ), (1 : ℤ))) 0 := by
      rw [regsAt_swapW, hr1]
      show RawRot (below f w v).tOdd (below f w (swapW v)).tEven _ _
      rw [below_of_lt f w v hvlen, below_of_lt f w (swapW v) (by rw [length_swapW]; exact hvlen)]
      have h := J1.1
      rw [pr1 v hr1] at h
      exact rawRot_of_tileRotation_slopes _ _ _ h (hsl v (by omega)).1 (hsl (swapW v) (by rw [length_swapW]; omega)).2.1
    have hH : RawRot (regOdo D.S (fun u => (below f w u).aOdd) (fun u => (below f w u).aEven)
        (regsAt (stripTrailing Digit.three w)).1 true) (regOdo D.S (fun u => (below f w u).aOdd)
        (fun u => (below f w u).aEven) (regsAt (swapW (stripTrailing Digit.three w))).2 false)
        (altParP (stripTrailing Digit.three w)).1 (altParP (stripTrailing Digit.three w)).2 := by
      rw [regsAt_swapW, hr1]
      show RawRot (below f w v).aOdd (below f w (swapW v)).aEven _ _
      rw [below_of_lt f w v hvlen, below_of_lt f w (swapW v) (by rw [length_swapW]; exact hvlen)]
      have h := J1.2.2.1
      have hcf := altCf_odd_reg v Digit.two (Or.inr rfl)
      rw [← hpre] at hcf
      rw [hcf] at h
      exact rawRot_of_altRotation_slopes _ _ _ _ h (hsl v (by omega)).2.2.1
        (hsl (swapW v) (by rw [length_swapW]; omega)).2.2.2
    have ho := (hLp.2 plus elong hdef').1
    have hoR := (hLp'.1 (plus != W1Odd w) elong (oddLDefined_swapW hdef')).1
    have hT := rawRot_of_tileRotation_slopes _ _ _ (hrot w hw).2.1 (hsl w (by omega)).2.1 (hsl (swapW w) (by omega)).1
    obtain ⟨C, hC⟩ := good_of_sides _ _ _ _ _ _ _ _ _ _ _ hT (hLp.2 plus elong hdef').2
      (hLp'.1 (plus != W1Odd w) elong (oddLDefined_swapW hdef')).2
    exact lRotation_of_rawRot _ _ _ (evenL_special_rawRot D.S _ _ _ _ w plus elong _ _ ho hoR
      (hcO (plus != W1Odd w) elong (oddLDefined_swapW hdef')) hd hS hH
      ⟨C, fun x hx _ => hC x (hB1 x hx).1 (hB1 x hx).2⟩ hE1)
  · -- the odd L-correction at a prefix `3^j`
    obtain ⟨hB1, hE1⟩ := (hcells w hw).2 hdef hsp plus elong
    have hd : (!(stripTrailing Digit.two w).isEmpty &&
        (stripTrailing Digit.two w).all (fun d => decide (d = Digit.three))) = true := by
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true, decide_eq_true_eq]
      exact hsp
    obtain ⟨v, sd, k, hs, hwv⟩ := hdef
    have hdef' : OddLDefined w := ⟨v, sd, k, hs, hwv⟩
    have hpre : stripTrailing Digit.two w = v ++ [sd] := by rw [hwv]; exact strip_of_defined _ _ hs v k
    have hsd : sd = Digit.three := hsp.2 sd (by rw [hpre]; simp)
    subst hsd
    have hlen : (v ++ [Digit.three]).length ≤ w.length := by rw [← hpre]; exact stripTrailing_length_le _ _
    have hvlen : v.length < w.length := by simp at hlen; omega
    have hr2 : (regsAt (stripTrailing Digit.two w)).2 = some v := by
      rw [hpre, regsAt_append_singleton]; rfl
    obtain ⟨-, pr2⟩ := parents_of_regs (stripTrailing Digit.two w)
    have J2 := (hgood v (by omega)).2.2.2.1
    have hS : RawRot (regOdo D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven)
        (regsAt (stripTrailing Digit.two w)).2 false) (regOdo D.S (fun u => (below f w u).tOdd)
        (fun u => (below f w u).tEven) (regsAt (swapW (stripTrailing Digit.two w))).1 true)
        (vQ1 (stripTrailing Digit.two w) - ((0 : ℤ), (1 : ℤ))) 0 := by
      rw [regsAt_swapW, hr2]
      show RawRot (below f w v).tEven (below f w (swapW v)).tOdd _ _
      rw [below_of_lt f w v hvlen, below_of_lt f w (swapW v) (by rw [length_swapW]; exact hvlen)]
      have h := J2.2.1
      rw [pr2 v hr2] at h
      exact rawRot_of_tileRotation_slopes _ _ _ h (hsl v (by omega)).2.1 (hsl (swapW v) (by rw [length_swapW]; omega)).1
    have hH : RawRot (regOdo D.S (fun u => (below f w u).aOdd) (fun u => (below f w u).aEven)
        (regsAt (stripTrailing Digit.two w)).2 false) (regOdo D.S (fun u => (below f w u).aOdd)
        (fun u => (below f w u).aEven) (regsAt (swapW (stripTrailing Digit.two w))).1 true)
        (altParQ (stripTrailing Digit.two w)).1 (altParQ (stripTrailing Digit.two w)).2 := by
      rw [regsAt_swapW, hr2]
      show RawRot (below f w v).aEven (below f w (swapW v)).aOdd _ _
      rw [below_of_lt f w v hvlen, below_of_lt f w (swapW v) (by rw [length_swapW]; exact hvlen)]
      have h := J2.2.2.2
      have hcf := altCf_even_reg v Digit.three (Or.inr rfl)
      rw [← hpre] at hcf
      rw [hcf] at h
      exact rawRot_of_altRotation_slopes _ _ _ _ h (hsl v (by omega)).2.2.2
        (hsl (swapW v) (by rw [length_swapW]; omega)).2.2.1
    have ho := (hLp.1 plus elong hdef').1
    have hoR := (hLp'.2 (plus == W1Odd w) elong (evenLDefined_swapW hdef')).1
    have hT := rawRot_of_tileRotation_slopes _ _ _ (hrot w hw).1 (hsl w (by omega)).1 (hsl (swapW w) (by omega)).2.1
    obtain ⟨C, hC⟩ := good_of_sides _ _ _ _ _ _ _ _ _ _ _ hT (hLp.1 plus elong hdef').2
      (hLp'.2 (plus == W1Odd w) elong (evenLDefined_swapW hdef')).2
    refine lRotation_of_rawRot _ _ _ (oddL_special_rawRot D.S _ _ _ _ w plus elong _ _ ho hoR
      (hcE (plus == W1Odd w) elong (evenLDefined_swapW hdef')) hd hS hH ⟨C, fun B hB x hx hxe => ?_⟩ hE1)
    rcases hB1 B hB x hx hxe with h | ⟨r, hr, hxr, hxre, y, hyr, hyre, hy1, hy2⟩
    · exact Or.inl (hC x h.1 h.2)
    · exact Or.inr ⟨r, hr, hxr, hxre, y, hyr, hyre, hC y hy1 hy2⟩

/-- **The rotation step**, with the special prefixes from their cells: `RotStepInput D` from the base slopes and rotations, the
paper sides of the L-corrections, the connectivity of the alternate and L decompositions, and `SpecialCells`. -/
theorem rotStepInput_of_cells (D : JointData) (hB : BaseSlopes D) (hBR : BaseRot D) (hlS : D.lSides = paperLSides)
    (hconnA : ∀ (f : Word → JSlice) (n : ℕ), LevelHyp D f n →
      ∀ w : Word, w.length = n → ¬ IsBase w → ConnectedAlt D (below f w) w)
    (hconnL : ∀ (f : Word → JSlice) (n : ℕ), LevelHyp D f n → ∀ w : Word, w.length = n → ConnectedL D (below f w) w)
    (hcells : ∀ (f : Word → JSlice) (n : ℕ), LevelHyp D f n → SpecialCells D f n) :
    RotStepInput D := by
  intro f n hg hlev w hw
  have hL : LevelHyp D f n := ⟨hg, hlev⟩
  have hrot : ∀ w : Word, w.length = n → RotProps w (f w) (f (swapW w)) := fun w hw =>
    rotProps_step D f n hg (fun w hw => (hlev w hw).1) hB hBR
      (fun w hw hb => connected4_of D hlS f n hg w hw hb (hconnA f n hL w hw hb)) w hw
  exact ⟨hrot w hw, lRotProps_step D f n hg (fun w hw => (hlev w hw).1) hB (hconnL f n hL)
    (specialLRot_of_cells D f n hg (fun w hw => (hlev w hw).1) hB (hconnL f n hL) (hcells f n hL) hrot) w hw⟩

end FLatticePaper.Tiles.JointRot
