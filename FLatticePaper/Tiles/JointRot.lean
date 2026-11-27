import FLatticePaper.Tiles.JointGlue

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
of `w` (`altParQ`, `altParP`, `altCf_even_reg`, `altCf_odd_reg`). -/

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

open FLatticePaper.Tiles.SurgicalAlt (altTypeOf altQ1Coeff altP1Coeff altP0Coeff altQ0Coeff coeffOff coeffAffine)
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
    (hA : RawRot (regOdo S aO aE (regsAt w).2 false) (regOdo S aO aE (regsAt (swapW w)).1 true) (altParQ w).1 (altParQ w).2)
    (hL : w.getLast? = some Digit.two → ∀ plus : Bool,
      RawRot (lO w.dropLast plus true) (lE (swapW w.dropLast) (plus == W1Odd w) true) (vP1 w - ((0 : ℤ), (1 : ℤ))) 0) :
    RawRot o oR (altCf w true).1 (altCf w true).2 := by
  refine rawRot_of_pairing o oR _ _ _ _ ho hoR hcov hconn ?_
  cases hWo : W1Odd w <;> rcases hl : w.getLast? with _ | d
  · exact tileAltOdd_rawRot_even_none S pO pE aO aE lE lO w hWo hl hP hQ
  · cases d
    · exact tileAltOdd_rawRot_even_one S pO pE aO aE lE lO w hWo hl hP hQ hA
    · exact tileAltOdd_rawRot_even_two S pO pE aO aE lE lO w hWo hl hP hQ hL
    · exact tileAltOdd_rawRot_even_three S pO pE aO aE lE lO w hWo hl hP hQ hA
  · exact tileAltOdd_rawRot_odd_none S pO pE aO aE lE lO w hWo hl hP hQ
  · cases d
    · exact tileAltOdd_rawRot_odd_one S pO pE aO aE lE lO w hWo hl hP hQ hA
    · exact tileAltOdd_rawRot_odd_two S pO pE aO aE lE lO w hWo hl hP hQ hL
    · exact tileAltOdd_rawRot_odd_three S pO pE aO aE lE lO w hWo hl hP hQ hA

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
    (hA : RawRot (regOdo S aO aE (regsAt w).1 true) (regOdo S aO aE (regsAt (swapW w)).2 false) (altParP w).1 (altParP w).2)
    (hL : w.getLast? = some Digit.three → ∀ plus : Bool,
      RawRot (lE w.dropLast plus true) (lO (swapW w.dropLast) (plus != W1Odd w) true) (vQ1 w - ((0 : ℤ), (1 : ℤ))) 0) :
    RawRot o oR (altCf w false).1 (altCf w false).2 := by
  refine rawRot_of_pairing o oR _ _ _ _ ho hoR hcov hconn ?_
  cases hWo : W1Odd w <;> rcases hl : w.getLast? with _ | d
  · exact tileAltEven_rawRot_even_none S pO pE aO aE lE lO w hWo hl hP hQ
  · cases d
    · exact tileAltEven_rawRot_even_one S pO pE aO aE lE lO w hWo hl hP hQ hA
    · exact tileAltEven_rawRot_even_two S pO pE aO aE lE lO w hWo hl hP hQ hA
    · exact tileAltEven_rawRot_even_three S pO pE aO aE lE lO w hWo hl hP hQ hL
  · exact tileAltEven_rawRot_odd_none S pO pE aO aE lE lO w hWo hl hP hQ
  · cases d
    · exact tileAltEven_rawRot_odd_one S pO pE aO aE lE lO w hWo hl hP hQ hA
    · exact tileAltEven_rawRot_odd_two S pO pE aO aE lE lO w hWo hl hP hQ hA
    · exact tileAltEven_rawRot_odd_three S pO pE aO aE lE lO w hWo hl hP hQ hL

end FLatticePaper.Tiles.JointRot
