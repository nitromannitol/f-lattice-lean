import FLatticePaper.Tiles.ClosedPathTriangle
import FLatticePaper.Tiles.StdCornerAnchors

/-! # Condition (C): the optional interfaces of the odd standard child

The odd child has two optional mixed interfaces in each orientation (`TriOdd`). This module proves them for parents whose
affine factor on the first bottom tile is zero (`SigmaZero`, the normalisation of eq:std_corner_values, where the four bottom
corner values vanish), following Step 1 of `lemma:weak_standard_odometer_properties` (the point `z*`):

* `W_1` even, `(P^-, Q^{+,2})` (`triOdd_ef_one`): if the copies meet, the real coordinate of `v_{p,1}` exceeds that of `v_{q,1}`
  (the boxes of `ClosedPathExcluded`), so `2 d_p > d_q`. With `n_q d_p - n_p d_q = 1` (`det_parentsAt`), the ceiling word of `P`
  has `n_q` letters `q` among its first `|w_h(q)| = (d_q + n_q)/2` letters and `n_q + 1` among the first `|w_h(q)| + 1`: the next
  tile of the bottom string of `P` is a one tile at `U = v_{q,1}`. The point `z* = U + V + 1` lies on it (relative to `P^-`) and on
  the first top corner of `Q^{+,2}`; there both normalised parents are a constant, and the triangle identity holds. -/

namespace FLatticePaper.Tiles.ClosedPathTriOdd

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.SiteInduction
open FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.CeilWords FLatticePaper.Tiles.ChildGlue
open FLatticePaper.Tiles.MixedPieces FLatticePaper.Tiles.ClosedPathSum FLatticePaper.Tiles.ClosedPathAssembly
open FLatticePaper.Tiles.ClosedPathStandard FLatticePaper.Tiles.StandardClause FLatticePaper.Tiles.ClosedPathExcluded
open FLatticePaper.Tiles.ClosedPathTriangle FLatticePaper.Tiles.ClosedPathCorners FLatticePaper.Tiles.HorizontalStepOne
open FLatticePaper.Tiles.Standard (oddTile evenTile)

/-- The normalisation of a parent: its affine factor on the first bottom tile vanishes, `S(1) = S(0)` and `S(X) = S(X - i)`. -/
def SigmaZero (S : GInt → ℤ) (X : GInt) : Prop := S e₁ - S 0 = 0 ∧ S X - S (X - e₂) = 0

/-- **A normalised parent along its bottom string**: the base odometer of each tile plus one constant. -/
theorem fwd_formula_norm (x : BinaryWord) (S : GInt → ℤ) (X : GInt) (hh : x.head? = some .q)
    (hl : x.getLast? = some .p) (hX : lastPosOf (hStringAt x 0) = X - (1, 1))
    (hR : RespectsTiles .horizontal false (hStringAt x 0) S) (hσ : SigmaZero S X) :
    ∃ β : ℤ, (∀ k < (hStringAt x 0).length, ∀ y : GInt,
      y - ((hStringAt x 0).getD k (ZTile.zero, 0)).2 ∈ tileShape ((hStringAt x 0).getD k (ZTile.zero, 0)).1 →
      S y = zTileOdo ((hStringAt x 0).getD k (ZTile.zero, 0)).1 (y - ((hStringAt x 0).getD k (ZTile.zero, 0)).2) + β) ∧
      S 0 = β ∧ S e₁ = β ∧ S X = β ∧ S (X - e₂) = β := by
  obtain ⟨α, β, h⟩ := horizontal_formula x 0 S hR
  have hne : x ≠ [] := by
    rintro rfl
    simp at hh
  have hlen : (hStringAt x 0).length = x.length := hStringAt_length' x 0
  have hpos : 0 < (hStringAt x 0).length := by rw [hlen]; exact List.length_pos_of_ne_nil hne
  have mem : ∀ k < (hStringAt x 0).length, ∀ y : GInt,
      y - ((hStringAt x 0).getD k (ZTile.zero, 0)).2 ∈ tileShape ((hStringAt x 0).getD k (ZTile.zero, 0)).1 →
      y ∈ (famOf fwdStr (hStringAt x 0)).dom k := by
    intro k _ y hy
    rw [mem_dom_iff, famOf_tile]
    exact hy
  have ht0 : (hStringAt x 0).getD 0 (ZTile.zero, 0) = (ZTile.one, 0) := by
    rw [← headD_eq_getD_zero']
    exact hStringAt_head_q x 0 hh
  have hwl : x.getD (x.length - 1) Letter.p = Letter.p := by
    rw [List.getD_eq_getElem?_getD, ← List.getLast?_eq_getElem?, hl]
    rfl
  have htl : (hStringAt x 0).getD ((hStringAt x 0).length - 1) (ZTile.zero, 0) = (ZTile.zero, X - (1, 1)) := by
    apply Prod.ext
    · rw [getD_fst_of_map _ _ (hStringAt_map_fst x 0), hlen]
      exact tileSeqAux_getD_p x none _ (by omega) hwl
    · rw [← hX, lastPosOf_eq_getD]
  have v0 := h 0 hpos 0 (mem 0 hpos 0 (by rw [ht0]; decide))
  have v1 := h 0 hpos e₁ (mem 0 hpos e₁ (by rw [ht0]; decide))
  have vX := h ((hStringAt x 0).length - 1) (by omega) X (mem ((hStringAt x 0).length - 1) (by omega) X (by
    rw [htl]
    have : X - (X - (1, 1)) = (1, 1) := by ext <;> simp
    rw [this]
    exact (by decide : ((1 : ℤ), (1 : ℤ)) ∈ tileShape ZTile.zero)))
  have vX' := h ((hStringAt x 0).length - 1) (by omega) (X - e₂) (mem ((hStringAt x 0).length - 1) (by omega) (X - e₂) (by
    rw [htl]
    have : X - e₂ - (X - (1, 1)) = (1, 0) := by ext <;> simp
    rw [this]
    exact (by decide : ((1 : ℤ), (0 : ℤ)) ∈ tileShape ZTile.zero)))
  rw [ht0] at v0 v1
  rw [htl] at vX vX'
  have e1 : X - (X - (1, 1)) = (1, 1) := by ext <;> simp
  have e2 : X - e₂ - (X - (1, 1)) = (1, 0) := by ext <;> simp
  rw [e1] at vX
  rw [e2] at vX'
  obtain ⟨hσ1, hσ2⟩ := hσ
  simp only [ptDot, sub_zero] at v0 v1 vX vX'
  have z1 : zTileOdo ZTile.one (0 : GInt) = 0 := by decide
  have z2 : zTileOdo ZTile.one e₁ = 0 := by decide
  have z3 : zTileOdo ZTile.zero ((1 : ℤ), (1 : ℤ)) = 0 := by decide
  have z4 : zTileOdo ZTile.zero ((1 : ℤ), (0 : ℤ)) = 0 := by decide
  rw [z1] at v0
  rw [z2] at v1
  rw [z3] at vX
  rw [z4] at vX'
  have ha1 : α.1 = 0 := by
    simp only [Prod.fst_zero, Prod.snd_zero, mul_zero, add_zero] at v0 v1
    simp only [e₁] at v1
    linarith
  have ha2 : α.2 = 0 := by
    simp only [Prod.fst_sub, Prod.snd_sub, e₂] at vX'
    simp only [e₂] at hσ2
    rw [ha1] at vX vX'
    linarith
  refine ⟨β, fun k hk y hy => ?_, ?_, ?_, ?_, ?_⟩
  · rw [h k hk y (mem k hk y hy)]
    simp [ptDot, ha1, ha2]
  · simp only [Prod.fst_zero, Prod.snd_zero, mul_zero, add_zero] at v0
    linarith
  · simp only [e₁] at v1 ⊢
    rw [ha1] at v1
    linarith
  · rw [ha1, ha2] at vX
    linarith
  · rw [ha1, ha2] at vX'
    simp only [e₂] at vX' ⊢
    linarith

/-- Two integers in the same ceiling interval are equal. -/
theorem ceil_unique (l J c m : ℤ) (hl : 0 < l) (h1 : l * c - l < J) (h2 : J ≤ l * c) (h3 : l * m - l < J)
    (h4 : J ≤ l * m) : c = m := by
  have a : c < m + 1 := by
    by_contra hc
    rw [not_lt] at hc
    nlinarith
  have b : m < c + 1 := by
    by_contra hc
    rw [not_lt] at hc
    nlinarith
  omega

/-! ### The optional interface `(P^-, Q^{+,2})`, `W_1` even -/

theorem phase_zero_of (w : Word) (hph : phase w ≠ 1) : phase w = 0 := by
  have : phase w < 2 := by unfold phase; exact Nat.mod_lt _ (by norm_num)
  omega

/-- **The triangle identity at `(P^-, Q^{+,2})` for `W_1` even.** -/
theorem triOdd_ef_one (w u1 u2 : Word) (hph : phase w ≠ 1)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (oP oQ : ℤ × ℤ → ℤ) (c : ℕ → ℤ)
    (hRP : RespectsTiles .horizontal false (hStringAt (hWordOf u1 false) 0) oP)
    (hRQ : RespectsTiles .horizontal false (hStringAt (hWordOf u2 true) 0) oQ)
    (hsP : SigmaZero oP (texV1Odd (parentsAt w).odd)) (hsQ : SigmaZero oQ (texV1Even (parentsAt w).even)) :
    (∃ z, z ∈ mOdd w u1 u2 1 ∧ z ∈ mOdd w u1 u2 3) → ∃ z, z ∈ mOdd w u1 u2 1 ∧ z ∈ mOdd w u1 u2 3 ∧
        placedOdd w oP oQ c 1 z - placedOdd w oP oQ c 3 z =
          (placedOdd w oP oQ c 1 (texV2 (parentsAt w).even + e₁) -
            placedOdd w oP oQ c 2 (texV2 (parentsAt w).even + e₁)) +
          (placedOdd w oP oQ c 2 (texV1Even (parentsAt w).even) -
            placedOdd w oP oQ c 3 (texV1Even (parentsAt w).even)) := by
  rintro ⟨z0, hz1, hz3⟩
  have hP := oddP_ef w hph
  have hQ := oddQ_ef w hph
  -- the overlap gives `2 d_p > d_q`
  have hd1 := mOdd_sub w u1 u2 1 hz1
  have hd3 := mOdd_sub w u1 u2 3 hz3
  simp only [dOdd, pieceSet, hP, hQ] at hd1 hd3
  simp at hd1 hd3
  have b1 := box_shift_odd u1 _ z0 hd1
  have b3 := box_shift_even u2 _ z0 hd3
  rw [← hp] at b1
  rw [← hq] at b3
  simp only [texV2, texV1Even] at b1 b3
  have hov : (parentsAt w).even.den + 1 ≤ 2 * (parentsAt w).odd.den := by omega
  -- the fractions
  have hdet := SiteScope.det_parentsAt w
  rw [phase_zero_of w hph] at hdet
  simp only [Fraction.det, Nat.cast_zero, mul_zero, zero_sub] at hdet
  have hpl := SiteHullOdd.curO_pos_lt u1
  have hql := SiteHullEven.curE_pos_lt u2
  have hqe := SiteHullEven.curE_num_add_den_even u2
  have hcu : SiteInduction.curO u1 = fracOdd u1 := rfl
  have hce : SiteInduction.curE u2 = fracEven u2 := rfl
  rw [hcu, ← hp] at hpl
  rw [hce, ← hq] at hql hqe
  set np := (parentsAt w).odd.num with hnp
  set dp := (parentsAt w).odd.den with hdp
  set nq := (parentsAt w).even.num with hnq
  set dq := (parentsAt w).even.den with hdq
  have hnq2 : nq ≤ 2 * np := by nlinarith
  -- the ceiling word of `P`
  have hcw := SiteHullOdd.cw_childP u1
  rw [hcu, ← hp] at hcw
  obtain ⟨hh, hl⟩ := hWordOf_head_last u1 false
  obtain ⟨t, ht⟩ : ∃ t, hWordOf u1 false = Letter.q :: t := by
    cases h : hWordOf u1 false with
    | nil => rw [h] at hh; simp at hh
    | cons a t =>
      rw [h] at hh
      simp only [List.head?_cons, Option.some.injEq] at hh
      exact ⟨t, by rw [hh]⟩
  rw [ht] at hcw hh hl hRP
  obtain ⟨hxl, hxc⟩ := hcw
  set lQ : ℕ := ((dq + nq) / 2).toNat with hlQdef
  have hlQ : 2 * (lQ : ℤ) = dq + nq := by
    rw [hlQdef, Int.toNat_of_nonneg (by omega)]
    omega
  have hidx : lQ + 1 ≤ (Letter.q :: t).length := by
    have : (lQ : ℤ) + 1 ≤ ((Letter.q :: t).length : ℤ) := by rw [hxl]; omega
    exact_mod_cast this
  have hl0 : 0 < dp + np := by omega
  have c0 : qPrefix (Letter.q :: t) lQ = nq := by
    obtain ⟨h1, h2⟩ := hxc lQ (by omega)
    exact ceil_unique (dp + np) ((lQ : ℤ) * (2 * np)) _ nq hl0 h1 h2 (by nlinarith) (by nlinarith)
  have c1 : qPrefix (Letter.q :: t) (lQ + 1) = nq + 1 := by
    obtain ⟨h1, h2⟩ := hxc (lQ + 1) (by push_cast; omega)
    push_cast at h1 h2
    exact ceil_unique (dp + np) (((lQ : ℤ) + 1) * (2 * np)) _ (nq + 1) hl0 h1 h2 (by nlinarith) (by nlinarith)
  have hk : lQ < (Letter.q :: t).length := by omega
  have hlet : (Letter.q :: t).getD lQ Letter.p = Letter.q := by
    have h := count_take_succ (Letter.q :: t) lQ hk
    rw [c0, c1] at h
    split_ifs at h with h'
    · exact h'
    · omega
  -- the tile of `P` at `U`
  have htile := fwd_tile t lQ hk
  rw [c1] at htile
  have hposU : (2 * (lQ : ℤ) + 1 - (nq + 1), nq + 1 - 1) = texV1Even (parentsAt w).even := by
    simp only [texV1Even]
    ext <;> simp <;> omega
  rw [hposU] at htile
  have htype := tileSeq_getD_q (Letter.q :: t) lQ hk hlet
  -- the normalised parents
  have hXP := TexVPositions.lastPos_hWordOf_false_tex u1
  rw [← hp, ht] at hXP
  obtain ⟨βP, hβP, vP0, vP1, -, -⟩ := fwd_formula_norm (Letter.q :: t) oP _ hh hl hXP hRP hsP
  have hXQ := TexVPositions.lastPos_hWordOf_true_tex u2
  rw [← hq] at hXQ
  obtain ⟨hhq, hlq⟩ := hWordOf_head_last u2 true
  obtain ⟨βQ, -, vQ0, -, vQU, -⟩ := fwd_formula_norm (hWordOf u2 true) oQ _ hhq hlq hXQ hRQ hsQ
  have vPU : oP (texV1Even (parentsAt w).even + e₁) = βP := by
    have hlen : lQ < (hStringAt (Letter.q :: t) 0).length := by rw [hStringAt_length']; exact hk
    have hmem : texV1Even (parentsAt w).even + e₁ - ((hStringAt (Letter.q :: t) 0).getD lQ (ZTile.zero, 0)).2 ∈
        tileShape ((hStringAt (Letter.q :: t) 0).getD lQ (ZTile.zero, 0)).1 := by
      rw [htile]
      simp only [add_sub_cancel_left]
      rcases htype with h | h
      · rw [h]; exact (by decide : e₁ ∈ tileShape ZTile.one)
      · rw [h]; exact (by decide : e₁ ∈ tileShape ZTile.oneD)
    rw [hβP lQ hlen _ hmem, htile]
    simp only [add_sub_cancel_left]
    rcases htype with h | h
    · rw [h]
      have : zTileOdo ZTile.one e₁ = 0 := by decide
      exact this.symm ▸ zero_add βP
    · rw [h]
      have : zTileOdo ZTile.oneD e₁ = 0 := by decide
      exact this.symm ▸ zero_add βP
  -- the point `z* = U + V + 1`
  refine ⟨texV1Even (parentsAt w).even + (texV2 (parentsAt w).even + e₁), ?_, ?_, ?_⟩
  · simp only [mOdd, pieceSet, hP]
    simp only [List.length_cons, List.length_nil, List.getD_cons_succ, List.getD_cons_zero]
    refine mem_shift _ _ _ (texV1Even (parentsAt w).even + e₁) ?_ (by abel)
    apply SiteHullOdd.mem_marksOdd_of_sh
    rw [ht]
    have hs := fwd_mem_sites t lQ hk hlet (1, 0) (by simp)
    rw [c1] at hs
    convert hs using 1
    rw [← hposU]
  · simp only [mOdd, pieceSet, hP, hQ]
    simp only [List.length_cons, List.length_nil, List.getD_cons_succ, List.getD_cons_zero]
    refine mem_shift _ _ _ (texV2 (parentsAt w).even + e₁) ?_ (by abel)
    have h := (ClosedPathContacts.corner_marks_even u2).2.2.2.2.1
    rw [← hq] at h
    exact h
  · have h1 : IsPiece (placedOdd w oP oQ c 1) oP (texV2 (parentsAt w).even)
        ((parentsAt w).even.num, -(parentsAt w).even.den) (c 1) := fun z => by simp [placedOdd, hP, affOdd]
    have h2 : IsPiece (placedOdd w oP oQ c 2) oQ 0 0 (c 2) := fun z => by simp [placedOdd, hQ, affOdd]
    have h3 : IsPiece (placedOdd w oP oQ c 3) oQ (texV1Even (parentsAt w).even) 0 (c 3) := fun z => by
      simp [placedOdd, hQ, affOdd]
    rw [piece_val h1 _ (texV1Even (parentsAt w).even + e₁) (by abel),
      piece_val h3 _ (texV2 (parentsAt w).even + e₁) (by abel),
      piece_val h1 (texV2 (parentsAt w).even + e₁) e₁ (by abel),
      piece_val h2 (texV2 (parentsAt w).even + e₁) (texV2 (parentsAt w).even + e₁) (by abel),
      piece_val h2 (texV1Even (parentsAt w).even) (texV1Even (parentsAt w).even) (by abel),
      piece_val h3 (texV1Even (parentsAt w).even) 0 (by abel), vPU, vP1, vQU, vQ0]
    simp only [dot2, texV1Even, texV2, e₁, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero]
    ring

/-! ### The optional interface `(P^-, Q^{+,1})`, `W_1` odd -/

theorem tile_has_e1 (t : ZTile) : e₁ ∈ tileShape t ∧ zTileOdo t e₁ = 0 := by
  cases t <;> decide

/-- **The triangle identity at `(P^-, Q^{+,1})` for `W_1` odd.** If the copies meet then `n_q + 1 ≤ 2 n_p`; with
`n_p d_q - n_q d_p = 1` the bottom string of `P` has a tile at `A - U - 1 - i` (index `|w_h(p)| - |w_h(q)| - 1`, with `2 n_p - n_q`
letters `q` up to it), and `z* = U + V + A - i` lies on it (relative to `P^-`) and on the last top corner of `Q^{+,1}`. -/
theorem triOdd_of_one (w u1 u2 : Word) (hph : phase w = 1)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (oP oQ : ℤ × ℤ → ℤ) (c : ℕ → ℤ)
    (hRP : RespectsTiles .horizontal false (hStringAt (hWordOf u1 false) 0) oP)
    (hRQ : RespectsTiles .horizontal false (hStringAt (hWordOf u2 true) 0) oQ)
    (hsP : SigmaZero oP (texV1Odd (parentsAt w).odd)) (hsQ : SigmaZero oQ (texV1Even (parentsAt w).even)) :
    (∃ z, z ∈ mOdd w u1 u2 1 ∧ z ∈ mOdd w u1 u2 2) → ∃ z, z ∈ mOdd w u1 u2 1 ∧ z ∈ mOdd w u1 u2 2 ∧
        placedOdd w oP oQ c 1 z - placedOdd w oP oQ c 2 z =
          (placedOdd w oP oQ c 1 (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even +
              texV2 (parentsAt w).even + (texV1Odd (parentsAt w).odd - e₂)) -
            placedOdd w oP oQ c 3 (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even +
              texV2 (parentsAt w).even + (texV1Odd (parentsAt w).odd - e₂))) +
          (placedOdd w oP oQ c 3 (texV1Odd (parentsAt w).odd + texV1Even (parentsAt w).even) -
            placedOdd w oP oQ c 2 (texV1Odd (parentsAt w).odd + texV1Even (parentsAt w).even)) := by
  rintro ⟨z0, hz1, hz2⟩
  have hP := oddP_of w hph
  have hQ := oddQ_of w hph
  -- the overlap gives `n_q + 1 ≤ 2 n_p`
  have hd1 := mOdd_sub w u1 u2 1 hz1
  have hd2 := mOdd_sub w u1 u2 2 hz2
  simp only [dOdd, pieceSet, hP, hQ] at hd1 hd2
  simp at hd1 hd2
  have b1 := box_shift_odd u1 _ z0 hd1
  have b2 := box_shift_even u2 _ z0 hd2
  rw [← hp] at b1
  rw [← hq] at b2
  simp only [texV2, texV1Even, texV1Odd, Prod.fst_add, Prod.snd_add] at b1 b2
  have hov : (parentsAt w).even.num + 1 ≤ 2 * (parentsAt w).odd.num := by omega
  -- the fractions
  have hdet := SiteScope.det_parentsAt w
  rw [hph] at hdet
  simp only [Fraction.det, Nat.cast_one, mul_one] at hdet
  have hpl := SiteHullOdd.curO_pos_lt u1
  have hql := SiteHullEven.curE_pos_lt u2
  have hqe := SiteHullEven.curE_num_add_den_even u2
  have hcu : SiteInduction.curO u1 = fracOdd u1 := rfl
  have hce : SiteInduction.curE u2 = fracEven u2 := rfl
  rw [hcu, ← hp] at hpl
  rw [hce, ← hq] at hql hqe
  set np := (parentsAt w).odd.num with hnp
  set dp := (parentsAt w).odd.den with hdp
  set nq := (parentsAt w).even.num with hnq
  set dq := (parentsAt w).even.den with hdq
  have hdq2 : dq + 1 ≤ 2 * dp := by nlinarith
  -- the ceiling word of `P`
  have hcw := SiteHullOdd.cw_childP u1
  rw [hcu, ← hp] at hcw
  obtain ⟨hh, hl⟩ := hWordOf_head_last u1 false
  obtain ⟨t, ht⟩ : ∃ t, hWordOf u1 false = Letter.q :: t := by
    cases h : hWordOf u1 false with
    | nil => rw [h] at hh; simp at hh
    | cons a t =>
      rw [h] at hh
      simp only [List.head?_cons, Option.some.injEq] at hh
      exact ⟨t, by rw [hh]⟩
  rw [ht] at hcw hh hl hRP
  obtain ⟨hxl, hxc⟩ := hcw
  set lQ : ℕ := ((dq + nq) / 2).toNat with hlQdef
  have hlQ : 2 * (lQ : ℤ) = dq + nq := by
    rw [hlQdef, Int.toNat_of_nonneg (by omega)]
    omega
  set j : ℕ := (Letter.q :: t).length - lQ - 1 with hjdef
  have hlen1 : lQ + 1 ≤ (Letter.q :: t).length := by
    have : (lQ : ℤ) + 1 ≤ ((Letter.q :: t).length : ℤ) := by rw [hxl]; omega
    exact_mod_cast this
  have hjZ : (j : ℤ) + 1 = dp + np - lQ := by
    have : (j : ℤ) = ((Letter.q :: t).length : ℤ) - lQ - 1 := by rw [hjdef]; push_cast [Nat.sub_sub]; omega
    rw [this, hxl]
    ring
  have hl0 : 0 < dp + np := by omega
  have c1 : qPrefix (Letter.q :: t) (j + 1) = 2 * np - nq := by
    obtain ⟨h1, h2⟩ := hxc (j + 1) (by push_cast; omega)
    push_cast at h1 h2
    rw [hjZ] at h1 h2
    exact ceil_unique (dp + np) ((dp + np - lQ) * (2 * np)) _ (2 * np - nq) hl0 h1 h2 (by nlinarith) (by nlinarith)
  have hk : j < (Letter.q :: t).length := by omega
  -- the tile of `P` at `A - U - 1 - i`
  have htile := fwd_tile t j hk
  rw [c1] at htile
  have hpos : (2 * (j : ℤ) + 1 - (2 * np - nq), 2 * np - nq - 1) + e₁ =
      texV1Odd (parentsAt w).odd - e₂ - texV1Even (parentsAt w).even := by
    simp only [texV1Odd, texV1Even, e₁, e₂]
    ext <;> simp <;> omega
  -- the normalised parents
  have hXP := TexVPositions.lastPos_hWordOf_false_tex u1
  rw [← hp, ht] at hXP
  obtain ⟨βP, hβP, -, -, -, vPA'⟩ := fwd_formula_norm (Letter.q :: t) oP _ hh hl hXP hRP hsP
  have hXQ := TexVPositions.lastPos_hWordOf_true_tex u2
  rw [← hq] at hXQ
  obtain ⟨hhq, hlq⟩ := hWordOf_head_last u2 true
  obtain ⟨βQ, -, vQ0, -, vQU, -⟩ := fwd_formula_norm (hWordOf u2 true) oQ _ hhq hlq hXQ hRQ hsQ
  have vPz : oP (texV1Odd (parentsAt w).odd - e₂ - texV1Even (parentsAt w).even) = βP := by
    have hlen : j < (hStringAt (Letter.q :: t) 0).length := by rw [hStringAt_length']; exact hk
    have hrel : texV1Odd (parentsAt w).odd - e₂ - texV1Even (parentsAt w).even -
        ((hStringAt (Letter.q :: t) 0).getD j (ZTile.zero, 0)).2 = e₁ := by
      rw [htile, ← hpos]
      abel
    have hmem := (tile_has_e1 ((hStringAt (Letter.q :: t) 0).getD j (ZTile.zero, 0)).1).1
    rw [← hrel] at hmem
    rw [hβP j hlen _ hmem, hrel, (tile_has_e1 _).2, zero_add]
  -- the point `z* = U + V + A - i`
  refine ⟨texV1Even (parentsAt w).even + texV2 (parentsAt w).even + (texV1Odd (parentsAt w).odd - e₂), ?_, ?_, ?_⟩
  · simp only [mOdd, pieceSet, hP]
    simp only [List.length_cons, List.length_nil, List.getD_cons_succ, List.getD_cons_zero]
    refine mem_shift _ _ _ (texV1Odd (parentsAt w).odd - e₂ - texV1Even (parentsAt w).even) ?_ (by abel)
    apply SiteHullOdd.mem_marksOdd_of_sh
    rw [ht]
    have hs := fwd_mem_sites_any t j hk (1, 0) (by simp)
    rw [c1] at hs
    convert hs using 1
    rw [← hpos]
  · have hm2 : mOdd w u1 u2 2 = shiftS (marksEven u2) (texV1Odd (parentsAt w).odd) := by
      simp [mOdd, pieceSet, hP, hQ]
    rw [hm2]
    refine mem_shift _ _ _ (texV1Even (parentsAt w).even + texV2 (parentsAt w).even - e₂) ?_ (by abel)
    have h := (ClosedPathContacts.corner_marks_even u2).2.2.2.2.2.2.2
    rw [← hq] at h
    exact h
  · have h1 : IsPiece (placedOdd w oP oQ c 1) oP
        (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even + texV2 (parentsAt w).even)
        ((parentsAt w).even.num, -(parentsAt w).even.den) (c 1) := fun z => by simp [placedOdd, hP, affOdd]
    have h2 : IsPiece (placedOdd w oP oQ c 2) oQ (texV1Odd (parentsAt w).odd) 0 (c 2) := fun z => by
      simp [placedOdd, hQ, affOdd]
    have h3 : IsPiece (placedOdd w oP oQ c 3) oQ (texV1Odd (parentsAt w).odd + texV1Even (parentsAt w).even) 0
        (c 3) := fun z => by simp [placedOdd, hQ, affOdd]
    rw [piece_val h1 _ (texV1Odd (parentsAt w).odd - e₂ - texV1Even (parentsAt w).even) (by abel),
      piece_val h2 _ (texV1Even (parentsAt w).even + texV2 (parentsAt w).even - e₂) (by abel),
      piece_val h1 _ (texV1Odd (parentsAt w).odd - e₂) (by abel),
      piece_val h3 _ (texV1Even (parentsAt w).even + texV2 (parentsAt w).even - e₂) (by abel),
      piece_val h3 (texV1Odd (parentsAt w).odd + texV1Even (parentsAt w).even) 0 (by abel),
      piece_val h2 (texV1Odd (parentsAt w).odd + texV1Even (parentsAt w).even) (texV1Even (parentsAt w).even)
        (by abel), vPz, vPA', vQU, vQ0]
    simp only [dot2, texV1Even, texV1Odd, texV2, e₂, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
      Prod.fst_zero, Prod.snd_zero]
    ring

/-! ### A normalised parent along its top string -/

theorem relOdo_rev_one (t : ZTile) (ht : t = ZTile.one ∨ t = ZTile.oneD) :
    relOdo revStr t ((0 : ℤ), (1 : ℤ)) = 0 ∧ relOdo revStr t ((1 : ℤ), (1 : ℤ)) = 0 := by
  rcases ht with rfl | rfl <;> decide

theorem relOdo_rev_zero : relOdo revStr ZTile.zero ((0 : ℤ), (1 : ℤ)) = 0 ∧
    relOdo revStr ZTile.zero ((0 : ℤ), (2 : ℤ)) = 0 := by
  decide

/-- **A normalised parent along its top string**: on the reversed horizontal string from `Y + 1 - 2i`, the odometer is the
relative reversed base odometer of each tile (`relOdo revStr`) plus the affine function `a_{n/d,2} = (n, -d)` and one constant.
The affine factor is read at the two top corners from the corner differences. -/
theorem top_formula_norm (wh wv : BinaryWord) (S : GInt → ℤ) (n d : ℤ) (X Y : GInt)
    (hh : wh.head? = some .q) (hl : wh.getLast? = some .p) (hX : lastPosOf (hStringAt wh 0) = X - (1, 1))
    (hY : lastPosOf (vRevStringAt wv.reverse 0) = Y + (1, -2))
    (hC : RespectsTiles .horizontal true (hRevStringAt wh.reverse (lastPosOf (vRevStringAt wv.reverse 0))) S)
    (hcd : CornerDiffs S X Y n d) (hσ : SigmaZero S X) :
    ∃ β : ℤ, ∀ k < wh.length, ∀ y : GInt,
      y - ((hRevStringAt wh.reverse (Y + (1, -2))).getD k (ZTile.zero, 0)).2 ∈
        tileShape ((hRevStringAt wh.reverse (Y + (1, -2))).getD k (ZTile.zero, 0)).1 →
      S y = relOdo revStr ((hRevStringAt wh.reverse (Y + (1, -2))).getD k (ZTile.zero, 0)).1
        (y - ((hRevStringAt wh.reverse (Y + (1, -2))).getD k (ZTile.zero, 0)).2) + dot2 (n, -d) y + β := by
  rw [hY] at hC
  obtain ⟨α, β, h⟩ := reversed_horizontal_formula wh.reverse (Y + (1, -2)) S hC
  set L := hRevStringAt wh.reverse (Y + (1, -2)) with hL
  have hne : wh ≠ [] := by
    rintro rfl
    simp at hh
  have hrne : wh.reverse ≠ [] := by simpa using hne
  have hlen : L.length = wh.length := by rw [hL, hRevStringAt_length, List.length_reverse]
  have hpos : 0 < wh.length := List.length_pos_of_ne_nil hne
  have mem : ∀ k < wh.length, ∀ y : GInt, y - (L.getD k (ZTile.zero, 0)).2 ∈ tileShape (L.getD k (ZTile.zero, 0)).1 →
      y ∈ (famOf revStr L).dom k := by
    intro k _ y hy
    rw [mem_dom_iff, famOf_tile]
    exact hy
  have hwr0 : wh.reverse.getD 0 Letter.p = Letter.p := by
    rw [List.getD_eq_getElem?_getD, ← List.head?_eq_getElem?, List.head?_reverse, hl]
    rfl
  have ht0 : L.getD 0 (ZTile.zero, 0) = (ZTile.zero, Y + (1, -2)) := by
    apply Prod.ext
    · rw [hL, hRevStringAt_getD_fst, tileSeq_getD_zero_head wh.reverse hrne hwr0]
    · rw [hL, hRevStringAt_getD_snd_zero wh.reverse _ hrne]
  have hwrl : wh.reverse.getD (wh.reverse.length - 1) Letter.p = Letter.q := by
    rw [List.getD_eq_getElem?_getD, ← List.getLast?_eq_getElem?, List.getLast?_reverse, hh]
    rfl
  have hCpos : (L.getD (wh.length - 1) (ZTile.zero, 0)).2 = X + Y + (0, -2) := by
    have h1 := hRev_lastPos_reverse wh (Y + (1, -2)) hh hl
    rw [lastPosOf_eq_getD, ← hL, hlen, hX] at h1
    rw [h1]
    ext <;> simp <;> ring
  have hCt : (L.getD (wh.length - 1) (ZTile.zero, 0)).1 = ZTile.one ∨
      (L.getD (wh.length - 1) (ZTile.zero, 0)).1 = ZTile.oneD := by
    rw [hL, hRevStringAt_getD_fst, ← List.length_reverse (as := wh)]
    exact tileSeq_getD_q wh.reverse _ (by rw [List.length_reverse]; omega) hwrl
  have hlast : wh.length - 1 < wh.length := by omega
  -- the four corner values
  have vD1 := h 0 (by rw [hlen]; exact hpos) (Y + e₁) (mem 0 hpos _ (by
    rw [ht0]
    have : Y + e₁ - (Y + (1, -2)) = (0, 2) := by ext <;> (simp; try ring)
    rw [this]
    exact (by decide : ((0 : ℤ), (2 : ℤ)) ∈ tileShape ZTile.zero)))
  have vD0 := h 0 (by rw [hlen]; exact hpos) (Y + e₁ - e₂) (mem 0 hpos _ (by
    rw [ht0]
    have : Y + e₁ - e₂ - (Y + (1, -2)) = (0, 1) := by ext <;> (simp; try ring)
    rw [this]
    exact (by decide : ((0 : ℤ), (1 : ℤ)) ∈ tileShape ZTile.zero)))
  have hCm : ∀ u : GInt, u = ((1 : ℤ), (1 : ℤ)) ∨ u = ((0 : ℤ), (1 : ℤ)) →
      u ∈ tileShape (L.getD (wh.length - 1) (ZTile.zero, 0)).1 := by
    intro u hu
    rcases hCt with h' | h' <;> rw [h'] <;> rcases hu with rfl | rfl <;> decide
  have vC1 := h (wh.length - 1) (by rw [hlen]; exact hlast) (X + Y + e₁ - e₂) (mem _ hlast _ (by
    rw [hCpos]
    have : X + Y + e₁ - e₂ - (X + Y + (0, -2)) = (1, 1) := by ext <;> (simp; try ring)
    rw [this]
    exact hCm _ (Or.inl rfl)))
  have vC0 := h (wh.length - 1) (by rw [hlen]; exact hlast) (X + Y - e₂) (mem _ hlast _ (by
    rw [hCpos]
    have : X + Y - e₂ - (X + Y + (0, -2)) = (0, 1) := by ext <;> (simp; try ring)
    rw [this]
    exact hCm _ (Or.inr rfl)))
  rw [ht0] at vD1 vD0
  rw [hCpos] at vC1 vC0
  have e1 : Y + e₁ - (Y + (1, -2)) = (0, 2) := by ext <;> (simp; try ring)
  have e2 : Y + e₁ - e₂ - (Y + (1, -2)) = (0, 1) := by ext <;> (simp; try ring)
  have e3 : X + Y + e₁ - e₂ - (X + Y + (0, -2)) = (1, 1) := by ext <;> (simp; try ring)
  have e4 : X + Y - e₂ - (X + Y + (0, -2)) = (0, 1) := by ext <;> (simp; try ring)
  rw [e1, relOdo_rev_zero.2] at vD1
  rw [e2, relOdo_rev_zero.1] at vD0
  rw [e3, (relOdo_rev_one _ hCt).2] at vC1
  rw [e4, (relOdo_rev_one _ hCt).1] at vC0
  obtain ⟨c1, c2⟩ := hcd
  obtain ⟨s1, s2⟩ := hσ
  simp only [ptDot, e₁, e₂, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at vD1 vD0 vC1 vC0 c1 c2 s1 s2
  have ha1 : α.1 = n := by linarith
  have ha2 : α.2 = -d := by linarith
  refine ⟨β, fun k hk y hy => ?_⟩
  rw [h k (by rw [hlen]; exact hk) y (mem k hk y hy)]
  simp only [ptDot, dot2, ha1, ha2]

theorem getD_reverse_eq (l : BinaryWord) (i : ℕ) (hi : i < l.length) :
    l.reverse.getD i Letter.p = l.getD (l.length - 1 - i) Letter.p := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hi),
    List.getElem?_eq_getElem (by omega), List.getElem_reverse]

/-! ### The optional interface `(P^+, Q^{-,1})`, `W_1` even -/

/-- **The triangle identity at `(P^+, Q^{-,1})` for `W_1` even**, the half-turn of `triOdd_ef_one`: if the copies meet then
`2 d_p > d_q`, and `z* = U + A + B - i` lies (relative to `P^+`) on the top tile of `P` that is the half-turn of the one tile at
`U` of its bottom string, and on the second bottom corner of `Q^{-,1}`. -/
theorem triOdd_ef_two (w u1 u2 : Word) (hph : phase w ≠ 1)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (oP oQ : ℤ × ℤ → ℤ) (c : ℕ → ℤ) (TP : Finset Site)
    (hRP : SurgicalWeak.RespectsAnchored TP (hWordOf u1 false) (vWordOf u1 false) oP)
    (hRQ : RespectsTiles .horizontal false (hStringAt (hWordOf u2 true) 0) oQ)
    (hsP : SigmaZero oP (texV1Odd (parentsAt w).odd)) (hsQ : SigmaZero oQ (texV1Even (parentsAt w).even)) :
    (∃ z, z ∈ mOdd w u1 u2 0 ∧ z ∈ mOdd w u1 u2 4) → ∃ z, z ∈ mOdd w u1 u2 0 ∧ z ∈ mOdd w u1 u2 4 ∧
        placedOdd w oP oQ c 0 z - placedOdd w oP oQ c 4 z =
          (placedOdd w oP oQ c 0 (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even +
              (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - e₂)) -
            placedOdd w oP oQ c 5 (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even +
              (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - e₂))) +
          (placedOdd w oP oQ c 5 (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd +
              texV1Even (parentsAt w).even) -
            placedOdd w oP oQ c 4 (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd +
              texV1Even (parentsAt w).even)) := by
  rintro ⟨z0, hz0, hz4⟩
  have hP := oddP_ef w hph
  have hQ := oddQ_ef w hph
  have hd0 := mOdd_sub w u1 u2 0 hz0
  have hd4 := mOdd_sub w u1 u2 4 hz4
  simp only [dOdd, pieceSet, hP, hQ] at hd0 hd4
  simp at hd0 hd4
  have b0 := box_shift_odd u1 _ z0 hd0
  have b4 := box_shift_even u2 _ z0 hd4
  rw [← hp] at b0
  rw [← hq] at b4
  simp only [texV2, texV1Even, texV1Odd, Prod.fst_add, Prod.snd_add] at b0 b4
  have hov : (parentsAt w).even.den + 1 ≤ 2 * (parentsAt w).odd.den := by omega
  have hdet := SiteScope.det_parentsAt w
  rw [phase_zero_of w hph] at hdet
  simp only [Fraction.det, Nat.cast_zero, mul_zero, zero_sub] at hdet
  have hpl := SiteHullOdd.curO_pos_lt u1
  have hql := SiteHullEven.curE_pos_lt u2
  have hqe := SiteHullEven.curE_num_add_den_even u2
  have hcu : SiteInduction.curO u1 = fracOdd u1 := rfl
  have hce : SiteInduction.curE u2 = fracEven u2 := rfl
  rw [hcu, ← hp] at hpl
  rw [hce, ← hq] at hql hqe
  -- the parents along their strings
  have hcd := ClosedPathStandard.cornerDiffs_odd u1 TP oP hRP
  rw [← hp] at hcd
  obtain ⟨-, hRPb, hRPt, -, -⟩ := hRP
  obtain ⟨hh0, hl0⟩ := hWordOf_head_last u1 false
  have hXP := TexVPositions.lastPos_hWordOf_false_tex u1
  rw [← hp] at hXP
  have hYP := StdCornerAnchors.stdAnchorY_odd u1
  rw [← hp] at hYP
  obtain ⟨βT, hβT⟩ := top_formula_norm (hWordOf u1 false) (vWordOf u1 false) oP _ _ _ _ hh0 hl0 hXP hYP hRPt hcd hsP
  have hXQ := TexVPositions.lastPos_hWordOf_true_tex u2
  rw [← hq] at hXQ
  obtain ⟨hhq, hlq⟩ := hWordOf_head_last u2 true
  obtain ⟨βQ, -, vQ0, -, vQU, -⟩ := fwd_formula_norm (hWordOf u2 true) oQ _ hhq hlq hXQ hRQ hsQ
  set np := (parentsAt w).odd.num with hnp
  set dp := (parentsAt w).odd.den with hdp
  set nq := (parentsAt w).even.num with hnq
  set dq := (parentsAt w).even.den with hdq
  have hnq2 : nq ≤ 2 * np := by nlinarith
  -- the ceiling word of `P`
  have hcw := SiteHullOdd.cw_childP u1
  rw [hcu, ← hp] at hcw
  obtain ⟨t, ht⟩ : ∃ t, hWordOf u1 false = Letter.q :: t := by
    cases h : hWordOf u1 false with
    | nil => rw [h] at hh0; simp at hh0
    | cons a t =>
      rw [h] at hh0
      simp only [List.head?_cons, Option.some.injEq] at hh0
      exact ⟨t, by rw [hh0]⟩
  rw [ht] at hcw hβT
  have htot := ceil_total _ _ _ hcw (by omega)
  obtain ⟨hxl, hxc⟩ := hcw
  set lQ : ℕ := ((dq + nq) / 2).toNat with hlQdef
  have hlQ : 2 * (lQ : ℤ) = dq + nq := by
    rw [hlQdef, Int.toNat_of_nonneg (by omega)]
    omega
  have hidx : lQ + 1 ≤ (Letter.q :: t).length := by
    have : (lQ : ℤ) + 1 ≤ ((Letter.q :: t).length : ℤ) := by rw [hxl]; omega
    exact_mod_cast this
  have hl0' : 0 < dp + np := by omega
  have c1 : qPrefix (Letter.q :: t) (lQ + 1) = nq + 1 := by
    obtain ⟨h1, h2⟩ := hxc (lQ + 1) (by push_cast; omega)
    push_cast at h1 h2
    exact ceil_unique (dp + np) (((lQ : ℤ) + 1) * (2 * np)) _ (nq + 1) hl0' h1 h2 (by nlinarith) (by nlinarith)
  have c0 : qPrefix (Letter.q :: t) lQ = nq := by
    obtain ⟨h1, h2⟩ := hxc lQ (by omega)
    exact ceil_unique (dp + np) ((lQ : ℤ) * (2 * np)) _ nq hl0' h1 h2 (by nlinarith) (by nlinarith)
  have hk : lQ < (Letter.q :: t).length := by omega
  have hlet : (Letter.q :: t).getD lQ Letter.p = Letter.q := by
    have h := count_take_succ (Letter.q :: t) lQ hk
    rw [c0, c1] at h
    split_ifs at h with h'
    · exact h'
    · omega
  -- the bottom point `U + 1` of `P`, and its half-turn on the top string
  have hposU : (2 * (lQ : ℤ) + 1 - (nq + 1), nq + 1 - 1) + (1, 0) = texV1Even (parentsAt w).even + e₁ := by
    simp only [texV1Even, e₁]
    ext <;> simp <;> omega
  set k0 : ℕ := (Letter.q :: t).length - 1 - lQ with hk0def
  have hk0 : k0 < (Letter.q :: t).length := by omega
  have hk0r : k0 < (Letter.q :: t).reverse.length := by simpa using hk0
  have hlet0 : (Letter.q :: t).reverse.getD k0 Letter.p = Letter.q := by
    rw [getD_reverse_eq _ _ hk0, show (Letter.q :: t).length - 1 - k0 = lQ by omega, hlet]
  have hwr0 : (Letter.q :: t).reverse.getD 0 Letter.p = Letter.p := by
    have hl0' := hl0
    rw [ht] at hl0'
    rw [List.getD_eq_getElem?_getD, ← List.head?_eq_getElem?, List.head?_reverse, hl0']
    rfl
  have hcnt : (((Letter.q :: t).reverse.take k0).count Letter.q : ℤ) = 2 * np - nq - 1 := by
    rw [count_reverse_take, show (Letter.q :: t).length - k0 = lQ + 1 by omega, c1, show qPrefix (Letter.q :: t)
      (Letter.q :: t).length = 2 * np from htot]
    ring
  have htop := rev_tile (Letter.q :: t).reverse (texV2 (parentsAt w).odd + (1, -2)) k0 hk0r
  rw [hlet0, hwr0, hOffset_sum, hcnt, List.length_take,
    show min k0 (Letter.q :: t).reverse.length = k0 by rw [List.length_reverse]; exact min_eq_left hk0.le] at htop
  have htype := tileSeq_getD_q (Letter.q :: t).reverse k0 hk0r hlet0
  have hrel : texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - e₂ - texV1Even (parentsAt w).even -
      ((hRevStringAt (Letter.q :: t).reverse (texV2 (parentsAt w).odd + (1, -2))).getD k0 (ZTile.zero, 0)).2 =
        ((0 : ℤ), (1 : ℤ)) := by
    rw [htop]
    simp only [texV1Odd, texV1Even, texV2, e₂, ClosedPathCorners.revShift]
    have hk0Z : (k0 : ℤ) = dp + np - 1 - lQ := by
      have : ((Letter.q :: t).length : ℤ) = dp + np := hxl
      rw [hk0def]; push_cast [Nat.sub_sub]; omega
    ext <;> simp <;> omega
  have vPz : oP (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - e₂ - texV1Even (parentsAt w).even) =
      dot2 (np, -dp) (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - e₂ - texV1Even (parentsAt w).even) +
        βT := by
    have hmem : texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - e₂ - texV1Even (parentsAt w).even -
        ((hRevStringAt (Letter.q :: t).reverse (texV2 (parentsAt w).odd + (1, -2))).getD k0 (ZTile.zero, 0)).2 ∈
        tileShape ((hRevStringAt (Letter.q :: t).reverse (texV2 (parentsAt w).odd + (1, -2))).getD k0
          (ZTile.zero, 0)).1 := by
      rw [hrel, hRevStringAt_getD_fst]
      rcases htype with h | h <;> rw [h] <;> decide
    rw [hβT k0 hk0 _ hmem, hrel, hRevStringAt_getD_fst, (relOdo_rev_one _ htype).1, zero_add]
  -- the corner `X + Y - i` of the last top tile
  have hlast := ClosedPathCorners.hRev_lastPos_reverse (Letter.q :: t) (texV2 (parentsAt w).odd + (1, -2))
    (by rw [← ht]; exact hWordOf_head_last u1 false |>.1) (by rw [← ht]; exact hl0)
  have hL1 : (Letter.q :: t).length - 1 < (Letter.q :: t).length := by omega
  have hrelC : texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - e₂ -
      ((hRevStringAt (Letter.q :: t).reverse (texV2 (parentsAt w).odd + (1, -2))).getD
        ((Letter.q :: t).length - 1) (ZTile.zero, 0)).2 = ((0 : ℤ), (1 : ℤ)) := by
    rw [lastPosOf_eq_getD, hRevStringAt_length, List.length_reverse] at hlast
    rw [hlast]
    rw [ht] at hXP
    have hXP' : lastPosOf (hStringAt (Letter.q :: t) 0) = texV1Odd (parentsAt w).odd - (1, 1) := hXP
    rw [hXP']
    ext <;> simp <;> ring
  have hz0 : (Letter.q :: t).length - 1 - ((Letter.q :: t).length - 1) = 0 := by omega
  have hletC : (Letter.q :: t).reverse.getD ((Letter.q :: t).length - 1) Letter.p = Letter.q := by
    rw [getD_reverse_eq _ _ hL1, hz0]
    rfl
  have htypeC := tileSeq_getD_q (Letter.q :: t).reverse ((Letter.q :: t).length - 1) (by simp) hletC
  have vPC : oP (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - e₂) =
      dot2 (np, -dp) (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - e₂) + βT := by
    have hmem : texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - e₂ -
        ((hRevStringAt (Letter.q :: t).reverse (texV2 (parentsAt w).odd + (1, -2))).getD
          ((Letter.q :: t).length - 1) (ZTile.zero, 0)).2 ∈
        tileShape ((hRevStringAt (Letter.q :: t).reverse (texV2 (parentsAt w).odd + (1, -2))).getD
          ((Letter.q :: t).length - 1) (ZTile.zero, 0)).1 := by
      rw [hrelC, hRevStringAt_getD_fst]
      rcases htypeC with h | h <;> rw [h] <;> decide
    rw [hβT _ hL1 _ hmem, hrelC, hRevStringAt_getD_fst, (relOdo_rev_one _ htypeC).1, zero_add]
  -- the point `z* = U + A + B - i`
  refine ⟨texV1Even (parentsAt w).even + (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - e₂), ?_, ?_, ?_⟩
  · have hm0 : mOdd w u1 u2 0 = shiftS (marksOdd u1) (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even) :=
      by simp [mOdd, pieceSet, hP]
    rw [hm0]
    refine mem_shift _ _ _ (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - e₂ - texV1Even (parentsAt w).even)
      ?_ (by abel)
    apply SiteHullOdd.mem_marksOdd_of_sh_refl
    have hs := fwd_mem_sites_any t lQ hk (1, 0) (by simp)
    rw [c1, hposU] at hs
    rw [ht]
    convert hs using 1
    rw [hcu, ← hp]
    simp only [texV1Odd, texV1Even, texV2, e₁, e₂]
    ext <;> simp <;> ring
  · have hm4 : mOdd w u1 u2 4 = shiftS (marksEven u2) (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd) := by
      simp [mOdd, pieceSet, hP, hQ]
    rw [hm4]
    refine mem_shift _ _ _ (texV1Even (parentsAt w).even - e₂) ?_ (by abel)
    have h := (ClosedPathContacts.corner_marks_even u2).2.2.1
    rw [← hq] at h
    exact h
  · have h0 : IsPiece (placedOdd w oP oQ c 0) oP (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even) 0
        (c 0) := fun z => by simp [placedOdd, hP, affOdd]
    have h4 : IsPiece (placedOdd w oP oQ c 4) oQ (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd)
        ((parentsAt w).odd.num, -(parentsAt w).odd.den) (c 4) := fun z => by simp [placedOdd, hQ, affOdd]
    have h5 : IsPiece (placedOdd w oP oQ c 5) oQ
        (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)
        ((parentsAt w).odd.num, -(parentsAt w).odd.den) (c 5) := fun z => by simp [placedOdd, hQ, affOdd]
    rw [piece_val h0 _ (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - e₂ - texV1Even (parentsAt w).even)
        (by abel),
      piece_val h4 _ (texV1Even (parentsAt w).even - e₂) (by abel),
      piece_val h0 _ (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - e₂) (by abel),
      piece_val h5 _ (texV1Even (parentsAt w).even - e₂) (by abel),
      piece_val h5 (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) 0 (by abel),
      piece_val h4 (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)
        (texV1Even (parentsAt w).even) (by abel), vPz, vPC, vQU, vQ0]
    simp only [dot2, texV1Even, texV1Odd, texV2, e₂, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
      Prod.fst_zero, Prod.snd_zero]
    ring

/-- The ceiling inequalities of the odd-first triangles: `2 n_p - n_q` letters `q` among the first `|w_h(p)| - |w_h(q)|`. -/
theorem ceil_facts_of (np dp nq dq L : ℤ) (hdet : np * dq - nq * dp = 1) (hdp : 1 ≤ dp) (hnp : 1 ≤ np)
    (hL : 2 * L = dq + nq) :
    (dp + np) * (2 * np - nq) - (dp + np) < (dp + np - L) * (2 * np) ∧
      (dp + np - L) * (2 * np) ≤ (dp + np) * (2 * np - nq) := by
  have h : np * (2 * L) = np * (dq + nq) := by rw [hL]
  constructor <;> nlinarith

/-! ### The optional interface `(P^+, Q^{-,2})`, `W_1` odd -/

/-- **The triangle identity at `(P^+, Q^{-,2})` for `W_1` odd**, the half-turn of `triOdd_of_one`: if the copies meet then
`n_q + 1 ≤ 2 n_p`, and `z* = B + U + 1` lies (relative to `P^+`) on the top tile of `P` that is the half-turn of the bottom tile
at `A - U - 1 - i`, and on the first bottom corner of `Q^{-,2}`. -/
theorem triOdd_of_two (w u1 u2 : Word) (hph : phase w = 1)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (oP oQ : ℤ × ℤ → ℤ) (c : ℕ → ℤ) (TP : Finset Site)
    (hRP : SurgicalWeak.RespectsAnchored TP (hWordOf u1 false) (vWordOf u1 false) oP)
    (hRQ : RespectsTiles .horizontal false (hStringAt (hWordOf u2 true) 0) oQ)
    (hsP : SigmaZero oP (texV1Odd (parentsAt w).odd)) (hsQ : SigmaZero oQ (texV1Even (parentsAt w).even)) :
    (∃ z, z ∈ mOdd w u1 u2 0 ∧ z ∈ mOdd w u1 u2 5) → ∃ z, z ∈ mOdd w u1 u2 0 ∧ z ∈ mOdd w u1 u2 5 ∧
        placedOdd w oP oQ c 0 z - placedOdd w oP oQ c 5 z =
          (placedOdd w oP oQ c 0 (texV2 (parentsAt w).odd + e₁) -
            placedOdd w oP oQ c 4 (texV2 (parentsAt w).odd + e₁)) +
          (placedOdd w oP oQ c 4 (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) -
            placedOdd w oP oQ c 5 (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) := by
  rintro ⟨z0, hz0, hz5⟩
  have hP := oddP_of w hph
  have hQ := oddQ_of w hph
  have hd0 := mOdd_sub w u1 u2 0 hz0
  have hd5 := mOdd_sub w u1 u2 5 hz5
  simp only [dOdd, pieceSet, hP, hQ] at hd0 hd5
  simp at hd0 hd5
  have b0 := box_shift_odd u1 _ z0 hd0
  have b5 := box_shift_even u2 _ z0 hd5
  rw [← hp] at b0
  rw [← hq] at b5
  simp only [texV2, texV1Even, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero] at b0 b5
  have hov : (parentsAt w).even.num + 1 ≤ 2 * (parentsAt w).odd.num := by omega
  have hdet := SiteScope.det_parentsAt w
  rw [hph] at hdet
  simp only [Fraction.det, Nat.cast_one, mul_one] at hdet
  have hpl := SiteHullOdd.curO_pos_lt u1
  have hql := SiteHullEven.curE_pos_lt u2
  have hqe := SiteHullEven.curE_num_add_den_even u2
  have hcu : SiteInduction.curO u1 = fracOdd u1 := rfl
  have hce : SiteInduction.curE u2 = fracEven u2 := rfl
  rw [hcu, ← hp] at hpl
  rw [hce, ← hq] at hql hqe
  -- the parents along their strings
  have hcd := ClosedPathStandard.cornerDiffs_odd u1 TP oP hRP
  rw [← hp] at hcd
  obtain ⟨-, -, hRPt, -, -⟩ := hRP
  obtain ⟨hh0, hl0⟩ := hWordOf_head_last u1 false
  have hXP := TexVPositions.lastPos_hWordOf_false_tex u1
  rw [← hp] at hXP
  have hYP := StdCornerAnchors.stdAnchorY_odd u1
  rw [← hp] at hYP
  obtain ⟨βT, hβT⟩ := top_formula_norm (hWordOf u1 false) (vWordOf u1 false) oP _ _ _ _ hh0 hl0 hXP hYP hRPt hcd hsP
  have hXQ := TexVPositions.lastPos_hWordOf_true_tex u2
  rw [← hq] at hXQ
  obtain ⟨hhq, hlq⟩ := hWordOf_head_last u2 true
  obtain ⟨βQ, -, vQ0, -, vQU, -⟩ := fwd_formula_norm (hWordOf u2 true) oQ _ hhq hlq hXQ hRQ hsQ
  set np := (parentsAt w).odd.num with hnp
  set dp := (parentsAt w).odd.den with hdp
  set nq := (parentsAt w).even.num with hnq
  set dq := (parentsAt w).even.den with hdq
  have hdq2 : dq + 1 ≤ 2 * dp := by nlinarith
  -- the ceiling word of `P`
  have hcw := SiteHullOdd.cw_childP u1
  rw [hcu, ← hp] at hcw
  obtain ⟨t, ht⟩ : ∃ t, hWordOf u1 false = Letter.q :: t := by
    cases h : hWordOf u1 false with
    | nil => rw [h] at hh0; simp at hh0
    | cons a t =>
      rw [h] at hh0
      simp only [List.head?_cons, Option.some.injEq] at hh0
      exact ⟨t, by rw [hh0]⟩
  rw [ht] at hcw hβT
  have htot := ceil_total _ _ _ hcw (by omega)
  obtain ⟨hxl, hxc⟩ := hcw
  set lQ : ℕ := ((dq + nq) / 2).toNat with hlQdef
  have hlQ : 2 * (lQ : ℤ) = dq + nq := by
    rw [hlQdef, Int.toNat_of_nonneg (by omega)]
    omega
  set j : ℕ := (Letter.q :: t).length - lQ - 1 with hjdef
  have hlen1 : lQ + 1 ≤ (Letter.q :: t).length := by
    have : (lQ : ℤ) + 1 ≤ ((Letter.q :: t).length : ℤ) := by rw [hxl]; omega
    exact_mod_cast this
  have hjZ : (j : ℤ) + 1 = dp + np - lQ := by
    have : (j : ℤ) = ((Letter.q :: t).length : ℤ) - lQ - 1 := by rw [hjdef]; push_cast [Nat.sub_sub]; omega
    rw [this, hxl]
    ring
  have hl0' : 0 < dp + np := by omega
  have c1 : qPrefix (Letter.q :: t) (j + 1) = 2 * np - nq := by
    obtain ⟨h1, h2⟩ := hxc (j + 1) (by push_cast; omega)
    push_cast at h1 h2
    rw [hjZ] at h1 h2
    obtain ⟨f1, f2⟩ := ceil_facts_of np dp nq dq lQ hdet (by omega) (by omega) hlQ
    exact ceil_unique (dp + np) ((dp + np - lQ) * (2 * np)) _ (2 * np - nq) hl0' h1 h2 f1 f2
  have hk : j < (Letter.q :: t).length := by omega
  have hposj : (2 * (j : ℤ) + 1 - (2 * np - nq), 2 * np - nq - 1) + (1, 0) =
      texV1Odd (parentsAt w).odd - e₂ - texV1Even (parentsAt w).even := by
    simp only [texV1Odd, texV1Even, e₂]
    ext <;> simp <;> omega
  -- the top tile at index `lQ`
  have hk0 : lQ < (Letter.q :: t).length := by omega
  have hk0r : lQ < (Letter.q :: t).reverse.length := by simpa using hk0
  have hwr0 : (Letter.q :: t).reverse.getD 0 Letter.p = Letter.p := by
    have hl0'' := hl0
    rw [ht] at hl0''
    rw [List.getD_eq_getElem?_getD, ← List.head?_eq_getElem?, List.head?_reverse, hl0'']
    rfl
  have hcnt : (((Letter.q :: t).reverse.take lQ).count Letter.q : ℤ) = nq := by
    rw [count_reverse_take, show (Letter.q :: t).length - lQ = j + 1 by omega, c1, show qPrefix (Letter.q :: t)
      (Letter.q :: t).length = 2 * np from htot]
    ring
  have htop := rev_tile (Letter.q :: t).reverse (texV2 (parentsAt w).odd + (1, -2)) lQ hk0r
  rw [hwr0, hOffset_sum, hcnt, List.length_take,
    show min lQ (Letter.q :: t).reverse.length = lQ by rw [List.length_reverse]; exact min_eq_left hk0.le] at htop
  have vPz : oP (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even + e₁) =
      dot2 (np, -dp) (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even + e₁) + βT := by
    have hmem : ∀ r : GInt, texV2 (parentsAt w).odd + texV1Even (parentsAt w).even + e₁ -
        ((hRevStringAt (Letter.q :: t).reverse (texV2 (parentsAt w).odd + (1, -2))).getD lQ (ZTile.zero, 0)).2 = r →
        r ∈ tileShape ((hRevStringAt (Letter.q :: t).reverse (texV2 (parentsAt w).odd + (1, -2))).getD lQ
          (ZTile.zero, 0)).1 →
        relOdo revStr ((hRevStringAt (Letter.q :: t).reverse (texV2 (parentsAt w).odd + (1, -2))).getD lQ
          (ZTile.zero, 0)).1 r = 0 →
        oP (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even + e₁) =
          dot2 (np, -dp) (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even + e₁) + βT := by
      intro r hr hrs hro
      rw [← hr] at hrs
      rw [hβT lQ hk0 _ hrs, hr, hro, zero_add]
    by_cases hlet : (Letter.q :: t).reverse.getD lQ Letter.p = Letter.q
    · have htype := tileSeq_getD_q (Letter.q :: t).reverse lQ hk0r hlet
      rw [hlet] at htop
      refine hmem ((0 : ℤ), (1 : ℤ)) ?_ ?_ ?_
      · rw [htop]
        simp only [texV2, texV1Even, e₁, ClosedPathCorners.revShift]
        ext <;> simp <;> omega
      · rw [hRevStringAt_getD_fst]
        rcases htype with h | h <;> rw [h] <;> decide
      · rw [hRevStringAt_getD_fst]
        exact (relOdo_rev_one _ htype).1
    · have hletp : (Letter.q :: t).reverse.getD lQ Letter.p = Letter.p := by
        cases h : (Letter.q :: t).reverse.getD lQ Letter.p
        · rfl
        · exact absurd h hlet
      have htype := tileSeqAux_getD_p (Letter.q :: t).reverse none lQ hk0r hletp
      rw [hletp] at htop
      refine hmem ((0 : ℤ), (2 : ℤ)) ?_ ?_ ?_
      · rw [htop]
        simp only [texV2, texV1Even, e₁, ClosedPathCorners.revShift]
        ext <;> simp <;> omega
      · rw [hRevStringAt_getD_fst]
        rw [show tileSeq (Letter.q :: t).reverse = tileSeqAux none (Letter.q :: t).reverse from rfl, htype]
        decide
      · rw [hRevStringAt_getD_fst]
        rw [show tileSeq (Letter.q :: t).reverse = tileSeqAux none (Letter.q :: t).reverse from rfl, htype]
        exact relOdo_rev_zero.2
  -- the corner `Y + 1` of the first top tile
  have hrne : (Letter.q :: t).reverse ≠ [] := by simp
  have vPD : oP (texV2 (parentsAt w).odd + e₁) = dot2 (np, -dp) (texV2 (parentsAt w).odd + e₁) + βT := by
    have ht0 : (hRevStringAt (Letter.q :: t).reverse (texV2 (parentsAt w).odd + (1, -2))).getD 0 (ZTile.zero, 0) =
        (ZTile.zero, texV2 (parentsAt w).odd + (1, -2)) := by
      apply Prod.ext
      · rw [hRevStringAt_getD_fst, tileSeq_getD_zero_head _ hrne hwr0]
      · rw [hRevStringAt_getD_snd_zero _ _ hrne]
    have hr : texV2 (parentsAt w).odd + e₁ - (texV2 (parentsAt w).odd + (1, -2)) = ((0 : ℤ), (2 : ℤ)) := by
      ext <;> (simp; try ring)
    have hmem : texV2 (parentsAt w).odd + e₁ -
        ((hRevStringAt (Letter.q :: t).reverse (texV2 (parentsAt w).odd + (1, -2))).getD 0 (ZTile.zero, 0)).2 ∈
        tileShape ((hRevStringAt (Letter.q :: t).reverse (texV2 (parentsAt w).odd + (1, -2))).getD 0
          (ZTile.zero, 0)).1 := by
      rw [ht0, hr]
      exact (by decide : ((0 : ℤ), (2 : ℤ)) ∈ tileShape ZTile.zero)
    rw [hβT 0 (by simp) _ hmem, ht0, hr, relOdo_rev_zero.2, zero_add]
  -- the point `z* = B + U + 1`
  refine ⟨texV2 (parentsAt w).odd + texV1Even (parentsAt w).even + e₁, ?_, ?_, ?_⟩
  · have hm0 : mOdd w u1 u2 0 = shiftS (marksOdd u1) 0 := by simp [mOdd, pieceSet, hP]
    rw [hm0]
    refine mem_shift _ _ _ (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even + e₁) ?_ (by abel)
    apply SiteHullOdd.mem_marksOdd_of_sh_refl
    have hs := fwd_mem_sites_any t j hk (1, 0) (by simp)
    rw [c1, hposj] at hs
    rw [ht]
    convert hs using 1
    rw [hcu, ← hp]
    simp only [texV1Odd, texV1Even, texV2, e₁, e₂]
    ext <;> simp <;> ring
  · have hm5 : mOdd w u1 u2 5 = shiftS (marksEven u2) (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) := by
      simp [mOdd, pieceSet, hP, hQ]
    rw [hm5]
    refine mem_shift _ _ _ e₁ ?_ (by abel)
    exact (ClosedPathContacts.corner_marks_even u2).2.1
  · have h0 : IsPiece (placedOdd w oP oQ c 0) oP 0 0 (c 0) := fun z => by simp [placedOdd, hP, affOdd]
    have h4 : IsPiece (placedOdd w oP oQ c 4) oQ (texV2 (parentsAt w).odd)
        ((parentsAt w).odd.num, -(parentsAt w).odd.den) (c 4) := fun z => by simp [placedOdd, hQ, affOdd]
    have h5 : IsPiece (placedOdd w oP oQ c 5) oQ (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)
        ((parentsAt w).odd.num, -(parentsAt w).odd.den) (c 5) := fun z => by simp [placedOdd, hQ, affOdd]
    rw [piece_val h0 _ (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even + e₁) (by abel),
      piece_val h5 _ e₁ (by abel),
      piece_val h0 _ (texV2 (parentsAt w).odd + e₁) (by abel),
      piece_val h4 _ e₁ (by abel),
      piece_val h4 (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) (texV1Even (parentsAt w).even) (by abel),
      piece_val h5 (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) 0 (by abel), vPz, vPD, vQU, vQ0]
    simp only [dot2, texV1Even, texV2, e₁, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero]
    ring

/-! ### The triangle identities of the odd child, and condition (C) -/

/-- **`TriOdd` for normalised parents**, in both orientations. -/
theorem triOdd_all (w u1 u2 : Word) (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (oP oQ : ℤ × ℤ → ℤ) (c : ℕ → ℤ) (TP TQ : Finset Site)
    (hRP : SurgicalWeak.RespectsAnchored TP (hWordOf u1 false) (vWordOf u1 false) oP)
    (hRQ : SurgicalWeak.RespectsAnchored TQ (hWordOf u2 true) (vWordOf u2 true) oQ)
    (hsP : SigmaZero oP (texV1Odd (parentsAt w).odd)) (hsQ : SigmaZero oQ (texV1Even (parentsAt w).even)) :
    TriOdd w u1 u2 oP oQ c := by
  have hRPb := hRP.2.1
  have hRQb := hRQ.2.1
  simp only [TriOdd]
  split_ifs with hph
  · exact ⟨triOdd_of_one w u1 u2 hph hp hq oP oQ c hRPb hRQb hsP hsQ,
      triOdd_of_two w u1 u2 hph hp hq oP oQ c TP hRP hRQb hsP hsQ⟩
  · exact ⟨triOdd_ef_one w u1 u2 hph hp hq oP oQ c hRPb hRQb hsP hsQ,
      triOdd_ef_two w u1 u2 hph hp hq oP oQ c TP hRP hRQb hsP hsQ⟩

/-- **Condition (C) for the odd standard child** (`ChildGlue.ClosedPathOdd`), in both orientations, for parents that respect
their strings and are normalised on their first bottom tile (eq:std_corner_values), with (c) of the even parent and local
compatibility of the mixed copies as the remaining inputs. -/
theorem closedPathOdd_final (w u1 u2 : Word)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (oP oQ : ℤ × ℤ → ℤ) (TP TQ : Finset Site) (c : ℕ → ℤ)
    (hRP : SurgicalWeak.RespectsAnchored TP (hWordOf u1 false) (vWordOf u1 false) oP)
    (hRQ : SurgicalWeak.RespectsAnchored TQ (hWordOf u2 true) (vWordOf u2 true) oQ)
    (hsP : SigmaZero oP (texV1Odd (parentsAt w).odd)) (hsQ : SigmaZero oQ (texV1Even (parentsAt w).even))
    (hdbl : ∃ k : ℤ, ∀ x, x ∈ tEvenSet u2 → x + texV1Even (parentsAt w).even ∈ tEvenSet u2 →
      oQ (x + texV1Even (parentsAt w).even) - oQ x = k)
    (hcompat : MixedCompatOdd w u1 u2 (placedOdd w oP oQ c)) :
    ClosedPathOdd w u1 u2 (placedOdd w oP oQ c) :=
  ClosedPathDiagonal.closedPathOdd_of w u1 u2 hp hq oP oQ TP TQ c hRP hRQ hdbl hcompat
    (triOdd_all w u1 u2 hp hq oP oQ c TP TQ hRP hRQ hsP hsQ)

end FLatticePaper.Tiles.ClosedPathTriOdd
