import FLatticePaper.Tiles.ClosedPathTriangle

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

end FLatticePaper.Tiles.ClosedPathTriOdd
