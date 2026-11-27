import FLatticePaper.Tiles.ClosedPathTriOdd
import FLatticePaper.Tiles.VerticalStepOne
import FLatticePaper.Tiles.MixedFromCells

/-! # Condition (C): the optional interfaces of the even standard child (vertical strings)

The even child has the doubled odd parent `P` (copies `P^{±,1}`, `P^{±,2}`, shift `B = v_{p,2}`) and the plain even parent `Q`. Its
two optional mixed interfaces in each orientation lie on vertical interfaces: the farther copy `P^{±,2}` of a doubled piece meets
`Q^±` along a vertical string of `Q`. Following Step 1 of `lemma:weak_standard_odometer_properties` (the even case, with
`h_0`): if they meet then `d_q > d_p`, and the point `z*` lies on the tile of the vertical string of `Q` after `|w_v(p)| = d_p`
letters, at the translate by `B` of a corner of `Q`. For parents normalised on their first bottom tile (`SigmaZero`), the vertical
formula of Step 1 (`VerticalStepOne`) makes both sides of the triangle identity equal to `-h_0(B)`.

This module gives the tools (positions of the forward vertical strings from the counts of the ceiling words, and the affine
factors of the vertical strings of a normalised parent, read at three points of a corner tile) and the identities. -/

namespace FLatticePaper.Tiles.ClosedPathTriEven

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.SiteInduction
open FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.CeilWords FLatticePaper.Tiles.ChildGlue
open FLatticePaper.Tiles.MixedPieces FLatticePaper.Tiles.ClosedPathSum FLatticePaper.Tiles.ClosedPathAssembly
open FLatticePaper.Tiles.ClosedPathStandard FLatticePaper.Tiles.StandardClause FLatticePaper.Tiles.ClosedPathExcluded
open FLatticePaper.Tiles.ClosedPathTriangle FLatticePaper.Tiles.ClosedPathCorners FLatticePaper.Tiles.ClosedPathTriOdd
open FLatticePaper.Tiles.Standard (oddTile evenTile)

/-! ### Positions of the forward vertical string -/

theorem vOffset_sum : ∀ L : BinaryWord,
    (L.map vOffset).sum = ((L.count Letter.q : ℤ) - (L.length : ℤ), (L.length : ℤ) + (L.count Letter.q : ℤ))
  | [] => by ext <;> simp
  | l :: L => by
    rw [List.map_cons, List.sum_cons, vOffset_sum L]
    cases l <;> ext <;> simp [vOffset] <;> ring

/-- **The `k`-th tile of the forward vertical string** of `p :: t` from `c`: the letter of `k`, at `c + (c_{k+1} - k, k + c_{k+1})`
with `c_j` the number of letters `q` among the first `j` letters. -/
theorem vfwd_tile (t : BinaryWord) (c : GInt) (k : ℕ) (hk : k < (Letter.p :: t).length) :
    (vStringAt (Letter.p :: t) c).getD k (ZTile.zero, 0) =
      (letterZTile ((Letter.p :: t).getD k Letter.p),
        c + (qPrefix (Letter.p :: t) (k + 1) - k, k + qPrefix (Letter.p :: t) (k + 1))) := by
  have hlen : ((Letter.p :: t).map letterZTile).length = (List.scanl (· + ·) c (t.map vOffset)).length := by simp
  apply Prod.ext
  · have hm : (vStringAt (Letter.p :: t) c).map Prod.fst = (Letter.p :: t).map letterZTile := by
      unfold vStringAt
      exact List.map_fst_zip (le_of_eq hlen)
    rw [getD_fst_of_map _ _ hm, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hk]
    rfl
  · have hm : (vStringAt (Letter.p :: t) c).map Prod.snd = List.scanl (· + ·) c (t.map vOffset) := by
      unfold vStringAt
      exact List.map_snd_zip (le_of_eq hlen.symm)
    have h2 : ((vStringAt (Letter.p :: t) c).getD k (ZTile.zero, 0)).2 = (List.scanl (· + ·) c (t.map vOffset)).getD k 0 := by
      rw [← hm, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
      generalize (vStringAt (Letter.p :: t) c)[k]? = o
      cases o <;> simp
    have hk' : k ≤ (t.map vOffset).length := by simp at hk ⊢; omega
    rw [h2, scanl_getD_sum _ c k hk', ← List.map_take, vOffset_sum]
    have hlt : ((t.take k).length : ℤ) = k := by
      rw [List.length_take]
      simp at hk
      omega
    have hq : qPrefix (Letter.p :: t) (k + 1) = ((t.take k).count Letter.q : ℤ) := by
      unfold qPrefix
      rw [List.take_succ_cons, List.count_cons]
      simp
    rw [hlt, hq]

/-! ### Small values of `h_0` -/

theorem h0_shift (x v : GInt) (hv : (v.1 + v.2) % 2 = 0) :
    zoH0 (x + v) - zoH0 x = (-v.1 - v.2) / 2 * x.1 + (v.2 - v.1) / 2 * x.2 + zoH0 v :=
  zoH0_shift_even x v _ _ (by omega) (by omega) hv

theorem h0_11 : zoH0 ((1 : ℤ), (1 : ℤ)) = 0 := by decide
theorem h0_m11 : zoH0 ((-1 : ℤ), (1 : ℤ)) = 1 := by decide
theorem h0_01 : zoH0 ((0 : ℤ), (1 : ℤ)) = 1 := by decide
theorem h0_00 : zoH0 ((0 : ℤ), (0 : ℤ)) = 0 := by decide

/-! ### The affine factors of the vertical strings of a normalised parent -/

/-- **The right string.** On the last bottom tile `T_{0/1}` at `X - 1 - i`, shared by the bottom string (a normalised parent is
the zero odometer plus a constant there) and the right vertical string (the vertical formula with factor `a_0`), the factor is
`a_0 = ℓ(X) = ((-X_1 - X_2)/2, (X_2 - X_1)/2)`. -/
theorem vright_a0 (S : GInt → ℤ) (X a0 : GInt) (β K : ℤ)
    (hB : ∀ u ∈ tileShape ZTile.zero, S (X - (1, 1) + u) = zTileOdo ZTile.zero u + β)
    (hV : ∀ u ∈ tileShape ZTile.zero, S (X - (1, 1) + u) + zoH0 (X - (1, 1) + u) -
      (a0.1 * (X - (1, 1) + u).1 + a0.2 * (X - (1, 1) + u).2) = vV Letter.p false u + K) :
    2 * a0.1 = -X.1 - X.2 ∧ 2 * a0.2 = X.2 - X.1 := by
  have b0 := hB (0, 0) (by decide)
  have b1 := hB (1, 1) (by decide)
  have b2 := hB (0, 2) (by decide)
  have v0 := hV (0, 0) (by decide)
  have v1 := hV (1, 1) (by decide)
  have v2 := hV (0, 2) (by decide)
  have z0 : zTileOdo ZTile.zero ((0 : ℤ), (0 : ℤ)) = 0 := by decide
  have z1 : zTileOdo ZTile.zero ((1 : ℤ), (1 : ℤ)) = 0 := by decide
  have z2 : zTileOdo ZTile.zero ((0 : ℤ), (2 : ℤ)) = -1 := by decide
  have w0 : vV Letter.p false ((0 : ℤ), (0 : ℤ)) = -1 := by decide
  have w1 : vV Letter.p false ((1 : ℤ), (1 : ℤ)) = 0 := by decide
  have w2 : vV Letter.p false ((0 : ℤ), (2 : ℤ)) = 0 := by decide
  rw [z0] at b0
  rw [z1] at b1
  rw [z2] at b2
  rw [w0] at v0
  rw [w1] at v1
  rw [w2] at v2
  have e1 : X - (1, 1) + (1, 1) = (X - (1, 1) + (0, 0)) + (1, 1) := by abel
  have e2 : X - (1, 1) + (0, 2) = (X - (1, 1) + (1, 1)) + (-1, 1) := by ext <;> simp <;> ring
  have s1 := zoH0_shift_even (X - (1, 1) + (0, 0)) (1, 1) (-1) 0 (by norm_num) (by norm_num) (by decide)
  have s2 := zoH0_shift_even (X - (1, 1) + (1, 1)) (-1, 1) 0 1 (by norm_num) (by norm_num) (by decide)
  rw [← e1, h0_11] at s1
  rw [← e2, h0_m11] at s2
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at s1 s2 v0 v1 v2
  constructor <;> linarith

/-- **The left string.** On the first bottom tile `T_{1/1}` at `0`, shared by the bottom string and the left (reversed) vertical
string from `0`, the factor of the vertical formula is `a_0 = 0`. -/
theorem vleft_a0 (S : GInt → ℤ) (a0 : GInt) (β K : ℤ)
    (hA : ∀ u ∈ tileShape ZTile.one, S u = zTileOdo ZTile.one u + β)
    (hV : ∀ u ∈ tileShape ZTile.one, S (0 + u) + zoH0 (0 + u) - (a0.1 * (0 + u).1 + a0.2 * (0 + u).2) =
      vV Letter.q true u + K) :
    a0 = 0 := by
  have b0 := hA (0, 0) (by decide)
  have b1 := hA (1, 1) (by decide)
  have b2 := hA (0, 1) (by decide)
  have v0 := hV (0, 0) (by decide)
  have v1 := hV (1, 1) (by decide)
  have v2 := hV (0, 1) (by decide)
  simp only [zero_add] at v0 v1 v2
  rw [h0_00] at v0
  rw [h0_11] at v1
  rw [h0_01] at v2
  have z0 : zTileOdo ZTile.one ((0 : ℤ), (0 : ℤ)) = 0 := by decide
  have z1 : zTileOdo ZTile.one ((1 : ℤ), (1 : ℤ)) = 0 := by decide
  have z2 : zTileOdo ZTile.one ((0 : ℤ), (1 : ℤ)) = -1 := by decide
  have w : ∀ u, vV Letter.q true u = 0 := fun u => rfl
  rw [z0] at b0
  rw [z1] at b1
  rw [z2] at b2
  rw [w] at v0 v1 v2
  have h1 : a0.2 = 0 := by linarith
  have h2 : a0.1 = 0 := by linarith
  ext
  · exact h2
  · exact h1

/-- The first and last tiles of the bottom string of a normalised parent: the one odometer on `T_{1/1}` at `0`, the zero odometer
on `T_{0/1}` at `X - 1 - i`, plus one constant. -/
theorem fwd_corner_tiles (x : BinaryWord) (S : GInt → ℤ) (X : GInt) (hh : x.head? = some .q)
    (hl : x.getLast? = some .p) (hX : lastPosOf (hStringAt x 0) = X - (1, 1))
    (hR : RespectsTiles .horizontal false (hStringAt x 0) S) (hσ : SigmaZero S X) :
    ∃ β : ℤ, (∀ u ∈ tileShape ZTile.one, S u = zTileOdo ZTile.one u + β) ∧
      (∀ u ∈ tileShape ZTile.zero, S (X - (1, 1) + u) = zTileOdo ZTile.zero u + β) := by
  obtain ⟨β, hβ, -⟩ := fwd_formula_norm x S X hh hl hX hR hσ
  have hne : x ≠ [] := by
    rintro rfl
    simp at hh
  have hlen : (hStringAt x 0).length = x.length := hStringAt_length' x 0
  have hpos : 0 < (hStringAt x 0).length := by rw [hlen]; exact List.length_pos_of_ne_nil hne
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
  refine ⟨β, fun u hu => ?_, fun u hu => ?_⟩
  · have h := hβ 0 hpos u (by rw [ht0]; simpa using hu)
    rw [ht0] at h
    simpa using h
  · have h := hβ ((hStringAt x 0).length - 1) (by omega) (X - (1, 1) + u) (by rw [htl]; simpa using hu)
    rw [htl] at h
    simpa using h

/-- The `q` counts of a word with the letters exchanged. -/
theorem qPrefix_swap (x : BinaryWord) (j : ℕ) (hj : j ≤ x.length) :
    qPrefix (x.map swapLetter) j = (j : ℤ) - qPrefix x j := by
  unfold qPrefix
  rw [← List.map_take, count_map_swapLetter_q]
  have h := length_eq_counts (x.take j)
  rw [List.length_take, min_eq_left hj] at h
  have h' : ((x.take j).count Letter.p : ℤ) + ((x.take j).count Letter.q : ℤ) = (j : ℤ) := by exact_mod_cast h.symm
  linarith

/-! ### The optional interface `(P^{+,2}, Q^+)`, `W_1` even -/

/-- The ceiling inequalities of the vertical word of `Q` at `d_p + 1` letters. -/
theorem vceil_facts (np dp nq dq ε : ℤ) (hdet : np * dq - nq * dp = ε) (hε : ε = 1 ∨ ε = -1)
    (hnq : 1 ≤ nq) (hgap : nq + 2 ≤ dq) :
    dq * (dp + 1 - np) - dq < (dp + 1) * (dq - nq) ∧ (dp + 1) * (dq - nq) ≤ dq * (dp + 1 - np) := by
  rcases hε with rfl | rfl <;> constructor <;> nlinarith

/-- **The triangle identity at `(P^{+,2}, Q^+)` for `W_1` even.** If the copies meet then `d_q > d_p`, the right vertical string of
`Q` has a tile at `v_{q,1} - 1 - i + v_{p,2}` (after `d_p` letters, with `n_p` letters `q`), and `z* = U + B` is the first bottom
corner of `P^{+,2}` and lies on that tile of `Q^+`. Both sides of the identity equal `-h_0(B)`. -/
theorem triEven_ef_one (w u1 u2 : Word) (hw : ¬ Standard.IsBase w) (hT1 : (Standard.stateAt w).tOdd = oddTile u1)
    (hT2 : (Standard.stateAt w).tEven = evenTile u2) (hph : phase w ≠ 1)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (oP oQ : ℤ × ℤ → ℤ) (c : ℕ → ℤ)
    (hRP : SurgicalWeak.RespectsAnchored (oddTile u1) (hWordOf u1 false) (vWordOf u1 false) oP)
    (hRQ : SurgicalWeak.RespectsAnchored (evenTile u2) (hWordOf u2 true) (vWordOf u2 true) oQ)
    (hsP : SigmaZero oP (texV1Odd (parentsAt w).odd)) (hsQ : SigmaZero oQ (texV1Even (parentsAt w).even)) :
    (∃ z, z ∈ mEven w u1 u2 1 ∧ z ∈ mEven w u1 u2 4) → ∃ z, z ∈ mEven w u1 u2 1 ∧ z ∈ mEven w u1 u2 4 ∧
        placedEven w oP oQ c 1 z - placedEven w oP oQ c 4 z =
          (placedEven w oP oQ c 1 (texV1Even (parentsAt w).even + (texV2 (parentsAt w).odd + e₁)) -
            placedEven w oP oQ c 0 (texV1Even (parentsAt w).even + (texV2 (parentsAt w).odd + e₁))) +
          (placedEven w oP oQ c 0 (texV1Even (parentsAt w).even) -
            placedEven w oP oQ c 4 (texV1Even (parentsAt w).even)) := by
  rintro ⟨z0, hz1, hz4⟩
  have hP := evenP_ef w hph
  have hQ := evenQ_ef w hph
  -- the overlap gives `n_p + d_p < n_q + d_q`
  have hd1 := mEven_sub w u1 u2 1 hz1
  have hd4 := mEven_sub w u1 u2 4 hz4
  simp only [dEven, pieceSet, hP, hQ] at hd1 hd4
  simp at hd1 hd4
  have b1 := box_shift_odd u1 _ z0 hd1
  have b4 := box_shift_even u2 _ z0 hd4
  rw [← hp] at b1
  rw [← hq] at b4
  simp only [texV2, texV1Even, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero] at b1 b4
  have hov : (parentsAt w).odd.num + (parentsAt w).odd.den + 1 ≤ (parentsAt w).even.num + (parentsAt w).even.den := by
    omega
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
  obtain ⟨hInQ, hRQb, -, -, hRQv⟩ := hRQ
  obtain ⟨-, hRPb, -, hRPl, -⟩ := hRP
  obtain ⟨hhq, hlq⟩ := hWordOf_head_last u2 true
  have hXQ := TexVPositions.lastPos_hWordOf_true_tex u2
  rw [← hq] at hXQ
  obtain ⟨βQ, hQA, hQB⟩ := fwd_corner_tiles (hWordOf u2 true) oQ _ hhq hlq hXQ hRQb hsQ
  obtain ⟨hhp, hlp⟩ := hWordOf_head_last u1 false
  have hXP := TexVPositions.lastPos_hWordOf_false_tex u1
  rw [← hp] at hXP
  obtain ⟨βP, hPA, -⟩ := fwd_corner_tiles (hWordOf u1 false) oP _ hhp hlp hXP hRPb hsP
  have hdpq : (parentsAt w).odd.den + 1 ≤ (parentsAt w).even.den := by
    by_contra h
    rw [not_le] at h
    nlinarith
  -- the vertical word of `Q`
  obtain ⟨hvh, hvl⟩ := StringCorners.vWord_even_head_last u2
  have hvc := StringCorners.vWord_even_counts u2
  rw [hce, ← hq] at hvc
  obtain ⟨t, ht⟩ : ∃ t, vWordOf u2 true = Letter.p :: t := by
    cases h : vWordOf u2 true with
    | nil => rw [h] at hvh; simp at hvh
    | cons a t =>
      rw [h] at hvh
      simp only [List.head?_cons, Option.some.injEq] at hvh
      exact ⟨t, by rw [hvh]⟩
  have hvlen : ((Letter.p :: t).length : ℤ) = (parentsAt w).even.den := by
    have h := length_eq_counts (vWordOf u2 true)
    rw [ht] at h hvc
    have h' : ((Letter.p :: t).length : ℤ) = ((Letter.p :: t).count Letter.p : ℤ) + ((Letter.p :: t).count Letter.q : ℤ) :=
      by exact_mod_cast h
    rw [h', hvc.1, hvc.2]
    ring
  have hcwv := SiteHullEven.cw_childP_swap u2
  rw [hce, ← hq] at hcwv
  have hvw : vWordOf u2 true = (quadAt [] (Standard.swapW u2)).childP.map swapLetter := rfl
  have hxl : ((quadAt [] (Standard.swapW u2)).childP.length : ℤ) = (parentsAt w).even.den := hcwv.1
  set dpN : ℕ := (parentsAt w).odd.den.toNat with hdpNdef
  have hdpN : (dpN : ℤ) = (parentsAt w).odd.den := Int.toNat_of_nonneg (by omega)
  have hk1 : dpN + 1 ≤ (quadAt [] (Standard.swapW u2)).childP.length := by
    have : (dpN : ℤ) + 1 ≤ ((quadAt [] (Standard.swapW u2)).childP.length : ℤ) := by rw [hdpN, hxl]; omega
    exact_mod_cast this
  have hcnt : qPrefix (Letter.p :: t) (dpN + 1) = (parentsAt w).odd.num := by
    rw [← ht, hvw, qPrefix_swap _ _ hk1]
    obtain ⟨h1, h2⟩ := hcwv.2 (dpN + 1) (by push_cast; omega)
    push_cast at h1 h2
    rw [hdpN] at h1 h2
    obtain ⟨f1, f2⟩ := vceil_facts (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (-1) (by linarith) (Or.inr rfl) (by omega) (by omega)
    have := ceil_unique (parentsAt w).even.den (((parentsAt w).odd.den + 1) * ((parentsAt w).even.den - (parentsAt w).even.num)) _ ((parentsAt w).odd.den + 1 - (parentsAt w).odd.num) (by omega) h1 h2 f1 f2
    push_cast
    rw [hdpN, this]
    ring
  have hkv : dpN < (Letter.p :: t).length := by
    have : (dpN : ℤ) < ((Letter.p :: t).length : ℤ) := by rw [hdpN, hvlen]; omega
    exact_mod_cast this
  -- the right vertical string of `Q` from `U - 1 - i`
  have hXQ' : lastPosOf (hStringAt (hWordOf u2 true) 0) = texV1Even (parentsAt w).even - (1, 1) := hXQ
  rw [hXQ', ht] at hRQv
  have hd0 : ((texV1Even (parentsAt w).even - (1, 1) - cstarV ((Letter.p :: t).headD Letter.p) false).1 +
      (texV1Even (parentsAt w).even - (1, 1) - cstarV ((Letter.p :: t).headD Letter.p) false).2) % 2 = 0 := by
    simp only [List.headD_cons, cstarV, texV1Even, Prod.fst_sub, Prod.snd_sub]
    omega
  obtain ⟨a0, K, hV⟩ := VerticalStepOne.vertical_formula (Letter.p :: t) _ oQ (by simp) hRQv hd0
  have ht0 : (vStringAt (Letter.p :: t) (texV1Even (parentsAt w).even - (1, 1))).getD 0 (ZTile.zero, 0) =
      (ZTile.zero, texV1Even (parentsAt w).even - (1, 1)) := by
    rw [vfwd_tile t _ 0 (by simp)]
    have : qPrefix (Letter.p :: t) 1 = 0 := by simp [qPrefix]
    rw [this]
    ext <;> simp [letterZTile]
  have hlen0 : 0 < (vStringAt (Letter.p :: t) (texV1Even (parentsAt w).even - (1, 1))).length := by
    simp [vStringAt]
  have hV0 : ∀ u ∈ tileShape ZTile.zero, oQ (texV1Even (parentsAt w).even - (1, 1) + u) +
      zoH0 (texV1Even (parentsAt w).even - (1, 1) + u) -
      (a0.1 * (texV1Even (parentsAt w).even - (1, 1) + u).1 + a0.2 * (texV1Even (parentsAt w).even - (1, 1) + u).2) =
      vV Letter.p false u + K := by
    intro u hu
    have h := hV 0 hlen0 u (by rw [ht0]; exact hu)
    rw [ht0] at h
    exact h
  obtain ⟨ha1, ha2⟩ := vright_a0 oQ _ a0 βQ K hQB hV0
  have htk : (vStringAt (Letter.p :: t) (texV1Even (parentsAt w).even - (1, 1))).getD dpN (ZTile.zero, 0) =
      (letterZTile ((Letter.p :: t).getD dpN Letter.p),
        texV1Even (parentsAt w).even - (1, 1) + texV2 (parentsAt w).odd) := by
    rw [vfwd_tile t _ dpN hkv, hcnt]
    congr 1
    simp only [texV2]
    ext <;> simp <;> omega
  have hlenk : dpN < (vStringAt (Letter.p :: t) (texV1Even (parentsAt w).even - (1, 1))).length := by
    simpa [vStringAt] using hkv
  have h11 : ∀ l : Letter, ((1 : ℤ), (1 : ℤ)) ∈ tileShape (letterZTile l) ∧ vV l false (1, 1) = 0 := by
    intro l
    cases l <;> decide
  have vQk := hV dpN hlenk (1, 1) (by rw [htk]; exact (h11 _).1)
  rw [htk, zTileLetter_letterZTile, (h11 _).2] at vQk
  have vQ0 := hV0 (1, 1) (by decide)
  rw [show vV Letter.p false ((1 : ℤ), (1 : ℤ)) = 0 by decide] at vQ0
  have eU : texV1Even (parentsAt w).even - (1, 1) + (1, 1) = texV1Even (parentsAt w).even := by abel
  have eUB : texV1Even (parentsAt w).even - (1, 1) + texV2 (parentsAt w).odd + (1, 1) =
      texV1Even (parentsAt w).even + texV2 (parentsAt w).odd := by abel
  rw [eU] at vQ0
  rw [eUB] at vQk
  have sQ := zoH0_shift_even (texV1Even (parentsAt w).even) (texV2 (parentsAt w).odd) (-(parentsAt w).odd.num) (parentsAt w).odd.den
    (by simp only [texV2]; ring) (by simp only [texV2]; ring) (by simp only [texV2]; omega)
  -- the left vertical string of `P` from `0`
  obtain ⟨hvhp, hvlp⟩ := StringCorners.vertWord_head_last u1
  have hwv : vWordOf u1 false = vertWord u1 := rfl
  have hne : (vWordOf u1 false).reverse ≠ [] := by
    rw [hwv]
    intro h
    rw [List.reverse_eq_nil_iff] at h
    rw [h] at hvhp
    simp at hvhp
  have hhd : (vWordOf u1 false).reverse.headD Letter.p = Letter.q := by
    rw [List.headD_eq_head?_getD, List.head?_reverse, hwv, hvlp]
    rfl
  have hd0P : (((0 : GInt) - cstarV ((vWordOf u1 false).reverse.headD Letter.p) true).1 +
      ((0 : GInt) - cstarV ((vWordOf u1 false).reverse.headD Letter.p) true).2) % 2 = 0 := by
    rw [hhd]
    decide
  obtain ⟨b0, KP, hVP⟩ := VerticalStepOne.reversed_vertical_formula _ 0 oP hne hRPl hd0P
  have hg0 : (vWordOf u1 false).reverse.getD 0 Letter.p = Letter.q := by
    rw [List.getD_eq_getElem?_getD, ← List.head?_eq_getElem?, List.head?_reverse, hwv, hvlp]
    rfl
  have hlenP : (vRevStringAt (vWordOf u1 false).reverse 0).length = (vWordOf u1 false).reverse.length :=
    vRevStringAt_length _ _
  have hposP : 0 < (vWordOf u1 false).reverse.length := List.length_pos_of_ne_nil hne
  have hP0 : (vRevStringAt (vWordOf u1 false).reverse 0).getD 0 (ZTile.zero, 0) = (ZTile.one, 0) := by
    apply Prod.ext
    · rw [vRevStringAt_getD_fst _ _ 0 hposP, hg0]
      rfl
    · exact vRevStringAt_getD_snd_zero _ _ hne
  have hVP0 : ∀ u ∈ tileShape ZTile.one, oP (0 + u) + zoH0 (0 + u) - (b0.1 * (0 + u).1 + b0.2 * (0 + u).2) =
      vV Letter.q true u + KP := by
    intro u hu
    have h := hVP 0 (by rw [hlenP]; exact hposP) u (by rw [hP0]; exact hu)
    rw [hP0] at h
    exact h
  have hb0 := vleft_a0 oP b0 βP KP hPA hVP0
  have hgl : (vWordOf u1 false).reverse.getD ((vWordOf u1 false).reverse.length - 1) Letter.p = Letter.p := by
    rw [List.getD_eq_getElem?_getD, ← List.getLast?_eq_getElem?, List.getLast?_reverse, hwv, hvhp]
    rfl
  have hYP := StdCornerAnchors.stdAnchorY_odd u1
  rw [← hp] at hYP
  have hPl : (vRevStringAt (vWordOf u1 false).reverse 0).getD ((vWordOf u1 false).reverse.length - 1) (ZTile.zero, 0) =
      (ZTile.zero, texV2 (parentsAt w).odd + (1, -2)) := by
    apply Prod.ext
    · rw [vRevStringAt_getD_fst _ _ _ (by omega), hgl]
      rfl
    · rw [← hYP, lastPosOf_eq_getD, hlenP]
  have vPD := hVP ((vWordOf u1 false).reverse.length - 1) (by rw [hlenP]; omega) (0, 2) (by
    rw [hPl]
    exact (by decide : ((0 : ℤ), (2 : ℤ)) ∈ tileShape ZTile.zero))
  rw [hPl] at vPD
  have vPA := hVP0 e₁ (by decide)
  rw [hb0, show zTileLetter ZTile.zero = Letter.p from rfl, show vV Letter.p true ((0 : ℤ), (2 : ℤ)) = 0 by decide]
    at vPD
  rw [hb0, show vV Letter.q true e₁ = 0 from rfl] at vPA
  have eD : texV2 (parentsAt w).odd + (1, -2) + (0, 2) = e₁ + texV2 (parentsAt w).odd := by
    ext <;> (simp; try ring)
  rw [eD] at vPD
  simp only [zero_add] at vPA
  have sP := zoH0_shift_even e₁ (texV2 (parentsAt w).odd) (-(parentsAt w).odd.num) (parentsAt w).odd.den
    (by simp only [texV2]; ring) (by simp only [texV2]; ring) (by simp only [texV2]; omega)
  have h10 : zoH0 e₁ = 0 := by decide
  -- the point `z* = U + B`
  have hm1 : mEven w u1 u2 1 = shiftS (marksOdd u1) (texV1Even (parentsAt w).even + texV2 (parentsAt w).odd) := by
    simp [mEven, pieceSet, hP]
  have hm4 : mEven w u1 u2 4 = shiftS (marksEven u2) 0 := by simp [mEven, pieceSet, hP, hQ]
  have hzin : texV1Even (parentsAt w).even + texV2 (parentsAt w).odd ∈
        shiftS (marksOdd u1) (texV1Even (parentsAt w).even + texV2 (parentsAt w).odd) ∧
      texV1Even (parentsAt w).even + texV2 (parentsAt w).odd ∈ shiftS (marksEven u2) 0 := by
    have hd := MixedFromCells.mixedEven_all w hw u1 u2 hT1 hT2
      (texV1Even (parentsAt w).even + texV2 (parentsAt w).odd) (by simp [pOffsetsEven, phase_zero_of w hph])
      0 (by simp [qOffsetsEven, phase_zero_of w hph]) (texV1Even (parentsAt w).even + texV2 (parentsAt w).odd)
    apply hd
    · refine mem_shift _ _ _ 0 ?_ (by abel)
      exact Finset.mem_coe.1 (MarksIn.marksOdd_sub u1 (ClosedPathContacts.corner_marks_odd u1).1)
    · refine mem_shift _ _ _ (texV1Even (parentsAt w).even + texV2 (parentsAt w).odd) ?_ (by abel)
      apply Finset.mem_coe.2
      apply hInQ
      unfold placedSites
      refine List.mem_flatMap.2 ⟨(vStringAt (Letter.p :: t) (texV1Even (parentsAt w).even - (1, 1))).getD dpN
        (ZTile.zero, 0), ?_, ?_⟩
      · rw [hXQ', ht]
        apply List.mem_append_right
        rw [List.getD_eq_getElem _ _ hlenk]
        exact List.getElem_mem hlenk
      · rw [htk]
        refine List.mem_map.2 ⟨(1, 1), (h11 _).1, ?_⟩
        show ((1 : ℤ), (1 : ℤ)) + (texV1Even (parentsAt w).even - (1, 1) + texV2 (parentsAt w).odd) =
          texV1Even (parentsAt w).even + texV2 (parentsAt w).odd
        abel
  refine ⟨texV1Even (parentsAt w).even + texV2 (parentsAt w).odd, ?_, ?_, ?_⟩
  · rw [hm1]; exact hzin.1
  · rw [hm4]; exact hzin.2
  · have h0 : IsPiece (placedEven w oP oQ c 0) oP (texV1Even (parentsAt w).even) 0 (c 0) := fun z => by
      simp [placedEven, hP, affEven]
    have h1 : IsPiece (placedEven w oP oQ c 1) oP (texV1Even (parentsAt w).even + texV2 (parentsAt w).odd)
        ((parentsAt w).odd.num, -(parentsAt w).odd.den) (c 1) := fun z => by simp [placedEven, hP, affEven]
    have h4 : IsPiece (placedEven w oP oQ c 4) oQ 0 0 (c 4) := fun z => by simp [placedEven, hQ, affEven]
    rw [piece_val h1 (texV1Even (parentsAt w).even + texV2 (parentsAt w).odd) 0 (by abel),
      piece_val h4 (texV1Even (parentsAt w).even + texV2 (parentsAt w).odd)
        (texV1Even (parentsAt w).even + texV2 (parentsAt w).odd) (by abel),
      piece_val h1 (texV1Even (parentsAt w).even + (texV2 (parentsAt w).odd + e₁)) e₁ (by abel),
      piece_val h0 (texV1Even (parentsAt w).even + (texV2 (parentsAt w).odd + e₁)) (texV2 (parentsAt w).odd + e₁)
        (by abel),
      piece_val h0 (texV1Even (parentsAt w).even) 0 (by abel),
      piece_val h4 (texV1Even (parentsAt w).even) (texV1Even (parentsAt w).even) (by abel)]
    have hPe : oP (texV2 (parentsAt w).odd + e₁) = oP (e₁ + texV2 (parentsAt w).odd) := by rw [add_comm]
    rw [hPe]
    simp only [texV1Even, texV2, Prod.fst_add, Prod.snd_add] at vQk vQ0 sQ
    simp only [texV2, e₁, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero] at vPD vPA sP
    simp only [dot2, texV1Even, texV2, e₁, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero] at ha1 ha2 ⊢
    simp only [zero_mul, add_zero, sub_zero, mul_zero] at vPD vPA
    have haB : a0.1 * ((parentsAt w).odd.num - (parentsAt w).odd.den) + a0.2 * ((parentsAt w).odd.num + (parentsAt w).odd.den) =
        (parentsAt w).even.num * (parentsAt w).odd.den - (parentsAt w).even.den * (parentsAt w).odd.num := by
      have h2 : 2 * (a0.1 * ((parentsAt w).odd.num - (parentsAt w).odd.den) +
          a0.2 * ((parentsAt w).odd.num + (parentsAt w).odd.den)) =
          2 * ((parentsAt w).even.num * (parentsAt w).odd.den - (parentsAt w).even.den * (parentsAt w).odd.num) := by
        linear_combination ((parentsAt w).odd.num - (parentsAt w).odd.den) * ha1 +
          ((parentsAt w).odd.num + (parentsAt w).odd.den) * ha2
      linarith
    linear_combination -vQk + vQ0 + sQ + vPD - vPA - sP - haB

/-! ### Positions of the reversed vertical string -/

theorem vRevOffset_eq (a b : Letter) :
    vRevOffset a b + ClosedPathCorners.revShift a = vOffset a + ClosedPathCorners.revShift b := by
  cases a <;> cases b <;> ext <;> simp [vRevOffset, vOffset, ClosedPathCorners.revShift]

/-- The positions of a reversed vertical string telescope: `posF + δ(u₀) = Σ_{i<k} vOffset(u_i) + δ(u_k)`. -/
theorem vrev_posF (u : BinaryWord) : ∀ k, k < u.length →
    posF Orientation.vertical true (fun j => u.getD j Letter.p) k + ClosedPathCorners.revShift (u.getD 0 Letter.p) =
      ((u.take k).map vOffset).sum + ClosedPathCorners.revShift (u.getD k Letter.p)
  | 0, _ => by simp [posF]
  | k + 1, hk => by
    have ih := vrev_posF u k (by omega)
    have e := vRevOffset_eq (u.getD k Letter.p) (u.getD (k + 1) Letter.p)
    have ht : u.take (k + 1) = u.take k ++ [u.getD k Letter.p] := by
      rw [List.take_add_one, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      rfl
    simp only [posF, stepOf_vert_rev] at ih ⊢
    rw [ht, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    have i1 := congrArg Prod.fst ih
    have i2 := congrArg Prod.snd ih
    have e1 := congrArg Prod.fst e
    have e2 := congrArg Prod.snd e
    simp only [Prod.fst_add, Prod.snd_add] at i1 i2 e1 e2
    ext
    · simp only [Prod.fst_add]; linarith
    · simp only [Prod.snd_add]; linarith

/-- **The `k`-th tile of a reversed vertical string**: the letter of `k`, at the start plus the vertical steps of the first `k`
letters, corrected by `δ`. -/
theorem vrev_tile (u : BinaryWord) (c : GInt) (k : ℕ) (hk : k < u.length) :
    (vRevStringAt u c).getD k (ZTile.zero, 0) =
      (letterZTile (u.getD k Letter.p), c + ((u.take k).map vOffset).sum +
        ClosedPathCorners.revShift (u.getD k Letter.p) - ClosedPathCorners.revShift (u.getD 0 Letter.p)) := by
  apply Prod.ext
  · exact vRevStringAt_getD_fst u c k hk
  · have hlen : (List.scanl (· + ·) c ((u.zip u.tail).map fun ab => vRevOffset ab.1 ab.2)).length ≤
        (u.map letterZTile).length := by
      obtain ⟨a, r, rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos (by omega : 0 < u.length))
      simp
    have hm : (vRevStringAt u c).map Prod.snd =
        List.scanl (· + ·) c ((u.zip u.tail).map fun ab => vRevOffset ab.1 ab.2) := by
      unfold vRevStringAt
      exact List.map_snd_zip hlen
    have h2 : ((vRevStringAt u c).getD k (ZTile.zero, 0)).2 =
        (List.scanl (· + ·) c ((u.zip u.tail).map fun ab => vRevOffset ab.1 ab.2)).getD k 0 := by
      rw [← hm, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
      generalize (vRevStringAt u c)[k]? = o
      cases o <;> simp
    rw [h2, vRev_pos_gen u c k hk]
    have := vrev_posF u k hk
    rw [show c + posF Orientation.vertical true (fun j => u.getD j Letter.p) k =
      c + (posF Orientation.vertical true (fun j => u.getD j Letter.p) k +
        ClosedPathCorners.revShift (u.getD 0 Letter.p)) - ClosedPathCorners.revShift (u.getD 0 Letter.p) by abel, this]
    abel

/-! ### The optional interface `(P^{+,2}, Q^+)`, `W_1` odd -/

/-- The ceiling inequalities of the vertical word of `Q` at `d_q - d_p` letters, for `n_p d_q - n_q d_p = 1`. -/
theorem vceil_facts_of (np dp nq dq : ℤ) (hdet : np * dq - nq * dp = 1) (hdq : 2 ≤ dq) :
    dq * (dq - dp - nq + np) - dq < (dq - dp) * (dq - nq) ∧ (dq - dp) * (dq - nq) ≤ dq * (dq - dp - nq + np) := by
  constructor <;> nlinarith

/-- **The triangle identity at `(P^{+,2}, Q^+)` for `W_1` odd.** If the copies meet then `d_q > d_p`, the left vertical string
of `Q` has a tile at `v_{p,2}` or `v_{p,2} - i` (after its last `d_p` letters, with `n_p` letters `q`), and `z* = A + B` is the
second bottom corner of `P^{+,2}` and lies on that tile of `Q^+`. -/
theorem triEven_of_one (w u1 u2 : Word) (hw : ¬ Standard.IsBase w) (hT1 : (Standard.stateAt w).tOdd = oddTile u1)
    (hT2 : (Standard.stateAt w).tEven = evenTile u2) (hph : phase w = 1)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (oP oQ : ℤ × ℤ → ℤ) (c : ℕ → ℤ)
    (hRP : SurgicalWeak.RespectsAnchored (oddTile u1) (hWordOf u1 false) (vWordOf u1 false) oP)
    (hRQ : SurgicalWeak.RespectsAnchored (evenTile u2) (hWordOf u2 true) (vWordOf u2 true) oQ)
    (hsP : SigmaZero oP (texV1Odd (parentsAt w).odd)) (hsQ : SigmaZero oQ (texV1Even (parentsAt w).even)) :
    (∃ z, z ∈ mEven w u1 u2 1 ∧ z ∈ mEven w u1 u2 4) → ∃ z, z ∈ mEven w u1 u2 1 ∧ z ∈ mEven w u1 u2 4 ∧
        placedEven w oP oQ c 1 z - placedEven w oP oQ c 4 z =
          (placedEven w oP oQ c 1 (texV2 (parentsAt w).odd + e₁) -
            placedEven w oP oQ c 0 (texV2 (parentsAt w).odd + e₁)) +
          (placedEven w oP oQ c 0 (texV1Odd (parentsAt w).odd) -
            placedEven w oP oQ c 4 (texV1Odd (parentsAt w).odd)) := by
  rintro ⟨z0, hz1, hz4⟩
  have hP := evenP_of w hph
  have hQ := evenQ_of w hph
  have hd1 := mEven_sub w u1 u2 1 hz1
  have hd4 := mEven_sub w u1 u2 4 hz4
  simp only [dEven, pieceSet, hP, hQ] at hd1 hd4
  simp at hd1 hd4
  have b1 := box_shift_odd u1 _ z0 hd1
  have b4 := box_shift_even u2 _ z0 hd4
  rw [← hp] at b1
  rw [← hq] at b4
  simp only [texV2, texV1Odd] at b1 b4
  have hov : (parentsAt w).odd.den + (parentsAt w).even.num + 1 ≤ (parentsAt w).odd.num + (parentsAt w).even.den := by
    omega
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
  obtain ⟨hInQ, hRQb, -, hRQl, -⟩ := hRQ
  obtain ⟨-, hRPb, -, hRPl, -⟩ := hRP
  obtain ⟨hhq, hlq⟩ := hWordOf_head_last u2 true
  have hXQ := TexVPositions.lastPos_hWordOf_true_tex u2
  rw [← hq] at hXQ
  obtain ⟨βQ, hQA, -⟩ := fwd_corner_tiles (hWordOf u2 true) oQ _ hhq hlq hXQ hRQb hsQ
  obtain ⟨hhp, hlp⟩ := hWordOf_head_last u1 false
  have hXP := TexVPositions.lastPos_hWordOf_false_tex u1
  rw [← hp] at hXP
  obtain ⟨βP, hPA, -⟩ := fwd_corner_tiles (hWordOf u1 false) oP _ hhp hlp hXP hRPb hsP
  have hdpq : (parentsAt w).odd.den + 1 ≤ (parentsAt w).even.den := by
    by_contra h
    rw [not_le] at h
    have h1 : 0 ≤ ((parentsAt w).odd.den - (parentsAt w).even.den) * ((parentsAt w).even.den - (parentsAt w).even.num) :=
      mul_nonneg (by omega) (by omega)
    have h2 : 0 ≤ ((parentsAt w).odd.num - ((parentsAt w).odd.den - (parentsAt w).even.den + (parentsAt w).even.num + 1)) *
        (parentsAt w).even.den := mul_nonneg (by omega) (by omega)
    nlinarith
  -- the vertical word of `Q`
  obtain ⟨hvh, hvl⟩ := StringCorners.vWord_even_head_last u2
  have hvc := StringCorners.vWord_even_counts u2
  rw [hce, ← hq] at hvc
  obtain ⟨t, ht⟩ : ∃ t, vWordOf u2 true = Letter.p :: t := by
    cases h : vWordOf u2 true with
    | nil => rw [h] at hvh; simp at hvh
    | cons a t =>
      rw [h] at hvh
      simp only [List.head?_cons, Option.some.injEq] at hvh
      exact ⟨t, by rw [hvh]⟩
  have hvlen : ((Letter.p :: t).length : ℤ) = (parentsAt w).even.den := by
    have h := length_eq_counts (vWordOf u2 true)
    rw [ht] at h hvc
    have h' : ((Letter.p :: t).length : ℤ) = ((Letter.p :: t).count Letter.p : ℤ) + ((Letter.p :: t).count Letter.q : ℤ) :=
      by exact_mod_cast h
    rw [h', hvc.1, hvc.2]
    ring
  have hqtot : qPrefix (Letter.p :: t) (Letter.p :: t).length = (parentsAt w).even.num := by
    unfold qPrefix
    rw [List.take_length]
    rw [ht] at hvc
    exact hvc.2
  have hcwv := SiteHullEven.cw_childP_swap u2
  rw [hce, ← hq] at hcwv
  have hvw : vWordOf u2 true = (quadAt [] (Standard.swapW u2)).childP.map swapLetter := rfl
  have hxl : ((quadAt [] (Standard.swapW u2)).childP.length : ℤ) = (parentsAt w).even.den := hcwv.1
  set dpN : ℕ := (parentsAt w).odd.den.toNat with hdpNdef
  have hdpN : (dpN : ℤ) = (parentsAt w).odd.den := Int.toNat_of_nonneg (by omega)
  set jN : ℕ := ((parentsAt w).even.den - (parentsAt w).odd.den).toNat with hjNdef
  have hjN : (jN : ℤ) = (parentsAt w).even.den - (parentsAt w).odd.den := Int.toNat_of_nonneg (by omega)
  have hjx : jN ≤ (quadAt [] (Standard.swapW u2)).childP.length := by
    have : (jN : ℤ) ≤ ((quadAt [] (Standard.swapW u2)).childP.length : ℤ) := by rw [hjN, hxl]; omega
    exact_mod_cast this
  have hcntj : qPrefix (Letter.p :: t) jN = (parentsAt w).even.num - (parentsAt w).odd.num := by
    rw [← ht, hvw, qPrefix_swap _ _ hjx]
    obtain ⟨h1, h2⟩ := hcwv.2 jN (by rw [hjN]; omega)
    rw [hjN] at h1 h2
    obtain ⟨f1, f2⟩ := vceil_facts_of (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
      (parentsAt w).even.den (by linarith) (by omega)
    have := ceil_unique (parentsAt w).even.den
      (((parentsAt w).even.den - (parentsAt w).odd.den) * ((parentsAt w).even.den - (parentsAt w).even.num)) _
      ((parentsAt w).even.den - (parentsAt w).odd.den - (parentsAt w).even.num + (parentsAt w).odd.num)
      (by omega) h1 h2 f1 f2
    rw [hjN, this]
    ring
  -- the left vertical string of `Q` from `0`
  have hneQ : (vWordOf u2 true).reverse ≠ [] := by rw [ht]; simp
  have hhdQ : (vWordOf u2 true).reverse.headD Letter.p = Letter.q := by
    rw [List.headD_eq_head?_getD, List.head?_reverse, hvl]
    rfl
  have hd0Q : (((0 : GInt) - cstarV ((vWordOf u2 true).reverse.headD Letter.p) true).1 +
      ((0 : GInt) - cstarV ((vWordOf u2 true).reverse.headD Letter.p) true).2) % 2 = 0 := by
    rw [hhdQ]
    decide
  obtain ⟨b0, KQ, hVQ⟩ := VerticalStepOne.reversed_vertical_formula _ 0 oQ hneQ hRQl hd0Q
  have hg0Q : (vWordOf u2 true).reverse.getD 0 Letter.p = Letter.q := by
    rw [List.getD_eq_getElem?_getD, ← List.head?_eq_getElem?, List.head?_reverse, hvl]
    rfl
  have hlenQ : (vRevStringAt (vWordOf u2 true).reverse 0).length = (vWordOf u2 true).reverse.length :=
    vRevStringAt_length _ _
  have hposQ : 0 < (vWordOf u2 true).reverse.length := List.length_pos_of_ne_nil hneQ
  have hQ0 : (vRevStringAt (vWordOf u2 true).reverse 0).getD 0 (ZTile.zero, 0) = (ZTile.one, 0) := by
    apply Prod.ext
    · rw [vRevStringAt_getD_fst _ _ 0 hposQ, hg0Q]
      rfl
    · exact vRevStringAt_getD_snd_zero _ _ hneQ
  have hVQ0 : ∀ u ∈ tileShape ZTile.one, oQ (0 + u) + zoH0 (0 + u) - (b0.1 * (0 + u).1 + b0.2 * (0 + u).2) =
      vV Letter.q true u + KQ := by
    intro u hu
    have h := hVQ 0 (by rw [hlenQ]; exact hposQ) u (by rw [hQ0]; exact hu)
    rw [hQ0] at h
    exact h
  have hb0 := vleft_a0 oQ b0 βQ KQ hQA hVQ0
  have hdpu : dpN < (vWordOf u2 true).reverse.length := by
    have : (dpN : ℤ) < ((vWordOf u2 true).reverse.length : ℤ) := by
      rw [List.length_reverse, ht, hdpN, hvlen]; omega
    exact_mod_cast this
  have htk := vrev_tile (vWordOf u2 true).reverse 0 dpN hdpu
  have hcq : (((vWordOf u2 true).reverse.take dpN).count Letter.q : ℤ) = (parentsAt w).odd.num := by
    rw [ht, count_reverse_take, hqtot]
    have hlj : (Letter.p :: t).length - dpN = jN := by
      have : ((Letter.p :: t).length : ℤ) - dpN = jN := by rw [hvlen, hdpN, hjN]
      omega
    rw [hlj, hcntj]
    ring
  rw [hg0Q, vOffset_sum, hcq, List.length_take, min_eq_left hdpu.le, hdpN] at htk
  have hlenk : dpN < (vRevStringAt (vWordOf u2 true).reverse 0).length := by rw [hlenQ]; exact hdpu
  -- the value of `Q` at `B`, on the tile of its left string after `d_p` letters
  have hB : ∃ r : GInt, ((vRevStringAt (vWordOf u2 true).reverse 0).getD dpN (ZTile.zero, 0)).2 + r =
        texV2 (parentsAt w).odd ∧ r ∈ tileShape ((vRevStringAt (vWordOf u2 true).reverse 0).getD dpN (ZTile.zero, 0)).1 ∧
        vV (zTileLetter ((vRevStringAt (vWordOf u2 true).reverse 0).getD dpN (ZTile.zero, 0)).1) true r = 0 := by
    rw [htk]
    by_cases hl : (vWordOf u2 true).reverse.getD dpN Letter.p = Letter.q
    · rw [hl]
      refine ⟨((0 : ℤ), (0 : ℤ)), ?_, (by decide : ((0 : ℤ), (0 : ℤ)) ∈ tileShape ZTile.one), rfl⟩
      simp only [ClosedPathCorners.revShift, texV2]
      ext <;> (simp; try ring)
    · have hl' : (vWordOf u2 true).reverse.getD dpN Letter.p = Letter.p := by
        cases h : (vWordOf u2 true).reverse.getD dpN Letter.p
        · rfl
        · exact absurd h hl
      rw [hl']
      refine ⟨((0 : ℤ), (1 : ℤ)), ?_, (by decide : ((0 : ℤ), (1 : ℤ)) ∈ tileShape ZTile.zero),
        (by decide : vV Letter.p true ((0 : ℤ), (1 : ℤ)) = 0)⟩
      simp only [ClosedPathCorners.revShift, texV2]
      ext <;> (simp; try ring)
  obtain ⟨r, hr, hrs, hrv⟩ := hB
  have vQB := hVQ dpN hlenk r hrs
  rw [hr, hrv, hb0] at vQB
  have vQ0 := hVQ0 0 (by decide)
  rw [hb0, show vV Letter.q true (0 : GInt) = 0 from rfl] at vQ0
  simp only [Prod.fst_zero, Prod.snd_zero, zero_mul, add_zero, sub_zero, zero_add] at vQB vQ0
  have hz00 : zoH0 (0 : GInt) = 0 := by decide
  -- the left vertical string of `P` from `0`
  obtain ⟨hvhp, hvlp⟩ := StringCorners.vertWord_head_last u1
  have hwv : vWordOf u1 false = vertWord u1 := rfl
  have hne : (vWordOf u1 false).reverse ≠ [] := by
    rw [hwv]
    intro h
    rw [List.reverse_eq_nil_iff] at h
    rw [h] at hvhp
    simp at hvhp
  have hhd : (vWordOf u1 false).reverse.headD Letter.p = Letter.q := by
    rw [List.headD_eq_head?_getD, List.head?_reverse, hwv, hvlp]
    rfl
  have hd0P : (((0 : GInt) - cstarV ((vWordOf u1 false).reverse.headD Letter.p) true).1 +
      ((0 : GInt) - cstarV ((vWordOf u1 false).reverse.headD Letter.p) true).2) % 2 = 0 := by
    rw [hhd]
    decide
  obtain ⟨bP, KP, hVP⟩ := VerticalStepOne.reversed_vertical_formula _ 0 oP hne hRPl hd0P
  have hg0 : (vWordOf u1 false).reverse.getD 0 Letter.p = Letter.q := by
    rw [List.getD_eq_getElem?_getD, ← List.head?_eq_getElem?, List.head?_reverse, hwv, hvlp]
    rfl
  have hlenP : (vRevStringAt (vWordOf u1 false).reverse 0).length = (vWordOf u1 false).reverse.length :=
    vRevStringAt_length _ _
  have hposP : 0 < (vWordOf u1 false).reverse.length := List.length_pos_of_ne_nil hne
  have hP0 : (vRevStringAt (vWordOf u1 false).reverse 0).getD 0 (ZTile.zero, 0) = (ZTile.one, 0) := by
    apply Prod.ext
    · rw [vRevStringAt_getD_fst _ _ 0 hposP, hg0]
      rfl
    · exact vRevStringAt_getD_snd_zero _ _ hne
  have hVP0 : ∀ u ∈ tileShape ZTile.one, oP (0 + u) + zoH0 (0 + u) - (bP.1 * (0 + u).1 + bP.2 * (0 + u).2) =
      vV Letter.q true u + KP := by
    intro u hu
    have h := hVP 0 (by rw [hlenP]; exact hposP) u (by rw [hP0]; exact hu)
    rw [hP0] at h
    exact h
  have hbP := vleft_a0 oP bP βP KP hPA hVP0
  have hgl : (vWordOf u1 false).reverse.getD ((vWordOf u1 false).reverse.length - 1) Letter.p = Letter.p := by
    rw [List.getD_eq_getElem?_getD, ← List.getLast?_eq_getElem?, List.getLast?_reverse, hwv, hvhp]
    rfl
  have hYP := StdCornerAnchors.stdAnchorY_odd u1
  rw [← hp] at hYP
  have hPl : (vRevStringAt (vWordOf u1 false).reverse 0).getD ((vWordOf u1 false).reverse.length - 1) (ZTile.zero, 0) =
      (ZTile.zero, texV2 (parentsAt w).odd + (1, -2)) := by
    apply Prod.ext
    · rw [vRevStringAt_getD_fst _ _ _ (by omega), hgl]
      rfl
    · rw [← hYP, lastPosOf_eq_getD, hlenP]
  have vPD := hVP ((vWordOf u1 false).reverse.length - 1) (by rw [hlenP]; omega) (0, 2) (by
    rw [hPl]
    exact (by decide : ((0 : ℤ), (2 : ℤ)) ∈ tileShape ZTile.zero))
  rw [hPl] at vPD
  have vPA := hVP0 e₁ (by decide)
  rw [hbP, show zTileLetter ZTile.zero = Letter.p from rfl, show vV Letter.p true ((0 : ℤ), (2 : ℤ)) = 0 by decide]
    at vPD
  rw [hbP, show vV Letter.q true e₁ = 0 from rfl] at vPA
  have eD : texV2 (parentsAt w).odd + (1, -2) + (0, 2) = e₁ + texV2 (parentsAt w).odd := by
    ext <;> (simp; try ring)
  rw [eD] at vPD
  simp only [zero_add] at vPA
  have sP := zoH0_shift_even e₁ (texV2 (parentsAt w).odd) (-(parentsAt w).odd.num) (parentsAt w).odd.den
    (by simp only [texV2]; ring) (by simp only [texV2]; ring) (by simp only [texV2]; omega)
  have h10 : zoH0 e₁ = 0 := by decide
  -- the point `z* = A + B`
  have hm1 : mEven w u1 u2 1 = shiftS (marksOdd u1) (texV2 (parentsAt w).odd) := by simp [mEven, pieceSet, hP]
  have hm4 : mEven w u1 u2 4 = shiftS (marksEven u2) (texV1Odd (parentsAt w).odd) := by
    simp [mEven, pieceSet, hP, hQ]
  have hzin : texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd ∈ shiftS (marksOdd u1) (texV2 (parentsAt w).odd) ∧
      texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd ∈ shiftS (marksEven u2) (texV1Odd (parentsAt w).odd) := by
    have hd := MixedFromCells.mixedEven_all w hw u1 u2 hT1 hT2
      (texV2 (parentsAt w).odd) (by simp [pOffsetsEven, hph])
      (texV1Odd (parentsAt w).odd) (by simp [qOffsetsEven, hph]) (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd)
    apply hd
    · refine mem_shift _ _ _ (texV1Odd (parentsAt w).odd) ?_ (by abel)
      have h := (ClosedPathContacts.corner_marks_odd u1).2.2.2.1
      rw [← hp] at h
      exact Finset.mem_coe.1 (MarksIn.marksOdd_sub u1 h)
    · refine mem_shift _ _ _ (texV2 (parentsAt w).odd) ?_ (by abel)
      apply Finset.mem_coe.2
      apply hInQ
      unfold placedSites
      refine List.mem_flatMap.2 ⟨(vRevStringAt (vWordOf u2 true).reverse 0).getD dpN (ZTile.zero, 0), ?_, ?_⟩
      · apply List.mem_append_left
        apply List.mem_append_right
        rw [List.getD_eq_getElem _ _ hlenk]
        exact List.getElem_mem hlenk
      · refine List.mem_map.2 ⟨r, hrs, ?_⟩
        show r + ((vRevStringAt (vWordOf u2 true).reverse 0).getD dpN (ZTile.zero, 0)).2 = texV2 (parentsAt w).odd
        rw [add_comm, hr]
  refine ⟨texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd, ?_, ?_, ?_⟩
  · rw [hm1]; exact hzin.1
  · rw [hm4]; exact hzin.2
  · have h0 : IsPiece (placedEven w oP oQ c 0) oP 0 0 (c 0) := fun z => by simp [placedEven, hP, affEven]
    have h1 : IsPiece (placedEven w oP oQ c 1) oP (texV2 (parentsAt w).odd)
        ((parentsAt w).odd.num, -(parentsAt w).odd.den) (c 1) := fun z => by simp [placedEven, hP, affEven]
    have h4 : IsPiece (placedEven w oP oQ c 4) oQ (texV1Odd (parentsAt w).odd) 0 (c 4) := fun z => by
      simp [placedEven, hQ, affEven]
    rw [piece_val h1 (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd) (texV1Odd (parentsAt w).odd) (by abel),
      piece_val h4 (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd) (texV2 (parentsAt w).odd) (by abel),
      piece_val h1 (texV2 (parentsAt w).odd + e₁) e₁ (by abel),
      piece_val h0 (texV2 (parentsAt w).odd + e₁) (texV2 (parentsAt w).odd + e₁) (by abel),
      piece_val h0 (texV1Odd (parentsAt w).odd) (texV1Odd (parentsAt w).odd) (by abel),
      piece_val h4 (texV1Odd (parentsAt w).odd) 0 (by abel)]
    have hPe : oP (texV2 (parentsAt w).odd + e₁) = oP (e₁ + texV2 (parentsAt w).odd) := by rw [add_comm]
    rw [hPe]
    simp only [texV2, e₁, Prod.fst_add, Prod.snd_add] at vPD vPA sP
    simp only [zero_mul, add_zero, sub_zero, mul_zero, Prod.fst_zero, Prod.snd_zero] at vPD vPA
    simp only [dot2, texV1Odd, texV2, e₁, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero] at vQB ⊢
    linear_combination -vQB + vQ0 + vPD - vPA - sP - hz00

/-! ### The optional interface `(P^{-,1}, Q^-)`, `W_1` even -/

/-- **The triangle identity at `(P^{-,1}, Q^-)` for `W_1` even.** If the copies meet then `d_q > d_p`, the left vertical string
of `Q` has a tile at `v_{q,2} + 1 - 2i - v_{p,2}` (or one unit higher), and `z* = A + B + V + 1 - i` is the last top corner of
`P^{-,1}` and lies on that tile of `Q^-`. -/
theorem triEven_ef_two (w u1 u2 : Word) (hw : ¬ Standard.IsBase w) (hT1 : (Standard.stateAt w).tOdd = oddTile u1)
    (hT2 : (Standard.stateAt w).tEven = evenTile u2) (hph : phase w ≠ 1)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (oP oQ : ℤ × ℤ → ℤ) (c : ℕ → ℤ)
    (hRP : SurgicalWeak.RespectsAnchored (oddTile u1) (hWordOf u1 false) (vWordOf u1 false) oP)
    (hRQ : SurgicalWeak.RespectsAnchored (evenTile u2) (hWordOf u2 true) (vWordOf u2 true) oQ)
    (hsP : SigmaZero oP (texV1Odd (parentsAt w).odd)) (hsQ : SigmaZero oQ (texV1Even (parentsAt w).even)) :
    (∃ z, z ∈ mEven w u1 u2 2 ∧ z ∈ mEven w u1 u2 5) → ∃ z, z ∈ mEven w u1 u2 2 ∧ z ∈ mEven w u1 u2 5 ∧
        placedEven w oP oQ c 2 z - placedEven w oP oQ c 5 z =
          (placedEven w oP oQ c 2 (texV2 (parentsAt w).even + texV2 (parentsAt w).odd + e₁) -
            placedEven w oP oQ c 3 (texV2 (parentsAt w).even + texV2 (parentsAt w).odd + e₁)) +
          (placedEven w oP oQ c 3 (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + texV2 (parentsAt w).odd +
              (texV2 (parentsAt w).even + e₁ - e₂)) -
            placedEven w oP oQ c 5 (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + texV2 (parentsAt w).odd +
              (texV2 (parentsAt w).even + e₁ - e₂))) := by
  rintro ⟨z0, hz2, hz5⟩
  have hP := evenP_ef w hph
  have hQ := evenQ_ef w hph
  have hd2 := mEven_sub w u1 u2 2 hz2
  have hd5 := mEven_sub w u1 u2 5 hz5
  simp only [dEven, pieceSet, hP, hQ] at hd2 hd5
  simp at hd2 hd5
  have b2 := box_shift_odd u1 _ z0 hd2
  have b5 := box_shift_even u2 _ z0 hd5
  rw [← hp] at b2
  rw [← hq] at b5
  simp only [texV2, texV1Odd, Prod.fst_add, Prod.snd_add] at b2 b5
  have hov : (parentsAt w).odd.num + (parentsAt w).odd.den + 1 ≤ (parentsAt w).even.num + (parentsAt w).even.den := by
    omega
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
  obtain ⟨hInQ, hRQb, -, hRQl, -⟩ := hRQ
  obtain ⟨-, hRPb, -, hRPl, -⟩ := hRP
  obtain ⟨hhq, hlq⟩ := hWordOf_head_last u2 true
  have hXQ := TexVPositions.lastPos_hWordOf_true_tex u2
  rw [← hq] at hXQ
  obtain ⟨βQ, hQA, -⟩ := fwd_corner_tiles (hWordOf u2 true) oQ _ hhq hlq hXQ hRQb hsQ
  obtain ⟨hhp, hlp⟩ := hWordOf_head_last u1 false
  have hXP := TexVPositions.lastPos_hWordOf_false_tex u1
  rw [← hp] at hXP
  obtain ⟨βP, hPA, -⟩ := fwd_corner_tiles (hWordOf u1 false) oP _ hhp hlp hXP hRPb hsP
  have hdpq : (parentsAt w).odd.den + 1 ≤ (parentsAt w).even.den := by
    by_contra h
    rw [not_le] at h
    nlinarith
  -- the vertical word of `Q`
  obtain ⟨hvh, hvl⟩ := StringCorners.vWord_even_head_last u2
  have hvc := StringCorners.vWord_even_counts u2
  rw [hce, ← hq] at hvc
  obtain ⟨t, ht⟩ : ∃ t, vWordOf u2 true = Letter.p :: t := by
    cases h : vWordOf u2 true with
    | nil => rw [h] at hvh; simp at hvh
    | cons a t =>
      rw [h] at hvh
      simp only [List.head?_cons, Option.some.injEq] at hvh
      exact ⟨t, by rw [hvh]⟩
  have hvlen : ((Letter.p :: t).length : ℤ) = (parentsAt w).even.den := by
    have h := length_eq_counts (vWordOf u2 true)
    rw [ht] at h hvc
    have h' : ((Letter.p :: t).length : ℤ) = ((Letter.p :: t).count Letter.p : ℤ) + ((Letter.p :: t).count Letter.q : ℤ) :=
      by exact_mod_cast h
    rw [h', hvc.1, hvc.2]
    ring
  have hqtot : qPrefix (Letter.p :: t) (Letter.p :: t).length = (parentsAt w).even.num := by
    unfold qPrefix
    rw [List.take_length]
    rw [ht] at hvc
    exact hvc.2
  have hcwv := SiteHullEven.cw_childP_swap u2
  rw [hce, ← hq] at hcwv
  have hvw : vWordOf u2 true = (quadAt [] (Standard.swapW u2)).childP.map swapLetter := rfl
  have hxl : ((quadAt [] (Standard.swapW u2)).childP.length : ℤ) = (parentsAt w).even.den := hcwv.1
  set dpN : ℕ := (parentsAt w).odd.den.toNat with hdpNdef
  have hdpN : (dpN : ℤ) = (parentsAt w).odd.den := Int.toNat_of_nonneg (by omega)
  have hk1 : dpN + 1 ≤ (quadAt [] (Standard.swapW u2)).childP.length := by
    have : (dpN : ℤ) + 1 ≤ ((quadAt [] (Standard.swapW u2)).childP.length : ℤ) := by rw [hdpN, hxl]; omega
    exact_mod_cast this
  have hcnt : qPrefix (Letter.p :: t) (dpN + 1) = (parentsAt w).odd.num := by
    rw [← ht, hvw, qPrefix_swap _ _ hk1]
    obtain ⟨h1, h2⟩ := hcwv.2 (dpN + 1) (by push_cast; omega)
    push_cast at h1 h2
    rw [hdpN] at h1 h2
    obtain ⟨f1, f2⟩ := vceil_facts (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
      (parentsAt w).even.den (-1) (by linarith) (Or.inr rfl) (by omega) (by omega)
    have := ceil_unique (parentsAt w).even.den (((parentsAt w).odd.den + 1) *
      ((parentsAt w).even.den - (parentsAt w).even.num)) _ ((parentsAt w).odd.den + 1 - (parentsAt w).odd.num)
      (by omega) h1 h2 f1 f2
    push_cast
    rw [hdpN, this]
    ring
  -- the left vertical string of `Q` from `0`
  have hneQ : (vWordOf u2 true).reverse ≠ [] := by rw [ht]; simp
  have hhdQ : (vWordOf u2 true).reverse.headD Letter.p = Letter.q := by
    rw [List.headD_eq_head?_getD, List.head?_reverse, hvl]
    rfl
  have hd0Q : (((0 : GInt) - cstarV ((vWordOf u2 true).reverse.headD Letter.p) true).1 +
      ((0 : GInt) - cstarV ((vWordOf u2 true).reverse.headD Letter.p) true).2) % 2 = 0 := by
    rw [hhdQ]
    decide
  obtain ⟨b0, KQ, hVQ⟩ := VerticalStepOne.reversed_vertical_formula _ 0 oQ hneQ hRQl hd0Q
  have hg0Q : (vWordOf u2 true).reverse.getD 0 Letter.p = Letter.q := by
    rw [List.getD_eq_getElem?_getD, ← List.head?_eq_getElem?, List.head?_reverse, hvl]
    rfl
  have hlenQ : (vRevStringAt (vWordOf u2 true).reverse 0).length = (vWordOf u2 true).reverse.length :=
    vRevStringAt_length _ _
  have hposQ : 0 < (vWordOf u2 true).reverse.length := List.length_pos_of_ne_nil hneQ
  have hQ0 : (vRevStringAt (vWordOf u2 true).reverse 0).getD 0 (ZTile.zero, 0) = (ZTile.one, 0) := by
    apply Prod.ext
    · rw [vRevStringAt_getD_fst _ _ 0 hposQ, hg0Q]
      rfl
    · exact vRevStringAt_getD_snd_zero _ _ hneQ
  have hVQ0 : ∀ u ∈ tileShape ZTile.one, oQ (0 + u) + zoH0 (0 + u) - (b0.1 * (0 + u).1 + b0.2 * (0 + u).2) =
      vV Letter.q true u + KQ := by
    intro u hu
    have h := hVQ 0 (by rw [hlenQ]; exact hposQ) u (by rw [hQ0]; exact hu)
    rw [hQ0] at h
    exact h
  have hb0 := vleft_a0 oQ b0 βQ KQ hQA hVQ0
  have hulen : ((vWordOf u2 true).reverse.length : ℤ) = (parentsAt w).even.den := by
    rw [List.length_reverse, ht, hvlen]
  set k0 : ℕ := (vWordOf u2 true).reverse.length - 1 - dpN with hk0def
  have hk0 : k0 < (vWordOf u2 true).reverse.length := by omega
  have hk0Z : (k0 : ℤ) = (parentsAt w).even.den - 1 - (parentsAt w).odd.den := by
    rw [hk0def]
    push_cast [Nat.sub_sub]
    omega
  have htk := vrev_tile (vWordOf u2 true).reverse 0 k0 hk0
  have hcq : (((vWordOf u2 true).reverse.take k0).count Letter.q : ℤ) =
      (parentsAt w).even.num - (parentsAt w).odd.num := by
    rw [ht, count_reverse_take, hqtot]
    have hlj : (Letter.p :: t).length - k0 = dpN + 1 := by
      have : ((Letter.p :: t).length : ℤ) - k0 = dpN + 1 := by
        rw [hk0Z, hdpN, hvlen]
        ring
      omega
    rw [hlj, hcnt]
  rw [hg0Q, vOffset_sum, hcq, List.length_take, min_eq_left hk0.le, hk0Z] at htk
  have hlenk : k0 < (vRevStringAt (vWordOf u2 true).reverse 0).length := by rw [hlenQ]; exact hk0
  have hB : ∃ r : GInt, ((vRevStringAt (vWordOf u2 true).reverse 0).getD k0 (ZTile.zero, 0)).2 + r =
        texV2 (parentsAt w).even + e₁ - e₂ - texV2 (parentsAt w).odd ∧
        r ∈ tileShape ((vRevStringAt (vWordOf u2 true).reverse 0).getD k0 (ZTile.zero, 0)).1 ∧
        vV (zTileLetter ((vRevStringAt (vWordOf u2 true).reverse 0).getD k0 (ZTile.zero, 0)).1) true r = 0 := by
    rw [htk]
    by_cases hl : (vWordOf u2 true).reverse.getD k0 Letter.p = Letter.q
    · rw [hl]
      refine ⟨((0 : ℤ), (0 : ℤ)), ?_, (by decide : ((0 : ℤ), (0 : ℤ)) ∈ tileShape ZTile.one), rfl⟩
      simp only [ClosedPathCorners.revShift, texV2, e₁, e₂]
      ext <;> simp <;> ring
    · have hl' : (vWordOf u2 true).reverse.getD k0 Letter.p = Letter.p := by
        cases h : (vWordOf u2 true).reverse.getD k0 Letter.p
        · rfl
        · exact absurd h hl
      rw [hl']
      refine ⟨((0 : ℤ), (1 : ℤ)), ?_, (by decide : ((0 : ℤ), (1 : ℤ)) ∈ tileShape ZTile.zero),
        (by decide : vV Letter.p true ((0 : ℤ), (1 : ℤ)) = 0)⟩
      simp only [ClosedPathCorners.revShift, texV2, e₁, e₂]
      ext <;> simp <;> ring
  obtain ⟨r, hr, hrs, hrv⟩ := hB
  have vQxB := hVQ k0 hlenk r hrs
  rw [hr, hrv, hb0] at vQxB
  -- the last tile of the left string of `Q`, at `V + 1 - 2i`
  have hglQ : (vWordOf u2 true).reverse.getD ((vWordOf u2 true).reverse.length - 1) Letter.p = Letter.p := by
    rw [List.getD_eq_getElem?_getD, ← List.getLast?_eq_getElem?, List.getLast?_reverse, hvh]
    rfl
  have hYQ := StdCornerAnchors.stdAnchorY_even u2
  rw [← hq] at hYQ
  have hQl : (vRevStringAt (vWordOf u2 true).reverse 0).getD ((vWordOf u2 true).reverse.length - 1) (ZTile.zero, 0) =
      (ZTile.zero, texV2 (parentsAt w).even + (1, -2)) := by
    apply Prod.ext
    · rw [vRevStringAt_getD_fst _ _ _ (by omega), hglQ]
      rfl
    · rw [← hYQ, lastPosOf_eq_getD, hlenQ]
  have vQx := hVQ ((vWordOf u2 true).reverse.length - 1) (by rw [hlenQ]; omega) (0, 1) (by
    rw [hQl]
    exact (by decide : ((0 : ℤ), (1 : ℤ)) ∈ tileShape ZTile.zero))
  rw [hQl, hb0, show zTileLetter ZTile.zero = Letter.p from rfl,
    show vV Letter.p true ((0 : ℤ), (1 : ℤ)) = 0 by decide] at vQx
  have eX : texV2 (parentsAt w).even + (1, -2) + (0, 1) = texV2 (parentsAt w).even + e₁ - e₂ := by
    ext <;> (simp; try ring)
  rw [eX] at vQx
  have sQ := zoH0_shift_even (texV2 (parentsAt w).even + e₁ - e₂ - texV2 (parentsAt w).odd) (texV2 (parentsAt w).odd)
    (-(parentsAt w).odd.num) (parentsAt w).odd.den
    (by simp only [texV2]; ring) (by simp only [texV2]; ring) (by simp only [texV2]; omega)
  rw [sub_add_cancel] at sQ
  -- the left vertical string of `P` from `0`
  obtain ⟨hvhp, hvlp⟩ := StringCorners.vertWord_head_last u1
  have hwv : vWordOf u1 false = vertWord u1 := rfl
  have hne : (vWordOf u1 false).reverse ≠ [] := by
    rw [hwv]
    intro h
    rw [List.reverse_eq_nil_iff] at h
    rw [h] at hvhp
    simp at hvhp
  have hhd : (vWordOf u1 false).reverse.headD Letter.p = Letter.q := by
    rw [List.headD_eq_head?_getD, List.head?_reverse, hwv, hvlp]
    rfl
  have hd0P : (((0 : GInt) - cstarV ((vWordOf u1 false).reverse.headD Letter.p) true).1 +
      ((0 : GInt) - cstarV ((vWordOf u1 false).reverse.headD Letter.p) true).2) % 2 = 0 := by
    rw [hhd]
    decide
  obtain ⟨bP, KP, hVP⟩ := VerticalStepOne.reversed_vertical_formula _ 0 oP hne hRPl hd0P
  have hg0 : (vWordOf u1 false).reverse.getD 0 Letter.p = Letter.q := by
    rw [List.getD_eq_getElem?_getD, ← List.head?_eq_getElem?, List.head?_reverse, hwv, hvlp]
    rfl
  have hlenP : (vRevStringAt (vWordOf u1 false).reverse 0).length = (vWordOf u1 false).reverse.length :=
    vRevStringAt_length _ _
  have hposP : 0 < (vWordOf u1 false).reverse.length := List.length_pos_of_ne_nil hne
  have hP0 : (vRevStringAt (vWordOf u1 false).reverse 0).getD 0 (ZTile.zero, 0) = (ZTile.one, 0) := by
    apply Prod.ext
    · rw [vRevStringAt_getD_fst _ _ 0 hposP, hg0]
      rfl
    · exact vRevStringAt_getD_snd_zero _ _ hne
  have hVP0 : ∀ u ∈ tileShape ZTile.one, oP (0 + u) + zoH0 (0 + u) - (bP.1 * (0 + u).1 + bP.2 * (0 + u).2) =
      vV Letter.q true u + KP := by
    intro u hu
    have h := hVP 0 (by rw [hlenP]; exact hposP) u (by rw [hP0]; exact hu)
    rw [hP0] at h
    exact h
  have hbP := vleft_a0 oP bP βP KP hPA hVP0
  have hgl : (vWordOf u1 false).reverse.getD ((vWordOf u1 false).reverse.length - 1) Letter.p = Letter.p := by
    rw [List.getD_eq_getElem?_getD, ← List.getLast?_eq_getElem?, List.getLast?_reverse, hwv, hvhp]
    rfl
  have hYP := StdCornerAnchors.stdAnchorY_odd u1
  rw [← hp] at hYP
  have hPl : (vRevStringAt (vWordOf u1 false).reverse 0).getD ((vWordOf u1 false).reverse.length - 1) (ZTile.zero, 0) =
      (ZTile.zero, texV2 (parentsAt w).odd + (1, -2)) := by
    apply Prod.ext
    · rw [vRevStringAt_getD_fst _ _ _ (by omega), hgl]
      rfl
    · rw [← hYP, lastPosOf_eq_getD, hlenP]
  have vPD := hVP ((vWordOf u1 false).reverse.length - 1) (by rw [hlenP]; omega) (0, 2) (by
    rw [hPl]
    exact (by decide : ((0 : ℤ), (2 : ℤ)) ∈ tileShape ZTile.zero))
  rw [hPl] at vPD
  have vPA := hVP0 e₁ (by decide)
  rw [hbP, show zTileLetter ZTile.zero = Letter.p from rfl, show vV Letter.p true ((0 : ℤ), (2 : ℤ)) = 0 by decide]
    at vPD
  rw [hbP, show vV Letter.q true e₁ = 0 from rfl] at vPA
  have eD : texV2 (parentsAt w).odd + (1, -2) + (0, 2) = e₁ + texV2 (parentsAt w).odd := by
    ext <;> (simp; try ring)
  rw [eD] at vPD
  simp only [zero_add] at vPA
  have sP := zoH0_shift_even e₁ (texV2 (parentsAt w).odd) (-(parentsAt w).odd.num) (parentsAt w).odd.den
    (by simp only [texV2]; ring) (by simp only [texV2]; ring) (by simp only [texV2]; omega)
  have h10 : zoH0 e₁ = 0 := by decide
  -- the point `z* = V + (A + B + 1 - i)`
  have hm2 : mEven w u1 u2 2 = shiftS (marksOdd u1) (texV2 (parentsAt w).even) := by simp [mEven, pieceSet, hP]
  have hm5 : mEven w u1 u2 5 = shiftS (marksEven u2)
      (texV1Odd (parentsAt w).odd + (texV2 (parentsAt w).odd + texV2 (parentsAt w).odd)) := by
    simp [mEven, pieceSet, hP, hQ]
  have hzin : texV2 (parentsAt w).even + (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + e₁ - e₂) ∈
        shiftS (marksOdd u1) (texV2 (parentsAt w).even) ∧
      texV2 (parentsAt w).even + (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + e₁ - e₂) ∈
        shiftS (marksEven u2) (texV1Odd (parentsAt w).odd + (texV2 (parentsAt w).odd + texV2 (parentsAt w).odd)) := by
    have hd := MixedFromCells.mixedEven_all w hw u1 u2 hT1 hT2
      (texV2 (parentsAt w).even) (by simp [pOffsetsEven, phase_zero_of w hph])
      (texV1Odd (parentsAt w).odd + (texV2 (parentsAt w).odd + texV2 (parentsAt w).odd))
      (by simp [qOffsetsEven, phase_zero_of w hph])
      (texV2 (parentsAt w).even + (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + e₁ - e₂))
    apply hd
    · refine mem_shift _ _ _ (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + e₁ - e₂) ?_ (by abel)
      have h := (ClosedPathContacts.corner_marks_odd u1).2.2.2.2.2.2.1
      rw [← hp] at h
      exact Finset.mem_coe.1 (MarksIn.marksOdd_sub u1 h)
    · refine mem_shift _ _ _ (texV2 (parentsAt w).even + e₁ - e₂ - texV2 (parentsAt w).odd) ?_ (by abel)
      apply Finset.mem_coe.2
      apply hInQ
      unfold placedSites
      refine List.mem_flatMap.2 ⟨(vRevStringAt (vWordOf u2 true).reverse 0).getD k0 (ZTile.zero, 0), ?_, ?_⟩
      · apply List.mem_append_left
        apply List.mem_append_right
        rw [List.getD_eq_getElem _ _ hlenk]
        exact List.getElem_mem hlenk
      · refine List.mem_map.2 ⟨r, hrs, ?_⟩
        show r + ((vRevStringAt (vWordOf u2 true).reverse 0).getD k0 (ZTile.zero, 0)).2 =
          texV2 (parentsAt w).even + e₁ - e₂ - texV2 (parentsAt w).odd
        rw [add_comm, hr]
  refine ⟨texV2 (parentsAt w).even + (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + e₁ - e₂), ?_, ?_, ?_⟩
  · rw [hm2]; exact hzin.1
  · rw [hm5]; exact hzin.2
  · have h2 : IsPiece (placedEven w oP oQ c 2) oP (texV2 (parentsAt w).even)
        ((parentsAt w).even.num, -(parentsAt w).even.den) (c 2) := fun z => by simp [placedEven, hP, affEven]
    have h3 : IsPiece (placedEven w oP oQ c 3) oP (texV2 (parentsAt w).even + texV2 (parentsAt w).odd)
        (((parentsAt w).odd.num, -(parentsAt w).odd.den) + ((parentsAt w).even.num, -(parentsAt w).even.den)) (c 3) :=
      fun z => by simp [placedEven, hP, affEven]
    have h5 : IsPiece (placedEven w oP oQ c 5) oQ
        (texV1Odd (parentsAt w).odd + (texV2 (parentsAt w).odd + texV2 (parentsAt w).odd))
        (((parentsAt w).odd.num, -(parentsAt w).odd.den) + ((parentsAt w).odd.num, -(parentsAt w).odd.den)) (c 5) :=
      fun z => by simp [placedEven, hQ, affEven]
    rw [piece_val h2 (texV2 (parentsAt w).even + (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + e₁ - e₂))
        (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + e₁ - e₂) (by abel),
      piece_val h5 (texV2 (parentsAt w).even + (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + e₁ - e₂))
        (texV2 (parentsAt w).even + e₁ - e₂ - texV2 (parentsAt w).odd) (by abel),
      piece_val h2 (texV2 (parentsAt w).even + texV2 (parentsAt w).odd + e₁) (texV2 (parentsAt w).odd + e₁) (by abel),
      piece_val h3 (texV2 (parentsAt w).even + texV2 (parentsAt w).odd + e₁) e₁ (by abel),
      piece_val h3 (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + texV2 (parentsAt w).odd +
        (texV2 (parentsAt w).even + e₁ - e₂)) (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + e₁ - e₂) (by abel),
      piece_val h5 (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + texV2 (parentsAt w).odd +
        (texV2 (parentsAt w).even + e₁ - e₂)) (texV2 (parentsAt w).even + e₁ - e₂) (by abel)]
    have hPe : oP (texV2 (parentsAt w).odd + e₁) = oP (e₁ + texV2 (parentsAt w).odd) := by rw [add_comm]
    rw [hPe]
    simp only [texV2, e₁, Prod.fst_add, Prod.snd_add] at vPD vPA sP
    simp only [zero_mul, add_zero, sub_zero, mul_zero, Prod.fst_zero, Prod.snd_zero] at vPD vPA
    simp only [zero_mul, add_zero, sub_zero, Prod.fst_zero, Prod.snd_zero, zero_add] at vQx vQxB
    simp only [dot2, texV1Odd, texV2, e₁, e₂, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at vQx vQxB sQ ⊢
    linear_combination vQx - vQxB - sQ - vPD + vPA + sP

/-! ### The optional interface `(P^{-,1}, Q^-)`, `W_1` odd -/

/-- **The triangle identity at `(P^{-,1}, Q^-)` for `W_1` odd.** If the copies meet then `d_q > d_p`, the right vertical string
of `Q` has a tile at `U + V - 1 - 2i - B + (0, 1)` (its last `d_p + 1` letters before the corner `C` removed), and
`z* = U + V + B + 1 - i` is the first top corner of `P^{-,1}` and lies on that tile of `Q^-`. -/
theorem triEven_of_two (w u1 u2 : Word) (hw : ¬ Standard.IsBase w) (hT1 : (Standard.stateAt w).tOdd = oddTile u1)
    (hT2 : (Standard.stateAt w).tEven = evenTile u2) (hph : phase w = 1)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (oP oQ : ℤ × ℤ → ℤ) (c : ℕ → ℤ)
    (hRP : SurgicalWeak.RespectsAnchored (oddTile u1) (hWordOf u1 false) (vWordOf u1 false) oP)
    (hRQ : SurgicalWeak.RespectsAnchored (evenTile u2) (hWordOf u2 true) (vWordOf u2 true) oQ)
    (hsP : SigmaZero oP (texV1Odd (parentsAt w).odd)) (hsQ : SigmaZero oQ (texV1Even (parentsAt w).even)) :
    (∃ z, z ∈ mEven w u1 u2 2 ∧ z ∈ mEven w u1 u2 5) → ∃ z, z ∈ mEven w u1 u2 2 ∧ z ∈ mEven w u1 u2 5 ∧
        placedEven w oP oQ c 2 z - placedEven w oP oQ c 5 z =
          (placedEven w oP oQ c 2 (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + texV2 (parentsAt w).odd +
              e₁) -
            placedEven w oP oQ c 3 (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + texV2 (parentsAt w).odd +
              e₁)) +
          (placedEven w oP oQ c 3 (texV2 (parentsAt w).odd + texV2 (parentsAt w).odd +
              (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + e₁ - e₂)) -
            placedEven w oP oQ c 5 (texV2 (parentsAt w).odd + texV2 (parentsAt w).odd +
              (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + e₁ - e₂))) := by
  rintro ⟨z0, hz2, hz5⟩
  have hP := evenP_of w hph
  have hQ := evenQ_of w hph
  have hd2 := mEven_sub w u1 u2 2 hz2
  have hd5 := mEven_sub w u1 u2 5 hz5
  simp only [dEven, pieceSet, hP, hQ] at hd2 hd5
  simp at hd2 hd5
  have b2 := box_shift_odd u1 _ z0 hd2
  have b5 := box_shift_even u2 _ z0 hd5
  rw [← hp] at b2
  rw [← hq] at b5
  simp only [texV2, texV1Even, Prod.fst_add, Prod.snd_add] at b2 b5
  have hov : (parentsAt w).odd.den + (parentsAt w).even.num + 1 ≤ (parentsAt w).odd.num + (parentsAt w).even.den := by
    omega
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
  obtain ⟨hInQ, hRQb, -, -, hRQv⟩ := hRQ
  obtain ⟨-, hRPb, -, hRPl, -⟩ := hRP
  obtain ⟨hhq, hlq⟩ := hWordOf_head_last u2 true
  have hXQ := TexVPositions.lastPos_hWordOf_true_tex u2
  rw [← hq] at hXQ
  obtain ⟨βQ, -, hQB⟩ := fwd_corner_tiles (hWordOf u2 true) oQ _ hhq hlq hXQ hRQb hsQ
  obtain ⟨hhp, hlp⟩ := hWordOf_head_last u1 false
  have hXP := TexVPositions.lastPos_hWordOf_false_tex u1
  rw [← hp] at hXP
  obtain ⟨βP, hPA, -⟩ := fwd_corner_tiles (hWordOf u1 false) oP _ hhp hlp hXP hRPb hsP
  have hdpq : (parentsAt w).odd.den + 1 ≤ (parentsAt w).even.den := by
    by_contra h
    rw [not_le] at h
    have h1 : 0 ≤ ((parentsAt w).odd.den - (parentsAt w).even.den) * ((parentsAt w).even.den - (parentsAt w).even.num) :=
      mul_nonneg (by omega) (by omega)
    have h2 : 0 ≤ ((parentsAt w).odd.num - ((parentsAt w).odd.den - (parentsAt w).even.den + (parentsAt w).even.num + 1)) *
        (parentsAt w).even.den := mul_nonneg (by omega) (by omega)
    nlinarith
  -- the vertical word of `Q`
  obtain ⟨hvh, hvl⟩ := StringCorners.vWord_even_head_last u2
  have hvc := StringCorners.vWord_even_counts u2
  rw [hce, ← hq] at hvc
  obtain ⟨t, ht⟩ : ∃ t, vWordOf u2 true = Letter.p :: t := by
    cases h : vWordOf u2 true with
    | nil => rw [h] at hvh; simp at hvh
    | cons a t =>
      rw [h] at hvh
      simp only [List.head?_cons, Option.some.injEq] at hvh
      exact ⟨t, by rw [hvh]⟩
  have hvlen : ((Letter.p :: t).length : ℤ) = (parentsAt w).even.den := by
    have h := length_eq_counts (vWordOf u2 true)
    rw [ht] at h hvc
    have h' : ((Letter.p :: t).length : ℤ) = ((Letter.p :: t).count Letter.p : ℤ) + ((Letter.p :: t).count Letter.q : ℤ) :=
      by exact_mod_cast h
    rw [h', hvc.1, hvc.2]
    ring
  have hqtot : qPrefix (Letter.p :: t) (Letter.p :: t).length = (parentsAt w).even.num := by
    unfold qPrefix
    rw [List.take_length]
    rw [ht] at hvc
    exact hvc.2
  have hcwv := SiteHullEven.cw_childP_swap u2
  rw [hce, ← hq] at hcwv
  have hvw : vWordOf u2 true = (quadAt [] (Standard.swapW u2)).childP.map swapLetter := rfl
  have hxl : ((quadAt [] (Standard.swapW u2)).childP.length : ℤ) = (parentsAt w).even.den := hcwv.1
  set jN : ℕ := ((parentsAt w).even.den - (parentsAt w).odd.den).toNat with hjNdef
  have hjN : (jN : ℤ) = (parentsAt w).even.den - (parentsAt w).odd.den := Int.toNat_of_nonneg (by omega)
  have hjx : jN ≤ (quadAt [] (Standard.swapW u2)).childP.length := by
    have : (jN : ℤ) ≤ ((quadAt [] (Standard.swapW u2)).childP.length : ℤ) := by rw [hjN, hxl]; omega
    exact_mod_cast this
  have hcntj : qPrefix (Letter.p :: t) jN = (parentsAt w).even.num - (parentsAt w).odd.num := by
    rw [← ht, hvw, qPrefix_swap _ _ hjx]
    obtain ⟨h1, h2⟩ := hcwv.2 jN (by rw [hjN]; omega)
    rw [hjN] at h1 h2
    obtain ⟨f1, f2⟩ := vceil_facts_of (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
      (parentsAt w).even.den (by linarith) (by omega)
    have := ceil_unique (parentsAt w).even.den
      (((parentsAt w).even.den - (parentsAt w).odd.den) * ((parentsAt w).even.den - (parentsAt w).even.num)) _
      ((parentsAt w).even.den - (parentsAt w).odd.den - (parentsAt w).even.num + (parentsAt w).odd.num)
      (by omega) h1 h2 f1 f2
    rw [hjN, this]
    ring
  -- the right vertical string of `Q` from `U - 1 - i`
  have hXQ' : lastPosOf (hStringAt (hWordOf u2 true) 0) = texV1Even (parentsAt w).even - (1, 1) := hXQ
  rw [hXQ', ht] at hRQv
  have hd0 : ((texV1Even (parentsAt w).even - (1, 1) - cstarV ((Letter.p :: t).headD Letter.p) false).1 +
      (texV1Even (parentsAt w).even - (1, 1) - cstarV ((Letter.p :: t).headD Letter.p) false).2) % 2 = 0 := by
    simp only [List.headD_cons, cstarV, texV1Even, Prod.fst_sub, Prod.snd_sub]
    omega
  obtain ⟨a0, K, hV⟩ := VerticalStepOne.vertical_formula (Letter.p :: t) _ oQ (by simp) hRQv hd0
  have ht0 : (vStringAt (Letter.p :: t) (texV1Even (parentsAt w).even - (1, 1))).getD 0 (ZTile.zero, 0) =
      (ZTile.zero, texV1Even (parentsAt w).even - (1, 1)) := by
    rw [vfwd_tile t _ 0 (by simp)]
    have : qPrefix (Letter.p :: t) 1 = 0 := by simp [qPrefix]
    rw [this]
    ext <;> simp [letterZTile]
  have hlen0 : 0 < (vStringAt (Letter.p :: t) (texV1Even (parentsAt w).even - (1, 1))).length := by
    simp [vStringAt]
  have hV0 : ∀ u ∈ tileShape ZTile.zero, oQ (texV1Even (parentsAt w).even - (1, 1) + u) +
      zoH0 (texV1Even (parentsAt w).even - (1, 1) + u) -
      (a0.1 * (texV1Even (parentsAt w).even - (1, 1) + u).1 + a0.2 * (texV1Even (parentsAt w).even - (1, 1) + u).2) =
      vV Letter.p false u + K := by
    intro u hu
    have h := hV 0 hlen0 u (by rw [ht0]; exact hu)
    rw [ht0] at h
    exact h
  obtain ⟨ha1, ha2⟩ := vright_a0 oQ _ a0 βQ K hQB hV0
  have hlenV : (vStringAt (Letter.p :: t) (texV1Even (parentsAt w).even - (1, 1))).length = (Letter.p :: t).length := by
    simp [vStringAt]
  set k0 : ℕ := (Letter.p :: t).length - 1 - (parentsAt w).odd.den.toNat with hk0def
  have hk0j : k0 + 1 = jN := by
    have h1 : (((parentsAt w).odd.den.toNat : ℕ) : ℤ) = (parentsAt w).odd.den := Int.toNat_of_nonneg (by omega)
    have : ((k0 + 1 : ℕ) : ℤ) = (jN : ℤ) := by
      rw [hjN, hk0def]
      push_cast [Nat.sub_sub]
      omega
    exact_mod_cast this
  have hk0 : k0 < (Letter.p :: t).length := by
    have : (k0 : ℤ) + 1 = (parentsAt w).even.den - (parentsAt w).odd.den := by rw [← hjN]; exact_mod_cast hk0j
    have : (k0 : ℤ) < ((Letter.p :: t).length : ℤ) := by rw [hvlen]; omega
    exact_mod_cast this
  have h11 : ∀ l : Letter, ((1 : ℤ), (1 : ℤ)) ∈ tileShape (letterZTile l) ∧ vV l false (1, 1) = 0 := by
    intro l
    cases l <;> decide
  have htk : (vStringAt (Letter.p :: t) (texV1Even (parentsAt w).even - (1, 1))).getD k0 (ZTile.zero, 0) =
      (letterZTile ((Letter.p :: t).getD k0 Letter.p),
        texV1Even (parentsAt w).even + texV2 (parentsAt w).even + e₁ - e₂ - texV2 (parentsAt w).odd - (1, 1)) := by
    rw [vfwd_tile t _ k0 hk0, hk0j, hcntj]
    congr 1
    have : (k0 : ℤ) + 1 = (parentsAt w).even.den - (parentsAt w).odd.den := by rw [← hjN]; exact_mod_cast hk0j
    simp only [texV1Even, texV2, e₁, e₂]
    ext <;> simp <;> omega
  have hlast : (vStringAt (Letter.p :: t) (texV1Even (parentsAt w).even - (1, 1))).getD ((Letter.p :: t).length - 1)
      (ZTile.zero, 0) = (letterZTile ((Letter.p :: t).getD ((Letter.p :: t).length - 1) Letter.p),
        texV1Even (parentsAt w).even + texV2 (parentsAt w).even + e₁ - e₂ - (1, 1)) := by
    rw [vfwd_tile t _ _ (by simp), Nat.sub_add_cancel (by simp), hqtot]
    congr 1
    have : (((Letter.p :: t).length - 1 : ℕ) : ℤ) = (parentsAt w).even.den - 1 := by
      have h := hvlen
      have : 1 ≤ (Letter.p :: t).length := by simp
      push_cast [this]
      omega
    rw [this]
    simp only [texV1Even, texV2, e₁, e₂]
    ext <;> (simp; try ring)
  have vQxB := hV k0 (by rw [hlenV]; exact hk0) (1, 1) (by rw [htk]; exact (h11 _).1)
  rw [htk, zTileLetter_letterZTile, (h11 _).2] at vQxB
  have vQx := hV ((Letter.p :: t).length - 1) (by rw [hlenV]; simp) (1, 1) (by rw [hlast]; exact (h11 _).1)
  rw [hlast, zTileLetter_letterZTile, (h11 _).2] at vQx
  have e1 : texV1Even (parentsAt w).even + texV2 (parentsAt w).even + e₁ - e₂ - texV2 (parentsAt w).odd - (1, 1) + (1, 1) =
      texV1Even (parentsAt w).even + texV2 (parentsAt w).even + e₁ - e₂ - texV2 (parentsAt w).odd := by abel
  have e2 : texV1Even (parentsAt w).even + texV2 (parentsAt w).even + e₁ - e₂ - (1, 1) + (1, 1) =
      texV1Even (parentsAt w).even + texV2 (parentsAt w).even + e₁ - e₂ := by abel
  rw [e1] at vQxB
  rw [e2] at vQx
  have sQ := zoH0_shift_even (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + e₁ - e₂ - texV2 (parentsAt w).odd)
    (texV2 (parentsAt w).odd) (-(parentsAt w).odd.num) (parentsAt w).odd.den
    (by simp only [texV2]; ring) (by simp only [texV2]; ring) (by simp only [texV2]; omega)
  rw [sub_add_cancel] at sQ
  -- the left vertical string of `P` from `0`
  obtain ⟨hvhp, hvlp⟩ := StringCorners.vertWord_head_last u1
  have hwv : vWordOf u1 false = vertWord u1 := rfl
  have hne : (vWordOf u1 false).reverse ≠ [] := by
    rw [hwv]
    intro h
    rw [List.reverse_eq_nil_iff] at h
    rw [h] at hvhp
    simp at hvhp
  have hhd : (vWordOf u1 false).reverse.headD Letter.p = Letter.q := by
    rw [List.headD_eq_head?_getD, List.head?_reverse, hwv, hvlp]
    rfl
  have hd0P : (((0 : GInt) - cstarV ((vWordOf u1 false).reverse.headD Letter.p) true).1 +
      ((0 : GInt) - cstarV ((vWordOf u1 false).reverse.headD Letter.p) true).2) % 2 = 0 := by
    rw [hhd]
    decide
  obtain ⟨bP, KP, hVP⟩ := VerticalStepOne.reversed_vertical_formula _ 0 oP hne hRPl hd0P
  have hg0 : (vWordOf u1 false).reverse.getD 0 Letter.p = Letter.q := by
    rw [List.getD_eq_getElem?_getD, ← List.head?_eq_getElem?, List.head?_reverse, hwv, hvlp]
    rfl
  have hlenP : (vRevStringAt (vWordOf u1 false).reverse 0).length = (vWordOf u1 false).reverse.length :=
    vRevStringAt_length _ _
  have hposP : 0 < (vWordOf u1 false).reverse.length := List.length_pos_of_ne_nil hne
  have hP0 : (vRevStringAt (vWordOf u1 false).reverse 0).getD 0 (ZTile.zero, 0) = (ZTile.one, 0) := by
    apply Prod.ext
    · rw [vRevStringAt_getD_fst _ _ 0 hposP, hg0]
      rfl
    · exact vRevStringAt_getD_snd_zero _ _ hne
  have hVP0 : ∀ u ∈ tileShape ZTile.one, oP (0 + u) + zoH0 (0 + u) - (bP.1 * (0 + u).1 + bP.2 * (0 + u).2) =
      vV Letter.q true u + KP := by
    intro u hu
    have h := hVP 0 (by rw [hlenP]; exact hposP) u (by rw [hP0]; exact hu)
    rw [hP0] at h
    exact h
  have hbP := vleft_a0 oP bP βP KP hPA hVP0
  have hgl : (vWordOf u1 false).reverse.getD ((vWordOf u1 false).reverse.length - 1) Letter.p = Letter.p := by
    rw [List.getD_eq_getElem?_getD, ← List.getLast?_eq_getElem?, List.getLast?_reverse, hwv, hvhp]
    rfl
  have hYP := StdCornerAnchors.stdAnchorY_odd u1
  rw [← hp] at hYP
  have hPl : (vRevStringAt (vWordOf u1 false).reverse 0).getD ((vWordOf u1 false).reverse.length - 1) (ZTile.zero, 0) =
      (ZTile.zero, texV2 (parentsAt w).odd + (1, -2)) := by
    apply Prod.ext
    · rw [vRevStringAt_getD_fst _ _ _ (by omega), hgl]
      rfl
    · rw [← hYP, lastPosOf_eq_getD, hlenP]
  have vPD := hVP ((vWordOf u1 false).reverse.length - 1) (by rw [hlenP]; omega) (0, 2) (by
    rw [hPl]
    exact (by decide : ((0 : ℤ), (2 : ℤ)) ∈ tileShape ZTile.zero))
  rw [hPl] at vPD
  have vPA := hVP0 e₁ (by decide)
  rw [hbP, show zTileLetter ZTile.zero = Letter.p from rfl, show vV Letter.p true ((0 : ℤ), (2 : ℤ)) = 0 by decide]
    at vPD
  rw [hbP, show vV Letter.q true e₁ = 0 from rfl] at vPA
  have eD : texV2 (parentsAt w).odd + (1, -2) + (0, 2) = e₁ + texV2 (parentsAt w).odd := by
    ext <;> (simp; try ring)
  rw [eD] at vPD
  simp only [zero_add] at vPA
  have sP := zoH0_shift_even e₁ (texV2 (parentsAt w).odd) (-(parentsAt w).odd.num) (parentsAt w).odd.den
    (by simp only [texV2]; ring) (by simp only [texV2]; ring) (by simp only [texV2]; omega)
  have h10 : zoH0 e₁ = 0 := by decide
  -- the point `z* = B + (U + V + 1 - i)`
  have hm2 : mEven w u1 u2 2 = shiftS (marksOdd u1) (texV1Even (parentsAt w).even + texV2 (parentsAt w).even) := by
    simp [mEven, pieceSet, hP]
  have hm5 : mEven w u1 u2 5 = shiftS (marksEven u2) (texV2 (parentsAt w).odd + texV2 (parentsAt w).odd) := by
    simp [mEven, pieceSet, hP, hQ]
  have hzin : texV2 (parentsAt w).odd + (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + e₁ - e₂) ∈
        shiftS (marksOdd u1) (texV1Even (parentsAt w).even + texV2 (parentsAt w).even) ∧
      texV2 (parentsAt w).odd + (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + e₁ - e₂) ∈
        shiftS (marksEven u2) (texV2 (parentsAt w).odd + texV2 (parentsAt w).odd) := by
    have hd := MixedFromCells.mixedEven_all w hw u1 u2 hT1 hT2
      (texV1Even (parentsAt w).even + texV2 (parentsAt w).even) (by simp [pOffsetsEven, hph])
      (texV2 (parentsAt w).odd + texV2 (parentsAt w).odd) (by simp [qOffsetsEven, hph])
      (texV2 (parentsAt w).odd + (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + e₁ - e₂))
    apply hd
    · refine mem_shift _ _ _ (texV2 (parentsAt w).odd + e₁ - e₂) ?_ (by abel)
      have h := (ClosedPathContacts.corner_marks_odd u1).2.2.2.2.2.1
      rw [← hp] at h
      exact Finset.mem_coe.1 (MarksIn.marksOdd_sub u1 h)
    · refine mem_shift _ _ _ (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + e₁ - e₂ -
        texV2 (parentsAt w).odd) ?_ (by abel)
      apply Finset.mem_coe.2
      apply hInQ
      unfold placedSites
      refine List.mem_flatMap.2 ⟨(vStringAt (Letter.p :: t) (texV1Even (parentsAt w).even - (1, 1))).getD k0
        (ZTile.zero, 0), ?_, ?_⟩
      · rw [hXQ', ht]
        apply List.mem_append_right
        rw [List.getD_eq_getElem _ _ (by rw [hlenV]; exact hk0)]
        exact List.getElem_mem _
      · rw [htk]
        refine List.mem_map.2 ⟨(1, 1), (h11 _).1, ?_⟩
        show ((1 : ℤ), (1 : ℤ)) + (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + e₁ - e₂ -
          texV2 (parentsAt w).odd - (1, 1)) = texV1Even (parentsAt w).even + texV2 (parentsAt w).even + e₁ - e₂ -
          texV2 (parentsAt w).odd
        abel
  refine ⟨texV2 (parentsAt w).odd + (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + e₁ - e₂), ?_, ?_, ?_⟩
  · rw [hm2]; exact hzin.1
  · rw [hm5]; exact hzin.2
  · have h2 : IsPiece (placedEven w oP oQ c 2) oP (texV1Even (parentsAt w).even + texV2 (parentsAt w).even)
        ((parentsAt w).even.num, -(parentsAt w).even.den) (c 2) := fun z => by simp [placedEven, hP, affEven]
    have h3 : IsPiece (placedEven w oP oQ c 3) oP
        (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + texV2 (parentsAt w).odd)
        (((parentsAt w).odd.num, -(parentsAt w).odd.den) + ((parentsAt w).even.num, -(parentsAt w).even.den)) (c 3) :=
      fun z => by simp [placedEven, hP, affEven]
    have h5 : IsPiece (placedEven w oP oQ c 5) oQ (texV2 (parentsAt w).odd + texV2 (parentsAt w).odd)
        (((parentsAt w).odd.num, -(parentsAt w).odd.den) + ((parentsAt w).odd.num, -(parentsAt w).odd.den)) (c 5) :=
      fun z => by simp [placedEven, hQ, affEven]
    rw [piece_val h2 (texV2 (parentsAt w).odd + (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + e₁ - e₂))
        (texV2 (parentsAt w).odd + e₁ - e₂) (by abel),
      piece_val h5 (texV2 (parentsAt w).odd + (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + e₁ - e₂))
        (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + e₁ - e₂ - texV2 (parentsAt w).odd) (by abel),
      piece_val h2 (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + texV2 (parentsAt w).odd + e₁)
        (texV2 (parentsAt w).odd + e₁) (by abel),
      piece_val h3 (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + texV2 (parentsAt w).odd + e₁) e₁ (by abel),
      piece_val h3 (texV2 (parentsAt w).odd + texV2 (parentsAt w).odd +
        (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + e₁ - e₂)) (texV2 (parentsAt w).odd + e₁ - e₂)
        (by abel),
      piece_val h5 (texV2 (parentsAt w).odd + texV2 (parentsAt w).odd +
        (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + e₁ - e₂))
        (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + e₁ - e₂) (by abel)]
    have hPe : oP (texV2 (parentsAt w).odd + e₁) = oP (e₁ + texV2 (parentsAt w).odd) := by rw [add_comm]
    rw [hPe]
    simp only [texV2, e₁, Prod.fst_add, Prod.snd_add] at vPD vPA sP
    simp only [zero_mul, add_zero, sub_zero, mul_zero, Prod.fst_zero, Prod.snd_zero] at vPD vPA
    simp only [dot2, texV1Even, texV2, e₁, e₂, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at vQx vQxB sQ ha1 ha2 ⊢
    have haB : a0.1 * ((parentsAt w).odd.num - (parentsAt w).odd.den) + a0.2 * ((parentsAt w).odd.num + (parentsAt w).odd.den) =
        (parentsAt w).even.num * (parentsAt w).odd.den - (parentsAt w).even.den * (parentsAt w).odd.num := by
      have h2 : 2 * (a0.1 * ((parentsAt w).odd.num - (parentsAt w).odd.den) +
          a0.2 * ((parentsAt w).odd.num + (parentsAt w).odd.den)) =
          2 * ((parentsAt w).even.num * (parentsAt w).odd.den - (parentsAt w).even.den * (parentsAt w).odd.num) := by
        linear_combination ((parentsAt w).odd.num - (parentsAt w).odd.den) * ha1 +
          ((parentsAt w).odd.num + (parentsAt w).odd.den) * ha2
      linarith
    linear_combination vQx - vQxB - sQ - vPD + vPA + sP + haB

/-! ### The triangle identities of the even child, and condition (C) -/

/-- **`TriEven` for normalised parents respecting their strings on their standard tiles**, in both orientations. -/
theorem triEven_all (w u1 u2 : Word) (hw : ¬ Standard.IsBase w) (hT1 : (Standard.stateAt w).tOdd = oddTile u1)
    (hT2 : (Standard.stateAt w).tEven = evenTile u2)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (oP oQ : ℤ × ℤ → ℤ) (c : ℕ → ℤ)
    (hRP : SurgicalWeak.RespectsAnchored (oddTile u1) (hWordOf u1 false) (vWordOf u1 false) oP)
    (hRQ : SurgicalWeak.RespectsAnchored (evenTile u2) (hWordOf u2 true) (vWordOf u2 true) oQ)
    (hsP : SigmaZero oP (texV1Odd (parentsAt w).odd)) (hsQ : SigmaZero oQ (texV1Even (parentsAt w).even)) :
    TriEven w u1 u2 oP oQ c := by
  simp only [TriEven]
  split_ifs with hph
  · exact ⟨triEven_of_one w u1 u2 hw hT1 hT2 hph hp hq oP oQ c hRP hRQ hsP hsQ,
      triEven_of_two w u1 u2 hw hT1 hT2 hph hp hq oP oQ c hRP hRQ hsP hsQ⟩
  · exact ⟨triEven_ef_one w u1 u2 hw hT1 hT2 hph hp hq oP oQ c hRP hRQ hsP hsQ,
      triEven_ef_two w u1 u2 hw hT1 hT2 hph hp hq oP oQ c hRP hRQ hsP hsQ⟩

/-- **Condition (C) for the even standard child** (`ChildGlue.ClosedPathEven`), in both orientations, for parents that respect
their strings on their standard tiles and are normalised on their first bottom tile (eq:std_corner_values), with (c) of the odd
parent and local compatibility of the mixed copies as the remaining inputs. -/
theorem closedPathEven_final (w u1 u2 : Word) (hw : ¬ Standard.IsBase w)
    (hT1 : (Standard.stateAt w).tOdd = oddTile u1) (hT2 : (Standard.stateAt w).tEven = evenTile u2)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (oP oQ : ℤ × ℤ → ℤ) (c : ℕ → ℤ)
    (hRP : SurgicalWeak.RespectsAnchored (oddTile u1) (hWordOf u1 false) (vWordOf u1 false) oP)
    (hRQ : SurgicalWeak.RespectsAnchored (evenTile u2) (hWordOf u2 true) (vWordOf u2 true) oQ)
    (hsP : SigmaZero oP (texV1Odd (parentsAt w).odd)) (hsQ : SigmaZero oQ (texV1Even (parentsAt w).even))
    (hdbl : ∃ k : ℤ, ∀ x, x ∈ tOddSet u1 → x + texV2 (parentsAt w).odd ∈ tOddSet u1 →
      oP (x + texV2 (parentsAt w).odd) - oP x - dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) x = k)
    (hcompat : MixedCompatEven w u1 u2 (placedEven w oP oQ c)) :
    ClosedPathEven w u1 u2 (placedEven w oP oQ c) :=
  ClosedPathDiagonal.closedPathEven_of w u1 u2 hp hq oP oQ (oddTile u1) (evenTile u2) c hRP hRQ hdbl hcompat
    (triEven_all w u1 u2 hw hT1 hT2 hp hq oP oQ c hRP hRQ hsP hsQ)

end FLatticePaper.Tiles.ClosedPathTriEven
