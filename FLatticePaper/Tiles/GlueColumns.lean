import FLatticePaper.Tiles.GlueBlockExcl
import FLatticePaper.Tiles.ReflectedCoverConverse
import FLatticePaper.Tiles.ClosedPathTriEven
import FLatticePaper.Tiles.SubOddCopy
import FLatticePaper.Tiles.SubEvenCopy

/-! # The column inputs of the glued children

A standard tile of fraction `n/d` is the window `H_{n/d}` in the coordinates `t = n x - d y` and `s = (d + n) x + (d - n) y`
(`SubOddCopy.mem_oddTile_iff`, `SubEvenCopy.mem_evenTile_iff`). Its boundary strings lie in bands of this window: the bottom
string has `t ≥ -2n - 2d + 1` and the left string `s ≤ 4d + n - 2`, from the ceiling words of the forward and the reversed
vertical words (`bot_band`, `left_band`); the top and the right strings are their half-turns (`ReflectedCoverConverse`), so
they lie in the opposite bands (`top_band_odd`, `right_band_odd`, ...). In the column cases the earlier copy of the register is
the window translated by `δ`, and `t(δ)` or `s(δ)` puts it beyond the band of the block (`room_*`, from the Farey relations of
the parents after the last digit), which proves the column inputs `ColumnExclOdd`, `ColumnExclEven`; the one word `w = 1` is
a finite check. -/

namespace FLatticePaper.Tiles.GlueColumns

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.SiteInduction
open FLatticePaper.Tiles.CeilWords
open FLatticePaper.Tiles.SiteStrings (hWordOf vWordOf halfTurnCentre)
open FLatticePaper.Tiles.StandardClause (fracOdd fracEven)
open FLatticePaper.Tiles.Standard (oddTile evenTile)

/-! ### Bands of the strings -/

theorem mem_getD (s : List (ZTile × GInt)) (t : ZTile × GInt) (ht : t ∈ s) :
    ∃ k < s.length, s.getD k (ZTile.zero, 0) = t := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 ht
  exact ⟨k, hk, List.getD_eq_getElem _ _ hk⟩

theorem tile_t_lo (N D : ℤ) (hN : 0 ≤ N) (hND : N ≤ D) (ty : ZTile) (y : GInt) (hy : y ∈ tileShape ty) :
    -2 * D ≤ N * y.1 - D * y.2 := by
  cases ty <;> simp only [tileShape, List.mem_cons, List.not_mem_nil, or_false] at hy <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num <;> linarith

theorem tile_s_hi (N D : ℤ) (hN : 0 ≤ N) (hND : N ≤ D) (l : Letter) (y : GInt) (hy : y ∈ tileShape (letterZTile l)) :
    (D + N) * y.1 + (D - N) * y.2 ≤ 3 * D - N := by
  cases l <;> simp only [letterZTile, tileShape, List.mem_cons, List.not_mem_nil, or_false] at hy <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num <;> linarith

theorem len_hString (x : BinaryWord) (hx : x ≠ []) (c : GInt) : (hStringAt x c).length = x.length := by
  obtain ⟨a, x', rfl⟩ := List.exists_cons_of_ne_nil hx
  simp [hStringAt, tileSeq, StringJoin.tileSeqAux_length]

theorem len_vRevString (x : BinaryWord) (hx : x ≠ []) (c : GInt) : (vRevStringAt x c).length = x.length := by
  obtain ⟨a, x', rfl⟩ := List.exists_cons_of_ne_nil hx
  simp [vRevStringAt]

/-- **The band of a bottom string**: for a forward word of slope `2n/(d+n)` its sites have `t ≥ -2n - 2d + 1`. -/
theorem bot_band (ℓ' : BinaryWord) (N D : ℤ) (hN : 0 ≤ N) (hND : N ≤ D)
    (hc : ∀ j : ℕ, (j : ℤ) ≤ (Letter.q :: ℓ').length →
      (D + N) * qPrefix (Letter.q :: ℓ') j - (D + N) < (j : ℤ) * (2 * N)) :
    ∀ z ∈ placedSites (hStringAt (Letter.q :: ℓ') 0), -2 * N - 2 * D + 1 ≤ N * z.1 - D * z.2 := by
  intro z hz
  unfold placedSites at hz
  obtain ⟨t, ht, hz⟩ := List.mem_flatMap.1 hz
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
  obtain ⟨k, hk, hkt⟩ := mem_getD _ t ht
  rw [len_hString _ (List.cons_ne_nil _ _)] at hk
  rw [ClosedPathTriangle.fwd_tile ℓ' k hk] at hkt
  subst hkt
  have hcj := hc (k + 1) (by push_cast; omega)
  have hty := tile_t_lo N D hN hND _ y hy
  simp only [Prod.fst_add, Prod.snd_add]
  push_cast at hcj
  nlinarith [hcj, hty]

/-- **The band of a left string**: for a reversed vertical word of slope `n/d` its sites have `s ≤ 4d + n - 2`. -/
theorem left_band (ℓ' : BinaryWord) (N D : ℤ) (hN : 0 ≤ N) (hND : N ≤ D)
    (hc : ∀ j : ℕ, (j : ℤ) ≤ (Letter.q :: ℓ').length →
      D * qPrefix (Letter.q :: ℓ') j - D < (j : ℤ) * N) :
    ∀ z ∈ placedSites (vRevStringAt (Letter.q :: ℓ') 0), (D + N) * z.1 + (D - N) * z.2 ≤ 4 * D + N - 2 := by
  intro z hz
  unfold placedSites at hz
  obtain ⟨t, ht, hz⟩ := List.mem_flatMap.1 hz
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
  obtain ⟨k, hk, hkt⟩ := mem_getD _ t ht
  rw [len_vRevString _ (List.cons_ne_nil _ _)] at hk
  rw [ClosedPathTriEven.vrev_tile _ 0 k hk] at hkt
  subst hkt
  have hk' : ((List.take k (Letter.q :: ℓ')).length : ℤ) = k := by
    rw [List.length_take]; simp at hk ⊢; omega
  have hcount : (((List.take k (Letter.q :: ℓ')).count Letter.q : ℕ) : ℤ) = qPrefix (Letter.q :: ℓ') k := rfl
  have hsum := ClosedPathTriEven.vOffset_sum (List.take k (Letter.q :: ℓ'))
  rw [hk', hcount] at hsum
  have hsucc := ClosedPathTriangle.count_take_succ (Letter.q :: ℓ') k hk
  have hc0 := hc k (by omega)
  have hc1 := hc (k + 1) (by push_cast; omega)
  push_cast at hc1
  have hle : N * qPrefix (Letter.q :: ℓ') k ≤ N * qPrefix (Letter.q :: ℓ') (k + 1) := by
    apply mul_le_mul_of_nonneg_left _ hN
    rw [hsucc]
    split_ifs <;> omega
  have h0 : (Letter.q :: ℓ').getD 0 Letter.p = Letter.q := rfl
  simp only [hsum, h0] at hy ⊢
  rcases hl : (Letter.q :: ℓ').getD k Letter.p with _ | _
  · rw [hl] at hy hsucc
    have hty := tile_s_hi N D hN hND _ y hy
    simp only [ClosedPathCorners.revShift, if_neg (by decide : Letter.p ≠ Letter.q), add_zero] at hsucc ⊢
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero]
    rw [hsucc] at hc1 hle
    nlinarith [hc0, hc1, hty, hle]
  · rw [hl] at hy hsucc
    have hty := tile_s_hi N D hN hND _ y hy
    simp only [ClosedPathCorners.revShift, ↓reduceIte] at hsucc ⊢
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero]
    rw [hsucc] at hc1 hle
    nlinarith [hc0, hc1, hty, hle]

/-! ### The bands of the registers -/

theorem cu_odd (u : Word) : curO u = fracOdd u := rfl
theorem cu_even (u : Word) : curE u = fracEven u := rfl

theorem pos_odd (u : Word) : 0 < (fracOdd u).num ∧ (fracOdd u).num < (fracOdd u).den := SiteHullOdd.curO_pos_lt u
theorem pos_even (u : Word) : 0 < (fracEven u).num ∧ (fracEven u).num < (fracEven u).den := SiteHullEven.curE_pos_lt u
theorem par_odd (u : Word) : ((fracOdd u).num + (fracOdd u).den) % 2 = 1 := SiteHullOdd.curO_odd u
theorem par_even (u : Word) : ((fracEven u).num + (fracEven u).den) % 2 = 0 := SiteHullEven.curE_num_add_den_even u

theorem bot_band_odd (u : Word) : ∀ z ∈ placedSites (hStringAt (hWordOf u false) 0),
    -2 * (fracOdd u).num - 2 * (fracOdd u).den + 1 ≤ (fracOdd u).num * z.1 - (fracOdd u).den * z.2 := by
  have hpl := pos_odd u
  have hC : CeilWord (hWordOf u false) (2 * (fracOdd u).num) ((fracOdd u).den + (fracOdd u).num) :=
    SiteHullOdd.cw_childP u
  obtain ⟨ℓ', hℓ⟩ := SiteHullOdd.head_q_of_ceil _ _ _ hC (by omega) (by omega)
  rw [hℓ] at hC ⊢
  exact bot_band ℓ' _ _ (by omega) (by omega) (fun j hj => (hC.2 j (by rw [← hC.1]; exact hj)).1)

theorem bot_band_even (u : Word) : ∀ z ∈ placedSites (hStringAt (hWordOf u true) 0),
    -2 * (fracEven u).num - 2 * (fracEven u).den + 1 ≤ (fracEven u).num * z.1 - (fracEven u).den * z.2 := by
  have hpl := pos_even u
  have hpar := par_even u
  have hC : CeilWord (hWordOf u true) (fracEven u).num (((fracEven u).den + (fracEven u).num) / 2) :=
    SiteHullEven.cw_childQ_even u
  obtain ⟨M, hM⟩ : ∃ M, ((fracEven u).den + (fracEven u).num) / 2 = M := ⟨_, rfl⟩
  have hM2 : (fracEven u).den + (fracEven u).num = 2 * M := by omega
  rw [hM] at hC
  obtain ⟨ℓ', hℓ⟩ := SiteHullOdd.head_q_of_ceil _ _ _ hC (by omega) (by omega)
  rw [hℓ] at hC ⊢
  refine bot_band ℓ' _ _ (by omega) (by omega) (fun j hj => ?_)
  have h := (hC.2 j (by rw [← hC.1]; exact hj)).1
  rw [hM2]
  linarith

theorem left_band_odd (u : Word) : ∀ z ∈ placedSites (vRevStringAt (vWordOf u false).reverse 0),
    ((fracOdd u).den + (fracOdd u).num) * z.1 + ((fracOdd u).den - (fracOdd u).num) * z.2 ≤
      4 * (fracOdd u).den + (fracOdd u).num - 2 := by
  have hpl := pos_odd u
  have hC : CeilWord (vWordOf u false).reverse (fracOdd u).num (fracOdd u).den := SiteHullOdd.cw_vert u
  obtain ⟨ℓ', hℓ⟩ := SiteHullOdd.head_q_of_ceil _ _ _ hC (by omega) (by omega)
  rw [hℓ] at hC ⊢
  exact left_band ℓ' _ _ (by omega) (by omega) (fun j hj => (hC.2 j (by rw [← hC.1]; exact hj)).1)

theorem left_band_even (u : Word) : ∀ z ∈ placedSites (vRevStringAt (vWordOf u true).reverse 0),
    ((fracEven u).den + (fracEven u).num) * z.1 + ((fracEven u).den - (fracEven u).num) * z.2 ≤
      4 * (fracEven u).den + (fracEven u).num - 2 := by
  have hpl := pos_even u
  have hC : CeilWord (vWordOf u true).reverse (fracEven u).num (fracEven u).den := SiteHullEven.cw_vert_even u
  obtain ⟨ℓ', hℓ⟩ := SiteHullOdd.head_q_of_ceil _ _ _ hC (by omega) (by omega)
  rw [hℓ] at hC ⊢
  exact left_band ℓ' _ _ (by omega) (by omega) (fun j hj => (hC.2 j (by rw [← hC.1]; exact hj)).1)

/-- **The band of the top string of the odd register**, the half-turn of its bottom string. -/
theorem top_band_odd (u : Word) :
    ∀ y ∈ placedSites (hRevStringAt (hWordOf u false).reverse (texV2 (fracOdd u) + (1, -2))),
      (fracOdd u).num * y.1 - (fracOdd u).den * y.2 ≤
        (fracOdd u).num * ((fracOdd u).den + (fracOdd u).num + 1) -
          (fracOdd u).den * (3 * (fracOdd u).num + (fracOdd u).den - 1) + 2 * (fracOdd u).num + 2 * (fracOdd u).den - 1 := by
  intro y hy
  have e : texV2 (fracOdd u) + (1, -2) = lastPosOf (vRevStringAt (vWordOf u false).reverse ((0 : ℤ), (0 : ℤ))) := by
    rw [show ((0 : ℤ), (0 : ℤ)) = (0 : GInt) from rfl, GlueStringDecomp.lp_left_odd, zero_add]
  rw [e] at hy
  have h := (ReflectedCoverConverse.hRev_halfTurn_odd u y).1 hy
  rw [SiteHullOdd.centre_odd, cu_odd] at h
  have hb := bot_band_odd u _ h
  simp only [Prod.fst_sub, Prod.snd_sub] at hb
  linarith

theorem top_band_even (u : Word) :
    ∀ y ∈ placedSites (hRevStringAt (hWordOf u true).reverse (texV2 (fracEven u) + (1, -2))),
      (fracEven u).num * y.1 - (fracEven u).den * y.2 ≤
        (fracEven u).num * ((fracEven u).num + 1) -
          (fracEven u).den * (2 * (fracEven u).num + (fracEven u).den - 1) + 2 * (fracEven u).num + 2 * (fracEven u).den - 1 := by
  intro y hy
  have e : texV2 (fracEven u) + (1, -2) = lastPosOf (vRevStringAt (vWordOf u true).reverse ((0 : ℤ), (0 : ℤ))) := by
    rw [show ((0 : ℤ), (0 : ℤ)) = (0 : GInt) from rfl, GlueStringDecomp.lp_left_even, zero_add]
  rw [e] at hy
  have h := (ReflectedCoverConverse.hRev_halfTurn_even u y).1 hy
  rw [SiteHullEven.centre_even, cu_even] at h
  have hb := bot_band_even u _ h
  simp only [Prod.fst_sub, Prod.snd_sub] at hb
  linarith

/-- **The band of the right string of the odd register**, the half-turn of its left string. -/
theorem right_band_odd (u : Word) :
    ∀ y ∈ placedSites (vStringAt (vWordOf u false) (texV1Odd (fracOdd u) - (1, 1))),
      ((fracOdd u).den + (fracOdd u).num) * ((fracOdd u).den + (fracOdd u).num + 1) +
          ((fracOdd u).den - (fracOdd u).num) * (3 * (fracOdd u).num + (fracOdd u).den - 1) -
          (4 * (fracOdd u).den + (fracOdd u).num - 2) ≤
        ((fracOdd u).den + (fracOdd u).num) * y.1 + ((fracOdd u).den - (fracOdd u).num) * y.2 := by
  intro y hy
  have e : texV1Odd (fracOdd u) - (1, 1) = lastPosOf (hStringAt (hWordOf u false) ((0 : ℤ), (0 : ℤ))) := by
    rw [show ((0 : ℤ), (0 : ℤ)) = (0 : GInt) from rfl, GlueStringDecomp.lp_bot_odd, zero_add]
  rw [e] at hy
  have h := (ReflectedCoverConverse.vFwd_halfTurn_odd u y).1 hy
  rw [SiteHullOdd.centre_odd, cu_odd] at h
  have hb := left_band_odd u _ h
  simp only [Prod.fst_sub, Prod.snd_sub] at hb
  linarith

theorem right_band_even (u : Word) :
    ∀ y ∈ placedSites (vStringAt (vWordOf u true) (texV1Even (fracEven u) - (1, 1))),
      ((fracEven u).den + (fracEven u).num) * ((fracEven u).num + 1) +
          ((fracEven u).den - (fracEven u).num) * (2 * (fracEven u).num + (fracEven u).den - 1) -
          (4 * (fracEven u).den + (fracEven u).num - 2) ≤
        ((fracEven u).den + (fracEven u).num) * y.1 + ((fracEven u).den - (fracEven u).num) * y.2 := by
  intro y hy
  have e : texV1Even (fracEven u) - (1, 1) = lastPosOf (hStringAt (hWordOf u true) ((0 : ℤ), (0 : ℤ))) := by
    rw [show ((0 : ℤ), (0 : ℤ)) = (0 : GInt) from rfl, GlueStringDecomp.lp_bot_even, zero_add]
  rw [e] at hy
  have h := (ReflectedCoverConverse.vFwd_halfTurn_even u y).1 hy
  rw [SiteHullEven.centre_even, cu_even] at h
  have hb := left_band_even u _ h
  simp only [Prod.fst_sub, Prod.snd_sub] at hb
  linarith

/-! ### Shifted blocks and the window of a copy -/

theorem shift_hRev (w : BinaryWord) (o c e x : GInt) (he : e = o + c) (hx : x ∈ placedSites (hRevStringAt w e)) :
    x - o ∈ placedSites (hRevStringAt w c) := by
  rw [he, add_comm, ← GlueChain.hRevStringAt_shift, GlueRespectsAll.ps_map_shift] at hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  simpa using hy

theorem shift_vRev (w : BinaryWord) (o c e x : GInt) (he : e = o + c) (hx : x ∈ placedSites (vRevStringAt w e)) :
    x - o ∈ placedSites (vRevStringAt w c) := by
  rw [he, add_comm, ← GlueChain.vRevStringAt_shift, GlueRespectsAll.ps_map_shift] at hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  simpa using hy

theorem shift_vFwd (w : BinaryWord) (o c e x : GInt) (he : e = o + c) (hx : x ∈ placedSites (vStringAt w e)) :
    x - o ∈ placedSites (vStringAt w c) := by
  rw [he, add_comm, ← GlueChain.vStringAt_shift, GlueRespectsAll.ps_map_shift] at hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  simpa using hy

theorem aOf_ge (f : Fraction) (h : 0 < f.num ∧ f.num < f.den) (ev : Bool) : 1 ≤ aOf f ev := by
  unfold aOf
  split_ifs <;> omega

theorem lOf_ge (f : Fraction) (h : 0 < f.num ∧ f.num < f.den) (ev : Bool) : 2 - f.den ≤ lOf f ev := by
  unfold lOf
  split_ifs <;> omega

/-- The window of a copy of the odd register. -/
theorem window_odd (u : Word) (v x : GInt) (hx : x ∈ SiteInduction.shiftS (ChildGlue.tOddSet u) v) :
    let z := x - v
    1 - tOf (fracOdd u) ≤ tCo (fracOdd u) z ∧ tCo (fracOdd u) z ≤ (fracOdd u).den + (fracOdd u).num - 1 ∧
      2 - (fracOdd u).den ≤ sCo (fracOdd u) z ∧
      sCo (fracOdd u) z ≤ 2 * tOf (fracOdd u) + 2 * (fracOdd u).num + (fracOdd u).den - 2 := by
  intro z
  have hin : z ∈ oddTile u := Finset.mem_coe.1 (ClosedPathAssembly.sub_mem_of_shift _ _ _ hx)
  have hH := (SubOddCopy.mem_oddTile_iff u z).1 hin
  rw [cu_odd] at hH
  have hpl := pos_odd u
  have ha := aOf_ge (fracOdd u) hpl (decide ((z.1 + z.2) % 2 = 0))
  have hl := lOf_ge (fracOdd u) hpl (decide ((z.1 + z.2) % 2 = 0))
  have hμ : SiteInduction.muOf (fracOdd u) = 2 := by
    unfold SiteInduction.muOf
    rw [if_pos (par_odd u)]
  obtain ⟨h1, h2, h3, h4⟩ := hH
  rw [hμ] at h4
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The window of a copy of the even register. -/
theorem window_even (u : Word) (v x : GInt) (hx : x ∈ SiteInduction.shiftS (ChildGlue.tEvenSet u) v) :
    let z := x - v
    1 - tOf (fracEven u) ≤ tCo (fracEven u) z ∧ tCo (fracEven u) z ≤ (fracEven u).den + (fracEven u).num - 1 ∧
      2 - (fracEven u).den ≤ sCo (fracEven u) z ∧
      sCo (fracEven u) z ≤ tOf (fracEven u) + 2 * (fracEven u).num + (fracEven u).den - 2 := by
  intro z
  have hin : z ∈ evenTile u := Finset.mem_coe.1 (ClosedPathAssembly.sub_mem_of_shift _ _ _ hx)
  have hH := (SubEvenCopy.mem_evenTile_iff u z).1 hin
  rw [cu_even] at hH
  have hpl := pos_even u
  have ha := aOf_ge (fracEven u) hpl (decide ((z.1 + z.2) % 2 = 0))
  have hl := lOf_ge (fracEven u) hpl (decide ((z.1 + z.2) % 2 = 0))
  have hμ : SiteInduction.muOf (fracEven u) = 1 := by
    unfold SiteInduction.muOf
    rw [if_neg (by have := par_even u; omega)]
  obtain ⟨h1, h2, h3, h4⟩ := hH
  rw [hμ] at h4
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-! ### The rooms: the earlier copy beyond the band of the block -/

-- The odd child after a `2`: `p = p' + q` with `p' = (a, b)`; `δ` is `V - 2U` (`W_1` even) or `2U + V` (`W_1` odd).
theorem room_odd_ef_top (np dp nq dq a b : ℤ) (h1 : 0 < np) (h2 : np < dp) (h3 : 0 < nq) (h4 : nq + 2 ≤ dq)
    (hdet : np * dq - nq * dp = -1) (_ha : np = a + nq) (_hb : dp = b + dq) (_h5 : 1 ≤ b - a) (_h6 : 0 ≤ a) :
    np * (nq - 3 * dq) - dp * (dq - nq) ≤ -3 * (np + dp) := by nlinarith

theorem room_odd_ef_left (np dp nq dq a b : ℤ) (h1 : 0 < np) (h2 : np < dp) (h3 : 0 < nq) (h4 : nq + 2 ≤ dq)
    (hdet : np * dq - nq * dp = -1) (_ha : np = a + nq) (_hb : dp = b + dq) (_h5 : 1 ≤ b - a) (_h6 : 0 ≤ a) :
    (dp + np) * (nq - 3 * dq) + (dp - np) * (dq - nq) ≤ 2 - 5 * dp - np := by nlinarith

theorem room_odd_of_top (np dp nq dq a b : ℤ) (h1 : 0 < np) (h2 : np < dp) (h3 : 0 < nq) (h4 : nq + 2 ≤ dq)
    (hdet : np * dq - nq * dp = 1) (ha : np = a + nq) (hb : dp = b + dq) (h5 : 1 ≤ b - a) (_h6 : 0 ≤ a) :
    np * (dq + nq) - dp * (3 * nq + dq) ≤ -3 * (np + dp) := by nlinarith

theorem room_odd_of_right (np dp nq dq a b : ℤ) (h1 : 0 < np) (h2 : np < dp) (h3 : 0 < nq) (h4 : nq + 2 ≤ dq)
    (hdet : np * dq - nq * dp = 1) (ha : np = a + nq) (hb : dp = b + dq) (h5 : 1 ≤ b - a) (_h6 : 0 ≤ a) :
    5 * dp + np - 2 ≤ (dp + np) * (dq + nq) + (dp - np) * (3 * nq + dq) := by nlinarith

-- The even child after a `3`: `q = 2p + q'` with `q' = (c, e)`; `δ` is `A + 2B` (`W_1` even) or `2B - A` (`W_1` odd).
theorem room_even_ef_top (np dp nq dq c e : ℤ) (h1 : 0 < np) (h2 : np < dp) (h3 : 0 < nq) (h4 : nq + 2 ≤ dq)
    (_hdet : np * dq - nq * dp = -1) (_hc : nq = 2 * np + c) (_he : dq = 2 * dp + e) (_h5 : 1 ≤ c) (_h6 : 0 ≤ e - c) :
    nq * (2 * np) - dq * (4 * np + 2 * dp) ≤ -3 * (nq + dq) := by nlinarith

theorem room_even_ef_right (np dp nq dq c e : ℤ) (h1 : 0 < np) (h2 : np < dp) (h3 : 0 < nq) (h4 : nq + 2 ≤ dq)
    (hdet : np * dq - nq * dp = -1) (_hc : nq = 2 * np + c) (_he : dq = 2 * dp + e) (_h5 : 1 ≤ c) (_h6 : 0 ≤ e - c) :
    5 * dq + nq - 2 ≤ (dq + nq) * (2 * np) + (dq - nq) * (4 * np + 2 * dp) := by nlinarith

theorem room_even_of_top (np dp nq dq c e : ℤ) (h1 : 0 < np) (h2 : np < dp) (h3 : 0 < nq) (h4 : nq + 2 ≤ dq)
    (hdet : np * dq - nq * dp = 1) (hc : nq = 2 * np + c) (_he : dq = 2 * dp + e) (h5 : 1 ≤ c) (_h6 : 0 ≤ e - c) :
    nq * (2 * np - 4 * dp) - dq * (2 * dp) ≤ -3 * (nq + dq) := by nlinarith

theorem room_even_of_left (np dp nq dq c e : ℤ) (h1 : 0 < np) (h2 : np < dp) (h3 : 0 < nq) (h4 : nq + 2 ≤ dq)
    (hdet : np * dq - nq * dp = 1) (hc : nq = 2 * np + c) (_he : dq = 2 * dp + e) (h5 : 1 ≤ c) (_h6 : 0 ≤ e - c) :
    (dq + nq) * (2 * np - 4 * dp) + (dq - nq) * (2 * dp) ≤ 2 - 5 * dq - nq := by nlinarith

/-! ### The column cases -/

theorem det_of (w u1 u2 : Word) (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2) :
    (fracOdd u1).num * (fracEven u2).den - (fracEven u2).num * (fracOdd u1).den = 2 * (phase w : ℤ) - 1 := by
  have h := SiteScope.det_parentsAt w
  rw [hp, hq] at h
  exact h

/-- **The column case of the odd child, `W_1` even**: after a `2` the blocks of `P^-` avoid `P^+`. -/
theorem col_odd_ef (w u1 u2 : Word) (hw : w ≠ []) (hph : phase w ≠ 1) (hp : (parentsAt w).odd = fracOdd u1)
    (hq : (parentsAt w).even = fracEven u2) (hl : w.getLast? = some Digit.two) :
    ∀ x ∈ GlueRespectsAll.blockSitesOdd w u1 u2 1,
      x ∈ ChildGlue.pieceSet (ChildGlue.oddP w) (ChildGlue.oddQ w) (ChildGlue.tOddSet u1) (ChildGlue.tEvenSet u2) 0 →
        False := by
  intro x hx hxj
  have hP := ClosedPathAssembly.oddP_ef w hph
  have hQ := ClosedPathAssembly.oddQ_ef w hph
  have pc : ChildGlue.pieceSet (ChildGlue.oddP w) (ChildGlue.oddQ w) (ChildGlue.tOddSet u1) (ChildGlue.tEvenSet u2) 0 =
      SiteInduction.shiftS (ChildGlue.tOddSet u1) (texV1Even (fracEven u2) + texV1Even (fracEven u2)) := by
    simp [ChildGlue.pieceSet, hP, hq]
  rw [pc] at hxj
  have hW := window_odd u1 _ x hxj
  have hpl := pos_odd u1
  have hql := pos_even u2
  have hqe := par_even u2
  have hdet := det_of w u1 u2 hp hq
  rw [ClosedPathTriOdd.phase_zero_of w hph] at hdet
  norm_num at hdet
  obtain ⟨p', q', f1, f2, f3, f4, -, -, -, -, h2, -⟩ := GlueBlockBounds.last_facts w hw
  rw [hp, hq] at h2
  obtain ⟨e1, e2, e3, e4⟩ := h2 hl
  simp only [GlueRespectsAll.blockSitesOdd, if_neg hph, List.mem_append] at hx
  simp only [tCo, sCo, tOf, texV1Even, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] at hW
  rcases hx with hx | hx
  · have hb := top_band_odd u1 _ (shift_hRev _ (texV2 (fracEven u2)) _ _ x rfl hx)
    have room := room_odd_ef_top _ _ _ _ p'.num p'.den hpl.1 hpl.2 hql.1 (by omega) hdet (by omega) (by omega) f1 f2
    simp only [texV2, Prod.fst_sub, Prod.snd_sub] at hb
    nlinarith [hW.1, hb, room]
  · have hb := left_band_odd u1 _ (shift_vRev _ (texV2 (fracEven u2)) 0 _ x (add_zero _).symm hx)
    have room := room_odd_ef_left _ _ _ _ p'.num p'.den hpl.1 hpl.2 hql.1 (by omega) hdet (by omega) (by omega) f1 f2
    simp only [texV2, Prod.fst_sub, Prod.snd_sub] at hb
    nlinarith [hW.2.2.1, hb, room]

/-- **The column case of the odd child, `W_1` odd.** -/
theorem col_odd_of (w u1 u2 : Word) (hw : w ≠ []) (hph : phase w = 1) (hp : (parentsAt w).odd = fracOdd u1)
    (hq : (parentsAt w).even = fracEven u2) (hl : w.getLast? = some Digit.two) :
    ∀ x ∈ GlueRespectsAll.blockSitesOdd w u1 u2 1,
      x ∈ ChildGlue.pieceSet (ChildGlue.oddP w) (ChildGlue.oddQ w) (ChildGlue.tOddSet u1) (ChildGlue.tEvenSet u2) 0 →
        False := by
  intro x hx hxj
  have hP := ClosedPathAssembly.oddP_of w hph
  have hQ := ClosedPathAssembly.oddQ_of w hph
  have pc : ChildGlue.pieceSet (ChildGlue.oddP w) (ChildGlue.oddQ w) (ChildGlue.tOddSet u1) (ChildGlue.tEvenSet u2) 0 =
      SiteInduction.shiftS (ChildGlue.tOddSet u1) 0 := by
    simp [ChildGlue.pieceSet, hP, hq]
  rw [pc] at hxj
  have hW := window_odd u1 _ x hxj
  have hpl := pos_odd u1
  have hql := pos_even u2
  have hqe := par_even u2
  have hdet := det_of w u1 u2 hp hq
  rw [hph] at hdet
  norm_num at hdet
  obtain ⟨p', q', f1, f2, f3, f4, -, -, -, -, h2, -⟩ := GlueBlockBounds.last_facts w hw
  rw [hp, hq] at h2
  obtain ⟨e1, e2, e3, e4⟩ := h2 hl
  simp only [GlueRespectsAll.blockSitesOdd, if_pos hph, List.mem_append] at hx
  simp only [tCo, sCo, tOf, sub_zero] at hW
  rcases hx with hx | hx
  · have hb := top_band_odd u1 _
      (shift_hRev _ (texV1Even (fracEven u2) + texV1Even (fracEven u2) + texV2 (fracEven u2)) _ _ x rfl hx)
    have room := room_odd_of_top _ _ _ _ p'.num p'.den hpl.1 hpl.2 hql.1 (by omega) hdet (by omega) (by omega) f1 f2
    simp only [texV1Even, texV2, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] at hb
    nlinarith [hW.1, hb, room]
  · have hb := right_band_odd u1 _
      (shift_vFwd _ (texV1Even (fracEven u2) + texV1Even (fracEven u2) + texV2 (fracEven u2)) _ _ x rfl hx)
    have room := room_odd_of_right _ _ _ _ p'.num p'.den hpl.1 hpl.2 hql.1 (by omega) hdet (by omega) (by omega) f1 f2
    simp only [texV1Even, texV2, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] at hb
    nlinarith [hW.2.2.2, hb, room]

/-- **The column case of the even child, `W_1` even**: after a `3` the blocks of `Q^-` avoid `Q^+`. -/
theorem col_even_ef (w u1 u2 : Word) (hw : w ≠ []) (hph : phase w ≠ 1) (hp : (parentsAt w).odd = fracOdd u1)
    (hq : (parentsAt w).even = fracEven u2) (hl : w.getLast? = some Digit.three) :
    ∀ x ∈ GlueRespectsAll.blockSitesEven w u1 u2 5,
      x ∈ ChildGlue.pieceSet (ChildGlue.evenP w) (ChildGlue.evenQ w) (ChildGlue.tOddSet u1) (ChildGlue.tEvenSet u2) 4 →
        False := by
  intro x hx hxj
  have hP := ClosedPathAssembly.evenP_ef w hph
  have hQ := ClosedPathAssembly.evenQ_ef w hph
  have pc : ChildGlue.pieceSet (ChildGlue.evenP w) (ChildGlue.evenQ w) (ChildGlue.tOddSet u1) (ChildGlue.tEvenSet u2) 4 =
      SiteInduction.shiftS (ChildGlue.tEvenSet u2) 0 := by
    simp [ChildGlue.pieceSet, hP, hQ, hp, hq]
  rw [pc] at hxj
  have hW := window_even u2 _ x hxj
  have hpl := pos_odd u1
  have hql := pos_even u2
  have hqe := par_even u2
  have hdet := det_of w u1 u2 hp hq
  rw [ClosedPathTriOdd.phase_zero_of w hph] at hdet
  norm_num at hdet
  obtain ⟨p', q', f1, f2, f3, f4, -, -, -, -, -, h3⟩ := GlueBlockBounds.last_facts w hw
  rw [hp, hq] at h3
  obtain ⟨e1, e2, e3, e4⟩ := h3 hl
  simp only [GlueRespectsAll.blockSitesEven, if_neg hph, List.mem_append] at hx
  simp only [tCo, sCo, tOf, sub_zero] at hW
  rcases hx with hx | hx
  · have hb := top_band_even u2 _
      (shift_hRev _ (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV2 (fracOdd u1)) _ _ x rfl hx)
    have room := room_even_ef_top _ _ _ _ q'.num q'.den hpl.1 hpl.2 hql.1 (by omega) hdet (by omega) (by omega) f3 f4
    simp only [texV1Odd, texV2, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] at hb
    nlinarith [hW.1, hb, room]
  · have hb := right_band_even u2 _
      (shift_vFwd _ (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV2 (fracOdd u1)) _ _ x rfl hx)
    have room := room_even_ef_right _ _ _ _ q'.num q'.den hpl.1 hpl.2 hql.1 (by omega) hdet (by omega) (by omega) f3 f4
    simp only [texV1Odd, texV2, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] at hb
    nlinarith [hW.2.2.2, hb, room]

/-- **The column case of the even child, `W_1` odd.** -/
theorem col_even_of (w u1 u2 : Word) (hw : w ≠ []) (hph : phase w = 1) (hp : (parentsAt w).odd = fracOdd u1)
    (hq : (parentsAt w).even = fracEven u2) (hl : w.getLast? = some Digit.three) :
    ∀ x ∈ GlueRespectsAll.blockSitesEven w u1 u2 5,
      x ∈ ChildGlue.pieceSet (ChildGlue.evenP w) (ChildGlue.evenQ w) (ChildGlue.tOddSet u1) (ChildGlue.tEvenSet u2) 4 →
        False := by
  intro x hx hxj
  have hP := ClosedPathAssembly.evenP_of w hph
  have hQ := ClosedPathAssembly.evenQ_of w hph
  have pc : ChildGlue.pieceSet (ChildGlue.evenP w) (ChildGlue.evenQ w) (ChildGlue.tOddSet u1) (ChildGlue.tEvenSet u2) 4 =
      SiteInduction.shiftS (ChildGlue.tEvenSet u2) (texV1Odd (fracOdd u1)) := by
    simp [ChildGlue.pieceSet, hP, hQ, hp, hq]
  rw [pc] at hxj
  have hW := window_even u2 _ x hxj
  have hpl := pos_odd u1
  have hql := pos_even u2
  have hqe := par_even u2
  have hdet := det_of w u1 u2 hp hq
  rw [hph] at hdet
  norm_num at hdet
  obtain ⟨p', q', f1, f2, f3, f4, -, -, -, -, -, h3⟩ := GlueBlockBounds.last_facts w hw
  rw [hp, hq] at h3
  obtain ⟨e1, e2, e3, e4⟩ := h3 hl
  simp only [GlueRespectsAll.blockSitesEven, if_pos hph, List.mem_append] at hx
  simp only [tCo, sCo, tOf, texV1Odd, Prod.fst_sub, Prod.snd_sub] at hW
  rcases hx with hx | hx
  · have hb := top_band_even u2 _ (shift_hRev _ (texV2 (fracOdd u1) + texV2 (fracOdd u1)) _ _ x rfl hx)
    have room := room_even_of_top _ _ _ _ q'.num q'.den hpl.1 hpl.2 hql.1 (by omega) hdet (by omega) (by omega) f3 f4
    simp only [texV2, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] at hb
    nlinarith [hW.1, hb, room]
  · have hb := left_band_even u2 _ (shift_vRev _ (texV2 (fracOdd u1) + texV2 (fracOdd u1)) 0 _ x (add_zero _).symm hx)
    have room := room_even_of_left _ _ _ _ q'.num q'.den hpl.1 hpl.2 hql.1 (by omega) hdet (by omega) (by omega) f3 f4
    simp only [texV2, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] at hb
    nlinarith [hW.2.2.1, hb, room]

/-! ### The word `1` -/

theorem regs_one : SurgicalWeak.regsAt [Digit.one] = (some [], some []) := by decide

theorem one_block_window : ∀ x ∈ GlueRespectsAll.blockSitesOdd [Digit.one] [] [] 5,
    ¬ SiteInduction.InH (SiteInduction.curE []) (x - (4, 2)) := by decide

/-- **The word `1`**: the block of `Q^{-,2}` avoids `Q^{+,1}` (a finite check in the window of the even register). -/
theorem col_one : ∀ x ∈ GlueRespectsAll.blockSitesOdd [Digit.one] [] [] 5,
    x ∈ ChildGlue.pieceSet (ChildGlue.oddP [Digit.one]) (ChildGlue.oddQ [Digit.one]) (ChildGlue.tOddSet [])
      (ChildGlue.tEvenSet []) 2 → False := by
  intro x hx hxj
  have hQ0 : (ChildGlue.oddQ [Digit.one]).getD 0 0 = (4, 2) := by decide
  simp only [ChildGlue.pieceSet, ClosedPathCycle.oddP_length, lt_self_iff_false, if_false, Nat.sub_self, hQ0] at hxj
  have hin : x - (4, 2) ∈ evenTile [] := Finset.mem_coe.1 (ClosedPathAssembly.sub_mem_of_shift _ _ _ hxj)
  exact one_block_window x hx ((SubEvenCopy.mem_evenTile_iff [] _).1 hin)

/-! ### The column inputs -/

/-- **The column inputs hold at every uncorrected child.** -/
theorem columnInput : GlueBlockExcl.ColumnInput := by
  intro w u1 u2 hw hreg
  have hp : (parentsAt w).odd = fracOdd u1 := (WeakStepAssembly.regsAt_parents w).1 u1 (by rw [hreg])
  have hq : (parentsAt w).even = fracEven u2 := (WeakStepAssembly.regsAt_parents w).2 u2 (by rw [hreg])
  have hne : w ≠ [] := fun h => hw (Or.inl h)
  refine ⟨fun _ => ⟨fun hl => ?_, fun hs hl => ?_⟩, fun _ hl => ?_⟩
  · by_cases hph : phase w = 1
    · exact col_odd_of w u1 u2 hne hph hp hq hl
    · exact col_odd_ef w u1 u2 hne hph hp hq hl
  · obtain ⟨d, rfl⟩ := hs
    simp only [List.getLast?_singleton, Option.some.injEq] at hl
    subst hl
    rw [regs_one] at hreg
    simp only [Prod.mk.injEq, Option.some.injEq] at hreg
    obtain ⟨rfl, rfl⟩ := hreg
    exact col_one
  · by_cases hph : phase w = 1
    · exact col_even_of w u1 u2 hne hph hp hq hl
    · exact col_even_ef w u1 u2 hne hph hp hq hl

/-- **`GlueRespectsInput` for the paper's data**: item (a) of `lemma:weak_standard_odometer_properties` for the glued standard
children at the children that Section 8 does not correct. -/
theorem glueRespectsInput_paper (D : JointFamily.JointData) (hS : D.S = WeakStepPaper.paperS) :
    WeakStepAssembly.GlueRespectsInput D :=
  GlueBlockExcl.glueRespectsInput_of_columns D hS columnInput

/-- **`GlueLatticeInput` for the paper's data**: item (c) of the glued standard children at the uncorrected children, given the
zero-slope normalisation of the registers. -/
theorem glueLatticeInput_paper (D : JointFamily.JointData) (hS : D.S = WeakStepPaper.paperS)
    (hsl : WeakStepAssembly.TileSlopeZero D) : WeakStepAssembly.GlueLatticeInput D :=
  GlueBlockExcl.glueLatticeInput_of_columns D hS hsl columnInput

end FLatticePaper.Tiles.GlueColumns
