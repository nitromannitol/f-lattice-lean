import FLatticePaper.Tiles.SiteBoundary
import FLatticePaper.Tiles.SiteFwdCover
import FLatticePaper.Tiles.SiteHullEven
import FLatticePaper.Tiles.SiteVertCover

/-! Task 53, item 4 (the `t_hi` boundary sites are forward marks): a site of `H` with `−n < t` (odd) or `0 < t` (even), and the index
bound of `tband_hi_m_bounds`, is a site of the forward string of `q :: ℓ'`. The offsets are the same as in `tband_stringSites`:
`(1, 0)` for an odd site (its error is `d − t`), and `(0,0)` or the tip `(1,−1)` for an even site (`t ≤ C` or `C < t`). -/

namespace FLatticePaper.Tiles.SiteBoundaryCover

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.CeilWords
  FLatticePaper.Tiles.SiteBand FLatticePaper.Tiles.SiteBoundary FLatticePaper.Tiles.SiteHullOdd FLatticePaper.Tiles.SiteHullEven
  FLatticePaper.Tiles.SiteVertCover FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.SiteBase
  FLatticePaper.Tiles.Standard
  FLatticePaper.Tiles.SiteMarksCursor FLatticePaper.Tiles.SiteFwdLink FLatticePaper.Tiles.SiteFwdCover

theorem cover_hi_odd (n d : ℤ) (ℓ' : BinaryWord) (_hn : 0 < n) (hnd : n < d)
    (hB : CursorB (Letter.q :: ℓ') n d)
    (x y t _s a _l : ℤ) (hodd : (x + y) % 2 = 1) (hm1 : 1 ≤ x + y) (hm2 : x + y ≤ 2 * ((Letter.q :: ℓ').length : ℤ) - 1)
    (ht : t = n * x - d * y) (htl : -n < t) (htL : t ≤ d + n - a) (ha : a = n) :
    (x, y) ∈ stringSites false false (Letter.q :: ℓ') := by
  have hL0 : 0 < d + n := by omega
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = (x + y - 1) / 2 := ⟨((x + y - 1) / 2).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hk2 : 2 * (k : ℤ) + 1 = x + y := by omega
  have hkl : k < (Letter.q :: ℓ').length := by
    have h1 : (k : ℤ) < (((Letter.q :: ℓ').length : ℕ) : ℤ) := by omega
    exact_mod_cast h1
  have hkn1 : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
  have hE : (d + n) * (y + 1) - 2 * n * ((k : ℤ) + 1) = d - t := by
    linear_combination (-(n : ℤ)) * hk2 + ht
  have hcursor : qPrefix (Letter.q :: ℓ') (k + 1) = y + 1 := by
    apply qPrefix_eq_of_err (Letter.q :: ℓ') n d hB hL0 (k + 1) (by omega) (y + 1)
    · rw [hkn1, hE]
      linarith
    · rw [hkn1, hE]
      linarith
  refine mem_of_cursor ℓ' n d hB hnd k hkl (1, 0) x y ?_ ⟨?_, ?_, ?_⟩ ?_
  · show qPrefix (Letter.q :: ℓ') (k + 1) = y + 1 - 0
    rw [hcursor]
    ring
  · intro _
    dsimp only
    norm_num
  · intro _ _
    dsimp only
    norm_num
  · intro _ _
    dsimp only
    exact Or.inl ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
  · dsimp only
    linarith

theorem cover_hi_even (n d : ℤ) (ℓ' : BinaryWord) (hn : 0 < n) (hnd : n < d)
    (hB : CursorB (Letter.q :: ℓ') n d)
    (x y t _s a _l : ℤ) (heven : (x + y) % 2 = 0) (hm1 : 1 ≤ x + y) (hm2 : x + y ≤ 2 * ((Letter.q :: ℓ').length : ℤ) - 2)
    (ht : t = n * x - d * y) (_htl : -n < t) (hte : 0 < t) (htL : t ≤ d + n - a)
    (ha : a = min (2 * n) (d - n)) :
    (x, y) ∈ stringSites false false (Letter.q :: ℓ') := by
  have hL0 : 0 < d + n := by omega
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = (x + y) / 2 := ⟨((x + y) / 2).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hk2 : 2 * (k : ℤ) = x + y := by omega
  have hkl : k < (Letter.q :: ℓ').length := by
    have h1 : (k : ℤ) < (((Letter.q :: ℓ').length : ℕ) : ℤ) := by omega
    exact_mod_cast h1
  have hkn1 : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
  have hE : (d + n) * (y + 1) - 2 * n * ((k : ℤ) + 1) = (d - n) - t := by
    linear_combination (-(n : ℤ)) * hk2 + ht
  by_cases ht0 : t ≤ d - n
  · have hcursor : qPrefix (Letter.q :: ℓ') (k + 1) = y + 1 := by
      apply qPrefix_eq_of_err (Letter.q :: ℓ') n d hB hL0 (k + 1) (by omega) (y + 1)
      · rw [hkn1, hE]
        linarith
      · rw [hkn1, hE]
        linarith
    refine mem_of_cursor ℓ' n d hB hnd k hkl (0, 0) x y ?_ ⟨?_, ?_, ?_⟩ ?_
    · show qPrefix (Letter.q :: ℓ') (k + 1) = y + 1 - 0
      rw [hcursor]
      ring
    · intro _
      dsimp only
      norm_num
    · intro _ _
      dsimp only
      norm_num
    · intro _ _
      dsimp only
      exact Or.inl ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
    · dsimp only
      linarith
  · have ht2n : t ≤ 2 * n := by
      rw [ha] at htL
      omega
    have hE2 : (d + n) * (y + 2) - 2 * n * ((k : ℤ) + 1) = 2 * d - t := by
      linear_combination (-(n : ℤ)) * hk2 + ht
    have hcursor : qPrefix (Letter.q :: ℓ') (k + 1) = y + 2 := by
      apply qPrefix_eq_of_err (Letter.q :: ℓ') n d hB hL0 (k + 1) (by omega) (y + 2)
      · rw [hkn1, hE2]
        linarith
      · rw [hkn1, hE2]
        linarith
    refine mem_of_cursor ℓ' n d hB hnd k hkl (1, -1) x y ?_ ⟨?_, ?_, ?_⟩ ?_
    · show qPrefix (Letter.q :: ℓ') (k + 1) = y + 1 - (-1)
      rw [hcursor]
      ring
    · intro h
      dsimp only at h ⊢
      exfalso
      linarith
    · intro h1 h2
      dsimp only at h1 h2 ⊢
      exfalso
      linarith
    · intro _ _
      dsimp only
      exact Or.inr (Or.inr rfl)
    · dsimp only
      show x = 2 * (k : ℤ) + 1 - (y + 1 - (-1)) + 1
      linarith

/-- **The `t_hi` boundary sites of the odd tile are forward marks.** An odd-tile site with `−n < t` (and an even site with
`0 < t`) of `H` lies in the forward string of `hWordOf w false`. -/
theorem sh_hi_odd (w : Word) (z : ℤ × ℤ) (hz : InH (curO w) z)
    (htl : -(curO w).num < tCo (curO w) z) (hte : (z.1 + z.2) % 2 = 0 → 0 < tCo (curO w) z) :
    z ∈ stringSites false false (hWordOf w false) := by
  have hpos := curO_pos_lt w
  have hodd : ((curO w).num + (curO w).den) % 2 = 1 := curO_odd w
  obtain ⟨ℓ', hℓ⟩ := head_q_of_ceil _ _ _ (cw_childP w) (by omega) (by omega)
  have hC := cw_childP w
  rw [hℓ] at hC ⊢
  have hB : CursorB (Letter.q :: ℓ') (curO w).num (curO w).den := cursorB_of_ceil _ _ _ hC
  have hlen : (((Letter.q :: ℓ').length : ℕ) : ℤ) * 2 = 2 * ((curO w).den + (curO w).num) := by
    rw [hC.1]
    ring
  obtain ⟨hz1, hz2, hz3, hz4⟩ := hz
  have hμ : muOf (curO w) = 2 := by
    unfold muOf
    rw [if_pos hodd]
  rw [hμ] at hz4
  obtain ⟨hm1, hm2⟩ := tband_hi_m_bounds (curO w).num (curO w).den 2 z.1 z.2 (tCo (curO w) z) (sCo (curO w) z)
    (aOf (curO w) (decide ((z.1 + z.2) % 2 = 0))) (lOf (curO w) (decide ((z.1 + z.2) % 2 = 0)))
    (by omega) (by omega) (fun _ => rfl) (fun h => by omega) rfl rfl (site_ab (curO w) z)
    htl hte hz2 hz3 (by unfold tOf at hz4; exact hz4)
  rcases (show (z.1 + z.2) % 2 = 0 ∨ (z.1 + z.2) % 2 = 1 by omega) with hz' | hz'
  · have hm2' : z.1 + z.2 ≤ 2 * ((Letter.q :: ℓ').length : ℤ) - 2 := by omega
    exact cover_hi_even (curO w).num (curO w).den ℓ' hpos.1 hpos.2 hB z.1 z.2 (tCo (curO w) z) (sCo (curO w) z)
      (aOf (curO w) (decide ((z.1 + z.2) % 2 = 0))) (lOf (curO w) (decide ((z.1 + z.2) % 2 = 0)))
      hz' hm1 hm2' rfl htl (hte hz') hz2 ((site_ab (curO w) z).2 hz').1
  · have hm2' : z.1 + z.2 ≤ 2 * ((Letter.q :: ℓ').length : ℤ) - 1 := by omega
    exact cover_hi_odd (curO w).num (curO w).den ℓ' hpos.1 hpos.2 hB z.1 z.2 (tCo (curO w) z) (sCo (curO w) z)
      (aOf (curO w) (decide ((z.1 + z.2) % 2 = 0))) (lOf (curO w) (decide ((z.1 + z.2) % 2 = 0)))
      hz' hm1 hm2' rfl htl hz2 ((site_ab (curO w) z).1 hz').1

/-- **The `t_hi` boundary sites of the even tile are forward marks.** -/
theorem sh_hi_even (w : Word) (z : ℤ × ℤ) (hz : InH (curE w) z)
    (htl : -(curE w).num < tCo (curE w) z) (hte : (z.1 + z.2) % 2 = 0 → 0 < tCo (curE w) z) :
    z ∈ stringSites false false (hWordOf w true) := by
  have hpos := curE_pos_lt w
  have hpar := curE_num_add_den_even w
  obtain ⟨ℓ', hℓ⟩ := head_even w
  have hC := cw_childQ_even w
  rw [hℓ] at hC ⊢
  have hB : CursorB (Letter.q :: ℓ') (curE w).num (curE w).den :=
    cursorB_even _ _ _ hC (by omega)
  have hlen : (((Letter.q :: ℓ').length : ℕ) : ℤ) * 2 = 1 * ((curE w).den + (curE w).num) := by
    rw [hC.1]
    have : ((curE w).den + (curE w).num) / 2 * 2 = (curE w).den + (curE w).num := by omega
    linarith
  have hμ : muOf (curE w) = 1 := by
    unfold muOf
    rw [if_neg (by omega)]
  obtain ⟨hz1, hz2, hz3, hz4⟩ := hz
  rw [hμ] at hz4
  obtain ⟨hm1, hm2⟩ := tband_hi_m_bounds (curE w).num (curE w).den 1 z.1 z.2 (tCo (curE w) z) (sCo (curE w) z)
    (aOf (curE w) (decide ((z.1 + z.2) % 2 = 0))) (lOf (curE w) (decide ((z.1 + z.2) % 2 = 0)))
    (by omega) (by omega) (fun h => by omega) (fun _ => rfl) rfl rfl (site_ab (curE w) z)
    htl hte hz2 hz3 (by unfold tOf at hz4; exact hz4)
  rcases (show (z.1 + z.2) % 2 = 0 ∨ (z.1 + z.2) % 2 = 1 by omega) with hz' | hz'
  · have hm2' : z.1 + z.2 ≤ 2 * ((Letter.q :: ℓ').length : ℤ) - 2 := by omega
    exact cover_hi_even (curE w).num (curE w).den ℓ' hpos.1 hpos.2 hB z.1 z.2 (tCo (curE w) z) (sCo (curE w) z)
      (aOf (curE w) (decide ((z.1 + z.2) % 2 = 0))) (lOf (curE w) (decide ((z.1 + z.2) % 2 = 0)))
      hz' hm1 hm2' rfl htl (hte hz') hz2 ((site_ab (curE w) z).2 hz').1
  · have hm2' : z.1 + z.2 ≤ 2 * ((Letter.q :: ℓ').length : ℤ) - 1 := by omega
    exact cover_hi_odd (curE w).num (curE w).den ℓ' hpos.1 hpos.2 hB z.1 z.2 (tCo (curE w) z) (sCo (curE w) z)
      (aOf (curE w) (decide ((z.1 + z.2) % 2 = 0))) (lOf (curE w) (decide ((z.1 + z.2) % 2 = 0)))
      hz' hm1 hm2' rfl htl hz2 ((site_ab (curE w) z).1 hz').1

/-- **The `s_lo` boundary sites of the odd tile are vertical marks.** A site of `H` with `s < L` (odd) or `s < 2d` (even)
has `(z₁+1, z₂+1)` in the vertical string of `(vWordOf w false).reverse`. -/
theorem sv_hi_odd (w : Word) (z : ℤ × ℤ) (hz : InH (curO w) z)
    (hsodd : (z.1 + z.2) % 2 = 1 → sCo (curO w) z < (curO w).den + (curO w).num)
    (heven : (z.1 + z.2) % 2 = 0 → sCo (curO w) z < 2 * (curO w).den) :
    (z.1 + 1, z.2 + 1) ∈ stringSites true true (vWordOf w false).reverse := by
  have hpos := curO_pos_lt w
  have hodd : ((curO w).num + (curO w).den) % 2 = 1 := curO_odd w
  obtain ⟨ℓ'', hℓ⟩ := head_q_of_ceil _ _ _ (cw_vert w) (by omega) (by omega)
  have hC := cw_vert w
  rw [hℓ] at hC ⊢
  have hV := cursorV_of_ceil _ _ _ hC
  obtain ⟨hz1, hz2, hz3, -⟩ := hz
  have hM := vband_hi_M_odd (curO w).num (curO w).den z.1 z.2 (tCo (curO w) z) (sCo (curO w) z)
    (aOf (curO w) (decide ((z.1 + z.2) % 2 = 0))) (lOf (curO w) (decide ((z.1 + z.2) % 2 = 0)))
    hpos.1 hpos.2 (by omega) rfl rfl (site_ab (curO w) z) (by unfold tOf at hz1; exact hz1) hz2 hz3 hsodd heven
  exact vband_stringSites_ext (curO w).num (curO w).den z.1 z.2 (tCo (curO w) z) (sCo (curO w) z)
    (aOf (curO w) (decide ((z.1 + z.2) % 2 = 0))) (lOf (curO w) (decide ((z.1 + z.2) % 2 = 0))) ℓ''
    hpos.1 hpos.2 hM hV hC.1 rfl (site_ab (curO w) z) hz3 hsodd heven

/-- **The `s_lo` boundary sites of the even tile are vertical marks.** -/
theorem sv_hi_even (w : Word) (z : ℤ × ℤ) (hz : InH (curE w) z)
    (hsodd : (z.1 + z.2) % 2 = 1 → sCo (curE w) z < (curE w).den + (curE w).num)
    (heven : (z.1 + z.2) % 2 = 0 → sCo (curE w) z < 2 * (curE w).den) :
    (z.1 + 1, z.2 + 1) ∈ stringSites true true (vWordOf w true).reverse := by
  have hpos := curE_pos_lt w
  have hpar := curE_num_add_den_even w
  have hdodd := curE_den_odd w
  obtain ⟨ℓ'', hℓ⟩ := head_q_of_ceil _ _ _ (cw_vert_even w) (by omega) (by omega)
  have hC := cw_vert_even w
  rw [hℓ] at hC ⊢
  have hV := cursorV_of_ceil _ _ _ hC
  obtain ⟨hz1, hz2, hz3, -⟩ := hz
  have hM := vband_hi_M_even (curE w).num (curE w).den z.1 z.2 (tCo (curE w) z) (sCo (curE w) z)
    (aOf (curE w) (decide ((z.1 + z.2) % 2 = 0))) (lOf (curE w) (decide ((z.1 + z.2) % 2 = 0)))
    hpos.1 hpos.2 (by omega) hdodd rfl rfl (site_ab (curE w) z) (by unfold tOf at hz1; exact hz1) hz2 hz3 hsodd heven
  exact vband_stringSites_ext (curE w).num (curE w).den z.1 z.2 (tCo (curE w) z) (sCo (curE w) z)
    (aOf (curE w) (decide ((z.1 + z.2) % 2 = 0))) (lOf (curE w) (decide ((z.1 + z.2) % 2 = 0))) ℓ''
    hpos.1 hpos.2 hM hV hC.1 rfl (site_ab (curE w) z) hz3 hsodd heven

end FLatticePaper.Tiles.SiteBoundaryCover
