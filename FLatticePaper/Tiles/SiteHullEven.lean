import FLatticePaper.Tiles.SiteHullOdd

/-! Task 53, item 4 (the hull of the even tile): the words and parameters of the even standard tile of `w`.

For `w` a word, the even current fraction `E = curE w = (n, d)` satisfies `0 < n < d`, `n + d` even, `d` odd (`Fraction.rotate_odd_of_even`
on the reduced even current), and `d − n`, `d + n` are even. The forward word `hWordOf w true` is a ceiling word of slope `n/((d+n)/2)`
(its `sEven`), and the vertical word, reversed, is a ceiling word of slope `n/d` (`ceil_rev_comp` on the child word of the swapped word,
which has slope `(d−n)/d` since `(curE w).rotate = ((d−n)/2, (d+n)/2)`). -/

namespace FLatticePaper.Tiles.SiteHullEven

open FLatticePaper FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.Standard FLatticePaper.Tiles.CeilWords
  FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.SiteScope
  FLatticePaper.Tiles.SiteFwdLink FLatticePaper.Tiles.SiteFwdCover FLatticePaper.Tiles.SiteVertLink
  FLatticePaper.Tiles.SiteVertCover FLatticePaper.Tiles.SiteVertWord FLatticePaper.Tiles.StandardHalfTurn
  FLatticePaper.Tiles.SiteHull FLatticePaper.Tiles.SiteHullOdd FLatticePaper.Tiles.SiteLowLeft
  FLatticePaper.Tiles.SiteUnique FLatticePaper.Tiles.SiteRot

theorem curE_pos_lt (w : Word) : 0 < (curE w).num ∧ (curE w).num < (curE w).den := by
  obtain ⟨h1, h2, h3, h4⟩ := parents_bounds w
  simp only [curE, Parents.current, Parents.combine]
  constructor <;> omega

theorem curE_even (w : Word) : Fraction.Even (curE w) := (parentsAt_valid w).current_even_parity

theorem curE_reduced (w : Word) : Fraction.Reduced (curE w) := (parentsAt_valid w).current_reduced .even

/-- The denominator of the even current fraction is odd (its rotation is odd). -/
theorem curE_den_odd (w : Word) : (curE w).den % 2 = 1 := by
  have h := Fraction.rotate_odd_of_even (curE_even w) (curE_reduced w)
  rw [Fraction.rotate_of_even (curE_even w)] at h
  unfold Fraction.Odd at h
  have hpar : ((curE w).num + (curE w).den) % 2 = 0 := curE_even w
  simp only at h
  omega

theorem curE_num_add_den_even (w : Word) : ((curE w).num + (curE w).den) % 2 = 0 := curE_even w

/-- The forward word of the even tile is a ceiling word of slope `n/((d+n)/2)`. -/
theorem cw_childQ_even (w : Word) :
    CeilWord (hWordOf w true) (curE w).num (((curE w).den + (curE w).num) / 2) := by
  obtain ⟨-, c2, -, -⟩ := quadInv_all w
  simp only [hWordOf, if_true]
  exact c2

/-- The child word of the swapped word has slope `(d−n)/d`. -/
theorem cw_childP_swap (w : Word) :
    CeilWord (quadAt [] (swapW w)).childP ((curE w).den - (curE w).num) (curE w).den := by
  obtain ⟨c1, -, -, -⟩ := quadInv_all (swapW w)
  have hrot : (parentsAt (swapW w)).current .odd = (curE w).rotate := by
    rw [parentsAt_swapW]
    exact ((parentsAt_valid w).rotate_current_even).symm
  have hpar := curE_num_add_den_even w
  have h2 : sOdd (curE w).rotate = ((curE w).den - (curE w).num, (curE w).den) := by
    rw [Fraction.rotate_of_even (curE_even w)]
    unfold sOdd
    apply Prod.ext
    · simp only
      omega
    · simp only
      omega
  have hc := c1
  rw [hrot, h2] at hc
  exact hc

/-- A ceiling word of slope `n/m` with `2m = d + n` has the cursor bounds of `CursorB` (the even length). -/
theorem cursorB_even (ℓ : BinaryWord) (n d : ℤ) (hC : CeilWord ℓ n ((d + n) / 2)) (hd : (d + n) % 2 = 0) :
    CursorB ℓ n d := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, d + n = 2 * m := ⟨(d + n) / 2, by omega⟩
  have hmm : (d + n) / 2 = m := by omega
  rw [hmm] at hC
  intro j hj
  have hj' : (j : ℤ) ≤ m := by have := hC.1; omega
  obtain ⟨h1, h2⟩ := hC.2 j hj'
  rw [hm]
  constructor <;> nlinarith [h1, h2]

/-- The vertical word of the even tile, reversed, is a ceiling word of slope `n/d`. -/
theorem cw_vert_even (w : Word) :
    CeilWord (vWordOf w true).reverse (curE w).num (curE w).den := by
  have h3 := ceil_rev_comp (quadAt [] (swapW w)).childP _ _ (cw_childP_swap w)
    (by have := curE_pos_lt w; omega)
  have hv : vWordOf w true = (quadAt [] (swapW w)).childP.map swapLetter := by simp [vWordOf]
  rw [hv]
  have e3 : (curE w).den - ((curE w).den - (curE w).num) = (curE w).num := by ring
  rw [e3] at h3
  exact h3

/-- The forward word of the even tile starts with `q`. -/
theorem head_even (w : Word) : ∃ ℓ' : BinaryWord, hWordOf w true = Letter.q :: ℓ' := by
  have hpos := curE_pos_lt w
  have hpar := curE_num_add_den_even w
  exact head_q_of_ceil _ _ _ (cw_childQ_even w) (by omega) (by omega)

/-- **The forward band of the even tile is in the forward marks.** -/
theorem sh_even_of_tband (w : Word) (z : ℤ × ℤ) (hz : InH (curE w) z)
    (hta : aOf (curE w) (decide ((z.1 + z.2) % 2 = 0)) ≤ tCo (curE w) z) :
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
  exact tband_stringSites (curE w).num (curE w).den 1 ℓ' (by omega) (by omega) hB hlen
    (fun h => by omega) (fun _ => rfl) z.1 z.2 (tCo (curE w) z) (sCo (curE w) z)
    (aOf (curE w) (decide ((z.1 + z.2) % 2 = 0))) (lOf (curE w) (decide ((z.1 + z.2) % 2 = 0)))
    rfl rfl (site_ab (curE w) z) hta hz2 hz3
    (by unfold tOf at hz4; exact hz4)

/-- **The vertical band of the even tile is in the vertical marks.** -/
theorem sv_even_of_sband (w : Word) (z : ℤ × ℤ) (hz : InH (curE w) z)
    (hsb : sCo (curE w) z ≤ 2 * (curE w).num - lOf (curE w) (decide ((z.1 + z.2) % 2 = 0))) :
    (z.1 + 1, z.2 + 1) ∈ stringSites true true (vWordOf w true).reverse := by
  have hpos := curE_pos_lt w
  have hpar := curE_num_add_den_even w
  have hdodd := curE_den_odd w
  obtain ⟨ℓ'', hℓ⟩ := head_q_of_ceil _ _ _ (cw_vert_even w) (by omega) (by omega)
  have hC := cw_vert_even w
  rw [hℓ] at hC ⊢
  have hV := cursorV_of_ceil _ _ _ hC
  obtain ⟨hz1, hz2, hz3, -⟩ := hz
  have hM := vband_M_even (curE w).num (curE w).den z.1 z.2 (tCo (curE w) z) (sCo (curE w) z)
    (aOf (curE w) (decide ((z.1 + z.2) % 2 = 0))) (lOf (curE w) (decide ((z.1 + z.2) % 2 = 0)))
    (by omega) (by omega) (by omega) (by omega) rfl rfl (site_ab (curE w) z)
    (by unfold tOf at hz1; exact hz1) hz2 hz3 hsb
  exact vband_stringSites_M (curE w).num (curE w).den z.1 z.2 (tCo (curE w) z) (sCo (curE w) z)
    (aOf (curE w) (decide ((z.1 + z.2) % 2 = 0))) (lOf (curE w) (decide ((z.1 + z.2) % 2 = 0))) ℓ''
    (by omega) (by omega) hM hV hC.1 rfl (site_ab (curE w) z) hz3 hsb

/-- The even centre vector: `tF(rotate E) + mulI (tF E) = (−(n+1), 1 − 2n − d)` for `E = (n, d)` with `n + d` even. -/
theorem even_centre_vec (n d : ℤ) (h : (n + d) % 2 = 0) :
    tF ⟨(d - n) / 2, (d + n) / 2⟩ + mulI (tF ⟨n, d⟩) = (-(n + 1), 1 - 2 * n - d) := by
  apply Prod.ext
  · simp only [tF, tV, mulI, Prod.fst_add]
    omega
  · simp only [tF, tV, mulI, Prod.snd_add]
    omega

/-- **The half-turn centre of the even tile** is `R' = (n + 1, 2n + d − 1)`. -/
theorem centre_even (w : Word) :
    halfTurnCentre (evenTile w) = ((curE w).num + 1, 2 * (curE w).num + (curE w).den - 1) := by
  have hpos := curE_pos_lt w
  have hpar := curE_num_add_den_even w
  have hdodd := curE_den_odd w
  have hv : tF ((parentsAt (swapW w)).current .odd) + mulI (tF ((parentsAt w).current .even)) =
      (-((curE w).num + 1), 1 - 2 * (curE w).num - (curE w).den) := by
    have hrot : (parentsAt (swapW w)).current .odd = (curE w).rotate := by
      rw [parentsAt_swapW]
      exact ((parentsAt_valid w).rotate_current_even).symm
    rw [hrot, Fraction.rotate_of_even (curE_even w)]
    exact even_centre_vec (curE w).num (curE w).den hpar
  have hsym : ∀ z ∈ evenTile w,
      ((curE w).num + 1 - z.1, 2 * (curE w).num + (curE w).den - 1 - z.2) ∈ evenTile w := by
    intro z hz
    have hx : ((-z.1, -z.2) : ℤ × ℤ) ∈ rot (rot (evenTile w)) := by
      apply mem_rot.mpr
      apply mem_rot.mpr
      simpa using hz
    rw [rot_rot_evenTile w, mem_shift, hv] at hx
    have e : ((curE w).num + 1 - z.1, 2 * (curE w).num + (curE w).den - 1 - z.2) =
        ((-z.1, -z.2) : ℤ × ℤ) - (-((curE w).num + 1), 1 - 2 * (curE w).num - (curE w).den) := by
      apply Prod.ext
      · simp only [Prod.fst_sub]
        ring
      · simp only [Prod.snd_sub]
        ring
    rw [e]
    exact hx
  exact halfTurnCentre_of_symm (evenTile w) _ ⟨0, (standard_tiles_normalised w).2.1⟩ hsym

/-- **The symmetry of the even `H`.** For `f` of even type, `z ∈ H_f` implies `R' − z ∈ H_f` with `R' = (num + 1, 2num + den − 1)`:
`t ↦ L − T − t`, `s ↦ T + 2num − s`. -/
theorem inH_halfTurn_even (f : Fraction) (heven : (f.num + f.den) % 2 = 0) (z : ℤ × ℤ) (hz : InH f z) :
    InH f (f.num + 1 - z.1, 2 * f.num + f.den - 1 - z.2) := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  have hμ : muOf f = 1 := by
    unfold muOf
    rw [if_neg (by omega)]
  have ht' : tCo f (f.num + 1 - z.1, 2 * f.num + f.den - 1 - z.2) = (f.den + f.num) - tOf f - tCo f z := by
    unfold tCo tOf
    ring
  have hs' : sCo f (f.num + 1 - z.1, 2 * f.num + f.den - 1 - z.2) = tOf f + 2 * f.num - sCo f z := by
    unfold sCo tOf
    ring
  have hev : decide (((f.num + 1 - z.1) + (2 * f.num + f.den - 1 - z.2)) % 2 = 0) =
      decide ((z.1 + z.2) % 2 = 0) := by
    congr 1
    apply propext
    omega
  unfold InH
  simp only at hev ⊢
  rw [hev, ht', hs', hμ]
  rw [hμ] at h4
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- A forward site of the even tile is a mark. -/
theorem mem_marksEven_of_sh (w : Word) (z : ℤ × ℤ) (h : z ∈ stringSites false false (hWordOf w true)) :
    z ∈ marksEven w := by
  have hc := lowLeft_evenTile w
  have hz : z ∈ (stringSites false false (hWordOf w true)).map
      (fun z => (z.1 + (lowLeft (evenTile w)).1, z.2 + (lowLeft (evenTile w)).2)) :=
    List.mem_map.mpr ⟨z, h, by rw [hc]; simp⟩
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hz))

/-- A vertical site of the even tile (shifted by `(1,1)`) is a mark. -/
theorem mem_marksEven_of_sv (w : Word) (z : ℤ × ℤ)
    (h : (z.1 + 1, z.2 + 1) ∈ stringSites true true (vWordOf w true).reverse) : z ∈ marksEven w := by
  have hc := lowLeft_evenTile w
  have hz : z ∈ (stringSites true true (vWordOf w true).reverse).map
      (fun z => (z.1 + (lowLeft (evenTile w)).1 - 1, z.2 + (lowLeft (evenTile w)).2 - 1)) :=
    List.mem_map.mpr ⟨(z.1 + 1, z.2 + 1), h, by rw [hc]; simp⟩
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hz))

/-- A reflected forward site of the even tile is a mark. -/
theorem mem_marksEven_of_sh_refl (w : Word) (z : ℤ × ℤ)
    (h : ((curE w).num + 1 - z.1, 2 * (curE w).num + (curE w).den - 1 - z.2) ∈
      stringSites false false (hWordOf w true)) : z ∈ marksEven w := by
  have hc := lowLeft_evenTile w
  have hA : ((curE w).num + 1 - z.1, 2 * (curE w).num + (curE w).den - 1 - z.2) ∈
      (stringSites false false (hWordOf w true)).map
        (fun z => (z.1 + (lowLeft (evenTile w)).1, z.2 + (lowLeft (evenTile w)).2)) :=
    List.mem_map.mpr ⟨_, h, by rw [hc]; simp⟩
  have hz : z ∈ ((stringSites false false (hWordOf w true)).map
      (fun z => (z.1 + (lowLeft (evenTile w)).1, z.2 + (lowLeft (evenTile w)).2))).map
        (halfTurn (evenTile w)) :=
    List.mem_map.mpr ⟨_, hA, by
      rw [halfTurn, centre_even]
      simp⟩
  exact List.mem_append_left _ (List.mem_append_right _ hz)

/-- A reflected vertical site of the even tile is a mark. -/
theorem mem_marksEven_of_sv_refl (w : Word) (z : ℤ × ℤ)
    (h : ((curE w).num + 1 - z.1 + 1, 2 * (curE w).num + (curE w).den - 1 - z.2 + 1) ∈
      stringSites true true (vWordOf w true).reverse) : z ∈ marksEven w := by
  have hc := lowLeft_evenTile w
  have hA : ((curE w).num + 1 - z.1, 2 * (curE w).num + (curE w).den - 1 - z.2) ∈
      (stringSites true true (vWordOf w true).reverse).map
        (fun z => (z.1 + (lowLeft (evenTile w)).1 - 1, z.2 + (lowLeft (evenTile w)).2 - 1)) :=
    List.mem_map.mpr ⟨_, h, by rw [hc]; simp⟩
  have hz : z ∈ ((stringSites true true (vWordOf w true).reverse).map
      (fun z => (z.1 + (lowLeft (evenTile w)).1 - 1, z.2 + (lowLeft (evenTile w)).2 - 1))).map
        (halfTurn (evenTile w)) :=
    List.mem_map.mpr ⟨_, hA, by
      rw [halfTurn, centre_even]
      simp⟩
  exact List.mem_append_right _ hz

/-- **The hull of the even tile.** A site of `H_{curE w}` that is not the unique representative of its class is a marked site. -/
theorem hull_even (w : Word) (z : ℤ × ℤ) (hz : InH (curE w) z)
    (hnu : ¬ UniqueIn (curE w) z) : z ∈ marksEven w := by
  have hpos := curE_pos_lt w
  have heven : ((curE w).num + (curE w).den) % 2 = 0 := curE_num_add_den_even w
  have hμ : muOf (curE w) = 1 := by
    unfold muOf
    rw [if_neg (by omega)]
  by_cases c1 : tCo (curE w) z < aOf (curE w) (decide ((z.1 + z.2) % 2 = 0))
  · by_cases c2 : (curE w).den + (curE w).num - aOf (curE w) (decide ((z.1 + z.2) % 2 = 0)) - tOf (curE w)
        < tCo (curE w) z
    · by_cases c3 : 2 * (curE w).num - lOf (curE w) (decide ((z.1 + z.2) % 2 = 0)) < sCo (curE w) z
      · by_cases c4 : sCo (curE w) z < lOf (curE w) (decide ((z.1 + z.2) % 2 = 0)) + muOf (curE w) * tOf (curE w)
        · exact absurd (unique_of_bounds (curE w) hpos.1 hpos.2 z hz c1 c2 c3 c4) hnu
        · -- the upper `s`-band: `s ≥ l + T`, reflected to the lower vertical band
          push Not at c4
          rw [hμ] at c4
          have hz' := inH_halfTurn_even (curE w) heven z hz
          have hpar : ((((curE w).num + 1 - z.1) + (2 * (curE w).num + (curE w).den - 1 - z.2)) % 2 = 0) ↔
              ((z.1 + z.2) % 2 = 0) := by omega
          have hdec : decide ((((curE w).num + 1 - z.1) +
              (2 * (curE w).num + (curE w).den - 1 - z.2)) % 2 = 0) = decide ((z.1 + z.2) % 2 = 0) :=
            decide_eq_decide.mpr hpar
          have hS : sCo (curE w) ((curE w).num + 1 - z.1, 2 * (curE w).num + (curE w).den - 1 - z.2)
              = tOf (curE w) + 2 * (curE w).num - sCo (curE w) z := by
            unfold sCo tOf
            ring
          have hsb : sCo (curE w) ((curE w).num + 1 - z.1, 2 * (curE w).num + (curE w).den - 1 - z.2)
              ≤ 2 * (curE w).num - lOf (curE w) (decide ((((curE w).num + 1 - z.1) +
                (2 * (curE w).num + (curE w).den - 1 - z.2)) % 2 = 0)) := by
            rw [hdec, hS]
            omega
          exact mem_marksEven_of_sv_refl w z (sv_even_of_sband w _ hz' hsb)
      · push Not at c3
        exact mem_marksEven_of_sv w z (sv_even_of_sband w z hz c3)
    · -- the lower `t`-band: `t ≤ L − a − T`, reflected to the upper horizontal band
      push Not at c2
      have hz' := inH_halfTurn_even (curE w) heven z hz
      have hpar : ((((curE w).num + 1 - z.1) + (2 * (curE w).num + (curE w).den - 1 - z.2)) % 2 = 0) ↔
          ((z.1 + z.2) % 2 = 0) := by omega
      have hdec : decide ((((curE w).num + 1 - z.1) +
          (2 * (curE w).num + (curE w).den - 1 - z.2)) % 2 = 0) = decide ((z.1 + z.2) % 2 = 0) :=
        decide_eq_decide.mpr hpar
      have ht' : tCo (curE w) ((curE w).num + 1 - z.1, 2 * (curE w).num + (curE w).den - 1 - z.2)
          = (curE w).den + (curE w).num - tOf (curE w) - tCo (curE w) z := by
        unfold tCo tOf
        ring
      have hta : aOf (curE w) (decide ((((curE w).num + 1 - z.1) +
          (2 * (curE w).num + (curE w).den - 1 - z.2)) % 2 = 0)) ≤ tCo (curE w)
          ((curE w).num + 1 - z.1, 2 * (curE w).num + (curE w).den - 1 - z.2) := by
        rw [hdec, ht']
        omega
      exact mem_marksEven_of_sh_refl w z (sh_even_of_tband w _ hz' hta)
  · push Not at c1
    exact mem_marksEven_of_sh w z (sh_even_of_tband w z hz c1)

end FLatticePaper.Tiles.SiteHullEven
