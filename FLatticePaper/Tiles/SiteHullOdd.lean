import FLatticePaper.Tiles.SiteHull
import FLatticePaper.Tiles.SiteVertWord
import FLatticePaper.Tiles.SiteVertCover
import FLatticePaper.Tiles.SiteFwdCover
import FLatticePaper.Tiles.SiteScope
import FLatticePaper.Tiles.SiteLowLeft
import FLatticePaper.Tiles.SiteInduction
import FLatticePaper.Tiles.StandardHalfTurn

/-! Task 53, item 4 (the hull of the odd tile): the words and the parameters of the odd standard tile of `w`.

For `w` non-base, `n = (curO w).num`, `d = (curO w).den` satisfy `0 < n < d`, `n + d` odd (`Fraction.Odd`); the forward word
`hWordOf w false` is a ceiling word of slope `2n/(d+n)`; the reversed vertical word `vWordOf w false` (reversed) is a ceiling word
of slope `n/d`, from `ceil_rev_comp` applied to the child word of the swapped word, whose even current fraction is the rotation of `curO w`
(`parentsAt_swapW` and `rotate_current_odd`). -/

namespace FLatticePaper.Tiles.SiteHullOdd

open FLatticePaper FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.Standard FLatticePaper.Tiles.CeilWords
  FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.SiteScope
  FLatticePaper.Tiles.SiteFwdLink FLatticePaper.Tiles.SiteFwdCover FLatticePaper.Tiles.SiteVertLink
  FLatticePaper.Tiles.SiteVertCover FLatticePaper.Tiles.SiteVertWord FLatticePaper.Tiles.StandardHalfTurn
  FLatticePaper.Tiles.SiteHull FLatticePaper.Tiles.SiteLowLeft FLatticePaper.Tiles.SiteUnique

theorem curO_pos_lt (w : Word) : 0 < (curO w).num ∧ (curO w).num < (curO w).den := by
  obtain ⟨h1, h2, h3, h4⟩ := parents_bounds w
  unfold curO Parents.current Parents.combine
  simp only [one_mul]
  constructor <;> omega

theorem head_q_of_ceil (ℓ : BinaryWord) (k l : ℤ) (hC : CeilWord ℓ k l) (hk : 0 < k) (hkl : k < l) :
    ∃ ℓ' : BinaryWord, ℓ = Letter.q :: ℓ' := by
  obtain ⟨hlen, hbd⟩ := hC
  cases ℓ with
  | nil => simp at hlen; omega
  | cons c ℓ' =>
    cases c with
    | q => exact ⟨ℓ', rfl⟩
    | p =>
      exfalso
      obtain ⟨-, h2⟩ := hbd 1 (by omega)
      have hq : qPrefix (Letter.p :: ℓ') 1 = 0 := by simp [qPrefix, List.take_succ_cons]
      rw [hq] at h2
      push_cast at h2
      omega

theorem cursorB_of_ceil (ℓ : BinaryWord) (n d : ℤ) (hC : CeilWord ℓ (2 * n) (d + n)) : CursorB ℓ n d := by
  intro j hj
  have hj' : (j : ℤ) ≤ d + n := by have := hC.1; omega
  obtain ⟨h1, h2⟩ := hC.2 j hj'
  constructor <;> linarith [h1, h2]

theorem cursorV_of_ceil (ℓ : BinaryWord) (n d : ℤ) (hC : CeilWord ℓ n d) : CursorV ℓ n d := by
  intro j hj
  have hj' : (j : ℤ) ≤ d := by have := hC.1; omega
  obtain ⟨h1, h2⟩ := hC.2 j hj'
  constructor <;> linarith [h1, h2]

/-- The even current fraction of the swapped word is the rotation of the odd current fraction. -/
theorem curE_swapW (w : Word) : (parentsAt (swapW w)).current .even = (curO w).rotate := by
  rw [parentsAt_swapW]
  exact ((parentsAt_valid w).rotate_current_odd).symm

theorem curO_odd (w : Word) : Fraction.Odd (curO w) := (parentsAt_valid w).current_odd_parity

/-- The parity data of the bounds `a`, `l` of `H_f` at a site `z`. -/
theorem site_ab (f : Fraction) (z : ℤ × ℤ) :
    ((z.1 + z.2) % 2 = 1 → aOf f (decide ((z.1 + z.2) % 2 = 0)) = f.num ∧
        lOf f (decide ((z.1 + z.2) % 2 = 0)) = min (f.den - f.num) (3 * f.num - f.den)) ∧
      ((z.1 + z.2) % 2 = 0 → aOf f (decide ((z.1 + z.2) % 2 = 0)) = min (2 * f.num) (f.den - f.num) ∧
        lOf f (decide ((z.1 + z.2) % 2 = 0)) = 0) := by
  constructor
  · intro h
    have h0 : ¬ ((z.1 + z.2) % 2 = 0) := by omega
    simp [aOf, lOf, h0]
  · intro h
    simp [aOf, lOf, h]

/-- The forward word of the odd tile is a ceiling word of slope `2n/(d+n)`. -/
theorem cw_childP (w : Word) :
    CeilWord (hWordOf w false) (2 * (curO w).num) ((curO w).den + (curO w).num) := by
  obtain ⟨c1, -, -, -⟩ := quadInv_all w
  simp only [hWordOf]
  exact c1

/-- The child word of the swapped word has slope `(d − n)/d`. -/
theorem cw_childQ_swap (w : Word) :
    CeilWord (quadAt [] (swapW w)).childQ ((curO w).den - (curO w).num) (curO w).den := by
  obtain ⟨-, c2, -, -⟩ := quadInv_all (swapW w)
  have h := c2
  rw [curE_swapW, Fraction.rotate_of_odd (curO_odd w)] at h
  unfold CeilOf sEven at h
  have e2 : ((curO w).den + (curO w).num + ((curO w).den - (curO w).num)) / 2 = (curO w).den := by omega
  rw [e2] at h
  exact h

/-- The vertical word, reversed, is a ceiling word of slope `n/d`. -/
theorem cw_vert (w : Word) : CeilWord (vWordOf w false).reverse (curO w).num (curO w).den := by
  have h3 := ceil_rev_comp (quadAt [] (swapW w)).childQ _ _ (cw_childQ_swap w) (by have := curO_pos_lt w; omega)
  have hv : vWordOf w false = (quadAt [] (swapW w)).childQ.map swapLetter := by simp [vWordOf]
  rw [hv]
  have e3 : (curO w).den - ((curO w).den - (curO w).num) = (curO w).num := by ring
  rw [e3] at h3
  exact h3

/-- **The forward band is in the forward marks.** A site of `H_{curO w}` with `a ≤ t` is in the forward string of `hWordOf w false`. -/
theorem sh_of_tband (w : Word) (z : ℤ × ℤ) (hz : InH (curO w) z)
    (hta : aOf (curO w) (decide ((z.1 + z.2) % 2 = 0)) ≤ tCo (curO w) z) :
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
  exact tband_stringSites (curO w).num (curO w).den 2 ℓ' (by omega) (by omega) hB hlen (fun _ => rfl)
    (fun h => by omega) z.1 z.2 (tCo (curO w) z) (sCo (curO w) z) (aOf (curO w) (decide ((z.1 + z.2) % 2 = 0)))
    (lOf (curO w) (decide ((z.1 + z.2) % 2 = 0))) rfl rfl (site_ab (curO w) z) hta hz2 hz3
    (by unfold tOf at hz4; exact hz4)

/-- **The vertical band is in the vertical marks.** A site of `H_{curO w}` with `s ≤ N − l` has `(z₁ + 1, z₂ + 1)` in the vertical
string of `(vWordOf w false).reverse`. -/
theorem sv_of_sband (w : Word) (z : ℤ × ℤ) (hz : InH (curO w) z)
    (hsb : sCo (curO w) z ≤ 2 * (curO w).num - lOf (curO w) (decide ((z.1 + z.2) % 2 = 0))) :
    (z.1 + 1, z.2 + 1) ∈ stringSites true true (vWordOf w false).reverse := by
  have hpos := curO_pos_lt w
  have hodd : ((curO w).num + (curO w).den) % 2 = 1 := curO_odd w
  obtain ⟨ℓ'', hℓ⟩ := head_q_of_ceil _ _ _ (cw_vert w) (by omega) (by omega)
  have hC := cw_vert w
  rw [hℓ] at hC ⊢
  have hV := cursorV_of_ceil _ _ _ hC
  obtain ⟨hz1, hz2, hz3, -⟩ := hz
  exact vband_stringSites (curO w).num (curO w).den z.1 z.2 (tCo (curO w) z) (sCo (curO w) z)
    (aOf (curO w) (decide ((z.1 + z.2) % 2 = 0))) (lOf (curO w) (decide ((z.1 + z.2) % 2 = 0))) ℓ''
    (by omega) (by omega) (by omega) hV hC.1 rfl rfl (site_ab (curO w) z)
    (by unfold tOf at hz1; exact hz1) hz2 hz3 hsb

/-- **The half-turn centre of the odd tile** is `R = (d + n + 1, 3n + d − 1)`. -/
theorem centre_odd (w : Word) :
    halfTurnCentre (oddTile w) = ((curO w).den + (curO w).num + 1, 3 * (curO w).num + (curO w).den - 1) := by
  have hv : tF ((parentsAt (swapW w)).current .even) + mulI (tF ((parentsAt w).current .odd)) =
      (-((curO w).den + (curO w).num + 1), 1 - 3 * (curO w).num - (curO w).den) := by
    rw [curE_swapW, Fraction.rotate_of_odd (curO_odd w)]
    apply Prod.ext
    · simp [tF, tV, mulI, curO]
      ring
    · simp [tF, tV, mulI, curO]
      ring
  have hsym : ∀ z ∈ oddTile w,
      ((curO w).den + (curO w).num + 1 - z.1, 3 * (curO w).num + (curO w).den - 1 - z.2) ∈ oddTile w := by
    intro z hz
    have hx : ((-z.1, -z.2) : ℤ × ℤ) ∈ rot (rot (oddTile w)) := by
      apply mem_rot.mpr
      apply mem_rot.mpr
      simpa using hz
    rw [rot_rot_oddTile w, mem_shift, hv] at hx
    have e : ((curO w).den + (curO w).num + 1 - z.1, 3 * (curO w).num + (curO w).den - 1 - z.2) =
        ((-z.1, -z.2) : ℤ × ℤ) - (-((curO w).den + (curO w).num + 1), 1 - 3 * (curO w).num - (curO w).den) := by
      apply Prod.ext
      · simp only [Prod.fst_sub]
        ring
      · simp only [Prod.snd_sub]
        ring
    rw [e]
    exact hx
  exact halfTurnCentre_of_symm (oddTile w) _ ⟨0, (standard_tiles_normalised w).1.1⟩ hsym

/-- A forward site of the odd tile is a mark. -/
theorem mem_marksOdd_of_sh (w : Word) (z : ℤ × ℤ) (h : z ∈ stringSites false false (hWordOf w false)) :
    z ∈ marksOdd w := by
  have hc := lowLeft_oddTile w
  have hz : z ∈ (stringSites false false (hWordOf w false)).map
      (fun z => (z.1 + (lowLeft (oddTile w)).1, z.2 + (lowLeft (oddTile w)).2)) :=
    List.mem_map.mpr ⟨z, h, by rw [hc]; simp⟩
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hz))

/-- A vertical site (shifted by `(1,1)`) is a mark. -/
theorem mem_marksOdd_of_sv (w : Word) (z : ℤ × ℤ)
    (h : (z.1 + 1, z.2 + 1) ∈ stringSites true true (vWordOf w false).reverse) : z ∈ marksOdd w := by
  have hc := lowLeft_oddTile w
  have hz : z ∈ (stringSites true true (vWordOf w false).reverse).map
      (fun z => (z.1 + (lowLeft (oddTile w)).1 - 1, z.2 + (lowLeft (oddTile w)).2 - 1)) :=
    List.mem_map.mpr ⟨(z.1 + 1, z.2 + 1), h, by rw [hc]; simp⟩
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hz))

/-- A reflected forward site is a mark: `z` is the half-turn of the forward site `R − z`. -/
theorem mem_marksOdd_of_sh_refl (w : Word) (z : ℤ × ℤ)
    (h : ((curO w).den + (curO w).num + 1 - z.1, 3 * (curO w).num + (curO w).den - 1 - z.2) ∈
      stringSites false false (hWordOf w false)) : z ∈ marksOdd w := by
  have hc := lowLeft_oddTile w
  have hA : ((curO w).den + (curO w).num + 1 - z.1, 3 * (curO w).num + (curO w).den - 1 - z.2) ∈
      (stringSites false false (hWordOf w false)).map
        (fun z => (z.1 + (lowLeft (oddTile w)).1, z.2 + (lowLeft (oddTile w)).2)) :=
    List.mem_map.mpr ⟨_, h, by rw [hc]; simp⟩
  have hz : z ∈ ((stringSites false false (hWordOf w false)).map
      (fun z => (z.1 + (lowLeft (oddTile w)).1, z.2 + (lowLeft (oddTile w)).2))).map
        (halfTurn (oddTile w)) :=
    List.mem_map.mpr ⟨_, hA, by
      rw [halfTurn, centre_odd]
      simp⟩
  exact List.mem_append_left _ (List.mem_append_right _ hz)

/-- A reflected vertical site is a mark. -/
theorem mem_marksOdd_of_sv_refl (w : Word) (z : ℤ × ℤ)
    (h : ((curO w).den + (curO w).num + 1 - z.1 + 1, 3 * (curO w).num + (curO w).den - 1 - z.2 + 1) ∈
      stringSites true true (vWordOf w false).reverse) : z ∈ marksOdd w := by
  have hc := lowLeft_oddTile w
  have hA : ((curO w).den + (curO w).num + 1 - z.1, 3 * (curO w).num + (curO w).den - 1 - z.2) ∈
      (stringSites true true (vWordOf w false).reverse).map
        (fun z => (z.1 + (lowLeft (oddTile w)).1 - 1, z.2 + (lowLeft (oddTile w)).2 - 1)) :=
    List.mem_map.mpr ⟨_, h, by rw [hc]; simp⟩
  have hz : z ∈ ((stringSites true true (vWordOf w false).reverse).map
      (fun z => (z.1 + (lowLeft (oddTile w)).1 - 1, z.2 + (lowLeft (oddTile w)).2 - 1))).map
        (halfTurn (oddTile w)) :=
    List.mem_map.mpr ⟨_, hA, by
      rw [halfTurn, centre_odd]
      simp⟩
  exact List.mem_append_right _ hz

/-- **The hull of the odd tile.** A site of `H_{curO w}` that is not the unique representative of its class is a marked site. -/
theorem hull_odd (w : Word) (z : ℤ × ℤ) (hz : InH (curO w) z)
    (hnu : ¬ UniqueIn (curO w) z) : z ∈ marksOdd w := by
  have hpos := curO_pos_lt w
  have hodd : ((curO w).num + (curO w).den) % 2 = 1 := curO_odd w
  have hμ : muOf (curO w) = 2 := by
    unfold muOf
    rw [if_pos hodd]
  by_cases c1 : tCo (curO w) z < aOf (curO w) (decide ((z.1 + z.2) % 2 = 0))
  · by_cases c2 : (curO w).den + (curO w).num - aOf (curO w) (decide ((z.1 + z.2) % 2 = 0)) - tOf (curO w)
        < tCo (curO w) z
    · by_cases c3 : 2 * (curO w).num - lOf (curO w) (decide ((z.1 + z.2) % 2 = 0)) < sCo (curO w) z
      · by_cases c4 : sCo (curO w) z < lOf (curO w) (decide ((z.1 + z.2) % 2 = 0)) + muOf (curO w) * tOf (curO w)
        · exact absurd (unique_of_bounds (curO w) hpos.1 hpos.2 z hz c1 c2 c3 c4) hnu
        · -- the upper `s`-band: `s ≥ l + μT`, reflected to the lower vertical band
          push Not at c4
          rw [hμ] at c4
          have hz' := inH_halfTurn (curO w) hodd z hz
          have hpar : ((((curO w).den + (curO w).num + 1 - z.1) + (3 * (curO w).num + (curO w).den - 1 - z.2)) % 2 = 0) ↔
              ((z.1 + z.2) % 2 = 0) := by omega
          have hdec : decide ((((curO w).den + (curO w).num + 1 - z.1) +
              (3 * (curO w).num + (curO w).den - 1 - z.2)) % 2 = 0) = decide ((z.1 + z.2) % 2 = 0) :=
            decide_eq_decide.mpr hpar
          have hS : sCo (curO w) ((curO w).den + (curO w).num + 1 - z.1, 3 * (curO w).num + (curO w).den - 1 - z.2)
              = 2 * tOf (curO w) + 2 * (curO w).num - sCo (curO w) z := by
            unfold sCo tOf
            ring
          have hsb : sCo (curO w) ((curO w).den + (curO w).num + 1 - z.1, 3 * (curO w).num + (curO w).den - 1 - z.2)
              ≤ 2 * (curO w).num - lOf (curO w) (decide ((((curO w).den + (curO w).num + 1 - z.1) +
                (3 * (curO w).num + (curO w).den - 1 - z.2)) % 2 = 0)) := by
            rw [hdec, hS]
            omega
          exact mem_marksOdd_of_sv_refl w z (sv_of_sband w _ hz' hsb)
      · push Not at c3
        exact mem_marksOdd_of_sv w z (sv_of_sband w z hz c3)
    · -- the lower `t`-band: `t ≤ L − a − T`, reflected to the upper horizontal band
      push Not at c2
      have hz' := inH_halfTurn (curO w) hodd z hz
      have hpar : ((((curO w).den + (curO w).num + 1 - z.1) + (3 * (curO w).num + (curO w).den - 1 - z.2)) % 2 = 0) ↔
          ((z.1 + z.2) % 2 = 0) := by omega
      have hdec : decide ((((curO w).den + (curO w).num + 1 - z.1) +
          (3 * (curO w).num + (curO w).den - 1 - z.2)) % 2 = 0) = decide ((z.1 + z.2) % 2 = 0) :=
        decide_eq_decide.mpr hpar
      have ht' : tCo (curO w) ((curO w).den + (curO w).num + 1 - z.1, 3 * (curO w).num + (curO w).den - 1 - z.2)
          = (curO w).den + (curO w).num - tOf (curO w) - tCo (curO w) z := by
        unfold tCo tOf
        ring
      have hta : aOf (curO w) (decide ((((curO w).den + (curO w).num + 1 - z.1) +
          (3 * (curO w).num + (curO w).den - 1 - z.2)) % 2 = 0)) ≤ tCo (curO w)
          ((curO w).den + (curO w).num + 1 - z.1, 3 * (curO w).num + (curO w).den - 1 - z.2) := by
        rw [hdec, ht']
        omega
      exact mem_marksOdd_of_sh_refl w z (sh_of_tband w _ hz' hta)
  · push Not at c1
    exact mem_marksOdd_of_sh w z (sh_of_tband w z hz c1)

end FLatticePaper.Tiles.SiteHullOdd
