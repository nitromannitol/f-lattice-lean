import FLatticePaper.Tiles.StandardInstance
import FLatticePaper.Tiles.CornerPositions
import FLatticePaper.Tiles.TexVPositions

/-! The even-child copies of the standard-tile instances (`StandardInstance`): the horizontal pair with `v = -v_{n/d,2}`,
`a = -a_{n/d,2}` for the even fraction, and the vertical pair with `v = almostV1(evenBottom w)`, `a = 0`. The even word has
`hWordOf w true` (the childQ of the quad) and `vWordOf w true` (the swapped childP); the counts and the corner identity are
`vWord_even_counts` and `corner_3_family_even`. -/

namespace FLatticePaper.Tiles

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles.SiteStrings
  FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.TexVPositions

theorem even_hWord_almostPalindrome (w : FLatticePaper.Farey.Word) : IsAlmostPalindrome (hWordOf w true) :=
  (almost_palindrome_one [] w).2

theorem even_vWord_almostPalindrome (w : FLatticePaper.Farey.Word) : IsAlmostPalindrome (vWordOf w true) :=
  isAP_map_swapLetter _ (almost_palindrome_one [] (Standard.swapW w)).1

theorem vertical_B_eq_even (w : FLatticePaper.Farey.Word) :
    lastPosOf (hStringAt (hWordOf w true) 0) = almostV₁ (evenBottom w) + (-1, -1) := by
  have key : lastPosOf (hStringAt (hWordOf w true) 0) = almostV₁ (evenBottom w) - (1, 1) :=
    FLatticePaper.Tiles.CornerPositions.lastPos_hWordOf_true w
  rw [key, sub_eq_add_neg]
  rfl

theorem hlin_standard_horizontal_even (S : FLatticePaper.Tiles.SurgicalWeak.WeakData)
    (oddO evenO : FLatticePaper.Farey.Word → PartialOdometer)
    (h : FLatticePaper.Tiles.SurgicalWeak.IsWeakStdFamily S oddO evenO) (w : FLatticePaper.Farey.Word) :
    ∃ (v a : GInt) (FA P M FB : PTFamily),
      v = (-((((FLatticePaper.Farey.parentsAt w).current .even).num : ℤ) -
          ((FLatticePaper.Farey.parentsAt w).current .even).den),
        -((((FLatticePaper.Farey.parentsAt w).current .even).num : ℤ) +
          ((FLatticePaper.Farey.parentsAt w).current .even).den)) ∧
      a = (-((((FLatticePaper.Farey.parentsAt w).current .even).num : ℤ)),
        ((FLatticePaper.Farey.parentsAt w).current .even).den) ∧
      (∀ k < FA.n, ∀ x ∈ FA.dom k, (evenO w).val x = FA.odo k x) ∧
      (∀ k < FB.n, ∀ x ∈ FB.dom k, (evenO w).val (x - v) + a.1 * x.1 + a.2 * x.2 = FB.odo k x) ∧
      P.ts = FA.ts ∧ M.ts = FB.ts ∧
      FA.ts = hStringAt (hWordOf w true) 0 ∧ P.ts = hStringAt (hWordOf w true) (0, 0) ∧
      M.ts = hRevStringAt (hWordOf w true).reverse (1, -2) ∧
      FA.Respects Orientation.horizontal false ∧ FB.Respects Orientation.horizontal true ∧
      P.Respects Orientation.horizontal false ∧ M.Respects Orientation.horizontal true ∧
      WithinCommon P ∧ WithinCommon M ∧ CrossCommon P M ∧
      P.a 0 - M.a 0 = (0, -1) ∧
      (∀ (α γ : GInt) (β δ : ℤ),
        (∀ k < P.n, ∀ x : GInt, FA.odo k x = P.odo k x + α.1 * x.1 + α.2 * x.2 + β) →
        (∀ j < M.n, ∀ x : GInt, FB.odo j x = M.odo j x + γ.1 * x.1 + γ.2 * x.2 + δ) →
        α = γ) := by
  obtain ⟨-, hA, hC, -, -⟩ := (h w).2.2.2.2.2
  obtain ⟨FA, hFAts, hFA, hFAR⟩ := hA
  obtain ⟨G, hGts, hGS, hGR⟩ := hC
  obtain ⟨num, hnum⟩ : ∃ n : ℤ, n = ((FLatticePaper.Farey.parentsAt w).current .even).num := ⟨_, rfl⟩
  obtain ⟨den, hden⟩ : ∃ d : ℤ, d = ((FLatticePaper.Farey.parentsAt w).current .even).den := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : GInt, v = (-(num - den), -(num + den)) := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : GInt, a = (-num, den) := ⟨_, rfl⟩
  have hhead : (hWordOf w true).head? = some Letter.q := (hWordOf_head_last w true).1
  have hlast : (hWordOf w true).getLast? = some Letter.p := (hWordOf_head_last w true).2
  have hvh : (vWordOf w true).head? = some Letter.p := (StringCorners.vWord_even_head_last w).1
  have hvl : (vWordOf w true).getLast? = some Letter.q := (StringCorners.vWord_even_head_last w).2
  have hcnt := StringCorners.vWord_even_counts w
  have hq : (((vWordOf w true).count Letter.q : ℕ) : ℤ) = num := by
    rw [hnum]
    exact_mod_cast hcnt.2
  have hlenZ : (((vWordOf w true).length : ℕ) : ℤ) = den := by
    rw [hden]
    have hl := length_eq_counts (vWordOf w true)
    have h1 : (((vWordOf w true).length : ℕ) : ℤ) =
        (((vWordOf w true).count Letter.p : ℕ) : ℤ) + (((vWordOf w true).count Letter.q : ℕ) : ℤ) := by
      exact_mod_cast hl
    rw [h1]
    have hp : (((vWordOf w true).count Letter.p : ℕ) : ℤ) =
        ((FLatticePaper.Farey.parentsAt w).current .even).den -
          ((FLatticePaper.Farey.parentsAt w).current .even).num := hcnt.1
    rw [hp, hq, ← hnum]
    ring
  obtain ⟨P, M, hPts, hMts, hPR, hMR, hWP, hWM, hCr, hPa⟩ :=
    horizontalMoreover_proof (hWordOf w true) (even_hWord_almostPalindrome w) hhead hlast
  obtain ⟨FB, hFB⟩ : ∃ F : PTFamily, F = (G.translate v).affineAdd a 0 := ⟨_, rfl⟩
  have hFBn : FB.n = G.n := by
    rw [hFB, PTFamily.affineAdd_n, PTFamily.translate_n]
  have hFBdom : ∀ k, k < G.n → FB.dom k = (G.dom k).map (· + v) := by
    intro k hk
    rw [hFB, PTFamily.affineAdd_dom, PTFamily.translate_dom _ _ k hk]
  have hFBodo : ∀ k, k < G.n → ∀ x : GInt,
      FB.odo k x = G.odo k (x - v) + a.1 * x.1 + a.2 * x.2 + 0 := by
    intro k hk x
    rw [hFB, PTFamily.affineAdd_odo, PTFamily.translate_odo _ _ k hk]
  have hFBts : FB.ts = hRevStringAt (hWordOf w true).reverse (1, -2) := by
    have hpos : lastPosOf (vRevStringAt (vWordOf w true).reverse 0) = (1 + num - den, num + den - 2) := by
      rw [vRev_last_top (vWordOf w true) hvh hvl, hq, hlenZ]
    have hsum : (1 + num - den, num + den - 2) + v = (1, -2) := by
      rw [hv]
      apply Prod.ext
      · simp only [Prod.fst_add]
        ring
      · simp only [Prod.snd_add]
        ring
    have e1 : FB.ts = G.ts.map (fun p => (p.1, p.2 + v)) := by
      rw [hFB]
      rfl
    rw [e1, hGts, hpos, ← hRevStringAt_add, hsum]
  have hFBR : FB.Respects Orientation.horizontal true := by
    rw [hFB]
    exact PTFamily.affineAdd_respects _ _ _ _ _ (PTFamily.translate_respects G _ _ v hGR)
  have hFB' : ∀ k < FB.n, ∀ x ∈ FB.dom k,
      (evenO w).val (x - v) + a.1 * x.1 + a.2 * x.2 = FB.odo k x := by
    intro k hk x hx
    have hkG : k < G.n := by rw [← hFBn]; exact hk
    rw [hFBdom k hkG] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    rw [hFBodo k hkG, add_sub_cancel_right, hGS k hkG y hy]
    ring
  have htsP : P.ts = FA.ts := by
    rw [hPts, hFAts]
    exact zoForwardE_eq_hStringAt _
  have htsM : M.ts = FB.ts := by
    rw [hMts, zoReversedStackedE_eq, hFBts]
  have hPts0 : P.ts = hStringAt (hWordOf w true) (0, 0) := by
    rw [hPts]
    exact zoForwardE_eq_hStringAt _
  have hMts0 : M.ts = hRevStringAt (hWordOf w true).reverse (1, -2) := by
    rw [hMts]
    exact zoReversedStackedE_eq _
  have hC3 : tileAffine (evenO w).val (cornerTiles (hWordOf w true) (vWordOf w true) 0).2.2.1 -
      tileAffine (evenO w).val (cornerTiles (hWordOf w true) (vWordOf w true) 0).2.1 =
      ((num : ℚ) - 1, 1 - (den : ℚ)) := by
    rw [corner_3_family_even S oddO evenO h w, hnum, hden]
  refine ⟨v, a, FA, P, M, FB, (by rw [hv, hnum, hden]), (by rw [ha, hnum, hden]), hFA,
    hFB', htsP, htsM, hFAts, hPts0, hMts0, hFAR, hFBR, hPR, hMR, hWP, hWM, hCr, hPa, ?_⟩
  intro α γ β δ hα hγ
  exact hlin_horizontal (evenO w).val (hWordOf w true) (vWordOf w true) num den v a hhead hlast hvh hvl
    (by rw [hq]) (by rw [hlenZ]) (by rw [hv]) (by rw [ha]) FA P M FB hFA hFB' hPts htsP htsM hMts
    hFAR hFBR hPa hC3 α γ β δ hα hγ

/-- The vertical instance for the even standard tile: the right side of the even tile and the left side of its translate by
`v = almostV1 (evenBottom w)`, both carried by the vertical Moreover families translated by `B`. -/
theorem vlin_standard_vertical_even (S : FLatticePaper.Tiles.SurgicalWeak.WeakData)
    (oddO evenO : FLatticePaper.Farey.Word → PartialOdometer)
    (h : FLatticePaper.Tiles.SurgicalWeak.IsWeakStdFamily S oddO evenO) (w : FLatticePaper.Farey.Word) :
    ∃ (FA P M FB : PTFamily),
      (∀ k < FA.n, ∀ x ∈ FA.dom k, (evenO w).val x = FA.odo k x) ∧
      (∀ k < FB.n, ∀ x ∈ FB.dom k, (evenO w).val (x - almostV₁ (evenBottom w)) = FB.odo k x) ∧
      P.ts = FA.ts ∧ M.ts = FB.ts ∧ P.a 0 = M.a 0 ∧
      FA.ts = vStringAt (vWordOf w true) (lastPosOf (hStringAt (hWordOf w true) 0)) ∧
      FB.ts = vRevStringAt (vWordOf w true).reverse (almostV₁ (evenBottom w)) ∧
      FA.Respects Orientation.vertical false ∧ P.Respects Orientation.vertical false ∧
      FB.Respects Orientation.vertical true ∧ M.Respects Orientation.vertical true ∧
      WithinCommon P ∧ WithinCommon M ∧ CrossCommon P M ∧
      (∀ (α γ : GInt) (β δ : ℤ),
        (∀ k < P.n, ∀ x : GInt, FA.odo k x = P.odo k x + α.1 * x.1 + α.2 * x.2 + β) →
        (∀ j < M.n, ∀ x : GInt, FB.odo j x = M.odo j x + γ.1 * x.1 + γ.2 * x.2 + δ) →
        α = γ) := by
  obtain ⟨-, hA, -, hVr, hVf⟩ := (h w).2.2.2.2.2
  obtain ⟨FA, hFAts, hFA, hFAR⟩ := hVf
  obtain ⟨G, hGts, hGS, hGR⟩ := hVr
  have hvh : (vWordOf w true).head? = some Letter.p := (StringCorners.vWord_even_head_last w).1
  have hvl : (vWordOf w true).getLast? = some Letter.q := (StringCorners.vWord_even_head_last w).2
  have hhead : (hWordOf w true).head? = some Letter.q := (hWordOf_head_last w true).1
  have hlast : (hWordOf w true).getLast? = some Letter.p := (hWordOf_head_last w true).2
  obtain ⟨P0, M0, hP0ts, hM0ts, hP0R, hM0R, hW0P, hW0M, hC0, hPM0⟩ :=
    verticalMoreover_proof (vWordOf w true) (even_vWord_almostPalindrome w) hvh hvl
  obtain ⟨B, hB⟩ : ∃ B : GInt, B = lastPosOf (hStringAt (hWordOf w true) 0) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : GInt, v = almostV₁ (evenBottom w) := ⟨_, rfl⟩
  have hBv : B = v + (-1, -1) := by
    rw [hB, hv]
    exact vertical_B_eq_even w
  obtain ⟨P, hP⟩ : ∃ P : PTFamily, P = P0.translate B := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : PTFamily, M = M0.translate B := ⟨_, rfl⟩
  obtain ⟨FB, hFBdef⟩ : ∃ F : PTFamily, F = G.translate v := ⟨_, rfl⟩
  have hPts : P.ts = vStringAt (vWordOf w true) B := by
    rw [hP]
    show P0.ts.map (fun p => (p.1, p.2 + B)) = _
    rw [hP0ts, zoForwardV_eq, ← vStringAt_add, zero_add]
  have htsP : P.ts = FA.ts := by
    rw [hPts, hFAts, hB]
  have hMts' : M.ts = vRevStringAt (vWordOf w true).reverse ((1, 1) + B) := by
    rw [hM]
    show M0.ts.map (fun p => (p.1, p.2 + B)) = _
    rw [hM0ts, zoReversedStackedV_eq, ← vRevStringAt_add]
  have hFBts : FB.ts = vRevStringAt (vWordOf w true).reverse v := by
    rw [hFBdef]
    show G.ts.map (fun p => (p.1, p.2 + v)) = _
    rw [hGts, ← vRevStringAt_add, zero_add]
  have hsh : (1, 1) + (v + (-1, -1)) = v := by
    apply Prod.ext
    · show (1 : ℤ) + (v.1 + -1) = v.1
      omega
    · show (1 : ℤ) + (v.2 + -1) = v.2
      omega
  have htsM : M.ts = FB.ts := by
    rw [hMts', hFBts, hBv, hsh]
  have hFB' : ∀ k < FB.n, ∀ x ∈ FB.dom k, (evenO w).val (x - v) = FB.odo k x := by
    intro k hk x hx
    have hkG : k < G.n := by
      rw [hFBdef, PTFamily.translate_n] at hk
      exact hk
    rw [hFBdef, PTFamily.translate_dom _ _ k hkG] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    rw [hFBdef, PTFamily.translate_odo _ _ k hkG, add_sub_cancel_right]
    exact hGS k hkG y hy
  have hPM : P.a 0 = M.a 0 := by
    rw [hP, hM]
    exact hPM0
  have hBv' : lastPosOf (hStringAt (hWordOf w true) 0) = v + (-1, -1) := by
    rw [← hB]
    exact hBv
  refine ⟨FA, P, M, FB, hFA, (by rw [← hv]; exact hFB'), htsP, htsM, hPM, hFAts,
    (by rw [hFBts, hv]), hFAR,
    (by rw [hP]; exact PTFamily.translate_respects _ _ _ _ hP0R),
    (by rw [hFBdef]; exact PTFamily.translate_respects _ _ _ _ hGR),
    (by rw [hM]; exact PTFamily.translate_respects _ _ _ _ hM0R),
    (by rw [hP]; exact PTFamily.translate_within _ _ hW0P),
    (by rw [hM]; exact PTFamily.translate_within _ _ hW0M),
    (by rw [hP, hM]; exact crossCommon_translate P0 M0 B hC0), ?_⟩
  intro α γ β δ hα hγ
  exact vlin_vertical (evenO w).val (hWordOf w true) (vWordOf w true) v hhead hlast hvh hvl hBv' hA
    FA P M FB hFA hFB' hFAts htsP htsM hFBts hPM α γ β δ hα hγ

end FLatticePaper.Tiles
