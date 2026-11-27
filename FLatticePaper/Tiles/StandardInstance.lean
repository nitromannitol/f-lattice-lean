import FLatticePaper.Tiles.HLinHorizontal
import FLatticePaper.Tiles.VLinVertical
import FLatticePaper.Tiles.VerticalIdentities
import FLatticePaper.Tiles.HorizontalEnlargedCross
import FLatticePaper.Tiles.VerticalMoreoverProof
import FLatticePaper.Tiles.SurgicalCornerThird
import FLatticePaper.Tiles.SurgicalWeakOdometers

/-! The linear hypotheses of the standard tile, from the surgical odometer `(oddO w).val`.

* The almost-palindrome conditions of both Moreover halves hold for the standard words (`almost_palindrome_one`).
* `hlin_standard_horizontal`: the horizontal pair, with `v = -v_{n/d,2}`, `a = -a_{n/d,2}`, and `hC3` from `corner_3_family`.
* `vlin_standard_vertical`: the vertical pair, with `v = v_{n/d,1}`, `a = 0`, both translates carried by the Moreover families. -/

namespace FLatticePaper.Tiles

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles.SiteStrings
  FLatticePaper.Tiles.StandardBoundary

theorem isAP_map_swapLetter (l : BinaryWord) (h : IsAlmostPalindrome l) :
    IsAlmostPalindrome (l.map swapLetter) := by
  obtain ⟨f, la, m, hm, hl⟩ := h
  refine ⟨swapLetter f, swapLetter la, m.map swapLetter, ?_, ?_⟩
  · rw [← List.map_reverse, hm]
  · rw [hl]
    simp [List.map_append]

theorem standard_hWord_almostPalindrome (w : FLatticePaper.Farey.Word) :
    IsAlmostPalindrome (hWordOf w false) :=
  (almost_palindrome_one [] w).1

theorem standard_vWord_almostPalindrome (w : FLatticePaper.Farey.Word) :
    IsAlmostPalindrome (vWordOf w false) :=
  isAP_map_swapLetter _ (almost_palindrome_one [] (Standard.swapW w)).2

theorem hlin_standard_horizontal (S : FLatticePaper.Tiles.SurgicalWeak.WeakData)
    (oddO evenO : FLatticePaper.Farey.Word → PartialOdometer)
    (h : FLatticePaper.Tiles.SurgicalWeak.IsWeakStdFamily S oddO evenO) (w : FLatticePaper.Farey.Word) :
    ∃ (v a : GInt) (FA P M FB : PTFamily),
      v = (-((((FLatticePaper.Farey.parentsAt w).current .odd).num : ℤ) -
          ((FLatticePaper.Farey.parentsAt w).current .odd).den),
        -((((FLatticePaper.Farey.parentsAt w).current .odd).num : ℤ) +
          ((FLatticePaper.Farey.parentsAt w).current .odd).den)) ∧
      a = (-((((FLatticePaper.Farey.parentsAt w).current .odd).num : ℤ)),
        ((FLatticePaper.Farey.parentsAt w).current .odd).den) ∧
      (∀ k < FA.n, ∀ x ∈ FA.dom k, (oddO w).val x = FA.odo k x) ∧
      (∀ k < FB.n, ∀ x ∈ FB.dom k, (oddO w).val (x - v) + a.1 * x.1 + a.2 * x.2 = FB.odo k x) ∧
      P.ts = FA.ts ∧ M.ts = FB.ts ∧
      FA.Respects Orientation.horizontal false ∧ FB.Respects Orientation.horizontal true ∧
      P.a 0 - M.a 0 = (0, -1) ∧
      (∀ (α γ : GInt) (β δ : ℤ),
        (∀ k < P.n, ∀ x : GInt, FA.odo k x = P.odo k x + α.1 * x.1 + α.2 * x.2 + β) →
        (∀ j < M.n, ∀ x : GInt, FB.odo j x = M.odo j x + γ.1 * x.1 + γ.2 * x.2 + δ) →
        α = γ) := by
  obtain ⟨-, hA, hC, -, -⟩ := (h w).2.2.2.2.1
  obtain ⟨FA, hFAts, hFA, hFAR⟩ := hA
  obtain ⟨G, hGts, hGS, hGR⟩ := hC
  obtain ⟨num, hnum⟩ : ∃ n : ℤ, n = ((FLatticePaper.Farey.parentsAt w).current .odd).num := ⟨_, rfl⟩
  obtain ⟨den, hden⟩ : ∃ d : ℤ, d = ((FLatticePaper.Farey.parentsAt w).current .odd).den :=
    ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : GInt, v = (-(num - den), -(num + den)) := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : GInt, a = (-num, den) := ⟨_, rfl⟩
  have hhead : (hWordOf w false).head? = some Letter.q := (hWordOf_head_last w false).1
  have hlast : (hWordOf w false).getLast? = some Letter.p := (hWordOf_head_last w false).2
  have hvw : vWordOf w false = vertWord w := rfl
  have hvh : (vWordOf w false).head? = some Letter.p := by
    rw [hvw]
    exact (StringCorners.vertWord_head_last w).1
  have hvl : (vWordOf w false).getLast? = some Letter.q := by
    rw [hvw]
    exact (StringCorners.vertWord_head_last w).2
  -- the counts of the vertical word
  have hcnt := vertWord_counts w
  have hq : (((vWordOf w false).count Letter.q : ℕ) : ℤ) = num := by
    rw [hvw, hnum]
    exact_mod_cast hcnt.2
  have hlenZ : (((vWordOf w false).length : ℕ) : ℤ) = den := by
    rw [hvw, hden]
    have hl := length_eq_counts (vertWord w)
    have h1 : (((vertWord w).length : ℕ) : ℤ) =
        (((vertWord w).count Letter.p : ℕ) : ℤ) + (((vertWord w).count Letter.q : ℕ) : ℤ) := by
      exact_mod_cast hl
    rw [h1, hcnt.1, hcnt.2]
    ring
  -- the horizontal Moreover pair
  obtain ⟨P, M, hPts, hMts, hPR, hMR, -, -, -, hPa⟩ :=
    horizontalMoreover_proof (hWordOf w false) (standard_hWord_almostPalindrome w) hhead hlast
  -- the translate `FB` of `G` by `v`, with the affine factor `a`
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
  have hFBts : FB.ts = hRevStringAt (hWordOf w false).reverse (1, -2) := by
    have hpos : lastPosOf (vRevStringAt (vWordOf w false).reverse 0) = (1 + num - den, num + den - 2) := by
      rw [vRev_last_top (vWordOf w false) hvh hvl, hq, hlenZ]
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
      (oddO w).val (x - v) + a.1 * x.1 + a.2 * x.2 = FB.odo k x := by
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
  have hFAodo : ∀ k < FA.n, ∀ x ∈ FA.dom k, (oddO w).val x = FA.odo k x := hFA
  have hC3 : tileAffine (oddO w).val (cornerTiles (hWordOf w false) (vWordOf w false) 0).2.2.1 -
      tileAffine (oddO w).val (cornerTiles (hWordOf w false) (vWordOf w false) 0).2.1 =
      ((num : ℚ) - 1, 1 - (den : ℚ)) := by
    rw [corner_3_family S oddO evenO h w, hnum, hden]
  refine ⟨v, a, FA, P, M, FB, (by rw [hv, hnum, hden]), (by rw [ha, hnum, hden]), hFAodo, hFB', htsP, htsM, hFAR, hFBR, hPa, ?_⟩
  intro α γ β δ hα hγ
  exact hlin_horizontal (oddO w).val (hWordOf w false) (vWordOf w false) num den v a hhead hlast hvh hvl
    (by rw [hq]) (by rw [hlenZ]) (by rw [hv]) (by rw [ha]) FA P M FB hFAodo hFB' hPts htsP htsM hMts
    hFAR hFBR hPa hC3 α γ β δ hα hγ

/-- The vertical instance for the standard tile: the right side `vStringAt` of the standard tile and the left side of its
translate by `v = almostV1 (oddBottom w)`, both carried by the vertical Moreover families translated by `B`. -/
theorem vlin_standard_vertical (S : FLatticePaper.Tiles.SurgicalWeak.WeakData)
    (oddO evenO : FLatticePaper.Farey.Word → PartialOdometer)
    (h : FLatticePaper.Tiles.SurgicalWeak.IsWeakStdFamily S oddO evenO) (w : FLatticePaper.Farey.Word) :
    ∃ (FA P M FB : PTFamily),
      (∀ k < FA.n, ∀ x ∈ FA.dom k, (oddO w).val x = FA.odo k x) ∧
      (∀ k < FB.n, ∀ x ∈ FB.dom k, (oddO w).val (x - almostV₁ (oddBottom w)) = FB.odo k x) ∧
      P.ts = FA.ts ∧ M.ts = FB.ts ∧ P.a 0 = M.a 0 ∧
      (∀ (α γ : GInt) (β δ : ℤ),
        (∀ k < P.n, ∀ x : GInt, FA.odo k x = P.odo k x + α.1 * x.1 + α.2 * x.2 + β) →
        (∀ j < M.n, ∀ x : GInt, FB.odo j x = M.odo j x + γ.1 * x.1 + γ.2 * x.2 + δ) →
        α = γ) := by
  obtain ⟨-, hA, -, hVr, hVf⟩ := (h w).2.2.2.2.1
  obtain ⟨FA, hFAts, hFA, -⟩ := hVf
  obtain ⟨G, hGts, hGS, -⟩ := hVr
  have hvw : vWordOf w false = vertWord w := rfl
  have hvh : (vWordOf w false).head? = some Letter.p := by
    rw [hvw]
    exact (StringCorners.vertWord_head_last w).1
  have hvl : (vWordOf w false).getLast? = some Letter.q := by
    rw [hvw]
    exact (StringCorners.vertWord_head_last w).2
  have hhead : (hWordOf w false).head? = some Letter.q := (hWordOf_head_last w false).1
  have hlast : (hWordOf w false).getLast? = some Letter.p := (hWordOf_head_last w false).2
  obtain ⟨P0, M0, hP0ts, hM0ts, -, -, -, -, -, hPM0⟩ :=
    verticalMoreover_proof (vWordOf w false) (standard_vWord_almostPalindrome w) hvh hvl
  obtain ⟨B, hB⟩ : ∃ B : GInt, B = lastPosOf (hStringAt (hWordOf w false) 0) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : GInt, v = almostV₁ (oddBottom w) := ⟨_, rfl⟩
  have hBv : B = v + (-1, -1) := by
    rw [hB, hv]
    exact vertical_B_eq w
  obtain ⟨P, hP⟩ : ∃ P : PTFamily, P = P0.translate B := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : PTFamily, M = M0.translate B := ⟨_, rfl⟩
  obtain ⟨FB, hFB⟩ : ∃ F : PTFamily, F = G.translate v := ⟨_, rfl⟩
  have hPts : P.ts = vStringAt (vWordOf w false) B := by
    rw [hP]
    show P0.ts.map (fun p => (p.1, p.2 + B)) = _
    rw [hP0ts, zoForwardV_eq, ← vStringAt_add, zero_add]
  have htsP : P.ts = FA.ts := by
    rw [hPts, hFAts, hB]
  have hMts' : M.ts = vRevStringAt (vWordOf w false).reverse ((1, 1) + B) := by
    rw [hM]
    show M0.ts.map (fun p => (p.1, p.2 + B)) = _
    rw [hM0ts, zoReversedStackedV_eq, ← vRevStringAt_add]
  have hFBts : FB.ts = vRevStringAt (vWordOf w false).reverse v := by
    rw [hFB]
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
  have hFB' : ∀ k < FB.n, ∀ x ∈ FB.dom k, (oddO w).val (x - v) = FB.odo k x := by
    intro k hk x hx
    have hkG : k < G.n := by
      rw [hFB, PTFamily.translate_n] at hk
      exact hk
    rw [hFB, PTFamily.translate_dom _ _ k hkG] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    rw [hFB, PTFamily.translate_odo _ _ k hkG, add_sub_cancel_right]
    exact hGS k hkG y hy
  have hPM : P.a 0 = M.a 0 := by
    rw [hP, hM]
    exact hPM0
  have hBv' : lastPosOf (hStringAt (hWordOf w false) 0) = v + (-1, -1) := by
    rw [← hB]
    exact hBv
  refine ⟨FA, P, M, FB, hFA, (by rw [← hv]; exact hFB'), htsP, htsM, hPM, ?_⟩
  intro α γ β δ hα hγ
  exact vlin_vertical (oddO w).val (hWordOf w false) (vWordOf w false) v hhead hlast hvh hvl hBv' hA
    FA P M FB hFA hFB' hFAts htsP htsM hFBts hPM α γ β δ hα hγ

end FLatticePaper.Tiles
