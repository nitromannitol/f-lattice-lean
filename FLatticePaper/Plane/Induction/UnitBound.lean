import FLatticePaper.Plane.Induction.PlusOffer
import FLatticePaper.Plane.Induction.StrongDeckSpan
import FLatticePaper.Plane.Induction.StrongPriceRange
import FLatticePaper.Plane.Induction.StrongVStar
import FLatticePaper.Plane.Induction.StrongHSpan
import FLatticePaper.Plane.Induction.PolygonGeometry
import FLatticePaper.Plane.Induction.Packet
import FLatticePaper.Plane.Induction.RotatedMono
import FLatticePaper.Plane.Induction.Sheets
import FLatticePaper.Tiles.SiteScope
import FLatticePaper.Farey.Rotation
import FLatticePaper.Farey.Recursion

/-! # The unit bound of the sign `+1` permit (Q34, W3): `ψ₊(x) ≤ ψ₊(x − e) + 1`

Write `c` for the cut price of the conjugate, `P'` for its price, and `ψ₊(x) = c − P'(zTurn x)`
(`pJump_eq_cutPrice`). The conjugate's kernel `U'` has `s`-grade `T'` and moves `P'` by `−1`; the
transverse `V'` keeps `P'` and `s`. A kernel count `k` is admissible for `w` when `s(w) + kT'` lies in the
`s`-range of the closed polygon at the parity of `w`. Then `P'(w) ∈ [c − 1 + k, c + k]` (`price_window`).

The canonical count `k(w)` is the least admissible one: `lo ≤ s(w) + k T' < lo + T'`. Along `x ↦ x − e` the
`s`-grade rises by `2 t_p(−e) ≥ 0`, so the canonical count falls (`index_mono`), and
`ψ₊(x) ≤ 1 − k(x) ≤ 1 − k(x − e) ≤ ψ₊(x − e) + 1`.

The inequality `t_p(−e) ≥ 0` is `D e₂ − N e₁ ≥ 0` for `e = V_q + ε U_q`, from the parent bounds
(`SiteScope.parents_bounds`) and `ε = ±1`. No premise beyond the word hypothesis. -/

namespace FLatticePaper.UnitBound

open Farey FLatticePaper FLatticePaper.Induction

/-- An integer `k` with `lo ≤ s + k T < lo + T`. -/
theorem index_ex (s lo T : ℤ) (hT : 0 < T) : ∃ k : ℤ, lo ≤ s + k * T ∧ s + k * T < lo + T := by
  refine ⟨-((s - lo) / T), ?_, ?_⟩
  · have h1 := Int.emod_def (s - lo) T
    have h2 := Int.emod_nonneg (s - lo) hT.ne'
    nlinarith
  · have h1 := Int.emod_def (s - lo) T
    have h3 := Int.emod_lt_of_pos (s - lo) hT
    nlinarith

/-- The canonical count is antitone in the `s`-grade. -/
theorem index_mono {s s' lo T k k' : ℤ} (hT : 0 < T) (hss : s ≤ s')
    (hk : lo ≤ s + k * T ∧ s + k * T < lo + T) (hk' : lo ≤ s' + k' * T ∧ s' + k' * T < lo + T) :
    k' ≤ k := by
  by_contra hcon
  have h1 : k + 1 ≤ k' := by omega
  have h2 : (k + 1) * T ≤ k' * T := by nlinarith
  nlinarith [hk.1, hk'.2]

/-- The `s`-grade is affine along the deck: `s(x + k a) = s(x) + k s(a)`. -/
theorem sGrade_add_smul (fr : ChildFrame) (x a : Site) (k : ℤ) :
    fr.sGrade (x + k • a) = fr.sGrade x + k * fr.sGrade a := by
  unfold ChildFrame.sGrade
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- **A kernel count admissible for the `s`-range gives the price window.** -/
theorem price_window {u : Word} (hS : StrongEstimates u) (w : Site) (k : ℤ)
    (hsk : (EvenSite w ∧ 0 ≤ (frameAt u).sGrade w + k * (frameAt u).child.periodDenominator ∧
        (frameAt u).sGrade w + k * (frameAt u).child.periodDenominator ≤
          (frameAt u).child.periodDenominator + 2 * (frameAt u).child.num) ∨
      (¬ EvenSite w ∧ 2 - (frameAt u).child.den + (frameAt u).child.num ≤
          (frameAt u).sGrade w + k * (frameAt u).child.periodDenominator ∧
        (frameAt u).sGrade w + k * (frameAt u).child.periodDenominator ≤
          (frameAt u).child.periodDenominator + (frameAt u).child.den + (frameAt u).child.num - 2)) :
    (frameAt u).cutPrice - 1 + k ≤ (frameAt u).price (standardField u) w ∧
      (frameAt u).price (standardField u) w ≤ (frameAt u).cutPrice + k := by
  obtain ⟨l, hpar, hw1⟩ := StrongPriceRange.exists_transverse_t_window (frameAt u) w
  have hEv : EvenSite (w + l • (frameAt u).child.modifiedDeck.transverse +
      k • (frameAt u).child.modifiedDeck.kernel) ↔ EvenSite w :=
    ((frameAt u).evenSite_add_smul_kernel _ k).trans (StrongHSpan.evenSite_add_transverse (frameAt u) w l)
  have htl : (frameAt u).tGrade (w + l • (frameAt u).child.modifiedDeck.transverse +
      k • (frameAt u).child.modifiedDeck.kernel) =
        (frameAt u).tGrade (w + l • (frameAt u).child.modifiedDeck.transverse) := by
    rw [(frameAt u).tGrade_add_pt, (frameAt u).tGrade_smul, StrongVStar.tGrade_kernel_eq_zero (frameAt u)]
    ring
  have hsG : (frameAt u).sGrade (w + l • (frameAt u).child.modifiedDeck.transverse +
      k • (frameAt u).child.modifiedDeck.kernel) = (frameAt u).sGrade w + k * (frameAt u).child.periodDenominator := by
    rw [sGrade_add_smul, sGrade_add_smul, RotatedMono.sGrade_transverse, RotatedMono.sGrade_kernel]
    ring
  have hmem : w + l • (frameAt u).child.modifiedDeck.transverse +
      k • (frameAt u).child.modifiedDeck.kernel ∈ (frameAt u).closedPolygon := by
    rw [ChildFrame.mem_closedPolygon_iff, htl, hsG]
    rcases hsk with ⟨hE, hs1, hs2⟩ | ⟨hE, hs1, hs2⟩
    · left
      exact ⟨hEv.mpr hE, (hw1.1 hE).1, (hw1.1 hE).2, hs1, hs2⟩
    · right
      exact ⟨fun hh => hE (hEv.mp hh), (hw1.2 hE).1, (hw1.2 hE).2, hs1, hs2⟩
  have hPU : ∀ s : Site, (frameAt u).price (standardField u)
      (s + (frameAt u).child.modifiedDeck.kernel) = (frameAt u).price (standardField u) s - 1 :=
    fun s => by linarith [(hS.priceDrift s).1]
  have hPV : ∀ s : Site, (frameAt u).price (standardField u)
      (s + (frameAt u).child.modifiedDeck.transverse) = (frameAt u).price (standardField u) s :=
    fun s => by linarith [(hS.priceDrift s).2]
  have hdeck := StrongDeckSpan.price_of_deck_rep (frameAt u) (standardField u) hPU hPV w l k
  have hr := hS.priceRange _ hmem
  constructor <;> linarith [hr.1, hr.2, hdeck]

/-- The conjugate's `s`-grade at `zTurn y`: `s(zTurn y) = 2 (N y₁ − D y₂) − 2 N`, with `(N, D)` the odd parent. -/
theorem conj_child_sums {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) :
    (frameAt (conjWord word)).child.den = (frameAt word).parents.odd.den + (frameAt word).parents.odd.num ∧
      (frameAt (conjWord word)).child.num = (frameAt word).parents.odd.den - (frameAt word).parents.odd.num := by
  have hc : (frameAt (conjWord word)).child = (frameAt word).parents.odd.rotate := frameAt_conj_child h
  have ho : (frameAt word).parents.odd.Odd := (parentsAt_valid word).odd_parity
  rw [hc, Fraction.rotate_of_odd ho]
  exact ⟨by ring, by ring⟩

theorem sGrade_conj_zTurn {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (y : Site) :
    (frameAt (conjWord word)).sGrade (zTurn y) =
      2 * ((frameAt word).parents.odd.num * y.1 - (frameAt word).parents.odd.den * y.2) -
        2 * (frameAt word).parents.odd.num := by
  obtain ⟨h1, h2⟩ := conj_child_sums h
  unfold ChildFrame.sGrade zTurn
  rw [h1, h2]
  ring

/-- The sheet offset in coordinates: `e = V_q + ε U_q` with `U_q = (d_q, n_q)`, `V_q = (n_q − d_q, n_q + d_q)`. -/
theorem sheetOffset_coords {word : Word} :
    (frameAt word).sheetOffset =
      ((frameAt word).parents.even.num - (frameAt word).parents.even.den +
          (frameAt word).eps * (frameAt word).parents.even.den,
        (frameAt word).parents.even.num + (frameAt word).parents.even.den +
          (frameAt word).eps * (frameAt word).parents.even.num) := by
  unfold ChildFrame.sheetOffset Fraction.unmodifiedDeck
  ext <;> simp

/-- **`t_p(−e) ≥ 0`:** `D e₂ − N e₁ ≥ 0`, from the parent bounds and `ε = ±1`. -/
theorem tp_negE_nonneg {word : Word} :
    0 ≤ (frameAt word).parents.odd.den * (frameAt word).sheetOffset.2 -
      (frameAt word).parents.odd.num * (frameAt word).sheetOffset.1 := by
  obtain ⟨hb1, hb2, hb3, hb4⟩ := FLatticePaper.Tiles.SiteScope.parents_bounds word
  have hN0 : 0 ≤ (frameAt word).parents.odd.num := hb2
  have hND : 0 ≤ (frameAt word).parents.odd.den - (frameAt word).parents.odd.num := by
    have : (1:ℤ) ≤ (frameAt word).parents.odd.den - (frameAt word).parents.odd.num := hb1
    linarith
  have heN : 0 ≤ (frameAt word).parents.even.num := by
    have : (1:ℤ) ≤ (frameAt word).parents.even.num := hb3
    linarith
  have heD' : 0 ≤ (frameAt word).parents.even.den - (frameAt word).parents.even.num := hb4
  have hD0 : 0 ≤ (frameAt word).parents.odd.den := by linarith
  have hEDn : 0 ≤ (frameAt word).parents.even.den := by linarith
  have hε := ChildFrame.eps_unit (frameAt word)
  rw [sheetOffset_coords]
  rcases hε with h1 | h1 <;> rw [h1] <;>
    nlinarith [mul_nonneg hD0 heD', mul_nonneg heN hND, mul_nonneg hD0 heN, mul_nonneg hN0 hEDn]

/-- **The unit bound (W3, `hunit`):** `ψ₊(x) ≤ ψ₊(x − e) + 1`, for every `x`. -/
theorem unit_bound {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (x : Site) :
    pJump (frameAt word) (quarterTurnField (standardField (conjWord word))) x ≤
      pJump (frameAt word) (quarterTurnField (standardField (conjWord word)))
        (x - (frameAt word).sheetOffset) + 1 := by
  rw [PlusOffer.pJump_eq_cutPrice h hSE x,
    PlusOffer.pJump_eq_cutPrice h hSE (x - (frameAt word).sheetOffset)]
  obtain ⟨hn, hnd, -, hd3, hTeq⟩ := (frameAt (conjWord word)).child_facts
  have hT : 0 < (frameAt (conjWord word)).child.periodDenominator := by
    rw [hTeq]
    nlinarith
  have hs12 : (frameAt (conjWord word)).sGrade (zTurn x) ≤
      (frameAt (conjWord word)).sGrade (zTurn (x - (frameAt word).sheetOffset)) := by
    rw [sGrade_conj_zTurn h, sGrade_conj_zTurn h]
    have := tp_negE_nonneg (word := word)
    simp only [Prod.fst_sub, Prod.snd_sub]
    nlinarith
  have hpar : EvenSite (zTurn (x - (frameAt word).sheetOffset)) ↔ EvenSite (zTurn x) := by
    have hev : ((frameAt word).parents.even.num + (frameAt word).parents.even.den) % 2 = 0 :=
      (parentsAt_valid word).even_parity
    have hε := ChildFrame.eps_unit (frameAt word)
    have he1 : (frameAt word).sheetOffset.1 + (frameAt word).sheetOffset.2 =
        2 * (frameAt word).parents.even.num +
          (frameAt word).eps * ((frameAt word).parents.even.den + (frameAt word).parents.even.num) := by
      rw [sheetOffset_coords]
      dsimp only
      ring
    unfold EvenSite zTurn
    simp only [Prod.fst_sub, Prod.snd_sub]
    rcases hε with h1 | h1 <;> rw [h1] at he1 <;> omega
  by_cases hE : EvenSite (zTurn x)
  · obtain ⟨k, hk1, hk2⟩ := index_ex ((frameAt (conjWord word)).sGrade (zTurn x)) 0 _ hT
    obtain ⟨k', hk1', hk2'⟩ := index_ex ((frameAt (conjWord word)).sGrade (zTurn (x - (frameAt word).sheetOffset))) 0 _ hT
    have hkk := index_mono hT hs12 ⟨hk1, hk2⟩ ⟨hk1', hk2'⟩
    have hP1 := price_window hSE (zTurn x) k (Or.inl ⟨hE, hk1, by linarith⟩)
    have hP2 := price_window hSE (zTurn (x - (frameAt word).sheetOffset)) k'
      (Or.inl ⟨hpar.mpr hE, hk1', by linarith⟩)
    linarith [hP1.1, hP1.2, hP2.1, hP2.2]
  · have hnE : ¬ EvenSite (zTurn (x - (frameAt word).sheetOffset)) := fun hh => hE (hpar.mp hh)
    obtain ⟨k, hk1, hk2⟩ := index_ex ((frameAt (conjWord word)).sGrade (zTurn x))
      (2 - (frameAt (conjWord word)).child.den + (frameAt (conjWord word)).child.num) _ hT
    obtain ⟨k', hk1', hk2'⟩ := index_ex ((frameAt (conjWord word)).sGrade (zTurn (x - (frameAt word).sheetOffset)))
      (2 - (frameAt (conjWord word)).child.den + (frameAt (conjWord word)).child.num) _ hT
    have hkk := index_mono hT hs12 ⟨hk1, hk2⟩ ⟨hk1', hk2'⟩
    have hP1 := price_window hSE (zTurn x) k (Or.inr ⟨hE, hk1, by linarith⟩)
    have hP2 := price_window hSE (zTurn (x - (frameAt word).sheetOffset)) k'
      (Or.inr ⟨hnE, hk1', by linarith⟩)
    linarith [hP1.1, hP1.2, hP2.1, hP2.2]

end FLatticePaper.UnitBound
