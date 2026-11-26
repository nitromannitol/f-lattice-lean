import FLatticePaper.Plane.Induction.W1Lower
import FLatticePaper.Plane.Induction.W1Strips
import FLatticePaper.Plane.Induction.W1Seeds
import FLatticePaper.Plane.Induction.W1ZeroStrip
import FLatticePaper.Plane.Induction.Q3VStar
import FLatticePaper.Plane.Induction.W1ArcBottom

/-! # The parent's even zero interval for the top price (Q23-style step 2 input, PsiFaceSign)

Let `G = standardField (conjWord word)` be the conjugate field, `N/D` the odd parent of the word (`N = odd.num`, `D = odd.den`).
Its child frame has `num = D − N`, `den = D + N` (`frameAt_conj_num_den`), and the parent query `p(x) = N x₁ − D x₂` is the
conjugate's `s`-grade of the quarter turn: `sGrade(Z x) = 2 (p(x) − N)` (`W1ZeroStrip.sGrade_Z`).

`quarterTurnField G x = 0` holds at every even `x` with `1 − (N + D) ≤ p(x) ≤ 2 (N + D) − 1`:
* `p ≤ −D`: the conjugate's lower odd `h₀` (`W1Lower.lower_odd_h0`, on the conjugate frame, with the price range and drifts of
  `hSE` and the odd seed `hpar.odd_bottom`) gives `G (Z x) = h₀ (Z x)` on the odd site `Z x`;
* `N + D ≤ p`: the upper odd `h₀` (`W1Strips.V_side_full`, with the reflection `standardField_iRefl hSE` and the lower one);
* `−D < p < N + D`: the conjugate's harmonic strip (`hSE.packet.strips.2`).
No `hbd` is used: the conjugate's own price range (`hSE.priceRange`) is the input. -/

namespace FLatticePaper.TopParentZero

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1Strips FLatticePaper.W1Seeds FLatticePaper.W1ZeroStrip

/-- The conjugate's lower odd `h₀` interval, from `hSE` (price range and drifts of the conjugate) and the odd seed of `hpar`. -/
theorem conj_lower_odd {word : Word} (hSE : StrongEstimates (conjWord word)) (hpar : SeedFields (conjWord word))
    (z : Site) (hz : ¬ EvenSite z)
    (hlo : 2 - 3 * (frameAt (conjWord word)).child.den + (frameAt (conjWord word)).child.num ≤
      (frameAt (conjWord word)).sGrade z)
    (hhi : (frameAt (conjWord word)).sGrade z ≤ 1 - 2 * (frameAt (conjWord word)).child.den) :
    standardField (conjWord word) z = harmonicGrid z :=
  FLatticePaper.W1Lower.lower_odd_h0 (frameAt (conjWord word)) hSE.packet.strips hSE.priceRange
    (fun w => by have := (hSE.priceDrift w).1; linarith)
    (fun w => by have := (hSE.priceDrift w).2; linarith)
    (fun w hw hs => SeedFields.odd_bottom hpar w hw hs) z hz hlo hhi

/-- The conjugate's upper odd `h₀` interval `[den + num − 2 < s ≤ 3 den + num − 2]`, from the lower one by the reflection. -/
theorem conj_upper_odd {word : Word} (hSE : StrongEstimates (conjWord word)) (hpar : SeedFields (conjWord word))
    (z : Site) (hz : ¬ EvenSite z)
    (hlo : (frameAt (conjWord word)).child.den + (frameAt (conjWord word)).child.num - 2 <
      (frameAt (conjWord word)).sGrade z)
    (hhi : (frameAt (conjWord word)).sGrade z ≤
      3 * (frameAt (conjWord word)).child.den + (frameAt (conjWord word)).child.num - 2) :
    standardField (conjWord word) z = harmonicGrid z :=
  W1Strips.V_side_full (frameAt (conjWord word)) (F := standardField (conjWord word)) hSE.packet.strips
    (standardField_iRefl hSE)
    (fun z hz' h1 h2 => conj_lower_odd hSE hpar z hz' h1 h2) z hz hlo hhi

/-- **The parent's even zero interval.** For an even site `x` whose parent query `p(x) = N x₁ − D x₂` lies in
`[1 − (N + D), 2 (N + D) − 1]`, the quarter turn of the conjugate field vanishes (`N/D` the odd parent of the word). -/
theorem parent_even_zero {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hpar : SeedFields (conjWord word)) (hn3 : 3 ≤ (frameAt word).child.num) (x : Site) (hx : EvenSite x)
    (hlo : 1 - ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den) ≤
      (frameAt word).parents.odd.num * x.1 - (frameAt word).parents.odd.den * x.2)
    (hhi : (frameAt word).parents.odd.num * x.1 - (frameAt word).parents.odd.den * x.2 ≤
      2 * ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den) - 1) :
    quarterTurnField (standardField (conjWord word)) x = 0 := by
  obtain ⟨hcn, hcd⟩ := FLatticePaper.Induction.frameAt_conj_num_den h
  have hD2 := FLatticePaper.W1ArcBottom.odd_den_ge_two (frameAt word) hn3
  have hNu : 2 * (frameAt word).parents.odd.num =
      (frameAt (conjWord word)).child.den - (frameAt (conjWord word)).child.num := by
    rw [hcn, hcd]; ring
  have hDu : 2 * (frameAt word).parents.odd.den =
      (frameAt (conjWord word)).child.den + (frameAt (conjWord word)).child.num := by
    rw [hcn, hcd]; ring
  have hsg := sGrade_Z (frameAt (conjWord word)) x _ _ hNu hDu
  -- the parent query `p` and the odd site `Z x`
  obtain ⟨p, hp⟩ : ∃ p : ℤ, p = (frameAt word).parents.odd.num * x.1 - (frameAt word).parents.odd.den * x.2 :=
    ⟨_, rfl⟩
  rw [← hp] at hlo hhi hsg
  have hodd : ¬ EvenSite (-x.2, x.1 - 1) := by
    intro h
    have h1 : (x.1 + x.2) % 2 = 0 := hx
    have h2 : ((-x.2) + (x.1 - 1)) % 2 = 0 := h
    omega
  apply quarterTurn_zero_of_harmonic
  -- `sGrade (Z x) = 2 (p − N)`
  rw [hcn, hcd] at hsg
  rcases le_or_gt p (-(frameAt word).parents.odd.den) with hlow | hmid
  · -- lower odd interval: `sGrade (Z x) ∈ [2 − 3 den + num, 1 − 2 den]` for the conjugate
    refine conj_lower_odd hSE hpar _ hodd ?_ ?_
    · rw [hsg]; omega
    · rw [hsg]; omega
  · rcases le_or_gt ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den) p with hup | hmid'
    · -- upper odd interval
      refine conj_upper_odd hSE hpar _ hodd ?_ ?_
      · rw [hsg]; omega
      · rw [hsg]; omega
    · -- the harmonic strip of the conjugate
      exact hSE.packet.strips.2 _ (by rw [hsg]; omega) (by rw [hsg]; omega)

end FLatticePaper.TopParentZero
