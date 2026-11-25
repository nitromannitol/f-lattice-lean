import FLatticePaper.Plane.Induction.PsiIdentity
import FLatticePaper.Plane.Induction.ChainDeck
import FLatticePaper.Plane.Induction.Q3Hlat
import FLatticePaper.Plane.Induction.Q3VStar
import FLatticePaper.Plane.Induction.ClippedIdentity
import FLatticePaper.CanonicalHeadline

/-! Task 72 / Q31 psi, the reflected form `ψ(x) = c₀' − P'(I − Z x)`.

* `price_reflectI`: for a field with `F(I − z) = F z`, `P(q + v) + P(I − q) = 2 c₀` (`v = parentShift`, `c₀ = cutPrice`). The `F`-terms cancel,
  and `−ε(s_p(v) + s_p(I)) = T − ε(N + D) = 2c₀`, using `ε² = 1` and the evenness of `T − ε(N + D)`.
* `psi_reflect_price`: `Fp(x + uq) − Fp(x) = c₀' − P'(I − Z x)`. The lattice relation `δ = v + k·T` (`lattice_bridge_exists`) and
  the transverse invariance of `P'` (`price_transverse_mul`) reduce `P'(Z(x + uq))` to `P'(Z x + v)`. -/

namespace FLatticePaper.PriceReflect

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1MSheet

/-- `2 · ((T − ε(D + N))/2) = T − ε(D + N)` for `ε = ±1`, with `T = D² + 2DN − N²`. -/
theorem two_mul_half (D N ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    2 * ((D ^ 2 + 2 * D * N - N ^ 2 - ε * (D + N)) / 2) = D ^ 2 + 2 * D * N - N ^ 2 - ε * (D + N) := by
  have hE := ClippedIdentity.even_half D N
  rcases hε with h1 | h1
  · have e : D ^ 2 + 2 * D * N - N ^ 2 - 1 * (D + N) = D ^ 2 + 2 * D * N - N ^ 2 - D - N := by ring
    rw [h1, e]
    exact hE
  · have e : D ^ 2 + 2 * D * N - N ^ 2 - (-1) * (D + N) = (D ^ 2 + 2 * D * N - N ^ 2 - D - N) + 2 * (D + N) := by ring
    rw [h1, e, Int.add_mul_ediv_left _ _ (by norm_num : (2 : ℤ) ≠ 0)]
    linarith [hE]

/-- **The reflection of the price.** For a field with `F(I − z) = F z` on a child frame `C` (with odd parent `N/D`):
`P(q + v) + P(I − q) = 2 c₀`. -/
theorem price_reflectI (C : ChildFrame) {F : Field} (hI : ∀ z, F (reflectionI - z) = F z) (q : Site) :
    C.price F (q + C.parentShift) + C.price F (reflectionI - q) = 2 * C.cutPrice := by
  have hε2 := ChildFrame.eps_sq_one C
  have hεu := C.eps_unit
  have e1 : reflectionI - q - C.parentShift = reflectionI - (q + C.parentShift) := by abel
  unfold ChildFrame.price ChildFrame.cutPrice
  rw [e1, hI (q + C.parentShift), hI q]
  unfold ChildFrame.parentSlope ChildFrame.parentShift reflectionI
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, add_sub_cancel_right]
  have hc := two_mul_half C.parents.odd.den C.parents.odd.num C.eps hεu
  unfold Fraction.periodDenominator at hc ⊢
  linear_combination (C.parents.odd.den ^ 2 + 2 * C.parents.odd.den * C.parents.odd.num - C.parents.odd.num ^ 2 : ℤ) * hε2 - hc

/-- The transverse vector of a child frame: `(n − d, n + d)`. -/
theorem transverse_vec (C : ChildFrame) :
    C.child.modifiedDeck.transverse = (C.child.num - C.child.den, C.child.num + C.child.den) := by
  have ht : C.child.modifiedDeck.transverse = C.child.modifiedDeck.combine 0 1 := by
    unfold Farey.PeriodDeck.combine
    simp
  rw [ht, ChainDeck.combine_eq_vec]
  ext <;> simp

/-- **The reflected jump.** `Fp(x + uq) − Fp(x) = c₀' − P'(I − Z x)`, for the conjugate price `P'` and cut price `c₀'`. -/
theorem psi_reflect_price {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (x : Site) :
    FqW word (x + (frameAt word).uq) - FqW word x =
      (frameAt (conjWord word)).cutPrice -
        (frameAt (conjWord word)).price (standardField (conjWord word)) (reflectionI - zTurn x) := by
  have hI : ∀ z, standardField (conjWord word) (reflectionI - z) = standardField (conjWord word) z :=
    fun z => FLatticePaper.standardField_reflectI_conj word hSE z
  have hP := hSE.packet
  have hconj := frameAt_conj_child h
  obtain ⟨j, hj⟩ := ChildFrame.lattice_bridge_exists (frameAt word) (frameAt (conjWord word)) hconj
  obtain ⟨hcn, hcd⟩ := frameAt_conj_num_den h
  have hT : (frameAt (conjWord word)).child.modifiedDeck.transverse =
      (-2 * (frameAt word).parents.odd.num, 2 * (frameAt word).parents.odd.den) := by
    rw [transverse_vec, hcn, hcd]
    ext <;> simp <;> ring
  have hdelta : zTurn (x + (frameAt word).uq) =
      zTurn x + ((frameAt (conjWord word)).parentShift +
        (-j) • (frameAt (conjWord word)).child.modifiedDeck.transverse) := by
    rw [hT]
    have h1 := congrArg Prod.fst hj
    have h2 := congrArg Prod.snd hj
    simp only [Prod.fst_add, Prod.snd_add] at h1 h2
    unfold zTurn ChildFrame.uq ChildFrame.parentShift
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_eq_mul] <;> linarith
  rw [FLatticePaper.PsiIdentity.psi_eq_price h hSE x, hdelta, ← add_assoc,
    ChainDeck.price_transverse_mul (frameAt (conjWord word)) hP (-j)]
  have hr := price_reflectI (frameAt (conjWord word)) hI (zTurn x)
  linarith

end FLatticePaper.PriceReflect
