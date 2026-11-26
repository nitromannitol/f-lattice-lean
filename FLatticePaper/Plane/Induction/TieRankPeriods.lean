import FLatticePaper.Plane.Induction.EHPrice
import FLatticePaper.Plane.Induction.OppKernel
import FLatticePaper.Plane.Induction.VArcOffers
import FLatticePaper.Plane.Induction.ChainDeck
import FLatticePaper.Plane.Induction.BaseGeometry
import FLatticePaper.Plane.Induction.MatchedPolicy
import FLatticePaper.Plane.Induction.Packet
import FLatticePaper.Plane.Induction.StrongResidual
import FLatticePaper.Plane.Induction.StrongEstimates
import FLatticePaper.Plane.Induction.TieRankBound

/-! # The sheet difference and the rank on the conjugate deck (Q15, finiteness of the ties)

Let `o` be the odd parent of the word. The two vectors `wK = (o.den − o.num, −(o.den + o.num)) = −tipVertex` and
`wT = (2 o.den, 2 o.num)` have images `zTurn`-lifted to the kernel and transverse of the conjugate child:
`zTurn(x + wK) = zTurn x + K'` and `zTurn(x + wT) = zTurn x + T'`. Along them

* `Ψ(z + wK) = Ψ z + 1` (the tip shift, `EHPrice`), and
* `Ψ(z + wT) = Ψ z − 2 ε` (`qtf_two_up` makes the quarter-turn field periodic along `wT`; the sibling slope gives `−2 ε`),

while a rank with increments `(−1, 2ε)·λ` on `(K', T')` has proportional increments along `(wK, wT)`. So `rank_bounded_on_zero`
bounds the rank on the ties. -/

namespace FLatticePaper.TieRankPeriods

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.Induction.TipVertex FLatticePaper.W1Step
  FLatticePaper.W1MSheet FLatticePaper.EHPrice FLatticePaper.OppKernel

/-- The tip vertex of the word is the odd parent's transverse. -/
theorem tip_eq (word : Word) :
    tipVertex (frameAt word) = ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den,
      (frameAt word).parents.odd.num + (frameAt word).parents.odd.den) := rfl

/-- The sibling slope is additive. -/
theorem siblingSlope_add (fr : ChildFrame) (x y : Site) :
    fr.siblingSlope (x + y) = fr.siblingSlope x + fr.siblingSlope y := by
  unfold ChildFrame.siblingSlope
  simp only [Prod.fst_add, Prod.snd_add]
  ring

/-- The sibling slope of the vector `wT = (2 o.den, 2 o.num)` is `−2 ε`. -/
theorem siblingSlope_wT (word : Word) :
    (frameAt word).siblingSlope (2 * (frameAt word).parents.odd.den, 2 * (frameAt word).parents.odd.num) =
      -2 * (frameAt word).eps := by
  unfold ChildFrame.siblingSlope
  rw [ZoneI1.eps_eq]
  simp only
  ring

/-- **The tip shift by `wK = −tipVertex`.** `Ψ(z + wK) = Ψ z + 1`. -/
theorem psi_add_wK {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (z : Site) :
    sheetPsi word (z + ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num,
      -((frameAt word).parents.odd.den + (frameAt word).parents.odd.num))) = sheetPsi word z + 1 := by
  have hz : z + ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num,
      -((frameAt word).parents.odd.den + (frameAt word).parents.odd.num)) + tipVertex (frameAt word) = z := by
    rw [tip_eq]
    ext <;> simp <;> ring
  rcases ChildFrame.eps_unit (frameAt word) with h1 | h1
  · have := sheetPsi_add_tip_W1 h hSE h1 (z + ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num,
      -((frameAt word).parents.odd.den + (frameAt word).parents.odd.num)))
    rw [hz] at this
    linarith
  · have := sheetPsi_add_tip_W0 h hSE h1 (z + ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num,
      -((frameAt word).parents.odd.den + (frameAt word).parents.odd.num)))
    rw [hz] at this
    linarith

/-- **The shift by `wT = (2 o.den, 2 o.num)`.** `Ψ(z + wT) = Ψ z − 2 ε`. -/
theorem psi_add_wT {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (z : Site) :
    sheetPsi word (z + (2 * (frameAt word).parents.odd.den, 2 * (frameAt word).parents.odd.num)) =
      sheetPsi word z + (-2 * (frameAt word).eps) := by
  have q1 : ∀ y : Site, FqW word (y + (2 * (frameAt word).parents.odd.den, 2 * (frameAt word).parents.odd.num)) =
      FqW word y := fun y => qtf_two_up h hSE y
  have e1 : z + (2 * (frameAt word).parents.odd.den, 2 * (frameAt word).parents.odd.num) -
      (frameAt word).sheetShift - (frameAt word).sheetOffset =
      (z - (frameAt word).sheetShift - (frameAt word).sheetOffset) +
        (2 * (frameAt word).parents.odd.den, 2 * (frameAt word).parents.odd.num) := by
    ext <;> simp <;> ring
  have e2 : z + (2 * (frameAt word).parents.odd.den, 2 * (frameAt word).parents.odd.num) -
      (frameAt word).sheetShift =
      (z - (frameAt word).sheetShift) +
        (2 * (frameAt word).parents.odd.den, 2 * (frameAt word).parents.odd.num) := by
    ext <;> simp <;> ring
  unfold sheetPsi ChildFrame.sheetC ChildFrame.sheetA
  rw [e1, e2, q1, q1, siblingSlope_add, siblingSlope_wT]
  ring

/-- The conjugate child is `(odd.den − odd.num, odd.den + odd.num)` (numerator, denominator). -/
theorem conj_child_pair (word : Word) (h : ∃ x ∈ word, x ≠ Digit.three) :
    (frameAt (conjWord word)).child.num = (frameAt word).parents.odd.den - (frameAt word).parents.odd.num ∧
      (frameAt (conjWord word)).child.den = (frameAt word).parents.odd.den + (frameAt word).parents.odd.num :=
  conj_child_num_den (frameAt_conj_child h)

/-- The conjugate kernel is `(odd.den + odd.num, odd.den − odd.num)` (the multiplicity is one). -/
theorem conj_kernel (word : Word) (h : ∃ x ∈ word, x ≠ Digit.three) :
    (frameAt (conjWord word)).child.modifiedDeck.kernel =
      ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num,
        (frameAt word).parents.odd.den - (frameAt word).parents.odd.num) := by
  obtain ⟨hn, hd⟩ := conj_child_pair word h
  have hm := FLatticePaper.ChainDeck.periodMultiplicity_eq_one (frameAt (conjWord word))
  simp only [Fraction.modifiedDeck, hm, one_mul, hn, hd]

/-- The conjugate transverse is `(−2 odd.num, 2 odd.den)`. -/
theorem conj_transverse (word : Word) (h : ∃ x ∈ word, x ≠ Digit.three) :
    (frameAt (conjWord word)).child.modifiedDeck.transverse =
      (-2 * (frameAt word).parents.odd.num, 2 * (frameAt word).parents.odd.den) := by
  obtain ⟨hn, hd⟩ := conj_child_pair word h
  rw [ChildFrame.modTransverse_eq, hn, hd]
  ext <;> simp <;> ring

/-- `zTurn` carries `wK` to the conjugate kernel. -/
theorem zTurn_add_wK (word : Word) (x : Site) :
    zTurn (x + ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num,
      -((frameAt word).parents.odd.den + (frameAt word).parents.odd.num))) =
      zTurn x + ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num,
        (frameAt word).parents.odd.den - (frameAt word).parents.odd.num) := by
  unfold zTurn
  ext <;> simp <;> ring

/-- `zTurn` carries `wT` to the conjugate transverse. -/
theorem zTurn_add_wT (word : Word) (x : Site) :
    zTurn (x + (2 * (frameAt word).parents.odd.den, 2 * (frameAt word).parents.odd.num)) =
      zTurn x + (-2 * (frameAt word).parents.odd.num, 2 * (frameAt word).parents.odd.den) := by
  unfold zTurn
  ext <;> simp <;> ring

/-- **The rank bound on the ties.** Let `r` be the rank with increments `(−1, 2 ε) λ` on the conjugate kernel and transverse (the
`RankWithIncrements` of the policy, with `η = ε`). Then `r` is strictly decreasing along the retained edges, and it is bounded above
at `zTurn (z − lv)` over the sites `z` where `Ψ z = 0`. -/
theorem rank_bound_on_ties {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) {retained : Site → Site → Prop} (lv : Site)
    (hRI : RankWithIncrements retained (frameAt (conjWord word)).child.modifiedDeck.kernel
      (frameAt (conjWord word)).child.modifiedDeck.transverse (-1) (2 * (frameAt word).eps)) :
    ∃ r : Site → ℤ, (∀ x i, retained x i → r i < r x) ∧
      ∃ B : ℤ, ∀ z, sheetPsi word z = 0 → r (zTurn (z - lv)) ≤ B := by
  obtain ⟨r, lam, -, hdec, hU, hV⟩ := hRI
  rw [conj_kernel word h] at hU
  rw [conj_transverse word h] at hV
  refine ⟨r, hdec, ?_⟩
  have hdet := child_det_ne_zero (conjWord word)
  rw [conj_kernel word h, conj_transverse word h] at hdet
  dsimp only at hdet
  have hD : ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) *
      (2 * (frameAt word).parents.odd.num) -
      (-((frameAt word).parents.odd.den + (frameAt word).parents.odd.num)) *
        (2 * (frameAt word).parents.odd.den) ≠ 0 := by
    intro h0
    apply hdet
    linear_combination h0
  have hRU : ∀ z, r (zTurn (z + ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num,
      -((frameAt word).parents.odd.den + (frameAt word).parents.odd.num)) - lv)) =
      r (zTurn (z - lv)) + -1 * lam := by
    intro z
    have e : z + ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num,
        -((frameAt word).parents.odd.den + (frameAt word).parents.odd.num)) - lv =
        (z - lv) + ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num,
          -((frameAt word).parents.odd.den + (frameAt word).parents.odd.num)) := by
      ext <;> simp <;> ring
    rw [e, zTurn_add_wK word (z - lv)]
    have := hU (zTurn (z - lv))
    linarith
  have hRV : ∀ z, r (zTurn (z + (2 * (frameAt word).parents.odd.den, 2 * (frameAt word).parents.odd.num) - lv)) =
      r (zTurn (z - lv)) + 2 * (frameAt word).eps * lam := by
    intro z
    have e : z + (2 * (frameAt word).parents.odd.den, 2 * (frameAt word).parents.odd.num) - lv =
        (z - lv) + (2 * (frameAt word).parents.odd.den, 2 * (frameAt word).parents.odd.num) := by
      ext <;> simp <;> ring
    rw [e, zTurn_add_wT word (z - lv)]
    have := hV (zTurn (z - lv))
    linarith
  have hc : (-1 * lam) * (-2 * (frameAt word).eps) = (2 * (frameAt word).eps * lam) * 1 := by ring
  obtain ⟨B, hB⟩ := TieRankBound.rank_bounded_on_zero (U := ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num,
      -((frameAt word).parents.odd.den + (frameAt word).parents.odd.num)))
      (V := (2 * (frameAt word).parents.odd.den, 2 * (frameAt word).parents.odd.num)) hD
      (F := sheetPsi word) (R := fun z => r (zTurn (z - lv))) (p := 1) (q := -2 * (frameAt word).eps)
      (p' := -1 * lam) (q' := 2 * (frameAt word).eps * lam)
      (fun z => psi_add_wK h hSE z) (fun z => psi_add_wT h hSE z) hRU hRV hc (Or.inl one_ne_zero)
  exact ⟨B, fun z hz => hB z hz⟩

end FLatticePaper.TieRankPeriods
