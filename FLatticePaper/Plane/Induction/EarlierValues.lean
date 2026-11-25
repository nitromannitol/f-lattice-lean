import FLatticePaper.Plane.Induction.EarlierV
import FLatticePaper.Plane.Induction.VWindow

/-! Task w3, step 2(a): the earlier chain price on the conjugate's V cut, in the nominal form
`f(k) = c₀' + D'_η(V'_{k − ε' r'})`, with `D'_η(y) = G y − G(y + η σ')`.

* `valV`: at a V point whose window is not an endpoint, `Φ'_η(V'_k) = f(k)` (E1, E2a, E3).
* `valH`: `Φ'_η((1,0) + m V') = f(m L')` (E1, E2b, and `(1,0) − v'` is the odd upper endpoint of ordinate `−ε' r'`). -/

namespace FLatticePaper.EarlierValues

open Farey FLatticePaper FLatticePaper.Induction

/-- `vAt` moves by `m·V` under `j ↦ j + m·L`. -/
theorem vAt_add_mul_period (frame : ChildFrame) (base : ℤ → Site) (j m : ℤ) :
    FreeEnum.vAt frame base (j + m * FreeEnum.period frame) = FreeEnum.vAt frame base j + m • Vdeck frame := by
  have hp : FreeEnum.period frame ≠ 0 := (FreeEnum.period_pos frame).ne'
  have h1 : (j + m * FreeEnum.period frame) % FreeEnum.period frame = j % FreeEnum.period frame := by
    simp
  have h2 : (j + m * FreeEnum.period frame) / FreeEnum.period frame = j / FreeEnum.period frame + m := by
    rw [Int.add_mul_ediv_right _ _ hp]
  unfold FreeEnum.vAt
  rw [h1, h2]
  ext <;> simp <;> ring

/-- **valV:** the value at a non-endpoint V point of the conjugate. -/
theorem valV {word : Word} (hSE : StrongEstimates (conjWord word))
    (base : ℤ → Site)
    (hbase : ∀ r : ℤ, 0 ≤ r → r < FreeEnum.period (frameAt (conjWord word)) →
      base r ∈ (frameAt (conjWord word)).freeV ∧ (base r).2 = r) (k : ℤ)
    (hns : (EvenSite (FreeEnum.vAt (frameAt (conjWord word)) base k) →
        (frameAt (conjWord word)).sGrade (FreeEnum.vAt (frameAt (conjWord word)) base k) ≠ 0) ∧
      (¬ EvenSite (FreeEnum.vAt (frameAt (conjWord word)) base k) →
        (frameAt (conjWord word)).sGrade (FreeEnum.vAt (frameAt (conjWord word)) base k) ≠
          2 - (frameAt (conjWord word)).child.den + (frameAt (conjWord word)).child.num)) :
    FLatticePaper.earlierChainPrice (standardField (conjWord word)) (frameAt (conjWord word)).parents.odd
        (frameAt (oddBirthPrefix word)).eps (frameAt word).eps (FreeEnum.vAt (frameAt (conjWord word)) base k) =
      (frameAt (conjWord word)).cutPrice +
        (standardField (conjWord word) (FreeEnum.vAt (frameAt (conjWord word)) base
            (k - (frameAt (conjWord word)).eps * ((frameAt (conjWord word)).parents.odd.den +
              (frameAt (conjWord word)).parents.odd.num))) -
          standardField (conjWord word) (FreeEnum.vAt (frameAt (conjWord word)) base
            (k - (frameAt (conjWord word)).eps * ((frameAt (conjWord word)).parents.odd.den +
              (frameAt (conjWord word)).parents.odd.num)) +
            (frameAt word).eps • (frameAt (conjWord word)).shortShift)) := by
  rw [EarlierV.earlierP_eq_price_add, EarlierV.price_vAt_eq hSE base hbase k,
    VWindow.shift_vAt (frameAt (conjWord word)) base hbase k hns]

/-- **valH:** the value at the H-form point `(1,0) + m V'`. -/
theorem valH {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hTraceConj : ∀ w ∈ (frameAt (conjWord word)).freeH,
      (frameAt (conjWord word)).price (standardField (conjWord word)) w =
        (frameAt (conjWord word)).cutPrice - (if w = ((1 : ℤ), (0 : ℤ)) then 0 else 1))
    (base : ℤ → Site)
    (hbase : ∀ r : ℤ, 0 ≤ r → r < FreeEnum.period (frameAt (conjWord word)) →
      base r ∈ (frameAt (conjWord word)).freeV ∧ (base r).2 = r) (m : ℤ) :
    FLatticePaper.earlierChainPrice (standardField (conjWord word)) (frameAt (conjWord word)).parents.odd
        (frameAt (oddBirthPrefix word)).eps (frameAt word).eps (((1 : ℤ), (0 : ℤ)) + m • Vdeck (frameAt (conjWord word))) =
      (frameAt (conjWord word)).cutPrice +
        (standardField (conjWord word) (FreeEnum.vAt (frameAt (conjWord word)) base
            (m * FreeEnum.period (frameAt (conjWord word)) - (frameAt (conjWord word)).eps *
              ((frameAt (conjWord word)).parents.odd.den + (frameAt (conjWord word)).parents.odd.num))) -
          standardField (conjWord word) (FreeEnum.vAt (frameAt (conjWord word)) base
            (m * FreeEnum.period (frameAt (conjWord word)) - (frameAt (conjWord word)).eps *
              ((frameAt (conjWord word)).parents.odd.den + (frameAt (conjWord word)).parents.odd.num)) +
            (frameAt word).eps • (frameAt (conjWord word)).shortShift)) := by
  set C := frameAt (conjWord word) with hC
  have hp := FreeEnum.period_pos C
  have hA : ((1 : ℤ), (0 : ℤ)) - C.parentShift = FreeEnum.vAt C base (-(C.eps * (C.parents.odd.den + C.parents.odd.num))) := by
    have hord : (((1 : ℤ), (0 : ℤ)) - C.parentShift).2 =
        (FreeEnum.vAt C base (-(C.eps * (C.parents.odd.den + C.parents.odd.num)))).2 := by
      rw [FreeEnum.vAt_snd C base (fun r h0 h1 => (hbase r h0 h1).2)]
      unfold ChildFrame.parentShift
      simp only [Prod.snd_sub]
      ring
    have hwin : (EvenSite (((1 : ℤ), (0 : ℤ)) - C.parentShift) →
        0 ≤ C.sGrade (((1 : ℤ), (0 : ℤ)) - C.parentShift) ∧ C.sGrade (((1 : ℤ), (0 : ℤ)) - C.parentShift) ≤ 2 * C.child.num) ∧
      (¬ EvenSite (((1 : ℤ), (0 : ℤ)) - C.parentShift) →
        2 - C.child.den + C.child.num ≤ C.sGrade (((1 : ℤ), (0 : ℤ)) - C.parentShift) ∧
          C.sGrade (((1 : ℤ), (0 : ℤ)) - C.parentShift) ≤ C.child.den + C.child.num - 2) := by
      have hsx : C.sGrade (((1 : ℤ), (0 : ℤ)) - C.parentShift) = C.child.den + C.child.num - 2 := by
        have h1 := VWindow.sGrade_add C (((1 : ℤ), (0 : ℤ)) - C.parentShift) C.parentShift
        rw [sub_add_cancel, VWindow.sGrade_parentShift] at h1
        have h2 : C.sGrade ((1 : ℤ), (0 : ℤ)) = C.child.den + C.child.num := by
          unfold ChildFrame.sGrade
          ring
        linarith
      have hodd : ¬ EvenSite (((1 : ℤ), (0 : ℤ)) - C.parentShift) := by
        unfold EvenSite
        have hev : (C.parents.odd.num + C.parents.odd.den) % 2 = 1 := C.valid.odd_parity
        unfold ChildFrame.parentShift
        simp only [Prod.fst_sub, Prod.snd_sub]
        have hab : C.eps * (C.parents.odd.num - C.parents.odd.den) + C.eps * (C.parents.odd.num + C.parents.odd.den) =
            2 * (C.eps * C.parents.odd.num) := by ring
        generalize C.eps * (C.parents.odd.num - C.parents.odd.den) = a at hab ⊢
        generalize C.eps * (C.parents.odd.num + C.parents.odd.den) = b at hab ⊢
        generalize C.eps * C.parents.odd.num = q at hab ⊢
        omega
      refine ⟨fun he => absurd he hodd, fun _ => ?_⟩
      rw [hsx]
      obtain ⟨hn0, hnd, hdn, hd3, -⟩ := C.child_facts
      constructor <;> omega
    exact VWindow.row_unique C hord hwin (VWindow.vAt_window C base hbase _)
  have hz : ((1 : ℤ), (0 : ℤ)) + m • Vdeck C - C.parentShift =
      FreeEnum.vAt C base (m * FreeEnum.period C - C.eps * (C.parents.odd.den + C.parents.odd.num)) := by
    have e1 : ((1 : ℤ), (0 : ℤ)) + m • Vdeck C - C.parentShift = (((1 : ℤ), (0 : ℤ)) - C.parentShift) + m • Vdeck C := by
      abel
    rw [e1, hA, ← vAt_add_mul_period C base (-(C.eps * (C.parents.odd.den + C.parents.odd.num))) m]
    congr 1
    ring
  rw [EarlierV.earlierP_eq_price_add, EarlierV.price_one_add h hSE hTraceConj m, hz]

end FLatticePaper.EarlierValues
