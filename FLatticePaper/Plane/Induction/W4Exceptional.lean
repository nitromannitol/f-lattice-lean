import FLatticePaper.Plane.Induction.W4OldV
import FLatticePaper.Plane.Induction.PsiMonoOffset
import FLatticePaper.Plane.Induction.PriceDeck

/-! # W4 (Q35): the exceptional endpoint `v_{r−1}` of the old V star, under the west prescription

The old root `x` with `ζx = hFirst + c₁U' + c₂V'` (`hFirst = H'_0`, `reflH hLast = hFirst`) is the exceptional `v_{r−1}`: its `Y`-image is
`hLast` and its target under the free policy is the west neighbour `x' = x − (1,0)` (`ζx' = ζx + (0, −η)` by `prescribedH η hFirst`).
Both `a(x)` and `a(x')` equal `−c₁` (`= 1` at `c₁ = −1`): `P'(0) = c'₀` is the native V trace (`price_on_freeV`, `vFirst` is a
free V point), and `P'(U') = c'₀ − 1`. -/

namespace FLatticePaper.W4Exceptional

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1 FLatticePaper.W4OldV

variable {word : Word}

/-- The origin `vFirst = (0,0)` is a free V point of every child frame. -/
theorem vFirst_mem_freeV (frame : ChildFrame) : vFirst ∈ frame.freeV := by
  obtain ⟨hn0, hnd, hd2, hd3, hT⟩ := frame.child_facts
  have hT2 : 2 ≤ frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2 := by
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [closedPolygon_eq_closedRect frame]
    show closedRect frame.child.num frame.child.den vFirst
    unfold closedRect vFirst
    simp only [EvenSite, w1t, w1s, w1T]
    simp only [if_pos (show ((0:ℤ) + 0) % 2 = 0 by norm_num)]
    omega
  · rw [closedPolygon_eq_closedRect frame]
    show ¬ closedRect frame.child.num frame.child.den (vFirst.1 - 1, vFirst.2)
    unfold closedRect vFirst
    simp only [EvenSite, w1t, w1s, w1T]
    simp only [if_neg (show ¬ ((0:ℤ) - 1 + 0) % 2 = 0 by norm_num)]
    omega
  · have hs : frame.sGrade vFirst = 0 := by
      unfold ChildFrame.sGrade vFirst
      simp
    unfold ChildFrame.vSpectrum
    rw [hs]
    omega

/-- `P'(0) = c'₀`: the price is `cutPrice` on the free V cut, and `vFirst` is a free V point. -/
theorem price_vFirst_conj (hSE : StrongEstimates (conjWord word)) :
    (frameAt (conjWord word)).price (standardField (conjWord word)) vFirst =
      (frameAt (conjWord word)).cutPrice :=
  PriceDeck.price_on_freeV (frameAt (conjWord word)) (standardField (conjWord word)) hSE.packet.strips
    (vFirst_mem_freeV (frameAt (conjWord word)))

theorem prescribedH_hFirst (frame : ChildFrame) (η : ℤ) : frame.prescribedH η hFirst = (0, -η) := by
  unfold ChildFrame.prescribedH
  rw [if_pos rfl]

/-- The reflection of the last H label is the first: `reflH hLast = U' + I − hLast = (1, 0)`. -/
theorem reflH_hLast (frame : ChildFrame) :
    FLatticePaper.ReflectedFan.reflH frame frame.hLast = hFirst := by
  unfold FLatticePaper.ReflectedFan.reflH ChildFrame.hLast hFirst
  refine Prod.ext ?_ ?_ <;> simp

theorem hLast_ne_hFirst (frame : ChildFrame) : frame.hLast ≠ hFirst := by
  obtain ⟨-, -, -, hd3, -⟩ := frame.child_facts
  intro h
  unfold ChildFrame.hLast hFirst at h
  have := congrArg Prod.fst h
  simp only at this
  omega

/-- **The west prescription at the exceptional white.** With `ζx = hFirst + c₁U' + c₂V'` and the policy hypothesis `hPres`
(the retained inputs at free-closure whites are the prescribed ones), the retained target has `ζx' = ζx + (0, −η)`, `η = ε(word)`. -/
theorem west_of_prescription (_h : ∃ x ∈ word, x ≠ Digit.three)
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hPres : ∀ c : Site, FreeClosure.freeClosure (frameAt (conjWord word)) c →
      laplacian (standardField (conjWord word)) c = 0 →
      ∀ j : Site, P.retained c j ↔ FreePolicy.FreePresc (frameAt (conjWord word)) (frameAt word).eps c j)
    (c1 c2 : ℤ) (x x' : Site)
    (hx : zTurn x = FLatticePaper.Induction.hFirst +
      (c1 * (frameAt (conjWord word)).child.modifiedDeck.kernel.1 + c2 * (frameAt (conjWord word)).child.modifiedDeck.transverse.1,
        c1 * (frameAt (conjWord word)).child.modifiedDeck.kernel.2 + c2 * (frameAt (conjWord word)).child.modifiedDeck.transverse.2))
    (hwhite : laplacian (standardField (conjWord word)) (zTurn x) = 0)
    (hpol : parentPolicy P x x') :
    zTurn x' = zTurn x + (0, -(frameAt word).eps) := by
  set C := frameAt (conjWord word) with hC
  set η := (frameAt word).eps with hη
  have hlast : zTurn x + C.child.modifiedDeck.combine (-c1) (-c2) = hFirst := by
    rw [hx]
    unfold PeriodDeck.combine
    refine Prod.ext ?_ ?_ <;> simp <;> ring
  have hfree : hFirst ∈ C.freeH := FLatticePaper.PsiMonoOffset.hFirst_mem_freeH C
  have hfc : FreeClosure.freeClosure C (zTurn x) :=
    ⟨C.child.modifiedDeck.combine (-c1) (-c2), ⟨-c1, -c2, rfl⟩, Or.inl (by rw [hlast]; exact hfree)⟩
  have hpres1 : FreePolicy.FreePresc C η (zTurn x) (zTurn x + (0, -η)) :=
    ⟨C.child.modifiedDeck.combine (-c1) (-c2), ⟨-c1, -c2, rfl⟩,
      Or.inl ⟨by rw [hlast]; exact hfree, by rw [hlast, prescribedH_hFirst]⟩⟩
  have hPf := (hPres (zTurn x) hfc hwhite (zTurn x')).mp hpol
  exact FreePolicy.freePresc_single C η hPf hpres1

/-- **The exceptional endpoint of the old V star (Q35, `j = r − 1`).** With `ε = 1` and `ζx = hFirst + c₁U' + c₂V'`, the retained target is
`x' = x − (1,0)` and `a(x) = a(x') = −c₁`. -/
theorem oldV_exceptional (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hTr : TraceFromPsi.TraceAt (conjWord word)) (hW : (frameAt word).eps = 1)
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hPres : ∀ c : Site, FreeClosure.freeClosure (frameAt (conjWord word)) c →
      laplacian (standardField (conjWord word)) c = 0 →
      ∀ j : Site, P.retained c j ↔ FreePolicy.FreePresc (frameAt (conjWord word)) (frameAt word).eps c j)
    (c1 c2 : ℤ) (x x' : Site)
    (hx : zTurn x = FLatticePaper.Induction.hFirst +
      (c1 * (frameAt (conjWord word)).child.modifiedDeck.kernel.1 + c2 * (frameAt (conjWord word)).child.modifiedDeck.transverse.1,
        c1 * (frameAt (conjWord word)).child.modifiedDeck.kernel.2 + c2 * (frameAt (conjWord word)).child.modifiedDeck.transverse.2))
    (hwhite : laplacian (standardField (conjWord word)) (zTurn x) = 0)
    (hpol : parentPolicy P x x') :
    x' = x - (1, 0) ∧
      jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x = -c1 ∧
      jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x' = -c1 := by
  have hW' := west_of_prescription h P hPres c1 c2 x x' hx hwhite hpol
  rw [hW] at hW'
  have hzx' : zTurn x' = zTurn (x - (1, 0)) := by
    rw [hW']
    unfold zTurn
    refine Prod.ext ?_ ?_
    · simp
    · simp
      ring
  have hx' : x' = x - (1, 0) := W4OldH.zTurn_injective hzx'
  -- the jump at `x`: `g = hLast`, `reflH hLast = hFirst`
  have hx_refl : zTurn x = FLatticePaper.ReflectedFan.reflH (frameAt (conjWord word)) (frameAt (conjWord word)).hLast +
      (c1 * (frameAt (conjWord word)).child.modifiedDeck.kernel.1 + c2 * (frameAt (conjWord word)).child.modifiedDeck.transverse.1,
        c1 * (frameAt (conjWord word)).child.modifiedDeck.kernel.2 + c2 * (frameAt (conjWord word)).child.modifiedDeck.transverse.2) := by
    rw [reflH_hLast]
    exact hx
  have hg : (frameAt (conjWord word)).hLast ∈ (frameAt (conjWord word)).freeH := hLast_mem_freeH _
  have ja : jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x =
      (if (frameAt (conjWord word)).hLast = ((1 : ℤ), (0 : ℤ)) then 0 else 1) - c1 - 1 :=
    oldV_jumpA_of_trace h hSE hTr c1 c2 x hg hx_refl
  have hne : ¬ (frameAt (conjWord word)).hLast = ((1 : ℤ), (0 : ℤ)) := hLast_ne_hFirst _
  rw [if_neg hne] at ja
  -- the jump at `x'`
  have hj : ∀ y : Site, jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) y =
      (frameAt (conjWord word)).cutPrice -
        (frameAt (conjWord word)).price (standardField (conjWord word)) (reflectionI - zTurn y) := by
    intro y
    rw [jumpA_eq_cutPrice h hSE, zTurn_reflect]
  rw [W4OldH.conj_kernel_eq h, W4OldH.conj_transverse_eq h] at hx
  have hI : reflectionI - zTurn x' =
      (vFirst + ((-c1) * ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num),
          (-c1) * ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num))) +
        ((-c2) * (-2 * (frameAt word).parents.odd.num), (-c2) * (2 * (frameAt word).parents.odd.den)) := by
    rw [hW', hx]
    unfold reflectionI vFirst hFirst
    refine Prod.ext ?_ ?_ <;> simp <;> ring
  have hP : (frameAt (conjWord word)).price (standardField (conjWord word)) (reflectionI - zTurn x') =
      (frameAt (conjWord word)).cutPrice + c1 := by
    rw [hI, priceV_add_smul h hSE _ (-c2), priceU_add_smul h hSE vFirst (-c1), price_vFirst_conj hSE]
    ring
  refine ⟨hx', ?_, ?_⟩
  · rw [ja]; ring
  · rw [hj x', hP]; ring

end FLatticePaper.W4Exceptional
