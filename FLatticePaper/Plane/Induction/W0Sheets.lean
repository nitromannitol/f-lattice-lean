import FLatticePaper.Plane.Induction.ChartPeriods
import FLatticePaper.Plane.Induction.Q3Paragraph8
import FLatticePaper.Plane.Induction.W1Hstrong
import FLatticePaper.Plane.Induction.SheetPieces
import FLatticePaper.Plane.Induction.Q3Field
import FLatticePaper.Plane.Induction.I3Permits
import FLatticePaper.Plane.Induction.Reflection
import FLatticePaper.Plane.Induction.TipVertex

/-! Task 72 (TIP_THEOREM, the W0 middle through the sheets): the V_p jet of the parent field and the harmonic translation identities.

* `quarterTurnField_add_tipVertex`: the quarter-turn field `Fp = quarterTurnField G` of the conjugate satisfies
  `Fp (x + V_p) = Fp x + (harmonicGrid (x + V_p) − harmonicGrid x)`. The quarter turn sends `V_p` to minus the conjugate
  kernel `(d_p + n_p, d_p − n_p)`, along which `G` is periodic with constant `0` (`coherentConstantU_eq_zero`).
* `harmonicGrid_add_tipVertex`: `harmonicGrid (x + V_p) = harmonicGrid x + n_p x.1 − d_p x.2 + s` for the constant `s` of
  `harmonicGrid_sub_V` (with `2s = −n_p − d_p − T_p`).
* `harmonicGrid_sub_Vq`: `harmonicGrid (x − V_q) = harmonicGrid x − n_q x.1 + d_q x.2 + s_q`, `2 s_q = n_q + d_q − T_q`.
* `harmonicGrid_two_one`: `harmonicGrid (2,1) = 1`. -/

namespace FLatticePaper.Induction

namespace W0Sheets

open Farey FLatticePaper FLatticePaper.Induction.TipVertex ShortPassages FLatticePaper.W1Seeds

/-- The quarter turn of `x + V_p` is the quarter turn of `x` minus the conjugate kernel. -/
theorem i3Z_add_tipVertex_eq {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (x : Site) :
    QuarterTurn.counterclockwise.mapSite (0, -1) (x + tipVertex (frameAt word)) =
      QuarterTurn.counterclockwise.mapSite (0, -1) x -
        ((frameAt (conjWord word)).child.den, (frameAt (conjWord word)).child.num) := by
  obtain ⟨hcn, hcd⟩ := frameAt_conj_num_den h
  rw [i3_mapSite_eq, i3_mapSite_eq, hcn, hcd]
  unfold i3Z tipVertex
  ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> ring

/-- **The V_p jet of the quarter-turn field.** -/
theorem quarterTurnField_add_tipVertex {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (x : Site) :
    quarterTurnField (standardField (conjWord word)) (x + tipVertex (frameAt word)) =
      quarterTurnField (standardField (conjWord word)) x +
        (harmonicGrid (x + tipVertex (frameAt word)) - harmonicGrid x) := by
  have hK := hSE.packet.periods.1
  rw [(frameAt (conjWord word)).child_modifiedDeck_kernel,
    (frameAt (conjWord word)).coherentConstantU_eq_zero] at hK
  have hper : standardField (conjWord word) (QuarterTurn.counterclockwise.mapSite (0, -1) x) =
      standardField (conjWord word)
        (QuarterTurn.counterclockwise.mapSite (0, -1) x -
          ((frameAt (conjWord word)).child.den, (frameAt (conjWord word)).child.num)) := by
    have := hK (QuarterTurn.counterclockwise.mapSite (0, -1) x -
      ((frameAt (conjWord word)).child.den, (frameAt (conjWord word)).child.num))
    rw [sub_add_cancel, add_zero] at this
    exact this
  simp only [quarterTurnField]
  rw [i3Z_add_tipVertex_eq h x, ← hper]
  ring

/-- **The harmonic translation by V_p.** `s` is the constant of `harmonicGrid_sub_V` with `p = −n_p`, `q = −d_p`. -/
theorem harmonicGrid_add_tipVertex (frame : ChildFrame) (x : Site) (s : ℤ)
    (hs : 2 * s = (-frame.parents.odd.num) + (-frame.parents.odd.den) -
      ((-frame.parents.odd.den) ^ 2 + 2 * (-frame.parents.odd.den) * (-frame.parents.odd.num) -
        (-frame.parents.odd.num) ^ 2)) :
    harmonicGrid (x + tipVertex frame) = harmonicGrid x + (frame.parents.odd.num * x.1 - frame.parents.odd.den * x.2 + s) := by
  have H := harmonicGrid_sub_V (-frame.parents.odd.num) (-frame.parents.odd.den) x.1 x.2 s (by linear_combination hs)
  have e : x + tipVertex frame =
      (x.1 - (-frame.parents.odd.num - -frame.parents.odd.den), x.2 - (-frame.parents.odd.num + -frame.parents.odd.den)) := by
    unfold tipVertex
    ext <;> simp <;> ring
  rw [e, H]
  ring

/-- **The harmonic translation by −V_q.** -/
theorem harmonicGrid_sub_Vq (frame : ChildFrame) (x : Site) (s : ℤ)
    (hs : 2 * s = frame.parents.even.num + frame.parents.even.den -
      (frame.parents.even.den ^ 2 + 2 * frame.parents.even.den * frame.parents.even.num - frame.parents.even.num ^ 2)) :
    harmonicGrid (x - (frame.parents.even.num - frame.parents.even.den, frame.parents.even.num + frame.parents.even.den)) =
      harmonicGrid x + (-frame.parents.even.num * x.1 + frame.parents.even.den * x.2 + s) := by
  have H := harmonicGrid_sub_V frame.parents.even.num frame.parents.even.den x.1 x.2 s (by linear_combination hs)
  exact H

/-- `harmonicGrid (2, 1) = 1`. -/
theorem harmonicGrid_two_one : harmonicGrid (2, 1) = 1 := by
  unfold harmonicGrid
  norm_num

/-! ### The sheets at the W0 east input -/

/-- The even parent's kernel is `(d_q, n_q)`. -/
theorem sheetShift_of_eps (frame : ChildFrame) (heps : frame.eps = -1) :
    frame.sheetShift = (frame.parents.even.den, frame.parents.even.num) := by
  unfold ChildFrame.sheetShift ChildFrame.phaseW
  rw [heps]
  simp [Fraction.unmodifiedDeck]

/-- The sheet offset is `V_q − U_q = (n_q − 2d_q, d_q)`. -/
theorem sheetOffset_of_eps (frame : ChildFrame) (heps : frame.eps = -1) :
    frame.sheetOffset = (frame.parents.even.num - 2 * frame.parents.even.den, frame.parents.even.den) := by
  unfold ChildFrame.sheetOffset
  rw [heps]
  simp [Fraction.unmodifiedDeck]
  ring

/-- The sheet constant is `(T_q − d_q − n_q)/2` when `eps = −1` (the phase is `0`). -/
theorem sheetConstant_of_eps (frame : ChildFrame) (heps : frame.eps = -1) :
    frame.sheetConstant = (frame.parents.even.periodDenominator - frame.parents.even.den - frame.parents.even.num) / 2 := by
  unfold ChildFrame.sheetConstant ChildFrame.phaseW
  rw [heps]
  norm_num

/-- The sheet `A` at `z` is the parent field at `z − U_q`. -/
theorem sheetA_of_eps (frame : ChildFrame) (Fp : Field) (heps : frame.eps = -1) (z : Site) :
    frame.sheetA Fp z = Fp (z - (frame.parents.even.den, frame.parents.even.num)) := by
  unfold ChildFrame.sheetA
  rw [sheetShift_of_eps frame heps]

/-- The sheet `C` at `z` is the parent field at `z − V_q`, plus the sibling slope and the constant. -/
theorem sheetC_of_eps (frame : ChildFrame) (Fp : Field) (heps : frame.eps = -1) (z : Site) :
    frame.sheetC Fp z = Fp (z - (frame.parents.even.num - frame.parents.even.den,
        frame.parents.even.num + frame.parents.even.den)) +
      (frame.parents.even.num * z.1 - frame.parents.even.den * z.2) + frame.sheetConstant := by
  unfold ChildFrame.sheetC
  rw [sheetShift_of_eps frame heps, sheetOffset_of_eps frame heps]
  have hsite : z - (frame.parents.even.den, frame.parents.even.num) -
      (frame.parents.even.num - 2 * frame.parents.even.den, frame.parents.even.den) =
      z - (frame.parents.even.num - frame.parents.even.den, frame.parents.even.num + frame.parents.even.den) := by
    ext <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> ring
  rw [hsite]
  unfold ChildFrame.siblingSlope
  simp only [Prod.fst_sub, Prod.snd_sub]
  ring

/-- The tip vertex's `s`-constant: `2 s = −n_p − d_p − T_p` is solvable. -/
theorem exists_tip_s (frame : ChildFrame) :
    ∃ s : ℤ, 2 * s = (-frame.parents.odd.num) + (-frame.parents.odd.den) -
      ((-frame.parents.odd.den) ^ 2 + 2 * (-frame.parents.odd.den) * (-frame.parents.odd.num) -
        (-frame.parents.odd.num) ^ 2) := by
  have h1 := Int.even_mul_succ_self frame.parents.odd.den
  have h2 := Int.even_mul_succ_self (frame.parents.odd.num - 1)
  have h3 : Even (2 * (frame.parents.odd.den * frame.parents.odd.num)) := even_two_mul _
  have e : (-frame.parents.odd.num) + (-frame.parents.odd.den) -
      ((-frame.parents.odd.den) ^ 2 + 2 * (-frame.parents.odd.den) * (-frame.parents.odd.num) -
        (-frame.parents.odd.num) ^ 2) =
      -(frame.parents.odd.den * (frame.parents.odd.den + 1)) +
        (frame.parents.odd.num - 1) * (frame.parents.odd.num - 1 + 1) -
          2 * (frame.parents.odd.den * frame.parents.odd.num) := by
    ring
  have hE : Even ((-frame.parents.odd.num) + (-frame.parents.odd.den) -
      ((-frame.parents.odd.den) ^ 2 + 2 * (-frame.parents.odd.den) * (-frame.parents.odd.num) -
        (-frame.parents.odd.num) ^ 2)) := by
    rw [e]
    exact ((h1.neg).add h2).sub h3
  obtain ⟨r, hr⟩ := hE
  exact ⟨r, by rw [hr]; ring⟩

/-- The even parent's `s`-constant: `2 s_q = n_q + d_q − T_q` is solvable. -/
theorem exists_even_s (frame : ChildFrame) :
    ∃ s : ℤ, 2 * s = frame.parents.even.num + frame.parents.even.den -
      (frame.parents.even.den ^ 2 + 2 * frame.parents.even.den * frame.parents.even.num -
        frame.parents.even.num ^ 2) := by
  have h1 := Int.even_mul_succ_self frame.parents.even.num
  have h2 := Int.even_mul_succ_self (frame.parents.even.den - 1)
  have h3 : Even (2 * (frame.parents.even.den * frame.parents.even.num)) := even_two_mul _
  have e : frame.parents.even.num + frame.parents.even.den -
      (frame.parents.even.den ^ 2 + 2 * frame.parents.even.den * frame.parents.even.num -
        frame.parents.even.num ^ 2) =
      frame.parents.even.num * (frame.parents.even.num + 1) -
        (frame.parents.even.den - 1) * (frame.parents.even.den - 1 + 1) -
          2 * (frame.parents.even.den * frame.parents.even.num) := by
    ring
  have hE : Even (frame.parents.even.num + frame.parents.even.den -
      (frame.parents.even.den ^ 2 + 2 * frame.parents.even.den * frame.parents.even.num -
        frame.parents.even.num ^ 2)) := by
    rw [e]
    exact (h1.sub h2).sub h3
  obtain ⟨r, hr⟩ := hE
  exact ⟨r, by rw [hr]; ring⟩

/-- The W0 east input `(2,1) + V_p` lies in the closed polygon (odd branch). -/
theorem tipEast_mem (frame : ChildFrame) (heps : frame.eps = -1) (hB0 : 0 ≤ tipB frame)
    (hB2 : 5 * (frame.child.den + frame.child.num) ≤ frame.child.periodDenominator - tipB frame) :
    ((2, 1) + tipVertex frame) ∈ frame.closedPolygon := by
  have hv := evenSite_tipVertex frame
  have hodd : ¬ EvenSite ((2, 1) + tipVertex frame) := by
    unfold EvenSite at hv ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  have hT := tGrade_tipVertex frame
  have hS := sGrade_tipVertex frame
  rw [heps] at hS
  obtain ⟨-, hN0, hND, -⟩ := period_facts frame
  have ht : frame.tGrade ((2, 1) + tipVertex frame) = -tipB frame + (2 * frame.child.num - frame.child.den) := by
    rw [← hT]
    unfold ChildFrame.tGrade
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  have hS' : frame.sGrade (tipVertex frame) = -2 := by
    rw [hS]
    norm_num
  have hsv : frame.sGrade ((2, 1) + tipVertex frame) =
      frame.sGrade (tipVertex frame) + (2 * (frame.child.den + frame.child.num) + (frame.child.den - frame.child.num)) := by
    unfold ChildFrame.sGrade
    simp only [Prod.fst_add, Prod.snd_add]
    unfold ChildFrame.sGrade at hS'
    ring
  have hs : frame.sGrade ((2, 1) + tipVertex frame) =
      -2 + (2 * (frame.child.den + frame.child.num) + (frame.child.den - frame.child.num)) := by
    rw [hsv, hS']
  rw [FLatticePaper.Induction.mem_closedPolygon_iff, if_neg hodd]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ht]
    linarith
  · rw [ht]
    linarith
  · rw [hs]
    linarith
  · rw [hs]
    linarith

/-- **The W0 east sheet value.** At `z = (2,1) + V_p`, the sheet minimum is the harmonic value: `F z = harmonicGrid z`. -/
theorem tipEast_standard {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpar : FLatticePaper.W1Seeds.SeedFields (conjWord word))
    (heps : (frameAt word).eps = -1) (hB0 : 0 ≤ tipB (frameAt word))
    (hB2 : 5 * ((frameAt word).child.den + (frameAt word).child.num) ≤
      (frameAt word).child.periodDenominator - tipB (frameAt word)) :
    standardField word ((2, 1) + tipVertex (frameAt word)) =
      harmonicGrid ((2, 1) + tipVertex (frameAt word)) := by
  obtain ⟨hTd, hN0, hND, -⟩ := period_facts (frameAt word)
  have hdet : (frameAt word).eps = (frameAt word).parents.odd.num * (frameAt word).parents.even.den -
      (frameAt word).parents.even.num * (frameAt word).parents.odd.den := rfl
  have hdp : 0 < (frameAt word).parents.odd.den := (frameAt word).valid.odd_bounds.1
  have hnp0 : 0 ≤ (frameAt word).parents.odd.num := (frameAt word).valid.odd_bounds.2.1
  have hcn : (frameAt word).child.num = 2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num :=
    ChildFrame.child_num_eq (frameAt word)
  have hcd : (frameAt word).child.den = 2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den :=
    ChildFrame.child_den_eq (frameAt word)
  have hprop : 2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num + 2 ≤
      2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den := by
    rw [hcn, hcd] at hND
    linarith
  have hnp_le : (frameAt word).parents.odd.num ≤ (frameAt word).parents.odd.den - 1 := by
    by_contra hc
    rw [not_le] at hc
    nlinarith [mul_le_mul_of_nonneg_left hprop hdp.le,
      mul_nonneg (show (0 : ℤ) ≤ (frameAt word).parents.odd.num - (frameAt word).parents.odd.den by omega)
        (show (0 : ℤ) ≤ 2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den by omega)]
  obtain ⟨s, hs⟩ := exists_tip_s (frameAt word)
  obtain ⟨sq, hsq⟩ := exists_even_s (frameAt word)
  have hmem := tipEast_mem (frameAt word) heps hB0 hB2
  rw [standardField_eq_sheetMin_of_strong h hSE hmem]
  unfold ChildFrame.sheetMin
  rw [sheetA_of_eps _ _ heps, sheetC_of_eps _ _ heps, sheetConstant_of_eps _ heps]
  -- the first sheet: `Fp (z − U_q) = harmonicGrid z`, through the zero band at `(2,1) − U_q`
  have hA : quarterTurnField (standardField (conjWord word))
      ((2, 1) + tipVertex (frameAt word) - ((frameAt word).parents.even.den, (frameAt word).parents.even.num)) =
      harmonicGrid ((2, 1) + tipVertex (frameAt word)) := by
    have hsite : (2, 1) + tipVertex (frameAt word) - ((frameAt word).parents.even.den, (frameAt word).parents.even.num) =
        (2 - (frameAt word).parents.even.den, 1 - (frameAt word).parents.even.num) + tipVertex (frameAt word) := by
      refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> ring
    have hz1 : 1 - (frameAt word).parents.odd.den ≤
        (frameAt word).parentTGrade (2 - (frameAt word).parents.even.den, 1 - (frameAt word).parents.even.num) := by
      unfold ChildFrame.parentTGrade
      simp only
      linarith
    have hz2 : (frameAt word).parentTGrade (2 - (frameAt word).parents.even.den, 1 - (frameAt word).parents.even.num) ≤
        (frameAt word).parents.odd.num + 2 * (frameAt word).parents.odd.den - 1 := by
      unfold ChildFrame.parentTGrade
      simp only
      linarith
    rw [hsite, quarterTurnField_add_tipVertex h hSE, zeroStrip_of_strong h hSE _ hz1 hz2,
      harmonicGrid_add_tipVertex (frameAt word) _ s hs, harmonicGrid_add_tipVertex (frameAt word) (2, 1) s hs,
      harmonicGrid_two_one]
    dsimp only
    linarith
  -- the second sheet: `Fp (z − V_q) = harmonicGrid (z − V_q)` through the harmonic band at `(2,1) − V_q`
  have hC : quarterTurnField (standardField (conjWord word))
      ((2, 1) + tipVertex (frameAt word) -
        ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
          (frameAt word).parents.even.num + (frameAt word).parents.even.den)) +
      ((frameAt word).parents.even.num * ((2, 1) + tipVertex (frameAt word)).1 -
        (frameAt word).parents.even.den * ((2, 1) + tipVertex (frameAt word)).2) +
      ((frameAt word).parents.even.periodDenominator - (frameAt word).parents.even.den -
        (frameAt word).parents.even.num) / 2 =
      harmonicGrid ((2, 1) + tipVertex (frameAt word)) := by
    have hsiteC : (2, 1) + tipVertex (frameAt word) -
        ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
          (frameAt word).parents.even.num + (frameAt word).parents.even.den) =
        ((2, 1) - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
          (frameAt word).parents.even.num + (frameAt word).parents.even.den)) + tipVertex (frameAt word) := by
      refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> ring
    have hbC_odd : ¬ EvenSite ((2, 1) - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
          (frameAt word).parents.even.num + (frameAt word).parents.even.den)) := by
      unfold EvenSite
      simp only [Prod.fst_sub, Prod.snd_sub]
      omega
    have hpS : (frameAt word).parentSGrade ((2, 1) - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
          (frameAt word).parents.even.num + (frameAt word).parents.even.den)) =
        3 * (frameAt word).parents.odd.den + (frameAt word).parents.odd.num - 2 := by
      unfold ChildFrame.parentSGrade
      simp only [Prod.fst_sub, Prod.snd_sub]
      linarith
    have hJ := FLatticePaper.W1Hstrong.hStrong_of_strong h hSE hpar _ hbC_odd (by linarith) (by linarith)
    rw [hsiteC, quarterTurnField_add_tipVertex h hSE, hJ]
    have hsiteC2 : ((2, 1) - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
          (frameAt word).parents.even.num + (frameAt word).parents.even.den)) + tipVertex (frameAt word) =
        (2, 1) + tipVertex (frameAt word) -
          ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
            (frameAt word).parents.even.num + (frameAt word).parents.even.den) := by
      refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> ring
    rw [hsiteC2, harmonicGrid_sub_Vq (frameAt word) ((2, 1) + tipVertex (frameAt word)) sq hsq]
    have hconst : ((frameAt word).parents.even.periodDenominator - (frameAt word).parents.even.den -
        (frameAt word).parents.even.num) / 2 = -sq := by
      have hT : (frameAt word).parents.even.periodDenominator =
          (frameAt word).parents.even.den ^ 2 + 2 * (frameAt word).parents.even.den * (frameAt word).parents.even.num -
            (frameAt word).parents.even.num ^ 2 := rfl
      rw [hT]
      have e : (frameAt word).parents.even.den ^ 2 + 2 * (frameAt word).parents.even.den * (frameAt word).parents.even.num -
            (frameAt word).parents.even.num ^ 2 - (frameAt word).parents.even.den - (frameAt word).parents.even.num =
          -2 * sq := by
        linarith
      rw [e]
      omega
    simp only [Prod.fst_add, Prod.snd_add]
    rw [hconst]
    linarith
  rw [hA, hC, min_self]

/-- **The W0 middle is white.** The middle `u = v + (1,1)` is even: its own value and its west input lie in the harmonic s-strip
(`s = −2 + 2d` and `s = −2 + c`), and its east input `(2,1) + v` has the harmonic value `tipEast_standard`. So the
horizontal star of `u` is harmonic and `laplacian F u = 0`. -/
theorem W0_middle_white {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpar : FLatticePaper.W1Seeds.SeedFields (conjWord word))
    (hP : (frameAt word).Packet (standardField word))
    (heps : (frameAt word).eps = -1) (hB0 : 0 ≤ tipB (frameAt word))
    (hB2 : 5 * ((frameAt word).child.den + (frameAt word).child.num) ≤
      (frameAt word).child.periodDenominator - tipB (frameAt word)) :
    laplacian (standardField word) (tipVertex (frameAt word) + (1, 1)) = 0 := by
  have hE := tipEast_standard h hSE hpar heps hB0 hB2
  have hv := evenSite_tipVertex (frameAt word)
  have hS' : (frameAt word).sGrade (tipVertex (frameAt word)) = -2 := by
    rw [sGrade_tipVertex, heps]
    norm_num
  obtain ⟨-, hN0, hND, -⟩ := period_facts (frameAt word)
  have hu_s : (frameAt word).sGrade (tipVertex (frameAt word) + (1, 1)) =
      -2 + (2 * (frameAt word).child.den) := by
    have e : (frameAt word).sGrade (tipVertex (frameAt word) + (1, 1)) =
        (frameAt word).sGrade (tipVertex (frameAt word)) +
          ((frameAt word).child.den + (frameAt word).child.num + ((frameAt word).child.den - (frameAt word).child.num)) := by
      unfold ChildFrame.sGrade
      simp only [Prod.fst_add, Prod.snd_add]
      ring
    rw [e, hS']
    ring
  have hw_s : (frameAt word).sGrade ((tipVertex (frameAt word) + (1, 1)).1 - 1, (tipVertex (frameAt word) + (1, 1)).2) =
      -2 + ((frameAt word).child.den - (frameAt word).child.num) := by
    have e : (frameAt word).sGrade ((tipVertex (frameAt word) + (1, 1)).1 - 1, (tipVertex (frameAt word) + (1, 1)).2) =
        (frameAt word).sGrade (tipVertex (frameAt word)) + ((frameAt word).child.den - (frameAt word).child.num) := by
      unfold ChildFrame.sGrade
      simp only [Prod.fst_add, Prod.snd_add]
      ring
    rw [e, hS']
  have hEu : EvenSite (tipVertex (frameAt word) + (1, 1)) := by
    unfold EvenSite at hv ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  have hsiteE : ((tipVertex (frameAt word) + (1, 1)).1 + 1, (tipVertex (frameAt word) + (1, 1)).2) =
      (2, 1) + tipVertex (frameAt word) := by
    refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
  have hu := (hP.strips).2 (tipVertex (frameAt word) + (1, 1))
    (by rw [hu_s]; linarith) (by rw [hu_s]; linarith)
  have hw := (hP.strips).2 ((tipVertex (frameAt word) + (1, 1)).1 - 1, (tipVertex (frameAt word) + (1, 1)).2)
    (by rw [hw_s]; linarith) (by rw [hw_s]; linarith)
  have he : standardField word ((tipVertex (frameAt word) + (1, 1)).1 + 1, (tipVertex (frameAt word) + (1, 1)).2) =
      harmonicGrid ((tipVertex (frameAt word) + (1, 1)).1 + 1, (tipVertex (frameAt word) + (1, 1)).2) := by
    rw [hsiteE]
    exact hE
  have hlapF : laplacian (standardField word) (tipVertex (frameAt word) + (1, 1)) =
      (standardField word ((tipVertex (frameAt word) + (1, 1)).1 - 1, (tipVertex (frameAt word) + (1, 1)).2) -
          standardField word (tipVertex (frameAt word) + (1, 1))) +
        (standardField word ((tipVertex (frameAt word) + (1, 1)).1 + 1, (tipVertex (frameAt word) + (1, 1)).2) -
          standardField word (tipVertex (frameAt word) + (1, 1))) := by
    unfold laplacian incomingNeg incomingPos
    simp only [if_pos hEu]
  have hH : (harmonicGrid ((tipVertex (frameAt word) + (1, 1)).1 - 1, (tipVertex (frameAt word) + (1, 1)).2) -
          harmonicGrid (tipVertex (frameAt word) + (1, 1))) +
        (harmonicGrid ((tipVertex (frameAt word) + (1, 1)).1 + 1, (tipVertex (frameAt word) + (1, 1)).2) -
          harmonicGrid (tipVertex (frameAt word) + (1, 1))) = 0 := by
    have := harmonicGrid_harmonic (tipVertex (frameAt word) + (1, 1))
    unfold laplacian incomingNeg incomingPos at this
    simp only [if_pos hEu] at this
    exact this
  rw [hlapF, hw, hu, he]
  linarith [hH]

end W0Sheets

end FLatticePaper.Induction
