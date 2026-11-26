import FLatticePaper.Plane.Induction.OppCore
import FLatticePaper.Plane.Induction.OppKernel
import FLatticePaper.Plane.Induction.OppParent
import FLatticePaper.Plane.Induction.OppWordCover
import FLatticePaper.Plane.Induction.OppAlg
import FLatticePaper.Plane.Induction.OppYBox
import FLatticePaper.Plane.Induction.W1CollarFrame
import FLatticePaper.Plane.Induction.SheetPieces
import FLatticePaper.Plane.Induction.W1ArcBottom
import FLatticePaper.Plane.Induction.Q3Para10
import FLatticePaper.Plane.Induction.Q3VStar
import FLatticePaper.Plane.Induction.W1Seeds
import FLatticePaper.Plane.Induction.W1Step
import FLatticePaper.Plane.Induction.SheetOffsets
import FLatticePaper.Plane.Induction.FaceWitness

/-! # The opposite sign: `Ψ ≤ 0` at an opposite point of the strict collar

For a strict centre `c` with a witness `v`, put `u = v − K` (`ε = +1`) or `u = v` (`ε = −1`), `(k, m) = c − v`, and
`Y = u + (k, m)`. Then `c = Y + K` (resp. `c = Y`) and:
* `C(c) = h₀(Y)` (`OppKernel`);
* `F(c) = h₀(Y)`: the field is kernel periodic with constant `0` (`ε = +1`), and `OppWordCover` gives `F(Y) = h₀(Y)`;
* `F = min(A, C)` on the closed polygon, so `C(c) = F(c) ≤ A(c)` and `Ψ = C − A ≤ 0`.
The case split is `OppCore`. The sign lemmas are stated in the coordinates `(u₁, u₂, k, m)`, so that `Y` and its projections reduce. -/

namespace FLatticePaper.OppMain

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1 FLatticePaper.W1Seeds FLatticePaper.W1Step
open FLatticePaper.W1OffCollar

/-- A strict centre lies in the closed rectangle. -/
theorem strict_closedRect {n d : ℤ} (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) {p : Site}
    (h : FLatticePaper.W1.StrictInterior n d p) : closedRect n d p := by
  rw [FLatticePaper.W1OffCollarCases.strict_grades] at h
  rw [closedRect_iff]
  generalize w1t n d p = t at h ⊢
  generalize w1s n d p = s at h ⊢
  generalize w1T n d = T at h ⊢
  unfold EvenSite at *
  omega

/-- **The opposite sign, `ε = +1`, at the coordinates `(u₁, u₂, k, m)`.** -/
theorem opp_plus_at {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hS : StrongCore word)
    (hpar : SeedFields word) (hpc : SeedFields (conjWord word)) (hSE : StrongEstimates (conjWord word))
    (hn3 : 3 ≤ (frameAt word).child.num) (hε : (frameAt word).eps = 1)
    (u1 u2 k m : ℤ) (hk : k = -1 ∨ k = 0 ∨ k = 1) (hm : m = -1 ∨ m = 0 ∨ m = 1)
    (hfree : FLatticePaper.W1OffCollar.freeVn (frameAt word).child.num (frameAt word).child.den (u1, u2))
    (hc : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den
      ((u1 + k, u2 + m) + ((frameAt word).child.den, (frameAt word).child.num))) :
    sheetPsi word ((u1 + k, u2 + m) + ((frameAt word).child.den, (frameAt word).child.num)) ≤ 0 := by
  have hK := ChildFrame.child_modifiedDeck_kernel (frameAt word)
  obtain ⟨-, -, hnd0, -, -⟩ := (frameAt word).child_facts
  have hnd : (frameAt word).child.num + 2 ≤ (frameAt word).child.den := by omega
  obtain ⟨hdv, hnv, hD0, hN0, hNlt, -, -, -, hL⟩ := ChildFrame.linear_facts (frameAt word)
  have hD2 := FLatticePaper.W1ArcBottom.odd_den_ge_two (frameAt word) hn3
  have hodd : ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den) % 2 = 1 :=
    (frameAt word).valid.odd_parity
  have hdetE := FLatticePaper.SheetOffsets.eps_eq_det (word := word)
  have hdet : (frameAt word).parents.odd.num * (frameAt word).parents.even.den -
      (frameAt word).parents.odd.den * (frameAt word).parents.even.num = 1 := by
    rw [hε] at hdetE
    linarith
  have hεND : (1 : ℤ) = (frameAt word).parents.odd.num * (frameAt word).child.den -
      (frameAt word).parents.odd.den * (frameAt word).child.num := by
    rw [hdv, hnv]
    linear_combination -hdet
  have hCd := FLatticePaper.OppAlg.CC_mul_d hεND
  have hCn := FLatticePaper.OppAlg.CC_mul_n hεND
  have hCL := FLatticePaper.OppAlg.CC_mul_L hεND
  have hTT : FLatticePaper.OppAlg.TT (frameAt word).child.num (frameAt word).child.den =
      w1T (frameAt word).child.num (frameAt word).child.den := by
    unfold FLatticePaper.OppAlg.TT w1T
    ring
  rw [hTT] at hCd hCn hCL
  obtain ⟨hcn', hcd'⟩ := FLatticePaper.Induction.frameAt_conj_num_den h
  have hcore := FLatticePaper.OppCore.core_plus (frameAt word).child.num (frameAt word).child.den
    (frameAt word).parents.odd.num (frameAt word).parents.odd.den
    (FLatticePaper.OppAlg.CC (frameAt word).parents.odd.num (frameAt word).parents.odd.den
      (frameAt word).child.num (frameAt word).child.den)
    (frameAt word).parents.even.num (frameAt word).parents.even.den u1 u2 k m
    (by omega) hn3 hnd hD2 hN0 (by omega) (by omega) hdet hCd hCn hCL hk hm hfree hc
  have hmem : (u1 + k, u2 + m) + ((frameAt word).child.den, (frameAt word).child.num) ∈
      (frameAt word).closedPolygon := by
    rw [FLatticePaper.W1.closedPolygon_eq_closedRect]
    exact strict_closedRect hn3 hnd hc
  have hmin := FLatticePaper.Induction.standardField_eq_sheetMin_of_strong h hSE hmem
  unfold ChildFrame.sheetMin at hmin
  have hle := min_le_left ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word)))
    ((u1 + k, u2 + m) + ((frameAt word).child.den, (frameAt word).child.num)))
    ((frameAt word).sheetC (quarterTurnField (standardField (conjWord word)))
    ((u1 + k, u2 + m) + ((frameAt word).child.den, (frameAt word).child.num)))
  rcases hcore with ⟨hYe, hWx, hCov⟩ | ⟨hYo, hWx, hCov⟩
  · -- the even point: the parent zero strip
    have hfx := FLatticePaper.OppParent.quarterTurn_h0_of_strip hSE (frameAt word).parents.odd.num
      (frameAt word).parents.odd.den hcn' hcd' ((u1 + k, u2 + m) - ((frameAt word).parents.even.num -
        (frameAt word).parents.even.den, (frameAt word).parents.even.num + (frameAt word).parents.even.den))
      (by simp only [Prod.fst_sub, Prod.snd_sub]; linarith [hWx.1]) (by simp only [Prod.fst_sub, Prod.snd_sub]; linarith [hWx.2])
    have hCc := FLatticePaper.OppKernel.sheetC_kernel_plus h hSE hε (u1 + k, u2 + m) hfx
    rw [hK] at hCc
    have hper := hS.packet.periods.1 (u1 + k, u2 + m)
    rw [FLatticePaper.Induction.coherentConstantU_eq_zero (frameAt word), add_zero, hK] at hper
    have hlo : 1 - 2 * (frameAt word).child.den ≤ (frameAt word).sGrade (u1 + k, u2 + m) := by
      unfold ChildFrame.sGrade
      try dsimp only
      linarith [hCov.1]
    have hhi : (frameAt word).sGrade (u1 + k, u2 + m) ≤
        2 * ((frameAt word).child.den + (frameAt word).child.num) - 1 := by
      unfold ChildFrame.sGrade
      try dsimp only
      linarith [hCov.2]
    have hF := FLatticePaper.OppWordCover.word_strip hS (u1 + k, u2 + m) hlo hhi
    unfold sheetPsi FLatticePaper.W1MSheet.FqW
    linarith
  · -- the odd point: the parent even zero
    have hfx := FLatticePaper.OppParent.quarterTurn_h0_of_even_zero hSE hpc (frameAt word).parents.odd.num
      (frameAt word).parents.odd.den hcn' hcd' ((u1 + k, u2 + m) - ((frameAt word).parents.even.num -
        (frameAt word).parents.even.den, (frameAt word).parents.even.num + (frameAt word).parents.even.den))
      (by simp only [EvenSite, Prod.fst_sub, Prod.snd_sub] at hYo ⊢; omega)
      (by simp only [Prod.fst_sub, Prod.snd_sub]; linarith [hWx.1]) (by simp only [Prod.fst_sub, Prod.snd_sub]; linarith [hWx.2])
    have hCc := FLatticePaper.OppKernel.sheetC_kernel_plus h hSE hε (u1 + k, u2 + m) hfx
    rw [hK] at hCc
    have hper := hS.packet.periods.1 (u1 + k, u2 + m)
    rw [FLatticePaper.Induction.coherentConstantU_eq_zero (frameAt word), add_zero, hK] at hper
    have hlo : 2 - 3 * (frameAt word).child.den + (frameAt word).child.num ≤
        (frameAt word).sGrade (u1 + k, u2 + m) := by
      unfold ChildFrame.sGrade
      try dsimp only
      linarith [hCov.1]
    have hhi : (frameAt word).sGrade (u1 + k, u2 + m) ≤
        3 * (frameAt word).child.den + (frameAt word).child.num - 2 := by
      unfold ChildFrame.sGrade
      try dsimp only
      linarith [hCov.2]
    have hF := FLatticePaper.OppWordCover.word_odd_cover hS hpar (u1 + k, u2 + m) hYo (by omega) hlo hhi
    unfold sheetPsi FLatticePaper.W1MSheet.FqW
    linarith

/-- **The opposite sign, `ε = −1`, at the coordinates `(u₁, u₂, k, m)`.** -/
theorem opp_minus_at {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hS : StrongCore word)
    (hpar : SeedFields word) (hpc : SeedFields (conjWord word)) (hSE : StrongEstimates (conjWord word))
    (hn3 : 3 ≤ (frameAt word).child.num) (hε : (frameAt word).eps = -1)
    (u1 u2 k m : ℤ) (hk : k = -1 ∨ k = 0 ∨ k = 1) (hm : m = -1 ∨ m = 0 ∨ m = 1)
    (hfree : FLatticePaper.W1OffCollar.freeVn (frameAt word).child.num (frameAt word).child.den (u1, u2))
    (hc : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den (u1 + k, u2 + m)) :
    sheetPsi word (u1 + k, u2 + m) ≤ 0 := by
  obtain ⟨-, -, hnd0, -, -⟩ := (frameAt word).child_facts
  have hnd : (frameAt word).child.num + 2 ≤ (frameAt word).child.den := by omega
  obtain ⟨hdv, hnv, hD0, hN0, hNlt, -, -, -, hL⟩ := ChildFrame.linear_facts (frameAt word)
  have hD2 := FLatticePaper.W1ArcBottom.odd_den_ge_two (frameAt word) hn3
  have hodd : ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den) % 2 = 1 :=
    (frameAt word).valid.odd_parity
  have hdetE := FLatticePaper.SheetOffsets.eps_eq_det (word := word)
  have hdet : (frameAt word).parents.odd.num * (frameAt word).parents.even.den -
      (frameAt word).parents.odd.den * (frameAt word).parents.even.num = -1 := by
    rw [hε] at hdetE
    linarith
  have hεND : (-1 : ℤ) = (frameAt word).parents.odd.num * (frameAt word).child.den -
      (frameAt word).parents.odd.den * (frameAt word).child.num := by
    rw [hdv, hnv]
    linear_combination -hdet
  have hCd := FLatticePaper.OppAlg.CC_mul_d hεND
  have hCn := FLatticePaper.OppAlg.CC_mul_n hεND
  have hCL := FLatticePaper.OppAlg.CC_mul_L hεND
  have hTT : FLatticePaper.OppAlg.TT (frameAt word).child.num (frameAt word).child.den =
      w1T (frameAt word).child.num (frameAt word).child.den := by
    unfold FLatticePaper.OppAlg.TT w1T
    ring
  rw [hTT] at hCd hCn hCL
  obtain ⟨hcn', hcd'⟩ := FLatticePaper.Induction.frameAt_conj_num_den h
  have hcore := FLatticePaper.OppCore.core_minus (frameAt word).child.num (frameAt word).child.den
    (frameAt word).parents.odd.num (frameAt word).parents.odd.den
    (FLatticePaper.OppAlg.CC (frameAt word).parents.odd.num (frameAt word).parents.odd.den
      (frameAt word).child.num (frameAt word).child.den)
    (frameAt word).parents.even.num (frameAt word).parents.even.den u1 u2 k m
    hn3 hnd hD2 hN0 (by omega) (by omega) hdet hCd hCn hCL hk hm hfree hc
  have hmem : (u1 + k, u2 + m) ∈ (frameAt word).closedPolygon := by
    rw [FLatticePaper.W1.closedPolygon_eq_closedRect]
    exact strict_closedRect hn3 hnd hc
  have hmin := FLatticePaper.Induction.standardField_eq_sheetMin_of_strong h hSE hmem
  unfold ChildFrame.sheetMin at hmin
  have hle := min_le_left ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) (u1 + k, u2 + m))
    ((frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) (u1 + k, u2 + m))
  rcases hcore with ⟨hYe, hWx, hCov⟩ | ⟨hYo, hWx, hCov⟩
  · have hfx := FLatticePaper.OppParent.quarterTurn_h0_of_strip hSE (frameAt word).parents.odd.num
      (frameAt word).parents.odd.den hcn' hcd' ((u1 + k, u2 + m) - ((frameAt word).parents.even.num -
        (frameAt word).parents.even.den, (frameAt word).parents.even.num + (frameAt word).parents.even.den))
      (by simp only [Prod.fst_sub, Prod.snd_sub]; linarith [hWx.1]) (by simp only [Prod.fst_sub, Prod.snd_sub]; linarith [hWx.2])
    have hCc := FLatticePaper.OppKernel.sheetC_minus_at_y hε (u1 + k, u2 + m) hfx
    have hlo : 1 - 2 * (frameAt word).child.den ≤ (frameAt word).sGrade (u1 + k, u2 + m) := by
      unfold ChildFrame.sGrade
      try dsimp only
      linarith [hCov.1]
    have hhi : (frameAt word).sGrade (u1 + k, u2 + m) ≤
        2 * ((frameAt word).child.den + (frameAt word).child.num) - 1 := by
      unfold ChildFrame.sGrade
      try dsimp only
      linarith [hCov.2]
    have hF := FLatticePaper.OppWordCover.word_strip hS (u1 + k, u2 + m) hlo hhi
    unfold sheetPsi FLatticePaper.W1MSheet.FqW
    linarith
  · have hfx := FLatticePaper.OppParent.quarterTurn_h0_of_even_zero hSE hpc (frameAt word).parents.odd.num
      (frameAt word).parents.odd.den hcn' hcd' ((u1 + k, u2 + m) - ((frameAt word).parents.even.num -
        (frameAt word).parents.even.den, (frameAt word).parents.even.num + (frameAt word).parents.even.den))
      (by simp only [EvenSite, Prod.fst_sub, Prod.snd_sub] at hYo ⊢; omega)
      (by simp only [Prod.fst_sub, Prod.snd_sub]; linarith [hWx.1]) (by simp only [Prod.fst_sub, Prod.snd_sub]; linarith [hWx.2])
    have hCc := FLatticePaper.OppKernel.sheetC_minus_at_y hε (u1 + k, u2 + m) hfx
    have hlo : 2 - 3 * (frameAt word).child.den + (frameAt word).child.num ≤
        (frameAt word).sGrade (u1 + k, u2 + m) := by
      unfold ChildFrame.sGrade
      try dsimp only
      linarith [hCov.1]
    have hhi : (frameAt word).sGrade (u1 + k, u2 + m) ≤
        3 * (frameAt word).child.den + (frameAt word).child.num - 2 := by
      unfold ChildFrame.sGrade
      try dsimp only
      linarith [hCov.2]
    have hF := FLatticePaper.OppWordCover.word_odd_cover hS hpar (u1 + k, u2 + m) hYo (by omega) hlo hhi
    unfold sheetPsi FLatticePaper.W1MSheet.FqW
    linarith

/-- **The opposite sign, `ε = +1`, from the witness.** -/
theorem opp_plus_w {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hS : StrongCore word)
    (hpar : SeedFields word) (hpc : SeedFields (conjWord word)) (hSE : StrongEstimates (conjWord word))
    (hn3 : 3 ≤ (frameAt word).child.num) (hε : (frameAt word).eps = 1) (c : Site)
    (hc : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hw : ∃ v : Site, |v.1 - c.1| ≤ 1 ∧ |v.2 - c.2| ≤ 1 ∧
      (v - (frameAt word).child.modifiedDeck.kernel) ∈ (frameAt word).freeV) :
    sheetPsi word c ≤ 0 := by
  have hK := ChildFrame.child_modifiedDeck_kernel (frameAt word)
  rw [hK] at hw
  obtain ⟨v, hv1, hv2, hvf⟩ := hw
  have hfree := (FLatticePaper.W1CollarFrame.freeV_iff (frameAt word) _).1 hvf
  have hab1 := abs_le.mp hv1
  have hab2 := abs_le.mp hv2
  have hk : c.1 - v.1 = -1 ∨ c.1 - v.1 = 0 ∨ c.1 - v.1 = 1 := by omega
  have hm : c.2 - v.2 = -1 ∨ c.2 - v.2 = 0 ∨ c.2 - v.2 = 1 := by omega
  have hcc : (v.1 - (frameAt word).child.den + (c.1 - v.1), v.2 - (frameAt word).child.num + (c.2 - v.2)) +
      ((frameAt word).child.den, (frameAt word).child.num) = c :=
    Prod.ext (show v.1 - (frameAt word).child.den + (c.1 - v.1) + (frameAt word).child.den = c.1 by ring)
      (show v.2 - (frameAt word).child.num + (c.2 - v.2) + (frameAt word).child.num = c.2 by ring)
  rw [← hcc]
  exact opp_plus_at h hS hpar hpc hSE hn3 hε (v.1 - (frameAt word).child.den) (v.2 - (frameAt word).child.num)
    (c.1 - v.1) (c.2 - v.2) hk hm hfree (by rw [hcc]; exact hc)

/-- **The opposite sign, `ε = −1`, from the witness.** -/
theorem opp_minus_w {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hS : StrongCore word)
    (hpar : SeedFields word) (hpc : SeedFields (conjWord word)) (hSE : StrongEstimates (conjWord word))
    (hn3 : 3 ≤ (frameAt word).child.num) (hε : (frameAt word).eps = -1) (c : Site)
    (hc : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hw : ∃ v : Site, |v.1 - c.1| ≤ 1 ∧ |v.2 - c.2| ≤ 1 ∧ v ∈ (frameAt word).freeV) :
    sheetPsi word c ≤ 0 := by
  obtain ⟨v, hv1, hv2, hvf⟩ := hw
  have hfree := (FLatticePaper.W1CollarFrame.freeV_iff (frameAt word) _).1 hvf
  have hab1 := abs_le.mp hv1
  have hab2 := abs_le.mp hv2
  have hk : c.1 - v.1 = -1 ∨ c.1 - v.1 = 0 ∨ c.1 - v.1 = 1 := by omega
  have hm : c.2 - v.2 = -1 ∨ c.2 - v.2 = 0 ∨ c.2 - v.2 = 1 := by omega
  have hcc : (v.1 + (c.1 - v.1), v.2 + (c.2 - v.2)) = c := Prod.ext (by (try dsimp only); ring) (by (try dsimp only); ring)
  rw [← hcc]
  exact opp_minus_at h hS hpar hpc hSE hn3 hε v.1 v.2 (c.1 - v.1) (c.2 - v.2) hk hm hfree (by rw [hcc]; exact hc)

/-- **The opposite sign.** At a strict centre with an opposite witness, `Ψ ≤ 0`. -/
theorem opposite_sheetPsi {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hS : StrongCore word)
    (hpar : SeedFields word) (hpc : SeedFields (conjWord word)) (hSE : StrongEstimates (conjWord word))
    (hn3 : 3 ≤ (frameAt word).child.num) (c : Site)
    (hc : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hopp : FLatticePaper.FaceWitness.OppositeWit (frameAt word) c) :
    sheetPsi word c ≤ 0 := by
  unfold FLatticePaper.FaceWitness.OppositeWit at hopp
  rcases hopp with ⟨hε, hw⟩ | ⟨hε, hw⟩
  · exact opp_plus_w h hS hpar hpc hSE hn3 hε c hc hw
  · exact opp_minus_w h hS hpar hpc hSE hn3 hε c hc hw

end FLatticePaper.OppMain
