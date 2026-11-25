import FLatticePaper.Plane.Induction.FreeHPrice
import FLatticePaper.Plane.Induction.ReflectedFan

/-! The phase-one membership at the reflected neighbour: `reflH (r + prescribedH η r) + tip ∈ closedPolygon` for sign `ε = +1`.

The reflection `reflH z = (d+1−z₁, n−1−z₂)` acts on the grades by `tGrade (reflH z) = (n + d) − tGrade z` and
`sGrade (reflH z) = T + 2n − sGrade z` (with `T = d² + 2dn − n²`), and preserves the parity of a site (`n + d` is even). -/

namespace FLatticePaper.TipReflect

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.Induction.TipVertex FLatticePaper.FreeHPrice

/-- Two more bounds of the tip shift `c_t = n(N−D) − d(N+D)`: `c_t ≤ n − d − 2` and `2n − 2 ≤ T + c_t`. -/
theorem tip_bounds_refl (n d N D nq dq T : ℤ) (hN1 : 1 ≤ N) (hND : N < D) (hD2 : 2 ≤ D) (hnq : 0 ≤ nq)
    (hdq : 0 ≤ dq) (hn : n = 2 * N + nq) (hd : d = 2 * D + dq) (hnd : n + 2 ≤ d)
    (hT : T = d * d + 2 * d * n - n * n) :
    n * (N - D) - d * (N + D) ≤ n - d - 2 ∧ 2 * n - 2 ≤ T + (n * (N - D) - d * (N + D)) := by
  have hn0 : 0 ≤ n := by omega
  have hd0 : 0 ≤ d := by omega
  have hk : 0 ≤ d - n := by omega
  have hDN : 0 ≤ D - N - 1 := by omega
  have hNDm : 0 ≤ N + D - 3 := by omega
  constructor
  · nlinarith [mul_nonneg hn0 hDN, mul_nonneg hd0 hNDm]
  · rw [hT]
    nlinarith [mul_nonneg hn0 (show (0:ℤ) ≤ d - 2 * D by omega), mul_nonneg hk (show (0:ℤ) ≤ d - 2 * D by omega),
      mul_nonneg hk (show (0:ℤ) ≤ n - 2 * N by omega), mul_nonneg hn0 hk, sq_nonneg (n - 1), sq_nonneg (d - n),
      sq_nonneg n]

/-- **The phase-one membership at the reflected neighbour.** For a free H root `r` and its prescribed neighbour `i`, the point
`reflH i + tip` lies in `closedPolygon` when `ε = +1`. -/
theorem tip_closed_reflH_W1 (frame : ChildFrame) (hN1 : 1 ≤ frame.parents.odd.num)
    (hND : frame.parents.odd.num < frame.parents.odd.den) (hD2 : 2 ≤ frame.parents.odd.den)
    (hnq : 0 ≤ frame.parents.even.num) (hdq : 0 ≤ frame.parents.even.den)
    (hn_eq : frame.child.num = 2 * frame.parents.odd.num + frame.parents.even.num)
    (hd_eq : frame.child.den = 2 * frame.parents.odd.den + frame.parents.even.den)
    (heps : frame.eps = frame.parents.odd.num * frame.parents.even.den - frame.parents.even.num * frame.parents.odd.den)
    (hε : frame.eps = 1) {r : Site} (hr : r ∈ frame.freeH) {η : ℤ} (hη : η = 1 ∨ η = -1) :
    ReflectedFan.reflH frame (r + frame.prescribedH η r) + tipVertex frame ∈ frame.closedPolygon := by
  obtain ⟨hn0, hnd, -, -, -⟩ := frame.child_facts
  obtain ⟨hco1, hco2⟩ := frame.child_odd
  have hnd2 : frame.child.num + 2 ≤ frame.child.den := by omega
  obtain ⟨hb1, hb2, hb3, hb4⟩ := FLatticePaper.Induction.FreeTraceBox.freeH_box frame hr
  have hsp := hr.2.2
  unfold ChildFrame.hSpectrum at hsp
  have hpar : frame.tGrade r % 2 = (r.1 + r.2) % 2 := by
    unfold ChildFrame.tGrade
    rw [Int.sub_emod, Int.mul_emod, Int.mul_emod frame.child.den, hco1, hco2]
    omega
  have hTdef : frame.child.periodDenominator = frame.child.den * frame.child.den +
      2 * frame.child.den * frame.child.num - frame.child.num * frame.child.num := by
    unfold Fraction.periodDenominator
    ring
  obtain ⟨hA0, hC0, hB0, hD0⟩ := tip_bounds frame.child.num frame.child.den frame.parents.odd.num
    frame.parents.odd.den frame.parents.even.num frame.parents.even.den frame.child.periodDenominator
    hN1 hND hD2 hnq hdq hn_eq hd_eq hnd2 hTdef
  obtain ⟨hR1, hR2⟩ := tip_bounds_refl frame.child.num frame.child.den frame.parents.odd.num
    frame.parents.odd.den frame.parents.even.num frame.parents.even.den frame.child.periodDenominator
    hN1 hND hD2 hnq hdq hn_eq hd_eq hnd2 hTdef
  have htipT : ∀ z : Site, frame.tGrade (z + tipVertex frame) = frame.tGrade z +
      (frame.child.num * (frame.parents.odd.num - frame.parents.odd.den) -
        frame.child.den * (frame.parents.odd.num + frame.parents.odd.den)) := by
    intro z
    unfold ChildFrame.tGrade tipVertex
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  have htipS : ∀ z : Site, frame.sGrade (z + tipVertex frame) = frame.sGrade z + 2 * frame.eps := by
    intro z
    unfold ChildFrame.sGrade tipVertex
    simp only [Prod.fst_add, Prod.snd_add]
    rw [heps, hn_eq, hd_eq]
    ring
  have hreflT : ∀ z : Site, frame.tGrade (ReflectedFan.reflH frame z) = frame.child.num + frame.child.den -
      frame.tGrade z := by
    intro z
    unfold ChildFrame.tGrade ReflectedFan.reflH
    ring
  have hreflS : ∀ z : Site, frame.sGrade (ReflectedFan.reflH frame z) =
      frame.child.periodDenominator + 2 * frame.child.num - frame.sGrade z := by
    intro z
    rw [hTdef]
    unfold ChildFrame.sGrade ReflectedFan.reflH
    ring
  have hsr : frame.sGrade r = (frame.child.den + frame.child.num) * r.1 + (frame.child.den - frame.child.num) * r.2 := by
    unfold ChildFrame.sGrade
    ring
  have hS : frame.child.den + frame.child.num ≤ frame.sGrade r ∧ frame.sGrade r ≤
      frame.child.den * frame.child.den + 2 * frame.child.den * frame.child.num - frame.child.num * frame.child.num
        - frame.child.den + frame.child.num := by
    rw [hsr]
    exact FLatticePaper.PriceInputs.s_box frame.child.num frame.child.den r.1 r.2 hn0 hnd2 hb1 hb2 hb3 hb4
  by_cases h1 : r = hFirst
  · subst h1
    rw [ChildFrame.prescribedH_hFirst]
    rcases hη with rfl | rfl
    · have e1 : frame.tGrade (hFirst + (0, -1)) = frame.child.num + frame.child.den := by
        unfold ChildFrame.tGrade hFirst
        simp only [Prod.fst_add, Prod.snd_add]
        ring
      have e2 : frame.sGrade (hFirst + (0, -1)) = 2 * frame.child.num := by
        unfold ChildFrame.sGrade hFirst
        simp only [Prod.fst_add, Prod.snd_add]
        ring
      have hev : EvenSite (ReflectedFan.reflH frame (hFirst + (0, -1)) + tipVertex frame) := by
        unfold EvenSite ReflectedFan.reflH tipVertex hFirst
        simp only [Prod.fst_add, Prod.snd_add]
        omega
      rw [frame.mem_closedPolygon_iff]
      refine Or.inl ⟨hev, ?_, ?_, ?_, ?_⟩
      · rw [htipT, hreflT, e1]; linarith
      · rw [htipT, hreflT, e1]; linarith
      · rw [htipS, hreflS, e2, hε]; linarith
      · rw [htipS, hreflS, e2, hε]; linarith
    · have e1 : frame.tGrade (hFirst + (0, -(-1))) = frame.child.num - frame.child.den := by
        unfold ChildFrame.tGrade hFirst
        simp only [Prod.fst_add, Prod.snd_add]
        ring
      have e2 : frame.sGrade (hFirst + (0, -(-1))) = 2 * frame.child.den := by
        unfold ChildFrame.sGrade hFirst
        simp only [Prod.fst_add, Prod.snd_add]
        ring
      have hev : EvenSite (ReflectedFan.reflH frame (hFirst + (0, -(-1))) + tipVertex frame) := by
        unfold EvenSite ReflectedFan.reflH tipVertex hFirst
        simp only [Prod.fst_add, Prod.snd_add]
        omega
      rw [frame.mem_closedPolygon_iff]
      refine Or.inl ⟨hev, ?_, ?_, ?_, ?_⟩
      · rw [htipT, hreflT, e1]; linarith
      · rw [htipT, hreflT, e1]; linarith
      · rw [htipS, hreflS, e2, hε]; linarith
      · rw [htipS, hreflS, e2, hε]; linarith
  · by_cases he : EvenSite r
    · unfold EvenSite at he
      rw [FLatticePaper.FreePolicy.pH_even frame η he]
      have ht_e : 2 ≤ frame.tGrade r ∧ frame.tGrade r ≤ frame.child.den + frame.child.num - 2 := by
        rcases hsp with ⟨h1', h2, h3⟩ | ⟨h1', h2, h3⟩ <;> omega
      have e1 : frame.tGrade (r + (1, 0)) = frame.tGrade r + frame.child.num := by
        unfold ChildFrame.tGrade
        simp only [Prod.fst_add, Prod.snd_add]
        ring
      have e2 : frame.sGrade (r + (1, 0)) = frame.sGrade r + (frame.child.den + frame.child.num) := by
        unfold ChildFrame.sGrade
        simp only [Prod.fst_add, Prod.snd_add]
        ring
      have hnev : ¬ EvenSite (ReflectedFan.reflH frame (r + (1, 0)) + tipVertex frame) := by
        unfold EvenSite ReflectedFan.reflH tipVertex
        simp only [Prod.fst_add, Prod.snd_add]
        omega
      rw [frame.mem_closedPolygon_iff]
      refine Or.inr ⟨hnev, ?_, ?_, ?_, ?_⟩
      · rw [htipT, hreflT, e1]; linarith [ht_e.1, ht_e.2, hS.1, hS.2, hA0, hC0, hR1, hR2, hD0, hTdef]
      · rw [htipT, hreflT, e1]; linarith [ht_e.1, ht_e.2, hS.1, hS.2, hA0, hC0, hR1, hR2, hD0, hTdef]
      · rw [htipS, hreflS, e2, hε]; linarith [ht_e.1, ht_e.2, hS.1, hS.2, hTdef]
      · rw [htipS, hreflS, e2, hε]; linarith [ht_e.1, ht_e.2, hS.1, hS.2, hTdef]
    · unfold EvenSite at he
      rw [FLatticePaper.FreePolicy.pH_odd' frame η he h1]
      have ht_o : frame.child.num ≤ frame.tGrade r ∧ frame.tGrade r ≤ frame.child.den := by
        rcases hsp with ⟨h1', h2, h3⟩ | ⟨h1', h2, h3⟩ <;> omega
      have e1 : frame.tGrade (r + (0, 1)) = frame.tGrade r - frame.child.den := by
        unfold ChildFrame.tGrade
        simp only [Prod.fst_add, Prod.snd_add]
        ring
      have e2 : frame.sGrade (r + (0, 1)) = frame.sGrade r + (frame.child.den - frame.child.num) := by
        unfold ChildFrame.sGrade
        simp only [Prod.fst_add, Prod.snd_add]
        ring
      have hev : EvenSite (ReflectedFan.reflH frame (r + (0, 1)) + tipVertex frame) := by
        unfold EvenSite ReflectedFan.reflH tipVertex
        simp only [Prod.fst_add, Prod.snd_add]
        omega
      rw [frame.mem_closedPolygon_iff]
      refine Or.inl ⟨hev, ?_, ?_, ?_, ?_⟩
      · rw [htipT, hreflT, e1]; linarith [ht_o.1, ht_o.2, hS.1, hS.2, hR1, hR2, hD0, hTdef]
      · rw [htipT, hreflT, e1]; linarith [ht_o.1, ht_o.2, hS.1, hS.2, hR1, hR2, hD0, hTdef]
      · rw [htipS, hreflS, e2, hε]; linarith [hS.1, hS.2, hTdef]
      · rw [htipS, hreflS, e2, hε]; linarith [hS.1, hS.2, hTdef]

end FLatticePaper.TipReflect
