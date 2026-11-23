import FLatticePaper.Plane.Induction.W1Exit
import FLatticePaper.Plane.Induction.W1Constructor
import FLatticePaper.Plane.Induction.S3FreeBoundary
import FLatticePaper.Plane.Induction.S3Canonical

/-! Task 72 (nonfree bridge): a nonfree site has a deck translate in the strict interior.

* `Nonfree frame z`: no deck translate of `z` lies in the free H or V set (`ChildFrame.freeH`, `ChildFrame.freeV`).
* `outside_SI_free`: a point of the closed polygon outside `StrictInterior` is free, or its translate by `−V` or `−K` is free:
  the deck vectors `K = (d, n)` (shifts `s` by `T`) and `V = (n − d, n + d)` (shifts `t` by `−T`) move the outside strips onto the
  free H and V traces.
* `nonfree_bridge`: a nonfree site has a deck translate in `StrictInterior` (the translate lies in the closed polygon, by
  `exists_shift_mem`). -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- The kernel deck vector `K = (d, n)`: it shifts the grade `s` by `T` and fixes `t`. -/
def Kdeck (frame : ChildFrame) : Site := (frame.child.den, frame.child.num)

/-- The transverse deck vector `V = (n − d, n + d)`: it shifts the grade `t` by `−T` and fixes `s`. -/
def Vdeck (frame : ChildFrame) : Site := (frame.child.num - frame.child.den, frame.child.num + frame.child.den)

/-- A site is nonfree when no deck translate of it lies in the free H or V set. -/
def Nonfree (frame : ChildFrame) (z : Site) : Prop :=
  ∀ v ∈ frame.child.modifiedDeck.span, z + v ∉ frame.freeH ∪ frame.freeV

theorem mem_closedPolygon_iff (frame : ChildFrame) (z : Site) :
    z ∈ frame.closedPolygon ↔
      (if EvenSite z then
        2 - frame.child.periodDenominator ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den + frame.child.num - 2 ∧
          0 ≤ frame.sGrade z ∧ frame.sGrade z ≤ frame.child.periodDenominator + 2 * frame.child.num
      else
        frame.child.num - frame.child.periodDenominator ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den ∧
          2 - frame.child.den + frame.child.num ≤ frame.sGrade z ∧
          frame.sGrade z ≤ frame.child.periodDenominator + frame.child.den + frame.child.num - 2) :=
  Iff.rfl

theorem tGrade_parity (frame : ChildFrame) (z : Site) : frame.tGrade z % 2 = (z.1 + z.2) % 2 := by
  obtain ⟨hn, hd⟩ := FLatticePaper.W1Exit.child_parity frame
  obtain ⟨a, ha⟩ : ∃ a, frame.child.num = 2 * a + 1 := ⟨frame.child.num / 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, frame.child.den = 2 * b + 1 := ⟨frame.child.den / 2, by omega⟩
  have key : ∃ k, frame.tGrade z = (z.1 + z.2) + 2 * k := by
    refine ⟨a * z.1 - b * z.2 - z.2, ?_⟩
    unfold ChildFrame.tGrade
    rw [ha, hb]
    ring
  obtain ⟨k, hk⟩ := key
  omega

theorem sGrade_even (frame : ChildFrame) (z : Site) : frame.sGrade z % 2 = 0 := by
  obtain ⟨hn, hd⟩ := FLatticePaper.W1Exit.child_parity frame
  obtain ⟨a, ha⟩ : ∃ a, frame.child.num = 2 * a + 1 := ⟨frame.child.num / 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, frame.child.den = 2 * b + 1 := ⟨frame.child.den / 2, by omega⟩
  have key : ∃ k, frame.sGrade z = 2 * k := by
    refine ⟨(a + b + 1) * z.1 + (b - a) * z.2, ?_⟩
    unfold ChildFrame.sGrade
    rw [ha, hb]
    ring
  obtain ⟨k, hk⟩ := key
  omega

theorem tGrade_add_negV (frame : ChildFrame) (w : Site) :
    frame.tGrade (w + -Vdeck frame) = frame.tGrade w + frame.child.periodDenominator := by
  unfold ChildFrame.tGrade Vdeck Fraction.periodDenominator
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg]
  ring

theorem sGrade_add_negV (frame : ChildFrame) (w : Site) :
    frame.sGrade (w + -Vdeck frame) = frame.sGrade w := by
  unfold ChildFrame.sGrade Vdeck
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg]
  ring

theorem tGrade_add_negK (frame : ChildFrame) (w : Site) :
    frame.tGrade (w + -Kdeck frame) = frame.tGrade w := by
  unfold ChildFrame.tGrade Kdeck
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg]
  ring

theorem sGrade_add_negK (frame : ChildFrame) (w : Site) :
    frame.sGrade (w + -Kdeck frame) = frame.sGrade w - frame.child.periodDenominator := by
  unfold ChildFrame.sGrade Kdeck Fraction.periodDenominator
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg]
  ring

theorem evenSite_add_negV (frame : ChildFrame) (w : Site) :
    EvenSite (w + -Vdeck frame) ↔ EvenSite w := by
  obtain ⟨hn, hd⟩ := FLatticePaper.W1Exit.child_parity frame
  unfold EvenSite Vdeck
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg]
  omega

theorem evenSite_add_negK (frame : ChildFrame) (w : Site) :
    EvenSite (w + -Kdeck frame) ↔ EvenSite w := by
  obtain ⟨hn, hd⟩ := FLatticePaper.W1Exit.child_parity frame
  unfold EvenSite Kdeck
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg]
  omega

/-- The site below `z` (`(z.1, z.2 − 1)`) is outside `E` when `z` is even and `t(z) ≥ 2`. -/
theorem not_mem_below_even (frame : ChildFrame) (z : Site) (hz : EvenSite z) (ht : 2 ≤ frame.tGrade z) :
    (z.1, z.2 - 1) ∉ frame.closedPolygon := by
  intro hmem
  rw [mem_closedPolygon_iff] at hmem
  have hodd : ¬ EvenSite (z.1, z.2 - 1) := by
    unfold EvenSite at hz ⊢
    simp only
    omega
  rw [if_neg hodd] at hmem
  have e : frame.tGrade (z.1, z.2 - 1) = frame.tGrade z + frame.child.den := by
    unfold ChildFrame.tGrade
    ring
  obtain ⟨-, h2, -⟩ := hmem
  rw [e] at h2
  have hpos : 0 < frame.child.den := by linarith [frame.child_facts.2.2.2.1]
  linarith

/-- The site below `z` is outside `E` when `z` is odd and `t(z) ≥ n`. -/
theorem not_mem_below_odd (frame : ChildFrame) (z : Site) (hz : ¬ EvenSite z) (ht : frame.child.num ≤ frame.tGrade z) :
    (z.1, z.2 - 1) ∉ frame.closedPolygon := by
  intro hmem
  rw [mem_closedPolygon_iff] at hmem
  have hev : EvenSite (z.1, z.2 - 1) := by
    unfold EvenSite at hz ⊢
    simp only at hz ⊢
    omega
  rw [if_pos hev] at hmem
  have e : frame.tGrade (z.1, z.2 - 1) = frame.tGrade z + frame.child.den := by
    unfold ChildFrame.tGrade
    ring
  obtain ⟨-, h2, -, -⟩ := hmem
  rw [e] at h2
  have hn := frame.child_facts.1
  have hd := frame.child_facts.2.2.2.1
  have hdn := frame.child_facts.2.2.1
  linarith

/-- The site to the left of `z` (`(z.1 − 1, z.2)`) is outside `E` when `z` is even and `s(z) ≤ 2n`. -/
theorem not_mem_left_even (frame : ChildFrame) (z : Site) (hz : EvenSite z) (hs : frame.sGrade z ≤ 2 * frame.child.num) :
    (z.1 - 1, z.2) ∉ frame.closedPolygon := by
  intro hmem
  rw [mem_closedPolygon_iff] at hmem
  have hodd : ¬ EvenSite (z.1 - 1, z.2) := by
    unfold EvenSite at hz ⊢
    simp only at hz ⊢
    omega
  rw [if_neg hodd] at hmem
  have e : frame.sGrade (z.1 - 1, z.2) = frame.sGrade z - (frame.child.den + frame.child.num) := by
    unfold ChildFrame.sGrade
    ring
  obtain ⟨-, -, h3, -⟩ := hmem
  rw [e] at h3
  have hn := frame.child_facts.1
  have hdn := frame.child_facts.2.2.1
  linarith

/-- The site to the left of `z` is outside `E` when `z` is odd and `s(z) ≤ d + n − 2`. -/
theorem not_mem_left_odd (frame : ChildFrame) (z : Site) (hz : ¬ EvenSite z)
    (hs : frame.sGrade z ≤ frame.child.den + frame.child.num - 2) :
    (z.1 - 1, z.2) ∉ frame.closedPolygon := by
  intro hmem
  rw [mem_closedPolygon_iff] at hmem
  have hev : EvenSite (z.1 - 1, z.2) := by
    unfold EvenSite at hz ⊢
    simp only at hz ⊢
    omega
  rw [if_pos hev] at hmem
  have e : frame.sGrade (z.1 - 1, z.2) = frame.sGrade z - (frame.child.den + frame.child.num) := by
    unfold ChildFrame.sGrade
    ring
  obtain ⟨-, -, h3, -⟩ := hmem
  rw [e] at h3
  linarith


/-- The strict interior at an even site, in the grades. -/
theorem SI_even_iff (frame : ChildFrame) (w : Site) (hw : EvenSite w) :
    FLatticePaper.W1.StrictInterior frame.child.num frame.child.den w ↔
      frame.child.den + frame.child.num - 2 - frame.child.periodDenominator < frame.tGrade w ∧ frame.tGrade w < 2 ∧
        2 * frame.child.num < frame.sGrade w ∧ frame.sGrade w < frame.child.periodDenominator := by
  unfold FLatticePaper.W1.StrictInterior FLatticePaper.W1.w1b FLatticePaper.W1.w1a FLatticePaper.W1.w1h
    FLatticePaper.W1.w1c FLatticePaper.W1.w1T FLatticePaper.W1.w1t FLatticePaper.W1.w1s
    ChildFrame.tGrade ChildFrame.sGrade
  simp only [if_pos hw, add_zero]
  unfold Fraction.periodDenominator
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨by linarith, h2, h3, by linarith⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨by linarith, h2, h3, by linarith⟩

/-- The strict interior at an odd site, in the grades. -/
theorem SI_odd_iff (frame : ChildFrame) (w : Site) (hw : ¬ EvenSite w) :
    FLatticePaper.W1.StrictInterior frame.child.num frame.child.den w ↔
      frame.child.den - frame.child.periodDenominator < frame.tGrade w ∧ frame.tGrade w < frame.child.num ∧
        frame.child.den + frame.child.num - 2 < frame.sGrade w ∧
        frame.sGrade w < frame.child.periodDenominator + (2 - frame.child.den + frame.child.num) := by
  unfold FLatticePaper.W1.StrictInterior FLatticePaper.W1.w1b FLatticePaper.W1.w1a FLatticePaper.W1.w1h
    FLatticePaper.W1.w1c FLatticePaper.W1.w1T FLatticePaper.W1.w1t FLatticePaper.W1.w1s
    ChildFrame.tGrade ChildFrame.sGrade
  simp only [if_neg hw]
  unfold Fraction.periodDenominator
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨by linarith, h2, h3, by linarith⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨by linarith, h2, h3, by linarith⟩

theorem mem_freeH_of (frame : ChildFrame) (z : Site) (h1 : z ∈ frame.closedPolygon)
    (h2 : (z.1, z.2 - 1) ∉ frame.closedPolygon) (h3 : frame.hSpectrum (frame.tGrade z)) : z ∈ frame.freeH := by
  show z ∈ frame.closedPolygon ∧ (z.1, z.2 - 1) ∉ frame.closedPolygon ∧ frame.hSpectrum (frame.tGrade z)
  exact ⟨h1, h2, h3⟩

theorem mem_freeV_of (frame : ChildFrame) (z : Site) (h1 : z ∈ frame.closedPolygon)
    (h2 : (z.1 - 1, z.2) ∉ frame.closedPolygon) (h3 : frame.vSpectrum (frame.sGrade z)) : z ∈ frame.freeV := by
  show z ∈ frame.closedPolygon ∧ (z.1 - 1, z.2) ∉ frame.closedPolygon ∧ frame.vSpectrum (frame.sGrade z)
  exact ⟨h1, h2, h3⟩

theorem hSpec_even (frame : ChildFrame) (z : Site) (hz : EvenSite z) (h1 : 2 ≤ frame.tGrade z)
    (h2 : frame.tGrade z ≤ frame.child.den + frame.child.num - 2) : frame.hSpectrum (frame.tGrade z) := by
  unfold ChildFrame.hSpectrum
  refine Or.inl ⟨?_, h1, h2⟩
  rw [tGrade_parity]
  exact hz

theorem hSpec_odd (frame : ChildFrame) (z : Site) (hz : ¬ EvenSite z) (h1 : frame.child.num ≤ frame.tGrade z)
    (h2 : frame.tGrade z ≤ frame.child.den) : frame.hSpectrum (frame.tGrade z) := by
  unfold ChildFrame.hSpectrum
  refine Or.inr ⟨?_, h1, h2⟩
  rw [tGrade_parity]
  unfold EvenSite at hz
  omega

theorem vSpec_even (frame : ChildFrame) (z : Site) (h : (0 ≤ frame.sGrade z ∧ frame.sGrade z ≤ 2 * frame.child.num) ∨
    (2 - frame.child.den + frame.child.num ≤ frame.sGrade z ∧ frame.sGrade z ≤ frame.child.den + frame.child.num - 2)) :
    frame.vSpectrum (frame.sGrade z) :=
  ⟨sGrade_even frame z, h⟩

/-- The deck vectors `K` and `V` lie in the span of the child deck. -/
theorem Kdeck_mem_span (frame : ChildFrame) : Kdeck frame ∈ frame.child.modifiedDeck.span :=
  ⟨1, 0, by ext <;> simp [PeriodDeck.combine, Kdeck, ChildFrame.child_modifiedDeck_kernel]⟩

theorem Vdeck_mem_span (frame : ChildFrame) : Vdeck frame ∈ frame.child.modifiedDeck.span :=
  ⟨0, 1, by ext <;> simp [PeriodDeck.combine, Vdeck, ChildFrame.child_modifiedDeck_transverse]⟩

theorem span_add_mem {frame : ChildFrame} {v w : Site} (hv : v ∈ frame.child.modifiedDeck.span)
    (hw : w ∈ frame.child.modifiedDeck.span) : v + w ∈ frame.child.modifiedDeck.span := by
  obtain ⟨i, j, rfl⟩ := hv
  obtain ⟨i', j', rfl⟩ := hw
  exact ⟨i + i', j + j', by ext <;> simp [PeriodDeck.combine] <;> ring⟩

theorem span_neg_mem {frame : ChildFrame} {v : Site} (hv : v ∈ frame.child.modifiedDeck.span) :
    -v ∈ frame.child.modifiedDeck.span := by
  obtain ⟨i, j, rfl⟩ := hv
  exact ⟨-i, -j, by ext <;> simp [PeriodDeck.combine] <;> ring⟩

theorem periodDenominator_pos (frame : ChildFrame) : 0 < frame.child.periodDenominator := by
  obtain ⟨h1, h2, -, -, hT⟩ := frame.child_facts
  rw [hT]
  nlinarith

/-- **The strict-interior case analysis.** A point of the closed polygon outside `StrictInterior` is free, or its translate by
`−V` or by `−K` is free. -/
theorem outside_SI_free (frame : ChildFrame) (w : Site) (hw : w ∈ frame.closedPolygon)
    (hnot : ¬ FLatticePaper.W1.StrictInterior frame.child.num frame.child.den w) :
    w ∈ frame.freeH ∪ frame.freeV ∨ w + -Vdeck frame ∈ frame.freeH ∪ frame.freeV ∨
      w + -Kdeck frame ∈ frame.freeH ∪ frame.freeV := by
  have hfac := frame.child_facts
  have hTpos := periodDenominator_pos frame
  by_cases hev : EvenSite w
  · have hwE := hw
    rw [mem_closedPolygon_iff, if_pos hev] at hw
    obtain ⟨hw1, hw2, hw3, hw4⟩ := hw
    have hSI : ¬ (frame.child.den + frame.child.num - 2 - frame.child.periodDenominator < frame.tGrade w ∧
        frame.tGrade w < 2 ∧ 2 * frame.child.num < frame.sGrade w ∧ frame.sGrade w < frame.child.periodDenominator) :=
      fun h => hnot ((SI_even_iff frame w hev).mpr h)
    by_cases h1 : 2 ≤ frame.tGrade w
    · -- the upper H strip: the site is on the bottom free H trace
      exact Or.inl (Set.mem_union_left _ (mem_freeH_of frame w hwE
        (not_mem_below_even frame w hev h1) (hSpec_even frame w hev h1 hw2)))
    have h2 : frame.tGrade w < 2 := not_le.mp h1
    by_cases h3 : frame.tGrade w ≤ frame.child.den + frame.child.num - 2 - frame.child.periodDenominator
    · -- the lower H strip: translate by −V onto the upper H strip
      have hVe : EvenSite (w + -Vdeck frame) := (evenSite_add_negV frame w).mpr hev
      have hmem : w + -Vdeck frame ∈ frame.closedPolygon := by
        rw [mem_closedPolygon_iff, if_pos hVe, tGrade_add_negV, sGrade_add_negV]
        exact ⟨by linarith, by linarith, hw3, by linarith⟩
      exact Or.inr (Or.inl (Set.mem_union_left _ (mem_freeH_of frame _ hmem
        (not_mem_below_even frame _ hVe (by rw [tGrade_add_negV]; linarith))
        (hSpec_even frame _ hVe (by rw [tGrade_add_negV]; linarith) (by rw [tGrade_add_negV]; linarith)))))
    have h3' : frame.child.den + frame.child.num - 2 - frame.child.periodDenominator < frame.tGrade w := not_le.mp h3
    by_cases h4 : frame.sGrade w ≤ 2 * frame.child.num
    · -- the lower V strip: free V trace
      exact Or.inl (Set.mem_union_right _ (mem_freeV_of frame w hwE
        (not_mem_left_even frame w hev h4) (vSpec_even frame w (Or.inl ⟨hw3, h4⟩))))
    have h4' : 2 * frame.child.num < frame.sGrade w := not_le.mp h4
    by_cases h5 : frame.child.periodDenominator ≤ frame.sGrade w
    · -- the upper V strip: translate by −K onto the lower V strip
      have hKe : EvenSite (w + -Kdeck frame) := (evenSite_add_negK frame w).mpr hev
      have hmem : w + -Kdeck frame ∈ frame.closedPolygon := by
        rw [mem_closedPolygon_iff, if_pos hKe, tGrade_add_negK, sGrade_add_negK]
        exact ⟨hw1, hw2, by linarith, by linarith⟩
      exact Or.inr (Or.inr (Set.mem_union_right _ (mem_freeV_of frame _ hmem
        (not_mem_left_even frame _ hKe (by rw [sGrade_add_negK]; linarith))
        (vSpec_even frame _ (Or.inl ⟨by rw [sGrade_add_negK]; linarith, by rw [sGrade_add_negK]; linarith⟩)))))
    have h5' : frame.sGrade w < frame.child.periodDenominator := not_le.mp h5
    exfalso
    exact hSI ⟨h3', h2, h4', h5'⟩
  · have hwE := hw
    rw [mem_closedPolygon_iff, if_neg hev] at hw
    obtain ⟨hw1, hw2, hw3, hw4⟩ := hw
    have hSI : ¬ (frame.child.den - frame.child.periodDenominator < frame.tGrade w ∧
        frame.tGrade w < frame.child.num ∧ frame.child.den + frame.child.num - 2 < frame.sGrade w ∧
        frame.sGrade w < frame.child.periodDenominator + (2 - frame.child.den + frame.child.num)) :=
      fun h => hnot ((SI_odd_iff frame w hev).mpr h)
    by_cases h1 : frame.child.num ≤ frame.tGrade w
    · -- the upper odd H strip: the site is on the bottom free H trace
      exact Or.inl (Set.mem_union_left _ (mem_freeH_of frame w hwE
        (not_mem_below_odd frame w hev h1) (hSpec_odd frame w hev h1 hw2)))
    have h1' : frame.tGrade w < frame.child.num := not_le.mp h1
    have hVo : ¬ EvenSite (w + -Vdeck frame) := fun h => hev ((evenSite_add_negV frame w).mp h)
    by_cases h2 : frame.tGrade w ≤ frame.child.den - frame.child.periodDenominator
    · -- the lower odd H strip: translate by −V onto the upper odd H strip
      have hmem : w + -Vdeck frame ∈ frame.closedPolygon := by
        rw [mem_closedPolygon_iff, if_neg hVo, tGrade_add_negV, sGrade_add_negV]
        exact ⟨by linarith, by linarith, hw3, hw4⟩
      exact Or.inr (Or.inl (Set.mem_union_left _ (mem_freeH_of frame _ hmem
        (not_mem_below_odd frame _ hVo (by rw [tGrade_add_negV]; linarith))
        (hSpec_odd frame _ hVo (by rw [tGrade_add_negV]; linarith) (by rw [tGrade_add_negV]; linarith)))))
    have h2' : frame.child.den - frame.child.periodDenominator < frame.tGrade w := not_le.mp h2
    by_cases h3 : frame.sGrade w ≤ frame.child.den + frame.child.num - 2
    · -- the lower odd V strip: free V trace
      exact Or.inl (Set.mem_union_right _ (mem_freeV_of frame w hwE
        (not_mem_left_odd frame w hev h3) (vSpec_even frame w (Or.inr ⟨hw3, h3⟩))))
    have h3' : frame.child.den + frame.child.num - 2 < frame.sGrade w := not_le.mp h3
    by_cases h4 : frame.child.periodDenominator + (2 - frame.child.den + frame.child.num) ≤ frame.sGrade w
    · -- the upper odd V strip: translate by −K onto the lower odd V strip
      have hKo : ¬ EvenSite (w + -Kdeck frame) := fun h => hev ((evenSite_add_negK frame w).mp h)
      have hmem : w + -Kdeck frame ∈ frame.closedPolygon := by
        rw [mem_closedPolygon_iff, if_neg hKo, tGrade_add_negK, sGrade_add_negK]
        exact ⟨hw1, hw2, by linarith, by linarith⟩
      exact Or.inr (Or.inr (Set.mem_union_right _ (mem_freeV_of frame _ hmem
        (not_mem_left_odd frame _ hKo (by rw [sGrade_add_negK]; linarith))
        (vSpec_even frame _ (Or.inr ⟨by rw [sGrade_add_negK]; linarith, by rw [sGrade_add_negK]; linarith⟩)))))
    have h4' : frame.sGrade w < frame.child.periodDenominator + (2 - frame.child.den + frame.child.num) :=
      not_le.mp h4
    exfalso
    exact hSI ⟨h2', h1', h3', h4'⟩

/-- **The nonfree bridge.** A nonfree site has a deck translate in the strict interior `StrictInterior`. -/
theorem nonfree_bridge (frame : ChildFrame) (z : Site) (hz : Nonfree frame z) :
    ∃ v ∈ frame.child.modifiedDeck.span, FLatticePaper.W1.StrictInterior frame.child.num frame.child.den (z + v) := by
  obtain ⟨i, j, hmem⟩ := frame.exists_shift_mem z
  have hv0 : frame.child.modifiedDeck.combine i j ∈ frame.child.modifiedDeck.span := ⟨i, j, rfl⟩
  by_contra hcon
  have hns : ¬ FLatticePaper.W1.StrictInterior frame.child.num frame.child.den
      (z + frame.child.modifiedDeck.combine i j) := fun h => hcon ⟨_, hv0, h⟩
  rcases outside_SI_free frame _ hmem hns with h | h | h
  · exact hz _ hv0 h
  · have hv := span_add_mem hv0 (span_neg_mem (Vdeck_mem_span frame))
    apply hz _ hv
    rw [← add_assoc]
    exact h
  · have hv := span_add_mem hv0 (span_neg_mem (Kdeck_mem_span frame))
    apply hz _ hv
    rw [← add_assoc]
    exact h

end FLatticePaper.Induction
