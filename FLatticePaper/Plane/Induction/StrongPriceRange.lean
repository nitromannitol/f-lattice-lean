import FLatticePaper.Plane.Induction.BaseUpper
import FLatticePaper.Plane.Induction.StrongHSpan
import FLatticePaper.Plane.Induction.W1Lower
import FLatticePaper.Plane.Induction.W1Pointers
import FLatticePaper.Plane.Induction.Bands
import FLatticePaper.Plane.Induction.StrongVStar
import FLatticePaper.Plane.Induction.StrongPriceValues
import FLatticePaper.Plane.Induction.BaseRecurrent

/-! Task 67, STRONG_PRICE §2 (the price range): `c₀ − 1 ≤ P ≤ c₀` on the closed polygon `E`, from the recurrent comparison of `M`.

Upper bound (`price_upper_of_recurrent`): the comparison of `M = F` on `E` against the binary competitor
`g(z) = F(z − v) + ε(N z₁ − D z₂) + c₀` (`P z ≤ c₀ ⇔ F z ≤ g z`), on the finite set of sites of `E` whose four neighbours lie in `E`, with the
boundary of `E` as the named input `P ≤ c₀` on `∂E` (the arc data of the note). The recurrence of `M` enters through `RecurrentField M`.

Lower bound (`price_lower_of_upper`): the reflection identity `P z + P (R − z + v) = 2c₀ − 1` (from the reflection of `F` and the
constant `2c₀ − 1 = t(v) − ε a·(R + v)`), with `P ≤ c₀` on the upper half-plane `E + ℕU + ℤV` (the points with `s` above the `s`-range of
`E`), where `P` drops by one per kernel period (`P(z + kU) = P z − k`) and is constant along `V`.
`s(R) = T + 2n` and `s(v) = 2` give `s(R − z + v) ≥ 0` (even) and `≥ 2 − d + n` (odd) for `z ∈ E`. -/

namespace FLatticePaper.StrongPriceRange

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.StrongHSpan

/-- The shift `v = ε(N − D, N + D)` is even. -/
theorem evenSite_parentShift (frame : ChildFrame) : EvenSite frame.parentShift := by
  unfold EvenSite ChildFrame.parentShift
  show (frame.eps * (frame.parents.odd.num - frame.parents.odd.den) + frame.eps * (frame.parents.odd.num + frame.parents.odd.den)) % 2 = 0
  have : frame.eps * (frame.parents.odd.num - frame.parents.odd.den) + frame.eps * (frame.parents.odd.num + frame.parents.odd.den) =
      2 * (frame.eps * frame.parents.odd.num) := by ring
  rw [this]
  omega

/-- The binary competitor of the upper bound: `g z = F (z − v) + ε(N z₁ − D z₂) + c₀`. -/
def priceCompetitor (frame : ChildFrame) (F : Field) (z : Site) : ℤ :=
  F (z - frame.parentShift) + ((frame.eps * frame.parents.odd.num) * z.1 + (-(frame.eps * frame.parents.odd.den)) * z.2 +
    frame.cutPrice)

/-- The Laplacian of the competitor is the Laplacian of `F` at the shifted site (the affine part is harmonic). -/
theorem laplacian_priceCompetitor (frame : ChildFrame) (F : Field) (x : Site) :
    laplacian (priceCompetitor frame F) x = laplacian F (x - frame.parentShift) := by
  have h1 := FLatticePaper.W1Pointers.laplacian_add (fun z => F (z - frame.parentShift))
    (fun z => (frame.eps * frame.parents.odd.num) * z.1 + (-(frame.eps * frame.parents.odd.den)) * z.2 + frame.cutPrice) x
  have h2 := FLatticePaper.W1Pointers.laplacian_affine (frame.eps * frame.parents.odd.num) (-(frame.eps * frame.parents.odd.den)) frame.cutPrice x
  have h3 := FLatticePaper.W1Pointers.laplacian_translate F frame.parentShift x (evenSite_parentShift frame)
  unfold priceCompetitor
  rw [h1, h2, h3, add_zero]

/-- `P z ≤ c₀` is `F z ≤ g z`. -/
theorem price_le_iff_competitor (frame : ChildFrame) (F : Field) (z : Site) :
    frame.price F z ≤ frame.cutPrice ↔ F z ≤ priceCompetitor frame F z := by
  unfold ChildFrame.price priceCompetitor ChildFrame.parentSlope
  constructor <;> intro h <;> linarith


/-- **The upper bound `P ≤ c₀` on `E`**, from the recurrent comparison of `M = F` on `E` against the binary competitor `g`. The
boundary of `E` is the named input `hbd` (the arc data). -/
theorem price_upper_of_recurrent (frame : ChildFrame) {F M : Field} (hagree : ∀ y ∈ frame.closedPolygon, F y = M y)
    (hbinF : ∀ z, laplacian F z = -1 ∨ laplacian F z = 0)
    (hbinM : ∀ z, laplacian M z = -1 ∨ laplacian M z = 0) (hrec : RecurrentField M)
    (hbd : ∀ z, OnBoundary frame.closedPolygon z → frame.price F z ≤ frame.cutPrice) :
    ∀ x ∈ frame.closedPolygon, frame.price F x ≤ frame.cutPrice := by
  classical
  obtain ⟨R, hR⟩ := closedPolygon_box frame
  set D : Finset Site := (Finset.Icc (-R, -R) (R, R)).filter
    (fun z => FourNbr frame.closedPolygon z ∧ z ∈ frame.closedPolygon) with hDdef
  have hmemD : ∀ z, z ∈ D ↔ (FourNbr frame.closedPolygon z ∧ z ∈ frame.closedPolygon) := by
    intro z
    constructor
    · intro hz
      exact (Finset.mem_filter.mp hz).2
    · rintro ⟨h1, h2⟩
      obtain ⟨a, b, c, e⟩ := hR z h2
      rw [hDdef, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨Prod.mk_le_mk.mpr ⟨by omega, by omega⟩, Prod.mk_le_mk.mpr ⟨by omega, by omega⟩⟩, h1, h2⟩
  have hA : ∀ x ∈ D, laplacian (priceCompetitor frame F) x = -1 ∨ laplacian (priceCompetitor frame F) x = 0 := by
    intro x _
    rw [laplacian_priceCompetitor]
    exact hbinF _
  have hbd' : ∀ y x, x ∈ D → Edge y x → y ∉ D → M y ≤ priceCompetitor frame F y := by
    intro y x hxD hE hyD
    have hxN := (hmemD x).mp hxD
    have hyE : y ∈ frame.closedPolygon := edge_mem_of_fourNbr hxN.1 hE
    have hnot : ¬ FourNbr frame.closedPolygon y := fun h => hyD ((hmemD y).mpr ⟨h, hyE⟩)
    have hb := hbd y (onBoundary_of_not_fourNbr hyE hnot)
    rw [← hagree y hyE]
    exact (price_le_iff_competitor frame F y).mp hb
  have key := recurrent_comparison (priceCompetitor frame F) M D hbinM hrec hA hbd'
  intro x hx
  by_cases hN : FourNbr frame.closedPolygon x
  · have hk := key x ((hmemD x).mpr ⟨hN, hx⟩)
    exact (price_le_iff_competitor frame F x).mpr (by rw [hagree x hx]; exact hk)
  · exact hbd x (onBoundary_of_not_fourNbr hx hN)

/-- The centre in coordinates: `R = (n + 1, 2n + d − 1)`. -/
theorem centre_coords (frame : ChildFrame) :
    frame.centre = (frame.child.num + 1, 2 * frame.child.num + frame.child.den - 1) := by
  unfold ChildFrame.centre
  rw [frame.child_modifiedDeck_kernel, frame.child_modifiedDeck_transverse]
  ext
  all_goals simp
  all_goals ring

/-- The `s`-grade of the centre is `T + 2n`. -/
theorem sGrade_centre (frame : ChildFrame) :
    frame.sGrade frame.centre = frame.child.periodDenominator + 2 * frame.child.num := by
  obtain ⟨-, -, -, -, hT⟩ := frame.child_facts
  rw [centre_coords, hT]
  unfold ChildFrame.sGrade
  ring

/-- The `s`-grade of the parent shift `v` is `2`. -/
theorem sGrade_parentShift (frame : ChildFrame) : frame.sGrade frame.parentShift = 2 := by
  have hsq : frame.eps ^ 2 = 1 := by
    rcases frame.eps_unit with h | h <;> rw [h] <;> norm_num
  have hdef := frame.eps_eq
  unfold ChildFrame.sGrade ChildFrame.parentShift
  linear_combination (-2 * frame.eps) * hdef + 2 * hsq

/-- The key identity: `t(v) − ε a·(R + v) = 2 c₀ − 1` (with `a = (N, −D)`). -/
theorem key_identity (frame : ChildFrame) :
    frame.tGrade frame.parentShift -
        frame.eps * (frame.parents.odd.num * (frame.centre + frame.parentShift).1 -
          frame.parents.odd.den * (frame.centre + frame.parentShift).2) = 2 * frame.cutPrice - 1 := by
  have hsq : frame.eps ^ 2 = 1 := by
    rcases frame.eps_unit with h | h <;> rw [h] <;> norm_num
  have hdef := frame.eps_eq
  have h2c := FLatticePaper.W1Lower.two_cutPrice frame
  rw [centre_coords]
  unfold ChildFrame.tGrade ChildFrame.parentShift
  simp only [Prod.fst_add, Prod.snd_add]
  linear_combination (-(1 + frame.parents.odd.num ^ 2 - 2 * frame.parents.odd.num * frame.parents.odd.den -
    frame.parents.odd.den ^ 2)) * hsq + frame.eps * hdef - h2c

/-- **The reflection identity.** `P z + P (R − z + v) = 2 c₀ − 1`, from the reflection of `F`. -/
theorem price_add_reflect (frame : ChildFrame) {F : Field}
    (hrefl : ∀ z, F (frame.centre - z) = F z - frame.tGrade z + frame.symmetryConstant) (z : Site) :
    frame.price F z + frame.price F (frame.centre - z + frame.parentShift) = 2 * frame.cutPrice - 1 := by
  have hA := hrefl (z - frame.parentShift)
  have hB := hrefl z
  have e1 : frame.centre - (z - frame.parentShift) = frame.centre - z + frame.parentShift := by abel
  have e2 : frame.centre - z + frame.parentShift - frame.parentShift = frame.centre - z := by abel
  rw [e1] at hA
  have key := key_identity frame
  unfold ChildFrame.price ChildFrame.parentSlope
  rw [e2, hB, hA]
  have ht1 : frame.tGrade (z - frame.parentShift) = frame.tGrade z - frame.tGrade frame.parentShift := by
    unfold ChildFrame.tGrade
    simp only [Prod.fst_sub, Prod.snd_sub]
    ring
  rw [ht1]
  unfold ChildFrame.tGrade at key ⊢
  simp only [centre_coords, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at key ⊢
  linear_combination key


/-- The price drops by `k` along `k` kernel periods: `P (z + k U) = P z − k`. -/
theorem price_zsmul_kernel (frame : ChildFrame) (F : Field)
    (hPU : ∀ w, frame.price F (w + frame.child.modifiedDeck.kernel) = frame.price F w - 1) (z : Site) (k : ℤ) :
    frame.price F (z + k • frame.child.modifiedDeck.kernel) = frame.price F z - k := by
  induction k using Int.induction_on with
  | zero => simp
  | succ i ih =>
    rw [add_smul, one_smul, ← add_assoc, hPU, ih]
    ring
  | pred i ih =>
    have e : z + (-(i : ℤ) - 1) • frame.child.modifiedDeck.kernel + frame.child.modifiedDeck.kernel =
        z + (-(i : ℤ)) • frame.child.modifiedDeck.kernel := by
      rw [sub_smul, one_smul]
      abel
    have h := hPU (z + (-(i : ℤ) - 1) • frame.child.modifiedDeck.kernel)
    rw [e, ih] at h
    linarith

/-- A transverse shift puts the `t`-grade into the `t`-range of `E` at the parity of `w`, and keeps the parity. -/
theorem exists_transverse_t_window (frame : ChildFrame) (w : Site) :
    ∃ l : ℤ, (EvenSite (w + l • frame.child.modifiedDeck.transverse) ↔ EvenSite w) ∧
      ((EvenSite w → 2 - frame.child.periodDenominator ≤ frame.tGrade (w + l • frame.child.modifiedDeck.transverse) ∧
          frame.tGrade (w + l • frame.child.modifiedDeck.transverse) ≤ frame.child.den + frame.child.num - 2) ∧
        (¬ EvenSite w → frame.child.num - frame.child.periodDenominator ≤
          frame.tGrade (w + l • frame.child.modifiedDeck.transverse) ∧
          frame.tGrade (w + l • frame.child.modifiedDeck.transverse) ≤ frame.child.den)) := by
  obtain ⟨hn0, hnd, hdn, hd3, hT⟩ := frame.child_facts
  have hTpos : 0 < frame.child.periodDenominator := by rw [hT]; nlinarith
  have htV : ∀ l : ℤ, frame.tGrade (w + l • frame.child.modifiedDeck.transverse) =
      frame.tGrade w - l * frame.child.periodDenominator := by
    intro l
    rw [frame.tGrade_add_pt, frame.tGrade_smul, FLatticePaper.StrongHSpan.tGrade_transverse_eq]
    ring
  by_cases he : EvenSite w
  · have hm := Int.emod_def (frame.tGrade w - (2 - frame.child.periodDenominator)) frame.child.periodDenominator
    have hr0 := Int.emod_nonneg (frame.tGrade w - (2 - frame.child.periodDenominator)) hTpos.ne'
    have hr1 := Int.emod_lt_of_pos (frame.tGrade w - (2 - frame.child.periodDenominator)) hTpos
    refine ⟨(frame.tGrade w - (2 - frame.child.periodDenominator)) / frame.child.periodDenominator,
      FLatticePaper.StrongHSpan.evenSite_add_transverse frame w _, ⟨fun _ => ?_, fun h => absurd he h⟩⟩
    rw [htV]
    constructor <;> nlinarith
  · have hm := Int.emod_def (frame.tGrade w - (frame.child.num - frame.child.periodDenominator))
      frame.child.periodDenominator
    have hr0 := Int.emod_nonneg (frame.tGrade w - (frame.child.num - frame.child.periodDenominator)) hTpos.ne'
    have hr1 := Int.emod_lt_of_pos (frame.tGrade w - (frame.child.num - frame.child.periodDenominator)) hTpos
    refine ⟨(frame.tGrade w - (frame.child.num - frame.child.periodDenominator)) / frame.child.periodDenominator,
      FLatticePaper.StrongHSpan.evenSite_add_transverse frame w _, ⟨fun h => absurd h he, fun _ => ?_⟩⟩
    rw [htV]
    constructor <;> nlinarith

/-- A kernel shift with `k ≤ 0` puts the `s`-grade into a window `[lo, lo + T)` when `s x ≥ lo`. -/
theorem exists_kernel_nonpos_shift (frame : ChildFrame) (x : Site) (lo : ℤ) (hx : lo ≤ frame.sGrade x) :
    ∃ k : ℤ, k ≤ 0 ∧ ∃ e : ℤ, 0 ≤ e ∧ e < frame.child.periodDenominator ∧
      frame.sGrade (x + k • frame.child.modifiedDeck.kernel) = lo + e := by
  obtain ⟨hn0, hnd, hdn, hd3, hT⟩ := frame.child_facts
  have hTpos : 0 < frame.child.periodDenominator := by rw [hT]; nlinarith
  have hq : 0 ≤ (frame.sGrade x - lo) / frame.child.periodDenominator :=
    Int.ediv_nonneg (by omega) hTpos.le
  refine ⟨-((frame.sGrade x - lo) / frame.child.periodDenominator), by omega,
    (frame.sGrade x - lo) % frame.child.periodDenominator,
    Int.emod_nonneg _ hTpos.ne', Int.emod_lt_of_pos _ hTpos, ?_⟩
  rw [frame.sGrade_add_pt, frame.sGrade_smul, frame.sGrade_kernel_eq, Int.emod_def]
  ring

/-- **The upper half-plane bound.** `P ≤ c₀` on `E` gives `P ≤ c₀` at every site whose `s`-grade lies above the lower `s`-bound of `E`
(at its parity): `P` drops by one per kernel period, and the transverse shift does not change `P`. -/
theorem price_le_of_upper_half (frame : ChildFrame) {F : Field}
    (hPU : ∀ w, frame.price F (w + frame.child.modifiedDeck.kernel) = frame.price F w - 1)
    (hPV : ∀ w, frame.price F (w + frame.child.modifiedDeck.transverse) = frame.price F w)
    (hup : ∀ y ∈ frame.closedPolygon, frame.price F y ≤ frame.cutPrice) (w : Site)
    (hs : (EvenSite w → 0 ≤ frame.sGrade w) ∧
      (¬ EvenSite w → 2 - frame.child.den + frame.child.num ≤ frame.sGrade w)) :
    frame.price F w ≤ frame.cutPrice := by
  obtain ⟨hn0, hnd, hdn, hd3, hT⟩ := frame.child_facts
  obtain ⟨l, hpar, hwin⟩ := exists_transverse_t_window frame w
  have hPx : frame.price F (w + l • frame.child.modifiedDeck.transverse) = frame.price F w :=
    price_zsmul_transverse frame F hPV w l
  have hsx : frame.sGrade (w + l • frame.child.modifiedDeck.transverse) = frame.sGrade w := by
    rw [frame.sGrade_add_pt, frame.sGrade_smul, FLatticePaper.StrongHSpan.sGrade_transverse_eq]
    ring
  by_cases he : EvenSite w
  · have hxe : EvenSite (w + l • frame.child.modifiedDeck.transverse) := hpar.mpr he
    obtain ⟨k, hk, e, he0, heT, hse⟩ := exists_kernel_nonpos_shift frame
      (w + l • frame.child.modifiedDeck.transverse) 0 (by rw [hsx]; exact hs.1 he)
    have hy : (w + l • frame.child.modifiedDeck.transverse) + k • frame.child.modifiedDeck.kernel ∈
        frame.closedPolygon := by
      apply frame.mem_closedPolygon_of_even ((frame.evenSite_add_smul_kernel _ k).mpr hxe)
      · rw [frame.tGrade_add_pt, frame.tGrade_smul, StrongVStar.tGrade_kernel_eq_zero]
        have := (hwin.1 he)
        constructor <;> nlinarith [this.1, this.2]
      · rw [hse]
        constructor <;> omega
    have h1 := hup _ hy
    have h2 := price_zsmul_kernel frame F hPU (w + l • frame.child.modifiedDeck.transverse) k
    linarith
  · have hxe : ¬ EvenSite (w + l • frame.child.modifiedDeck.transverse) := fun h => he (hpar.mp h)
    obtain ⟨k, hk, e, he0, heT, hse⟩ := exists_kernel_nonpos_shift frame
      (w + l • frame.child.modifiedDeck.transverse) (2 - frame.child.den + frame.child.num)
      (by rw [hsx]; exact hs.2 he)
    have hy : (w + l • frame.child.modifiedDeck.transverse) + k • frame.child.modifiedDeck.kernel ∈
        frame.closedPolygon := by
      apply frame.mem_closedPolygon_of_odd (fun h => hxe ((frame.evenSite_add_smul_kernel _ k).mp h))
      · rw [frame.tGrade_add_pt, frame.tGrade_smul, StrongVStar.tGrade_kernel_eq_zero]
        have := (hwin.2 he)
        constructor <;> nlinarith [this.1, this.2]
      · rw [hse]
        constructor <;> omega
    have h1 := hup _ hy
    have h2 := price_zsmul_kernel frame F hPU (w + l • frame.child.modifiedDeck.transverse) k
    linarith


/-- The parity of the reflected point `R − z + v` is the parity of `z`. -/
theorem reflect_parity (frame : ChildFrame) (z : Site) :
    EvenSite (frame.centre - z + frame.parentShift) ↔ EvenSite z := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, frame.parentShift.1 + frame.parentShift.2 = 2 * m :=
    ⟨frame.eps * frame.parents.odd.num, by unfold ChildFrame.parentShift; ring⟩
  have hc : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  rw [centre_coords]
  unfold EvenSite
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
  constructor <;> intro h <;> omega

/-- The `s`-grade of the reflected point: `s(R − z + v) = T + 2n − s z + 2`. -/
theorem sGrade_reflect (frame : ChildFrame) (z : Site) :
    frame.sGrade (frame.centre - z + frame.parentShift) =
      frame.child.periodDenominator + 2 * frame.child.num - frame.sGrade z + 2 := by
  have hV := sGrade_parentShift frame
  have hC := sGrade_centre frame
  unfold ChildFrame.sGrade at hV hC ⊢
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hC ⊢
  linear_combination hC + hV

/-- **The lower bound `P ≥ c₀ − 1` on `E`**, from the reflection identity and the upper bound on the upper half-plane. -/
theorem price_lower_of_upper (frame : ChildFrame) {F : Field}
    (hrefl : ∀ z, F (frame.centre - z) = F z - frame.tGrade z + frame.symmetryConstant)
    (hPU : ∀ w, frame.price F (w + frame.child.modifiedDeck.kernel) = frame.price F w - 1)
    (hPV : ∀ w, frame.price F (w + frame.child.modifiedDeck.transverse) = frame.price F w)
    (hup : ∀ y ∈ frame.closedPolygon, frame.price F y ≤ frame.cutPrice)
    (z : Site) (hz : z ∈ frame.closedPolygon) : frame.cutPrice - 1 ≤ frame.price F z := by
  obtain ⟨hn0, hnd, hdn, hd3, hT⟩ := frame.child_facts
  have hsz : (EvenSite z → frame.sGrade z ≤ frame.child.periodDenominator + 2 * frame.child.num) ∧
      (¬ EvenSite z → frame.sGrade z ≤ frame.child.periodDenominator + frame.child.den + frame.child.num - 2) := by
    by_cases he : EvenSite z
    · have hz' := hz
      simp only [ChildFrame.closedPolygon, Set.mem_setOf_eq, if_pos he] at hz'
      exact ⟨fun _ => hz'.2.2.2, fun h => absurd he h⟩
    · have hz' := hz
      simp only [ChildFrame.closedPolygon, Set.mem_setOf_eq, if_neg he] at hz'
      exact ⟨fun h => absurd h he, fun _ => hz'.2.2.2⟩
  have hid := price_add_reflect frame hrefl z
  have hw := price_le_of_upper_half frame hPU hPV hup (frame.centre - z + frame.parentShift) (by
    constructor
    · intro h
      rw [sGrade_reflect]
      have := hsz.1 ((reflect_parity frame z).mp h)
      omega
    · intro h
      rw [sGrade_reflect]
      have hodd : ¬ EvenSite z := fun he => h ((reflect_parity frame z).mpr he)
      have := hsz.2 hodd
      omega)
  linarith

/-- **The price range `c₀ − 1 ≤ P ≤ c₀` on the closed polygon `E`**, from the recurrence of `M` (the upper bound by the comparison, the lower
bound by the reflection). The named inputs are the agreement `F = M` on `E`, the binarity, the boundary bound `P ≤ c₀` on `∂E` (the arc
data), the reflection of `F` and the drifts of `P`. -/
theorem priceRange_of_recurrent (frame : ChildFrame) {F M : Field} (hagree : ∀ y ∈ frame.closedPolygon, F y = M y)
    (hbinF : ∀ z, laplacian F z = -1 ∨ laplacian F z = 0)
    (hbinM : ∀ z, laplacian M z = -1 ∨ laplacian M z = 0) (hrec : RecurrentField M)
    (hbd : ∀ z, OnBoundary frame.closedPolygon z → frame.price F z ≤ frame.cutPrice)
    (hrefl : ∀ z, F (frame.centre - z) = F z - frame.tGrade z + frame.symmetryConstant)
    (hPU : ∀ w, frame.price F (w + frame.child.modifiedDeck.kernel) = frame.price F w - 1)
    (hPV : ∀ w, frame.price F (w + frame.child.modifiedDeck.transverse) = frame.price F w) :
    ∀ z ∈ frame.closedPolygon, frame.cutPrice - 1 ≤ frame.price F z ∧ frame.price F z ≤ frame.cutPrice := by
  have hup := price_upper_of_recurrent frame hagree hbinF hbinM hrec hbd
  intro z hz
  exact ⟨price_lower_of_upper frame hrefl hPU hPV hup z hz, hup z hz⟩


/-- **The price range of a word from the conjugate's strong estimates.** The recurrence and the binarity of `M = min(A, C)` come from the
conjugate's strong estimates (`sheetMin_binary_recurrent_of_strong`). The agreement `F = M` on `E`, the packet and drifts of the current
field, and the boundary bound `P ≤ c₀` on `∂E` (the arc data) are named inputs. -/
theorem priceRange_of_strong {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hpk : (frameAt word).Packet (standardField word))
    (hagree : ∀ y ∈ (frameAt word).closedPolygon,
      standardField word y = (frameAt word).sheetMin (quarterTurnField (standardField (conjWord word))) y)
    (hPU : ∀ w, (frameAt word).price (standardField word) (w + (frameAt word).child.modifiedDeck.kernel) =
      (frameAt word).price (standardField word) w - 1)
    (hPV : ∀ w, (frameAt word).price (standardField word) (w + (frameAt word).child.modifiedDeck.transverse) =
      (frameAt word).price (standardField word) w)
    (hbd : ∀ z, OnBoundary (frameAt word).closedPolygon z →
      (frameAt word).price (standardField word) z ≤ (frameAt word).cutPrice) :
    ∀ z ∈ (frameAt word).closedPolygon,
      (frameAt word).cutPrice - 1 ≤ (frameAt word).price (standardField word) z ∧
        (frameAt word).price (standardField word) z ≤ (frameAt word).cutPrice := by
  obtain ⟨hbinM, hrecM⟩ := FLatticePaper.StrongPriceValues.sheetMin_binary_recurrent_of_strong h hSE
  have hrec := recurrentField_of_recurrent hrecM hbinM
  exact priceRange_of_recurrent (frameAt word) hagree hpk.binary hbinM hrec hbd hpk.reflection hPU hPV

end FLatticePaper.StrongPriceRange
