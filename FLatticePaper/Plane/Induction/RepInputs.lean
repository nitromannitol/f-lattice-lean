import FLatticePaper.Plane.Induction.ChartWitness
import FLatticePaper.Plane.Induction.W1Exit
import FLatticePaper.Plane.Induction.ExitSlip
import FLatticePaper.Plane.AlternateSlip

/-! Task 67 (1): the deck representative (hrep).

The period lattice `i U + j V` (`U = (d, n)` the child kernel, `V = (n − d, n + d)` the transverse) acts on a rising pair:
* `F` is `U`-periodic with constant `0` (`F_add_child_kernel`);
* under `V` the slip `D w = F w − F (w + σ)` shifts by the constant `2`, and the Laplacian is unchanged (the affine part
  `tGrade` has zero Laplacian).
So `RisingBlackPair` is invariant under the lattice, and every rising pair has a translate with centre in `E`
(`closedPolygon_covers`). For a black centre `z ∈ E` with an input outside `E`, the exit lemma (`W1Exit`) gives a
boundary-spectrum centre, which is white (its translate lies in a strip of `F`). Hence the inputs of a black centre in `E`
lie in `E`, and `NoBlackPairRise` reduces to its `E`-version. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- The shift `i U`, `U = (d, n)`. -/
def ChildFrame.shiftU (frame : ChildFrame) (i : ℤ) : Site := (i * frame.child.den, i * frame.child.num)

/-- The shift `j V`, `V = (n − d, n + d)`. -/
def ChildFrame.shiftV (frame : ChildFrame) (j : ℤ) : Site :=
  (j * (frame.child.num - frame.child.den), j * (frame.child.num + frame.child.den))

theorem ChildFrame.combine_eq_shift (frame : ChildFrame) (i j : ℤ) :
    frame.child.modifiedDeck.combine i j = frame.shiftU i + frame.shiftV j := by
  rw [frame.child_modifiedDeck_combine]
  unfold ChildFrame.shiftU ChildFrame.shiftV
  ext <;> simp only [Prod.fst_add, Prod.snd_add]

theorem ChildFrame.evenSite_shiftU (frame : ChildFrame) (i : ℤ) : EvenSite (frame.shiftU i) := by
  obtain ⟨hn, hd⟩ := frame.child_odd
  have hL : (frame.child.den + frame.child.num) % 2 = 0 := by omega
  unfold EvenSite ChildFrame.shiftU
  show (i * frame.child.den + i * frame.child.num) % 2 = 0
  have e : i * frame.child.den + i * frame.child.num = i * (frame.child.den + frame.child.num) := by ring
  rw [e, Int.mul_emod, hL]
  simp

theorem ChildFrame.evenSite_shiftV (frame : ChildFrame) (j : ℤ) : EvenSite (frame.shiftV j) := by
  unfold EvenSite ChildFrame.shiftV
  show (j * (frame.child.num - frame.child.den) + j * (frame.child.num + frame.child.den)) % 2 = 0
  have e : j * (frame.child.num - frame.child.den) + j * (frame.child.num + frame.child.den) =
      2 * (j * frame.child.num) := by ring
  rw [e]
  simp

theorem ChildFrame.evenSite_combine (frame : ChildFrame) (i j : ℤ) :
    EvenSite (frame.child.modifiedDeck.combine i j) := by
  rw [frame.combine_eq_shift]
  have hU := frame.evenSite_shiftU i
  have hV := frame.evenSite_shiftV j
  unfold EvenSite at hU hV ⊢
  simp only [Prod.fst_add, Prod.snd_add]
  omega

theorem ChildFrame.evenSite_transV (frame : ChildFrame) : EvenSite frame.transV := by
  unfold EvenSite ChildFrame.transV
  show ((frame.child.num - frame.child.den) + (frame.child.num + frame.child.den)) % 2 = 0
  have e : (frame.child.num - frame.child.den) + (frame.child.num + frame.child.den) = 2 * frame.child.num := by ring
  rw [e]
  simp

/-- `tGrade` of the two inputs of a site is twice its own `tGrade` (the inputs are opposite in `x₁ ± x₂`). -/
theorem ChildFrame.tGrade_incomingNeg_add_pos (frame : ChildFrame) (w : Site) :
    frame.tGrade (FLatticePaper.incomingNeg w) + frame.tGrade (FLatticePaper.incomingPos w) =
      2 * frame.tGrade w := by
  unfold FLatticePaper.incomingNeg FLatticePaper.incomingPos
  split_ifs <;> unfold ChildFrame.tGrade <;> ring

/-- The Laplacian is invariant under the transverse period (the affine part has zero Laplacian). -/
theorem ChildFrame.laplacian_add_transV {F : Field} (frame : ChildFrame) (hP : frame.Packet F) (w : Site) :
    laplacian F (w + frame.transV) = laplacian F w := by
  have hV := frame.evenSite_transV
  have h1 := frame.tGrade_incomingNeg_add_pos w
  unfold laplacian
  rw [FLatticePaper.incomingNeg_add_of_even w frame.transV hV,
    FLatticePaper.incomingPos_add_of_even w frame.transV hV]
  rw [frame.periods_transV hP (FLatticePaper.incomingNeg w), frame.periods_transV hP
    (FLatticePaper.incomingPos w), frame.periods_transV hP w]
  linarith

/-- `F` is `U`-periodic with constant `0`. -/
theorem ChildFrame.F_add_shiftU {F : Field} (frame : ChildFrame) (hP : frame.Packet F) (i : ℤ) (x : Site) :
    F (x + frame.shiftU i) = F x := by
  induction i using Int.induction_on with
  | zero => unfold ChildFrame.shiftU; simp only [zero_mul, Prod.mk_zero_zero, add_zero]
  | succ k ih =>
    have e : x + frame.shiftU ((k : ℤ) + 1) = (x + frame.shiftU k) + (frame.child.den, frame.child.num) := by
      unfold ChildFrame.shiftU
      ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
    rw [e, frame.F_add_child_kernel hP, ih]
  | pred k ih =>
    have h := frame.F_add_child_kernel hP (x + frame.shiftU (-(k : ℤ) - 1))
    have e : x + frame.shiftU (-(k : ℤ) - 1) + (frame.child.den, frame.child.num) =
        x + frame.shiftU (-(k : ℤ)) := by
      unfold ChildFrame.shiftU
      ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
    rw [e] at h
    rw [← h]
    exact ih

/-- The Laplacian is invariant under the `U`-shift. -/
theorem ChildFrame.laplacian_add_shiftU {F : Field} (frame : ChildFrame) (hP : frame.Packet F) (i : ℤ) (w : Site) :
    laplacian F (w + frame.shiftU i) = laplacian F w := by
  unfold laplacian
  rw [FLatticePaper.incomingNeg_add_of_even w (frame.shiftU i) (frame.evenSite_shiftU i),
    FLatticePaper.incomingPos_add_of_even w (frame.shiftU i) (frame.evenSite_shiftU i)]
  rw [frame.F_add_shiftU hP, frame.F_add_shiftU hP, frame.F_add_shiftU hP]

/-- The Laplacian is invariant under `j V`. -/
theorem ChildFrame.laplacian_add_shiftV {F : Field} (frame : ChildFrame) (hP : frame.Packet F) (j : ℤ) (w : Site) :
    laplacian F (w + frame.shiftV j) = laplacian F w := by
  induction j using Int.induction_on generalizing w with
  | zero => unfold ChildFrame.shiftV; simp only [zero_mul, Prod.mk_zero_zero, add_zero]
  | succ k ih =>
    have e : w + frame.shiftV ((k : ℤ) + 1) = (w + frame.shiftV k) + frame.transV := by
      unfold ChildFrame.shiftV ChildFrame.transV
      ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
    rw [e, frame.laplacian_add_transV hP, ih]
  | pred k ih =>
    have h := frame.laplacian_add_transV hP (w + frame.shiftV (-(k : ℤ) - 1))
    have e : w + frame.shiftV (-(k : ℤ) - 1) + frame.transV = w + frame.shiftV (-(k : ℤ)) := by
      unfold ChildFrame.shiftV ChildFrame.transV
      ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
    rw [e] at h
    rw [← h]
    exact ih w

/-- The slip `w ↦ F w − F (w + σ)` shifts by `2` under `j V`. -/
theorem ChildFrame.slip_add_shiftV {F : Field} (frame : ChildFrame) (hP : frame.Packet F) (j : ℤ) (w : Site) :
    F (w + frame.shiftV j) - F (w + frame.shiftV j + frame.shortShift) =
      (F w - F (w + frame.shortShift)) + 2 * j := by
  induction j using Int.induction_on generalizing w with
  | zero => unfold ChildFrame.shiftV; simp only [zero_mul, Prod.mk_zero_zero, add_zero, mul_zero]
  | succ k ih =>
    have e : w + frame.shiftV ((k : ℤ) + 1) = (w + frame.shiftV k) + frame.transV := by
      unfold ChildFrame.shiftV ChildFrame.transV
      ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
    rw [e]
    have h := frame.slip_translate_V hP (w + frame.shiftV k + frame.transV)
    rw [add_sub_cancel_right] at h
    rw [h, ih]
    ring
  | pred k ih =>
    have h := frame.slip_translate_V hP (w + frame.shiftV (-(k : ℤ) - 1) + frame.transV)
    rw [add_sub_cancel_right] at h
    have e : w + frame.shiftV (-(k : ℤ) - 1) + frame.transV = w + frame.shiftV (-(k : ℤ)) := by
      unfold ChildFrame.shiftV ChildFrame.transV
      ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
    rw [e] at h
    have h2 := ih w
    linarith

/-- The lattice vector `τ = combine i j = i U + j V` (even). The Laplacian is invariant under it. -/
theorem ChildFrame.laplacian_add_lattice {F : Field} (frame : ChildFrame) (hP : frame.Packet F) (i j : ℤ) (w : Site) :
    laplacian F (w + frame.child.modifiedDeck.combine i j) = laplacian F w := by
  rw [frame.combine_eq_shift, ← add_assoc, frame.laplacian_add_shiftV hP j, frame.laplacian_add_shiftU hP i]

/-- The slip shifts by `2 j` under the lattice vector `combine i j`. -/
theorem ChildFrame.slip_add_lattice {F : Field} (frame : ChildFrame) (hP : frame.Packet F) (i j : ℤ) (w : Site) :
    F (w + frame.child.modifiedDeck.combine i j) - F (w + frame.child.modifiedDeck.combine i j + frame.shortShift) =
      (F w - F (w + frame.shortShift)) + 2 * j := by
  rw [frame.combine_eq_shift, ← add_assoc]
  have h1 := frame.slip_add_shiftV hP j (w + frame.shiftU i)
  have hx1 : F (w + frame.shiftU i) = F w := frame.F_add_shiftU hP i w
  have hx2 : F (w + frame.shiftU i + frame.shortShift) = F (w + frame.shortShift) := by
    rw [add_right_comm w (frame.shiftU i) frame.shortShift]
    exact frame.F_add_shiftU hP i (w + frame.shortShift)
  rw [h1, hx1, hx2]

/-! ### Whiteness of boundary-spectrum centres -/

/-- The V-strip white lemma, with the hypothesis `vSpectrum (sGrade w)` only (the copy of `laplacian_eq_zero_of_freeV`
without its free-boundary side condition). -/
theorem ChildFrame.laplacian_eq_zero_of_vSpectrum {F : Field} (frame : ChildFrame) (hstrips : frame.HasStrips F)
    {w : Site} (hvs : frame.vSpectrum (frame.sGrade w)) : laplacian F w = 0 := by
  obtain ⟨hd, hn, hD, hN0, hND, hq, hn0, hnq, hpar⟩ := frame.linear_facts
  unfold ChildFrame.vSpectrum at hvs
  have hh := hstrips.2
  have hlap := harmonicGrid_harmonic w
  unfold laplacian at hlap ⊢
  by_cases he : EvenSite w
  · simp only [incomingNeg, incomingPos, if_pos he] at hlap ⊢
    have h0 : F w = harmonicGrid w := hh w (by omega) (by omega)
    have h1 : F (w.1 - 1, w.2) = harmonicGrid (w.1 - 1, w.2) :=
      hh _ (by rw [frame.sGrade_sub_x w]; omega) (by rw [frame.sGrade_sub_x w]; omega)
    have h2 : F (w.1 + 1, w.2) = harmonicGrid (w.1 + 1, w.2) :=
      hh _ (by rw [frame.sGrade_add_x w]; omega) (by rw [frame.sGrade_add_x w]; omega)
    rw [h0, h1, h2]
    linarith
  · simp only [incomingNeg, incomingPos, if_neg he] at hlap ⊢
    have h0 : F w = harmonicGrid w := hh w (by omega) (by omega)
    have h1 : F (w.1, w.2 - 1) = harmonicGrid (w.1, w.2 - 1) :=
      hh _ (by rw [frame.sGrade_sub_y w]; omega) (by rw [frame.sGrade_sub_y w]; omega)
    have h2 : F (w.1, w.2 + 1) = harmonicGrid (w.1, w.2 + 1) :=
      hh _ (by rw [frame.sGrade_add_y w]; omega) (by rw [frame.sGrade_add_y w]; omega)
    rw [h0, h1, h2]
    linarith

/-- The H-strip white lemma: `F = 0` on the t-strip, so a centre with `tGrade (spectrum)` and its two inputs are `0`. -/
theorem ChildFrame.laplacian_eq_zero_of_hSpectrum {F : Field} (frame : ChildFrame) (hstrips : frame.HasStrips F)
    {w : Site} (hw : frame.hSpectrum (frame.tGrade w)) : laplacian F w = 0 := by
  obtain ⟨hd, hn, hD, hN0, hND, hq, hn0, hnq, hpar⟩ := frame.linear_facts
  unfold ChildFrame.hSpectrum at hw
  have hNeg : Edge (FLatticePaper.incomingNeg w) w := Or.inl rfl
  have hPos : Edge (FLatticePaper.incomingPos w) w := Or.inr rfl
  by_cases he : EvenSite w
  · have hin1 := frame.tGrade_input_even he hNeg
    have hin2 := frame.tGrade_input_even he hPos
    have h0 : F w = 0 := hstrips.1 w (by omega) (by omega)
    have h1 : F (FLatticePaper.incomingNeg w) = 0 := hstrips.1 _ (by omega) (by omega)
    have h2 : F (FLatticePaper.incomingPos w) = 0 := hstrips.1 _ (by omega) (by omega)
    unfold laplacian
    simp [h0, h1, h2]
  · have hin1 := frame.tGrade_input_odd he hNeg
    have hin2 := frame.tGrade_input_odd he hPos
    have h0 : F w = 0 := hstrips.1 w (by omega) (by omega)
    have h1 : F (FLatticePaper.incomingNeg w) = 0 := hstrips.1 _ (by omega) (by omega)
    have h2 : F (FLatticePaper.incomingPos w) = 0 := hstrips.1 _ (by omega) (by omega)
    unfold laplacian
    simp [h0, h1, h2]

theorem ChildFrame.sGrade_shiftU (frame : ChildFrame) (k : ℤ) :
    frame.sGrade (frame.shiftU k) = k * frame.child.periodDenominator := by
  unfold ChildFrame.sGrade ChildFrame.shiftU Fraction.periodDenominator
  ring

theorem ChildFrame.tGrade_shiftV (frame : ChildFrame) (j : ℤ) :
    frame.tGrade (frame.shiftV j) = -(j * frame.child.periodDenominator) := by
  unfold ChildFrame.tGrade ChildFrame.shiftV Fraction.periodDenominator
  ring

/-- A boundary-spectrum centre is white: translating it by `shiftV (−k)` (resp. `shiftU k`) puts it on the H-strip
(resp. V-strip) with the same Laplacian. -/
theorem ChildFrame.laplacian_eq_zero_of_boundary {F : Field} (frame : ChildFrame) (hP : frame.Packet F) {z : Site}
    (hz : frame.onBoundarySpectrum z) : laplacian F z = 0 := by
  obtain ⟨k, -, hs⟩ := hz
  rcases hs with hH | hV
  · have ht : frame.tGrade (z + frame.shiftV (-k)) = frame.tGrade z + k * frame.child.periodDenominator := by
      rw [frame.tGrade_add, frame.tGrade_shiftV]
      ring
    have hw := frame.laplacian_eq_zero_of_hSpectrum hP.strips (w := z + frame.shiftV (-k))
      (by rw [ht]; exact hH)
    rw [frame.laplacian_add_shiftV hP (-k) z] at hw
    exact hw
  · have hs' : frame.sGrade (z + frame.shiftU k) = frame.sGrade z + k * frame.child.periodDenominator := by
      rw [frame.sGrade_add, frame.sGrade_shiftU]
    have hw := frame.laplacian_eq_zero_of_vSpectrum hP.strips (w := z + frame.shiftU k) (by rw [hs']; exact hV)
    rw [frame.laplacian_add_shiftU hP k z] at hw
    exact hw

/-- The inputs of a black centre in `E` lie in `E` (the exit lemma plus the whiteness of boundary-spectrum centres). -/
theorem ChildFrame.rising_centre_input_mem {F : Field} (frame : ChildFrame) (hP : frame.Packet F) {c i : Site}
    (hc : c ∈ frame.closedPolygon) (hr : RisingBlackPair F frame.shortShift c i) :
    i ∈ frame.closedPolygon := by
  by_contra hout
  have hb := FLatticePaper.W1Exit.exit_centre_on_boundary_spectrum frame c i hc hr.1 hout
  have hw := frame.laplacian_eq_zero_of_boundary hP hb
  rw [hr.2.1] at hw
  norm_num at hw

/-- Translation: a rising pair at `(y + τ, i' + τ)` gives the rising pair at `(y, i')`, for `τ = combine i j`. -/
theorem ChildFrame.rising_translate {G : Field} (frame : ChildFrame) (hP : frame.Packet G) (i j : ℤ) {y i' : Site}
    (h : RisingBlackPair G frame.shortShift (y + frame.child.modifiedDeck.combine i j)
      (i' + frame.child.modifiedDeck.combine i j)) :
    RisingBlackPair G frame.shortShift y i' := by
  obtain ⟨hin, hlap, hpar, hlap', hslip⟩ := h
  have hτ := frame.evenSite_combine i j
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rcases hin with h1 | h1
    · left
      rw [FLatticePaper.incomingNeg_add_of_even y _ hτ] at h1
      exact add_right_cancel h1
    · right
      rw [FLatticePaper.incomingPos_add_of_even y _ hτ] at h1
      exact add_right_cancel h1
  · rw [frame.laplacian_add_lattice hP i j] at hlap
    exact hlap
  · rw [frame.slip_add_lattice hP i j y] at hpar
    omega
  · rw [add_right_comm y (frame.child.modifiedDeck.combine i j) frame.shortShift,
      frame.laplacian_add_lattice hP i j] at hlap'
    exact hlap'
  · unfold slipIncrement at hslip ⊢
    dsimp only at hslip ⊢
    rw [frame.slip_add_lattice hP i j i', frame.slip_add_lattice hP i j y] at hslip
    linarith

/-- The `E`-version of `NoBlackPairRise`: a rising pair with centre in `E` is excluded implies no rising pair at all
(translate the pair into `E`). -/
theorem ChildFrame.noBlackPairRise_of_E {G : Field} (frame : ChildFrame) (hP : frame.Packet G)
    (hE : ∀ c i, RisingBlackPair G frame.shortShift c i → c ∈ frame.closedPolygon → False) :
    NoBlackPairRise G frame.shortShift := by
  intro c h1 h2 h3 i hi hs
  obtain ⟨y, hy, a, b, hc⟩ := frame.closedPolygon_covers c
  subst hc
  refine hE y (i - frame.child.modifiedDeck.combine a b) ?_ hy
  refine frame.rising_translate hP a b ?_
  rw [sub_add_cancel]
  exact ⟨hi, h1, h2, h3, hs⟩

/-- The chart cover with the `E`-restricted hypotheses: `hrep` is discharged by the exit-and-white argument, and
`NoBlackPairRise` follows by translation. Only `hstrict` and `hret` remain as named leaves. -/
theorem noBlackPairRise_of_chart_cover_E {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpk : (frameAt word).Packet (standardField word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed)
    (hstrict : ∀ c i, RisingBlackPair (standardField word) (frameAt word).shortShift c i →
      c ∈ (frameAt word).closedPolygon → 1 ≤ sheetDiffW word c ∧ 1 ≤ sheetDiffW word i)
    (hret : ∀ c i, RisingBlackPair (standardField word) (frameAt word).shortShift c i →
      c ∈ (frameAt word).closedPolygon → sheetPolicyA P (frameAt word).sheetShift c i) :
    NoBlackPairRise (standardField word) (frameAt word).shortShift :=
  (frameAt word).noBlackPairRise_of_E hpk
    (noBlackPairRise_of_chart_cover h hSE hpk P
      (fun _ _ hr hc => (frameAt word).rising_centre_input_mem hpk hc hr) hstrict hret)

end FLatticePaper.Induction
