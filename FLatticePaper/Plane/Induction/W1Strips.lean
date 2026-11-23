import FLatticePaper.Plane.Induction.Strips
import FLatticePaper.Plane.Induction.W1Exit
import FLatticePaper.Plane.Induction.StrongEstimates
import FLatticePaper.Plane.Induction.Q3Field

/-! Task 47, step 1: the lower extension of the even zero interval, `F = 0` on even `t ∈ [2 − L, 1 − d]`.

Source: `.work/fields/escape/newzeros/PARITY_ZERO_INTERVAL_EXTENSION.md` ("Even role") and `escape/ALL_SLOPE_STEP.md` lines 25–34.
Inputs (all named as hypotheses): the mutual seed (`hseed`: `F = 0` on the even sites with `t = 2 − L`), the slip inequality on the
closed polygon (`hslip`: `0 ≤ slip 1 z`, the StrongEstimates slip range), periodicity under the kernel (`hper`), and the ordinary
zero strip (`hstrip`, `hagree`, from `ChildFrame.zero_strip`). The even chain `t = 2 − L + 2k` is climbed by induction from the seed
(`F ≥ 0`) and descended from the ordinary strip (`F ≤ 0`), each step using the slip inequality at a kernel translate in `closedPolygon`. -/

namespace FLatticePaper.W1Strips

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1Exit

theorem tGrade_add (frame : ChildFrame) (x y : Site) : frame.tGrade (x + y) = frame.tGrade x + frame.tGrade y := by
  unfold ChildFrame.tGrade
  simp only [Prod.fst_add, Prod.snd_add]
  ring

theorem tGrade_neg (frame : ChildFrame) (x : Site) : frame.tGrade (-x) = -frame.tGrade x := by
  unfold ChildFrame.tGrade
  simp only [Prod.fst_neg, Prod.snd_neg]
  ring

theorem shortShift_eps_sq (frame : ChildFrame) : frame.eps * frame.eps = 1 := by
  rcases frame.eps_unit with h | h <;> rw [h] <;> norm_num

theorem tGrade_shortShift (frame : ChildFrame) : frame.tGrade frame.shortShift = -2 := by
  have he : frame.eps = frame.parents.odd.num * frame.child.den - frame.parents.odd.den * frame.child.num :=
    frame.eps_eq
  have hsq := shortShift_eps_sq frame
  unfold ChildFrame.tGrade ChildFrame.shortShift
  simp only
  linear_combination (2 * frame.eps) * he + (-2) * hsq

theorem evenSite_shortShift (frame : ChildFrame) : EvenSite frame.shortShift := by
  unfold EvenSite ChildFrame.shortShift
  simp only
  rw [show 2 * frame.eps * frame.parents.odd.den + 2 * frame.eps * frame.parents.odd.num =
    2 * (frame.eps * frame.parents.odd.den + frame.eps * frame.parents.odd.num) by ring]
  exact Int.mul_emod_right _ _

theorem evenSite_neg_pt {x : Site} (hx : EvenSite x) : EvenSite (-x) := by
  unfold EvenSite at hx ⊢
  simp only [Prod.fst_neg, Prod.snd_neg]
  omega

/-- The kernel translate of a site: the grade `t` is kernel invariant, the grade `s` moves by `q · T`. -/
theorem sGrade_add_smul_kernel (frame : ChildFrame) (z : Site) (q : ℤ) :
    frame.sGrade (z + q • frame.child.modifiedDeck.kernel) =
      frame.sGrade z + q * frame.child.periodDenominator := by
  rw [ChildFrame.sGrade_add_pt frame, ChildFrame.sGrade_smul frame, ChildFrame.sGrade_kernel_eq frame]

/-- Even sites of the chain lie in the closed polygon after a kernel translate (the `s` grade is brought into `[0, T)`). -/
theorem exists_kernel_shift_closed (frame : ChildFrame) (z : Site) (hz : EvenSite z)
    (hlo : 2 - frame.child.periodDenominator ≤ frame.tGrade z) (hhi : frame.tGrade z ≤ frame.child.den + frame.child.num - 2) :
    ∃ q : ℤ, z + q • frame.child.modifiedDeck.kernel ∈ frame.closedPolygon := by
  have hT : 0 < frame.child.periodDenominator := ChildFrame.periodDen_pos frame
  refine ⟨-(frame.sGrade z / frame.child.periodDenominator), ?_⟩
  have hE : EvenSite (z + (-(frame.sGrade z / frame.child.periodDenominator)) • frame.child.modifiedDeck.kernel) :=
    (ChildFrame.evenSite_add_smul_kernel frame z _).2 hz
  unfold ChildFrame.closedPolygon
  simp only [Set.mem_setOf_eq]
  rw [if_pos hE, ChildFrame.tGrade_add_smul_kernel frame, sGrade_add_smul_kernel frame]
  have h1 := Int.emod_def (frame.sGrade z) frame.child.periodDenominator
  have h2 := Int.emod_nonneg (frame.sGrade z) hT.ne'
  have h3 := Int.emod_lt_of_pos (frame.sGrade z) hT
  have hn : 0 ≤ frame.child.num := by
    have := frame.child_facts
    omega
  refine ⟨hlo, hhi, ?_, ?_⟩ <;> nlinarith


theorem evenSite_add_pt {x y : Site} (hx : EvenSite x) (hy : EvenSite y) : EvenSite (x + y) := by
  unfold EvenSite at hx hy ⊢
  simp only [Prod.fst_add, Prod.snd_add]
  omega

theorem child_T_ge_L (frame : ChildFrame) : frame.child.den + frame.child.num ≤ frame.child.periodDenominator := by
  obtain ⟨hpos, hnlt, hdn, hd3, hT⟩ := frame.child_facts
  rw [hT]
  nlinarith

/-- **The lower even zero interval.** Let `F` be periodic under the kernel with the strip inputs of the child, let `F` be
nonnegative-slip on the closed polygon (`hslip`), and let `F` vanish at the even sites of the mutual seed level `t = 2 − L`
(`hseed`). Then `F = 0` at every even site with `2 − L ≤ t ≤ 1 − d`. -/
theorem even_zero_lower (frame : ChildFrame) {F : Field}
    (hper : HasGeneratorPeriods frame.child F 0 frame.coherentConstantV)
    (hstrips : frame.HasStrips F)
    (hslip : ∀ z ∈ frame.closedPolygon, 0 ≤ frame.slip F 1 z)
    (hseed : ∀ z : Site, EvenSite z → frame.tGrade z = 2 - (frame.child.den + frame.child.num) → F z = 0)
    (z : Site) (hz : EvenSite z) (hlo : 2 - (frame.child.den + frame.child.num) ≤ frame.tGrade z)
    (hhi : frame.tGrade z ≤ 1 - frame.child.den) : F z = 0 := by
  obtain ⟨hn1, hd1⟩ := child_parity frame
  obtain ⟨hpos, hnlt, hdn, hd3, -⟩ := frame.child_facts
  have hLev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hTL := child_T_ge_L frame
  have hK : ∀ w q, F (w + q • frame.child.modifiedDeck.kernel) = F w := fun w q =>
    ChildFrame.periodic_kernel frame hper w q
  have hT : 0 < frame.child.periodDenominator := ChildFrame.periodDen_pos frame
  -- the upward induction from the seed: `F ≥ 0` on the chain `t = 2 − L + 2m`
  have hA : ∀ m : ℕ, ∀ w : Site, EvenSite w → frame.tGrade w = 2 - (frame.child.den + frame.child.num) + 2 * (m : ℤ) →
      2 - (frame.child.den + frame.child.num) + 2 * (m : ℤ) ≤ 1 - frame.child.den → 0 ≤ F w := by
    intro m
    induction m with
    | zero =>
      intro w hw ht _
      have h0 : F w = 0 := hseed w hw (by simpa using ht)
      rw [h0]
    | succ m ih =>
      intro w hw ht hle
      push_cast at ht hle
      have hm0 : (0 : ℤ) ≤ (m : ℤ) := by positivity
      obtain ⟨q, hq⟩ := exists_kernel_shift_closed frame w hw (by omega) (by omega)
      have hws : EvenSite (w + q • frame.child.modifiedDeck.kernel) :=
        (ChildFrame.evenSite_add_smul_kernel frame w q).2 hw
      have htws : frame.tGrade (w + q • frame.child.modifiedDeck.kernel) = frame.tGrade w :=
        ChildFrame.tGrade_add_smul_kernel frame w q
      have hv : EvenSite ((w + q • frame.child.modifiedDeck.kernel) + frame.shortShift) :=
        evenSite_add_pt hws (evenSite_shortShift frame)
      have htv : frame.tGrade ((w + q • frame.child.modifiedDeck.kernel) + frame.shortShift) =
          2 - (frame.child.den + frame.child.num) + 2 * (m : ℤ) := by
        rw [tGrade_add frame, htws, tGrade_shortShift frame]
        omega
      have hvle : 2 - (frame.child.den + frame.child.num) + 2 * (m : ℤ) ≤ 1 - frame.child.den := by omega
      have hIH := ih _ hv htv hvle
      have hsl := hslip _ hq
      unfold ChildFrame.slip at hsl
      rw [one_zsmul, hK] at hsl
      have hFw := hK w q
      linarith
  -- the downward induction from the ordinary zero strip: `F ≤ 0` on the chain `t = 1 − d − 2m`
  have hB : ∀ m : ℕ, ∀ w : Site, EvenSite w → frame.tGrade w = 1 - frame.child.den - 2 * (m : ℤ) →
      2 - (frame.child.den + frame.child.num) ≤ 1 - frame.child.den - 2 * (m : ℤ) → F w ≤ 0 := by
    intro m
    induction m with
    | zero =>
      intro w hw ht _
      push_cast at ht
      have h0 : F w = 0 := hstrips.1 w (by omega) (by omega)
      rw [h0]
    | succ m ih =>
      intro w hw ht hle
      push_cast at ht hle
      have hm0 : (0 : ℤ) ≤ (m : ℤ) := by positivity
      have hy : EvenSite (w + -frame.shortShift) :=
        evenSite_add_pt hw (evenSite_neg_pt (evenSite_shortShift frame))
      have hty : frame.tGrade (w + -frame.shortShift) = 1 - frame.child.den - 2 * (m : ℤ) := by
        rw [tGrade_add frame, tGrade_neg frame, tGrade_shortShift frame]
        omega
      have hyle : 2 - (frame.child.den + frame.child.num) ≤ 1 - frame.child.den - 2 * (m : ℤ) := by omega
      have hIH := ih _ hy hty hyle
      obtain ⟨q, hq⟩ := exists_kernel_shift_closed frame (w + -frame.shortShift) hy (by omega) (by omega)
      have hsl := hslip _ hq
      unfold ChildFrame.slip at hsl
      rw [one_zsmul, hK] at hsl
      have hpt : (w + -frame.shortShift) + q • frame.child.modifiedDeck.kernel + frame.shortShift =
          w + q • frame.child.modifiedDeck.kernel := by
        ext <;> simp <;> ring
      rw [hpt, hK] at hsl
      linarith
  -- the parity of the grade and the two chain indices of `z`
  have hpar : frame.tGrade z % 2 = 0 := by
    obtain ⟨x, y⟩ := z
    have hxy : (x + y) % 2 = 0 := hz
    show (frame.child.num * x - frame.child.den * y) % 2 = 0
    rw [parity_t _ _ x y hn1 hd1]
    exact hxy
  obtain ⟨m, hm⟩ : ∃ m : ℕ, frame.tGrade z = 2 - (frame.child.den + frame.child.num) + 2 * (m : ℤ) := by
    have hnn : 0 ≤ (frame.tGrade z - (2 - (frame.child.den + frame.child.num))) / 2 := by omega
    exact ⟨((frame.tGrade z - (2 - (frame.child.den + frame.child.num))) / 2).toNat, by
      rw [Int.toNat_of_nonneg hnn]
      omega⟩
  obtain ⟨m', hm'⟩ : ∃ m' : ℕ, frame.tGrade z = 1 - frame.child.den - 2 * (m' : ℤ) := by
    have hnn : 0 ≤ (1 - frame.child.den - frame.tGrade z) / 2 := by omega
    exact ⟨((1 - frame.child.den - frame.tGrade z) / 2).toNat, by
      rw [Int.toNat_of_nonneg hnn]
      omega⟩
  have hA' := hA m z hz hm (by omega)
  have hB' := hB m' z hz hm' (by omega)
  exact le_antisymm hB' hA'


/-- The reflection `z ↦ I − z` about `I = (1, −1)`. -/
def iRefl (z : Site) : Site := (1 - z.1, -1 - z.2)

theorem iRefl_iRefl (z : Site) : iRefl (iRefl z) = z := by
  unfold iRefl
  ext <;> simp

theorem evenSite_iRefl (z : Site) : EvenSite (iRefl z) ↔ EvenSite z := by
  unfold EvenSite iRefl
  simp only
  omega

theorem tGrade_iRefl (frame : ChildFrame) (z : Site) :
    frame.tGrade (iRefl z) = frame.child.num + frame.child.den - frame.tGrade z := by
  unfold ChildFrame.tGrade iRefl
  ring

theorem sGrade_iRefl (frame : ChildFrame) (z : Site) :
    frame.sGrade (iRefl z) = 2 * frame.child.num - frame.sGrade z := by
  unfold ChildFrame.sGrade iRefl
  ring

theorem harmonicGrid_iRefl (z : Site) : harmonicGrid (iRefl z) = harmonicGrid z := by
  obtain ⟨a, b⟩ := z
  have hp : ((1 - a) + (-1 - b)) % 2 = (a + b) % 2 := by omega
  show ((1 - a) ^ 2 + 2 * (1 - a) * (-1 - b) - (-1 - b) ^ 2 - 2 * (-1 - b) - ((1 - a) + (-1 - b)) % 2) / 4 =
    (a ^ 2 + 2 * a * b - b ^ 2 - 2 * b - (a + b) % 2) / 4
  rw [hp]
  congr 1
  ring

/-- **The upper even zero interval `[n + 2d − 1, 2L − 2]`**, from the lower one and the reflection `I − z`. -/
theorem even_zero_upper (frame : ChildFrame) {F : Field}
    (hper : HasGeneratorPeriods frame.child F 0 frame.coherentConstantV)
    (hstrips : frame.HasStrips F)
    (hslip : ∀ z ∈ frame.closedPolygon, 0 ≤ frame.slip F 1 z)
    (hseed : ∀ z : Site, EvenSite z → frame.tGrade z = 2 - (frame.child.den + frame.child.num) → F z = 0)
    (hIsym : ∀ z : Site, F (iRefl z) = F z)
    (w : Site) (hw : EvenSite w) (hlo : frame.child.num + 2 * frame.child.den - 1 ≤ frame.tGrade w)
    (hhi : frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2) : F w = 0 := by
  obtain ⟨hpos, hnlt, hdn, hd3, -⟩ := frame.child_facts
  have hz : EvenSite (iRefl w) := (evenSite_iRefl w).2 hw
  have ht : frame.tGrade (iRefl w) = frame.child.num + frame.child.den - frame.tGrade w :=
    tGrade_iRefl frame w
  have h0 : F (iRefl w) = 0 :=
    even_zero_lower frame hper hstrips hslip hseed (iRefl w) hz (by omega) (by omega)
  rw [← hIsym w]
  exact h0

/-- **The even zero interval `[2 − L, 2L − 2]`.** -/
theorem even_zero_full (frame : ChildFrame) {F : Field}
    (hper : HasGeneratorPeriods frame.child F 0 frame.coherentConstantV)
    (hstrips : frame.HasStrips F)
    (hslip : ∀ z ∈ frame.closedPolygon, 0 ≤ frame.slip F 1 z)
    (hseed : ∀ z : Site, EvenSite z → frame.tGrade z = 2 - (frame.child.den + frame.child.num) → F z = 0)
    (hIsym : ∀ z : Site, F (iRefl z) = F z)
    (z : Site) (hz : EvenSite z) (hlo : 2 - (frame.child.den + frame.child.num) ≤ frame.tGrade z)
    (hhi : frame.tGrade z ≤ 2 * (frame.child.den + frame.child.num) - 2) : F z = 0 := by
  obtain ⟨hpos, hnlt, hdn, hd3, -⟩ := frame.child_facts
  by_cases h1 : frame.tGrade z ≤ 1 - frame.child.den
  · exact even_zero_lower frame hper hstrips hslip hseed z hz hlo h1
  by_cases h2 : frame.tGrade z ≤ frame.child.num + 2 * frame.child.den - 1
  · exact hstrips.1 z (by omega) h2
  exact even_zero_upper frame hper hstrips hslip hseed hIsym z hz (by omega) hhi

/-- **Top collar (archive section 2, `F(y) = 0`).** -/
theorem top_collar_zero_full (frame : ChildFrame) {F : Field}
    (hper : HasGeneratorPeriods frame.child F 0 frame.coherentConstantV)
    (hstrips : frame.HasStrips F)
    (hslip : ∀ z ∈ frame.closedPolygon, 0 ≤ frame.slip F 1 z)
    (hseed : ∀ z : Site, EvenSite z → frame.tGrade z = 2 - (frame.child.den + frame.child.num) → F z = 0)
    (hIsym : ∀ z : Site, F (iRefl z) = F z)
    (y : Site) (hy : (EvenSite y ∧ frame.child.den + frame.child.num - 2 < frame.tGrade y ∧
        frame.tGrade y ≤ 2 * (frame.child.den + frame.child.num) - 2) ∨
      (¬ EvenSite y ∧ frame.child.den < frame.tGrade y ∧
        frame.tGrade y ≤ frame.child.num + 2 * frame.child.den - 2)) : F y = 0 := by
  obtain ⟨hpos, hnlt, hdn, hd3, -⟩ := frame.child_facts
  rcases hy with ⟨he, hlo, hhi⟩ | ⟨hn, hlo, hhi⟩
  · exact even_zero_full frame hper hstrips hslip hseed hIsym y he (by omega) hhi
  · exact hstrips.1 y (by omega) (by omega)

/-- **The upper odd h0 interval `[2L − 1, 3d + n − 2]`**, from the lower one `[2 − 3d + n, 1 − 2d]` (named `hlow`) and `I − z`. -/
theorem odd_h0_upper (frame : ChildFrame) {F : Field}
    (hIsym : ∀ z : Site, F (iRefl z) = F z)
    (hlow : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 1 - 2 * frame.child.den → F z = harmonicGrid z)
    (w : Site) (hw : ¬ EvenSite w) (hlo : 2 * (frame.child.den + frame.child.num) - 1 ≤ frame.sGrade w)
    (hhi : frame.sGrade w ≤ 3 * frame.child.den + frame.child.num - 2) : F w = harmonicGrid w := by
  obtain ⟨hpos, hnlt, hdn, hd3, -⟩ := frame.child_facts
  have hz : ¬ EvenSite (iRefl w) := fun h => hw ((evenSite_iRefl w).1 h)
  have hs : frame.sGrade (iRefl w) = 2 * frame.child.num - frame.sGrade w := sGrade_iRefl frame w
  have h1 : F w = F (iRefl w) := by
    have h := hIsym (iRefl w)
    rw [iRefl_iRefl] at h
    exact h
  rw [h1, hlow (iRefl w) hz (by omega) (by omega), harmonicGrid_iRefl]

/-- **V side (archive section 2, `F = h0` on odd `s ∈ (L − 2, 3d + n − 2]`)**. -/
theorem V_side_full (frame : ChildFrame) {F : Field}
    (hstrips : frame.HasStrips F)
    (hIsym : ∀ z : Site, F (iRefl z) = F z)
    (hlow : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 1 - 2 * frame.child.den → F z = harmonicGrid z)
    (z : Site) (hz : ¬ EvenSite z) (hlo : frame.child.den + frame.child.num - 2 < frame.sGrade z)
    (hhi : frame.sGrade z ≤ 3 * frame.child.den + frame.child.num - 2) : F z = harmonicGrid z := by
  obtain ⟨hpos, hnlt, hdn, hd3, -⟩ := frame.child_facts
  by_cases h : frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 1
  · exact hstrips.2 z (by omega) h
  · exact odd_h0_upper frame hIsym hlow z hz (by omega) hhi

/-! ### The word level: the packet, the slip range and the reflection of the standard field. -/

theorem iRefl_eq_sub (z : Site) : iRefl z = (1, -1) - z := by
  ext <;> simp [iRefl]

/-- **The reflection of the standard field, from its packet** (`packet_reflection_I`): `F (I − z) = F z`. -/
theorem standardField_iRefl {u : Word} (h : StrongEstimates u) (z : Site) :
    standardField u (iRefl z) = standardField u z := by
  rw [iRefl_eq_sub]
  exact packet_reflection_I (frameAt u) h.packet z

/-- The periods of the standard field at the packet, with the kernel constant zero. -/
theorem hper_of_strong {u : Word} (h : StrongEstimates u) :
    HasGeneratorPeriods (frameAt u).child (standardField u) 0 (frameAt u).coherentConstantV := by
  have hp := h.packet.periods
  rw [coherentConstantU_eq_zero (frameAt u)] at hp
  exact hp

/-- **The top collar of the standard field of a word**, from the strong estimates and the named seed `hseed`. -/
theorem top_collar_of_strong {u : Word} (h : StrongEstimates u)
    (hseed : ∀ z : Site, EvenSite z → (frameAt u).tGrade z = 2 - ((frameAt u).child.den + (frameAt u).child.num) →
      standardField u z = 0)
    (y : Site) (hy : (EvenSite y ∧ (frameAt u).child.den + (frameAt u).child.num - 2 < (frameAt u).tGrade y ∧
        (frameAt u).tGrade y ≤ 2 * ((frameAt u).child.den + (frameAt u).child.num) - 2) ∨
      (¬ EvenSite y ∧ (frameAt u).child.den < (frameAt u).tGrade y ∧
        (frameAt u).tGrade y ≤ (frameAt u).child.num + 2 * (frameAt u).child.den - 2)) :
    standardField u y = 0 :=
  top_collar_zero_full (frameAt u) (hper_of_strong h) h.packet.strips (fun z hz => (h.slipRange z hz).1)
    hseed (standardField_iRefl h) y hy

/-- **The lower even zero interval of the standard field of a word**, from the strong estimates and the named seed. -/
theorem even_zero_lower_of_strong {u : Word} (h : StrongEstimates u)
    (hseed : ∀ z : Site, EvenSite z → (frameAt u).tGrade z = 2 - ((frameAt u).child.den + (frameAt u).child.num) →
      standardField u z = 0)
    (z : Site) (hz : EvenSite z) (hlo : 2 - ((frameAt u).child.den + (frameAt u).child.num) ≤ (frameAt u).tGrade z)
    (hhi : (frameAt u).tGrade z ≤ 1 - (frameAt u).child.den) : standardField u z = 0 :=
  even_zero_lower (frameAt u) (hper_of_strong h) h.packet.strips (fun z hz => (h.slipRange z hz).1) hseed z hz hlo hhi

end FLatticePaper.W1Strips
