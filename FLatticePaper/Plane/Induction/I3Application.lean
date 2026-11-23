import FLatticePaper.Plane.Induction.I3Unit
import FLatticePaper.Plane.Induction.StrongEstimates

/-! Task 38: the I3 application at the earlier word.

`i3_chainPotential_unit_of_frame`: for a child frame and a packet `G`, the chain potential `Φ = G − chainSheet` has unit
increments on every edge. The inputs are the unit slip and the unit price of `G`, the no-cross price stars, and the two
signed policies: the quota of `G` with `Φ` nonincreasing along its retained edges, and the quota of the chain sheet with
`Φ` nondecreasing along the reflected chain policy.

`i3_chainPotential_unit_of_strong`: the same at the earlier word `u = conjWord word`, from `StrongEstimates u`: its corrected
`F2F3` (monotonicity of `Φ` along the policy of `G`) and its `F2F4` chain data. The phase is `ε_u`, the sign of `u`'s frame. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

theorem i3_edge_translate (t : Site) (ht : EvenSite t) {i c : Site} (h : Edge i c) :
    Edge (i + t) (c + t) := by
  rcases h with rfl | rfl
  · exact Or.inl (incomingNeg_add_of_even c t ht).symm
  · exact Or.inr (incomingPos_add_of_even c t ht).symm

theorem i3_evenSite_sub (x y : Site) (hx : EvenSite x) (hy : EvenSite y) : EvenSite (x - y) := by
  unfold EvenSite at hx hy ⊢
  simp only [Prod.fst_sub, Prod.snd_sub]
  omega

theorem i3_evenSite_smul_shortShift (frame : ChildFrame) (e : ℤ) : EvenSite (e • frame.shortShift) := by
  unfold EvenSite ChildFrame.shortShift
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  have h : e * (2 * frame.eps * frame.parents.odd.den) + e * (2 * frame.eps * frame.parents.odd.num)
      = 2 * (e * frame.eps * (frame.parents.odd.den + frame.parents.odd.num)) := by ring
  rw [h]
  omega

theorem i3_evenSite_parentShift (frame : ChildFrame) : EvenSite frame.parentShift := by
  unfold EvenSite ChildFrame.parentShift
  have h : frame.eps * (frame.parents.odd.num - frame.parents.odd.den)
      + frame.eps * (frame.parents.odd.num + frame.parents.odd.den)
      = 2 * (frame.eps * frame.parents.odd.num) := by ring
  show (frame.eps * (frame.parents.odd.num - frame.parents.odd.den)
      + frame.eps * (frame.parents.odd.num + frame.parents.odd.den)) % 2 = 0
  rw [h]
  omega

/-- A linear function plus a constant has zero Laplacian. -/
theorem i3_laplacian_affine (α β k : ℤ) (x : Site) :
    laplacian (fun z : Site => α * z.1 + β * z.2 + k) x = 0 := by
  unfold laplacian incomingNeg incomingPos
  split_ifs <;> simp <;> ring

namespace ChildFrame

variable (frame : ChildFrame) (G : Field)

/-- The chain potential is the standard field minus the chain sheet, for every shift. -/
theorem i3_chainPotential_eq (η : ℤ) (z : Site) :
    frame.chainPotential G η z = G z - frame.chainSheet G η z := by
  unfold ChildFrame.chainPotential ChildFrame.slip ChildFrame.price ChildFrame.chainSheet
  ring

/-- The chain sheet is a translate of `G` plus an affine function. -/
theorem i3_chainSheet_eq (η : ℤ) :
    frame.chainSheet G η = fun z => G (z + (η • frame.shortShift - frame.parentShift)) +
      (frame.eps * frame.parents.odd.num * z.1 + -(frame.eps * frame.parents.odd.den) * z.2 +
        frame.eps * (frame.parents.odd.num * (η • frame.shortShift).1
          - frame.parents.odd.den * (η • frame.shortShift).2)) := by
  funext z
  unfold ChildFrame.chainSheet ChildFrame.parentSlope
  rw [add_sub_assoc]
  simp only [Prod.fst_add, Prod.snd_add]
  ring

/-- The Laplacian of the chain sheet is the Laplacian of `G` at the translated site. -/
theorem i3_laplacian_chainSheet (η : ℤ) (c : Site) :
    laplacian (frame.chainSheet G η) c =
      laplacian G (c + (η • frame.shortShift - frame.parentShift)) := by
  have ht : EvenSite (η • frame.shortShift - frame.parentShift) :=
    i3_evenSite_sub _ _ (i3_evenSite_smul_shortShift frame η) (i3_evenSite_parentShift frame)
  have key : laplacian (fun w => G (w + (η • frame.shortShift - frame.parentShift)) +
      (frame.eps * frame.parents.odd.num * w.1 + -(frame.eps * frame.parents.odd.den) * w.2 +
        frame.eps * (frame.parents.odd.num * (η • frame.shortShift).1
          - frame.parents.odd.den * (η • frame.shortShift).2))) c =
      laplacian (fun w => G (w + (η • frame.shortShift - frame.parentShift))) c +
      laplacian (fun w : Site => frame.eps * frame.parents.odd.num * w.1 + -(frame.eps * frame.parents.odd.den) * w.2 +
        frame.eps * (frame.parents.odd.num * (η • frame.shortShift).1
          - frame.parents.odd.den * (η • frame.shortShift).2)) c :=
    laplacian_add_fn _ _ c
  rw [frame.i3_chainSheet_eq G η, key, laplacian_translate_of_even G c _ ht, i3_laplacian_affine, add_zero]

/-- No-cross stars of a shifted primitive price, from unit increments and no-cross stars of the price. -/
theorem i3_noCrossStars_shift (hPU : HasUnitPrice frame G) (hPN : NoPriceSaddle frame G)
    (t : Site) (ht : EvenSite t) :
    NoCrossStars (fun z => frame.price G (z + t)) := by
  unfold NoCrossStars
  intro c h
  dsimp only at h
  rw [← incomingNeg_add_of_even c t ht, ← incomingPos_add_of_even c t ht] at h
  have hA : ¬((frame.price G (incomingNeg (c + t)) - frame.price G (c + t) = -1 ∧
      frame.price G (incomingPos (c + t)) - frame.price G (c + t) = 1) ∨
      (frame.price G (incomingNeg (c + t)) - frame.price G (c + t) = 1 ∧
      frame.price G (incomingPos (c + t)) - frame.price G (c + t) = -1)) := by
    have h' := hPN (c + t)
    simpa only [priceIncrement] using h'
  have hB := hPU (c + t) (incomingNeg (c + t)) (edge_incomingNeg (c + t))
  have hC := hPU (c + t) (incomingPos (c + t)) (edge_incomingPos (c + t))
  simp only [priceIncrement] at hB hC
  obtain ⟨hb1, hb2⟩ := hB
  obtain ⟨hc1, hc2⟩ := hC
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hA (Or.inr ⟨by omega, by omega⟩)
  · exact hA (Or.inl ⟨by omega, by omega⟩)

end ChildFrame

/-- **The chain potential has unit increments**, from the packet of `G` and its two signed policies. -/
theorem i3_chainPotential_unit_of_frame (frame : ChildFrame) (G : Field) (hP : frame.Packet G)
    (hU : HasUnitSlip G (fun z => G (z + frame.shortShift)))
    (hPU : HasUnitPrice frame G) (hPN : NoPriceSaddle frame G)
    {relF relH : Site → Site → Prop}
    (hqF : RetainQuota G relF) (hqH : RetainQuota (fun z => frame.chainSheet G frame.eps z) relH)
    (hmF : NonincreasingAlong (fun z => frame.chainPotential G frame.eps z) relF)
    (hmH : NondecreasingAlong (fun z => frame.chainPotential G frame.eps z) relH) :
    ∀ c i, Edge i c →
      -1 ≤ frame.chainPotential G frame.eps i - frame.chainPotential G frame.eps c ∧
        frame.chainPotential G frame.eps i - frame.chainPotential G frame.eps c ≤ 1 := by
  have hs_even : EvenSite (frame.eps • frame.shortShift) :=
    i3_evenSite_smul_shortShift frame frame.eps
  have hΦ : ∀ z, frame.chainPotential G frame.eps z = G z - frame.chainSheet G frame.eps z :=
    fun z => frame.i3_chainPotential_eq G frame.eps z
  have hfun : (fun z => frame.chainPotential G frame.eps z) =
      fun z => G z - frame.chainSheet G frame.eps z := funext hΦ
  -- the raw slip `G − G(· + ε σ)` has unit increments
  have hD : ∀ c i, Edge i c →
      -1 ≤ (G i - G (i + frame.eps • frame.shortShift)) - (G c - G (c + frame.eps • frame.shortShift)) ∧
        (G i - G (i + frame.eps • frame.shortShift)) - (G c - G (c + frame.eps • frame.shortShift)) ≤ 1 := by
    intro c i hi
    rcases frame.eps_unit with h1 | h1
    · have hs1 : (1 : ℤ) • frame.shortShift = frame.shortShift := by ext <;> simp
      rw [h1, hs1]
      exact hU c i hi
    · have hsm : (-1 : ℤ) • frame.shortShift = -frame.shortShift := by ext <;> simp
      have hev : EvenSite (-frame.shortShift) := by
        rw [← hsm]
        exact i3_evenSite_smul_shortShift frame (-1)
      have h := hU (c + -frame.shortShift) (i + -frame.shortShift)
        (i3_edge_translate _ hev hi)
      simp only [slipIncrement, neg_add_cancel_right] at h
      obtain ⟨h2, h3⟩ := h
      rw [h1, hsm]
      exact ⟨by linarith, by linarith⟩
  -- the shifted primitive price `G(· + εσ) − chainSheet` is the price at the translated site
  have hSH : ∀ z, G (z + frame.eps • frame.shortShift) - frame.chainSheet G frame.eps z =
      frame.price G (z + frame.eps • frame.shortShift) := by
    intro z
    unfold ChildFrame.price ChildFrame.chainSheet
    ring
  have hQ : ∀ c i, Edge i c →
      -1 ≤ (G (i + frame.eps • frame.shortShift) - frame.chainSheet G frame.eps i) -
          (G (c + frame.eps • frame.shortShift) - frame.chainSheet G frame.eps c) ∧
        (G (i + frame.eps • frame.shortShift) - frame.chainSheet G frame.eps i) -
          (G (c + frame.eps • frame.shortShift) - frame.chainSheet G frame.eps c) ≤ 1 := by
    intro c i hi
    rw [hSH i, hSH c]
    have h := hPU (c + frame.eps • frame.shortShift) (i + frame.eps • frame.shortShift)
      (i3_edge_translate _ hs_even hi)
    simp only [priceIncrement] at h
    exact h
  have hQno : NoCrossStars (fun z => G (z + frame.eps • frame.shortShift) - frame.chainSheet G frame.eps z) := by
    have hfun' : (fun z => G (z + frame.eps • frame.shortShift) - frame.chainSheet G frame.eps z) =
        fun z => frame.price G (z + frame.eps • frame.shortShift) := funext hSH
    rw [hfun']
    exact frame.i3_noCrossStars_shift G hPU hPN _ hs_even
  have hHb : ∀ c, laplacian (fun z => frame.chainSheet G frame.eps z) c = -1 ∨
      laplacian (fun z => frame.chainSheet G frame.eps z) c = 0 := by
    intro c
    rw [frame.i3_laplacian_chainSheet G frame.eps c]
    exact hP.binary _
  have hmF' : NonincreasingAlong (fun x => G x - frame.chainSheet G frame.eps x) relF := by
    rw [← hfun]
    exact hmF
  have hmH' : NondecreasingAlong (fun x => G x - frame.chainSheet G frame.eps x) relH := by
    rw [← hfun]
    exact hmH
  have key := unit_increments_of_summands
    (F := G) (S := fun z => G (z + frame.eps • frame.shortShift))
    (H := fun z => frame.chainSheet G frame.eps z)
    hD hQ hQno hP.binary hHb hqF hqH hmF' hmH'
  intro c i hi
  have hk := key c i hi
  simp only [hΦ]
  exact hk

/-- **The chain potential of the earlier word has unit increments**, from its strong estimates (the corrected `F2F3`, the
monotonicity of the potential along the policy of the standard field, and the `F2F4` chain data). -/
theorem i3_chainPotential_unit_of_strong {u : Word} (h : StrongEstimates u) :
    ∀ c i, Edge i c →
      -1 ≤ (frameAt u).chainPotential (standardField u) (frameAt u).eps i
          - (frameAt u).chainPotential (standardField u) (frameAt u).eps c ∧
        (frameAt u).chainPotential (standardField u) (frameAt u).eps i
          - (frameAt u).chainPotential (standardField u) (frameAt u).eps c ≤ 1 := by
  obtain ⟨relF, hqF, hmF, -⟩ := h.F2F3_policy
  obtain ⟨cp, -, R, w, hmH, hqH, -⟩ := h.F2F4_chain
  exact i3_chainPotential_unit_of_frame (frameAt u) (standardField u) h.packet h.F1_unitSlip
    h.F1_unitPrice h.F1_noPriceSaddle hqF hqH hmF hmH

end FLatticePaper.Induction
