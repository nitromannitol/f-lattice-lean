import FLatticePaper.Plane.Induction.I3NoA
import FLatticePaper.Plane.Induction.SheetDifference

/-! Task 38: the C sheet (the field `permitC` of `SheetLocalInputs`).

The sheet identity `sheetDifference_identifies` with `Ξ = G∘Z − h'∘Z` gives, for all `x`,
`h'_η(Z x) = Fp(x − e) − h0(x) + siblingSlope(x) + const`, with `e = sheetOffset` and `η = eps(word)`. Hence the Laplacian of
`Fp` at `c` is that of `h'_η` at `Z(c + e)`, and the reflected chain policy, pulled back by `Z(· + e)`, is a quota for `Fp`
inside the `C`-permits `Ξ(c + e) ≤ Ξ(i + e)`. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

theorem i3_laplacian_comp_Z (H : Field) (c : Site) :
    laplacian (fun y => H (i3Z y)) c = laplacian H (i3Z c) := by
  unfold laplacian
  by_cases hc : EvenSite c
  · simp only [i3_Z_neg_even hc, i3_Z_pos_even hc]
  · simp only [i3_Z_neg_odd hc, i3_Z_pos_odd hc]
    ring

theorem i3_laplacian_siblingSlope_shift (frame : ChildFrame) (e c : Site) :
    laplacian (fun x => frame.siblingSlope (x + e)) c = 0 := by
  have hfun : (fun x => frame.siblingSlope (x + e)) =
      fun x : Site => frame.parents.even.num * x.1 + -(frame.parents.even.den) * x.2 +
        (frame.parents.even.num * e.1 - frame.parents.even.den * e.2) := by
    funext x
    unfold ChildFrame.siblingSlope
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  rw [hfun]
  exact i3_laplacian_affine _ _ _ c

/-- The Laplacian of the quarter-turned field at `c` is the Laplacian of the chain sheet at `Z(c + e)`, from the identity
`h'(Z x) = Fp(x − e) − h0(x) + sl(x) + K` (the harmonic and affine summands have zero Laplacian). -/
theorem i3_laplacian_shift_of_identity {F H sl : Field} {e : Site} (he : EvenSite e) {K : ℤ}
    (hsl : ∀ c, laplacian (fun x => sl (x + e)) c = 0)
    (hid : ∀ x, H (i3Z x) = quarterTurnField F (x - e) - harmonicGrid x + sl x + K) (c : Site) :
    laplacian (quarterTurnField F) c = laplacian H (i3Z (c + e)) := by
  have hfun : (fun x => H (i3Z (x + e))) =
      fun x => quarterTurnField F x - harmonicGrid (x + e) + sl (x + e) + K := by
    funext x
    have h := hid (x + e)
    rw [add_sub_cancel_right] at h
    exact h
  have hh : laplacian (fun x => harmonicGrid (x + e)) c = 0 := by
    rw [laplacian_translate_of_even harmonicGrid c e he]
    exact harmonicGrid_harmonic (c + e)
  have h1 : laplacian (fun x => H (i3Z (x + e))) c = laplacian (quarterTurnField F) c := by
    rw [hfun]
    have hs := hsl c
    unfold laplacian at hh hs ⊢
    dsimp only at hh hs ⊢
    linarith
  have h2 : laplacian (fun x => H (i3Z (x + e))) c = laplacian H (i3Z (c + e)) := by
    have := laplacian_translate_of_even (fun y => H (i3Z y)) c e he
    rw [this, i3_laplacian_comp_Z]
  rw [← h1, h2]

/-- The quota transports through the quarter turn and the shift by `e`: the pullback of a quota of `H` along `Z(· + e)`. -/
theorem i3_retainQuota_shift_Z {F H : Field} {R : Site → Site → Prop} {e : Site} (he : EvenSite e)
    (hlap : ∀ c, laplacian (quarterTurnField F) c = laplacian H (i3Z (c + e)))
    (hq : RetainQuota H R) :
    RetainQuota (quarterTurnField F) (fun c i => R (i3Z (c + e)) (i3Z (i + e))) := by
  have hpar : ∀ c, EvenSite (c + e) ↔ EvenSite c := by
    intro c
    unfold EvenSite at he ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    constructor <;> intro h <;> omega
  constructor
  · intro c hc
    rw [hlap] at hc
    obtain ⟨h1, h2⟩ := hq.1 (i3Z (c + e)) hc
    by_cases hp : EvenSite (c + e)
    · refine ⟨?_, ?_⟩
      · show R (i3Z (c + e)) (i3Z (incomingNeg c + e))
        rw [← incomingNeg_add_of_even c e he, i3_Z_neg_even hp]
        exact h1
      · show R (i3Z (c + e)) (i3Z (incomingPos c + e))
        rw [← incomingPos_add_of_even c e he, i3_Z_pos_even hp]
        exact h2
    · refine ⟨?_, ?_⟩
      · show R (i3Z (c + e)) (i3Z (incomingNeg c + e))
        rw [← incomingNeg_add_of_even c e he, i3_Z_neg_odd hp]
        exact h2
      · show R (i3Z (c + e)) (i3Z (incomingPos c + e))
        rw [← incomingPos_add_of_even c e he, i3_Z_pos_odd hp]
        exact h1
  · intro c hc
    rw [hlap] at hc
    rcases hq.2 (i3Z (c + e)) hc with h | h
    · by_cases hp : EvenSite (c + e)
      · refine Or.inl ?_
        show R (i3Z (c + e)) (i3Z (incomingNeg c + e))
        rw [← incomingNeg_add_of_even c e he, i3_Z_neg_even hp]
        exact h
      · refine Or.inr ?_
        show R (i3Z (c + e)) (i3Z (incomingPos c + e))
        rw [← incomingPos_add_of_even c e he, i3_Z_pos_odd hp]
        exact h
    · by_cases hp : EvenSite (c + e)
      · refine Or.inr ?_
        show R (i3Z (c + e)) (i3Z (incomingPos c + e))
        rw [← incomingPos_add_of_even c e he, i3_Z_pos_even hp]
        exact h
      · refine Or.inl ?_
        show R (i3Z (c + e)) (i3Z (incomingNeg c + e))
        rw [← incomingNeg_add_of_even c e he, i3_Z_neg_odd hp]
        exact h

theorem i3_evenSite_offset (f : Fraction) (hf : f.Even) (ε : ℤ) :
    EvenSite (f.unmodifiedDeck.transverse + ε • f.unmodifiedDeck.kernel) := by
  have hf' : (f.num + f.den) % 2 = 0 := hf
  have hk : f.num + f.den = 2 * ((f.num + f.den) / 2) := by omega
  unfold EvenSite Fraction.unmodifiedDeck
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  have key : (f.num - f.den + ε * f.den) + (f.num + f.den + ε * f.num) =
      2 * (f.num + ε * ((f.num + f.den) / 2)) := by
    linear_combination ε * hk
  rw [key]
  omega

theorem i3_evenSite_sheetOffset (word : Word) : EvenSite (frameAt word).sheetOffset :=
  i3_evenSite_offset (frameAt word).parents.even ((parentsAt_valid word).even_parity) (frameAt word).eps

/-- The chain-sheet identity at the sheet placement: `h'_η(Z x) = Fp(x − e) − h0(x) + siblingSlope(x) + K'`, from
`sheetDifference_identifies` and `Ξ = G∘Z − h'∘Z`. -/
theorem i3_chainSheet_identity {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hG : (frameAt (conjWord word)).Packet (standardField (conjWord word))) :
    ∃ K' : ℤ, ∀ x : Site,
      (frameAt (conjWord word)).chainSheet (standardField (conjWord word)) (frameAt word).eps (i3Z x) =
        quarterTurnField (standardField (conjWord word)) (x - (frameAt word).sheetOffset) - harmonicGrid x +
          (frameAt word).siblingSlope x + K' := by
  obtain ⟨K, hK⟩ := sheetDifference_identifies hw hG
  refine ⟨(frameAt word).sheetConstant - K, fun x => ?_⟩
  have h1 := hK (x + (frameAt word).sheetShift)
  have hx : x + (frameAt word).sheetShift - (frameAt word).sheetShift = x := add_sub_cancel_right x _
  unfold ChildFrame.sheetC ChildFrame.sheetA at h1
  rw [hx] at h1
  have hΞ : FLatticePaper.earlierChainPrice (standardField (conjWord word))
      (frameAt (conjWord word)).parents.odd (frameAt (oddBirthPrefix word)).eps (frameAt word).eps
      (-x.2, x.1 - 1) =
      standardField (conjWord word) (i3Z x) -
        (frameAt (conjWord word)).chainSheet (standardField (conjWord word)) (frameAt word).eps (i3Z x) := by
    have e1 : FLatticePaper.earlierChainPrice (standardField (conjWord word))
        (frameAt (conjWord word)).parents.odd (frameAt (oddBirthPrefix word)).eps (frameAt word).eps
        (-x.2, x.1 - 1) = sheetChainPotential word (standardField (conjWord word)) x := rfl
    rw [e1, i3_sheet_eq_chainPotential, (frameAt (conjWord word)).i3_chainPotential_eq]
  rw [hΞ] at h1
  have hq : quarterTurnField (standardField (conjWord word)) x =
      standardField (conjWord word) (i3Z x) + harmonicGrid x := by
    unfold quarterTurnField
    rw [i3_mapSite_eq]
  linarith

/-- **The C-sheet permits have the quota at the word's own phase**: the reflected chain policy, pulled back by `Z(· + e)`,
is a quota for the quarter-turned field, and lies in the permit relation `Ξ(c + e) ≤ Ξ(i + e)` (the monotonicity of the chain
potential along the reflected policy). This is the field `permitC` of `SheetLocalInputs`. -/
theorem i3_permitC_of_strong {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (h : StrongEstimates (conjWord word)) :
    PermitLocal (quarterTurnField (standardField (conjWord word)))
      (fun c i => sheetChainPotential word (standardField (conjWord word)) (c + (frameAt word).sheetOffset) ≤
        sheetChainPotential word (standardField (conjWord word)) (i + (frameAt word).sheetOffset)) := by
  have hη := (frameAt word).eps_unit
  obtain ⟨cp, hmH, hqH, -⟩ := h.chain_data (frameAt word).eps hη
  obtain ⟨K', hid⟩ := i3_chainSheet_identity hw h.packet
  have he := i3_evenSite_sheetOffset word
  have hsl : ∀ c, laplacian (fun x => (frameAt word).siblingSlope (x + (frameAt word).sheetOffset)) c = 0 :=
    fun c => i3_laplacian_siblingSlope_shift (frameAt word) _ c
  have hlap := fun c => i3_laplacian_shift_of_identity he hsl hid c
  have hT := i3_retainQuota_shift_Z (R := ReflectedPolicy (frameAt (conjWord word)).centre
    ((frameAt word).eps • (frameAt (conjWord word)).shortShift - (frameAt (conjWord word)).parentShift) cp) he hlap hqH
  have hsub : ∀ c i, ReflectedPolicy (frameAt (conjWord word)).centre
      ((frameAt word).eps • (frameAt (conjWord word)).shortShift - (frameAt (conjWord word)).parentShift) cp
      (i3Z (c + (frameAt word).sheetOffset)) (i3Z (i + (frameAt word).sheetOffset)) →
      sheetChainPotential word (standardField (conjWord word)) (c + (frameAt word).sheetOffset) ≤
        sheetChainPotential word (standardField (conjWord word)) (i + (frameAt word).sheetOffset) := by
    intro c i hp
    rw [i3_sheet_eq_chainPotential, i3_sheet_eq_chainPotential]
    exact hmH (i3Z (c + (frameAt word).sheetOffset)) (i3Z (i + (frameAt word).sheetOffset)) hp
  rw [← retainQuota_iff_permitLocal]
  constructor
  · intro c hc
    obtain ⟨a, b⟩ := hT.1 c hc
    exact ⟨hsub c _ a, hsub c _ b⟩
  · intro c hc
    rcases hT.2 c hc with a | b
    · exact Or.inl (hsub c _ a)
    · exact Or.inr (hsub c _ b)

end FLatticePaper.Induction
