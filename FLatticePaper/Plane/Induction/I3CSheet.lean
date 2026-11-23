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

theorem i3_tGrade_add (frame : ChildFrame) (x k : Site) :
    frame.tGrade (x + k) - frame.tGrade x = frame.child.num * k.1 - frame.child.den * k.2 := by
  unfold ChildFrame.tGrade
  simp only [Prod.fst_add, Prod.snd_add]
  ring

theorem i3_odd_modifiedDeck_kernel (f : Fraction) (hodd : f.Odd) :
    f.modifiedDeck.kernel = (2 * f.den, 2 * f.num) := by
  have hm : f.periodMultiplicity = 2 := by
    unfold Fraction.periodMultiplicity
    have h1 : (f.num + f.den) % 2 = 1 := hodd
    exact if_neg (by omega)
  simp only [Fraction.modifiedDeck, hm]

theorem i3_odd_modifiedDeck_transverse (f : Fraction) :
    f.modifiedDeck.transverse = (f.num - f.den, f.num + f.den) := by
  simp only [Fraction.modifiedDeck, Fraction.unmodifiedDeck]

theorem i3_child_num (word : Word) :
    (frameAt word).child.num = 2 * (parentsAt word).odd.num + (parentsAt word).even.num := by
  show 2 * (parentsAt word).odd.num + 1 * (parentsAt word).even.num = _
  ring

theorem i3_child_den (word : Word) :
    (frameAt word).child.den = 2 * (parentsAt word).odd.den + (parentsAt word).even.den := by
  show 2 * (parentsAt word).odd.den + 1 * (parentsAt word).even.den = _
  ring

/-- **The restricted no-fort condition of the C sheet** (the field `noC`): the reflected chain rank with weights `(a_*, 2)`
has increments `−2η` and `−a_*` along the odd deck, which are the increments of `tGrade` (from `eps = N d − D n`). -/
theorem i3_noC_of_strong {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (h : StrongEstimates (conjWord word)) :
    RestrictedNoFort (quarterTurnField (standardField (conjWord word))) (frameAt word).tGrade
      (fun c i => sheetChainPotential word (standardField (conjWord word)) (c + (frameAt word).sheetOffset) ≤
        sheetChainPotential word (standardField (conjWord word)) (i + (frameAt word).sheetOffset)) := by
  have hη := (frameAt word).eps_unit
  obtain ⟨cp, hmH, hqH, hrank⟩ := h.chain_data (frameAt word).eps hη
  obtain ⟨K', hid⟩ := i3_chainSheet_identity hw h.packet
  have he := i3_evenSite_sheetOffset word
  have hsl : ∀ c, laplacian (fun x => (frameAt word).siblingSlope (x + (frameAt word).sheetOffset)) c = 0 :=
    fun c => i3_laplacian_siblingSlope_shift (frameAt word) _ c
  have hlap := fun c => i3_laplacian_shift_of_identity he hsl hid c
  have hT := i3_retainQuota_shift_Z (R := ReflectedPolicy (frameAt (conjWord word)).centre
    ((frameAt word).eps • (frameAt (conjWord word)).shortShift - (frameAt (conjWord word)).parentShift) cp) he hlap hqH
  have hodd : (parentsAt word).odd.Odd := (parentsAt_valid word).odd_parity
  have hbnd := (parentsAt_valid word).odd_bounds
  have hebnd := (parentsAt_valid word).even_bounds
  have hcn := i3_child_num word
  have hcd := i3_child_den word
  have hpos_a : 0 < (frameAt word).child.den * ((parentsAt word).odd.den + (parentsAt word).odd.num) +
      (frameAt word).child.num * ((parentsAt word).odd.den - (parentsAt word).odd.num) := by
    rw [hcn, hcd]
    obtain ⟨hD, hN0, hNle⟩ := hbnd
    obtain ⟨hd, hn0, hnle⟩ := hebnd
    have h1 : 0 ≤ (2 * (parentsAt word).odd.num + (parentsAt word).even.num) *
        ((parentsAt word).odd.den - (parentsAt word).odd.num) :=
      mul_nonneg (by linarith) (by linarith)
    have h2 : 0 < (2 * (parentsAt word).odd.den + (parentsAt word).even.den) *
        ((parentsAt word).odd.den + (parentsAt word).odd.num) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  obtain ⟨rk, lam, hlam, hstrict, hU, hV⟩ :=
    hrank ((frameAt word).child.den * ((parentsAt word).odd.den + (parentsAt word).odd.num) +
      (frameAt word).child.num * ((parentsAt word).odd.den - (parentsAt word).odd.num)) 2 hpos_a (by norm_num)
  -- the C-rank R(x) = rk(Z(x + e)) has increments −2η along the kernel and −a_* along the transverse
  have hK : ∀ x, rk (i3Z (x + (parentsAt word).odd.modifiedDeck.kernel + (frameAt word).sheetOffset)) -
      rk (i3Z (x + (frameAt word).sheetOffset)) =
      lam * ((frameAt word).tGrade (x + (parentsAt word).odd.modifiedDeck.kernel) - (frameAt word).tGrade x) := by
    intro x
    have hz : i3Z (x + (parentsAt word).odd.modifiedDeck.kernel + (frameAt word).sheetOffset) =
        i3Z (x + (frameAt word).sheetOffset) +
          (frameAt (conjWord word)).child.modifiedDeck.transverse := by
      rw [add_right_comm x _ (frameAt word).sheetOffset, i3Z_add, i3_child_kernel hw]
    have hgK : (frameAt word).tGrade (x + (parentsAt word).odd.modifiedDeck.kernel) - (frameAt word).tGrade x =
        -(2 * (frameAt word).eps) := by
      rw [i3_tGrade_add, i3_odd_modifiedDeck_kernel _ hodd]
      dsimp only
      have he' : (frameAt word).eps = (parentsAt word).odd.num * (frameAt word).child.den -
          (parentsAt word).odd.den * (frameAt word).child.num := (frameAt word).eps_eq
      linear_combination 2 * he'
    rw [hz, hV (i3Z (x + (frameAt word).sheetOffset)), hgK]
    ring
  have hT' : ∀ x, rk (i3Z (x + (parentsAt word).odd.modifiedDeck.transverse + (frameAt word).sheetOffset)) -
      rk (i3Z (x + (frameAt word).sheetOffset)) =
      lam * ((frameAt word).tGrade (x + (parentsAt word).odd.modifiedDeck.transverse) - (frameAt word).tGrade x) := by
    intro x
    have hz : i3Z (x + (parentsAt word).odd.modifiedDeck.transverse + (frameAt word).sheetOffset) =
        i3Z (x + (frameAt word).sheetOffset) + -(frameAt (conjWord word)).child.modifiedDeck.kernel := by
      rw [add_right_comm x _ (frameAt word).sheetOffset, i3Z_add, i3_child_transverse hw]
    have hU' := hU (i3Z (x + (frameAt word).sheetOffset) + -(frameAt (conjWord word)).child.modifiedDeck.kernel)
    rw [neg_add_cancel_right] at hU'
    have hgT : (frameAt word).tGrade (x + (parentsAt word).odd.modifiedDeck.transverse) - (frameAt word).tGrade x =
        -((frameAt word).child.den * ((parentsAt word).odd.den + (parentsAt word).odd.num) +
          (frameAt word).child.num * ((parentsAt word).odd.den - (parentsAt word).odd.num)) := by
      rw [i3_tGrade_add, i3_odd_modifiedDeck_transverse]
      dsimp only
      ring
    rw [hz, hgT]
    linear_combination (-1 : ℤ) * hU'
  have hbin : ∀ c, laplacian (quarterTurnField (standardField (conjWord word))) c = -1 ∨
      laplacian (quarterTurnField (standardField (conjWord word))) c = 0 :=
    fun c => quarterTurnField_binary h.packet.binary c
  have hcon_T := isConstrainedBurningRank_of_strict_quota
    (rank := fun x => rk (i3Z (x + (frameAt word).sheetOffset))) hbin hT
    (fun c i _ hp => hstrict _ _ hp)
  have hsub : ∀ c i, ReflectedPolicy (frameAt (conjWord word)).centre
      ((frameAt word).eps • (frameAt (conjWord word)).shortShift - (frameAt (conjWord word)).parentShift) cp
      (i3Z (c + (frameAt word).sheetOffset)) (i3Z (i + (frameAt word).sheetOffset)) →
      sheetChainPotential word (standardField (conjWord word)) (c + (frameAt word).sheetOffset) ≤
        sheetChainPotential word (standardField (conjWord word)) (i + (frameAt word).sheetOffset) := by
    intro c i hp
    rw [i3_sheet_eq_chainPotential, i3_sheet_eq_chainPotential]
    exact hmH (i3Z (c + (frameAt word).sheetOffset)) (i3Z (i + (frameAt word).sheetOffset)) hp
  have hcon := IsConstrainedBurningRank.mono hcon_T hsub
  have hint : (parentsAt word).odd.InUnitInterval := (parentsAt_valid word).odd_bounds
  exact restrictedNoFort_of_constrained_rankGrade (Fraction.det_modifiedDeck_pos hint)
    (fun x => rk (i3Z (x + (frameAt word).sheetOffset))) lam hlam hcon hK hT'

end FLatticePaper.Induction
