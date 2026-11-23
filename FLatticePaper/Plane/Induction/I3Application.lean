import FLatticePaper.Plane.Induction.I3Unit
import FLatticePaper.Plane.Induction.StrongEstimates
import FLatticePaper.Plane.Induction.SheetMinFromConj
import FLatticePaper.Plane.Induction.WordInduction

/-! Task 38: the I3 application at the earlier word, and the bridge to the sheet potential `Ξ`.

* `i3_chainPotential_unit_of_frame`: for a child frame, a packet `G` and a phase `η ∈ {1, −1}`, the chain potential
  `Φ_η = G − chainSheet_η` has unit increments on every edge, from the unit slip and price of `G`, the no-cross price stars,
  and the two signed policies of that phase.
* `i3_chainPotential_unit_of_strong`: the phase `ε_u` of the earlier word `u`, from `StrongEstimates u`.
* `i3_sheet_eq_chainPotential`: `Ξ_word(x) = Φ_η(Z x)` exactly, with `η = eps(word)` and `Z x = (−x₂, x₁ − 1)`. It uses
  `oldOr = ε_u` (`i3_eps_swap`), which comes from `rotate_parentsAt` and the halving determinant identity.
* `i3_sheet_unit_of_strong`: unit increments of `Ξ_word` at the matching phase `eps(word) = ε_u`. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- The quarter-turn offset `Z x = (−x₂, x₁ − 1)` of the sheet potential. -/
def i3Z (x : Site) : Site := (-x.2, x.1 - 1)

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

theorem i3_evenSite_Z (x : Site) : EvenSite (i3Z x) ↔ ¬ EvenSite x := by
  unfold EvenSite
  simp only [i3Z]
  constructor <;> intro h <;> omega

theorem i3_Z_neg_even {x : Site} (hx : EvenSite x) : i3Z (incomingNeg x) = incomingNeg (i3Z x) := by
  have hZ : ¬ EvenSite (i3Z x) := fun h => ((i3_evenSite_Z x).mp h) hx
  unfold incomingNeg
  rw [if_pos hx, if_neg hZ]
  ext <;> simp [i3Z]

theorem i3_Z_pos_even {x : Site} (hx : EvenSite x) : i3Z (incomingPos x) = incomingPos (i3Z x) := by
  have hZ : ¬ EvenSite (i3Z x) := fun h => ((i3_evenSite_Z x).mp h) hx
  unfold incomingPos
  rw [if_pos hx, if_neg hZ]
  ext <;> simp [i3Z]

theorem i3_Z_neg_odd {x : Site} (hx : ¬ EvenSite x) : i3Z (incomingNeg x) = incomingPos (i3Z x) := by
  have hZ : EvenSite (i3Z x) := (i3_evenSite_Z x).mpr hx
  unfold incomingNeg incomingPos
  rw [if_neg hx, if_pos hZ]
  ext <;> simp [i3Z]
  ring

theorem i3_Z_pos_odd {x : Site} (hx : ¬ EvenSite x) : i3Z (incomingPos x) = incomingNeg (i3Z x) := by
  have hZ : EvenSite (i3Z x) := (i3_evenSite_Z x).mpr hx
  unfold incomingNeg incomingPos
  rw [if_neg hx, if_pos hZ]
  ext <;> simp [i3Z]
  ring

/-- The quarter turn preserves the edge relation. -/
theorem i3_edge_Z {i c : Site} (h : Edge i c) : Edge (i3Z i) (i3Z c) := by
  unfold Edge at h ⊢
  by_cases hc : EvenSite c
  · rcases h with rfl | rfl
    · exact Or.inl (by rw [i3_Z_neg_even hc])
    · exact Or.inr (by rw [i3_Z_pos_even hc])
  · rcases h with rfl | rfl
    · exact Or.inr (by rw [i3_Z_neg_odd hc])
    · exact Or.inl (by rw [i3_Z_pos_odd hc])

/-- Halving identity: with `p + q` even, the rotated even vector against the rotated odd one has the determinant of the pair. -/
theorem i3_det_halved (p q r s : ℤ) (hE : (p + q) % 2 = 0) :
    (q - p) / 2 * (s + r) - (s - r) * ((q + p) / 2) = r * q - p * s := by
  have ha : 2 * ((q - p) / 2) = q - p := by omega
  have hb : 2 * ((q + p) / 2) = q + p := by omega
  have key : 2 * ((q - p) / 2 * (s + r) - (s - r) * ((q + p) / 2)) = 2 * (r * q - p * s) := by
    linear_combination (s + r) * ha - (s - r) * hb
  linarith

/-- The two signs of a swapped word agree: the quarter turn of the earlier parents has the same determinant. -/
theorem i3_eps_swap (b : Word) : (frameAt (b.map Digit.swapTwoThree)).eps = (frameAt b).eps := by
  have hv := parentsAt_valid b
  have hrot : parentsAt (b.map Digit.swapTwoThree) = (parentsAt b).rotate :=
    (rotate_parentsAt b).symm
  have hE : ((parentsAt b).even.num + (parentsAt b).even.den) % 2 = 0 := hv.even_parity
  show (parentsAt (b.map Digit.swapTwoThree)).odd.det (parentsAt (b.map Digit.swapTwoThree)).even
      = (parentsAt b).odd.det (parentsAt b).even
  rw [hrot]
  simp only [Parents.rotate]
  rw [Fraction.rotate_of_even hv.even_parity, Fraction.rotate_of_odd hv.odd_parity]
  unfold Fraction.det
  exact i3_det_halved _ _ _ _ hE

/-- The earlier chain shift is `η σ − v` when the earlier sign is the frame's own sign. -/
theorem i3_earlierChainShift_eq (fr : ChildFrame) (oldOr orient : ℤ) (h : oldOr = fr.eps) :
    earlierChainShift fr.parents.odd oldOr orient = orient • fr.shortShift - fr.parentShift := by
  subst h
  ext <;> simp [earlierChainShift, ChildFrame.shortShift, ChildFrame.parentShift] <;> ring

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
      laplacian (fun w : Site => frame.eps * frame.parents.odd.num * w.1
        + -(frame.eps * frame.parents.odd.den) * w.2 +
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

/-- **The chain potential of phase `η` has unit increments**, from the packet of `G` and the two signed policies of that
phase. -/
theorem i3_chainPotential_unit_of_frame (frame : ChildFrame) (G : Field) (η : ℤ) (hη : η = 1 ∨ η = -1)
    (hP : frame.Packet G)
    (hU : HasUnitSlip G (fun z => G (z + frame.shortShift)))
    (hPU : HasUnitPrice frame G) (hPN : NoPriceSaddle frame G)
    {relF relH : Site → Site → Prop}
    (hqF : RetainQuota G relF) (hqH : RetainQuota (fun z => frame.chainSheet G η z) relH)
    (hmF : NonincreasingAlong (fun z => frame.chainPotential G η z) relF)
    (hmH : NondecreasingAlong (fun z => frame.chainPotential G η z) relH) :
    ∀ c i, Edge i c →
      -1 ≤ frame.chainPotential G η i - frame.chainPotential G η c ∧
        frame.chainPotential G η i - frame.chainPotential G η c ≤ 1 := by
  have hs_even : EvenSite (η • frame.shortShift) := i3_evenSite_smul_shortShift frame η
  have hΦ : ∀ z, frame.chainPotential G η z = G z - frame.chainSheet G η z :=
    fun z => frame.i3_chainPotential_eq G η z
  have hfun : (fun z => frame.chainPotential G η z) = fun z => G z - frame.chainSheet G η z :=
    funext hΦ
  -- the raw slip `G − G(· + η σ)` has unit increments
  have hD : ∀ c i, Edge i c →
      -1 ≤ (G i - G (i + η • frame.shortShift)) - (G c - G (c + η • frame.shortShift)) ∧
        (G i - G (i + η • frame.shortShift)) - (G c - G (c + η • frame.shortShift)) ≤ 1 := by
    intro c i hi
    rcases hη with h1 | h1
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
  -- the shifted primitive price `G(· + η σ) − chainSheet` is the price at the translated site
  have hSH : ∀ z, G (z + η • frame.shortShift) - frame.chainSheet G η z =
      frame.price G (z + η • frame.shortShift) := by
    intro z
    unfold ChildFrame.price ChildFrame.chainSheet
    ring
  have hQ : ∀ c i, Edge i c →
      -1 ≤ (G (i + η • frame.shortShift) - frame.chainSheet G η i) -
          (G (c + η • frame.shortShift) - frame.chainSheet G η c) ∧
        (G (i + η • frame.shortShift) - frame.chainSheet G η i) -
          (G (c + η • frame.shortShift) - frame.chainSheet G η c) ≤ 1 := by
    intro c i hi
    rw [hSH i, hSH c]
    have h := hPU (c + η • frame.shortShift) (i + η • frame.shortShift)
      (i3_edge_translate _ hs_even hi)
    simp only [priceIncrement] at h
    exact h
  have hQno : NoCrossStars (fun z => G (z + η • frame.shortShift) - frame.chainSheet G η z) := by
    have hfun' : (fun z => G (z + η • frame.shortShift) - frame.chainSheet G η z) =
        fun z => frame.price G (z + η • frame.shortShift) := funext hSH
    rw [hfun']
    exact frame.i3_noCrossStars_shift G hPU hPN _ hs_even
  have hHb : ∀ c, laplacian (fun z => frame.chainSheet G η z) c = -1 ∨
      laplacian (fun z => frame.chainSheet G η z) c = 0 := by
    intro c
    rw [frame.i3_laplacian_chainSheet G η c]
    exact hP.binary _
  have hmF' : NonincreasingAlong (fun x => G x - frame.chainSheet G η x) relF := by
    rw [← hfun]
    exact hmF
  have hmH' : NondecreasingAlong (fun x => G x - frame.chainSheet G η x) relH := by
    rw [← hfun]
    exact hmH
  have key := unit_increments_of_summands
    (F := G) (S := fun z => G (z + η • frame.shortShift))
    (H := fun z => frame.chainSheet G η z)
    hD hQ hQno hP.binary hHb hqF hqH hmF' hmH'
  intro c i hi
  have hk := key c i hi
  simp only [hΦ]
  exact hk

/-- **The chain potential of the earlier word has unit increments**, at its own phase `ε_u`, from its strong estimates. -/
theorem i3_chainPotential_unit_of_strong {u : Word} (h : StrongEstimates u) :
    ∀ c i, Edge i c →
      -1 ≤ (frameAt u).chainPotential (standardField u) (frameAt u).eps i
          - (frameAt u).chainPotential (standardField u) (frameAt u).eps c ∧
        (frameAt u).chainPotential (standardField u) (frameAt u).eps i
          - (frameAt u).chainPotential (standardField u) (frameAt u).eps c ≤ 1 := by
  obtain ⟨relF, hqF, hmF, -⟩ := h.F2F3_policy
  obtain ⟨cp, -, R, w, hmH, hqH, -⟩ := h.F2F4_chain
  exact i3_chainPotential_unit_of_frame (frameAt u) (standardField u) (frameAt u).eps
    (frameAt u).eps_unit h.packet h.F1_unitSlip h.F1_unitPrice h.F1_noPriceSaddle hqF hqH hmF hmH

/-- **The sheet potential is the chain potential of the word's own phase**: `Ξ_word(x) = Φ_η(Z x)` exactly, with
`η = eps(word)` and `u = conjWord word`. -/
theorem i3_sheet_eq_chainPotential (word : Word) (G : Field) (x : Site) :
    sheetChainPotential word G x =
      (frameAt (conjWord word)).chainPotential G (frameAt word).eps (i3Z x) := by
  have hε : (frameAt (oddBirthPrefix word)).eps = (frameAt (conjWord word)).eps :=
    (i3_eps_swap (oddBirthPrefix word)).symm
  unfold sheetChainPotential FLatticePaper.earlierChainPrice
  rw [i3_earlierChainShift_eq _ _ _ hε, hε]
  unfold ChildFrame.chainPotential ChildFrame.slip ChildFrame.price i3Z Fraction.transverseGrade
  unfold ChildFrame.parentSlope ChildFrame.shortShift ChildFrame.parentShift
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, add_sub_assoc]
  ring

/-- **Unit increments of the sheet potential at the matching phase** `eps(word) = ε_u`, from the strong estimates of the
earlier word `conjWord word`. -/
theorem i3_sheet_unit_of_strong {word : Word} (h : StrongEstimates (conjWord word))
    (hphase : (frameAt word).eps = (frameAt (conjWord word)).eps) :
    ∀ c i : Site, Edge i c →
      -1 ≤ sheetChainPotential word (standardField (conjWord word)) i
          - sheetChainPotential word (standardField (conjWord word)) c ∧
        sheetChainPotential word (standardField (conjWord word)) i
          - sheetChainPotential word (standardField (conjWord word)) c ≤ 1 := by
  intro c i hi
  have key := i3_chainPotential_unit_of_strong h (i3Z c) (i3Z i) (i3_edge_Z hi)
  rw [i3_sheet_eq_chainPotential, i3_sheet_eq_chainPotential, hphase]
  exact key

end FLatticePaper.Induction
