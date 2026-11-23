import FLatticePaper.Plane.Induction.W1TieBand
import FLatticePaper.Plane.Induction.I3Application
import FLatticePaper.Plane.Induction.SheetDifference
import FLatticePaper.Plane.Induction.W1HagreeNonfree

/-! # Task 84 (continued): the inputs of an M-white tie are ties, and the tie is the level set of the chain potential

* `inputs_tie_of_mwhite`: at a sheet point `c` where the sheet minimum `M = min(A, C)` is white (`laplacian M c = 0`) and `C c = A c`
  (a tie), both sheet inputs of `c` are ties. Proof: `Σ (A − M)(input) = lap A c − lap M c = lap A c ≥ 0` and `lap A c ∈ {−1, 0}` give
  `lap A c = 0` and every term `A − M` at the inputs vanishes; the same for `C − M`. Hence `A = M = C` at both inputs.
* `tie_iff_chain`: `C z − A z + Φ(i3Z(z − lv)) = K` with `Φ = frame.chainPotential G η`, `η = eps(word)` (the sheet difference identity
  with the chain potential identification `i3_sheet_eq_chainPotential`). So a tie at `c` is `Φ(zTurn(c − lv)) = K`.
* `parent_inputs_tie`: at an M-white tie, the two parent inputs of the parent root `z = zTurn(c − lv)` have `Φ = K`. -/

namespace FLatticePaper.W1TieInputs

open Farey FLatticePaper FLatticePaper.Induction

theorem sheetA_binary (frame : ChildFrame) (Fp : Field) (hbin : ∀ x, laplacian Fp x = -1 ∨ laplacian Fp x = 0) (x : Site) :
    laplacian (frame.sheetA Fp) x = -1 ∨ laplacian (frame.sheetA Fp) x = 0 := by
  have h : laplacian (frame.sheetA Fp) x = laplacian Fp (x - frame.sheetShift) :=
    laplacian_sub_even Fp frame.sheetShift frame.evenSite_sheetShift x
  rw [h]
  exact hbin _

theorem sheetC_binary (frame : ChildFrame) (Fp : Field) (hbin : ∀ x, laplacian Fp x = -1 ∨ laplacian Fp x = 0) (x : Site) :
    laplacian (frame.sheetC Fp) x = -1 ∨ laplacian (frame.sheetC Fp) x = 0 := by
  rw [frame.laplacian_sheetC Fp x]
  exact hbin _

/-- **The inputs of an M-white tie are ties** (task 84). -/
theorem inputs_tie_of_mwhite (frame : ChildFrame) (Fp : Field)
    (hbin : ∀ x, laplacian Fp x = -1 ∨ laplacian Fp x = 0) (c : Site)
    (hM : laplacian (frame.sheetMin Fp) c = 0) (htie : frame.sheetC Fp c = frame.sheetA Fp c) :
    ∀ i : Site, (i = incomingNeg c ∨ i = incomingPos c) → frame.sheetC Fp i = frame.sheetA Fp i := by
  have hMdef : ∀ x, frame.sheetMin Fp x = min (frame.sheetA Fp x) (frame.sheetC Fp x) := fun x => rfl
  have hMc : frame.sheetMin Fp c = frame.sheetA Fp c := by
    rw [hMdef, htie, min_self]
  have eM : (frame.sheetMin Fp (incomingNeg c) - frame.sheetMin Fp c) +
      (frame.sheetMin Fp (incomingPos c) - frame.sheetMin Fp c) = 0 := hM
  have eA : laplacian (frame.sheetA Fp) c =
      (frame.sheetA Fp (incomingNeg c) - frame.sheetA Fp c) + (frame.sheetA Fp (incomingPos c) - frame.sheetA Fp c) := rfl
  have eC : laplacian (frame.sheetC Fp) c =
      (frame.sheetC Fp (incomingNeg c) - frame.sheetC Fp c) + (frame.sheetC Fp (incomingPos c) - frame.sheetC Fp c) := rfl
  have hMsum : frame.sheetMin Fp (incomingNeg c) + frame.sheetMin Fp (incomingPos c) = 2 * frame.sheetA Fp c := by
    linarith [eM, hMc]
  have hMsumC : frame.sheetMin Fp (incomingNeg c) + frame.sheetMin Fp (incomingPos c) = 2 * frame.sheetC Fp c := by
    linarith [hMsum, htie]
  -- the A side
  have hA1 : frame.sheetMin Fp (incomingNeg c) ≤ frame.sheetA Fp (incomingNeg c) := min_le_left _ _
  have hA2 : frame.sheetMin Fp (incomingPos c) ≤ frame.sheetA Fp (incomingPos c) := min_le_left _ _
  have hAsum : laplacian (frame.sheetA Fp) c =
      (frame.sheetA Fp (incomingNeg c) - frame.sheetMin Fp (incomingNeg c)) +
        (frame.sheetA Fp (incomingPos c) - frame.sheetMin Fp (incomingPos c)) := by
    rw [eA]
    linarith [hMsum]
  have hAnn : 0 ≤ laplacian (frame.sheetA Fp) c := by linarith [hAsum, hA1, hA2]
  have hA0 : laplacian (frame.sheetA Fp) c = 0 := by
    rcases sheetA_binary frame Fp hbin c with h | h
    · linarith
    · exact h
  have hAN1 : frame.sheetA Fp (incomingNeg c) - frame.sheetMin Fp (incomingNeg c) = 0 := by
    linarith [hAsum, hA0, hA1, hA2]
  have hAN2 : frame.sheetA Fp (incomingPos c) - frame.sheetMin Fp (incomingPos c) = 0 := by
    linarith [hAsum, hA0, hA1, hA2]
  -- the C side
  have hC1 : frame.sheetMin Fp (incomingNeg c) ≤ frame.sheetC Fp (incomingNeg c) := min_le_right _ _
  have hC2 : frame.sheetMin Fp (incomingPos c) ≤ frame.sheetC Fp (incomingPos c) := min_le_right _ _
  have hCsum : laplacian (frame.sheetC Fp) c =
      (frame.sheetC Fp (incomingNeg c) - frame.sheetMin Fp (incomingNeg c)) +
        (frame.sheetC Fp (incomingPos c) - frame.sheetMin Fp (incomingPos c)) := by
    rw [eC]
    linarith [hMsumC]
  have hCnn : 0 ≤ laplacian (frame.sheetC Fp) c := by linarith [hCsum, hC1, hC2]
  have hC0 : laplacian (frame.sheetC Fp) c = 0 := by
    rcases sheetC_binary frame Fp hbin c with h | h
    · linarith
    · exact h
  have hCN1 : frame.sheetC Fp (incomingNeg c) - frame.sheetMin Fp (incomingNeg c) = 0 := by
    linarith [hCsum, hC0, hC1, hC2]
  have hCN2 : frame.sheetC Fp (incomingPos c) - frame.sheetMin Fp (incomingPos c) = 0 := by
    linarith [hCsum, hC0, hC1, hC2]
  intro i hi
  rcases hi with h | h
  · rw [h]
    linarith [hAN1, hCN1]
  · rw [h]
    linarith [hAN2, hCN2]

/-- **A tie is the level set of the chain potential** (task 84): `C z − A z + Φ(i3Z(z − lv)) = K` for the chain potential of the phase
`η = eps(word)` of the conjugate frame. -/
theorem tie_iff_chain (word : Word) (h : ∃ x ∈ word, x ≠ Digit.three) {G : Field}
    (hG : (frameAt (conjWord word)).Packet G) :
    ∃ K : ℤ, ∀ z : Site,
      (frameAt word).sheetC (quarterTurnField G) z - (frameAt word).sheetA (quarterTurnField G) z +
        (frameAt (conjWord word)).chainPotential G (frameAt word).eps
          (i3Z (z - (frameAt word).sheetShift)) = K := by
  obtain ⟨K, hK⟩ := sheetDifference_identifies h hG
  refine ⟨K, fun z => ?_⟩
  have h2 := i3_sheet_eq_chainPotential word G (z - (frameAt word).sheetShift)
  rw [← h2]
  exact hK z

/-- The chain potential of the earlier word, at the phase of the word (`Φ` of the tie band). -/
def chainPot (word : Word) (G : Field) (x : Site) : ℤ :=
  (frameAt (conjWord word)).chainPotential G (frameAt word).eps x

/-- **The parent inputs of an M-white tie are in the tie band** (task 84): at a sheet tie `c` whose sheet minimum is white, the two
inputs of the parent root `z = zTurn(c − lv)` satisfy `chainPot = K`. -/
theorem parent_inputs_tie (word : Word) {G : Field}
    (hG : (frameAt (conjWord word)).Packet G) {K : ℤ}
    (hK : ∀ z : Site, (frameAt word).sheetC (quarterTurnField G) z - (frameAt word).sheetA (quarterTurnField G) z +
      chainPot word G (i3Z (z - (frameAt word).sheetShift)) = K)
    (c : Site) (hM : laplacian ((frameAt word).sheetMin (quarterTurnField G)) c = 0)
    (htie : (frameAt word).sheetC (quarterTurnField G) c = (frameAt word).sheetA (quarterTurnField G) c) :
    ∀ p : Site, (p = incomingNeg (zTurn (c - (frameAt word).sheetShift)) ∨
      p = incomingPos (zTurn (c - (frameAt word).sheetShift))) → chainPot word G p = K := by
  have hbin : ∀ x, laplacian (quarterTurnField G) x = -1 ∨ laplacian (quarterTurnField G) x = 0 :=
    fun x => quarterTurnField_binary hG.binary x
  have hlv : EvenSite (frameAt word).sheetShift := (frameAt word).evenSite_sheetShift
  have hn := FLatticePaper.W1HagreeNonfree.zTurn_neighbors c (frameAt word).sheetShift hlv
  intro p hp
  have key : ∃ i : Site, (i = incomingNeg c ∨ i = incomingPos c) ∧
      zTurn (i - (frameAt word).sheetShift) = p := by
    by_cases hc : EvenSite c
    · rcases hp with hp | hp
      · exact ⟨incomingNeg c, Or.inl rfl, by rw [(hn.1 hc).1, hp]⟩
      · exact ⟨incomingPos c, Or.inr rfl, by rw [(hn.1 hc).2, hp]⟩
    · rcases hp with hp | hp
      · exact ⟨incomingPos c, Or.inr rfl, by rw [(hn.2 hc).2, hp]⟩
      · exact ⟨incomingNeg c, Or.inl rfl, by rw [(hn.2 hc).1, hp]⟩
  obtain ⟨i, hi, hzi⟩ := key
  have hiT : (frameAt word).sheetC (quarterTurnField G) i = (frameAt word).sheetA (quarterTurnField G) i :=
    inputs_tie_of_mwhite (frameAt word) (quarterTurnField G) hbin c hM htie i hi
  have h3 := hK i
  rw [hiT, sub_self, zero_add] at h3
  rw [← hzi]
  exact h3

/-- **The chain of an M-white tie stays in the tie band** (task 84): with the root `z = zTurn(c − lv)` in the tie band, a parent input
`p0` of `z` in the tie band (`parent_inputs_tie`), and the chain `p0 → p1 → p2 → z` of retained edges along which `chainPot` is
nonincreasing, the points `p1`, `p2` lie in the tie band too. -/
theorem chain_in_band (word : Word) {G : Field} {K : ℤ} {Rel : Site → Site → Prop}
    (hmono : NonincreasingAlong (chainPot word G) Rel) {z p0 p1 p2 : Site}
    (hz : chainPot word G z = K) (hp0 : chainPot word G p0 = K)
    (h0 : Rel p0 p1) (h1 : Rel p1 p2) (h2 : Rel p2 z) :
    chainPot word G p1 = K ∧ chainPot word G p2 = K :=
  FLatticePaper.W1TieBand.chain_sandwich hmono h0 h1 h2 hz hp0

end FLatticePaper.W1TieInputs
