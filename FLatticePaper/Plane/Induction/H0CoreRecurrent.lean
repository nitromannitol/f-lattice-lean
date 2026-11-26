import FLatticePaper.Plane.Induction.H0Core
import FLatticePaper.Plane.Induction.SheetFort

/-! # The `H_0` core by the recurrence of the sheet minimum (Q23 paragraph 25)

For a fort `S` of a recurrent field `M`, the part `S ∩ openRect` is again a fort of `M` (an input of an interior site that lies in `S`
is interior, since the boundary candidates `H_0`, `V_0` are not called from the open rectangle: `minus_not_called`), and it is finite.
Recurrence (`RecurrentField`) empties it. The candidates `H_0` and `V_0` then force `(1,1) ∈ S`, which is interior, so `S = ∅`.
The recurrent field is the sheet minimum `MW word` (`SheetFort.sheetMin_recurrentField`, from the word and the strong estimates). -/

namespace FLatticePaper.H0Core

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1 FLatticePaper.FanTerminal

/-- A fort of a recurrent field has no interior point, when its boundary candidates are `H_0` and `V_0`. -/
theorem interior_empty_of_recurrent {M : Field} (frame : ChildFrame) (hrec : FLatticePaper.RecurrentField M)
    {S : Set Site} (hfort : IsIncomingFort M S)
    (hcand : ∀ z ∈ S, z ∈ frame.closedPolygon → ¬ frame.openRect z → z = hFirst ∨ z = vFirst) :
    ∀ z ∈ S, ¬ frame.openRect z := by
  have hT : IsIncomingFort M {y | y ∈ S ∧ frame.openRect y} := by
    intro x hx
    have hxS : x ∈ S := hx.1
    have hxo : frame.openRect x := hx.2
    have inner : ∀ i, (i = incomingNeg x ∨ i = incomingPos x) → i ∈ S → frame.openRect i := by
      intro i hi hiS
      by_contra hnot
      rcases hcand i hiS (FLatticePaper.W1Exit.rectInputs frame x hxo i hi) hnot with h | h
      · exact minus_not_called frame x hxo i (Or.inl h) hi
      · exact minus_not_called frame x hxo i (Or.inr h) hi
    rcases hfort x hxS with ⟨hl, hsome⟩ | ⟨hl, hn, hp⟩
    · rcases hsome with hn | hp
      · exact Or.inl ⟨hl, Or.inl ⟨hn, inner _ (Or.inl rfl) hn⟩⟩
      · exact Or.inl ⟨hl, Or.inr ⟨hp, inner _ (Or.inr rfl) hp⟩⟩
    · exact Or.inr ⟨hl, ⟨hn, inner _ (Or.inl rfl) hn⟩, ⟨hp, inner _ (Or.inr rfl) hp⟩⟩
  have hfin : {y | y ∈ S ∧ frame.openRect y}.Finite :=
    (FLatticePaper.FanTerminal.openRect_finite frame).subset (fun y hy => hy.2)
  have hempty := FLatticePaper.SheetFort.no_finite_fort_of_recurrent hrec hT hfin
  intro z hz ho
  have hmem : z ∈ {y | y ∈ S ∧ frame.openRect y} := ⟨hz, ho⟩
  rw [hempty] at hmem
  exact hmem

/-- **The minus core from recurrence.** A fort of a recurrent field whose boundary candidates are `H_0` and `V_0` is empty. -/
theorem h0_core_minus_recurrent {M : Field} (frame : ChildFrame) (hrec : FLatticePaper.RecurrentField M)
    {S : Set Site} (hfort : IsIncomingFort M S) (hsub : ∀ z ∈ S, z ∈ frame.closedPolygon)
    (hcand : ∀ z ∈ S, z ∈ frame.closedPolygon → ¬ frame.openRect z → z = hFirst ∨ z = vFirst) : S = ∅ := by
  have hint := interior_empty_of_recurrent frame hrec hfort hcand
  have hcW : FortAt (fun z => z = ((1 : ℤ), (0 : ℤ)) ∨ z = ((0 : ℤ), (0 : ℤ))) M S :=
    fortAt_of_incoming hfort
  have hH0 : hFirst ∉ S := by
    intro h
    have hfirst : hFirst = (1, 0) := rfl
    rw [hfirst] at h
    have hn : ((1 : ℤ), (-1 : ℤ)) ∉ S := fun hm => not_closed_one_neg frame (hsub _ hm)
    have hodd : ¬ EvenSite ((1 : ℤ), (0 : ℤ)) := by unfold EvenSite; simp
    have hinN : incomingNeg ((1 : ℤ), (0 : ℤ)) = ((1 : ℤ), (-1 : ℤ)) := by
      rw [incomingNeg_of_not_even _ hodd]; simp
    have hinP : incomingPos ((1 : ℤ), (0 : ℤ)) = ((1 : ℤ), (1 : ℤ)) := by
      rw [incomingPos_of_not_even _ hodd]; simp
    have hmem : ((1 : ℤ), (1 : ℤ)) ∈ S := by
      have := fort_pos_of_neg_not_fortAt hcW (Or.inl rfl) h (by rw [hinN]; exact hn)
      rw [hinP] at this
      exact this
    exact hint (1, 1) hmem (open_one_one frame)
  have hV0 : vFirst ∉ S := by
    intro h
    have hvfirst : vFirst = (0, 0) := rfl
    rw [hvfirst] at h
    have hn : ((-1 : ℤ), (0 : ℤ)) ∉ S := fun hm => not_closed_neg_one_zero frame (hsub _ hm)
    have hev : EvenSite ((0 : ℤ), (0 : ℤ)) := by unfold EvenSite; simp
    have hinN : incomingNeg ((0 : ℤ), (0 : ℤ)) = ((-1 : ℤ), (0 : ℤ)) := by
      rw [incomingNeg_of_even _ hev]; simp
    have hinP : incomingPos ((0 : ℤ), (0 : ℤ)) = ((1 : ℤ), (0 : ℤ)) := by
      rw [incomingPos_of_even _ hev]; simp
    have hH : ((1 : ℤ), (0 : ℤ)) ∈ S := by
      have := fort_pos_of_neg_not_fortAt hcW (Or.inr rfl) h (by rw [hinN]; exact hn)
      rw [hinP] at this
      exact this
    exact hH0 hH
  ext z
  constructor
  · intro hz
    have hcz : z = hFirst ∨ z = vFirst := by
      by_cases hopen : frame.openRect z
      · exact absurd hopen (fun ho => hint z hz ho)
      · exact hcand z hz (hsub z hz) hopen
    rcases hcz with rfl | rfl
    · exact absurd hz hH0
    · exact absurd hz hV0
  · intro hz
    exact absurd hz (Set.notMem_empty z)

/-- **The minus core at the sheet minimum of a word.** The recurrent field is `MW word` (`SheetFort.sheetMin_recurrentField`). -/
theorem h0_core_minus_word {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) {S : Set Site}
    (hfort : IsIncomingFort (FLatticePaper.W1MSheet.MW word) S)
    (hsub : ∀ z ∈ S, z ∈ (frameAt word).closedPolygon)
    (hcand : ∀ z ∈ S, z ∈ (frameAt word).closedPolygon → ¬ (frameAt word).openRect z → z = hFirst ∨ z = vFirst) :
    S = ∅ :=
  h0_core_minus_recurrent (frameAt word) (FLatticePaper.SheetFort.sheetMin_recurrentField hw hSE) hfort hsub hcand

/-- **Recurrence of an even translate.** If `M` is recurrent, so is `z ↦ M (z + V)` for an even `V`. -/
theorem recurrentField_translate {M : Field} (hrec : FLatticePaper.RecurrentField M) {V : Site} (hV : EvenSite V) :
    FLatticePaper.RecurrentField (fun z => M (z + V)) := by
  intro S hS hfort
  apply hrec (S.image (fun y => y + V)) (hS.image _)
  intro x hx
  rw [Finset.mem_coe, Finset.mem_image] at hx
  obtain ⟨y, hyS, rfl⟩ := hx
  have hy := hfort y (Finset.mem_coe.mpr hyS)
  rw [laplacian_translate_of_even M y V hV] at hy
  have hneg : incomingNeg (y + V) = incomingNeg y + V := incomingNeg_add_of_even y V hV
  have hpos : incomingPos (y + V) = incomingPos y + V := incomingPos_add_of_even y V hV
  have memN : ∀ a : Site, a ∈ (S : Set Site) → a + V ∈ ((S.image (fun y => y + V) : Finset Site) : Set Site) :=
    fun a ha => Finset.mem_coe.mpr (Finset.mem_image_of_mem (fun y => y + V) (Finset.mem_coe.mp ha))
  rcases hy with ⟨hl, hsome⟩ | ⟨hl, hn, hp⟩
  · rcases hsome with hn | hp
    · exact Or.inl ⟨hl, Or.inl (by rw [hneg]; exact memN _ hn)⟩
    · exact Or.inl ⟨hl, Or.inr (by rw [hpos]; exact memN _ hp)⟩
  · exact Or.inr ⟨hl, by rw [hneg]; exact memN _ hn, by rw [hpos]; exact memN _ hp⟩

/-- The interior of a plus fort is empty, from the recurrence of the translated sheet minimum. -/
theorem interior_empty_of_recurrent_plus {M : Field} (frame : ChildFrame) (hrec : FLatticePaper.RecurrentField M)
    {T : Set Site} (hfort : IsIncomingFort (fun z => M (z + plusV frame)) T)
    (hsub : ∀ z ∈ T, z + plusV frame ∈ frame.closedPolygon)
    (hcand : ∀ z ∈ T, z + plusV frame ∈ frame.closedPolygon → ¬ frame.openRect (z + plusV frame) →
      z = ((1 : ℤ), (0 : ℤ)) ∨ z = ((1 : ℤ), (-1 : ℤ))) :
    ∀ z ∈ T, ¬ frame.openRect (z + plusV frame) := by
  have hVe : EvenSite (plusV frame) := by
    unfold EvenSite
    have := plusV_even frame
    omega
  have hrecV := recurrentField_translate hrec hVe
  have hT' : IsIncomingFort (fun z => M (z + plusV frame))
      {y | y ∈ T ∧ frame.openRect (y + plusV frame)} := by
    intro x hx
    have hxT : x ∈ T := hx.1
    have hxo : frame.openRect (x + plusV frame) := hx.2
    have inner : ∀ i, (i = incomingNeg x ∨ i = incomingPos x) → i ∈ T →
        frame.openRect (i + plusV frame) := by
      intro i hi hiT
      by_contra hnot
      rcases hcand i hiT (hsub i hiT) hnot with h | h
      · exact plus_not_called frame x hxo i (Or.inl h) hi
      · exact plus_not_called frame x hxo i (Or.inr h) hi
    rcases hfort x hxT with ⟨hl, hsome⟩ | ⟨hl, hn, hp⟩
    · rcases hsome with hn | hp
      · exact Or.inl ⟨hl, Or.inl ⟨hn, inner _ (Or.inl rfl) hn⟩⟩
      · exact Or.inl ⟨hl, Or.inr ⟨hp, inner _ (Or.inr rfl) hp⟩⟩
    · exact Or.inr ⟨hl, ⟨hn, inner _ (Or.inl rfl) hn⟩, ⟨hp, inner _ (Or.inr rfl) hp⟩⟩
  have hfin : {y | y ∈ T ∧ frame.openRect (y + plusV frame)}.Finite :=
    ((FLatticePaper.FanTerminal.openRect_finite frame).image (fun y => y - plusV frame)).subset
      (fun x hx => ⟨x + plusV frame, hx.2, by simp⟩)
  have hempty := FLatticePaper.SheetFort.no_finite_fort_of_recurrent hrecV hT' hfin
  intro z hz ho
  have hmem : z ∈ {y | y ∈ T ∧ frame.openRect (y + plusV frame)} := ⟨hz, ho⟩
  rw [hempty] at hmem
  exact hmem

/-- **The plus core from recurrence.** A fort of the translated recurrent field whose candidates are `H_0` and `V_{−1}` is empty. -/
theorem plus_core_recurrent {M : Field} (frame : ChildFrame) (hrec : FLatticePaper.RecurrentField M)
    {T : Set Site} (hfort : IsIncomingFort (fun z => M (z + plusV frame)) T)
    (hsub : ∀ z ∈ T, z + plusV frame ∈ frame.closedPolygon)
    (hcand : ∀ z ∈ T, z + plusV frame ∈ frame.closedPolygon → ¬ frame.openRect (z + plusV frame) →
      z = ((1 : ℤ), (0 : ℤ)) ∨ z = ((1 : ℤ), (-1 : ℤ))) : T = ∅ := by
  have hint' := interior_empty_of_recurrent_plus frame hrec hfort hsub hcand
  have hcW : FortAt (fun z => z = ((1 : ℤ), (0 : ℤ)) ∨ z = ((1 : ℤ), (-1 : ℤ)))
      (fun z => M (z + plusV frame)) T := fortAt_of_incoming hfort
  have hVm1 : ((1 : ℤ), (-1 : ℤ)) ∈ T → False := by
    intro h
    have hev : EvenSite ((1 : ℤ), (-1 : ℤ)) := by unfold EvenSite; simp
    have hinN : incomingNeg ((1 : ℤ), (-1 : ℤ)) = ((0 : ℤ), (-1 : ℤ)) := by
      rw [incomingNeg_of_even _ hev]; simp
    have hinP : incomingPos ((1 : ℤ), (-1 : ℤ)) = ((2 : ℤ), (-1 : ℤ)) := by
      rw [incomingPos_of_even _ hev]; simp
    have h2 : ((2 : ℤ), (-1 : ℤ)) ∈ T :=
      fort_pos_of_neg_not_fortAt hcW (Or.inr rfl) h
        (by rw [hinN]; exact fun hm => plus_not_closed_zero_neg_one frame (hsub _ hm))
    exact hint' _ h2 (plus_open_two_neg_one frame)
  have hH0 : ((1 : ℤ), (0 : ℤ)) ∉ T := by
    intro h
    have hodd : ¬ EvenSite ((1 : ℤ), (0 : ℤ)) := by unfold EvenSite; simp
    have hinN : incomingNeg ((1 : ℤ), (0 : ℤ)) = ((1 : ℤ), (-1 : ℤ)) := by
      rw [incomingNeg_of_not_even _ hodd]; simp
    have hinP : incomingPos ((1 : ℤ), (0 : ℤ)) = ((1 : ℤ), (1 : ℤ)) := by
      rw [incomingPos_of_not_even _ hodd]; simp
    have hm1 : ((1 : ℤ), (-1 : ℤ)) ∈ T :=
      fort_neg_of_pos_not_fortAt hcW (Or.inl rfl) h
        (by rw [hinP]; exact fun hm => plus_not_closed_one_one frame (hsub _ hm))
    exact hVm1 hm1
  ext z
  constructor
  · intro hz
    rcases hcand z hz (hsub z hz) (hint' z hz) with rfl | rfl
    · exact absurd hz hH0
    · exact absurd hz (fun h => hVm1 h)
  · intro hz
    exact absurd hz (Set.notMem_empty z)

/-- **The plus core at the sheet minimum of a word.** -/
theorem plus_core_word {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) {T : Set Site}
    (hfort : IsIncomingFort (fun z => FLatticePaper.W1MSheet.MW word (z + plusV (frameAt word))) T)
    (hsub : ∀ z ∈ T, z + plusV (frameAt word) ∈ (frameAt word).closedPolygon)
    (hcand : ∀ z ∈ T, z + plusV (frameAt word) ∈ (frameAt word).closedPolygon →
      ¬ (frameAt word).openRect (z + plusV (frameAt word)) → z = ((1 : ℤ), (0 : ℤ)) ∨ z = ((1 : ℤ), (-1 : ℤ))) :
    T = ∅ :=
  plus_core_recurrent (frameAt word) (FLatticePaper.SheetFort.sheetMin_recurrentField hw hSE) hfort hsub hcand

end FLatticePaper.H0Core
