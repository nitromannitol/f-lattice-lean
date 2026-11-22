import FLatticePaper.Construction.ScheduleKinds
import FLatticePaper.Construction.RegisterFamily
import FLatticePaper.Tiles.StandardTiles

/-! # The constructor's ordinary standard tiles against the TeX standard tiles (task 42, part 1)

The ordinary standard schedule of a word (`ordinaryStandardSchedule`) places six donor tiles: the donors of the odd output
are `parents.even` four times and `parents.odd` twice, and the donors of the even output are `parents.even` twice and
`parents.odd` four times (`standardSources`). Its jets are the offsets `standardJets word parity`. The raw union of the
placed copies is the union of the six translated donors (`ordinaryStandard_raw_mem`). For words that are not base words, the
TeX standard tile is the union of six translates of the two parent tiles, `oddChildB` / `evenChildB`, with the offsets of
`eq:offsets_w1_odd/even`. The case lemmas compare the two unions, slot by slot.

The constructor's tile is the trimmed raw union, a translate of the raw union. -/

namespace FLatticePaper.Tiles.OrdinaryStandard

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard

/-- The sites of a placed donor: the donor's sites translated by the placement offset. -/
theorem placedBySlot_mem (jets : Fin 6 → TileJet) (donor : Fin 6 → NonemptyTile) (s : Fin 6) (v : Site) :
    v ∈ (placedBySlot jets donor s).val.sites ↔ v - (jets s).1 ∈ (donor s).val.sites :=
  HeightTile.mem_place_sites (donor s).val (jets s).1 (jets s).2 v

/-- Every slot of a standard schedule is the first copy or one of the five further copies. -/
theorem slot_cover (parity : Parity) (s : Fin 6) : s = 0 ∨ s ∈ afterFirstStandard parity := by
  cases parity <;> revert s <;> decide

/-- The raw union of the ordinary standard schedule is the union of the six placed donors. -/
theorem ordinaryStandard_raw_mem (parents : TileParents) (word : Word) (parity : Parity)
    (contacts : HeightTile.OrderedContacts (ordinaryStandardSchedule parents word parity).first.val.sites
      (ordinaryStandardSchedule parents word parity).copies) (v : Site) :
    v ∈ ((ordinaryStandardSchedule parents word parity).first.val.insertAll
        (ordinaryStandardSchedule parents word parity).copies contacts).sites ↔
      ∃ s : Fin 6, v - (standardJets word parity s).1 ∈ (standardSources parents parity s).val.sites := by
  rw [mem_insertAll]
  constructor
  · rintro (h | ⟨t, ht, hv⟩)
    · exact ⟨0, (placedBySlot_mem _ _ 0 v).mp h⟩
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ha
      exact ⟨s, (placedBySlot_mem _ _ s v).mp hv⟩
  · rintro ⟨s, hs⟩
    rcases slot_cover parity s with rfl | hsl
    · exact Or.inl ((placedBySlot_mem _ _ 0 v).mpr hs)
    · refine Or.inr ⟨(placedBySlot (standardJets word parity) (standardSources parents parity) s).val, ?_,
        (placedBySlot_mem _ _ s v).mpr hs⟩
      exact List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨s, hsl, rfl⟩, rfl⟩

/-- An existential over the six slots is the disjunction of the six cases. -/
theorem exists_fin_six (P : Fin 6 → Prop) :
    (∃ s, P s) ↔ P 0 ∨ P 1 ∨ P 2 ∨ P 3 ∨ P 4 ∨ P 5 := by
  constructor
  · rintro ⟨s, hs⟩
    fin_cases s
    · exact Or.inl hs
    · exact Or.inr (Or.inl hs)
    · exact Or.inr (Or.inr (Or.inl hs))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hs)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hs))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hs))))
  · rintro (h | h | h | h | h | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
    · exact ⟨4, h⟩
    · exact ⟨5, h⟩

/-- The odd standard schedule in phase `0`: its six slots are the TeX offsets of `oddChildB false`. -/
theorem odd_phase0_mem (parents : TileParents) (word : Word) (hph : phase word = 0) (T1 T2 : Tile)
    (h1 : parents.odd.val.sites = T1) (h2 : parents.even.val.sites = T2) (v : Site) :
    (∃ s : Fin 6, v - (standardJets word .odd s).1 ∈ (standardSources parents .odd s).val.sites) ↔
      v ∈ oddChildB false T1 T2 (parentsAt word).odd (parentsAt word).even := by
  subst h1 h2
  rw [exists_fin_six]
  have hj0 : (standardJets word .odd 0).1 = 0 := by
    simp [standardJets, hph, doubleFirst]
  have hj1 : (standardJets word .odd 1).1 = texV1Even (parentsAt word).even := by
    simp [standardJets, hph, doubleFirst, kernelJet, texV1Even]
  have hj2 : (standardJets word .odd 2).1 = texV1Odd (parentsAt word).odd + texV2 (parentsAt word).odd := by
    simp [standardJets, hph, doubleFirst, kernelJet, transverseJet, texV1Odd, texV2]
  have hj3 : (standardJets word .odd 3).1 =
      texV1Odd (parentsAt word).odd + texV2 (parentsAt word).odd + texV1Even (parentsAt word).even := by
    simp [standardJets, hph, doubleFirst, kernelJet, transverseJet, texV1Odd, texV1Even, texV2]
  have hj4 : (standardJets word .odd 4).1 = texV1Even (parentsAt word).even + texV1Even (parentsAt word).even := by
    simp [standardJets, hph, doubleFirst, kernelJet, texV1Even, two_mul]
  have hj5 : (standardJets word .odd 5).1 = texV2 (parentsAt word).even := by
    simp [standardJets, hph, doubleFirst, transverseJet, texV2]
  rw [hj0, hj1, hj2, hj3, hj4, hj5]
  simp only [standardSources, oddChildB, Finset.mem_union, mem_shift, sub_zero]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, or_assoc]

/-- The phase is `0` or `1`. -/
theorem phase_zero_or_one (word : Word) : phase word = 0 ∨ phase word = 1 := by
  have : phase word < 2 := Nat.mod_lt _ (by norm_num)
  omega

/-- The odd standard schedule in phase `1`. -/
theorem odd_phase1_mem (parents : TileParents) (word : Word) (hph : phase word = 1) (T1 T2 : Tile)
    (h1 : parents.odd.val.sites = T1) (h2 : parents.even.val.sites = T2) (v : Site) :
    (∃ s : Fin 6, v - (standardJets word .odd s).1 ∈ (standardSources parents .odd s).val.sites) ↔
      v ∈ oddChildB true T1 T2 (parentsAt word).odd (parentsAt word).even := by
  subst h1 h2
  rw [exists_fin_six]
  have hne : phase word ≠ 0 := by omega
  have hj0 : (standardJets word .odd 0).1 = texV1Odd (parentsAt word).odd := by
    simp [standardJets, hne, doubleFirst, kernelJet, texV1Odd]
  have hj1 : (standardJets word .odd 1).1 = texV1Odd (parentsAt word).odd + texV1Even (parentsAt word).even := by
    simp [standardJets, hne, doubleFirst, kernelJet, texV1Odd, texV1Even]
  have hj2 : (standardJets word .odd 2).1 = texV2 (parentsAt word).odd := by
    simp [standardJets, hne, doubleFirst, transverseJet, texV2]
  have hj3 : (standardJets word .odd 3).1 = texV2 (parentsAt word).odd + texV1Even (parentsAt word).even := by
    simp [standardJets, hne, doubleFirst, kernelJet, transverseJet, texV1Even, texV2]
  have hj4 : (standardJets word .odd 4).1 = 0 := by
    simp [standardJets, hne, doubleFirst]
  have hj5 : (standardJets word .odd 5).1 =
      texV1Even (parentsAt word).even + texV1Even (parentsAt word).even + texV2 (parentsAt word).even := by
    simp [standardJets, hne, doubleFirst, kernelJet, transverseJet, texV1Even, texV2, two_mul]
  rw [hj0, hj1, hj2, hj3, hj4, hj5]
  simp only [standardSources, oddChildB, Finset.mem_union, mem_shift, sub_zero]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, or_assoc]

/-- The even standard schedule in phase `0`. -/
theorem even_phase0_mem (parents : TileParents) (word : Word) (hph : phase word = 0) (T1 T2 : Tile)
    (h1 : parents.odd.val.sites = T1) (h2 : parents.even.val.sites = T2) (v : Site) :
    (∃ s : Fin 6, v - (standardJets word .even s).1 ∈ (standardSources parents .even s).val.sites) ↔
      v ∈ evenChildB false T1 T2 (parentsAt word).odd (parentsAt word).even := by
  subst h1 h2
  rw [exists_fin_six]
  have hj0 : (standardJets word .even 0).1 = 0 := by
    simp [standardJets, hph, doubleLast]
  have hj1 : (standardJets word .even 1).1 =
      texV1Odd (parentsAt word).odd + (texV2 (parentsAt word).odd + texV2 (parentsAt word).odd) := by
    simp [standardJets, hph, doubleLast, kernelJet, transverseJet, texV1Odd, texV2, two_mul, add_assoc]
  have hj2 : (standardJets word .even 2).1 = texV1Even (parentsAt word).even := by
    simp [standardJets, hph, doubleLast, kernelJet, texV1Even]
  have hj3 : (standardJets word .even 3).1 = texV1Even (parentsAt word).even + texV2 (parentsAt word).odd := by
    simp [standardJets, hph, doubleLast, kernelJet, transverseJet, texV1Even, texV2]
  have hj4 : (standardJets word .even 4).1 = texV2 (parentsAt word).even := by
    simp [standardJets, hph, doubleLast, transverseJet, texV2]
  have hj5 : (standardJets word .even 5).1 = texV2 (parentsAt word).even + texV2 (parentsAt word).odd := by
    simp [standardJets, hph, doubleLast, transverseJet, texV2]
  rw [hj0, hj1, hj2, hj3, hj4, hj5]
  simp only [standardSources, evenChildB, Finset.mem_union, mem_shift, sub_zero]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, or_assoc]

/-- The even standard schedule in phase `1`. -/
theorem even_phase1_mem (parents : TileParents) (word : Word) (hph : phase word = 1) (T1 T2 : Tile)
    (h1 : parents.odd.val.sites = T1) (h2 : parents.even.val.sites = T2) (v : Site) :
    (∃ s : Fin 6, v - (standardJets word .even s).1 ∈ (standardSources parents .even s).val.sites) ↔
      v ∈ evenChildB true T1 T2 (parentsAt word).odd (parentsAt word).even := by
  subst h1 h2
  rw [exists_fin_six]
  have hne : phase word ≠ 0 := by omega
  have hj0 : (standardJets word .even 0).1 = texV1Odd (parentsAt word).odd := by
    simp [standardJets, hne, doubleLast, kernelJet, texV1Odd]
  have hj1 : (standardJets word .even 1).1 = texV2 (parentsAt word).odd + texV2 (parentsAt word).odd := by
    simp [standardJets, hne, doubleLast, transverseJet, texV2, two_mul]
  have hj2 : (standardJets word .even 2).1 = 0 := by
    simp [standardJets, hne, doubleLast]
  have hj3 : (standardJets word .even 3).1 = texV2 (parentsAt word).odd := by
    simp [standardJets, hne, doubleLast, transverseJet, texV2]
  have hj4 : (standardJets word .even 4).1 = texV1Even (parentsAt word).even + texV2 (parentsAt word).even := by
    simp [standardJets, hne, doubleLast, kernelJet, transverseJet, texV1Even, texV2, add_comm]
  have hj5 : (standardJets word .even 5).1 =
      texV1Even (parentsAt word).even + texV2 (parentsAt word).even + texV2 (parentsAt word).odd := by
    simp [standardJets, hne, doubleLast, kernelJet, transverseJet, texV1Even, texV2, add_comm, add_assoc]
  rw [hj0, hj1, hj2, hj3, hj4, hj5]
  simp only [standardSources, evenChildB, Finset.mem_union, mem_shift, sub_zero]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, or_assoc]

/-- The raw union of the odd ordinary schedule is the TeX child union `oddChildB`, for every phase. -/
theorem raw_odd_eq_child (parents : TileParents) (word : Word) (T1 T2 : Tile)
    (h1 : parents.odd.val.sites = T1) (h2 : parents.even.val.sites = T2)
    (contacts : HeightTile.OrderedContacts (ordinaryStandardSchedule parents word .odd).first.val.sites
      (ordinaryStandardSchedule parents word .odd).copies) :
    ((ordinaryStandardSchedule parents word .odd).first.val.insertAll
        (ordinaryStandardSchedule parents word .odd).copies contacts).sites =
      oddChildB (phase word == 1) T1 T2 (parentsAt word).odd (parentsAt word).even := by
  ext v
  rw [ordinaryStandard_raw_mem]
  rcases phase_zero_or_one word with h | h
  · have hb : (phase word == 1) = false := by simp [h]
    rw [hb]
    exact odd_phase0_mem parents word h T1 T2 h1 h2 v
  · have hb : (phase word == 1) = true := by simp [h]
    rw [hb]
    exact odd_phase1_mem parents word h T1 T2 h1 h2 v

/-- The raw union of the even ordinary schedule is the TeX child union `evenChildB`, for every phase. -/
theorem raw_even_eq_child (parents : TileParents) (word : Word) (T1 T2 : Tile)
    (h1 : parents.odd.val.sites = T1) (h2 : parents.even.val.sites = T2)
    (contacts : HeightTile.OrderedContacts (ordinaryStandardSchedule parents word .even).first.val.sites
      (ordinaryStandardSchedule parents word .even).copies) :
    ((ordinaryStandardSchedule parents word .even).first.val.insertAll
        (ordinaryStandardSchedule parents word .even).copies contacts).sites =
      evenChildB (phase word == 1) T1 T2 (parentsAt word).odd (parentsAt word).even := by
  ext v
  rw [ordinaryStandard_raw_mem]
  rcases phase_zero_or_one word with h | h
  · have hb : (phase word == 1) = false := by simp [h]
    rw [hb]
    exact even_phase0_mem parents word h T1 T2 h1 h2 v
  · have hb : (phase word == 1) = true := by simp [h]
    rw [hb]
    exact even_phase1_mem parents word h T1 T2 h1 h2 v

/-- The TeX odd standard tile of a non-base word is the odd child union of its state. -/
theorem oddTile_eq_child {word : Word} (hw : ¬ IsBase word) :
    oddTile word = oddChildB (phase word == 1) (stateAt word).tOdd (stateAt word).tEven
      (parentsAt word).odd (parentsAt word).even := by
  have hnil : word ≠ [] := fun h => hw (Or.inl h)
  have hthree : word ≠ List.replicate word.length Digit.three := fun h =>
    hw (Or.inr (Or.inl (fun d hd => (List.eq_replicate_iff.mp h).2 d hd)))
  have htwo : word ≠ List.replicate word.length Digit.two := fun h =>
    hw (Or.inr (Or.inr (fun d hd => (List.eq_replicate_iff.mp h).2 d hd)))
  unfold oddTile childTiles
  rw [if_neg hnil, if_neg hthree, if_neg htwo, stateAt_par]

/-- The TeX even standard tile of a non-base word is the even child union of its state. -/
theorem evenTile_eq_child {word : Word} (hw : ¬ IsBase word) :
    evenTile word = evenChildB (phase word == 1) (stateAt word).tOdd (stateAt word).tEven
      (parentsAt word).odd (parentsAt word).even := by
  have hnil : word ≠ [] := fun h => hw (Or.inl h)
  have hthree : word ≠ List.replicate word.length Digit.three := fun h =>
    hw (Or.inr (Or.inl (fun d hd => (List.eq_replicate_iff.mp h).2 d hd)))
  have htwo : word ≠ List.replicate word.length Digit.two := fun h =>
    hw (Or.inr (Or.inr (fun d hd => (List.eq_replicate_iff.mp h).2 d hd)))
  unfold evenTile childTiles
  rw [if_neg hnil, if_neg hthree, if_neg htwo, stateAt_par]

/-- Two site sets are equal up to a translation. -/
def TransEq (A B : Finset Site) : Prop := ∃ c : Site, A = B.image (· + c)

/-- The trimmed raw union is a translate of the raw union. -/
theorem finish_tile_transEq (schedule : PlacedSchedule)
    (contacts : HeightTile.OrderedContacts schedule.first.val.sites schedule.copies) :
    TransEq (schedule.finish .tile contacts).val.sites (schedule.raw contacts).val.sites := by
  refine ⟨-((schedule.raw contacts).val.boxOrigin (schedule.raw contacts).property), ?_⟩
  simp only [PlacedSchedule.finish, NonemptyTile.trim]
  unfold HeightTile.trim HeightTile.place
  dsimp only
  rw [Finset.map_eq_image]
  rfl

/-- The constructor's ordinary odd standard tile of a non-base word is a translate of the TeX odd standard tile, when
its donors are the TeX registers of the word. -/
theorem ordinaryStandardTile_odd_transEq (parents : TileParents) (word : Word) (hw : ¬ IsBase word)
    (hT1 : parents.odd.val.sites = (stateAt word).tOdd) (hT2 : parents.even.val.sites = (stateAt word).tEven)
    (t : NonemptyTile) (ht : ordinaryStandardTile parents word .odd = .ok t) :
    TransEq t.val.sites (oddTile word) := by
  unfold ordinaryStandardTile at ht
  obtain ⟨contacts, hfin⟩ := (PlacedSchedule.eval_ok_iff _ _ _ t).mp ht
  have hraw : ((ordinaryStandardSchedule parents word .odd).raw contacts).val.sites = oddTile word := by
    show ((ordinaryStandardSchedule parents word .odd).first.val.insertAll
      (ordinaryStandardSchedule parents word .odd).copies contacts).sites = oddTile word
    rw [raw_odd_eq_child parents word _ _ hT1 hT2 contacts, oddTile_eq_child hw]
  obtain ⟨c, hc⟩ := finish_tile_transEq (ordinaryStandardSchedule parents word .odd) contacts
  refine ⟨c, ?_⟩
  rw [← hfin, hc, hraw]

/-- The constructor's ordinary even standard tile of a non-base word is a translate of the TeX even standard tile. -/
theorem ordinaryStandardTile_even_transEq (parents : TileParents) (word : Word) (hw : ¬ IsBase word)
    (hT1 : parents.odd.val.sites = (stateAt word).tOdd) (hT2 : parents.even.val.sites = (stateAt word).tEven)
    (t : NonemptyTile) (ht : ordinaryStandardTile parents word .even = .ok t) :
    TransEq t.val.sites (evenTile word) := by
  unfold ordinaryStandardTile at ht
  obtain ⟨contacts, hfin⟩ := (PlacedSchedule.eval_ok_iff _ _ _ t).mp ht
  have hraw : ((ordinaryStandardSchedule parents word .even).raw contacts).val.sites = evenTile word := by
    show ((ordinaryStandardSchedule parents word .even).first.val.insertAll
      (ordinaryStandardSchedule parents word .even).copies contacts).sites = evenTile word
    rw [raw_even_eq_child parents word _ _ hT1 hT2 contacts, evenTile_eq_child hw]
  obtain ⟨c, hc⟩ := finish_tile_transEq (ordinaryStandardSchedule parents word .even) contacts
  refine ⟨c, ?_⟩
  rw [← hfin, hc, hraw]

end FLatticePaper.Tiles.OrdinaryStandard
