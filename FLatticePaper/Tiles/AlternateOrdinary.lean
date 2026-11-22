import FLatticePaper.Construction.NativeSchedules
import FLatticePaper.Construction.RegisterFamily
import FLatticePaper.Tiles.AlternateTiles
import FLatticePaper.Tiles.OrdinaryStandard

/-! # The ordinary alternate schedules are the literal alternate pieces, with the head restoration (task 45, step 1)

An ordinary alternate schedule (`ordinaryAlternateSchedule`, for the odd output after digits `1` and `3`, and the even
output after digits `1` and `2`) places six standard donors at the jets `alternateJets`, and one alternate piece: the
alternate retained tile of the other parity, restored by `alternateRestoration` and placed at `seventhAlternateJet`.

The literal alternate tile `altPair` (AlternateTiles.lean, PROVISIONAL reading) places the same six standard donors at the
same offsets, and its alternate piece at the literal offset. The only difference is the head restoration: the alternate
piece is placed at its literal offset plus `alternateRestoration`. This file proves the odd and even membership statements
against `altPair` with the restored alternate inputs `shift aO (alternateRestoration word .odd)` and
`shift aE (alternateRestoration word .even)`.

Statements of the form `v ∈ (ordinary schedule).raw ↔ v ∈ (altPair ...).1` are the content; the restored inputs are the
alternate retained tiles shifted by the restoration (`restoreAlternate_sites`). -/

namespace FLatticePaper.Tiles.AlternateOrdinary

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
open FLatticePaper.Tiles.Alternate FLatticePaper.Tiles.OrdinaryStandard

/-- The alternate piece of an ordinary schedule: the alternate retained tile of the other parity, restored. -/
def oldAlternate (parents : TileParents) (word : Word) (parity : Parity) : NonemptyTile :=
  match parity with
  | .odd => restoreAlternate word .even parents.alternateEven
  | .even => restoreAlternate word .odd parents.alternateOdd

/-- The restored alternate tile is the alternate tile shifted by the restoration. -/
theorem restoreAlternate_sites (word : Word) (parity : Parity) (tile : NonemptyTile) (v : Site) :
    v ∈ (restoreAlternate word parity tile).val.sites ↔ v ∈ shift tile.val.sites (alternateRestoration word parity) := by
  rw [mem_shift]
  unfold restoreAlternate NonemptyTile.place
  exact HeightTile.mem_place_sites tile.val (alternateRestoration word parity) 0 v

/-- The six slots of an ordinary alternate schedule: slot `0` is the first copy, the others are the further copies. -/
theorem alt_slot_cover (parity : Parity) (s : Fin 6) : s = 0 ∨ s ∈ afterSeventhAlternate parity := by
  cases parity <;> revert s <;> decide

/-- The raw union of an ordinary alternate schedule: the six placed standard donors and the restored alternate piece. -/
theorem ordinaryAlternate_raw_mem (parents : TileParents) (beforePush : Word) (digit : Digit) (parity : Parity)
    (contacts : HeightTile.OrderedContacts (ordinaryAlternateSchedule parents beforePush digit parity).first.val.sites
      (ordinaryAlternateSchedule parents beforePush digit parity).copies) (v : Site) :
    v ∈ ((ordinaryAlternateSchedule parents beforePush digit parity).first.val.insertAll
        (ordinaryAlternateSchedule parents beforePush digit parity).copies contacts).sites ↔
      (∃ s : Fin 6, v - (alternateJets (beforePush ++ [digit]) parity s).1 ∈
          (standardSources parents parity.flip s).val.sites) ∨
        v - (seventhAlternateJet beforePush digit parity).1 ∈
          (oldAlternate parents (beforePush ++ [digit]) parity).val.sites := by
  rw [mem_insertAll]
  constructor
  · rintro (h | ⟨t, ht, hv⟩)
    · exact Or.inl ⟨0, (placedBySlot_mem _ _ 0 v).mp h⟩
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact Or.inr ((HeightTile.mem_place_sites _ _ _ v).mp hv)
      · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ha'
        exact Or.inl ⟨s, (placedBySlot_mem _ _ s v).mp hv⟩
  · rintro (⟨s, hs⟩ | hs)
    · rcases alt_slot_cover parity s with rfl | hsl
      · exact Or.inl ((placedBySlot_mem _ _ 0 v).mpr hs)
      · refine Or.inr ⟨(placedBySlot (alternateJets (beforePush ++ [digit]) parity)
            (standardSources parents parity.flip) s).val, ?_, (placedBySlot_mem _ _ s v).mpr hs⟩
        exact List.mem_map.mpr ⟨_, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨s, hsl, rfl⟩), rfl⟩
    · refine Or.inr ⟨((seventhAlternateJet beforePush digit parity).place
          (oldAlternate parents (beforePush ++ [digit]) parity)).val, ?_,
        (HeightTile.mem_place_sites _ _ _ v).mpr hs⟩
      exact List.mem_map.mpr ⟨_, List.mem_cons_self, rfl⟩

/-- The phase is `0` or `1`. -/
theorem phase_zero_or_one' (word : Word) : phase word = 0 ∨ phase word = 1 := by
  have : phase word < 2 := Nat.mod_lt _ (by norm_num)
  omega

/-- The odd ordinary alternate schedule in phase `0` is the literal odd alternate child (flag `false`), with the restored
alternate piece. -/
theorem ordinaryAlternate_odd_phase0 (parents : TileParents) (beforePush : Word) (digit : Digit)
    (hd : digit = Digit.one ∨ digit = Digit.three) (hph : phase (beforePush ++ [digit]) = 0) (v : Site) :
    ((∃ s : Fin 6, v - (alternateJets (beforePush ++ [digit]) .odd s).1 ∈
          (standardSources parents .even s).val.sites) ∨
        v - (seventhAlternateJet beforePush digit .odd).1 ∈
          (oldAlternate parents (beforePush ++ [digit]) .odd).val.sites) ↔
      v ∈ (altPair (phase (beforePush ++ [digit]) == 1) digit parents.odd.val.sites parents.even.val.sites
        (shift parents.alternateOdd.val.sites (alternateRestoration (beforePush ++ [digit]) .odd))
        (shift parents.alternateEven.val.sites (alternateRestoration (beforePush ++ [digit]) .even))
        (parentsAt (beforePush ++ [digit])).odd (parentsAt (beforePush ++ [digit])).even).1 := by
  have hflag : (phase (beforePush ++ [digit]) == 1) = false := by simp [hph]
  have hj0 : (alternateJets (beforePush ++ [digit]) .odd 0).1 = 0 := by
    simp [alternateJets, hph, doubleLast]
  have hj1 : (alternateJets (beforePush ++ [digit]) .odd 1).1 =
      texV1Odd (parentsAt (beforePush ++ [digit])).odd + (2 • texV2 (parentsAt (beforePush ++ [digit])).odd)
        + texV1Even (parentsAt (beforePush ++ [digit])).even := by
    ext <;> simp [alternateJets, hph, doubleLast, kernelJet, transverseJet, texV1Odd, texV1Even, texV2]
  have hj2 : (alternateJets (beforePush ++ [digit]) .odd 2).1 =
      texV1Even (parentsAt (beforePush ++ [digit])).even := by
    ext <;> simp [alternateJets, hph, doubleLast, kernelJet, texV1Even]
  have hj3 : (alternateJets (beforePush ++ [digit]) .odd 3).1 =
      texV1Even (parentsAt (beforePush ++ [digit])).even +
        (texV1Even (parentsAt (beforePush ++ [digit])).even + texV2 (parentsAt (beforePush ++ [digit])).odd) := by
    ext <;> simp [alternateJets, hph, doubleLast, kernelJet, transverseJet, texV1Even, texV2]
  have hj4 : (alternateJets (beforePush ++ [digit]) .odd 4).1 =
      texV2 (parentsAt (beforePush ++ [digit])).even := by
    ext <;> simp [alternateJets, hph, doubleLast, transverseJet, texV2]
  have hj5 : (alternateJets (beforePush ++ [digit]) .odd 5).1 =
      texV2 (parentsAt (beforePush ++ [digit])).even +
        (texV1Even (parentsAt (beforePush ++ [digit])).even + texV2 (parentsAt (beforePush ++ [digit])).odd) := by
    ext <;> simp [alternateJets, hph, doubleLast, kernelJet, transverseJet, texV1Even, texV2]
  have hseven : (seventhAlternateJet beforePush digit .odd).1 =
      texV1Even (parentsAt (beforePush ++ [digit])).even + texV2 (parentsAt (beforePush ++ [digit])).odd := by
    rcases hd with rfl | rfl <;> ext <;> simp [seventhAlternateJet, hph, kernelJet, transverseJet, texV1Even, texV2]
  rw [exists_fin_six, hj0, hj1, hj2, hj3, hj4, hj5, hseven]
  simp only [oldAlternate, restoreAlternate_sites, altPair, hflag, standardSources, Bool.false_eq_true, if_false]
  simp [hd, Finset.mem_union, mem_shift, or_assoc, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four]

/-- The odd ordinary alternate schedule in phase `1` is the literal odd alternate child (flag `true`), with the restored
alternate piece. -/
theorem ordinaryAlternate_odd_phase1 (parents : TileParents) (beforePush : Word) (digit : Digit)
    (hd : digit = Digit.one ∨ digit = Digit.three) (hph : phase (beforePush ++ [digit]) = 1) (v : Site) :
    ((∃ s : Fin 6, v - (alternateJets (beforePush ++ [digit]) .odd s).1 ∈
          (standardSources parents .even s).val.sites) ∨
        v - (seventhAlternateJet beforePush digit .odd).1 ∈
          (oldAlternate parents (beforePush ++ [digit]) .odd).val.sites) ↔
      v ∈ (altPair (phase (beforePush ++ [digit]) == 1) digit parents.odd.val.sites parents.even.val.sites
        (shift parents.alternateOdd.val.sites (alternateRestoration (beforePush ++ [digit]) .odd))
        (shift parents.alternateEven.val.sites (alternateRestoration (beforePush ++ [digit]) .even))
        (parentsAt (beforePush ++ [digit])).odd (parentsAt (beforePush ++ [digit])).even).1 := by
  have hflag : (phase (beforePush ++ [digit]) == 1) = true := by simp [hph]
  have hne : phase (beforePush ++ [digit]) ≠ 0 := by omega
  have hj0 : (alternateJets (beforePush ++ [digit]) .odd 0).1 =
      texV1Odd (parentsAt (beforePush ++ [digit])).odd := by
    ext <;> simp [alternateJets, hne, doubleLast, kernelJet, texV1Odd]
  have hj1 : (alternateJets (beforePush ++ [digit]) .odd 1).1 =
      2 • texV2 (parentsAt (beforePush ++ [digit])).odd - texV1Even (parentsAt (beforePush ++ [digit])).even := by
    ext <;> simp [alternateJets, hne, doubleLast, kernelJet, transverseJet, texV1Even, texV2]
  have hj2 : (alternateJets (beforePush ++ [digit]) .odd 2).1 = 0 := by
    simp [alternateJets, hne, doubleLast]
  have hj3 : (alternateJets (beforePush ++ [digit]) .odd 3).1 =
      0 + (-texV1Even (parentsAt (beforePush ++ [digit])).even + texV2 (parentsAt (beforePush ++ [digit])).odd) := by
    ext <;> simp [alternateJets, hne, doubleLast, kernelJet, transverseJet, texV1Even, texV2]
  have hj4 : (alternateJets (beforePush ++ [digit]) .odd 4).1 =
      texV1Even (parentsAt (beforePush ++ [digit])).even + texV2 (parentsAt (beforePush ++ [digit])).even := by
    ext <;> simp [alternateJets, hne, doubleLast, kernelJet, transverseJet, texV1Even, texV2]
  have hj5 : (alternateJets (beforePush ++ [digit]) .odd 5).1 =
      (texV1Even (parentsAt (beforePush ++ [digit])).even + texV2 (parentsAt (beforePush ++ [digit])).even) +
        (-texV1Even (parentsAt (beforePush ++ [digit])).even + texV2 (parentsAt (beforePush ++ [digit])).odd) := by
    ext <;> simp [alternateJets, hne, doubleLast, kernelJet, transverseJet, texV1Even, texV2]
  have hseven : (seventhAlternateJet beforePush digit .odd).1 =
      texV2 (parentsAt (beforePush ++ [digit])).odd + texV1Odd (parentsAt (beforePush ++ [digit])).odd
        - texV1Even (parentsAt (beforePush ++ [digit])).even := by
    rcases hd with rfl | rfl <;> ext <;> simp [seventhAlternateJet, hne, kernelJet, transverseJet, texV1Odd, texV1Even, texV2]
  rw [exists_fin_six, hj0, hj1, hj2, hj3, hj4, hj5, hseven]
  simp only [oldAlternate, restoreAlternate_sites, altPair, hflag, standardSources, if_true]
  simp [hd, Finset.mem_union, mem_shift, or_assoc, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four]

/-- The even ordinary alternate schedule in phase `0` (digits `1` and `2`) is the literal even alternate child (flag
`false`), with the restored alternate piece. -/
theorem ordinaryAlternate_even_phase0 (parents : TileParents) (beforePush : Word) (digit : Digit)
    (hd : digit = Digit.one ∨ digit = Digit.two) (hph : phase (beforePush ++ [digit]) = 0) (v : Site) :
    ((∃ s : Fin 6, v - (alternateJets (beforePush ++ [digit]) .even s).1 ∈
          (standardSources parents .odd s).val.sites) ∨
        v - (seventhAlternateJet beforePush digit .even).1 ∈
          (oldAlternate parents (beforePush ++ [digit]) .even).val.sites) ↔
      v ∈ (altPair (phase (beforePush ++ [digit]) == 1) digit parents.odd.val.sites parents.even.val.sites
        (shift parents.alternateOdd.val.sites (alternateRestoration (beforePush ++ [digit]) .odd))
        (shift parents.alternateEven.val.sites (alternateRestoration (beforePush ++ [digit]) .even))
        (parentsAt (beforePush ++ [digit])).odd (parentsAt (beforePush ++ [digit])).even).2 := by
  have hflag : (phase (beforePush ++ [digit]) == 1) = false := by simp [hph]
  have hj0 : (alternateJets (beforePush ++ [digit]) .even 0).1 = 0 := by
    simp [alternateJets, hph, doubleFirst]
  have hj1 : (alternateJets (beforePush ++ [digit]) .even 1).1 =
      0 + (-texV1Even (parentsAt (beforePush ++ [digit])).even + texV2 (parentsAt (beforePush ++ [digit])).odd) := by
    ext <;> simp [alternateJets, hph, doubleFirst, kernelJet, transverseJet, texV1Even, texV2]
  have hj2 : (alternateJets (beforePush ++ [digit]) .even 2).1 =
      texV1Odd (parentsAt (beforePush ++ [digit])).odd + texV2 (parentsAt (beforePush ++ [digit])).odd := by
    ext <;> simp [alternateJets, hph, doubleFirst, kernelJet, transverseJet, texV1Odd, texV2]
  have hj3 : (alternateJets (beforePush ++ [digit]) .even 3).1 =
      texV1Odd (parentsAt (beforePush ++ [digit])).odd + texV2 (parentsAt (beforePush ++ [digit])).odd +
        (-texV1Even (parentsAt (beforePush ++ [digit])).even + texV2 (parentsAt (beforePush ++ [digit])).odd) := by
    ext <;> simp [alternateJets, hph, doubleFirst, kernelJet, transverseJet, texV1Odd, texV1Even, texV2]
  have hj4 : (alternateJets (beforePush ++ [digit]) .even 4).1 =
      texV1Even (parentsAt (beforePush ++ [digit])).even := by
    ext <;> simp [alternateJets, hph, doubleFirst, kernelJet, texV1Even]
  have hj5 : (alternateJets (beforePush ++ [digit]) .even 5).1 =
      texV2 (parentsAt (beforePush ++ [digit])).odd + texV2 (parentsAt (beforePush ++ [digit])).even
        - texV1Even (parentsAt (beforePush ++ [digit])).even := by
    ext <;> simp [alternateJets, hph, doubleFirst, kernelJet, transverseJet, texV1Even, texV2] <;> ring
  rw [exists_fin_six, hj0, hj1, hj2, hj3, hj4, hj5]
  rcases hd with rfl | rfl
  · have hseven : (seventhAlternateJet beforePush Digit.one .even).1 =
        texV2 (parentsAt (beforePush ++ [Digit.one])).odd + texV1Odd (parentsAt (beforePush ++ [Digit.one])).odd
          - texV1Even (parentsAt (beforePush ++ [Digit.one])).even := by
      ext <;> simp [seventhAlternateJet, hph, kernelJet, transverseJet, texV1Odd, texV1Even, texV2] <;> ring
    rw [hseven]
    simp only [oldAlternate, restoreAlternate_sites, altPair, hflag, standardSources, Bool.false_eq_true, if_false]
    simp [Finset.mem_union, mem_shift, or_assoc, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]
  · have hseven : (seventhAlternateJet beforePush Digit.two .even).1 =
        texV2 (parentsAt (beforePush ++ [Digit.two])).even := by
      ext <;> simp [seventhAlternateJet, hph, transverseJet, texV2]
    rw [hseven]
    simp only [oldAlternate, restoreAlternate_sites, altPair, hflag, standardSources, Bool.false_eq_true, if_false]
    simp [Finset.mem_union, mem_shift, or_assoc, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]

/-- The even ordinary alternate schedule in phase `1` (digits `1` and `2`) is the literal even alternate child (flag
`true`), with the restored alternate piece. -/
theorem ordinaryAlternate_even_phase1 (parents : TileParents) (beforePush : Word) (digit : Digit)
    (hd : digit = Digit.one ∨ digit = Digit.two) (hph : phase (beforePush ++ [digit]) = 1) (v : Site) :
    ((∃ s : Fin 6, v - (alternateJets (beforePush ++ [digit]) .even s).1 ∈
          (standardSources parents .odd s).val.sites) ∨
        v - (seventhAlternateJet beforePush digit .even).1 ∈
          (oldAlternate parents (beforePush ++ [digit]) .even).val.sites) ↔
      v ∈ (altPair (phase (beforePush ++ [digit]) == 1) digit parents.odd.val.sites parents.even.val.sites
        (shift parents.alternateOdd.val.sites (alternateRestoration (beforePush ++ [digit]) .odd))
        (shift parents.alternateEven.val.sites (alternateRestoration (beforePush ++ [digit]) .even))
        (parentsAt (beforePush ++ [digit])).odd (parentsAt (beforePush ++ [digit])).even).2 := by
  have hflag : (phase (beforePush ++ [digit]) == 1) = true := by simp [hph]
  have hne : phase (beforePush ++ [digit]) ≠ 0 := by omega
  have hj0 : (alternateJets (beforePush ++ [digit]) .even 0).1 =
      texV1Odd (parentsAt (beforePush ++ [digit])).odd := by
    ext <;> simp [alternateJets, hne, doubleFirst, kernelJet, texV1Odd]
  have hj1 : (alternateJets (beforePush ++ [digit]) .even 1).1 =
      texV1Odd (parentsAt (beforePush ++ [digit])).odd +
        (texV1Even (parentsAt (beforePush ++ [digit])).even + texV2 (parentsAt (beforePush ++ [digit])).odd) := by
    ext <;> simp [alternateJets, hne, doubleFirst, kernelJet, transverseJet, texV1Odd, texV1Even, texV2]
  have hj2 : (alternateJets (beforePush ++ [digit]) .even 2).1 =
      texV2 (parentsAt (beforePush ++ [digit])).odd := by
    ext <;> simp [alternateJets, hne, doubleFirst, transverseJet, texV2]
  have hj3 : (alternateJets (beforePush ++ [digit]) .even 3).1 =
      texV2 (parentsAt (beforePush ++ [digit])).odd +
        (texV1Even (parentsAt (beforePush ++ [digit])).even + texV2 (parentsAt (beforePush ++ [digit])).odd) := by
    ext <;> simp [alternateJets, hne, doubleFirst, kernelJet, transverseJet, texV1Even, texV2]
  have hj4 : (alternateJets (beforePush ++ [digit]) .even 4).1 = 0 := by
    simp [alternateJets, hne, doubleFirst]
  have hj5 : (alternateJets (beforePush ++ [digit]) .even 5).1 =
      texV2 (parentsAt (beforePush ++ [digit])).odd + texV2 (parentsAt (beforePush ++ [digit])).even +
        2 • texV1Even (parentsAt (beforePush ++ [digit])).even := by
    ext <;> simp [alternateJets, hne, doubleFirst, kernelJet, transverseJet, texV1Even, texV2]
  rw [exists_fin_six, hj0, hj1, hj2, hj3, hj4, hj5]
  rcases hd with rfl | rfl
  · have hseven : (seventhAlternateJet beforePush Digit.one .even).1 =
        texV2 (parentsAt (beforePush ++ [Digit.one])).odd + texV1Even (parentsAt (beforePush ++ [Digit.one])).even := by
      ext <;> simp [seventhAlternateJet, hne, kernelJet, transverseJet, texV1Even, texV2] <;> ring
    rw [hseven]
    simp only [oldAlternate, restoreAlternate_sites, altPair, hflag, standardSources, if_true]
    simp [Finset.mem_union, mem_shift, or_assoc, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]
  · have hseven : (seventhAlternateJet beforePush Digit.two .even).1 =
        2 • texV1Even (parentsAt (beforePush ++ [Digit.two])).even + texV2 (parentsAt (beforePush ++ [Digit.two])).even := by
      ext <;> simp [seventhAlternateJet, hne, kernelJet, transverseJet, texV1Even, texV2]
    rw [hseven]
    simp only [oldAlternate, restoreAlternate_sites, altPair, hflag, standardSources, if_true]
    simp [Finset.mem_union, mem_shift, or_assoc, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]

/-- **Structural lemma, odd output.** The ordinary alternate schedule of the odd output after digit `1` or `3` has the sites
of the literal odd alternate child `altPair`, with the alternate piece restored by `alternateRestoration`. -/
theorem ordinaryAlternate_odd_structure (parents : TileParents) (beforePush : Word) (digit : Digit)
    (hd : digit = Digit.one ∨ digit = Digit.three)
    (contacts : HeightTile.OrderedContacts (ordinaryAlternateSchedule parents beforePush digit .odd).first.val.sites
      (ordinaryAlternateSchedule parents beforePush digit .odd).copies) (v : Site) :
    v ∈ ((ordinaryAlternateSchedule parents beforePush digit .odd).first.val.insertAll
        (ordinaryAlternateSchedule parents beforePush digit .odd).copies contacts).sites ↔
      v ∈ (altPair (phase (beforePush ++ [digit]) == 1) digit parents.odd.val.sites parents.even.val.sites
        (shift parents.alternateOdd.val.sites (alternateRestoration (beforePush ++ [digit]) .odd))
        (shift parents.alternateEven.val.sites (alternateRestoration (beforePush ++ [digit]) .even))
        (parentsAt (beforePush ++ [digit])).odd (parentsAt (beforePush ++ [digit])).even).1 := by
  rw [ordinaryAlternate_raw_mem]
  rcases phase_zero_or_one' (beforePush ++ [digit]) with h | h
  · exact ordinaryAlternate_odd_phase0 parents beforePush digit hd h v
  · exact ordinaryAlternate_odd_phase1 parents beforePush digit hd h v

/-- **Structural lemma, even output.** The ordinary alternate schedule of the even output after digit `1` or `2` has the
sites of the literal even alternate child `altPair`, with the alternate piece restored by `alternateRestoration`. -/
theorem ordinaryAlternate_even_structure (parents : TileParents) (beforePush : Word) (digit : Digit)
    (hd : digit = Digit.one ∨ digit = Digit.two)
    (contacts : HeightTile.OrderedContacts (ordinaryAlternateSchedule parents beforePush digit .even).first.val.sites
      (ordinaryAlternateSchedule parents beforePush digit .even).copies) (v : Site) :
    v ∈ ((ordinaryAlternateSchedule parents beforePush digit .even).first.val.insertAll
        (ordinaryAlternateSchedule parents beforePush digit .even).copies contacts).sites ↔
      v ∈ (altPair (phase (beforePush ++ [digit]) == 1) digit parents.odd.val.sites parents.even.val.sites
        (shift parents.alternateOdd.val.sites (alternateRestoration (beforePush ++ [digit]) .odd))
        (shift parents.alternateEven.val.sites (alternateRestoration (beforePush ++ [digit]) .even))
        (parentsAt (beforePush ++ [digit])).odd (parentsAt (beforePush ++ [digit])).even).2 := by
  rw [ordinaryAlternate_raw_mem]
  rcases phase_zero_or_one' (beforePush ++ [digit]) with h | h
  · exact ordinaryAlternate_even_phase0 parents beforePush digit hd h v
  · exact ordinaryAlternate_even_phase1 parents beforePush digit hd h v

end FLatticePaper.Tiles.AlternateOrdinary
