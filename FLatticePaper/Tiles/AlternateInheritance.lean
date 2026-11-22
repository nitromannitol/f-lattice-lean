import FLatticePaper.Tiles.RestoredAlternate

/-! # The inheritance of the missing sets through the alternate pieces (task 45, step 2)

Let `tp` be parents whose donors are the TeX registers, and `pc` parents whose donors are the constructor's registers, with
`pc.X = tp.X \ D_X` for the four donors (odd, even standard; odd, even alternate). The ordinary alternate schedule of `pc`
has the sites of `altPair` (restored) for `tp`, minus the sites that every placed piece containing them misses. This is the
piece-by-piece inheritance: a site `x` of the TeX child is missing from the constructor's child exactly when every placed
piece of the TeX child that contains `x` misses it in its donor frame.

The proof is pointwise: each constructor piece is the TeX piece minus its missing set, and the disjunction over the pieces
is a propositional identity (`inheritance_pointwise`). The membership forms of the TeX and constructor unions are the
structural lemmas of AlternateOrdinary.lean (the phase cases, with the parents as parameters). -/

namespace FLatticePaper.Tiles.AlternateInheritance

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
open FLatticePaper.Tiles.Alternate FLatticePaper.Tiles.AlternateOrdinary

/-- The pointwise inheritance: if each constructor piece `Q` is the TeX piece `P` minus its missing set `m`, the union of
the constructor pieces is the union of the TeX pieces minus the sites missed by every TeX piece containing them. -/
theorem inheritance_pointwise {n : ℕ} (P Q M : Fin n → Prop) (P7 Q7 M7 : Prop)
    (hQ : ∀ s, Q s ↔ P s ∧ ¬ M s) (hQ7 : Q7 ↔ P7 ∧ ¬ M7) :
    ((∃ s, Q s) ∨ Q7) ↔ (((∃ s, P s) ∨ P7) ∧ ¬ ((∀ s, P s → M s) ∧ (P7 → M7))) := by
  constructor
  · rintro (⟨s, hs⟩ | h7)
    · refine ⟨Or.inl ⟨s, ((hQ s).mp hs).1⟩, ?_⟩
      rintro ⟨hS, _⟩
      exact ((hQ s).mp hs).2 (hS s ((hQ s).mp hs).1)
    · refine ⟨Or.inr ((hQ7.mp h7).1), ?_⟩
      rintro ⟨_, hT⟩
      exact (hQ7.mp h7).2 (hT (hQ7.mp h7).1)
  · rintro ⟨hP, hnot⟩
    by_contra hcon
    apply hnot
    refine ⟨fun s hs => ?_, fun h7 => ?_⟩
    · by_contra hm
      exact hcon (Or.inl ⟨s, (hQ s).mpr ⟨hs, hm⟩⟩)
    · by_contra hm
      exact hcon (Or.inr ((hQ7).mpr ⟨h7, hm⟩))

/-- A translate of a tile minus a tile is the translate of the first minus the translate of the second. -/
theorem mem_shift_sdiff (X D : Tile) (r x : Site) :
    x ∈ shift (X \ D) r ↔ x ∈ shift X r \ shift D r := by
  simp only [mem_shift, Finset.mem_sdiff]

/-- **Inheritance, odd output.** The ordinary alternate schedule of constructor parents `pc` (the odd output after digit
`1` or `3`) has the sites of the restored literal odd child of the TeX parents `tp`, minus the sites that every placed
piece of that child containing them misses. The missing sets are the donors' missing sets: `Dodd`, `Deven` for the standard
donors (slots `0`, `1` take the even donor), `Dae` for the even alternate donor (the seventh piece, transported by the
restoration). -/
theorem ordinaryAlternate_odd_inherits (tp pc : TileParents) (beforePush : Word) (digit : Digit)
    (hd : digit = Digit.one ∨ digit = Digit.three) (Dodd Deven Dae : Finset Site)
    (h1 : pc.odd.val.sites = tp.odd.val.sites \ Dodd) (h2 : pc.even.val.sites = tp.even.val.sites \ Deven)
    (h4 : pc.alternateEven.val.sites = tp.alternateEven.val.sites \ Dae)
    (contacts : HeightTile.OrderedContacts (ordinaryAlternateSchedule pc beforePush digit .odd).first.val.sites
      (ordinaryAlternateSchedule pc beforePush digit .odd).copies) (v : Site) :
    v ∈ ((ordinaryAlternateSchedule pc beforePush digit .odd).first.val.insertAll
        (ordinaryAlternateSchedule pc beforePush digit .odd).copies contacts).sites ↔
      v ∈ (altPair (phase (beforePush ++ [digit]) == 1) digit tp.odd.val.sites tp.even.val.sites
          (shift tp.alternateOdd.val.sites (alternateRestoration (beforePush ++ [digit]) .odd))
          (shift tp.alternateEven.val.sites (alternateRestoration (beforePush ++ [digit]) .even))
          (parentsAt (beforePush ++ [digit])).odd (parentsAt (beforePush ++ [digit])).even).1 ∧
        ¬ ((∀ s : Fin 6, v - (alternateJets (beforePush ++ [digit]) .odd s).1 ∈
              (standardSources tp .even s).val.sites →
              v - (alternateJets (beforePush ++ [digit]) .odd s).1 ∈
                (if s = 0 ∨ s = 1 then Deven else Dodd)) ∧
           (v - (seventhAlternateJet beforePush digit .odd).1 ∈
              (oldAlternate tp (beforePush ++ [digit]) .odd).val.sites →
            v - (seventhAlternateJet beforePush digit .odd).1 ∈
              shift Dae (alternateRestoration (beforePush ++ [digit]) .even))) := by
  -- the TeX side: the union of the TeX pieces is the literal odd child
  have hTA : ((∃ s : Fin 6, v - (alternateJets (beforePush ++ [digit]) .odd s).1 ∈
          (standardSources tp .even s).val.sites) ∨
        v - (seventhAlternateJet beforePush digit .odd).1 ∈
          (oldAlternate tp (beforePush ++ [digit]) .odd).val.sites) ↔
      v ∈ (altPair (phase (beforePush ++ [digit]) == 1) digit tp.odd.val.sites tp.even.val.sites
          (shift tp.alternateOdd.val.sites (alternateRestoration (beforePush ++ [digit]) .odd))
          (shift tp.alternateEven.val.sites (alternateRestoration (beforePush ++ [digit]) .even))
          (parentsAt (beforePush ++ [digit])).odd (parentsAt (beforePush ++ [digit])).even).1 := by
    rcases phase_zero_or_one' (beforePush ++ [digit]) with h | h
    · exact ordinaryAlternate_odd_phase0 tp beforePush digit hd h v
    · exact ordinaryAlternate_odd_phase1 tp beforePush digit hd h v
  -- the constructor side: the raw union is the same disjunction, with the constructor donors
  rw [ordinaryAlternate_raw_mem, ← hTA]
  -- the seventh piece
  have hQ7 : v - (seventhAlternateJet beforePush digit .odd).1 ∈
        (oldAlternate pc (beforePush ++ [digit]) .odd).val.sites ↔
      v - (seventhAlternateJet beforePush digit .odd).1 ∈
          (oldAlternate tp (beforePush ++ [digit]) .odd).val.sites ∧
        ¬ v - (seventhAlternateJet beforePush digit .odd).1 ∈
          shift Dae (alternateRestoration (beforePush ++ [digit]) .even) := by
    simp only [oldAlternate, restoreAlternate_sites]
    rw [h4, mem_shift_sdiff]
    simp only [Finset.mem_sdiff]
  -- the standard pieces
  have hQ : ∀ s : Fin 6,
      v - (alternateJets (beforePush ++ [digit]) .odd s).1 ∈ (standardSources pc .even s).val.sites ↔
        (v - (alternateJets (beforePush ++ [digit]) .odd s).1 ∈ (standardSources tp .even s).val.sites ∧
          ¬ v - (alternateJets (beforePush ++ [digit]) .odd s).1 ∈ (if s = 0 ∨ s = 1 then Deven else Dodd)) := by
    intro s
    fin_cases s <;> simp [standardSources, h1, h2, Finset.mem_sdiff]
  exact inheritance_pointwise _ _ _ _ _ _ hQ hQ7

/-- **Inheritance, even output.** The ordinary alternate schedule of constructor parents `pc` (the even output after digit
`1` or `2`) has the sites of the restored literal even child of the TeX parents `tp`, minus the sites that every placed piece
of that child containing them misses. The standard donors take the even donor in slots `0` to `3` (missing `Deven`) and the
odd donor in slots `4`, `5` (missing `Dodd`); the seventh piece is the odd alternate donor (missing `Dao`, transported by the
restoration). -/
theorem ordinaryAlternate_even_inherits (tp pc : TileParents) (beforePush : Word) (digit : Digit)
    (hd : digit = Digit.one ∨ digit = Digit.two) (Dodd Deven Dao : Finset Site)
    (h1 : pc.odd.val.sites = tp.odd.val.sites \ Dodd) (h2 : pc.even.val.sites = tp.even.val.sites \ Deven)
    (h3 : pc.alternateOdd.val.sites = tp.alternateOdd.val.sites \ Dao)
    (contacts : HeightTile.OrderedContacts (ordinaryAlternateSchedule pc beforePush digit .even).first.val.sites
      (ordinaryAlternateSchedule pc beforePush digit .even).copies) (v : Site) :
    v ∈ ((ordinaryAlternateSchedule pc beforePush digit .even).first.val.insertAll
        (ordinaryAlternateSchedule pc beforePush digit .even).copies contacts).sites ↔
      v ∈ (altPair (phase (beforePush ++ [digit]) == 1) digit tp.odd.val.sites tp.even.val.sites
          (shift tp.alternateOdd.val.sites (alternateRestoration (beforePush ++ [digit]) .odd))
          (shift tp.alternateEven.val.sites (alternateRestoration (beforePush ++ [digit]) .even))
          (parentsAt (beforePush ++ [digit])).odd (parentsAt (beforePush ++ [digit])).even).2 ∧
        ¬ ((∀ s : Fin 6, v - (alternateJets (beforePush ++ [digit]) .even s).1 ∈
              (standardSources tp .odd s).val.sites →
              v - (alternateJets (beforePush ++ [digit]) .even s).1 ∈
                (if s = 4 ∨ s = 5 then Dodd else Deven)) ∧
           (v - (seventhAlternateJet beforePush digit .even).1 ∈
              (oldAlternate tp (beforePush ++ [digit]) .even).val.sites →
            v - (seventhAlternateJet beforePush digit .even).1 ∈
              shift Dao (alternateRestoration (beforePush ++ [digit]) .odd))) := by
  have hTA : ((∃ s : Fin 6, v - (alternateJets (beforePush ++ [digit]) .even s).1 ∈
          (standardSources tp .odd s).val.sites) ∨
        v - (seventhAlternateJet beforePush digit .even).1 ∈
          (oldAlternate tp (beforePush ++ [digit]) .even).val.sites) ↔
      v ∈ (altPair (phase (beforePush ++ [digit]) == 1) digit tp.odd.val.sites tp.even.val.sites
          (shift tp.alternateOdd.val.sites (alternateRestoration (beforePush ++ [digit]) .odd))
          (shift tp.alternateEven.val.sites (alternateRestoration (beforePush ++ [digit]) .even))
          (parentsAt (beforePush ++ [digit])).odd (parentsAt (beforePush ++ [digit])).even).2 := by
    rcases phase_zero_or_one' (beforePush ++ [digit]) with h | h
    · exact ordinaryAlternate_even_phase0 tp beforePush digit hd h v
    · exact ordinaryAlternate_even_phase1 tp beforePush digit hd h v
  rw [ordinaryAlternate_raw_mem, ← hTA]
  have hQ7 : v - (seventhAlternateJet beforePush digit .even).1 ∈
        (oldAlternate pc (beforePush ++ [digit]) .even).val.sites ↔
      v - (seventhAlternateJet beforePush digit .even).1 ∈
          (oldAlternate tp (beforePush ++ [digit]) .even).val.sites ∧
        ¬ v - (seventhAlternateJet beforePush digit .even).1 ∈
          shift Dao (alternateRestoration (beforePush ++ [digit]) .odd) := by
    simp only [oldAlternate, restoreAlternate_sites]
    rw [h3, mem_shift_sdiff]
    simp only [Finset.mem_sdiff]
  have hQ : ∀ s : Fin 6,
      v - (alternateJets (beforePush ++ [digit]) .even s).1 ∈ (standardSources pc .odd s).val.sites ↔
        (v - (alternateJets (beforePush ++ [digit]) .even s).1 ∈ (standardSources tp .odd s).val.sites ∧
          ¬ v - (alternateJets (beforePush ++ [digit]) .even s).1 ∈ (if s = 4 ∨ s = 5 then Dodd else Deven)) := by
    intro s
    fin_cases s <;> simp [standardSources, h1, h2, Finset.mem_sdiff]
  exact inheritance_pointwise _ _ _ _ _ _ hQ hQ7

end FLatticePaper.Tiles.AlternateInheritance
