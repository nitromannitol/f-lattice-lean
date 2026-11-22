import FLatticePaper.Construction.Native
import FLatticePaper.Construction.OffsetTables
import FLatticePaper.Farey.Recursion

/-! # Membership in the registers, through the evaluator's trim and centring (task 37, invariants)

The registers the evaluator stores are trimmed (`PlacedSchedule.finish .tile`), and a register is used as a donor after
`llCenter` (`parentsFor`). Both are translations, and the composite is the raw union translated by its lower-left cell:
`llCenter (trim raw)` has sites `raw.sites - lowerLeft raw`. So a membership fact about a register is a fact about the raw
union relative to its lower-left cell. This file proves that identity and the membership of an insertion's union. -/

namespace FLatticePaper.Construction

open HeightTile
open Farey

/-- The lower-left cell moves with a translation. -/
theorem lowerLeft_place (tile : HeightTile Site) (hne : tile.sites.Nonempty) (off : Site) :
    (tile.place off 0).lowerLeft (tile.place_sites_nonempty off 0 hne) = tile.lowerLeft hne + off := by
  apply HeightTile.lowerLeft_eq_of_minimal
  · have hmem := tile.lowerLeft_mem hne
    exact (tile.mem_place_sites off 0 _).mpr (by simpa using hmem)
  · intro site hsite
    obtain ⟨s, hs, rfl⟩ : ∃ s ∈ tile.sites, s + off = site := by
      rw [HeightTile.mem_place_sites] at hsite
      exact ⟨site - off, hsite, by simp⟩
    have h := tile.lowerLeft_le_of_mem hne hs
    simp only [Prod.fst_add, Prod.snd_add]
    constructor
    · omega
    · intro heq
      have := h.2 (by omega)
      omega

/-- The register stored after a trim, centred as a donor, has the raw sites shifted by the raw lower-left cell. -/
theorem mem_llCenter_trim (raw : HeightTile Site) (hne : raw.sites.Nonempty) (v : Site) :
    v ∈ ((raw.trim hne).llCenter (raw.trim_sites_nonempty hne)).sites ↔
      v + raw.lowerLeft hne ∈ raw.sites := by
  unfold HeightTile.llCenter HeightTile.trim
  rw [HeightTile.mem_place_sites, HeightTile.mem_place_sites, lowerLeft_place raw hne (-raw.boxOrigin hne)]
  have e : v - -(raw.lowerLeft hne + -raw.boxOrigin hne) - -raw.boxOrigin hne = v + raw.lowerLeft hne := by
    ext <;> simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg] <;> omega
  rw [e]

/-- Membership in a fold of unions. -/
theorem mem_foldl_union (l : List (HeightTile Site)) (init : Finset Site) (v : Site) :
    v ∈ l.foldl (fun acc tile => acc ∪ tile.sites) init ↔ v ∈ init ∨ ∃ t ∈ l, v ∈ t.sites := by
  induction l generalizing init with
  | nil => simp
  | cons t rest ih =>
    simp only [List.foldl_cons, ih]
    constructor
    · rintro (h | ⟨u, hu, hv⟩)
      · rcases Finset.mem_union.mp h with h | h
        · exact Or.inl h
        · exact Or.inr ⟨t, List.mem_cons_self, h⟩
      · exact Or.inr ⟨u, List.mem_cons_of_mem _ hu, hv⟩
    · rintro (h | ⟨u, hu, hv⟩)
      · exact Or.inl (Finset.mem_union_left _ h)
      · rcases List.mem_cons.mp hu with rfl | hu
        · exact Or.inl (Finset.mem_union_right _ hv)
        · exact Or.inr ⟨u, hu, hv⟩

/-- Membership in the union of an insertion sequence (the sites of `insertAll`). -/
theorem mem_insertAll (first : HeightTile Site) (copies : List (HeightTile Site))
    (contacts : OrderedContacts first.sites copies) (v : Site) :
    v ∈ (first.insertAll copies contacts).sites ↔ v ∈ first.sites ∨ ∃ t ∈ copies, v ∈ t.sites := by
  rw [HeightTile.insertAll_sites, mem_foldl_union]

/-- A site of a placed copy is a donor site translated by the copy's offset. -/
theorem mem_placedBySlot (jets : Fin 6 → TileJet) (donor : Fin 6 → NonemptyTile) (slot : Fin 6) (v : Site) :
    v ∈ (placedBySlot jets donor slot).val.sites ↔ v - (jets slot).1 ∈ (donor slot).val.sites := by
  unfold placedBySlot TileJet.place NonemptyTile.place
  rw [HeightTile.mem_place_sites]

/-- A site of an ordinary standard schedule's raw union: a slot of the schedule (the first or one of the rest) whose donor
contains the site translated back by the slot's offset. -/
theorem mem_ordinaryStandard_raw (parents : TileParents) (word : Word) (parity : Parity) (slot : Fin 6)
    (hslot : slot = 0 ∨ slot ∈ afterFirstStandard parity) (v : Site)
    (hv : v - (standardJets word parity slot).1 ∈ (standardSources parents parity slot).val.sites)
    (contacts : OrderedContacts (ordinaryStandardSchedule parents word parity).first.val.sites
      (ordinaryStandardSchedule parents word parity).copies) :
    v ∈ ((ordinaryStandardSchedule parents word parity).first.val.insertAll
      (ordinaryStandardSchedule parents word parity).copies contacts).sites := by
  rw [mem_insertAll]
  rcases hslot with rfl | hslot
  · left
    exact (mem_placedBySlot _ _ 0 v).mpr hv
  · right
    refine ⟨(placedBySlot (standardJets word parity) (standardSources parents parity) slot).val, ?_,
      (mem_placedBySlot _ _ slot v).mpr hv⟩
    exact List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨slot, hslot, rfl⟩, rfl⟩

/-! ### Lex non-negativity, the lower-left cell at the origin, and the kernel of the children -/

/-- A site is at or after the origin in row-first order (the lower-left order of `lowerLeft`). -/
def Lex0 (v : Site) : Prop := 0 ≤ v.2 ∧ (v.2 = 0 → 0 ≤ v.1)

/-- A donor is normalised: the origin is a site and every site is at or after it. -/
def ZeroLex (T : Finset Site) : Prop := (0 : Site) ∈ T ∧ ∀ d ∈ T, Lex0 d

theorem lex0_add {a b : Site} (ha : Lex0 a) (hb : Lex0 b) : Lex0 (a + b) := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  unfold Lex0 at *
  simp only [Prod.fst_add, Prod.snd_add]
  constructor
  · omega
  · intro h
    have h1 := ha2 (by omega)
    have h2 := hb2 (by omega)
    omega

theorem lex0_zero : Lex0 (0 : Site) := by
  unfold Lex0
  simp

theorem lex0_two_smul {a : Site} (ha : Lex0 a) : Lex0 ((2 : ℕ) • a) := by
  rw [two_nsmul]
  exact lex0_add ha ha

theorem lex0_texV1Odd {f : Fraction} (hf : 0 ≤ f.num ∧ 0 ≤ f.den) : Lex0 (texV1Odd f) := by
  unfold Lex0 texV1Odd
  simp only
  constructor
  · omega
  · intro h
    omega

theorem lex0_texV1Even {f : Fraction} (hf : 0 ≤ f.num ∧ 0 ≤ f.den) : Lex0 (texV1Even f) := by
  unfold Lex0 texV1Even
  simp only
  constructor
  · omega
  · intro h
    omega

theorem lex0_texV2 {f : Fraction} (hf : 0 ≤ f.num ∧ 0 ≤ f.den) : Lex0 (texV2 f) := by
  unfold Lex0 texV2
  simp only
  constructor
  · omega
  · intro h
    omega

/-- The odd child of the word is the sum of the parents, so its doubled kernel is the sum of the parent kernels. -/
theorem texV1Odd_current_odd (word : Word) :
    texV1Odd ((parentsAt word).current .odd) =
      texV1Odd (parentsAt word).odd + (2 : ℕ) • texV1Even (parentsAt word).even := by
  unfold Parents.current Parents.combine texV1Odd texV1Even
  refine Prod.ext ?_ ?_ <;> simp <;> ring

/-- The even child is `2 p + q`, so its kernel is the doubled-odd-parent kernel plus the even-parent kernel. -/
theorem texV1Even_current_even (word : Word) :
    texV1Even ((parentsAt word).current .even) =
      texV1Odd (parentsAt word).odd + texV1Even (parentsAt word).even := by
  unfold Parents.current Parents.combine texV1Odd texV1Even
  refine Prod.ext ?_ ?_ <;> simp

/-- Every standard jet translation is at or after the origin, for every parity, phase and slot. -/
theorem standardJets_lex0 (word : Word) (parity : Parity) (slot : Fin 6)
    (hw : (parentsAt word).ValidFrame) : Lex0 (standardJets word parity slot).1 := by
  obtain ⟨hpd, hpn, hpm⟩ := hw.odd_bounds
  obtain ⟨hqd, hqn, hqm⟩ := hw.even_bounds
  have hodd : 0 ≤ (parentsAt word).odd.num ∧ 0 ≤ (parentsAt word).odd.den := ⟨hpn, by omega⟩
  have heven : 0 ≤ (parentsAt word).even.num ∧ 0 ≤ (parentsAt word).even.den := ⟨hqn, by omega⟩
  have hph : phase word = 0 ∨ phase word = 1 := by
    unfold phase
    omega
  rcases hph with h | h <;> cases parity
  · obtain ⟨j0, j1, j2, j3, j4, j5⟩ := standard_odd_phase0 word h
    have e0 : Lex0 (standardJets word .odd 0).1 := by
      rw [j0]; exact lex0_zero
    have e1 : Lex0 (standardJets word .odd 1).1 := by
      rw [j1]; exact lex0_texV1Even heven
    have e2 : Lex0 (standardJets word .odd 2).1 := by
      rw [j2]; exact lex0_add (lex0_texV1Odd hodd) (lex0_texV2 hodd)
    have e3 : Lex0 (standardJets word .odd 3).1 := by
      rw [j3]; exact lex0_add (lex0_add (lex0_texV1Odd hodd) (lex0_texV2 hodd)) (lex0_texV1Even heven)
    have e4 : Lex0 (standardJets word .odd 4).1 := by
      rw [j4]; exact lex0_two_smul (lex0_texV1Even heven)
    have e5 : Lex0 (standardJets word .odd 5).1 := by
      rw [j5]; exact lex0_texV2 heven
    match slot with
    | 0 => exact e0
    | 1 => exact e1
    | 2 => exact e2
    | 3 => exact e3
    | 4 => exact e4
    | 5 => exact e5
  · obtain ⟨j0, j1, j2, j3, j4, j5⟩ := standard_even_phase0 word h
    have e0 : Lex0 (standardJets word .even 0).1 := by
      rw [j0]; exact lex0_zero
    have e1 : Lex0 (standardJets word .even 1).1 := by
      rw [j1]; exact lex0_add (lex0_texV1Odd hodd) (lex0_two_smul (lex0_texV2 hodd))
    have e2 : Lex0 (standardJets word .even 2).1 := by
      rw [j2]; exact lex0_texV1Even heven
    have e3 : Lex0 (standardJets word .even 3).1 := by
      rw [j3]; exact lex0_add (lex0_texV1Even heven) (lex0_texV2 hodd)
    have e4 : Lex0 (standardJets word .even 4).1 := by
      rw [j4]; exact lex0_texV2 heven
    have e5 : Lex0 (standardJets word .even 5).1 := by
      rw [j5]; exact lex0_add (lex0_texV2 heven) (lex0_texV2 hodd)
    match slot with
    | 0 => exact e0
    | 1 => exact e1
    | 2 => exact e2
    | 3 => exact e3
    | 4 => exact e4
    | 5 => exact e5
  · obtain ⟨j0, j1, j2, j3, j4, j5⟩ := standard_odd_phase1 word h
    have e0 : Lex0 (standardJets word .odd 0).1 := by
      rw [j0]; exact lex0_texV1Odd hodd
    have e1 : Lex0 (standardJets word .odd 1).1 := by
      rw [j1]; exact lex0_add (lex0_texV1Odd hodd) (lex0_texV1Even heven)
    have e2 : Lex0 (standardJets word .odd 2).1 := by
      rw [j2]; exact lex0_texV2 hodd
    have e3 : Lex0 (standardJets word .odd 3).1 := by
      rw [j3]; exact lex0_add (lex0_texV2 hodd) (lex0_texV1Even heven)
    have e4 : Lex0 (standardJets word .odd 4).1 := by
      rw [j4]; exact lex0_zero
    have e5 : Lex0 (standardJets word .odd 5).1 := by
      rw [j5]; exact lex0_add (lex0_two_smul (lex0_texV1Even heven)) (lex0_texV2 heven)
    match slot with
    | 0 => exact e0
    | 1 => exact e1
    | 2 => exact e2
    | 3 => exact e3
    | 4 => exact e4
    | 5 => exact e5
  · obtain ⟨j0, j1, j2, j3, j4, j5⟩ := standard_even_phase1 word h
    have e0 : Lex0 (standardJets word .even 0).1 := by
      rw [j0]; exact lex0_texV1Odd hodd
    have e1 : Lex0 (standardJets word .even 1).1 := by
      rw [j1]; exact lex0_two_smul (lex0_texV2 hodd)
    have e2 : Lex0 (standardJets word .even 2).1 := by
      rw [j2]; exact lex0_zero
    have e3 : Lex0 (standardJets word .even 3).1 := by
      rw [j3]; exact lex0_texV2 hodd
    have e4 : Lex0 (standardJets word .even 4).1 := by
      rw [j4]; exact lex0_add (lex0_texV1Even heven) (lex0_texV2 heven)
    have e5 : Lex0 (standardJets word .even 5).1 := by
      rw [j5]; exact lex0_add (lex0_add (lex0_texV1Even heven) (lex0_texV2 heven)) (lex0_texV2 hodd)
    match slot with
    | 0 => exact e0
    | 1 => exact e1
    | 2 => exact e2
    | 3 => exact e3
    | 4 => exact e4
    | 5 => exact e5

/-! ### The ordinary standard step: lower-left zero and the family of the child -/

theorem standardSources_zeroLex (parents : TileParents) (parity : Parity) (slot : Fin 6)
    (ho : ZeroLex parents.odd.val.sites) (he : ZeroLex parents.even.val.sites) :
    ZeroLex (standardSources parents parity slot).val.sites := by
  match slot with
  | 0 => cases parity <;> exact he
  | 1 => cases parity <;> exact he
  | 2 => cases parity
         · exact he
         · exact ho
  | 3 => cases parity
         · exact he
         · exact ho
  | 4 => cases parity <;> exact ho
  | 5 => cases parity <;> exact ho

theorem lex0_of_placed {jet site : Site} {T : Finset Site} (hT : ZeroLex T) (hj : Lex0 jet)
    (h : site - jet ∈ T) : Lex0 site := by
  have := lex0_add hj (hT.2 _ h)
  rwa [add_sub_cancel] at this

theorem copies_placed_ordStd (parents : TileParents) (word : Word) (parity : Parity) (t : HeightTile Site)
    (ht : t ∈ (ordinaryStandardSchedule parents word parity).copies) :
    ∃ s : Fin 6, t = (placedBySlot (standardJets word parity) (standardSources parents parity) s).val := by
  unfold PlacedSchedule.copies ordinaryStandardSchedule at ht
  simp only [List.mem_map] at ht
  obtain ⟨u, ⟨s, hs, rfl⟩, rfl⟩ := ht
  exact ⟨s, rfl⟩

/-- Every site of the raw union of an ordinary standard schedule is at or after the origin. -/
theorem ordStd_site_lex0 (parents : TileParents) (word : Word) (parity : Parity)
    (hw : (parentsAt word).ValidFrame) (ho : ZeroLex parents.odd.val.sites) (he : ZeroLex parents.even.val.sites)
    (contacts : OrderedContacts (ordinaryStandardSchedule parents word parity).first.val.sites
      (ordinaryStandardSchedule parents word parity).copies) (v : Site)
    (hv : v ∈ ((ordinaryStandardSchedule parents word parity).first.val.insertAll
      (ordinaryStandardSchedule parents word parity).copies contacts).sites) : Lex0 v := by
  rw [mem_insertAll] at hv
  rcases hv with h | ⟨t, ht, hvt⟩
  · have h' : v ∈ (placedBySlot (standardJets word parity) (standardSources parents parity) 0).val.sites := h
    rw [mem_placedBySlot] at h'
    exact lex0_of_placed (standardSources_zeroLex parents parity 0 ho he) (standardJets_lex0 word parity 0 hw) h'
  · obtain ⟨s, rfl⟩ := copies_placed_ordStd parents word parity t ht
    rw [mem_placedBySlot] at hvt
    exact lex0_of_placed (standardSources_zeroLex parents parity s ho he) (standardJets_lex0 word parity s hw) hvt

/-- The raw union of an ordinary standard schedule (the register before trimming). -/
def ordStdRaw (parents : TileParents) (word : Word) (parity : Parity)
    (contacts : OrderedContacts (ordinaryStandardSchedule parents word parity).first.val.sites
      (ordinaryStandardSchedule parents word parity).copies) : HeightTile Site :=
  (ordinaryStandardSchedule parents word parity).first.val.insertAll
    (ordinaryStandardSchedule parents word parity).copies contacts

/-- The lower-left cell of the raw union is the origin, given an origin site and lex non-negativity. -/
theorem ordStdRaw_lowerLeft_zero (parents : TileParents) (word : Word) (parity : Parity)
    (hw : (parentsAt word).ValidFrame) (ho : ZeroLex parents.odd.val.sites) (he : ZeroLex parents.even.val.sites)
    (contacts : OrderedContacts (ordinaryStandardSchedule parents word parity).first.val.sites
      (ordinaryStandardSchedule parents word parity).copies)
    (hzero : (0 : Site) ∈ (ordStdRaw parents word parity contacts).sites) (hne : (ordStdRaw parents word parity contacts).sites.Nonempty) :
    (ordStdRaw parents word parity contacts).lowerLeft hne = 0 := by
  apply HeightTile.lowerLeft_eq_of_minimal _ hne hzero
  intro site hsite
  have h := ordStd_site_lex0 parents word parity hw ho he contacts site hsite
  exact ⟨h.1, fun e => h.2 e.symm⟩

theorem sub_two_smul_helper (a Q : Site) : a + (2 : ℕ) • Q - (a + Q) = Q := by
  rw [two_nsmul]
  ext <;> simp

/-- The family of the odd child of an ordinary standard step: the child's doubled kernel, `e_1`, `e_2` and the origin. -/
theorem ordinaryStandard_odd_family (parents : TileParents) (word : Word) (_hw : (parentsAt word).ValidFrame)
    (ho : ZeroLex parents.odd.val.sites) (he : ZeroLex parents.even.val.sites)
    (hvo : texV1Odd (parentsAt word).odd ∈ parents.odd.val.sites)
    (hve : texV1Even (parentsAt word).even ∈ parents.even.val.sites)
    (ho1 : ((1 : ℤ), (0 : ℤ)) ∈ parents.odd.val.sites) (ho2 : ((0 : ℤ), (1 : ℤ)) ∈ parents.odd.val.sites)
    (he1 : ((1 : ℤ), (0 : ℤ)) ∈ parents.even.val.sites) (he2 : ((0 : ℤ), (1 : ℤ)) ∈ parents.even.val.sites)
    (contacts : OrderedContacts (ordinaryStandardSchedule parents word .odd).first.val.sites
      (ordinaryStandardSchedule parents word .odd).copies) :
    texV1Odd ((parentsAt word).current .odd) ∈ (ordStdRaw parents word .odd contacts).sites ∧
      ((1 : ℤ), (0 : ℤ)) ∈ (ordStdRaw parents word .odd contacts).sites ∧
      ((0 : ℤ), (1 : ℤ)) ∈ (ordStdRaw parents word .odd contacts).sites ∧
      (0 : Site) ∈ (ordStdRaw parents word .odd contacts).sites := by
  have hchild := texV1Odd_current_odd word
  have hph : phase word = 0 ∨ phase word = 1 := by
    unfold phase
    omega
  rcases hph with h | h
  · obtain ⟨j0, j1, j2, j3, j4, j5⟩ := standard_odd_phase0 word h
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply mem_ordinaryStandard_raw parents word .odd 4 (Or.inr (by decide)) _ _ contacts
      rw [j4, hchild, add_sub_cancel_right]
      exact hvo
    · apply mem_ordinaryStandard_raw parents word .odd 0 (Or.inl rfl) _ _ contacts
      rw [j0, sub_zero]
      exact he1
    · apply mem_ordinaryStandard_raw parents word .odd 0 (Or.inl rfl) _ _ contacts
      rw [j0, sub_zero]
      exact he2
    · apply mem_ordinaryStandard_raw parents word .odd 0 (Or.inl rfl) _ _ contacts
      rw [j0, sub_zero]
      exact he.1
  · obtain ⟨j0, j1, j2, j3, j4, j5⟩ := standard_odd_phase1 word h
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply mem_ordinaryStandard_raw parents word .odd 1 (Or.inr (by decide)) _ _ contacts
      rw [j1, hchild, sub_two_smul_helper]
      exact hve
    · apply mem_ordinaryStandard_raw parents word .odd 4 (Or.inr (by decide)) _ _ contacts
      rw [j4, sub_zero]
      exact ho1
    · apply mem_ordinaryStandard_raw parents word .odd 4 (Or.inr (by decide)) _ _ contacts
      rw [j4, sub_zero]
      exact ho2
    · apply mem_ordinaryStandard_raw parents word .odd 4 (Or.inr (by decide)) _ _ contacts
      rw [j4, sub_zero]
      exact ho.1

/-- The family of the even child of an ordinary standard step. -/
theorem ordinaryStandard_even_family (parents : TileParents) (word : Word) (_hw : (parentsAt word).ValidFrame)
    (ho : ZeroLex parents.odd.val.sites) (he : ZeroLex parents.even.val.sites)
    (hvo : texV1Odd (parentsAt word).odd ∈ parents.odd.val.sites)
    (hve : texV1Even (parentsAt word).even ∈ parents.even.val.sites)
    (ho1 : ((1 : ℤ), (0 : ℤ)) ∈ parents.odd.val.sites) (ho2 : ((0 : ℤ), (1 : ℤ)) ∈ parents.odd.val.sites)
    (he1 : ((1 : ℤ), (0 : ℤ)) ∈ parents.even.val.sites) (he2 : ((0 : ℤ), (1 : ℤ)) ∈ parents.even.val.sites)
    (contacts : OrderedContacts (ordinaryStandardSchedule parents word .even).first.val.sites
      (ordinaryStandardSchedule parents word .even).copies) :
    texV1Even ((parentsAt word).current .even) ∈ (ordStdRaw parents word .even contacts).sites ∧
      ((1 : ℤ), (0 : ℤ)) ∈ (ordStdRaw parents word .even contacts).sites ∧
      ((0 : ℤ), (1 : ℤ)) ∈ (ordStdRaw parents word .even contacts).sites ∧
      (0 : Site) ∈ (ordStdRaw parents word .even contacts).sites := by
  have hchild := texV1Even_current_even word
  have hph : phase word = 0 ∨ phase word = 1 := by
    unfold phase
    omega
  rcases hph with h | h
  · obtain ⟨j0, j1, j2, j3, j4, j5⟩ := standard_even_phase0 word h
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply mem_ordinaryStandard_raw parents word .even 2 (Or.inr (by decide)) _ _ contacts
      rw [j2, hchild, add_sub_cancel_right]
      exact hvo
    · apply mem_ordinaryStandard_raw parents word .even 0 (Or.inl rfl) _ _ contacts
      rw [j0, sub_zero]
      exact he1
    · apply mem_ordinaryStandard_raw parents word .even 0 (Or.inl rfl) _ _ contacts
      rw [j0, sub_zero]
      exact he2
    · apply mem_ordinaryStandard_raw parents word .even 0 (Or.inl rfl) _ _ contacts
      rw [j0, sub_zero]
      exact he.1
  · obtain ⟨j0, j1, j2, j3, j4, j5⟩ := standard_even_phase1 word h
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply mem_ordinaryStandard_raw parents word .even 0 (Or.inl rfl) _ _ contacts
      rw [j0, hchild, add_sub_cancel_left]
      exact hve
    · apply mem_ordinaryStandard_raw parents word .even 2 (Or.inr (by decide)) _ _ contacts
      rw [j2, sub_zero]
      exact ho1
    · apply mem_ordinaryStandard_raw parents word .even 2 (Or.inr (by decide)) _ _ contacts
      rw [j2, sub_zero]
      exact ho2
    · apply mem_ordinaryStandard_raw parents word .even 2 (Or.inr (by decide)) _ _ contacts
      rw [j2, sub_zero]
      exact ho.1

/-- The stored odd register of an ordinary standard step (trimmed, then centred as a donor): the family of the child. -/
theorem ordinaryStandard_odd_stored (parents : TileParents) (word : Word) (hw : (parentsAt word).ValidFrame)
    (ho : ZeroLex parents.odd.val.sites) (he : ZeroLex parents.even.val.sites)
    (hvo : texV1Odd (parentsAt word).odd ∈ parents.odd.val.sites)
    (hve : texV1Even (parentsAt word).even ∈ parents.even.val.sites)
    (ho1 : ((1 : ℤ), (0 : ℤ)) ∈ parents.odd.val.sites) (ho2 : ((0 : ℤ), (1 : ℤ)) ∈ parents.odd.val.sites)
    (he1 : ((1 : ℤ), (0 : ℤ)) ∈ parents.even.val.sites) (he2 : ((0 : ℤ), (1 : ℤ)) ∈ parents.even.val.sites)
    (contacts : OrderedContacts (ordinaryStandardSchedule parents word .odd).first.val.sites
      (ordinaryStandardSchedule parents word .odd).copies)
    (hne : (ordStdRaw parents word .odd contacts).sites.Nonempty) :
    texV1Odd ((parentsAt word).current .odd) ∈
        (((ordStdRaw parents word .odd contacts).trim hne).llCenter
          ((ordStdRaw parents word .odd contacts).trim_sites_nonempty hne)).sites ∧
      ((1 : ℤ), (0 : ℤ)) ∈ (((ordStdRaw parents word .odd contacts).trim hne).llCenter
          ((ordStdRaw parents word .odd contacts).trim_sites_nonempty hne)).sites ∧
      ((0 : ℤ), (1 : ℤ)) ∈ (((ordStdRaw parents word .odd contacts).trim hne).llCenter
          ((ordStdRaw parents word .odd contacts).trim_sites_nonempty hne)).sites := by
  obtain ⟨h1, h2, h3, h4⟩ := ordinaryStandard_odd_family parents word hw ho he hvo hve ho1 ho2 he1 he2 contacts
  have hll := ordStdRaw_lowerLeft_zero parents word .odd hw ho he contacts h4 hne
  refine ⟨?_, ?_, ?_⟩ <;> rw [mem_llCenter_trim, hll, add_zero]
  · exact h1
  · exact h2
  · exact h3

theorem ordinaryStandard_even_stored (parents : TileParents) (word : Word) (hw : (parentsAt word).ValidFrame)
    (ho : ZeroLex parents.odd.val.sites) (he : ZeroLex parents.even.val.sites)
    (hvo : texV1Odd (parentsAt word).odd ∈ parents.odd.val.sites)
    (hve : texV1Even (parentsAt word).even ∈ parents.even.val.sites)
    (ho1 : ((1 : ℤ), (0 : ℤ)) ∈ parents.odd.val.sites) (ho2 : ((0 : ℤ), (1 : ℤ)) ∈ parents.odd.val.sites)
    (he1 : ((1 : ℤ), (0 : ℤ)) ∈ parents.even.val.sites) (he2 : ((0 : ℤ), (1 : ℤ)) ∈ parents.even.val.sites)
    (contacts : OrderedContacts (ordinaryStandardSchedule parents word .even).first.val.sites
      (ordinaryStandardSchedule parents word .even).copies)
    (hne : (ordStdRaw parents word .even contacts).sites.Nonempty) :
    texV1Even ((parentsAt word).current .even) ∈
        (((ordStdRaw parents word .even contacts).trim hne).llCenter
          ((ordStdRaw parents word .even contacts).trim_sites_nonempty hne)).sites ∧
      ((1 : ℤ), (0 : ℤ)) ∈ (((ordStdRaw parents word .even contacts).trim hne).llCenter
          ((ordStdRaw parents word .even contacts).trim_sites_nonempty hne)).sites ∧
      ((0 : ℤ), (1 : ℤ)) ∈ (((ordStdRaw parents word .even contacts).trim hne).llCenter
          ((ordStdRaw parents word .even contacts).trim_sites_nonempty hne)).sites := by
  obtain ⟨h1, h2, h3, h4⟩ := ordinaryStandard_even_family parents word hw ho he hvo hve ho1 ho2 he1 he2 contacts
  have hll := ordStdRaw_lowerLeft_zero parents word .even hw ho he contacts h4 hne
  refine ⟨?_, ?_, ?_⟩ <;> rw [mem_llCenter_trim, hll, add_zero]
  · exact h1
  · exact h2
  · exact h3

end FLatticePaper.Construction
