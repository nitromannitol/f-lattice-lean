import FLatticePaper.Construction.PlaneIdentification

/-! The origin of the ordinary standard assembly (task 43).

Insertion moves heights but never sites, so the raw assembly of an ordinary standard schedule has as sites the union of
its six placed copies. Each copy is a centred donor (its lower-left site is the origin) translated by a standard jet
whose offset is row-first nonnegative. Hence the raw assembly has its lower-left site at the origin, and the chart
offset `lowerLeft(output) + boxOrigin(raw)` of the output vanishes. This discharges the chart hypothesis `hzero` of
`ordinaryStandard_identifies_register`, given that the donors are centred; the native parents are centred by
`TileRegisters.parentsFor`, which llCenters its registers. -/

namespace FLatticePaper.Construction

open Farey HeightTile

/-- Row-first nonnegativity: at or after the origin in the order (lowest row first, then leftmost). -/
def RowNonneg (s : FLatticePaper.Site) : Prop := 0 < s.2 ∨ (s.2 = 0 ∧ 0 ≤ s.1)

/-- A tile is centred when it contains the origin and all its sites are row-first nonnegative. -/
def RowCentred (tile : NonemptyTile) : Prop :=
  (0 : FLatticePaper.Site) ∈ tile.val.sites ∧ ∀ s ∈ tile.val.sites, RowNonneg s

theorem rowNonneg_zero : RowNonneg (0 : FLatticePaper.Site) := by
  unfold RowNonneg
  simp

theorem rowNonneg_add {a b : FLatticePaper.Site} (ha : RowNonneg a) (hb : RowNonneg b) :
    RowNonneg (a + b) := by
  unfold RowNonneg at *
  simp only [Prod.fst_add, Prod.snd_add]
  omega

theorem rowNonneg_two_mul {a : FLatticePaper.Site} (ha : RowNonneg a) : RowNonneg (2 * a) := by
  have h : (2 : FLatticePaper.Site) * a = a + a := by
    rw [two_mul]
  rw [h]
  exact rowNonneg_add ha ha

theorem kernelJet_rowNonneg {f : Fraction} (hden : 0 < f.den) (hnum : 0 ≤ f.num) :
    RowNonneg (kernelJet f).1 := by
  unfold RowNonneg kernelJet
  dsimp only
  omega

theorem transverseJet_rowNonneg {f : Fraction} (hden : 0 < f.den) (hnum : 0 ≤ f.num) :
    RowNonneg (transverseJet f).1 := by
  unfold RowNonneg transverseJet
  dsimp only
  omega

theorem parentsAt_bounds (word : Word) :
    (0 < (parentsAt word).odd.den ∧ 0 ≤ (parentsAt word).odd.num) ∧
      (0 < (parentsAt word).even.den ∧ 0 ≤ (parentsAt word).even.num) := by
  have hv := parentsAt_valid word
  have ho := hv.odd_bounds
  have he := hv.even_bounds
  unfold Fraction.InUnitInterval at ho he
  exact ⟨⟨ho.1, ho.2.1⟩, ⟨he.1, he.2.1⟩⟩

/-- Every standard jet has a row-first nonnegative offset. -/
theorem standardJets_rowNonneg (word : Word) (parity : Parity) (slot : Fin 6) :
    RowNonneg (standardJets word parity slot).1 := by
  obtain ⟨⟨ho1, ho2⟩, ⟨he1, he2⟩⟩ := parentsAt_bounds word
  have hKo := kernelJet_rowNonneg ho1 ho2
  have hTo := transverseJet_rowNonneg ho1 ho2
  have hKe := kernelJet_rowNonneg he1 he2
  have hTe := transverseJet_rowNonneg he1 he2
  unfold standardJets
  cases parity <;> split_ifs <;> fin_cases slot <;>
    simp [doubleFirst, doubleLast] <;>
    repeat' (first | exact rowNonneg_zero | exact hKo | exact hTo | exact hKe | exact hTe | apply rowNonneg_add | apply rowNonneg_two_mul)

/-- Each parity has a standard jet with offset zero, in the slot whose donor is centred. -/
theorem standardJets_zero_slot (word : Word) (parity : Parity) :
    ∃ slot : Fin 6, (standardJets word parity slot).1 = 0 := by
  unfold standardJets
  cases parity <;> split_ifs
  · exact ⟨0, by simp [doubleFirst]⟩
  · exact ⟨4, by simp [doubleFirst]⟩
  · exact ⟨0, by simp [doubleLast]⟩
  · exact ⟨2, by simp [doubleLast]⟩

theorem NonemptyTile.llCenter_rowCentred (tile : NonemptyTile) : RowCentred tile.llCenter := by
  refine ⟨tile.val.zero_mem_llCenter tile.property, ?_⟩
  intro s hs
  change s ∈ (tile.val.place (-tile.val.lowerLeft tile.property) 0).sites at hs
  rw [mem_place_sites, sub_neg_eq_add] at hs
  have hle := tile.val.lowerLeft_le_of_mem tile.property hs
  simp only [Prod.fst_add, Prod.snd_add] at hle
  unfold RowNonneg
  omega

theorem standardSources_rowCentred (parents : TileParents) (parity : Parity) (slot : Fin 6)
    (hodd : RowCentred parents.odd) (heven : RowCentred parents.even) :
    RowCentred (standardSources parents parity slot) := by
  cases parity <;> fin_cases slot <;> simp [standardSources] <;> assumption

theorem placed_mem_iff (jet : TileJet) (donor : NonemptyTile) (s : FLatticePaper.Site) :
    s ∈ (jet.place donor).val.sites ↔ s - jet.1 ∈ donor.val.sites :=
  mem_place_sites donor.val jet.1 jet.2 s

theorem copy_rowNonneg (parents : TileParents) (word : Word) (parity : Parity)
    (hodd : RowCentred parents.odd) (heven : RowCentred parents.even) (slot : Fin 6)
    {s : FLatticePaper.Site} (hs : s ∈ (ordinaryStandardCopy parents word parity slot).val.sites) :
    RowNonneg s := by
  have hdonor := standardSources_rowCentred parents parity slot hodd heven
  have hmem : s - (standardJets word parity slot).1 ∈ (standardSources parents parity slot).val.sites :=
    (placed_mem_iff _ _ s).mp hs
  have h := rowNonneg_add (hdonor.2 _ hmem) (standardJets_rowNonneg word parity slot)
  rwa [sub_add_cancel] at h

theorem copy_zero_mem (parents : TileParents) (word : Word) (parity : Parity)
    (hodd : RowCentred parents.odd) (heven : RowCentred parents.even) (slot : Fin 6)
    (hslot : (standardJets word parity slot).1 = 0) :
    (0 : FLatticePaper.Site) ∈ (ordinaryStandardCopy parents word parity slot).val.sites := by
  have hdonor := standardSources_rowCentred parents parity slot hodd heven
  apply (placed_mem_iff _ _ 0).mpr
  rw [hslot, sub_zero]
  exact hdonor.1

/-- The raw assembly of an ordinary standard schedule has its lower-left site at the origin. -/
theorem ordinaryStandard_raw_origin (parents : TileParents) (word : Word) (parity : Parity)
    (hodd : RowCentred parents.odd) (heven : RowCentred parents.even)
    (contacts : OrderedContacts (ordinaryStandardSchedule parents word parity).first.val.sites
      (ordinaryStandardSchedule parents word parity).copies) :
    ((ordinaryStandardSchedule parents word parity).raw contacts).val.lowerLeft
      ((ordinaryStandardSchedule parents word parity).raw contacts).property = 0 := by
  have hsites := ordinaryStandard_raw_sites parents word parity contacts
  have hzeroMem : (0 : FLatticePaper.Site) ∈
      ((ordinaryStandardSchedule parents word parity).raw contacts).val.sites := by
    rw [hsites]
    obtain ⟨slot, hslot⟩ := standardJets_zero_slot word parity
    unfold ordinaryStandardSites
    exact Finset.mem_biUnion.mpr ⟨slot, Finset.mem_univ _, copy_zero_mem parents word parity hodd heven slot hslot⟩
  have hmin : ∀ site ∈ ((ordinaryStandardSchedule parents word parity).raw contacts).val.sites,
      (0 : FLatticePaper.Site).2 ≤ site.2 ∧ ((0 : FLatticePaper.Site).2 = site.2 → (0 : FLatticePaper.Site).1 ≤ site.1) := by
    intro site hs
    rw [hsites] at hs
    unfold ordinaryStandardSites at hs
    obtain ⟨slot, -, hslot⟩ := Finset.mem_biUnion.mp hs
    have h := copy_rowNonneg parents word parity hodd heven slot hslot
    unfold RowNonneg at h
    simp only [Prod.fst_zero, Prod.snd_zero]
    omega
  exact lowerLeft_eq_of_minimal _ _ hzeroMem hmin

/-- The lower-left site of the trim of a tile is the lower-left site of the tile minus its box origin. -/
theorem trim_lowerLeft_eq (tile : HeightTile FLatticePaper.Site) (hne : tile.sites.Nonempty) :
    (tile.trim hne).lowerLeft (tile.trim_sites_nonempty hne) = tile.lowerLeft hne - tile.boxOrigin hne := by
  apply lowerLeft_eq_of_minimal
  · change tile.lowerLeft hne - tile.boxOrigin hne ∈ (tile.place (-tile.boxOrigin hne) 0).sites
    rw [mem_place_sites, sub_neg_eq_add, sub_add_cancel]
    exact tile.lowerLeft_mem hne
  · intro site hmem
    change site ∈ (tile.place (-tile.boxOrigin hne) 0).sites at hmem
    rw [mem_place_sites, sub_neg_eq_add] at hmem
    have h := tile.lowerLeft_le_of_mem hne hmem
    simp only [Prod.fst_add, Prod.snd_add] at h
    simp only [Prod.fst_sub, Prod.snd_sub]
    omega

theorem lowerLeft_eq_of_trim {E T : HeightTile FLatticePaper.Site} {hE : E.sites.Nonempty}
    {hT : T.sites.Nonempty} (h : E = T.trim hT) :
    E.lowerLeft hE = T.lowerLeft hT - T.boxOrigin hT := by
  subst h
  exact trim_lowerLeft_eq T hT

/-- The chart condition holds for every ordinary standard output of a centred schedule: the lower-left site of the
output plus the box origin of the raw assembly is zero. -/
theorem ordinaryStandard_chart_zero (parents : TileParents) (word : Word) (parity : Parity) (context : String)
    (hodd : RowCentred parents.odd) (heven : RowCentred parents.even)
    (contacts : OrderedContacts (ordinaryStandardSchedule parents word parity).first.val.sites
      (ordinaryStandardSchedule parents word parity).copies) (result : NonemptyTile)
    (hres : (ordinaryStandardSchedule parents word parity).eval .tile context = .ok result) :
    result.val.lowerLeft result.property +
      ((ordinaryStandardSchedule parents word parity).raw contacts).val.boxOrigin
        ((ordinaryStandardSchedule parents word parity).raw contacts).property = 0 := by
  obtain ⟨_, hfin⟩ := (PlacedSchedule.eval_ok_iff _ _ _ _).mp hres
  have hE : result.val = ((ordinaryStandardSchedule parents word parity).raw contacts).val.trim
      ((ordinaryStandardSchedule parents word parity).raw contacts).property := by
    rw [← hfin]
    rfl
  have hL := ordinaryStandard_raw_origin parents word parity hodd heven contacts
  rw [lowerLeft_eq_of_trim hE, hL]
  simp

/-- The output agreement with the plane field, with the chart condition discharged: for centred donors the output's
register `llCenter` agrees with `planeTarget word parity` up to one constant. -/
theorem ordinaryStandard_identifies_centred (parents : TileParents) (word : Word) (parity : Parity)
    (context : String) (hodd : RowCentred parents.odd) (heven : RowCentred parents.even)
    (hnom : ∀ slot : Fin 6,
      ∃ g : ℤ, (ordinaryStandardCopy parents word parity slot).val.Agrees (planeTarget word parity) g)
    (hcon : HeightTile.OrderedContacts (ordinaryStandardSchedule parents word parity).first.val.sites
      (ordinaryStandardSchedule parents word parity).copies) :
    ∃ result, (ordinaryStandardSchedule parents word parity).eval .tile context = .ok result ∧
      ∃ g : ℤ, (result.val.llCenter result.property).Agrees (planeTarget word parity) g :=
  ordinaryStandard_identifies_register parents word parity context hnom hcon
    (fun result hres => ordinaryStandard_chart_zero parents word parity context hodd heven hcon result hres)

/-- The native parents of every step are centred, because `TileRegisters.parentsFor` llCenters its registers. -/
theorem parentsFor_rowCentred (registers : TileRegisters) (digit : Digit) :
    RowCentred (registers.parentsFor digit).odd ∧ RowCentred (registers.parentsFor digit).even := by
  unfold TileRegisters.parentsFor
  constructor <;> dsimp only <;> split <;> apply NonemptyTile.llCenter_rowCentred

/-- The native ordinary standard output of a step, with the parents the native constructor uses
(`TileRegisters.parentsFor`): the chart condition is discharged, leaving only the nominal and contact hypotheses. -/
theorem ordinaryStandard_identifies_native (registers : TileRegisters) (digit : Digit) (word : Word) (parity : Parity)
    (context : String)
    (hnom : ∀ slot : Fin 6,
      ∃ g : ℤ, (ordinaryStandardCopy (registers.parentsFor digit) word parity slot).val.Agrees
        (planeTarget word parity) g)
    (hcon : HeightTile.OrderedContacts
      (ordinaryStandardSchedule (registers.parentsFor digit) word parity).first.val.sites
      (ordinaryStandardSchedule (registers.parentsFor digit) word parity).copies) :
    ∃ result, (ordinaryStandardSchedule (registers.parentsFor digit) word parity).eval .tile context = .ok result ∧
      ∃ g : ℤ, (result.val.llCenter result.property).Agrees (planeTarget word parity) g :=
  ordinaryStandard_identifies_centred (registers.parentsFor digit) word parity context
    (parentsFor_rowCentred registers digit).1 (parentsFor_rowCentred registers digit).2 hnom hcon

end FLatticePaper.Construction
