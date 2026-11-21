import FLatticePaper.Construction.NativeSchedules
import FLatticePaper.Construction.NativeCoverage
import Mathlib.Tactic.FinCases

/-! Step 1 of the ordinary odd alternate cover (hand theorem, 20 November 2026): the seven placed sources of the odd
alternate schedule, for a word `beforePush ++ [digit]` with `digit ≠ 2` and phase `1`, are reduced modulo the native
periods `U = 2p + 2e`, `V = w + f` to the six displayed translates of `P`, `Q`, `D` used by the hand proof. The
covering property is invariant under translations by the period lattice, so the reduced list covers exactly when the
seven sources cover. -/

namespace FLatticePaper.Construction

open Farey

/-- The kernel site `(d, n)` of a fraction `n/d`, the offset of `kernelJet`. -/
def kernelSite (fraction : Fraction) : Site := (fraction.den, fraction.num)

/-- The transverse site of a fraction, the offset of `transverseJet`. -/
def transverseSite (fraction : Fraction) : Site := (fraction.num - fraction.den, fraction.num + fraction.den)

theorem kernelJet_fst (fraction : Fraction) : (kernelJet fraction).1 = kernelSite fraction := rfl

theorem transverseJet_fst (fraction : Fraction) : (transverseJet fraction).1 = transverseSite fraction := rfl

/-- The native periods `U = 2p + 2e` and `V = w + f` of an ordinary odd alternate, with `p` the odd standard parent,
`e` the even standard parent, `w` the odd transverse site and `f` the even transverse site. -/
def oddAltDeck (parents : Parents) : PeriodDeck :=
  ⟨2 • kernelSite parents.odd + 2 • kernelSite parents.even,
    transverseSite parents.odd + transverseSite parents.even⟩

/-- A placed source covers the classes it hits: some site of the source, moved by its offset, differs from the target
site by a period. -/
def Hits (deck : PeriodDeck) (tile : NonemptyTile) (site : Site) : Prop :=
  ∃ rep ∈ tile.val.sites, site - rep ∈ deck.span

/-- A list of sources covers the deck. -/
def SourcesCover (deck : PeriodDeck) (sources : List NonemptyTile) : Prop :=
  ∀ site, ∃ tile ∈ sources, Hits deck tile site

theorem span_mem_iff (deck : PeriodDeck) (w : Site) :
    w ∈ deck.span ↔ ∃ k k' : ℤ, w = deck.combine k k' := Iff.rfl

theorem span_add_mem (deck : PeriodDeck) {u v : Site} (hu : u ∈ deck.span) (hv : v ∈ deck.span) :
    u + v ∈ deck.span := by
  obtain ⟨a, b, rfl⟩ := hu
  obtain ⟨c, d, rfl⟩ := hv
  exact ⟨a + c, b + d, by simp only [PeriodDeck.combine, Prod.mk_add_mk]; ext <;> simp <;> ring⟩

theorem span_sub_mem (deck : PeriodDeck) {u v : Site} (hu : u ∈ deck.span) (hv : v ∈ deck.span) :
    u - v ∈ deck.span := by
  obtain ⟨a, b, rfl⟩ := hu
  obtain ⟨c, d, rfl⟩ := hv
  exact ⟨a - c, b - d, by simp only [PeriodDeck.combine]; ext <;> simp <;> ring⟩

/-- The sites of a source placed at offset `t` are the shifted sites of its donor. -/
theorem hits_place_iff (deck : PeriodDeck) (tile : NonemptyTile) (t s : Site) (x : Site) :
    Hits deck (tile.place t s) x ↔ ∃ d ∈ tile.val.sites, x - (d + t) ∈ deck.span := by
  constructor
  · rintro ⟨rep, hrep, hx⟩
    have hd : rep - t ∈ tile.val.sites := (HeightTile.mem_place_sites tile.val t s rep).mp hrep
    refine ⟨rep - t, hd, ?_⟩
    simpa only [sub_add_cancel] using hx
  · rintro ⟨d, hd, hx⟩
    exact ⟨d + t, (HeightTile.mem_place_sites tile.val t s (d + t)).mpr (by simpa using hd), hx⟩

/-- Translating a source by an offset that differs from another by a period does not change what it hits. -/
theorem hits_place_congr (deck : PeriodDeck) (tile : NonemptyTile) {t t' s s' : Site}
    (h : t - t' ∈ deck.span) (x : Site) :
    Hits deck (tile.place t s) x ↔ Hits deck (tile.place t' s') x := by
  rw [hits_place_iff, hits_place_iff]
  constructor
  · rintro ⟨d, hd, hx⟩
    refine ⟨d, hd, ?_⟩
    have : x - (d + t') = (x - (d + t)) + (t - t') := by abel
    rw [this]
    exact span_add_mem deck hx h
  · rintro ⟨d, hd, hx⟩
    refine ⟨d, hd, ?_⟩
    have : x - (d + t) = (x - (d + t')) - (t - t') := by abel
    rw [this]
    exact span_sub_mem deck hx h

theorem ordinaryAlternateSchedule_odd_first (parents : TileParents) (beforePush : Word) (digit : Digit) :
    (ordinaryAlternateSchedule parents beforePush digit .odd).first =
      (alternateJets (beforePush ++ [digit]) .odd 0).place parents.even := rfl

theorem ordinaryAlternateSchedule_odd_rest (parents : TileParents) (beforePush : Word) (digit : Digit) :
    (ordinaryAlternateSchedule parents beforePush digit .odd).rest =
      [(seventhAlternateJet beforePush digit .odd).place
          (restoreAlternate (beforePush ++ [digit]) .even parents.alternateEven),
        (alternateJets (beforePush ++ [digit]) .odd 2).place parents.odd,
        (alternateJets (beforePush ++ [digit]) .odd 3).place parents.odd,
        (alternateJets (beforePush ++ [digit]) .odd 1).place parents.even,
        (alternateJets (beforePush ++ [digit]) .odd 4).place parents.odd,
        (alternateJets (beforePush ++ [digit]) .odd 5).place parents.odd] := rfl

/-- The six offsets of the odd alternate jets in phase `1`, written with the parents of the word. -/
def oddAltOffset (word : Word) : Fin 6 → Site :=
  let po := (parentsAt word).odd
  let pe := (parentsAt word).even
  ![2 • kernelSite po, 2 • transverseSite po - kernelSite pe, 0,
    -kernelSite pe + transverseSite po, kernelSite pe + transverseSite pe,
    (kernelSite pe + transverseSite pe) + (-kernelSite pe + transverseSite po)]

theorem alternateJets_odd_fst (word : Word) (hphase : phase word ≠ 0) (i : Fin 6) :
    (alternateJets word .odd i).1 = oddAltOffset word i := by
  unfold alternateJets
  dsimp only
  rw [if_neg hphase]
  change ((![2 • kernelJet (parentsAt word).odd, 2 • transverseJet (parentsAt word).odd -
      kernelJet (parentsAt word).even, (0 : TileJet), (0 : TileJet) + (-kernelJet (parentsAt word).even +
      transverseJet (parentsAt word).odd), kernelJet (parentsAt word).even + transverseJet (parentsAt word).even,
      (kernelJet (parentsAt word).even + transverseJet (parentsAt word).even) +
        (-kernelJet (parentsAt word).even + transverseJet (parentsAt word).odd)] : Fin 6 → TileJet) i).1 = _
  fin_cases i <;> simp [oddAltOffset, kernelJet_fst, transverseJet_fst, kernelSite, transverseSite,
    Prod.fst_add, Prod.fst_sub, Prod.fst_neg, Prod.smul_fst]

/-- The seventh star of the odd alternate at phase `1`, for a last digit `one` or `three`: `w + 2p - e`. -/
theorem seventh_odd_fst (beforePush : Word) (digit : Digit) (hdigit : digit ≠ .two)
    (hphase : phase (beforePush ++ [digit]) ≠ 0) :
    (seventhAlternateJet beforePush digit .odd).1 =
      transverseSite (parentsAt (beforePush ++ [digit])).odd + 2 • kernelSite (parentsAt (beforePush ++ [digit])).odd
        - kernelSite (parentsAt (beforePush ++ [digit])).even := by
  unfold seventhAlternateJet
  dsimp only
  simp only [hphase, decide_false]
  cases digit
  · simp [kernelSite, transverseSite, kernelJet_fst, transverseJet_fst]
  · exact absurd rfl hdigit
  · simp [kernelSite, transverseSite, kernelJet_fst, transverseJet_fst]

/-- The reduced six-plus-seventh list of the hand proof: each source is translated by a period vector from its
placement, to the displayed translates of `P`, `Q` and `D`. The order matches the schedule. -/
def oddAltReduced (tp : TileParents) (word : Word) : List NonemptyTile :=
  let po := (parentsAt word).odd
  let pe := (parentsAt word).even
  [tp.even.place (-(2 • kernelSite pe)) 0,
    (restoreAlternate word .even tp.alternateEven).place
      (2 • kernelSite po - kernelSite pe - transverseSite pe) 0,
    tp.odd.place 0 0,
    tp.odd.place (-kernelSite pe - transverseSite pe) 0,
    tp.even.place (-kernelSite pe - 2 • transverseSite pe) 0,
    tp.odd.place (-(2 • kernelSite po) - kernelSite pe - transverseSite po) 0,
    tp.odd.place 0 0]

theorem mem_span_of (deck : PeriodDeck) (k k' : ℤ) (w : Site) (h : w = deck.combine k k') : w ∈ deck.span :=
  ⟨k, k', h⟩

/-- Seven-source covering as a statement about the seven hits, in the schedule order. -/
theorem sourcesCover_seven_iff (deck : PeriodDeck) (a b c d e f g : NonemptyTile) :
    SourcesCover deck [a, b, c, d, e, f, g] ↔
      ∀ x, Hits deck a x ∨ Hits deck b x ∨ Hits deck c x ∨ Hits deck d x ∨ Hits deck e x ∨ Hits deck f x ∨
        Hits deck g x := by
  constructor
  · intro h x
    obtain ⟨tile, htile, hx⟩ := h x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at htile
    rcases htile with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [hx]
  · intro h x
    rcases h x with hx | hx | hx | hx | hx | hx | hx
    · exact ⟨a, by simp, hx⟩
    · exact ⟨b, by simp, hx⟩
    · exact ⟨c, by simp, hx⟩
    · exact ⟨d, by simp, hx⟩
    · exact ⟨e, by simp, hx⟩
    · exact ⟨f, by simp, hx⟩
    · exact ⟨g, by simp, hx⟩

/-- Step 1 of the ordinary odd alternate cover: for a word whose last digit is `one` or `three` and whose phase is
`1`, the seven placed sources cover the odd alternate's deck exactly when their reduced translates do. -/
theorem oddAlt_sourcesCover_iff_reduced (tp : TileParents) (beforePush : Word) (digit : Digit)
    (hdigit : digit ≠ .two) (hphase : phase (beforePush ++ [digit]) ≠ 0) :
    SourcesCover (oddAltDeck (parentsAt (beforePush ++ [digit])))
        ((ordinaryAlternateSchedule tp beforePush digit .odd).first ::
          (ordinaryAlternateSchedule tp beforePush digit .odd).rest) ↔
      SourcesCover (oddAltDeck (parentsAt (beforePush ++ [digit])))
        (oddAltReduced tp (beforePush ++ [digit])) := by
  rw [ordinaryAlternateSchedule_odd_first, ordinaryAlternateSchedule_odd_rest]
  rw [sourcesCover_seven_iff]
  unfold oddAltReduced
  simp only []
  rw [sourcesCover_seven_iff]
  set word := beforePush ++ [digit] with hword
  set deck := oddAltDeck (parentsAt word) with hdeck
  have hoff : ∀ i : Fin 6, (alternateJets word .odd i).1 = oddAltOffset word i :=
    fun i => alternateJets_odd_fst word hphase i
  have hs : (seventhAlternateJet beforePush digit .odd).1 =
      transverseSite (parentsAt word).odd + 2 • kernelSite (parentsAt word).odd
        - kernelSite (parentsAt word).even := seventh_odd_fst beforePush digit hdigit hphase
  have hU : deck.kernel = 2 • kernelSite (parentsAt word).odd + 2 • kernelSite (parentsAt word).even := rfl
  have hV : deck.transverse = transverseSite (parentsAt word).odd + transverseSite (parentsAt word).even := rfl
  -- the six placed offsets, and the seventh, each differ from their reduced translate by a period
  have m0 : (alternateJets word .odd 0).1 - (-(2 • kernelSite (parentsAt word).even)) ∈ deck.span := by
    rw [hoff]
    exact mem_span_of deck 1 0 _ (by ext <;> simp [hU, hV, PeriodDeck.combine, oddAltOffset])
  have m7 : (seventhAlternateJet beforePush digit .odd).1 -
      (2 • kernelSite (parentsAt word).odd - kernelSite (parentsAt word).even -
        transverseSite (parentsAt word).even) ∈ deck.span := by
    rw [hs]
    exact mem_span_of deck 0 1 _ (by ext <;> simp [hU, hV, PeriodDeck.combine] <;> ring)
  have m2 : (alternateJets word .odd 2).1 - 0 ∈ deck.span := by
    rw [hoff]
    exact mem_span_of deck 0 0 _ (by ext <;> simp [hU, hV, PeriodDeck.combine, oddAltOffset])
  have m3 : (alternateJets word .odd 3).1 - (-kernelSite (parentsAt word).even - transverseSite (parentsAt word).even)
      ∈ deck.span := by
    rw [hoff]
    exact mem_span_of deck 0 1 _ (by ext <;> simp [hU, hV, PeriodDeck.combine, oddAltOffset])
  have m1 : (alternateJets word .odd 1).1 -
      (-kernelSite (parentsAt word).even - 2 • transverseSite (parentsAt word).even) ∈ deck.span := by
    rw [hoff]
    exact mem_span_of deck 0 2 _ (by ext <;> simp [hU, hV, PeriodDeck.combine, oddAltOffset] <;> ring)
  have m4 : (alternateJets word .odd 4).1 -
      (-(2 • kernelSite (parentsAt word).odd) - kernelSite (parentsAt word).even - transverseSite (parentsAt word).odd)
      ∈ deck.span := by
    rw [hoff]
    exact mem_span_of deck 1 1 _ (by ext <;> simp [hU, hV, PeriodDeck.combine, oddAltOffset] <;> ring)
  have m5 : (alternateJets word .odd 5).1 - 0 ∈ deck.span := by
    rw [hoff]
    exact mem_span_of deck 0 1 _ (by ext <;> simp [hU, hV, PeriodDeck.combine, oddAltOffset] <;> ring)
  refine forall_congr' fun x => ?_
  refine or_congr ?_ (or_congr ?_ (or_congr ?_ (or_congr ?_ (or_congr ?_ (or_congr ?_ ?_)))))
  · exact hits_place_congr deck tp.even m0 x
  · exact hits_place_congr deck (restoreAlternate word .even tp.alternateEven) m7 x
  · exact hits_place_congr deck tp.odd m2 x
  · exact hits_place_congr deck tp.odd m3 x
  · exact hits_place_congr deck tp.even m1 x
  · exact hits_place_congr deck tp.odd m4 x
  · exact hits_place_congr deck tp.odd m5 x

/-- Phase-zero offsets of the six odd alternate jets: `0, 2p+2w+e, e, 2e+w, f, e+w+f`. -/
def oddAltOffset0 (word : Word) : Fin 6 → Site :=
  let po := (parentsAt word).odd
  let pe := (parentsAt word).even
  ![0, 2 • kernelSite po + 2 • transverseSite po + kernelSite pe, kernelSite pe,
    kernelSite pe + (kernelSite pe + transverseSite po), transverseSite pe,
    transverseSite pe + (kernelSite pe + transverseSite po)]

theorem alternateJets_odd_fst_zero (word : Word) (hphase : phase word = 0) (i : Fin 6) :
    (alternateJets word .odd i).1 = oddAltOffset0 word i := by
  unfold alternateJets
  dsimp only
  rw [if_pos hphase]
  change ((![(0 : TileJet),
      2 • kernelJet (parentsAt word).odd + 2 • transverseJet (parentsAt word).odd +
        kernelJet (parentsAt word).even,
      kernelJet (parentsAt word).even,
      kernelJet (parentsAt word).even + (kernelJet (parentsAt word).even + transverseJet (parentsAt word).odd),
      transverseJet (parentsAt word).even,
      transverseJet (parentsAt word).even +
        (kernelJet (parentsAt word).even + transverseJet (parentsAt word).odd)] : Fin 6 → TileJet) i).1 = _
  fin_cases i <;> simp [oddAltOffset0, kernelJet_fst, transverseJet_fst, kernelSite, transverseSite,
    Prod.fst_add, Prod.smul_fst]

/-- The phase-zero seventh source of the odd alternate sits at `e + w`. -/
theorem seventh_odd_fst_zero (beforePush : Word) (digit : Digit) (hphase : phase (beforePush ++ [digit]) = 0) :
    (seventhAlternateJet beforePush digit .odd).1 =
      kernelSite (parentsAt (beforePush ++ [digit])).even + transverseSite (parentsAt (beforePush ++ [digit])).odd := by
  unfold seventhAlternateJet
  dsimp only
  simp [hphase, kernelJet_fst, transverseJet_fst, kernelSite, transverseSite]

/-- The reduced seven sources of the phase-zero odd alternate, in schedule order. Each one is a period translate
(`U = 2p+2e`, `V = w+f`) of the matching literal source, and the list is the hand proof's `E0` (with `P` at `e`
listed twice, as the literal schedule does). -/
def oddAltReduced0 (tp : TileParents) (word : Word) : List NonemptyTile :=
  let po := (parentsAt word).odd
  let pe := (parentsAt word).even
  [tp.even.place 0 0,
    (restoreAlternate word .even tp.alternateEven).place (kernelSite pe - transverseSite pe) 0,
    tp.odd.place (kernelSite pe) 0,
    tp.odd.place (-(2 • kernelSite po) - transverseSite pe) 0,
    tp.even.place (-kernelSite pe - 2 • transverseSite pe) 0,
    tp.odd.place (-transverseSite po) 0,
    tp.odd.place (kernelSite pe) 0]

/-- Step 1 of the phase-zero case: the literal seven sources cover the odd alternate's deck exactly when the reduced
list does. -/
theorem oddAlt_sourcesCover_iff_reduced0 (tp : TileParents) (beforePush : Word) (digit : Digit)
    (hphase : phase (beforePush ++ [digit]) = 0) :
    SourcesCover (oddAltDeck (parentsAt (beforePush ++ [digit])))
        ((ordinaryAlternateSchedule tp beforePush digit .odd).first ::
          (ordinaryAlternateSchedule tp beforePush digit .odd).rest) ↔
      SourcesCover (oddAltDeck (parentsAt (beforePush ++ [digit])))
        (oddAltReduced0 tp (beforePush ++ [digit])) := by
  rw [ordinaryAlternateSchedule_odd_first, ordinaryAlternateSchedule_odd_rest]
  rw [sourcesCover_seven_iff]
  unfold oddAltReduced0
  simp only []
  rw [sourcesCover_seven_iff]
  set word := beforePush ++ [digit] with hword
  set deck := oddAltDeck (parentsAt word) with hdeck
  have hU : deck.kernel = 2 • kernelSite (parentsAt word).odd + 2 • kernelSite (parentsAt word).even := rfl
  have hV : deck.transverse = transverseSite (parentsAt word).odd + transverseSite (parentsAt word).even := rfl
  have hoff : ∀ i : Fin 6, (alternateJets word .odd i).1 = oddAltOffset0 word i :=
    fun i => alternateJets_odd_fst_zero word hphase i
  have hs : (seventhAlternateJet beforePush digit .odd).1 =
      kernelSite (parentsAt word).even + transverseSite (parentsAt word).odd :=
    seventh_odd_fst_zero beforePush digit hphase
  have m0 : (alternateJets word .odd 0).1 - 0 ∈ deck.span := by
    rw [hoff]
    exact mem_span_of deck 0 0 _ (by ext <;> simp [oddAltOffset0, hU, hV, PeriodDeck.combine])
  have m1 : (seventhAlternateJet beforePush digit .odd).1 -
      (kernelSite (parentsAt word).even - transverseSite (parentsAt word).even) ∈ deck.span := by
    rw [hs]
    exact mem_span_of deck 0 1 _ (by ext <;> simp [hU, hV, PeriodDeck.combine])
  have m2 : (alternateJets word .odd 2).1 - kernelSite (parentsAt word).even ∈ deck.span := by
    rw [hoff]
    exact mem_span_of deck 0 0 _ (by ext <;> simp [oddAltOffset0, hU, hV, PeriodDeck.combine])
  have m3 : (alternateJets word .odd 3).1 -
      (-(2 • kernelSite (parentsAt word).odd) - transverseSite (parentsAt word).even) ∈ deck.span := by
    rw [hoff]
    exact mem_span_of deck 1 1 _ (by ext <;> simp [oddAltOffset0, hU, hV, PeriodDeck.combine] <;> ring)
  have m4 : (alternateJets word .odd 1).1 -
      (-kernelSite (parentsAt word).even - 2 • transverseSite (parentsAt word).even) ∈ deck.span := by
    rw [hoff]
    exact mem_span_of deck 1 2 _ (by ext <;> simp [oddAltOffset0, hU, hV, PeriodDeck.combine] <;> ring)
  have m5 : (alternateJets word .odd 4).1 - -transverseSite (parentsAt word).odd ∈ deck.span := by
    rw [hoff]
    exact mem_span_of deck 0 1 _ (by ext <;> simp [oddAltOffset0, hU, hV, PeriodDeck.combine] <;> ring)
  have m6 : (alternateJets word .odd 5).1 - kernelSite (parentsAt word).even ∈ deck.span := by
    rw [hoff]
    exact mem_span_of deck 0 1 _ (by ext <;> simp [oddAltOffset0, hU, hV, PeriodDeck.combine] <;> ring)
  refine forall_congr' fun x => ?_
  refine or_congr ?_ (or_congr ?_ (or_congr ?_ (or_congr ?_ (or_congr ?_ (or_congr ?_ ?_)))))
  · exact hits_place_congr deck tp.even m0 x
  · exact hits_place_congr deck (restoreAlternate word .even tp.alternateEven) m1 x
  · exact hits_place_congr deck tp.odd m2 x
  · exact hits_place_congr deck tp.odd m3 x
  · exact hits_place_congr deck tp.even m4 x
  · exact hits_place_congr deck tp.odd m5 x
  · exact hits_place_congr deck tp.odd m6 x

end FLatticePaper.Construction
