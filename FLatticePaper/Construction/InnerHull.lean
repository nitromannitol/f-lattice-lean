import FLatticePaper.Construction.OrdinaryOddAltSources

/-! Part III: the equivalence between covering a native standard's deck and occupying its inner hull.

The note `STANDARD_NATIVE_COVER_CORE_AND_INNER_HULL_EQUIVALENCE` (19 November 2026) states, for an actual standard
`D` with outer hull `H`, unique core `J` and inner hull `I`:

    D + Λ = Z²   iff   J ⊆ D   iff   I ⊆ D.

Its definitions of `H`, `J` and `I` are in a document that is not in the archive, so they are not in Lean. This file
proves the equivalence from the four properties the note uses, each stated as a hypothesis:

* (I) `I` covers the deck (`CoversBy Λ I`): the covering subset of the sufficiency argument;
* (J) each `j ∈ J` is the only point of `H` in its class (`hJ`): the necessity of `J`, using `D ⊆ H`;
* (H) the standard's support lies in its outer hull (`D ⊆ H`);
* (R) retention: every point of `I` outside `J` lies in the actual standard `D` (`hret`). The note derives this from
  the ambiguity strips and the basic atoms of the constructor; that derivation is not formalized here.

The period set `Λ` is only assumed symmetric. For a `PeriodDeck` it is `deck.span`, which is symmetric. -/

namespace FLatticePaper.Construction

open Farey

/-- `S` covers every site modulo the period set `Λ`. -/
def CoversBy (Λ S : Set Site) : Prop :=
  ∀ x : Site, ∃ s ∈ S, x - s ∈ Λ

theorem deck_span_neg (deck : PeriodDeck) : ∀ x ∈ deck.span, -x ∈ deck.span := by
  rintro x ⟨k, k', rfl⟩
  exact ⟨-k, -k', by ext <;> simp [PeriodDeck.combine] <;> ring⟩

theorem coversBy_iff_covers (deck : PeriodDeck) (D : Finset Site) :
    CoversBy deck.span (D : Set Site) ↔ PeriodDeck.Covers deck D := by
  unfold CoversBy PeriodDeck.Covers
  simp

/-- The equivalence of the note: for an actual standard `D ⊆ H`, covering the deck, the core `J ⊆ D` and the inner
hull `I ⊆ D` are equivalent. -/
theorem inner_hull_equivalence {Λ : Set Site} (hneg : ∀ x ∈ Λ, -x ∈ Λ)
    {H I J D : Set Site} (hI : CoversBy Λ I) (hJ : ∀ j ∈ J, ∀ h ∈ H, h - j ∈ Λ → h = j)
    (hDH : D ⊆ H) (hret : ∀ i ∈ I, i ∈ J ∨ i ∈ D) :
    (CoversBy Λ D ↔ J ⊆ D) ∧ (CoversBy Λ D ↔ I ⊆ D) := by
  have hJD : CoversBy Λ D → J ⊆ D := by
    intro hD j hj
    obtain ⟨d, hdD, hjd⟩ := hD j
    have hdj : d - j ∈ Λ := by
      have h := hneg _ hjd
      rwa [neg_sub] at h
    have hdj' : d = j := hJ j hj d (hDH hdD) hdj
    rw [← hdj']
    exact hdD
  have hIofJ : J ⊆ D → I ⊆ D := fun hJs i hi => (hret i hi).elim (fun h => hJs h) id
  have hcovI : I ⊆ D → CoversBy Λ D := fun hIs x => by
    obtain ⟨i, hi, hxi⟩ := hI x
    exact ⟨i, hIs hi, hxi⟩
  have hcovJ : J ⊆ D → CoversBy Λ D := fun hJs => hcovI (hIofJ hJs)
  exact ⟨⟨hJD, hcovJ⟩, ⟨fun hD => hIofJ (hJD hD), hcovI⟩⟩

/-- The core lies in the inner hull, when the inner hull covers and lies in the outer hull. -/
theorem core_subset_inner {Λ : Set Site} (hneg : ∀ x ∈ Λ, -x ∈ Λ) {H I J : Set Site}
    (hI : CoversBy Λ I) (hIH : I ⊆ H) (hJ : ∀ j ∈ J, ∀ h ∈ H, h - j ∈ Λ → h = j) : J ⊆ I := by
  intro j hj
  obtain ⟨i, hi, hji⟩ := hI j
  have hij : i - j ∈ Λ := by
    have h := hneg _ hji
    rwa [neg_sub] at h
  have hie : i = j := hJ j hj i (hIH hi) hij
  rw [← hie]
  exact hi

/-- Occupancy of the inner hull, read from covering: a standard whose deck is covered occupies its inner hull. -/
theorem inner_hull_occupied {Λ : Set Site} (hneg : ∀ x ∈ Λ, -x ∈ Λ)
    {H I J D : Set Site} (hI : CoversBy Λ I) (hJ : ∀ j ∈ J, ∀ h ∈ H, h - j ∈ Λ → h = j)
    (hDH : D ⊆ H) (hret : ∀ i ∈ I, i ∈ J ∨ i ∈ D) (hcov : CoversBy Λ D) : I ⊆ D :=
  ((inner_hull_equivalence hneg hI hJ hDH hret).2).1 hcov

/-- Step 2 interface: a translate of an occupied inner hull hits every site that differs from the translated hull
point by a period. This is what the chart covering of the reduced sources consumes. -/
theorem hits_of_inner_hull (deck : PeriodDeck) (R : NonemptyTile) (o : Site) {I : Set Site}
    (hIR : ∀ i ∈ I, i ∈ R.val.sites) {x i : Site} (hi : i ∈ I) (hx : x - (i + o) ∈ deck.span) :
    Hits deck (R.place o 0) x :=
  ⟨i + o, (HeightTile.mem_place_sites R.val o 0 (i + o)).mpr
    (by rw [add_sub_cancel_right]; exact hIR i hi), hx⟩

end FLatticePaper.Construction
