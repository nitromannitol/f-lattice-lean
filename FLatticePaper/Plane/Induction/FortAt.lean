import FLatticePaper.Plane.BellmanRank

/-! # The fort condition at a set of sites

`IsIncomingFort F S` (BellmanRank) asks, at every site of `S`, for an input in `S` at a black site and both inputs at a white site.
The passage and fan arguments use this condition only at the sites where `N` holds: at the nonfree sites (the passage lemmas), or
at the open-rectangle sites (the fan lemmas, which are the strict-interior sites). `FortAt N F S` is that weaker condition.

* `IsIncomingFort F S` gives `FortAt N F S` for every `N` (`fortAt_of_incoming`).
* The restricted fort gives `FortAt (Nonfree frame) F S` in `FortAtRestricted.lean` (`fortAt_nonfree_of_restricted`).
-/

namespace FLatticePaper

open Farey FLatticePaper

/-- The fort condition at the sites where `N` holds: a black such site keeps an input in `sites`, a white one keeps both. -/
def FortAt (N : Site → Prop) (F : Field) (sites : Set Site) : Prop :=
  ∀ site ∈ sites, N site →
    (laplacian F site = -1 ∧ (incomingNeg site ∈ sites ∨ incomingPos site ∈ sites)) ∨
      (laplacian F site = 0 ∧ incomingNeg site ∈ sites ∧ incomingPos site ∈ sites)

/-- The unrestricted fort condition gives the fort condition at any set of sites. -/
theorem fortAt_of_incoming {N : Site → Prop} {F : Field} {sites : Set Site}
    (h : IsIncomingFort F sites) : FortAt N F sites :=
  fun site hs _ => h site hs

/-- The fort condition at every site is the unrestricted fort condition. -/
theorem incoming_of_fortAt_all {F : Field} {sites : Set Site} (h : FortAt (fun _ => True) F sites) :
    IsIncomingFort F sites :=
  fun site hs => h site hs trivial

/-- Weakening the set of sites: the condition at `N` gives the condition at any smaller `N'`. -/
theorem FortAt.mono {N N' : Site → Prop} {F : Field} {sites : Set Site} (h : FortAt N F sites)
    (hN : ∀ site, N' site → N site) : FortAt N' F sites :=
  fun site hs hn' => h site hs (hN site hn')

end FLatticePaper
