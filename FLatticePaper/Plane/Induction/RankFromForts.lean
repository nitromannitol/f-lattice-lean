import FLatticePaper.Plane.AlternateMidpoint
import FLatticePaper.Plane.BellmanRank

/-! The rank S3 of the sewn standard field (task 19): the constrained burning rank with the slip permits, the
restricted forts that obstruct it, the local reconciliation with the Bellman rank, and the chain from a restricted
no-fort hypothesis to an unconstrained burning rank through `exists_burningRank_of_no_incomingFort`. -/

namespace FLatticePaper

open Farey

/-- The permits of S3: an input is permitted when its slip increment is nonpositive (`StarEstimates`). -/
def slipPermits (first second : Field) : Site → Site → Prop :=
  fun center input => slipIncrement first second center input ≤ 0

/-- A restricted fort: a set blocking the constrained burning. A site of Laplacian `-1` is blocked when one of its
inputs is in the set or is not permitted; a site of Laplacian `0` when both inputs are. -/
def IsRestrictedFort (field : Field) (permits : Site → Site → Prop) (sites : Set Site) : Prop :=
  ∀ site ∈ sites,
    (laplacian field site = -1 ∧
        ((incomingNeg site ∈ sites ∨ ¬ permits site (incomingNeg site)) ∨
          (incomingPos site ∈ sites ∨ ¬ permits site (incomingPos site)))) ∨
    (laplacian field site = 0 ∧
        (incomingNeg site ∈ sites ∨ ¬ permits site (incomingNeg site)) ∧
        (incomingPos site ∈ sites ∨ ¬ permits site (incomingPos site)))

/-- With every input permitted, the restricted forts are the incoming forts of `BellmanRank`. -/
theorem isRestrictedFort_iff_incomingFort (field : Field) (sites : Set Site) :
    IsRestrictedFort field (fun _ _ => True) sites ↔ IsIncomingFort field sites := by
  unfold IsRestrictedFort IsIncomingFort
  simp

/-- Every incoming fort is a restricted fort, whatever the permits: the permits only add obstructions. -/
theorem isRestrictedFort_of_incomingFort (field : Field) (permits : Site → Site → Prop) {sites : Set Site}
    (h : IsIncomingFort field sites) : IsRestrictedFort field permits sites := by
  intro site hsite
  rcases h site hsite with ⟨hl, hn | hp⟩ | ⟨hl, hn, hp⟩
  · exact Or.inl ⟨hl, Or.inl (Or.inl hn)⟩
  · exact Or.inl ⟨hl, Or.inr (Or.inl hp)⟩
  · exact Or.inr ⟨hl, Or.inl hn, Or.inl hp⟩

/-- The local reconciliation: at a site of Laplacian `-1` both inputs are permitted, and at a site of Laplacian `0`
one input is. Every constrained rank forces it. -/
def PermitLocal (field : Field) (permits : Site → Site → Prop) : Prop :=
  (∀ c, laplacian field c = -1 → permits c (incomingNeg c) ∧ permits c (incomingPos c)) ∧
  (∀ c, laplacian field c = 0 → permits c (incomingNeg c) ∨ permits c (incomingPos c))

theorem permitLocal_of_constrained {α : Type*} [LT α] {field : Field} {rank : Site → α}
    {permits : Site → Site → Prop} (h : IsConstrainedBurningRank field rank permits) :
    PermitLocal field permits := by
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · rcases h c with ⟨-, hn, hp⟩ | ⟨hl, -⟩
    · exact ⟨hn.1, hp.1⟩
    · rw [hl] at hc
      norm_num at hc
  · rcases h c with ⟨hl, -, -⟩ | ⟨-, hn | hp⟩
    · rw [hl] at hc
      norm_num at hc
    · exact Or.inl hn.1
    · exact Or.inr hp.1

/-- Reconciliation: a burning rank whose decreasing inputs are all permitted is a constrained burning rank. -/
theorem isConstrainedBurningRank_of_burning_permitted {α : Type*} [LinearOrder α] {field : Field}
    {rank : Site → α} {permits : Site → Site → Prop} (hbur : IsBurningRank field rank)
    (hlow : ∀ c i, Edge i c → rank i < rank c → permits c i) :
    IsConstrainedBurningRank field rank permits := by
  intro c
  rcases hbur c with ⟨hl, hn, hp⟩ | ⟨hl, hn | hp⟩
  · exact Or.inl ⟨hl, ⟨hlow c _ (Or.inl rfl) hn, hn⟩, ⟨hlow c _ (Or.inr rfl) hp, hp⟩⟩
  · exact Or.inr ⟨hl, Or.inl ⟨hlow c _ (Or.inl rfl) hn, hn⟩⟩
  · exact Or.inr ⟨hl, Or.inr ⟨hlow c _ (Or.inr rfl) hp, hp⟩⟩

/-- S3 from a burning rank whose decreasing inputs are permitted by the slip permits. -/
theorem constrainedRank_of_burning_slip {α : Type*} [LinearOrder α] {first second : Field} {rank : Site → α}
    (hbur : IsBurningRank first rank)
    (hlow : ∀ c i, Edge i c → rank i < rank c → slipPermits first second c i) :
    ∃ rank' : Site → α, IsConstrainedBurningRank first rank' (slipPermits first second) :=
  ⟨rank, isConstrainedBurningRank_of_burning_permitted hbur hlow⟩

/-- The non-existence hypothesis that the constrained rank needs: no nonempty restricted fort in any grade
half-space. -/
def RestrictedNoFort (field grade : Field) (permits : Site → Site → Prop) : Prop :=
  ∀ (level : ℤ) (fort : Set Site), fort.Nonempty → IsRestrictedFort field permits fort →
    (∀ site ∈ fort, level ≤ grade site) → False

/-- The restricted no-fort hypothesis implies the incoming no-fort hypothesis of `BellmanRank`. -/
theorem noIncomingFort_of_restricted {field grade : Field} (permits : Site → Site → Prop)
    (h : RestrictedNoFort field grade permits) :
    ∀ (level : ℤ) (fort : Set Site), fort.Nonempty → IsIncomingFort field fort →
      (∀ site ∈ fort, level ≤ grade site) → False :=
  fun level fort hne hfort hlevel =>
    h level fort hne (isRestrictedFort_of_incomingFort field permits hfort) hlevel

/-- From the restricted no-fort hypothesis, the Bellman construction gives an unconstrained burning rank, with the
same deck and grade hypotheses as `exists_burningRank_of_no_incomingFort`. The permits of the constrained rank are
not controlled by this rank: that is the remaining step. -/
theorem unconstrainedBurningRank_of_restrictedNoFort {field grade : Field} (permits : Site → Site → Prop)
    {deck : PeriodDeck} {sites : Finset Site}
    (hcover : deck.Covers sites) (heven : ∀ step ∈ deck.span, EvenSite step)
    (hcharge : ∀ step ∈ deck.span, ∀ site, laplacian field (site + step) = laplacian field site)
    (hgrade : ∀ step ∈ deck.span, ∃ increment : ℤ, ∀ site, grade (site + step) = grade site + increment)
    (hbinary : ∀ site, laplacian field site = -1 ∨ laplacian field site = 0)
    (hno : RestrictedNoFort field grade permits) :
    ∃ (scale : ℤ) (remainder : Field) (budget : ℤ), 0 < scale ∧
      (∀ site, 0 ≤ remainder site ∧ remainder site ≤ budget) ∧
      (∀ step ∈ deck.span, ∀ site, remainder (site + step) = remainder site) ∧
      IsBurningRank field (fun site => scale * grade site + remainder site) :=
  exists_burningRank_of_no_incomingFort hcover heven hcharge hgrade hbinary
    (noIncomingFort_of_restricted permits hno)

end FLatticePaper
