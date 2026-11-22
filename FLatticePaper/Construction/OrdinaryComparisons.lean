import FLatticePaper.Construction.OrdinaryStandardCover

/-! The three comparisons of an insertion of one ordinary standard copy (task 41, supplement Part II).

For an incoming copy `c` inserted into the occupied union `occupied`, with target field `target` and offset `o`:
* comparison 1, fresh-site equality: `c − o = target` on the sites of `c` outside `occupied`;
* comparison 2, weak overlap inequality: `target ≤ c − o` on the sites of `c` inside `occupied`;
* comparison 3, contact: `c − o = target` at one site inside `occupied`.

`HeightTile.Fits` is their conjunction with a common offset. If the copy agrees with the target up to one constant
(the nominal price statement of ALL_PROPER_UNC_STANDARD_NOMINAL_PRICES, sections 2 to 4), comparisons 1 and 2 hold with
that constant; comparison 3 holds exactly when the copy meets the occupied union. -/

namespace FLatticePaper.Construction

open HeightTile

/-- Comparison 1: the incoming height minus the offset equals the target on the fresh sites. -/
def FreshEquality {α : Type*} (incoming : HeightTile α) (occupied : Finset α) (target : α → ℤ) (offset : ℤ) : Prop :=
  ∀ site : incoming.sites, site.val ∉ occupied → incoming.height site - offset = target site

/-- Comparison 2: the incoming height minus the offset is at least the target on the overlap. -/
def OverlapWeak {α : Type*} (incoming : HeightTile α) (occupied : Finset α) (target : α → ℤ) (offset : ℤ) : Prop :=
  ∀ site : incoming.sites, site.val ∈ occupied → target site ≤ incoming.height site - offset

/-- Comparison 3: the incoming height minus the offset equals the target at one overlap site. -/
def ContactEquality {α : Type*} (incoming : HeightTile α) (occupied : Finset α) (target : α → ℤ) (offset : ℤ) : Prop :=
  ∃ site : incoming.sites, site.val ∈ occupied ∧ incoming.height site - offset = target site

/-- The three comparisons with a common offset are exactly `HeightTile.Fits`. -/
theorem fits_iff_three {α : Type*} (incoming : HeightTile α) (occupied : Finset α) (target : α → ℤ) :
    incoming.Fits occupied target ↔
      ∃ offset : ℤ, FreshEquality incoming occupied target offset ∧
        OverlapWeak incoming occupied target offset ∧ ContactEquality incoming occupied target offset :=
  Iff.rfl

/-- Comparison 1 from the nominal agreement of the copy with the target, with the constant as offset. -/
theorem freshEquality_of_agrees {α : Type*} {incoming : HeightTile α} {occupied : Finset α} {target : α → ℤ} {gauge : ℤ}
    (h : incoming.Agrees target gauge) : FreshEquality incoming occupied target gauge :=
  fun site _ => by
    have := h site
    omega

/-- Comparison 2 from the nominal agreement: the weak overlap inequality holds with equality. -/
theorem overlapWeak_of_agrees {α : Type*} {incoming : HeightTile α} {occupied : Finset α} {target : α → ℤ} {gauge : ℤ}
    (h : incoming.Agrees target gauge) : OverlapWeak incoming occupied target gauge :=
  fun site _ => by
    have := h site
    omega

/-- Comparison 3 from the nominal agreement: a contact equality exists exactly when the copy meets the occupied union,
which is the chronological contact of the insertion. -/
theorem contactEquality_of_agrees {α : Type*} [DecidableEq α] {incoming : HeightTile α} {occupied : Finset α} {target : α → ℤ} {gauge : ℤ}
    (h : incoming.Agrees target gauge) (contact : (occupied ∩ incoming.sites).Nonempty) :
    ContactEquality incoming occupied target gauge := by
  obtain ⟨site, hsite⟩ := contact
  obtain ⟨hold, hin⟩ := Finset.mem_inter.mp hsite
  refine ⟨⟨site, hin⟩, hold, ?_⟩
  have := h ⟨site, hin⟩
  simp only at this ⊢
  omega

/-- The three comparisons from the nominal agreement and one chronological contact. -/
theorem fits_of_agrees {α : Type*} [DecidableEq α] {incoming : HeightTile α} {occupied : Finset α} {target : α → ℤ} {gauge : ℤ}
    (h : incoming.Agrees target gauge) (contact : (occupied ∩ incoming.sites).Nonempty) :
    incoming.Fits occupied target :=
  (fits_iff_three incoming occupied target).mpr
    ⟨gauge, freshEquality_of_agrees h, overlapWeak_of_agrees h, contactEquality_of_agrees h contact⟩

end FLatticePaper.Construction
