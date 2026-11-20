import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.Basic

namespace FLatticePaper.Construction

/-- A finite integer height function, with values only on its retained sites. -/
structure HeightTile (α : Type*) where
  sites : Finset α
  height : sites → ℤ

namespace HeightTile

variable {α : Type*} [DecidableEq α]

private def difference (old incoming : HeightTile α) (site : ↥(old.sites ∩ incoming.sites)) : ℤ :=
  incoming.height ⟨site, (Finset.mem_inter.mp site.property).2⟩ -
    old.height ⟨site, (Finset.mem_inter.mp site.property).1⟩

/-- The minimum of the incoming height minus the old height on the actual intersection. -/
def contactShift (old incoming : HeightTile α)
    (contact : (old.sites ∩ incoming.sites).Nonempty) : ℤ :=
  ((old.sites ∩ incoming.sites).attach.image (old.difference incoming)).min'
    ((Finset.attach_nonempty_iff.mpr contact).image _)

theorem contactShift_le_difference (old incoming : HeightTile α)
    (contact : (old.sites ∩ incoming.sites).Nonempty) {site : α}
    (hold : site ∈ old.sites) (hin : site ∈ incoming.sites) :
    old.contactShift incoming contact ≤ incoming.height ⟨site, hin⟩ - old.height ⟨site, hold⟩ :=
  Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.mem_attach _
    ⟨site, Finset.mem_inter.mpr ⟨hold, hin⟩⟩))

/-- The ordered minimum: at every common site the old value wins after normalization. -/
def insert (old incoming : HeightTile α)
    (contact : (old.sites ∩ incoming.sites).Nonempty) : HeightTile α where
  sites := old.sites ∪ incoming.sites
  height site :=
    if hold : site.val ∈ old.sites then old.height ⟨site, hold⟩
    else
      incoming.height ⟨site, (Finset.mem_union.mp site.property).resolve_left hold⟩ -
        old.contactShift incoming contact

@[simp]
theorem insert_sites (old incoming : HeightTile α) (contact) :
    (old.insert incoming contact).sites = old.sites ∪ incoming.sites := rfl

theorem insert_height_of_mem (old incoming : HeightTile α) (contact)
    {site : α} (hold : site ∈ old.sites) :
    (old.insert incoming contact).height ⟨site, Finset.mem_union_left _ hold⟩ =
      old.height ⟨site, hold⟩ := dif_pos hold

theorem insert_height_of_notMem (old incoming : HeightTile α) (contact)
    {site : α} (hold : site ∉ old.sites) (hin : site ∈ incoming.sites) :
    (old.insert incoming contact).height ⟨site, Finset.mem_union_right _ hin⟩ =
      incoming.height ⟨site, hin⟩ - old.contactShift incoming contact := dif_neg hold

theorem insert_height_eq_min (old incoming : HeightTile α) (contact)
    {site : α} (hold : site ∈ old.sites) (hin : site ∈ incoming.sites) :
    (old.insert incoming contact).height ⟨site, Finset.mem_union_left _ hold⟩ =
      min (old.height ⟨site, hold⟩)
        (incoming.height ⟨site, hin⟩ - old.contactShift incoming contact) := by
  rw [insert_height_of_mem, min_eq_left]
  have := old.contactShift_le_difference incoming contact hold hin
  omega

/-- Agreement on the tile's own domain, with a single constant. -/
def Agrees (tile : HeightTile α) (target : α → ℤ) (gauge : ℤ) : Prop :=
  ∀ site : tile.sites, tile.height site = target site + gauge

/-- Fresh-site equality, weak overlap comparison and one exact contact,
all after subtracting the same offset from the incoming copy. -/
def Fits (incoming : HeightTile α) (occupied : Finset α) (target : α → ℤ) : Prop :=
  ∃ offset : ℤ,
    (∀ site : incoming.sites, site.val ∉ occupied → incoming.height site - offset = target site) ∧
    (∀ site : incoming.sites, site.val ∈ occupied → target site ≤ incoming.height site - offset) ∧
    (∃ site : incoming.sites, site.val ∈ occupied ∧ incoming.height site - offset = target site)

theorem Fits.contact {incoming : HeightTile α} {occupied : Finset α} {target : α → ℤ}
    (hfit : incoming.Fits occupied target) : (occupied ∩ incoming.sites).Nonempty := by
  obtain ⟨_, _, _, site, hsite, _⟩ := hfit
  exact ⟨site, Finset.mem_inter.mpr ⟨hsite, site.property⟩⟩

/-- Section 9, recovering the finite tiles: the offset relative to the target,
minus the old gauge, is exactly the minimum subtracted at the insertion. -/
theorem contactShift_eq_of_agrees (old incoming : HeightTile α) (contact)
    {target : α → ℤ} {gauge offset : ℤ} (hold : old.Agrees target gauge)
    (hle : ∀ site : incoming.sites, site.val ∈ old.sites →
      target site ≤ incoming.height site - offset)
    (heq : ∃ site : incoming.sites, site.val ∈ old.sites ∧
      incoming.height site - offset = target site) :
    old.contactShift incoming contact = offset - gauge := by
  apply le_antisymm
  · obtain ⟨site, hsite, heq⟩ := heq
    have hbound := old.contactShift_le_difference incoming contact hsite site.property
    have hvalue := hold ⟨site, hsite⟩
    change old.contactShift incoming contact ≤ incoming.height site - old.height ⟨site, hsite⟩
      at hbound
    dsimp at hvalue
    omega
  · unfold contactShift
    apply Finset.le_min'
    intro value hvalue
    obtain ⟨site, _, rfl⟩ := Finset.mem_image.mp hvalue
    obtain ⟨hsiteOld, hsiteIn⟩ := Finset.mem_inter.mp site.property
    have hbound := hle ⟨site, hsiteIn⟩ hsiteOld
    have hvalue := hold ⟨site, hsiteOld⟩
    dsimp [difference] at hbound hvalue ⊢
    omega

/-- The weak comparisons suffice to identify the entire union, including
overlap sites where the normalized incoming value is strictly higher. -/
theorem insert_agrees (old incoming : HeightTile α) (contact)
    {target : α → ℤ} {gauge : ℤ} (hold : old.Agrees target gauge)
    (hfit : incoming.Fits old.sites target) :
    (old.insert incoming contact).Agrees target gauge := by
  obtain ⟨offset, hfresh, hle, heq⟩ := hfit
  have hshift := old.contactShift_eq_of_agrees incoming contact hold hle heq
  rintro ⟨site, hsite⟩
  by_cases hmem : site ∈ old.sites
  · rw [insert_height_of_mem old incoming contact hmem]
    exact hold ⟨site, hmem⟩
  · have hin := (Finset.mem_union.mp hsite).resolve_left hmem
    rw [insert_height_of_notMem old incoming contact hmem hin, hshift]
    have := hfresh ⟨site, hin⟩ hmem
    omega

/-- Each next copy must meet the whole earlier union, not just the previous copy. -/
def OrderedContacts (occupied : Finset α) : List (HeightTile α) → Prop
  | [] => True
  | incoming :: rest =>
      (occupied ∩ incoming.sites).Nonempty ∧ OrderedContacts (occupied ∪ incoming.sites) rest

/-- The manuscript's chronological insertion rule, defined on lists with genuine contacts. -/
def insertAll (old : HeightTile α) (copies : List (HeightTile α))
    (contacts : OrderedContacts old.sites copies) : HeightTile α :=
  match copies with
  | [] => old
  | incoming :: rest =>
      (old.insert incoming contacts.1).insertAll rest contacts.2

theorem insertAll_sites (old : HeightTile α) (copies : List (HeightTile α))
    (contacts : OrderedContacts old.sites copies) :
    (old.insertAll copies contacts).sites =
      copies.foldl (fun occupied incoming => occupied ∪ incoming.sites) old.sites := by
  induction copies generalizing old with
  | nil => rfl
  | cons incoming rest ih => exact ih (old.insert incoming contacts.1) contacts.2

theorem subset_insertAll_sites (old : HeightTile α)
    (copies : List (HeightTile α)) (contacts : OrderedContacts old.sites copies) :
    old.sites ⊆ (old.insertAll copies contacts).sites := by
  induction copies generalizing old with
  | nil => exact Finset.Subset.rfl
  | cons incoming rest ih =>
    exact Finset.Subset.trans Finset.subset_union_left
      (ih (old.insert incoming contacts.1) contacts.2)

/-- Comparisons for each actual successive earlier union in the specified list. -/
def OrderedComparisons (target : α → ℤ) (occupied : Finset α) : List (HeightTile α) → Prop
  | [] => True
  | incoming :: rest =>
      incoming.Fits occupied target ∧ OrderedComparisons target (occupied ∪ incoming.sites) rest

theorem OrderedComparisons.contacts {target : α → ℤ} {occupied : Finset α}
    {copies : List (HeightTile α)} (h : OrderedComparisons target occupied copies) :
    OrderedContacts occupied copies := by
  induction copies generalizing occupied with
  | nil => trivial
  | cons _ _ ih => exact ⟨h.1.contact, ih h.2⟩

theorem insertAll_agrees (old : HeightTile α)
    (copies : List (HeightTile α)) (contacts : OrderedContacts old.sites copies)
    {target : α → ℤ} {gauge : ℤ} (hold : old.Agrees target gauge)
    (hcopies : OrderedComparisons target old.sites copies) :
    (old.insertAll copies contacts).Agrees target gauge := by
  induction copies generalizing old with
  | nil => exact hold
  | cons incoming rest ih =>
    exact ih (old.insert incoming contacts.1) contacts.2
      (old.insert_agrees incoming contacts.1 hold hcopies.1) hcopies.2

theorem Agrees.fits {incoming : HeightTile α} {occupied : Finset α} {target : α → ℤ} {gauge : ℤ}
    (h : incoming.Agrees target gauge) (contact : (occupied ∩ incoming.sites).Nonempty) :
    incoming.Fits occupied target := by
  obtain ⟨site, hsite⟩ := contact
  obtain ⟨hold, hin⟩ := Finset.mem_inter.mp hsite
  refine ⟨gauge, fun site _ => ?_, fun site _ => ?_, ⟨⟨site, hin⟩, hold, ?_⟩⟩
  · rw [h site]
    omega
  · rw [h site]
    omega
  · rw [h ⟨site, hin⟩]
    omega

/-- The maximum height on a nonempty finite tile. -/
def maxHeight (tile : HeightTile α) (hne : tile.sites.Nonempty) : ℤ :=
  (tile.sites.attach.image tile.height).max' ((Finset.attach_nonempty_iff.mpr hne).image _)

/-- The normalization at the end of an L-correction, without changing its support. -/
def maxZero (tile : HeightTile α) (hne : tile.sites.Nonempty) : HeightTile α where
  sites := tile.sites
  height site := tile.height site - tile.maxHeight hne

omit [DecidableEq α] in
theorem maxZero_agrees (tile : HeightTile α) (hne : tile.sites.Nonempty)
    {target : α → ℤ} {gauge : ℤ} (h : tile.Agrees target gauge) :
    (tile.maxZero hne).Agrees target (gauge - tile.maxHeight hne) := by
  intro site
  change tile.height site - tile.maxHeight hne = target site + (gauge - tile.maxHeight hne)
  rw [h site]
  omega

end HeightTile

end FLatticePaper.Construction
