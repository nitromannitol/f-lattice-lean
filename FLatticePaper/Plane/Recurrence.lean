import FLatticePaper.Rank
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Relation

namespace FLatticePaper

/-- Directed paths confined to the induced graph on a finite set. -/
def Reaches (sites : Finset Site) (first last : Site) : Prop :=
  Relation.ReflTransGen (fun source target => source ∈ sites ∧ target ∈ sites ∧ Edge source target)
    first last

def StronglyConnected (sites : Finset Site) : Prop :=
  sites.Nonempty ∧ ∀ first ∈ sites, ∀ last ∈ sites, Reaches sites first last

def incomingBoundaryFinset (sites : Finset Site) : Finset Site :=
  (sites.image incomingNeg ∪ sites.image incomingPos) \ sites

theorem mem_incomingBoundaryFinset {sites : Finset Site} {site : Site} :
    site ∈ incomingBoundaryFinset sites ↔ site ∈ incomingBoundary sites := by
  unfold incomingBoundaryFinset incomingBoundary
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hneg | hpos, hout⟩
    · obtain ⟨center, hmem, rfl⟩ := hneg
      exact ⟨hout, center, hmem, Or.inl rfl⟩
    · obtain ⟨center, hmem, rfl⟩ := hpos
      exact ⟨hout, center, hmem, Or.inr rfl⟩
  · rintro ⟨hout, center, hmem, hneg | hpos⟩
    · exact ⟨Or.inl ⟨center, hmem, hneg.symm⟩, hout⟩
    · exact ⟨Or.inr ⟨center, hmem, hpos.symm⟩, hout⟩

theorem incomingBoundaryFinset_nonempty {sites : Finset Site} (hne : sites.Nonempty) :
    (incomingBoundaryFinset sites).Nonempty := by
  let grade (site : Site) : ℤ := site.1 + site.2
  obtain ⟨site, hsite, hmin⟩ := sites.exists_min_image grade hne
  have hlower : grade (incomingNeg site) < grade site := by
    by_cases heven : EvenSite site <;> simp [grade, incomingNeg, heven]
    all_goals omega
  exact ⟨incomingNeg site, mem_incomingBoundaryFinset.mpr
    ⟨fun hin => (not_lt_of_ge (hmin _ hin)) hlower, site, hsite, Or.inl rfl⟩⟩

def maxDifference (field competitor : Field) (sites : Finset Site) (hne : sites.Nonempty) : ℤ :=
  (sites.image (fun site => field site - competitor site)).max' (hne.image _)

theorem le_maxDifference (field competitor : Field) {sites : Finset Site} {site : Site}
    (hsite : site ∈ sites) :
    field site - competitor site ≤ maxDifference field competitor sites ⟨site, hsite⟩ :=
  Finset.le_max' _ _ (Finset.mem_image_of_mem (fun input => field input - competitor input) hsite)

theorem maxDifference_le (field competitor : Field) {sites : Finset Site} (hne : sites.Nonempty)
    {bound : ℤ} (hbound : ∀ site ∈ sites, field site - competitor site ≤ bound) :
    maxDifference field competitor sites hne ≤ bound := by
  apply Finset.max'_le
  intro value hv
  obtain ⟨site, hsite, rfl⟩ := Finset.mem_image.mp hv
  exact hbound site hsite

/-- The exact comparison in the manuscript's definition: the competitor is
superharmonic on the plane and the finite test set is strongly connected. -/
def Recurrent (field : Field) : Prop :=
  ∀ competitor : Field, Superharmonic competitor → ∀ (sites : Finset Site) (h : StronglyConnected sites),
    maxDifference field competitor sites h.1 ≤
      maxDifference field competitor (incomingBoundaryFinset sites) (incomingBoundaryFinset_nonempty h.1)

theorem Recurrent.finiteComparison {field competitor : Field} (hr : Recurrent field)
    (hf : Superharmonic competitor) (sites : Finset Site) (hsc : StronglyConnected sites) (bound : ℤ)
    (hb : ∀ site ∈ incomingBoundary sites, field site - competitor site ≤ bound) :
    ∀ site ∈ sites, field site - competitor site ≤ bound := by
  intro site hsite
  exact (le_maxDifference field competitor hsite).trans ((hr competitor hf sites hsc).trans
    (maxDifference_le field competitor (incomingBoundaryFinset_nonempty hsc.1)
      (fun input hin => hb input (mem_incomingBoundaryFinset.mp hin))))

theorem recurrent_of_allowed {field : Field}
    (hall : ∀ sites : Finset Site, sites.Nonempty → Allowed (fun site => laplacian field site + 1) sites) :
    Recurrent field := by
  intro competitor hf sites hsc
  apply maxDifference_le
  refine finiteComparison_of_allowed sites _ hall (fun site _ => hf site) ?_
  intro site hsite
  exact le_maxDifference field competitor (mem_incomingBoundaryFinset.mpr hsite)

theorem IsBurningRank.recurrent {α : Type*} [LinearOrder α] {field : Field} {rank : Site → α}
    (hr : IsBurningRank field rank) : Recurrent field :=
  recurrent_of_allowed hr.allowed

private noncomputable def predecessors (sites : Finset Site) (target : Site) : Finset Site :=
  by classical exact sites.filter (fun site => Reaches sites site target)

private theorem mem_predecessors {sites : Finset Site} {site target : Site} :
    site ∈ predecessors sites target ↔ site ∈ sites ∧ Reaches sites site target := by
  classical
  unfold predecessors
  exact Finset.mem_filter

private theorem Reaches.predecessors_subset {sites : Finset Site} {first last : Site}
    (h : Reaches sites first last) : predecessors sites first ⊆ predecessors sites last := by
  intro site hmem
  obtain ⟨hsite, hpath⟩ := mem_predecessors.mp hmem
  exact mem_predecessors.mpr ⟨hsite, hpath.trans h⟩

private theorem Reaches.restrict_to_predecessors {sites : Finset Site} {seed first last : Site}
    (h : Reaches sites first last) (hlast : last ∈ predecessors sites seed) :
    Reaches (predecessors sites seed) first last := by
  induction h with
  | refl => exact .refl
  | @tail before after _ hedge ih =>
    have hstep : Reaches sites before after := Relation.ReflTransGen.single hedge
    have hbefore := mem_predecessors.mpr
      ⟨hedge.1, hstep.trans (mem_predecessors.mp hlast).2⟩
    exact (ih hbefore).tail ⟨hbefore, hlast, hedge.2.2⟩

/-- A smallest predecessor set is a source strong component. In particular
its incoming degrees agree with those in the original set at every one of its sites. -/
theorem exists_source_component {sites : Finset Site} (hne : sites.Nonempty) :
    ∃ component : Finset Site, component ⊆ sites ∧ StronglyConnected component ∧
      ∀ site ∈ component, incomingDegree component site = incomingDegree sites site := by
  obtain ⟨seed, hseed, hmin⟩ := sites.exists_min_image (fun site => (predecessors sites site).card) hne
  let component := predecessors sites seed
  have hsub : component ⊆ sites := fun _ hmem => (mem_predecessors.mp hmem).1
  have hpres (site : Site) (hmem : site ∈ component) : predecessors sites site = component :=
    Finset.eq_of_subset_of_card_le (mem_predecessors.mp hmem).2.predecessors_subset
      (hmin site (hsub hmem))
  refine ⟨component, hsub, ⟨⟨seed, mem_predecessors.mpr ⟨hseed, .refl⟩⟩, ?_⟩, ?_⟩
  · intro first hfirst last hlast
    have hp : first ∈ predecessors sites last := hpres last hlast ▸ hfirst
    exact (mem_predecessors.mp hp).2.restrict_to_predecessors hlast
  · intro site hmem
    have hinput (input : Site) (hedge : Edge input site) : input ∈ component ↔ input ∈ sites := by
      refine ⟨fun hin => hsub hin, fun hin => ?_⟩
      have hstep : Reaches sites input site := Relation.ReflTransGen.single ⟨hin, hsub hmem, hedge⟩
      exact mem_predecessors.mpr ⟨hin, hstep.trans (mem_predecessors.mp hmem).2⟩
    simp only [incomingDegree, hinput (incomingNeg site) (Or.inl rfl),
      hinput (incomingPos site) (Or.inr rfl)]

theorem Recurrent.allowed {field : Field} (hr : Recurrent field) (hf : Superharmonic field)
    (sites : Finset Site) (hne : sites.Nonempty) :
    Allowed (fun site => laplacian field site + 1) sites := by
  by_contra! hforbidden
  obtain ⟨component, hsub, hsc, hdegree⟩ := exists_source_component hne
  let competitor : Field := fun site => field site - (if site ∈ component then 1 else 0)
  have hlap (site : Site) :
      laplacian competitor site = laplacian field site - incomingDegree component site +
        (if site ∈ component then 2 else 0) := by
    by_cases hmem : site ∈ component <;> simp [competitor, laplacian, incomingDegree, hmem] <;> omega
  have hsuper : Superharmonic competitor := by
    intro site
    rw [hlap]
    by_cases hmem : site ∈ component
    · have hbad : ¬ incomingDegree sites site ≤ laplacian field site + 1 :=
        fun hle => hforbidden ⟨site, hsub hmem, hle⟩
      rw [hdegree site hmem, if_pos hmem]
      omega
    · have hnonneg : 0 ≤ incomingDegree component site := by
        unfold incomingDegree
        split <;> split <;> omega
      have hle := hf site
      rw [if_neg hmem]
      omega
  obtain ⟨site, hsite⟩ := hsc.1
  have hcompare := hr.finiteComparison hsuper component hsc 0
    (fun input hinput => by
      have hout : input ∉ component := hinput.1
      simp [competitor, hout]) site hsite
  simp [competitor, hsite] at hcompare
  omega

/-- Proposition `prop:recurrence`, with no binary-Laplacian hypothesis. -/
theorem recurrent_iff_allowed {field : Field} (hf : Superharmonic field) :
    Recurrent field ↔
      ∀ sites : Finset Site, sites.Nonempty → Allowed (fun site => laplacian field site + 1) sites :=
  ⟨fun hr sites hne => hr.allowed hf sites hne, recurrent_of_allowed⟩

end FLatticePaper
