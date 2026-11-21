import FLatticePaper.Construction.BaseCaseRecurrence
import FLatticePaper.Plane.AlternateSlip
import FLatticePaper.Plane.PeriodCocycle
import FLatticePaper.Construction.StaircaseRotation
import FLatticePaper.Construction.AlternateStaircaseRecurrence
import FLatticePaper.Construction.LadderRank
import FLatticePaper.Construction.AlternateLadderRank
import FLatticePaper.Construction.StaircaseCoverage
import FLatticePaper.Construction.LadderCoverage
import FLatticePaper.Construction.LadderRotation

/-! The four near-one base cases of Section 6 of `paper/farey_recursion.tex`. The tiles and heights are transcribed
literally from the TeX (`lemma:basecase_2k_odd_std` lines 2180–2192, `lemma:basecase_2k_odd_alt` lines 2261–2280,
`lemma:basecase_2k_even_std` lines 2402–2420, `lemma:basecase_2k_even_alt` lines 2478–2500). The fraction is
`Fraction.rotate ⟨1, d⟩`. The physical graph is the one of `Graph.lean`; the paper's extension is stated in TeX
coordinates, and the recurrence and superharmonicity are stated for the physical translate `z ↦ field (z - (0,1))`. -/

namespace FLatticePaper.Construction

open Farey

/-! ### Standard odd near-one staircase, `lemma:basecase_2k_odd_std` (lines 2180–2192) -/

/-- The tile `T_{p_1}` of `lemma:basecase_2k_odd_std`. -/
def paperNearStairTile (d : ℤ) : Set Site :=
  {x | 0 ≤ x.1 ∧ x.1 ≤ d + 1 ∧ 1 ≤ x.2 ∧ x.2 ≤ 2 * d - 1 ∧ -1 ≤ x.2 - x.1 ∧ x.2 - x.1 ≤ d} ∪
    {(0, d + 1), (d + 1, d - 1)}

/-- The height `g_{p_1}` of `lemma:basecase_2k_odd_std`. -/
def paperNearStairValue (d : ℤ) (x : Site) : ℤ :=
  -((x.2 - x.1) ^ 2 / 4) + min (d - x.2) 0 + if x = (0, d + 1) ∨ x = (d + 1, d - 1) then 1 else 0

/-! ### Alternate odd near-one staircase, `lemma:basecase_2k_odd_alt` (lines 2261–2280) -/

/-- `A = [-1,0] × {2d} ∪ [d,d+1] × {d-2}` of `lemma:basecase_2k_odd_alt`. -/
def paperNearStairAltA (d : ℤ) : Set Site :=
  {x : Site | -1 ≤ x.1 ∧ x.1 ≤ 0 ∧ x.2 = 2 * d} ∪ {x : Site | d ≤ x.1 ∧ x.1 ≤ d + 1 ∧ x.2 = d - 2}

/-- `B = {(x_1, x_2) : x_2 - x_1 = d - 1 and 0 < x_1 < d}` of `lemma:basecase_2k_odd_alt`. -/
def paperNearStairAltB (d : ℤ) : Set Site :=
  {x : Site | x.2 - x.1 = d - 1 ∧ 0 < x.1 ∧ x.1 < d}

/-- `C = {-1} × [d+1,2d] ∪ {d+1} × [d-2,2d-3]` of `lemma:basecase_2k_odd_alt`. -/
def paperNearStairAltC (d : ℤ) : Set Site :=
  {x : Site | x.1 = -1 ∧ d + 1 ≤ x.2 ∧ x.2 ≤ 2 * d} ∪
    {x : Site | x.1 = d + 1 ∧ d - 2 ≤ x.2 ∧ x.2 ≤ 2 * d - 3}

/-- `D = {(x_1, x_2) ∈ [0, d] × [1, 3d-3] : -1 ≤ x_2 - x_1 ≤ 2d-1}` of `lemma:basecase_2k_odd_alt`. -/
def paperNearStairAltD (d : ℤ) : Set Site :=
  {x : Site | 0 ≤ x.1 ∧ x.1 ≤ d ∧ 1 ≤ x.2 ∧ x.2 ≤ 3 * d - 3 ∧ -1 ≤ x.2 - x.1 ∧ x.2 - x.1 ≤ 2 * d - 1}

/-- The tile `\hat T_{p_1} = A ∪ B ∪ C ∪ D` of `lemma:basecase_2k_odd_alt`. -/
def paperNearStairAltTile (d : ℤ) : Set Site :=
  paperNearStairAltA d ∪ paperNearStairAltB d ∪ paperNearStairAltC d ∪ paperNearStairAltD d

/-- The height `\hat g_{p_1}` on `\hat T_{p_1}` in `lemma:basecase_2k_odd_alt`, with `1_{A ∪ B}`. -/
noncomputable def paperNearStairAltValue (d : ℤ) (x : Site) : ℤ :=
  -((x.2 - x.1) ^ 2 / 4) + min (d - x.2 - 1) 0 + min ((2 * d - 1) - x.2) 0 +
    max ((x.2 - x.1) - d + 1) 0 + (paperNearStairAltA d ∪ paperNearStairAltB d).indicator (fun _ => (1 : ℤ)) x

/-! ### Standard even near-one doubled staircase, `lemma:basecase_2k_even_std` (lines 2402–2420) -/

/-- `A = (-1, 2d+1) ∪ (d+1, d-1)` of `lemma:basecase_2k_even_std`, as two sites. -/
def paperNearLadderA (d : ℤ) : Set Site := {(-1, 2 * d + 1), (d + 1, d - 1)}

/-- `B = {(x_1, x_2) : x_2 - x_1 = d and 0 < x_1 < d}` of `lemma:basecase_2k_even_std`. -/
def paperNearLadderB (d : ℤ) : Set Site :=
  {x : Site | x.2 - x.1 = d ∧ 0 < x.1 ∧ x.1 < d}

/-- `C = {(x_1, x_2) ∈ [-1, d+1] × [1, 3d-1] : -1 ≤ x_2 - x_1 ≤ 2d+1}` of `lemma:basecase_2k_even_std`. -/
def paperNearLadderC (d : ℤ) : Set Site :=
  {x : Site | -1 ≤ x.1 ∧ x.1 ≤ d + 1 ∧ 1 ≤ x.2 ∧ x.2 ≤ 3 * d - 1 ∧ -1 ≤ x.2 - x.1 ∧ x.2 - x.1 ≤ 2 * d + 1}

/-- `D = {x_1 = -1 and x_2 ≤ d+1, or x_1 = d+1 and x_2 ≥ 2d-1}` of `lemma:basecase_2k_even_std`. -/
def paperNearLadderD (d : ℤ) : Set Site :=
  {x : Site | (x.1 = -1 ∧ x.2 ≤ d + 1) ∨ (x.1 = d + 1 ∧ 2 * d - 1 ≤ x.2)}

/-- The tile `T_{q_1} = (A ∪ B ∪ C) \ D` of `lemma:basecase_2k_even_std`. -/
def paperNearLadderTile (d : ℤ) : Set Site :=
  (paperNearLadderA d ∪ paperNearLadderB d ∪ paperNearLadderC d) \ paperNearLadderD d

/-- The height `g_{q_1}` of `lemma:basecase_2k_even_std`, with `1_{A ∪ B}`. -/
noncomputable def paperNearLadderValue (d : ℤ) (x : Site) : ℤ :=
  -((x.2 - x.1) ^ 2 / 4) + min 0 (d - x.2) + min 0 (2 * d - x.2) + max ((x.2 - x.1) - d) 0 +
    (paperNearLadderA d ∪ paperNearLadderB d).indicator (fun _ => (1 : ℤ)) x

/-! ### Alternate even near-one doubled staircase, `lemma:basecase_2k_even_alt` (lines 2478–2500) -/

/-- `A = (-2, 2d) ∪ (d+1, d-1)` of `lemma:basecase_2k_even_alt`, as two sites. -/
def paperNearLadderAltA (d : ℤ) : Set Site := {(-2, 2 * d), (d + 1, d - 1)}

/-- `B = {(x_1, x_2) : x_2 - x_1 = d and 0 < x_1 < d-1}` of `lemma:basecase_2k_even_alt`. -/
def paperNearLadderAltB (d : ℤ) : Set Site :=
  {x : Site | x.2 - x.1 = d ∧ 0 < x.1 ∧ x.1 < d - 1}

/-- `C = {(x_1, x_2) ∈ [-2, d+1] × [1, 3d-2] : -1 ≤ x_2 - x_1 ≤ 2d+1}` of `lemma:basecase_2k_even_alt`. -/
def paperNearLadderAltC (d : ℤ) : Set Site :=
  {x : Site | -2 ≤ x.1 ∧ x.1 ≤ d + 1 ∧ 1 ≤ x.2 ∧ x.2 ≤ 3 * d - 2 ∧ -1 ≤ x.2 - x.1 ∧ x.2 - x.1 ≤ 2 * d + 1}

/-- `D = {x_1 ≤ -1 and x_2 ≤ d-1, or x_1 ≥ d and x_2 ≥ 2d}` of `lemma:basecase_2k_even_alt`. -/
def paperNearLadderAltD (d : ℤ) : Set Site :=
  {x : Site | (x.1 ≤ -1 ∧ x.2 ≤ d - 1) ∨ (d ≤ x.1 ∧ 2 * d ≤ x.2)}

/-- The tile `\hat T_{q_1} = (A ∪ B ∪ C) \ D` of `lemma:basecase_2k_even_alt`. -/
def paperNearLadderAltTile (d : ℤ) : Set Site :=
  (paperNearLadderAltA d ∪ paperNearLadderAltB d ∪ paperNearLadderAltC d) \ paperNearLadderAltD d

/-- The height `\hat g_{q_1}` on `\hat T_{q_1}` in `lemma:basecase_2k_even_alt`, with `1_{A ∪ B}`. -/
noncomputable def paperNearLadderAltValue (d : ℤ) (x : Site) : ℤ :=
  -((x.2 - x.1) ^ 2 / 4) + min 0 (d - x.2) + min 0 (2 * d - 1 - x.2) + max 0 (x.2 - x.1 - d) +
    (paperNearLadderAltA d ∪ paperNearLadderAltB d).indicator (fun _ => (1 : ℤ)) x


/-! ### Translation facts for physical fields -/

/-- Translating a field by `w` shifts the transverse constant by the transverse grade of `w`. -/
theorem hasGeneratorPeriods_translate {fraction : Fraction} {field : Field} {constantU constantV : ℤ}
    (w : Site) (h : HasGeneratorPeriods fraction field constantU constantV) :
    HasGeneratorPeriods fraction (fun z => field (z - w)) constantU
      (constantV + fraction.transverseGrade w) := by
  refine ⟨fun site => ?_, fun site => ?_⟩
  · have := h.1 (site - w)
    rw [show site - w + fraction.modifiedDeck.kernel = site + fraction.modifiedDeck.kernel - w by abel] at this
    exact this
  · have := h.2 (site - w)
    have hgrade : fraction.transverseGrade (site - w)
        = fraction.transverseGrade site - fraction.transverseGrade w := by
      simp only [Fraction.transverseGrade, Prod.fst_sub, Prod.snd_sub]
      ring
    rw [hgrade, show site - w + fraction.modifiedDeck.transverse
      = site + fraction.modifiedDeck.transverse - w by abel] at this
    show field (site + fraction.modifiedDeck.transverse - w)
      = field (site - w) - fraction.transverseGrade site + (constantV + fraction.transverseGrade w)
    rw [this]
    ring

/-- Superharmonicity is preserved by translation by an even site. -/
theorem superharmonic_translate_even {field : Field} {w : Site} (hw : EvenSite w)
    (h : Superharmonic field) : Superharmonic (fun z => field (z - w)) := by
  intro site
  have hneg : EvenSite (-w) := by
    unfold EvenSite at hw ⊢
    simp only [Prod.fst_neg, Prod.snd_neg]
    omega
  have := laplacian_translate_of_even field site (-w) hneg
  simp only [sub_eq_add_neg]
  rw [this]
  exact h _

theorem edge_add_even {y x w : Site} (hw : EvenSite w) (h : Edge y x) : Edge (y + w) (x + w) := by
  rcases h with h | h
  · left
    rw [h, incomingNeg_add_of_even x w hw]
  · right
    rw [h, incomingPos_add_of_even x w hw]

theorem edge_sub_even {y x w : Site} (hw : EvenSite w) (h : Edge (y + w) x) : Edge y (x - w) := by
  have hneg : EvenSite (-w) := by
    unfold EvenSite at hw ⊢
    simp only [Prod.fst_neg, Prod.snd_neg]
    omega
  have := edge_add_even hneg h
  simpa only [add_neg_cancel_right, sub_eq_add_neg] using this

theorem mem_image_sub_iff {S : Finset Site} {w y : Site} :
    y ∈ S.image (fun z => z - w) ↔ y + w ∈ S := by
  constructor
  · intro h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h
    simpa using ha
  · intro h
    exact Finset.mem_image.mpr ⟨y + w, h, by simp⟩

theorem reaches_translate {S : Finset Site} {w : Site} (hw : EvenSite w) {first last : Site}
    (h : Reaches S first last) : Reaches (S.image (fun z => z - w)) (first - w) (last - w) := by
  unfold Reaches at h ⊢
  have hr : ∀ a b : Site, (a ∈ S ∧ b ∈ S ∧ Edge a b) →
      (a - w ∈ S.image (fun z => z - w) ∧ b - w ∈ S.image (fun z => z - w) ∧ Edge (a - w) (b - w)) := by
    intro a b hab
    obtain ⟨ha, hb, hedge⟩ := hab
    refine ⟨Finset.mem_image.mpr ⟨a, ha, rfl⟩, Finset.mem_image.mpr ⟨b, hb, rfl⟩, ?_⟩
    have := edge_add_even (w := -w) (by
      unfold EvenSite at hw ⊢
      simp only [Prod.fst_neg, Prod.snd_neg]
      omega) hedge
    simpa only [sub_eq_add_neg] using this
  exact Relation.ReflTransGen.lift (p := fun s t => s ∈ S.image (fun z => z - w) ∧
    t ∈ S.image (fun z => z - w) ∧ Edge s t) (fun z => z - w) hr first last h

theorem stronglyConnected_translate {S : Finset Site} {w : Site} (hw : EvenSite w)
    (h : StronglyConnected S) : StronglyConnected (S.image (fun z => z - w)) := by
  obtain ⟨⟨z, hz⟩, hall⟩ := h
  refine ⟨Finset.Nonempty.image ⟨z, hz⟩ _, ?_⟩
  intro first hfirst last hlast
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hfirst
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hlast
  exact reaches_translate hw (hall a ha b hb)

theorem incomingBoundaryFinset_translate {S : Finset Site} {w : Site} (hw : EvenSite w) :
    incomingBoundaryFinset (S.image (fun z => z - w)) = (incomingBoundaryFinset S).image (fun z => z - w) := by
  ext y
  constructor
  · intro hy
    rw [mem_incomingBoundaryFinset] at hy
    obtain ⟨hout, x, hx, hedge⟩ := hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    refine Finset.mem_image.mpr ⟨y + w, ?_, by simp⟩
    rw [mem_incomingBoundaryFinset]
    refine ⟨fun hin => hout (mem_image_sub_iff.mpr hin), a, ha, ?_⟩
    simpa using edge_add_even hw hedge
  · intro hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    rw [mem_incomingBoundaryFinset] at hz
    obtain ⟨hzout, x, hx, hedge⟩ := hz
    rw [mem_incomingBoundaryFinset]
    refine ⟨fun hin => hzout ?_, x - w, Finset.mem_image.mpr ⟨x, hx, rfl⟩, edge_sub_even hw ?_⟩
    · simpa using mem_image_sub_iff.mp hin
    · simpa using hedge

theorem maxDifference_congr (field competitor : Field) {A B : Finset Site} (hAB : A = B)
    (hA : A.Nonempty) (hB : B.Nonempty) :
    maxDifference field competitor A hA = maxDifference field competitor B hB := by
  subst hAB
  rfl

theorem maxDifference_translate (field competitor : Field) {w : Site} (T : Finset Site)
    (hT : T.Nonempty) :
    maxDifference (fun z => field (z - w)) competitor T hT
      = maxDifference field (fun y => competitor (y + w)) (T.image (fun z => z - w)) (hT.image _) := by
  unfold maxDifference
  simp only [Finset.image_image, Function.comp_def, sub_add_cancel]

/-- Recurrence is preserved by translation by an even site (the physical graph is unchanged). -/
theorem recurrent_translate_even {field : Field} {w : Site} (hw : EvenSite w) (h : Recurrent field) :
    Recurrent (fun z => field (z - w)) := by
  intro competitor hC sites hsc
  have hcomp : Superharmonic (fun y => competitor (y + w)) := by
    intro site
    rw [laplacian_translate_of_even competitor site w hw]
    exact hC _
  have key := h (fun y => competitor (y + w)) hcomp (sites.image (fun z => z - w))
    (stronglyConnected_translate hw hsc)
  rw [maxDifference_translate field competitor sites hsc.1,
    maxDifference_translate field competitor (incomingBoundaryFinset sites) (incomingBoundaryFinset_nonempty hsc.1)]
  exact le_trans key (le_of_eq (maxDifference_congr _ _ (incomingBoundaryFinset_translate hw) _ _))

/-! ### The lower-left chart of a raw tile -/

section LowerLeft

open HeightTile

theorem lowerLeft_trim_eq (raw : HeightTile Site) (hne : raw.sites.Nonempty) {point : Site}
    (hpoint : point ∈ raw.sites)
    (hmin : ∀ site ∈ raw.sites, point.2 ≤ site.2 ∧ (point.2 = site.2 → point.1 ≤ site.1)) :
    (raw.trim hne).lowerLeft (raw.trim_sites_nonempty hne) = point - raw.boxOrigin hne := by
  apply lowerLeft_eq_of_minimal (raw.trim hne) (raw.trim_sites_nonempty hne)
  · unfold HeightTile.trim
    rw [mem_place_sites, sub_neg_eq_add, sub_add_cancel]
    exact hpoint
  · intro site hmem
    unfold HeightTile.trim at hmem
    rw [mem_place_sites, sub_neg_eq_add] at hmem
    have := hmin _ hmem
    simp only [Prod.fst_add, Prod.snd_add] at this
    simp only [Prod.fst_sub, Prod.snd_sub]
    omega

/-- The occupied sites of the lower-left chart are the raw sites translated by `point`. -/
theorem mem_llCenter_iff (raw : HeightTile Site) (hne : raw.sites.Nonempty) {point : Site}
    (hpoint : point ∈ raw.sites)
    (hmin : ∀ site ∈ raw.sites, point.2 ≤ site.2 ∧ (point.2 = site.2 → point.1 ≤ site.1))
    (s : Site) :
    s ∈ ((raw.trim hne).llCenter (raw.trim_sites_nonempty hne)).sites ↔ s + point ∈ raw.sites := by
  have hl := lowerLeft_trim_eq raw hne hpoint hmin
  unfold HeightTile.llCenter
  rw [mem_place_sites, hl]
  unfold HeightTile.trim
  rw [mem_place_sites]
  have key : s - -(point - raw.boxOrigin hne) - -raw.boxOrigin hne = s + point := by abel
  rw [key]

/-- The lower-left chart reads the raw height at the translated site. -/
theorem llCenter_height_eq (raw : HeightTile Site) (hne : raw.sites.Nonempty) {point : Site}
    (hpoint : point ∈ raw.sites)
    (hmin : ∀ site ∈ raw.sites, point.2 ≤ site.2 ∧ (point.2 = site.2 → point.1 ≤ site.1))
    (s : Site) (hs : s ∈ ((raw.trim hne).llCenter (raw.trim_sites_nonempty hne)).sites)
    (hraw : s + point ∈ raw.sites) :
    ((raw.trim hne).llCenter (raw.trim_sites_nonempty hne)).height ⟨s, hs⟩
      = raw.height ⟨s + point, hraw⟩ := by
  have hl := lowerLeft_trim_eq raw hne hpoint hmin
  have hT : s - -(raw.trim hne).lowerLeft (raw.trim_sites_nonempty hne) ∈ (raw.trim hne).sites :=
    (HeightTile.mem_place_sites _ _ _ _).mp hs
  have h1 : ((raw.trim hne).llCenter (raw.trim_sites_nonempty hne)).height ⟨s, hs⟩
      = (raw.trim hne).height ⟨s - -(raw.trim hne).lowerLeft (raw.trim_sites_nonempty hne), hT⟩
        + (0 * s.1 + 0 * s.2) := rfl
  have hR : s - -(raw.trim hne).lowerLeft (raw.trim_sites_nonempty hne) - -raw.boxOrigin hne ∈ raw.sites :=
    (HeightTile.mem_place_sites _ _ _ _).mp hT
  have h2 : (raw.trim hne).height ⟨s - -(raw.trim hne).lowerLeft (raw.trim_sites_nonempty hne), hT⟩
      = raw.height ⟨s - -(raw.trim hne).lowerLeft (raw.trim_sites_nonempty hne) - -raw.boxOrigin hne, hR⟩
        + (0 * (s - -(raw.trim hne).lowerLeft (raw.trim_sites_nonempty hne)).1
          + 0 * (s - -(raw.trim hne).lowerLeft (raw.trim_sites_nonempty hne)).2) := rfl
  have hkey : s - -(raw.trim hne).lowerLeft (raw.trim_sites_nonempty hne) - -raw.boxOrigin hne = s + point := by
    rw [hl]; abel
  have hcongr : raw.height ⟨s - -(raw.trim hne).lowerLeft (raw.trim_sites_nonempty hne) - -raw.boxOrigin hne, hR⟩
      = raw.height ⟨s + point, hraw⟩ := by
    congr 1
    exact Subtype.ext hkey
  rw [h1, h2, hcongr]
  simp

end LowerLeft

/-! ### The transfer from the lower-left chart to the TeX chart -/

theorem height_congr_site (raw : HeightTile Site) {x y : Site} (hx : x ∈ raw.sites) (hy : y ∈ raw.sites)
    (h : x = y) : raw.height ⟨x, hx⟩ = raw.height ⟨y, hy⟩ := by
  subst h
  rfl

/-- The extension in the lower-left chart, read at the TeX point `x - (0,1)`, is a TeX-chart field with the
TeX tile values, the same kernel constant, a transverse constant shifted by the grade of `(0,1)`, and the
physical superharmonicity and recurrence of its `(0,2)`-translate. -/
theorem nearOne_transfer (raw : HeightTile Site) (hne : raw.sites.Nonempty) (S : Set Site)
    (value : Site → ℤ) {fraction : Fraction} (hint : fraction.InUnitInterval)
    (hmem : ∀ x, x ∈ raw.sites ↔ x ∈ S)
    (hheight : ∀ x (hx : x ∈ raw.sites), raw.height ⟨x, hx⟩ = value x)
    (hpoint : ((0 : ℤ), (1 : ℤ)) ∈ raw.sites)
    (hmin : ∀ site ∈ raw.sites, ((0 : ℤ), (1 : ℤ)).2 ≤ site.2 ∧
      (((0 : ℤ), (1 : ℤ)).2 = site.2 → ((0 : ℤ), (1 : ℤ)).1 ≤ site.1))
    (hcover : fraction.modifiedDeck.Covers raw.sites)
    {field : Field} {U V : ℤ}
    (hagree : ((raw.trim hne).llCenter (raw.trim_sites_nonempty hne)).Agrees field 0)
    (hper : HasGeneratorPeriods fraction field U V)
    (hsup : Superharmonic field) (hrec : Recurrent field) :
    ∃ constantU constantV : ℤ, ∃ T : Field,
      (∀ x ∈ S, T x = value x) ∧ HasGeneratorPeriods fraction T constantU constantV ∧
      (∀ other : Field, (∀ x ∈ S, other x = value x) →
        HasGeneratorPeriods fraction other constantU constantV → other = T) ∧
      Superharmonic (fun z => T (z - (0, 1))) ∧ Recurrent (fun z => T (z - (0, 1))) := by
  have hTagree : ∀ x ∈ S, field (x - (0, 1)) = value x := by
    intro x hxS
    have hx : x ∈ raw.sites := (hmem x).mpr hxS
    have hraw : x - (0, 1) + (0, 1) ∈ raw.sites := by simpa using hx
    have hs : x - (0, 1) ∈ ((raw.trim hne).llCenter (raw.trim_sites_nonempty hne)).sites :=
      (mem_llCenter_iff raw hne hpoint hmin (x - (0, 1))).mpr hraw
    have e1 := hagree ⟨x - (0, 1), hs⟩
    have e2 := llCenter_height_eq raw hne hpoint hmin (x - (0, 1)) hs hraw
    have e3 := height_congr_site raw hraw hx (by simp)
    calc field (x - (0, 1)) = field (x - (0, 1)) + 0 := (add_zero _).symm
      _ = ((raw.trim hne).llCenter (raw.trim_sites_nonempty hne)).height ⟨x - (0, 1), hs⟩ := e1.symm
      _ = raw.height ⟨x - (0, 1) + (0, 1), hraw⟩ := e2
      _ = raw.height ⟨x, hx⟩ := e3
      _ = value x := hheight x hx
  have hperT := hasGeneratorPeriods_translate (0, 1) hper
  have hevenT : EvenSite ((0, 1) + (0, 1) : Site) := by
    unfold EvenSite
    norm_num
  refine ⟨U, V + fraction.transverseGrade (0, 1), fun z => field (z - (0, 1)), ?_, hperT, ?_, ?_, ?_⟩
  · intro x hxS
    exact hTagree x hxS
  · intro other hother hperO
    apply eq_of_covered_generator_periods hint hperO hperT hcover
    intro site hsite
    show other site = field (site - (0, 1))
    rw [hother site ((hmem site).mp hsite), hTagree site ((hmem site).mp hsite)]
  · have := superharmonic_translate_even hevenT hsup
    show Superharmonic (fun z => field (z - (0, 1) - (0, 1)))
    simpa only [sub_sub] using this
  · have := recurrent_translate_even hevenT hrec
    show Recurrent (fun z => field (z - (0, 1) - (0, 1)))
    simpa only [sub_sub] using this

/-! ### The four base cases in the TeX chart -/

/-- In the TeX chart the staircase extension is the physical field translated by `(0,1)` (see the lemma's notes). -/
theorem near_staircase_base {d : ℤ} (hd : 3 ≤ d ∧ d % 2 = 1) :
    ∃ constantU constantV : ℤ, ∃ field : Field,
      (∀ x ∈ paperNearStairTile d, field x = paperNearStairValue d x) ∧
      HasGeneratorPeriods (Fraction.rotate ⟨1, d⟩) field constantU constantV ∧
      (∀ other : Field, (∀ x ∈ paperNearStairTile d, other x = paperNearStairValue d x) →
        HasGeneratorPeriods (Fraction.rotate ⟨1, d⟩) other constantU constantV → other = field) ∧
      Superharmonic (fun z => field (z - (0, 1))) ∧ Recurrent (fun z => field (z - (0, 1))) := by
  have hden : BaseMask.stairOdd.Valid d := hd
  obtain ⟨field, hagree, hperiod, _, hsuper, hrec⟩ := stairOdd_exists_recurrent_extension hden
  have hpt : ((0 : ℤ), (1 : ℤ)) ∈ (BaseMask.stairOdd.raw d).sites :=
    BaseMask.mem_stairOdd_raw_direct.mpr (by dsimp only; omega)
  have hmem : ∀ x, x ∈ (BaseMask.stairOdd.raw d).sites ↔ x ∈ paperNearStairTile d := by
    intro x
    obtain ⟨a, b⟩ := x
    rw [BaseMask.mem_stairOdd_raw_direct]
    simp only [paperNearStairTile, Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff, Prod.mk.injEq]
    constructor <;> intro h <;> omega
  have hheight : ∀ x (hx : x ∈ (BaseMask.stairOdd.raw d).sites),
      (BaseMask.stairOdd.raw d).height ⟨x, hx⟩ = paperNearStairValue d x := by
    intro x hx
    rw [BaseMask.stairOdd_raw_height_direct d ⟨x, hx⟩]
    obtain ⟨a, b⟩ := x
    simp only [paperNearStairValue, Prod.mk.injEq]
    rw [show (a - b) ^ 2 = (b - a) ^ 2 by ring]
  have hmin : ∀ site ∈ (BaseMask.stairOdd.raw d).sites,
      ((0 : ℤ), (1 : ℤ)).2 ≤ site.2 ∧ (((0 : ℤ), (1 : ℤ)).2 = site.2 → ((0 : ℤ), (1 : ℤ)).1 ≤ site.1) := by
    intro site hsite
    obtain ⟨a, b⟩ := site
    rw [BaseMask.mem_stairOdd_raw_direct] at hsite
    dsimp only at hsite ⊢
    omega
  have hcover := covers_of_place (-(BaseMask.stairOdd.raw d).boxOrigin ⟨(0, 1), hpt⟩) 0
    (stairOdd_cover hden)
  exact nearOne_transfer (BaseMask.stairOdd.raw d) ⟨(0, 1), hpt⟩ (paperNearStairTile d)
    (paperNearStairValue d) (staircase_rotate_inUnitInterval hd.1 hd.2) hmem hheight hpt hmin hcover
    hagree hperiod hsuper hrec

set_option maxHeartbeats 400000 in
theorem near_alt_staircase_base {d : ℤ} (hd : 3 ≤ d ∧ d % 2 = 1) :
    ∃ constantU constantV : ℤ, ∃ field : Field,
      (∀ x ∈ paperNearStairAltTile d, field x = paperNearStairAltValue d x) ∧
      HasGeneratorPeriods (Fraction.rotate ⟨1, d⟩) field constantU constantV ∧
      (∀ other : Field, (∀ x ∈ paperNearStairAltTile d, other x = paperNearStairAltValue d x) →
        HasGeneratorPeriods (Fraction.rotate ⟨1, d⟩) other constantU constantV → other = field) ∧
      Superharmonic (fun z => field (z - (0, 1))) ∧ Recurrent (fun z => field (z - (0, 1))) := by
  have hden : BaseMask.stairOddAlt.Valid d := hd
  obtain ⟨field, hagree, hperiod, _, hsuper, hrec⟩ := stairOddAlt_exists_recurrent_extension hden
  have hpt : ((0 : ℤ), (1 : ℤ)) ∈ (BaseMask.stairOddAlt.raw d).sites :=
    BaseMask.mem_stairOddAlt_raw_direct.mpr (by dsimp only; omega)
  have hmem : ∀ x, x ∈ (BaseMask.stairOddAlt.raw d).sites ↔ x ∈ paperNearStairAltTile d := by
    intro x
    obtain ⟨a, b⟩ := x
    rw [BaseMask.mem_stairOddAlt_raw_direct]
    simp only [paperNearStairAltTile, paperNearStairAltA, paperNearStairAltB, paperNearStairAltC,
      paperNearStairAltD, Set.mem_union, Set.mem_setOf_eq]
    constructor <;> intro h <;> omega
  have hheight : ∀ x (hx : x ∈ (BaseMask.stairOddAlt.raw d).sites),
      (BaseMask.stairOddAlt.raw d).height ⟨x, hx⟩ = paperNearStairAltValue d x := by
    intro x hx
    classical
    rw [BaseMask.stairOddAlt_raw_height_direct d ⟨x, hx⟩]
    obtain ⟨a, b⟩ := x
    rw [paperNearStairAltValue, Set.indicator_apply]
    dsimp only
    rw [show (a - b) ^ 2 = (b - a) ^ 2 by ring]
    split_ifs with h1 h2 h2 <;>
      simp only [paperNearStairAltA, paperNearStairAltB, Set.mem_union, Set.mem_setOf_eq] at h1 h2 ⊢ <;> omega
  have hmin : ∀ site ∈ (BaseMask.stairOddAlt.raw d).sites,
      ((0 : ℤ), (1 : ℤ)).2 ≤ site.2 ∧ (((0 : ℤ), (1 : ℤ)).2 = site.2 → ((0 : ℤ), (1 : ℤ)).1 ≤ site.1) := by
    intro site hsite
    obtain ⟨a, b⟩ := site
    rw [BaseMask.mem_stairOddAlt_raw_direct] at hsite
    dsimp only at hsite ⊢
    omega
  have hcover := covers_of_place (-(BaseMask.stairOddAlt.raw d).boxOrigin ⟨(0, 1), hpt⟩) 0
    (stairOddAlt_cover hden)
  exact nearOne_transfer (BaseMask.stairOddAlt.raw d) ⟨(0, 1), hpt⟩ (paperNearStairAltTile d)
    (paperNearStairAltValue d) (staircase_rotate_inUnitInterval hd.1 hd.2) hmem hheight hpt hmin hcover
    hagree hperiod hsuper hrec

set_option maxHeartbeats 400000 in
theorem near_doubled_staircase_base {d : ℤ} (hd : 4 ≤ d ∧ d % 2 = 0) :
    ∃ constantU constantV : ℤ, ∃ field : Field,
      (∀ x ∈ paperNearLadderTile d, field x = paperNearLadderValue d x) ∧
      HasGeneratorPeriods (Fraction.rotate ⟨1, d⟩) field constantU constantV ∧
      (∀ other : Field, (∀ x ∈ paperNearLadderTile d, other x = paperNearLadderValue d x) →
        HasGeneratorPeriods (Fraction.rotate ⟨1, d⟩) other constantU constantV → other = field) ∧
      Superharmonic (fun z => field (z - (0, 1))) ∧ Recurrent (fun z => field (z - (0, 1))) := by
  have hden : BaseMask.ladderEven.Valid d := hd
  obtain ⟨field, hagree, hperiod, _, hsuper, hrec⟩ := ladderEven_exists_recurrent_extension hden
  have hpt : ((0 : ℤ), (1 : ℤ)) ∈ (BaseMask.ladderEven.raw d).sites :=
    BaseMask.mem_ladderEven_raw_direct.mpr (by dsimp only; omega)
  have hmem : ∀ x, x ∈ (BaseMask.ladderEven.raw d).sites ↔ x ∈ paperNearLadderTile d := by
    intro x
    obtain ⟨a, b⟩ := x
    rw [BaseMask.mem_ladderEven_raw_direct]
    simp only [paperNearLadderTile, paperNearLadderA, paperNearLadderB, paperNearLadderC,
      paperNearLadderD, Set.mem_sdiff, Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff, Prod.mk.injEq, not_or]
    constructor <;> intro h <;> omega
  have hheight : ∀ x (hx : x ∈ (BaseMask.ladderEven.raw d).sites),
      (BaseMask.ladderEven.raw d).height ⟨x, hx⟩ = paperNearLadderValue d x := by
    intro x hx
    classical
    rw [BaseMask.ladderEven_raw_height_direct d ⟨x, hx⟩]
    obtain ⟨a, b⟩ := x
    rw [paperNearLadderValue, Set.indicator_apply]
    dsimp only
    rw [show (a - b) ^ 2 = (b - a) ^ 2 by ring]
    split_ifs with h1 h2 h2 <;>
      simp only [paperNearLadderA, paperNearLadderB, Set.mem_union, Set.mem_setOf_eq,
        Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h1 h2 ⊢ <;> omega
  have hmin : ∀ site ∈ (BaseMask.ladderEven.raw d).sites,
      ((0 : ℤ), (1 : ℤ)).2 ≤ site.2 ∧ (((0 : ℤ), (1 : ℤ)).2 = site.2 → ((0 : ℤ), (1 : ℤ)).1 ≤ site.1) := by
    intro site hsite
    obtain ⟨a, b⟩ := site
    rw [BaseMask.mem_ladderEven_raw_direct] at hsite
    dsimp only at hsite ⊢
    omega
  have hcover := covers_of_place (-(BaseMask.ladderEven.raw d).boxOrigin ⟨(0, 1), hpt⟩) 0
    (ladderEven_cover hden)
  exact nearOne_transfer (BaseMask.ladderEven.raw d) ⟨(0, 1), hpt⟩ (paperNearLadderTile d)
    (paperNearLadderValue d) (ladder_rotate_inUnitInterval hd.1 hd.2) hmem hheight hpt hmin hcover
    hagree hperiod hsuper hrec

set_option maxHeartbeats 400000 in
theorem near_doubled_alt_staircase_base {d : ℤ} (hd : 4 ≤ d ∧ d % 2 = 0) :
    ∃ constantU constantV : ℤ, ∃ field : Field,
      (∀ x ∈ paperNearLadderAltTile d, field x = paperNearLadderAltValue d x) ∧
      HasGeneratorPeriods (Fraction.rotate ⟨1, d⟩) field constantU constantV ∧
      (∀ other : Field, (∀ x ∈ paperNearLadderAltTile d, other x = paperNearLadderAltValue d x) →
        HasGeneratorPeriods (Fraction.rotate ⟨1, d⟩) other constantU constantV → other = field) ∧
      Superharmonic (fun z => field (z - (0, 1))) ∧ Recurrent (fun z => field (z - (0, 1))) := by
  have hden : BaseMask.ladderEvenAlt.Valid d := hd
  obtain ⟨field, hagree, hperiod, _, hsuper, hrec⟩ := ladderEvenAlt_exists_recurrent_extension hden
  have hpt : ((0 : ℤ), (1 : ℤ)) ∈ (BaseMask.ladderEvenAlt.raw d).sites :=
    BaseMask.mem_ladderEvenAlt_raw_direct.mpr (by dsimp only; omega)
  have hmem : ∀ x, x ∈ (BaseMask.ladderEvenAlt.raw d).sites ↔ x ∈ paperNearLadderAltTile d := by
    intro x
    obtain ⟨a, b⟩ := x
    rw [BaseMask.mem_ladderEvenAlt_raw_direct]
    simp only [paperNearLadderAltTile, paperNearLadderAltA, paperNearLadderAltB, paperNearLadderAltC,
      paperNearLadderAltD, Set.mem_sdiff, Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff, Prod.mk.injEq, not_or]
    constructor <;> intro h <;> omega
  have hheight : ∀ x (hx : x ∈ (BaseMask.ladderEvenAlt.raw d).sites),
      (BaseMask.ladderEvenAlt.raw d).height ⟨x, hx⟩ = paperNearLadderAltValue d x := by
    intro x hx
    classical
    rw [BaseMask.ladderEvenAlt_raw_height_direct d ⟨x, hx⟩]
    obtain ⟨a, b⟩ := x
    rw [paperNearLadderAltValue, Set.indicator_apply]
    dsimp only
    rw [show (a - b) ^ 2 = (b - a) ^ 2 by ring]
    split_ifs with h1 h2 h2 <;>
      simp only [paperNearLadderAltA, paperNearLadderAltB, Set.mem_union, Set.mem_setOf_eq,
        Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h1 h2 ⊢ <;> omega
  have hmin : ∀ site ∈ (BaseMask.ladderEvenAlt.raw d).sites,
      ((0 : ℤ), (1 : ℤ)).2 ≤ site.2 ∧ (((0 : ℤ), (1 : ℤ)).2 = site.2 → ((0 : ℤ), (1 : ℤ)).1 ≤ site.1) := by
    intro site hsite
    obtain ⟨a, b⟩ := site
    rw [BaseMask.mem_ladderEvenAlt_raw_direct] at hsite
    dsimp only at hsite ⊢
    omega
  have hcover := covers_of_place (-(BaseMask.ladderEvenAlt.raw d).boxOrigin ⟨(0, 1), hpt⟩) 0
    (ladderEvenAlt_cover hden)
  exact nearOne_transfer (BaseMask.ladderEvenAlt.raw d) ⟨(0, 1), hpt⟩ (paperNearLadderAltTile d)
    (paperNearLadderAltValue d) (ladder_rotate_inUnitInterval hd.1 hd.2) hmem hheight hpt hmin hcover
    hagree hperiod hsuper hrec

/-- The chart issue of `lemma:basecase_2k_odd_std`: in the TeX coordinates the extension is not superharmonic
at `(0,2)` for `d = 3`, since the kernel period forces the value `-1` at `(-1,2)`. -/
theorem near_staircase_tex_chart_laplacian (field : Field) {constantU constantV : ℤ}
    (hagree : ∀ x ∈ paperNearStairTile 3, field x = paperNearStairValue 3 x)
    (hperiod : HasGeneratorPeriods (Fraction.rotate ⟨1, 3⟩) field constantU constantV) :
    laplacian field (0, 2) = 1 := by
  have hk : (Fraction.rotate ⟨1, 3⟩).modifiedDeck.kernel = (4, 2) := by decide
  have h02 := hperiod.1 (0, 2)
  have hm12 := hperiod.1 (-1, 2)
  rw [hk] at h02 hm12
  have e1 : ((0 : ℤ), (2 : ℤ)) + ((4 : ℤ), (2 : ℤ)) = ((4 : ℤ), (4 : ℤ)) := by norm_num
  have e2 : ((-1 : ℤ), (2 : ℤ)) + ((4 : ℤ), (2 : ℤ)) = ((3 : ℤ), (4 : ℤ)) := by norm_num
  rw [e1] at h02
  rw [e2] at hm12
  have a44 := hagree (4, 4) (Or.inl (by norm_num))
  have a34 := hagree (3, 4) (Or.inl (by norm_num))
  have a02 := hagree (0, 2) (Or.inl (by norm_num))
  have a12 := hagree (1, 2) (Or.inl (by norm_num))
  unfold paperNearStairValue at a44 a34 a02 a12
  norm_num at a44 a34 a02 a12
  have hneg : incomingNeg ((0 : ℤ), (2 : ℤ)) = ((-1 : ℤ), (2 : ℤ)) := by
    norm_num [incomingNeg, EvenSite]
  have hpos : incomingPos ((0 : ℤ), (2 : ℤ)) = ((1 : ℤ), (2 : ℤ)) := by
    norm_num [incomingPos, EvenSite]
  unfold laplacian
  rw [hneg, hpos]
  omega

end FLatticePaper.Construction
