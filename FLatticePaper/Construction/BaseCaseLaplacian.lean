import FLatticePaper.Construction.BaseCaseRecurrence
import FLatticePaper.Construction.StaircaseExtension
import FLatticePaper.Construction.StaircaseLaplacian
import FLatticePaper.Construction.StaircaseCoverage
import FLatticePaper.Construction.AlternateStaircaseExtension
import FLatticePaper.Construction.AlternateStaircaseLaplacian
import FLatticePaper.Construction.LadderRank
import FLatticePaper.Construction.LadderCoverage
import FLatticePaper.Construction.LadderLaplacian
import FLatticePaper.Construction.AlternateLadderLaplacian
import FLatticePaper.Construction.AlternateLadderRank

/-! The Section 6 Laplacian formulas `lemma:staircase_laplacian` and `lemma:doubled_staircase_laplacian`, in the
paper's notation. The tiles and heights are those of `BaseCaseRecurrence`. -/

namespace FLatticePaper.Construction

open Farey

set_option maxHeartbeats 400000 in
set_option maxHeartbeats 400000 in
set_option maxHeartbeats 400000 in
/-- `∂⁻T`, the sites of `T` with a lattice neighbour outside `T` (line 2312). -/
def innerBoundary (T : Set Site) : Set Site :=
  {x | x ∈ T ∧ ((x.1 + 1, x.2) ∉ T ∨ (x.1 - 1, x.2) ∉ T ∨ (x.1, x.2 + 1) ∉ T ∨ (x.1, x.2 - 1) ∉ T)}

/-! ### Helpers -/

/-- A field that agrees with a paper value on a tile agrees with the raw tile at gauge zero. -/
private theorem agrees_of_paper {tile : Set Site} {raw : HeightTile Site} {value : Site → ℤ} {field : Field}
    (hmem : ∀ x, x ∈ tile ↔ x ∈ raw.sites)
    (hheight : ∀ x (hx : x ∈ raw.sites), raw.height ⟨x, hx⟩ = value x)
    (hfield : ∀ x ∈ tile, field x = value x) : raw.Agrees field 0 := by
  intro site
  have hx : site.1 ∈ tile := (hmem site.1).mpr site.2
  have h1 : raw.height ⟨site.1, site.2⟩ = value site.1 := hheight site.1 site.2
  have h2 : field site.1 = value site.1 := hfield site.1 hx
  show raw.height site = field site.1 + 0
  rw [add_zero, h2]
  exact h1

/-- A field that agrees with a raw tile at gauge zero takes the paper value on the paper tile. -/
private theorem values_of_agrees {tile : Set Site} {raw : HeightTile Site} {value : Site → ℤ} {g : Field}
    (hmem : ∀ x, x ∈ tile ↔ x ∈ raw.sites)
    (hheight : ∀ x (hx : x ∈ raw.sites), raw.height ⟨x, hx⟩ = value x)
    (hagree : raw.Agrees g 0) : ∀ x ∈ tile, g x = value x := by
  intro x hx
  have hx' : x ∈ raw.sites := (hmem x).mp hx
  have h1 : raw.height ⟨x, hx'⟩ = g x + 0 := hagree ⟨x, hx'⟩
  have h2 : raw.height ⟨x, hx'⟩ = value x := hheight x hx'
  omega

/-- Two fields with prescribed generator periods agreeing on a tile have equal constants, once the tile
contains a kernel pair and a transverse pair. -/
private theorem constants_eq {fraction : Fraction} {tile : Set Site} {f g : Field}
    {cU cV cU' cV' : ℤ} (hf : HasGeneratorPeriods fraction f cU cV)
    (hg : HasGeneratorPeriods fraction g cU' cV') (hagree : ∀ x ∈ tile, f x = g x)
    {p q r s : Site} (hp : p ∈ tile) (hq : q ∈ tile) (hpq : p + fraction.modifiedDeck.kernel = q)
    (hr : r ∈ tile) (hs : s ∈ tile) (hrs : r + fraction.modifiedDeck.transverse = s) :
    cU = cU' ∧ cV = cV' := by
  have hU1 := hf.1 p
  rw [hpq] at hU1
  have hU2 := hg.1 p
  rw [hpq] at hU2
  have hV1 := hf.2 r
  rw [hrs] at hV1
  have hV2 := hg.2 r
  rw [hrs] at hV2
  have a1 := hagree q hq
  have a2 := hagree p hp
  have a3 := hagree s hs
  have a4 := hagree r hr
  constructor <;> linarith

/-- Two fields with the same generator periods that agree on the covered raw sites are equal. -/
private theorem field_eq {fraction : Fraction} (hinterval : fraction.InUnitInterval) {tile : Set Site}
    {raw : HeightTile Site} {f g : Field} {cU cV : ℤ} (hmem : ∀ x, x ∈ tile ↔ x ∈ raw.sites)
    (hcover : fraction.modifiedDeck.Covers raw.sites)
    (hf : HasGeneratorPeriods fraction f cU cV) (hg : HasGeneratorPeriods fraction g cU cV)
    (hagree : ∀ x ∈ tile, f x = g x) : f = g :=
  eq_of_covered_generator_periods hinterval hf hg hcover fun site hsite =>
    hagree site ((hmem site).mpr hsite)

/-- The periods of `1/d` put the kernel and transverse vectors in the span of the modified deck. -/
private theorem periodic_of_generatorPeriods {fraction : Fraction} (hinterval : fraction.InUnitInterval)
    {field : Field} {cU cV : ℤ} (hperiod : HasGeneratorPeriods fraction field cU cV) :
    (∀ x, laplacian field (x + fraction.modifiedDeck.kernel) = laplacian field x) ∧
      (∀ x, laplacian field (x + fraction.modifiedDeck.transverse) = laplacian field x) :=
  ⟨laplacian_periodic_of_generatorPeriods hinterval hperiod ⟨1, 0, by simp [PeriodDeck.combine]⟩,
    laplacian_periodic_of_generatorPeriods hinterval hperiod ⟨0, 1, by simp [PeriodDeck.combine]⟩⟩

/-- The fraction `1/d` lies in the unit interval for `d ≥ 1`. -/
private theorem interval_mk_one (d : ℤ) (hd : 1 ≤ d) : (Fraction.mk 1 d).InUnitInterval :=
  ⟨by dsimp; omega, by change (0 : ℤ) ≤ 1; decide, by dsimp; omega⟩

/-- A site of `∂⁻T` is in `T`, and every neighbour of a site of `T` outside `∂⁻T` is in `T`. -/
private theorem nbrs_of_not_boundary {T : Set Site} {x : Site} (hx : x ∈ T) (hb : x ∉ innerBoundary T) :
    (x.1 + 1, x.2) ∈ T ∧ (x.1 - 1, x.2) ∈ T ∧ (x.1, x.2 + 1) ∈ T ∧ (x.1, x.2 - 1) ∈ T := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra h
    exact hb ⟨hx, Or.inl h⟩
  · by_contra h
    exact hb ⟨hx, Or.inr (Or.inl h)⟩
  · by_contra h
    exact hb ⟨hx, Or.inr (Or.inr (Or.inl h))⟩
  · by_contra h
    exact hb ⟨hx, Or.inr (Or.inr (Or.inr h))⟩

/-! ### Standard even staircase -/

/-- The standard even tile at integer coordinates. -/
private def stairP (d a b : ℤ) : Prop :=
  (2 - d ≤ a ∧ a ≤ d) ∧ (0 ≤ b ∧ b ≤ d + 1) ∧
    ((a = 0 ∧ b = 0) ∨ (a = 2 ∧ b = d + 1) ∨ (1 ≤ a + b ∧ a + b ≤ d + 2))

private theorem stairP_iff {d a b : ℤ} :
    (a, b) ∈ (BaseMask.stairEven.raw d).sites ↔ stairP d a b := by
  rw [BaseMask.mem_stairEven_raw_iff]
  simp only [stairP, BaseMask.StairEvenCorner, or_assoc]

private theorem mem_tile_of_stairP {d a b : ℤ} (hd : 3 ≤ d) (h : stairP d a b) :
    (a, b) ∈ paperStairTile d :=
  (mem_paperStairTile_iff d hd (a, b)).mpr (stairP_iff.mpr h)

private theorem stairP_of_mem {d a b : ℤ} (hd : 3 ≤ d) (h : (a, b) ∈ paperStairTile d) :
    stairP d a b :=
  stairP_iff.mp ((mem_paperStairTile_iff d hd (a, b)).mp h)

/-- Odd sites of the standard tile whose four neighbours are in the tile lie in the interior window. -/
private theorem stairP_interior_of_odd {d a b : ℤ} (hodd : d % 2 = 1)
    (hpar : (a + b) % 2 = 1) (h1 : stairP d (a + 1) b) (h2 : stairP d (a - 1) b)
    (h3 : stairP d a (b + 1)) (h4 : stairP d a (b - 1)) :
    0 < b ∧ b < d + 1 ∧ 1 < a + b ∧ a + b < d + 2 := by
  unfold stairP at *
  omega

/-- Odd interior sites of the standard tile have all four neighbours in the tile. -/
private theorem stairP_nbrs_of_interior {d a b : ℤ} (hodd : d % 2 = 1) (h0 : stairP d a b)
    (hpar : (a + b) % 2 = 1) (hint : 0 < b ∧ b < d + 1 ∧ 1 < a + b ∧ a + b < d + 2) :
    stairP d (a + 1) b ∧ stairP d (a - 1) b ∧ stairP d a (b + 1) ∧ stairP d a (b - 1) := by
  unfold stairP at *
  omega

/-- Even sites of the standard tile in column one have all four neighbours in the tile. -/
private theorem stairP_nbrs_of_even_one {d a b : ℤ} (hd : 3 ≤ d) (hodd : d % 2 = 1) (h0 : stairP d a b)
    (hpar : (a + b) % 2 = 0) (ha : a = 1) :
    stairP d (a + 1) b ∧ stairP d (a - 1) b ∧ stairP d a (b + 1) ∧ stairP d a (b - 1) := by
  unfold stairP at *
  omega

/-- The standard lemma `lemma:staircase_laplacian`, with the periodicity, the interior formula and the boundary
value. -/
theorem staircase_laplacian {d : ℤ} (hd : 3 ≤ d ∧ d % 2 = 1) {field : Field} {constantU constantV : ℤ}
    (hagree : ∀ x ∈ paperStairTile d, field x = paperStairValue d x)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 d) field constantU constantV) :
    (∀ x, laplacian field (x + (Fraction.mk 1 d).modifiedDeck.kernel) = laplacian field x ∧
      laplacian field (x + (Fraction.mk 1 d).modifiedDeck.transverse) = laplacian field x) ∧
    (∀ x ∈ paperStairTile d \ innerBoundary (paperStairTile d),
      laplacian field x = -(if (x.1 + x.2) % 2 = 1 then 1 else 0) -
        (if (x.1 + x.2) % 2 = 0 ∧ x.1 = 1 then 1 else 0)) ∧
    (∀ x ∈ innerBoundary (paperStairTile d), laplacian field x = 0) := by
  have hden : BaseMask.stairEven.Valid d := ⟨hd.1, hd.2⟩
  have hd1 : 3 ≤ d := hd.1
  obtain ⟨ref, hrefA, hrefP, -⟩ := stairEven_exists_extension hden
  have hrefTile := values_of_agrees (mem_paperStairTile_iff d hd1) (stairEven_height_paper d) hrefA
  have hagreeRef : ∀ x ∈ paperStairTile d, field x = ref x := fun x hx =>
    (hagree x hx).trans (hrefTile x hx).symm
  -- the kernel and transverse vectors of 1/d
  have hk : (Fraction.mk 1 d).modifiedDeck.kernel = (d, 1) :=
    congrArg PeriodDeck.kernel (reciprocalEvenDeck_eq hd.2)
  have ht : (Fraction.mk 1 d).modifiedDeck.transverse = (1 - d, 1 + d) :=
    congrArg PeriodDeck.transverse (reciprocalEvenDeck_eq hd.2)
  have hinterval := interval_mk_one d (by omega)
  obtain ⟨hU, hV⟩ := constants_eq hperiod hrefP hagreeRef
    (mem_tile_of_stairP (a := 2 - d) (b := d - 1) hd1 (by unfold stairP; omega))
    (mem_tile_of_stairP (a := 2) (b := d) hd1 (by unfold stairP; omega))
    (by rw [hk]; exact Prod.ext (show 2 - d + d = 2 by ring) (show d - 1 + 1 = d by ring))
    (mem_tile_of_stairP (a := d) (b := 0) hd1 (by unfold stairP; omega))
    (mem_tile_of_stairP (a := 1) (b := d + 1) hd1 (by unfold stairP; omega))
    (by rw [ht]; exact Prod.ext (show d + (1 - d) = 1 by ring) (show 0 + (1 + d) = d + 1 by ring))
  rw [hU, hV] at hperiod
  have hagreeRaw : (BaseMask.stairEven.raw d).Agrees field 0 :=
    agrees_of_paper (mem_paperStairTile_iff d hd1) (stairEven_height_paper d) hagree
  have htable : ∀ x ∈ paperStairTile d, laplacian field x =
      if EvenSite x then (if x.1 = 1 then -1 else 0)
      else (if 0 < x.2 ∧ x.2 < d + 1 ∧ 1 < x.1 + x.2 ∧ x.1 + x.2 < d + 2 then -1 else 0) := fun x hx =>
    stairEven_laplacian_on_raw hden hagreeRaw hperiod x ((mem_paperStairTile_iff d hd1 x).mp hx)
  obtain ⟨hpK, hpT⟩ := periodic_of_generatorPeriods hinterval hperiod
  refine ⟨fun x => ⟨hpK x, hpT x⟩, ?_, ?_⟩
  · rintro ⟨a, b⟩ hx
    have hT := hx.1
    have hn := nbrs_of_not_boundary hT hx.2
    have h0 := stairP_of_mem hd1 hT
    dsimp only at hn
    obtain ⟨n1, n2, n3, n4⟩ := hn
    have hS1 := stairP_of_mem hd1 n1
    have hS2 := stairP_of_mem hd1 n2
    have hS3 := stairP_of_mem hd1 n3
    have hS4 := stairP_of_mem hd1 n4
    rw [htable (a, b) hT]
    dsimp only [EvenSite]
    by_cases hev : (a + b) % 2 = 0
    · split_ifs <;> omega
    · have hint := stairP_interior_of_odd hd.2 (by omega) hS1 hS2 hS3 hS4
      split_ifs
      all_goals omega
  · rintro ⟨a, b⟩ hx
    obtain ⟨hT, hb⟩ := hx
    have h0 := stairP_of_mem hd1 hT
    have hnot : ¬ (stairP d (a + 1) b ∧ stairP d (a - 1) b ∧ stairP d a (b + 1) ∧ stairP d a (b - 1)) := by
      rintro ⟨n1, n2, n3, n4⟩
      rcases hb with h | h | h | h
      · exact h (mem_tile_of_stairP hd1 n1)
      · exact h (mem_tile_of_stairP hd1 n2)
      · exact h (mem_tile_of_stairP hd1 n3)
      · exact h (mem_tile_of_stairP hd1 n4)
    rw [htable (a, b) hT]
    dsimp only [EvenSite]
    by_cases hev : (a + b) % 2 = 0
    · have hne : a ≠ 1 := fun ha => hnot (stairP_nbrs_of_even_one hd1 hd.2 h0 hev ha)
      split_ifs
      all_goals omega
    · have hnint : ¬ (0 < b ∧ b < d + 1 ∧ 1 < a + b ∧ a + b < d + 2) := fun hint =>
        hnot (stairP_nbrs_of_interior hd.2 h0 (by omega) hint)
      split_ifs
      all_goals omega


/-! ### Alternate even staircase -/

/-- The alternate even tile at integer coordinates, as in `lemma:basecase_3k_even_alt`. -/
private def altP (d a b : ℤ) : Prop :=
  (4 - 2 * d ≤ a ∧ a ≤ d) ∧ (-1 ≤ b ∧ b ≤ d + 1) ∧
    ((0 ≤ b ∧ b ≤ d ∧ 2 - d ≤ a + b ∧ a + b ≤ d + 2) ∨ (b = -1 ∧ 1 - d ≤ a ∧ a ≤ 0) ∨
      (b = d + 1 ∧ 4 - d ≤ a ∧ a ≤ 3) ∨ (a = 1 - d ∧ b = 0) ∨ (a = 3 ∧ b = d))

private theorem altP_iff {d a b : ℤ} :
    (a, b) ∈ (BaseMask.stairEvenAlt.raw d).sites ↔ altP d a b := by
  rw [BaseMask.mem_stairEvenAlt_raw_iff]
  simp only [altP]

private theorem mem_tile_of_altP {d a b : ℤ} (hd : 3 ≤ d) (h : altP d a b) :
    (a, b) ∈ paperStairAltTile d :=
  (mem_paperStairAltTile_iff d hd (a, b)).mpr (altP_iff.mpr h)

private theorem altP_of_mem {d a b : ℤ} (hd : 3 ≤ d) (h : (a, b) ∈ paperStairAltTile d) :
    altP d a b :=
  altP_iff.mp ((mem_paperStairAltTile_iff d hd (a, b)).mp h)

/-- Prove `altP d a b` by choosing the piece of the tile that holds. -/
local macro "altP_tac" : tactic =>
  `(tactic| (unfold altP; refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;>
    first
    | (left; omega)
    | (right; left; omega)
    | (right; right; left; omega)
    | (right; right; right; left; omega)
    | (right; right; right; right; omega)
    | omega))

/-- Prove the charge-zero condition by choosing the item of `StairEvenAltOddWhite` that holds. -/
local macro "altW_tac" : tactic =>
  `(tactic| (simp only [StairEvenAltOddWhite] <;>
    first
    | (left; omega)
    | (right; left; omega)
    | (right; right; left; omega)
    | (right; right; right; left; omega)
    | (right; right; right; right; left; omega)
    | (right; right; right; right; right; left; omega)
    | (right; right; right; right; right; right; left; omega)
    | (right; right; right; right; right; right; right; omega)))

/-- On an even interior site of the alternate tile, charge one is the interior charge-one list. -/
private theorem alt_evenBlack_iff_interior {d a b : ℤ} (hodd : d % 2 = 1)
    (h1 : altP d (a + 1) b) (h2 : altP d (a - 1) b) (hev : (a + b) % 2 = 0) :
    StairEvenAltEvenBlack d (a, b) ↔ (1 ≤ b ∧ b ≤ d - 1 ∧ (a = 2 - d ∨ a = 2 ∨ a + b = 2)) := by
  constructor
  · intro hE
    simp only [StairEvenAltEvenBlack] at hE
    rcases hE with hE | hE | hE
    · exact hE
    · exfalso
      unfold altP at h2
      omega
    · exfalso
      unfold altP at h1
      omega
  · intro h
    simp only [StairEvenAltEvenBlack]
    omega

/-- On an odd interior site of the alternate tile, the charge-zero sites are the interior ones of
formula (6). -/
private theorem alt_oddWhite_iff_interior {d a b : ℤ} (hd : 3 ≤ d) (hodd : d % 2 = 1)
    (h1 : altP d (a + 1) b) (h2 : altP d (a - 1) b) (h3 : altP d a (b + 1))
    (h4 : altP d a (b - 1)) (hpar : (a + b) % 2 = 1) :
    StairEvenAltOddWhite d (a, b) ↔
      ((a + b = 1 ∧ 1 ≤ b ∧ b ≤ d - 2) ∨ (a + b = 3 ∧ 2 ≤ b ∧ b ≤ d - 1)) := by
  constructor
  · intro hW
    simp only [StairEvenAltOddWhite] at hW
    rcases hW with h | h | h | h | h | h | h | h
    · exfalso; unfold altP at h4; omega
    · exfalso; unfold altP at h3; omega
    · exfalso; unfold altP at h4; omega
    · exfalso; unfold altP at h3; omega
    · exfalso; unfold altP at h2; omega
    · exfalso; unfold altP at h1; omega
    · rcases (show b = 0 ∨ 1 ≤ b by omega) with hb0 | hb1
      · exfalso
        unfold altP at h4
        omega
      · exact Or.inl ⟨by omega, hb1, by omega⟩
    · rcases (show b = d ∨ b ≤ d - 1 by omega) with hbd | hbd
      · exfalso
        unfold altP at h3
        omega
      · exact Or.inr ⟨by omega, by omega, hbd⟩
  · intro h
    rcases h with h | h <;> altW_tac

set_option maxHeartbeats 400000 in
/-- An even boundary site of the alternate tile with charge one is one of the two boundary sites of
`lemma:alt-staircase-laplacian`. -/
private theorem alt_evenBlack_boundary {d a b : ℤ} (hd : 3 ≤ d) (hodd : d % 2 = 1) (h0 : altP d a b)
    (hbd : ¬ (altP d (a + 1) b ∧ altP d (a - 1) b ∧ altP d a (b + 1) ∧ altP d a (b - 1)))
    (hev : (a + b) % 2 = 0) (hE : StairEvenAltEvenBlack d (a, b)) :
    (a = 1 - d ∧ b = 0) ∨ (a = 3 ∧ b = d) := by
  by_contra hne
  apply hbd
  unfold altP at h0
  obtain ⟨r1, r2, hp⟩ := h0
  simp only [StairEvenAltEvenBlack] at hE
  rcases hp with hp | hp | hp | hp | hp
  all_goals first
    | (exfalso; omega)
    | (refine ⟨?_, ?_, ?_, ?_⟩ <;> altP_tac)

set_option maxHeartbeats 400000 in
/-- An odd boundary site of the alternate tile is a charge-zero site. -/
private theorem alt_oddWhite_boundary {d a b : ℤ} (hd : 3 ≤ d) (hodd : d % 2 = 1) (h0 : altP d a b)
    (hbd : ¬ (altP d (a + 1) b ∧ altP d (a - 1) b ∧ altP d a (b + 1) ∧ altP d a (b - 1)))
    (hpar : (a + b) % 2 = 1) : StairEvenAltOddWhite d (a, b) := by
  by_contra hW
  apply hbd
  unfold altP at h0
  obtain ⟨r1, r2, hp⟩ := h0
  simp only [StairEvenAltOddWhite] at hW
  rcases hp with hp | hp | hp | hp | hp
  all_goals first
    | (exfalso; omega)
    | (refine ⟨?_, ?_, ?_, ?_⟩ <;> altP_tac)


set_option maxHeartbeats 400000 in
/-- `lemma:alt-staircase-laplacian` (`paper/farey_recursion.tex` lines 2324–2337), with the periodicity, the
interior formula and the boundary value. -/
theorem alt_staircase_laplacian {d : ℤ} (hd : 3 ≤ d ∧ d % 2 = 1) {field : Field} {constantU constantV : ℤ}
    (hagree : ∀ x ∈ paperStairAltTile d, field x = paperStairAltValue d x)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 d) field constantU constantV) :
    (∀ x, laplacian field (x + (Fraction.mk 1 d).modifiedDeck.kernel) = laplacian field x ∧
      laplacian field (x + (Fraction.mk 1 d).modifiedDeck.transverse) = laplacian field x) ∧
    (∀ x ∈ paperStairAltTile d \ innerBoundary (paperStairAltTile d),
      laplacian field x = -(if (x.1 + x.2) % 2 = 1 then 1 else 0) -
        (if (x.1 + x.2) % 2 = 0 ∧ ((x.1 = -(d - 2) ∧ 0 ≤ x.2 ∧ x.2 ≤ d - 1) ∨ (x.1 = 2 ∧ 1 ≤ x.2 ∧ x.2 ≤ d))
          then 1 else 0) -
        (if x.1 + x.2 = 2 ∧ 1 ≤ x.2 ∧ x.2 ≤ d - 1 then 1 else 0) +
        (if x.1 + x.2 = 1 ∧ 1 ≤ x.2 ∧ x.2 ≤ d - 2 then 1 else 0) +
        (if x.1 + x.2 = 3 ∧ 2 ≤ x.2 ∧ x.2 ≤ d - 1 then 1 else 0)) ∧
    (∀ x ∈ innerBoundary (paperStairAltTile d),
      laplacian field x = -(if x = (1 - d, 0) ∨ x = (3, d) then 1 else 0)) := by
  have hd1 : 3 ≤ d := hd.1
  have hden : BaseMask.stairEvenAlt.Valid d := ⟨hd.1, hd.2⟩
  have hdenS : BaseMask.stairEven.Valid d := ⟨hd.1, hd.2⟩
  obtain ⟨standard, hstdA, hstdP, -⟩ := stairEven_exists_extension hdenS
  have hgP := stairEvenAltField_periods hstdP
  have hgA := stairEvenAltField_agrees hden hstdA hstdP
  have hgTile := values_of_agrees (mem_paperStairAltTile_iff d hd1) (stairEvenAlt_height_paper d) hgA
  have hagreeG : ∀ x ∈ paperStairAltTile d, field x = stairEvenAltField d standard x :=
    fun x hx => (hagree x hx).trans (hgTile x hx).symm
  have hk : (Fraction.mk 1 d).modifiedDeck.kernel = (d, 1) :=
    congrArg PeriodDeck.kernel (reciprocalEvenDeck_eq hd.2)
  have ht : (Fraction.mk 1 d).modifiedDeck.transverse = (1 - d, 1 + d) :=
    congrArg PeriodDeck.transverse (reciprocalEvenDeck_eq hd.2)
  obtain ⟨hU, hV⟩ := constants_eq hperiod hgP hagreeG
    (mem_tile_of_altP (a := 1 - d) (b := 0) hd1 (by altP_tac))
    (mem_tile_of_altP (a := 1) (b := 1) hd1 (by altP_tac))
    (by rw [hk]; exact Prod.ext (show 1 - d + d = 1 by ring) (show 0 + 1 = 1 by ring))
    (mem_tile_of_altP (a := 0) (b := -1) hd1 (by altP_tac))
    (mem_tile_of_altP (a := 1 - d) (b := d) hd1 (by altP_tac))
    (by rw [ht]; exact Prod.ext (show 0 + (1 - d) = 1 - d by ring) (show -1 + (1 + d) = d by ring))
  rw [hU, hV] at hperiod
  have hinterval := interval_mk_one d (by omega)
  have hfg : field = stairEvenAltField d standard :=
    field_eq hinterval (mem_paperStairAltTile_iff d hd1) (stairEvenAlt_raw_cover hden) hperiod hgP hagreeG
  subst hfg
  have htable : ∀ x ∈ paperStairAltTile d, laplacian (stairEvenAltField d standard) x =
      if EvenSite x then (if StairEvenAltEvenBlack d x then -1 else 0)
      else (if StairEvenAltOddWhite d x then 0 else -1) := fun x hx =>
    stairEvenAlt_laplacian_on_raw hden hstdA hstdP x ((mem_paperStairAltTile_iff d hd1 x).mp hx)
  obtain ⟨hpK, hpT⟩ := periodic_of_generatorPeriods hinterval hperiod
  refine ⟨fun x => ⟨hpK x, hpT x⟩, ?_, ?_⟩
  · rintro ⟨a, b⟩ hx
    have hT : (a, b) ∈ paperStairAltTile d := hx.1
    have hn := nbrs_of_not_boundary hT hx.2
    dsimp only at hn
    obtain ⟨n1, n2, n3, n4⟩ := hn
    have h0 := altP_of_mem hd1 hT
    have s1 := altP_of_mem hd1 n1
    have s2 := altP_of_mem hd1 n2
    have s3 := altP_of_mem hd1 n3
    have s4 := altP_of_mem hd1 n4
    rw [htable (a, b) hT]
    dsimp only [EvenSite]
    by_cases hev : (a + b) % 2 = 0
    · rw [if_pos hev]
      simp only [alt_evenBlack_iff_interior hd.2 s1 s2 hev]
      split_ifs
      all_goals omega
    · rw [if_neg hev]
      simp only [alt_oddWhite_iff_interior hd1 hd.2 s1 s2 s3 s4 (by omega)]
      split_ifs
      all_goals omega
  · rintro ⟨a, b⟩ hx
    obtain ⟨hT, hb⟩ := hx
    have h0 := altP_of_mem hd1 hT
    have hbd : ¬ (altP d (a + 1) b ∧ altP d (a - 1) b ∧ altP d a (b + 1) ∧ altP d a (b - 1)) := by
      rintro ⟨n1, n2, n3, n4⟩
      rcases hb with h | h | h | h
      · exact h (mem_tile_of_altP hd1 n1)
      · exact h (mem_tile_of_altP hd1 n2)
      · exact h (mem_tile_of_altP hd1 n3)
      · exact h (mem_tile_of_altP hd1 n4)
    rw [htable (a, b) hT]
    dsimp only [EvenSite]
    simp only [Prod.mk.injEq]
    by_cases hev : (a + b) % 2 = 0
    · rw [if_pos hev]
      by_cases hE : StairEvenAltEvenBlack d (a, b)
      · have hpt := alt_evenBlack_boundary hd1 hd.2 h0 hbd hev hE
        rw [if_pos hE]
        split_ifs
        all_goals omega
      · rw [if_neg hE]
        have hn : ¬ ((a = 1 - d ∧ b = 0) ∨ (a = 3 ∧ b = d)) := fun h => hE (by
          simp only [StairEvenAltEvenBlack]
          omega)
        split_ifs
        all_goals omega
    · rw [if_neg hev]
      have hW := alt_oddWhite_boundary hd1 hd.2 h0 hbd (by omega)
      rw [if_pos hW]
      split_ifs
      all_goals omega


/-! ### Standard odd doubled staircase -/

/-- The B5 tile at integer coordinates, as in `lemma:basecase_3k_odd_std`. -/
private def ladP5 (d a b : ℤ) : Prop :=
  (2 - d ≤ a ∧ a ≤ 2 * d) ∧ (0 ≤ b ∧ b ≤ d + 2) ∧
    ((a = 0 ∧ b = 0) ∨ (a = d + 2 ∧ b = d + 2) ∨
      (1 ≤ a + b ∧ a + b ≤ 2 * d + 3 ∧ ¬((b = 0 ∧ d ≤ a) ∨ (b = d + 2 ∧ a ≤ 2))))

private theorem ladP5_iff {d a b : ℤ} :
    (a, b) ∈ (BaseMask.ladderOdd.raw d).sites ↔ ladP5 d a b := by
  rw [BaseMask.mem_ladderOdd_raw_iff]
  simp only [ladP5, BaseMask.LadderOddCorner, or_assoc]

private theorem mem_tile_of_ladP5 {d a b : ℤ} (hd : 4 ≤ d) (h : ladP5 d a b) :
    (a, b) ∈ paperLadderTile d :=
  (mem_paperLadderTile_iff d hd (a, b)).mpr (ladP5_iff.mpr h)

private theorem ladP5_of_mem {d a b : ℤ} (hd : 4 ≤ d) (h : (a, b) ∈ paperLadderTile d) :
    ladP5 d a b :=
  ladP5_iff.mp ((mem_paperLadderTile_iff d hd (a, b)).mp h)

/-- Prove `ladP5 d a b` by choosing the piece of the tile that holds. -/
local macro "ladP5_tac" : tactic =>
  `(tactic| (unfold ladP5; refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;>
    first
    | (left; omega)
    | (right; left; omega)
    | (right; right; omega)
    | omega))

/-- Prove the B5 charge-zero condition by choosing the item that holds. -/
local macro "ladW5_tac" : tactic =>
  `(tactic| (simp only [LadderOddOddWhite, LadderOddLowerBoundary, reflectLadderOdd, Prod.fst_sub,
      Prod.snd_sub, or_assoc] <;>
    first
    | (left; omega)
    | (right; left; omega)
    | (right; right; left; omega)
    | (right; right; right; left; omega)
    | (right; right; right; right; left; omega)
    | (right; right; right; right; right; left; omega)
    | (right; right; right; right; right; right; left; omega)
    | (right; right; right; right; right; right; right; left; omega)
    | (right; right; right; right; right; right; right; right; left; omega)
    | (right; right; right; right; right; right; right; right; right; omega)))

/-- On an even B5 site the charge-one list is the parity restriction of the interior list. -/
private theorem ladder5_evenBlack_iff {d a b : ℤ} (hodd : d % 2 = 0) (hev : (a + b) % 2 = 0) :
    LadderOddEvenBlack d (a, b) ↔
      ((a = 1 ∧ 1 ≤ b ∧ b ≤ d) ∨ (a = d + 1 ∧ 2 ≤ b ∧ b ≤ d + 1) ∨ (a + b = d + 2 ∧ 2 ≤ b ∧ b ≤ d)) := by
  simp only [LadderOddEvenBlack]
  constructor <;> intro h <;> omega

set_option maxHeartbeats 400000 in
/-- On an odd interior site of B5, the charge-zero sites are the interior odd sites of formula (6). -/
private theorem ladder5_oddWhite_iff_interior {d a b : ℤ} (hd : 4 ≤ d) (hodd : d % 2 = 0)
    (h1 : ladP5 d (a + 1) b) (h2 : ladP5 d (a - 1) b) (h3 : ladP5 d a (b + 1))
    (h4 : ladP5 d a (b - 1)) (hpar : (a + b) % 2 = 1) :
    LadderOddOddWhite d (a, b) ↔
      ((a + b = d + 3 ∧ 3 ≤ b ∧ b ≤ d) ∨ (a + b = d + 1 ∧ 2 ≤ b ∧ b ≤ d - 1)) := by
  constructor
  · intro hW
    simp only [LadderOddOddWhite, LadderOddLowerBoundary, reflectLadderOdd, Prod.fst_sub,
      Prod.snd_sub, or_assoc] at hW
    rcases hW with h | h | h | h | h | h | h | h | h | h
    · exfalso
      unfold ladP5 at h4
      omega
    · exfalso
      unfold ladP5 at h4
      omega
    · exfalso
      unfold ladP5 at h4
      omega
    · exfalso
      unfold ladP5 at h1
      omega
    · exfalso
      unfold ladP5 at h3
      omega
    · exfalso
      unfold ladP5 at h3
      omega
    · rcases (show b = 1 ∨ 2 ≤ b by omega) with hb1 | hb2
      · exfalso
        unfold ladP5 at h4
        omega
      · exact Or.inr ⟨by omega, hb2, by omega⟩
    · rcases (show b = d + 1 ∨ b ≤ d by omega) with hb1 | hb2
      · exfalso
        unfold ladP5 at h3
        omega
      · exact Or.inl ⟨by omega, by omega, hb2⟩
    · exfalso
      unfold ladP5 at h2
      omega
    · exfalso
      unfold ladP5 at h1
      omega
  · intro h
    rcases h with h | h <;> ladW5_tac

set_option maxHeartbeats 400000 in
/-- An even boundary site of B5 is not a charge-one site. -/
private theorem ladder5_evenBlack_boundary {d a b : ℤ} (hd : 4 ≤ d) (h0 : ladP5 d a b)
    (hbd : ¬ (ladP5 d (a + 1) b ∧ ladP5 d (a - 1) b ∧ ladP5 d a (b + 1) ∧ ladP5 d a (b - 1)))
    (hE : LadderOddEvenBlack d (a, b)) : False := by
  apply hbd
  unfold ladP5 at h0
  obtain ⟨r1, r2, hp⟩ := h0
  simp only [LadderOddEvenBlack] at hE
  rcases hp with hp | hp | hp
  all_goals first
    | (exfalso; omega)
    | (refine ⟨?_, ?_, ?_, ?_⟩ <;> ladP5_tac)

/-- A right-exit of an odd B5 site (with the site in the tile) gives a charge-zero site. -/
private theorem ladder5_W_of_right {d a b : ℤ} (hd : 4 ≤ d) (hodd : d % 2 = 0) (hband : ladP5 d a b)
    (hn : ¬ ladP5 d (a + 1) b) (hpar : (a + b) % 2 = 1) : LadderOddOddWhite d (a, b) := by
  unfold ladP5 at hband hn
  simp only [LadderOddOddWhite, LadderOddLowerBoundary, reflectLadderOdd, Prod.fst_sub, Prod.snd_sub]
  have key : a = 2 * d ∨ (a + b = 2 * d + 3 ∧ b ≠ d + 2) ∨ (b = 0 ∧ a = d - 1) := by
    omega
  rcases key with ke | ke | ke
  · rcases (show b = 1 ∨ b = 3 by omega) with hb | hb
    · exact Or.inl (Or.inr (Or.inr ⟨by omega, by omega, by omega⟩))
    · exact Or.inr (Or.inl (Or.inl ⟨by omega, by omega, by omega⟩))
  · rcases (show (3 ≤ b ∧ b ≤ d) ∨ b = d + 1 by omega) with hb | hb
    · exact Or.inr (Or.inl (Or.inl ⟨by omega, by omega, by omega⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))
  · exact Or.inl (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))

set_option maxHeartbeats 400000 in
/-- A left-exit of an odd B5 site (with the site in the tile) gives a charge-zero site. -/
private theorem ladder5_W_of_left {d a b : ℤ} (hd : 4 ≤ d) (hodd : d % 2 = 0) (hband : ladP5 d a b)
    (hn : ¬ ladP5 d (a - 1) b) (hpar : (a + b) % 2 = 1) : LadderOddOddWhite d (a, b) := by
  unfold ladP5 at hband hn
  simp only [LadderOddOddWhite, LadderOddLowerBoundary, reflectLadderOdd, Prod.fst_sub, Prod.snd_sub]
  have key : a = 2 - d ∨ (a + b = 1 ∧ ¬(a = 1 ∧ b = 0)) ∨ (b = d + 2 ∧ a = 3) := by
    omega
  rcases key with ke | ke | ke
  · rcases (show b = d - 1 ∨ b = d + 1 by omega) with hb | hb
    · exact Or.inl (Or.inl ⟨by omega, by omega, by omega⟩)
    · exact Or.inr (Or.inl (Or.inr (Or.inr ⟨by omega, by omega, by omega⟩)))
  · rcases (show b = 0 ∨ b = 1 ∨ 2 ≤ b by omega) with hb | hb | hb
    · exfalso
      omega
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))
    · exact Or.inl (Or.inl ⟨by omega, by omega, by omega⟩)
  · exact Or.inr (Or.inl (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))

set_option maxHeartbeats 400000 in
/-- An odd boundary site of B5 is a charge-zero site. -/
private theorem ladder5_oddWhite_boundary {d a b : ℤ} (hd : 4 ≤ d) (hodd : d % 2 = 0) (h0 : ladP5 d a b)
    (hbd : ¬ (ladP5 d (a + 1) b ∧ ladP5 d (a - 1) b ∧ ladP5 d a (b + 1) ∧ ladP5 d a (b - 1)))
    (hpar : (a + b) % 2 = 1) : LadderOddOddWhite d (a, b) := by
  have hsplit : ¬ ladP5 d (a + 1) b ∨ ¬ ladP5 d (a - 1) b ∨ ¬ ladP5 d a (b + 1) ∨
      ¬ ladP5 d a (b - 1) := by
    tauto
  have hsite : (a, b) ∈ (BaseMask.ladderOdd.raw d).sites := ladP5_iff.mpr h0
  have hdenV : BaseMask.ladderOdd.Valid d := ⟨hd, hodd⟩
  have hodd' : ¬ EvenSite (a, b) := by
    unfold EvenSite
    omega
  rcases hsplit with hn | hn | hn | hn
  · exact ladder5_W_of_right hd hodd h0 hn hpar
  · exact ladder5_W_of_left hd hodd h0 hn hpar
  · have hnr : (a, b + 1) ∉ (BaseMask.ladderOdd.raw d).sites := fun h => hn (ladP5_iff.mp h)
    exact Or.inr (Or.inl ((ladderOdd_up_notMem_iff hdenV hsite hodd').mp hnr))
  · have hnr : (a, b - 1) ∉ (BaseMask.ladderOdd.raw d).sites := fun h => hn (ladP5_iff.mp h)
    exact Or.inl ((ladderOdd_down_notMem_iff hdenV hsite (by omega)).mp hnr)

set_option maxHeartbeats 400000 in
/-- The standard B5 interior formula of `lemma:doubled_staircase_laplacian`. -/
private theorem ladder5_interior {d : ℤ} (hd : 4 ≤ d ∧ d % 2 = 0) (field : Field)
    (htable : ∀ x ∈ paperLadderTile d, laplacian field x =
      if EvenSite x then (if LadderOddEvenBlack d x then -1 else 0)
      else (if LadderOddOddWhite d x then 0 else -1)) :
    ∀ x ∈ paperLadderTile d \ innerBoundary (paperLadderTile d),
      laplacian field x = -(if (x.1 + x.2) % 2 = 1 then 1 else 0) -
        (if (x.1 + x.2) % 2 = 0 ∧ ((x.1 = 1 ∧ 1 ≤ x.2 ∧ x.2 ≤ d) ∨ (x.1 = d + 1 ∧ 2 ≤ x.2 ∧ x.2 ≤ d + 1))
          then 1 else 0) -
        (if x.1 + x.2 = d + 2 ∧ 2 ≤ x.2 ∧ x.2 ≤ d then 1 else 0) +
        (if x.1 + x.2 = d + 3 ∧ 3 ≤ x.2 ∧ x.2 ≤ d then 1 else 0) +
        (if x.1 + x.2 = d + 1 ∧ 2 ≤ x.2 ∧ x.2 ≤ d - 1 then 1 else 0) := by
  rintro ⟨a, b⟩ hx
  have hd1 : 4 ≤ d := hd.1
  have hT : (a, b) ∈ paperLadderTile d := hx.1
  have hn := nbrs_of_not_boundary hT hx.2
  dsimp only at hn
  obtain ⟨n1, n2, n3, n4⟩ := hn
  have h0 := ladP5_of_mem hd1 hT
  have s1 := ladP5_of_mem hd1 n1
  have s2 := ladP5_of_mem hd1 n2
  have s3 := ladP5_of_mem hd1 n3
  have s4 := ladP5_of_mem hd1 n4
  rw [htable (a, b) hT]
  dsimp only [EvenSite]
  by_cases hev : (a + b) % 2 = 0
  · rw [if_pos hev]
    simp only [ladder5_evenBlack_iff hd.2 hev]
    split_ifs
    all_goals omega
  · rw [if_neg hev]
    simp only [ladder5_oddWhite_iff_interior hd1 hd.2 s1 s2 s3 s4 (by omega)]
    split_ifs
    all_goals omega

set_option maxHeartbeats 400000 in
/-- The standard B5 boundary value of `lemma:doubled_staircase_laplacian`. -/
private theorem ladder5_boundary {d : ℤ} (hd : 4 ≤ d ∧ d % 2 = 0) (field : Field)
    (htable : ∀ x ∈ paperLadderTile d, laplacian field x =
      if EvenSite x then (if LadderOddEvenBlack d x then -1 else 0)
      else (if LadderOddOddWhite d x then 0 else -1)) :
    ∀ x ∈ innerBoundary (paperLadderTile d), laplacian field x = 0 := by
  rintro ⟨a, b⟩ hx
  obtain ⟨hT, hb⟩ := hx
  have hd1 : 4 ≤ d := hd.1
  have h0 := ladP5_of_mem hd1 hT
  have hbd : ¬ (ladP5 d (a + 1) b ∧ ladP5 d (a - 1) b ∧ ladP5 d a (b + 1) ∧ ladP5 d a (b - 1)) := by
    rintro ⟨n1, n2, n3, n4⟩
    rcases hb with h | h | h | h
    · exact h (mem_tile_of_ladP5 hd1 n1)
    · exact h (mem_tile_of_ladP5 hd1 n2)
    · exact h (mem_tile_of_ladP5 hd1 n3)
    · exact h (mem_tile_of_ladP5 hd1 n4)
  rw [htable (a, b) hT]
  dsimp only [EvenSite]
  by_cases hev : (a + b) % 2 = 0
  · rw [if_pos hev]
    by_cases hE : LadderOddEvenBlack d (a, b)
    · exact (ladder5_evenBlack_boundary hd1 h0 hbd hE).elim
    · rw [if_neg hE]
  · rw [if_neg hev]
    have hpar : (a + b) % 2 = 1 := by omega
    by_cases hW : LadderOddOddWhite d (a, b)
    · rw [if_pos hW]
    · exact (hW (ladder5_oddWhite_boundary hd1 hd.2 h0 hbd hpar)).elim

set_option maxHeartbeats 400000 in
/-- `lemma:doubled_staircase_laplacian` (`paper/farey_recursion.tex` lines 2530–2568), standard part. -/
theorem doubled_staircase_laplacian {d : ℤ} (hd : 4 ≤ d ∧ d % 2 = 0) {field : Field} {constantU constantV : ℤ}
    (hagree : ∀ x ∈ paperLadderTile d, field x = paperLadderValue d x)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 d) field constantU constantV) :
    (∀ x, laplacian field (x + (Fraction.mk 1 d).modifiedDeck.kernel) = laplacian field x ∧
      laplacian field (x + (Fraction.mk 1 d).modifiedDeck.transverse) = laplacian field x) ∧
    (∀ x ∈ paperLadderTile d \ innerBoundary (paperLadderTile d),
      laplacian field x = -(if (x.1 + x.2) % 2 = 1 then 1 else 0) -
        (if (x.1 + x.2) % 2 = 0 ∧ ((x.1 = 1 ∧ 1 ≤ x.2 ∧ x.2 ≤ d) ∨ (x.1 = d + 1 ∧ 2 ≤ x.2 ∧ x.2 ≤ d + 1))
          then 1 else 0) -
        (if x.1 + x.2 = d + 2 ∧ 2 ≤ x.2 ∧ x.2 ≤ d then 1 else 0) +
        (if x.1 + x.2 = d + 3 ∧ 3 ≤ x.2 ∧ x.2 ≤ d then 1 else 0) +
        (if x.1 + x.2 = d + 1 ∧ 2 ≤ x.2 ∧ x.2 ≤ d - 1 then 1 else 0)) ∧
    (∀ x ∈ innerBoundary (paperLadderTile d), laplacian field x = 0) := by
  have hd1 : 4 ≤ d := hd.1
  have hden : BaseMask.ladderOdd.Valid d := ⟨hd.1, hd.2⟩
  obtain ⟨ref, hrefA, hrefP, -, -, -⟩ := ladderOdd_exists_recurrent_extension hden
  have hrefTile := values_of_agrees (mem_paperLadderTile_iff d hd1) (ladderOdd_height_paper d) hrefA
  have hagreeRef : ∀ x ∈ paperLadderTile d, field x = ref x := fun x hx =>
    (hagree x hx).trans (hrefTile x hx).symm
  have hk : (Fraction.mk 1 d).modifiedDeck.kernel = (2 * d, 2) :=
    congrArg PeriodDeck.kernel (reciprocalLadderDeck_eq hd.2)
  have ht : (Fraction.mk 1 d).modifiedDeck.transverse = (1 - d, 1 + d) :=
    congrArg PeriodDeck.transverse (reciprocalLadderDeck_eq hd.2)
  obtain ⟨hU, hV⟩ := constants_eq hperiod hrefP hagreeRef
    (mem_tile_of_ladP5 (a := 2 - d) (b := d) hd1 (by ladP5_tac))
    (mem_tile_of_ladP5 (a := d + 2) (b := d + 2) hd1 (by ladP5_tac))
    (by rw [hk]; exact Prod.ext (show 2 - d + 2 * d = d + 2 by ring) (show d + 2 = d + 2 by ring))
    (mem_tile_of_ladP5 (a := 2) (b := 0) hd1 (by ladP5_tac))
    (mem_tile_of_ladP5 (a := 3 - d) (b := d + 1) hd1 (by ladP5_tac))
    (by rw [ht]; exact Prod.ext (show 2 + (1 - d) = 3 - d by ring) (show 0 + (1 + d) = d + 1 by ring))
  rw [hU, hV] at hperiod
  have hinterval := interval_mk_one d (by omega)
  have hagreeRaw : (BaseMask.ladderOdd.raw d).Agrees field 0 :=
    agrees_of_paper (mem_paperLadderTile_iff d hd1) (ladderOdd_height_paper d) hagree
  have htable : ∀ x ∈ paperLadderTile d, laplacian field x =
      if EvenSite x then (if LadderOddEvenBlack d x then -1 else 0)
      else (if LadderOddOddWhite d x then 0 else -1) := fun x hx =>
    ladderOdd_laplacian_on_raw hden hagreeRaw hperiod x ((mem_paperLadderTile_iff d hd1 x).mp hx)
  obtain ⟨hpK, hpT⟩ := periodic_of_generatorPeriods hinterval hperiod
  exact ⟨fun x => ⟨hpK x, hpT x⟩, ladder5_interior hd field htable, ladder5_boundary hd field htable⟩


/-! ### Alternate odd doubled staircase -/

/-- The B7 tile at integer coordinates, as in `lemma:basecase_3k_odd_alt`. -/
private def ladP7 (d a b : ℤ) : Prop :=
  (1 - d ≤ a ∧ a ≤ 2 * d - 2) ∧ (-1 ≤ b ∧ b ≤ d + 2) ∧
    ((a = -1 ∧ b = -1) ∨ (a = d ∧ b = d + 2) ∨
      (-1 ≤ a + b ∧ a + b ≤ 2 * d + 1 ∧ ¬((-1 ≤ b ∧ b ≤ 0 ∧ d ≤ a) ∨ (d + 1 ≤ b ∧ b ≤ d + 2 ∧ a ≤ -1))))

private theorem ladP7_iff {d a b : ℤ} :
    (a, b) ∈ (BaseMask.ladderOddAlt.raw d).sites ↔ ladP7 d a b := by
  rw [BaseMask.mem_ladderOddAlt_raw_iff]
  simp only [ladP7, BaseMask.LadderOddAltCorner, or_assoc]

private theorem mem_tile_of_ladP7 {d a b : ℤ} (hd : 4 ≤ d) (h : ladP7 d a b) :
    (a, b) ∈ paperLadderAltTile d :=
  (mem_paperLadderAltTile_iff d hd (a, b)).mpr (ladP7_iff.mpr h)

private theorem ladP7_of_mem {d a b : ℤ} (hd : 4 ≤ d) (h : (a, b) ∈ paperLadderAltTile d) :
    ladP7 d a b :=
  ladP7_iff.mp ((mem_paperLadderAltTile_iff d hd (a, b)).mp h)

/-- Prove `ladP7 d a b` by choosing the piece of the tile that holds. -/
local macro "ladP7_tac" : tactic =>
  `(tactic| (unfold ladP7; refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;>
    first
    | (left; omega)
    | (right; left; omega)
    | (right; right; omega)
    | omega))

/-- On an even B7 site the charge-one list is the parity restriction of the interior list. -/
private theorem ladder7_evenBlack_iff {d a b : ℤ} (hodd : d % 2 = 0) (hev : (a + b) % 2 = 0) :
    LadderOddAltEvenBlack d (a, b) ↔
      ((a = 0 ∧ -1 ≤ b ∧ b ≤ d - 1) ∨ (a = d - 1 ∧ 2 ≤ b ∧ b ≤ d + 2) ∨
        (a + b = d ∧ 2 ≤ b ∧ b ≤ d - 1)) := by
  simp only [LadderOddAltEvenBlack, BaseMask.LadderOddAltDiagonal]
  constructor <;> intro h <;> omega

/-- An even boundary site of B7 is not a charge-one site. -/
private theorem ladder7_evenBlack_boundary {d a b : ℤ} (hd : 4 ≤ d) (h0 : ladP7 d a b)
    (hbd : ¬ (ladP7 d (a + 1) b ∧ ladP7 d (a - 1) b ∧ ladP7 d a (b + 1) ∧ ladP7 d a (b - 1)))
    (hE : LadderOddAltEvenBlack d (a, b)) : False := by
  apply hbd
  unfold ladP7 at h0
  obtain ⟨r1, r2, hp⟩ := h0
  simp only [LadderOddAltEvenBlack, BaseMask.LadderOddAltDiagonal] at hE
  rcases hp with hp | hp | hp
  all_goals first
    | (exfalso; omega)
    | (refine ⟨?_, ?_, ?_, ?_⟩ <;> ladP7_tac)

set_option maxHeartbeats 400000 in
/-- The two boundary sites of B7 with value `-1` are not charge-zero sites. -/
private theorem ladder7_oddWhite_special (d : ℤ) (hd : 4 ≤ d) :
    ¬ LadderOddAltOddWhite d (d - 1, 0) ∧ ¬ LadderOddAltOddWhite d (0, d + 1) := by
  constructor
  · intro h
    simp only [LadderOddAltOddWhite, LadderOddAltLowerExit, reflectLadderOddAlt, Prod.fst_sub,
      Prod.snd_sub] at h
    omega
  · intro h
    simp only [LadderOddAltOddWhite, LadderOddAltLowerExit, reflectLadderOddAlt, Prod.fst_sub,
      Prod.snd_sub] at h
    omega

/-- An up exit of an odd B7 site (in the tile) gives a charge-zero site. -/
private theorem ladder7_W_of_up {d a b : ℤ} (hd : 4 ≤ d) (hodd : d % 2 = 0) (hband : ladP7 d a b)
    (hn : ¬ ladP7 d a (b + 1)) (hpar : (a + b) % 2 = 1) : LadderOddAltOddWhite d (a, b) := by
  unfold ladP7 at hband hn
  simp only [LadderOddAltOddWhite, LadderOddAltLowerExit, reflectLadderOddAlt, Prod.fst_sub,
    Prod.snd_sub]
  have key : b = d + 2 ∨ (a + b = 2 * d + 1 ∧ 3 ≤ b ∧ b ≤ d) ∨ (b = d ∧ a ≤ -1) := by
    omega
  rcases key with ke | ke | ke
  · exact Or.inr (Or.inl (Or.inl ⟨by omega, by omega, by omega⟩))
  · exact Or.inr (Or.inl (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))
  · exact Or.inr (Or.inl (Or.inr (Or.inr ⟨by omega, by omega, by omega⟩)))

set_option maxHeartbeats 400000 in
/-- A left exit of an odd B7 site (in the tile, away from `(0, d+1)`) gives a charge-zero site. -/
private theorem ladder7_W_of_left {d a b : ℤ} (hd : 4 ≤ d) (hodd : d % 2 = 0) (hband : ladP7 d a b)
    (hn : ¬ ladP7 d (a - 1) b) (hne : ¬ (a = 0 ∧ b = d + 1)) (hpar : (a + b) % 2 = 1) :
    LadderOddAltOddWhite d (a, b) := by
  unfold ladP7 at hband hn
  simp only [LadderOddAltOddWhite, LadderOddAltLowerExit, reflectLadderOddAlt, Prod.fst_sub,
    Prod.snd_sub]
  have key : a = 1 - d ∨ (a + b = -1 ∧ 0 ≤ b) := by
    omega
  rcases key with ke | ⟨ks, kb⟩
  · rcases (show b = d - 2 ∨ b = d ∨ b = d + 2 by omega) with hb | hb | hb
    · exact Or.inl (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))
    · exact Or.inr (Or.inl (Or.inr (Or.inr ⟨by omega, by omega, by omega⟩)))
    · exfalso
      omega
  · rcases (show b = 0 ∨ 1 ≤ b by omega) with hb0 | hb1
    · exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))
    · exact Or.inl (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))

set_option maxHeartbeats 400000 in
/-- A right exit of an odd B7 site (in the tile, away from `(d-1, 0)`) gives a charge-zero site. -/
private theorem ladder7_W_of_right {d a b : ℤ} (hd : 4 ≤ d) (hodd : d % 2 = 0) (hband : ladP7 d a b)
    (hn : ¬ ladP7 d (a + 1) b) (hne : ¬ (a = d - 1 ∧ b = 0)) (hpar : (a + b) % 2 = 1) :
    LadderOddAltOddWhite d (a, b) := by
  unfold ladP7 at hband hn
  simp only [LadderOddAltOddWhite, LadderOddAltLowerExit, reflectLadderOddAlt, Prod.fst_sub,
    Prod.snd_sub]
  have key : a = 2 * d - 2 ∨ (a + b = 2 * d + 1 ∧ 3 ≤ b ∧ b ≤ d) ∨ (a + b = 2 * d + 1 ∧ b = d + 1) := by
    omega
  rcases key with ke | ke | ke
  · rcases (show b = 1 ∨ b = 3 by omega) with hb | hb
    · exact Or.inl (Or.inr (Or.inr ⟨by omega, by omega, by omega⟩))
    · exact Or.inr (Or.inl (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))
  · exact Or.inr (Or.inl (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))

set_option maxHeartbeats 400000 in
/-- An odd boundary site of B7 is a charge-zero site unless it is one of the two sites of value `-1`. -/
private theorem ladder7_oddWhite_boundary {d a b : ℤ} (hd : 4 ≤ d) (hodd : d % 2 = 0) (h0 : ladP7 d a b)
    (hbd : ¬ (ladP7 d (a + 1) b ∧ ladP7 d (a - 1) b ∧ ladP7 d a (b + 1) ∧ ladP7 d a (b - 1)))
    (hpar : (a + b) % 2 = 1) (hne1 : ¬ (a = d - 1 ∧ b = 0)) (hne2 : ¬ (a = 0 ∧ b = d + 1)) :
    LadderOddAltOddWhite d (a, b) := by
  have hsplit : ¬ ladP7 d (a + 1) b ∨ ¬ ladP7 d (a - 1) b ∨ ¬ ladP7 d a (b + 1) ∨
      ¬ ladP7 d a (b - 1) := by
    tauto
  have hsite : (a, b) ∈ (BaseMask.ladderOddAlt.raw d).sites := ladP7_iff.mpr h0
  have hdenV : BaseMask.ladderOddAlt.Valid d := ⟨hd, hodd⟩
  have hodd' : ¬ EvenSite (a, b) := by
    unfold EvenSite
    omega
  rcases hsplit with hn | hn | hn | hn
  · exact ladder7_W_of_right hd hodd h0 hn hne1 hpar
  · exact ladder7_W_of_left hd hodd h0 hn hne2 hpar
  · have hnr : (a, b + 1) ∉ (BaseMask.ladderOddAlt.raw d).sites := fun h => hn (ladP7_iff.mp h)
    exact ladder7_W_of_up hd hodd h0 hn hpar
  · have hnr : (a, b - 1) ∉ (BaseMask.ladderOddAlt.raw d).sites := fun h => hn (ladP7_iff.mp h)
    exact Or.inl ((ladderOddAlt_down_notMem_iff hdenV hsite (by omega)).mp hnr)


/-- On an odd interior site of B7, the charge-zero sites are the interior odd sites of formula (6). -/
private theorem ladder7_oddWhite_iff_interior {d a b : ℤ} (hd : 4 ≤ d)
    (h1 : ladP7 d (a + 1) b) (h2 : ladP7 d (a - 1) b) (h3 : ladP7 d a (b + 1))
    (h4 : ladP7 d a (b - 1)) :
    LadderOddAltOddWhite d (a, b) ↔
      ((a + b = d + 1 ∧ 3 ≤ b ∧ b ≤ d) ∨ (a + b = d - 1 ∧ 1 ≤ b ∧ b ≤ d - 2)) := by
  constructor
  · intro hW
    simp only [LadderOddAltOddWhite, LadderOddAltLowerExit, reflectLadderOddAlt, Prod.fst_sub,
      Prod.snd_sub, or_assoc] at hW
    rcases hW with h | h | h | h | h | h | h | h | h
    · exfalso
      unfold ladP7 at h4
      omega
    · exfalso
      unfold ladP7 at h4
      omega
    · exfalso
      unfold ladP7 at h4
      omega
    · exfalso
      unfold ladP7 at h3
      omega
    · exfalso
      unfold ladP7 at h1
      omega
    · exfalso
      unfold ladP7 at h3
      omega
    · exfalso
      unfold ladP7 at h2
      omega
    · exfalso
      unfold ladP7 at h1
      omega
    · obtain ⟨t1, t2, t3⟩ := h
      rcases t3 with t3 | t3
      · exact Or.inr ⟨by omega, by omega, by omega⟩
      · exact Or.inl ⟨by omega, by omega, by omega⟩
  · intro h
    simp only [LadderOddAltOddWhite, LadderOddAltLowerExit, reflectLadderOddAlt, Prod.fst_sub,
      Prod.snd_sub, or_assoc]
    rcases h with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨by omega, by omega, Or.inr (by omega)⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨by omega, by omega, Or.inl (by omega)⟩)))))))

set_option maxHeartbeats 400000 in
/-- The standard B7 interior formula of `lemma:doubled_staircase_laplacian`. -/
private theorem ladder7_interior {d : ℤ} (hd : 4 ≤ d ∧ d % 2 = 0) (field : Field)
    (htable : ∀ x ∈ paperLadderAltTile d, laplacian field x =
      if EvenSite x then (if LadderOddAltEvenBlack d x then -1 else 0)
      else (if LadderOddAltOddWhite d x then 0 else -1)) :
    ∀ x ∈ paperLadderAltTile d \ innerBoundary (paperLadderAltTile d),
      laplacian field x = -(if (x.1 + x.2) % 2 = 1 then 1 else 0) -
        (if (x.1 + x.2) % 2 = 0 ∧ ((x.1 = 0 ∧ -1 ≤ x.2 ∧ x.2 ≤ d - 1) ∨ (x.1 = d - 1 ∧ 2 ≤ x.2 ∧ x.2 ≤ d + 2))
          then 1 else 0) -
        (if x.1 + x.2 = d ∧ 2 ≤ x.2 ∧ x.2 ≤ d - 1 then 1 else 0) +
        (if x.1 + x.2 = d + 1 ∧ 3 ≤ x.2 ∧ x.2 ≤ d then 1 else 0) +
        (if x.1 + x.2 = d - 1 ∧ 1 ≤ x.2 ∧ x.2 ≤ d - 2 then 1 else 0) := by
  rintro ⟨a, b⟩ hx
  have hd1 : 4 ≤ d := hd.1
  have hT : (a, b) ∈ paperLadderAltTile d := hx.1
  have hn := nbrs_of_not_boundary hT hx.2
  dsimp only at hn
  obtain ⟨n1, n2, n3, n4⟩ := hn
  have h0 := ladP7_of_mem hd1 hT
  have s1 := ladP7_of_mem hd1 n1
  have s2 := ladP7_of_mem hd1 n2
  have s3 := ladP7_of_mem hd1 n3
  have s4 := ladP7_of_mem hd1 n4
  rw [htable (a, b) hT]
  dsimp only [EvenSite]
  by_cases hev : (a + b) % 2 = 0
  · rw [if_pos hev]
    simp only [ladder7_evenBlack_iff hd.2 hev]
    split_ifs
    all_goals omega
  · rw [if_neg hev]
    simp only [ladder7_oddWhite_iff_interior hd1 s1 s2 s3 s4]
    split_ifs
    all_goals omega

set_option maxHeartbeats 400000 in
/-- The standard B7 boundary value of `lemma:doubled_staircase_laplacian`. -/
private theorem ladder7_boundary {d : ℤ} (hd : 4 ≤ d ∧ d % 2 = 0) (field : Field)
    (htable : ∀ x ∈ paperLadderAltTile d, laplacian field x =
      if EvenSite x then (if LadderOddAltEvenBlack d x then -1 else 0)
      else (if LadderOddAltOddWhite d x then 0 else -1)) :
    ∀ x ∈ innerBoundary (paperLadderAltTile d),
      laplacian field x = -(if x = (d - 1, 0) ∨ x = (0, d + 1) then 1 else 0) := by
  rintro ⟨a, b⟩ hx
  obtain ⟨hT, hb⟩ := hx
  have hd1 : 4 ≤ d := hd.1
  have h0 := ladP7_of_mem hd1 hT
  have hbd : ¬ (ladP7 d (a + 1) b ∧ ladP7 d (a - 1) b ∧ ladP7 d a (b + 1) ∧ ladP7 d a (b - 1)) := by
    rintro ⟨n1, n2, n3, n4⟩
    rcases hb with h | h | h | h
    · exact h (mem_tile_of_ladP7 hd1 n1)
    · exact h (mem_tile_of_ladP7 hd1 n2)
    · exact h (mem_tile_of_ladP7 hd1 n3)
    · exact h (mem_tile_of_ladP7 hd1 n4)
  rw [htable (a, b) hT]
  dsimp only [EvenSite]
  simp only [Prod.mk.injEq]
  by_cases hev : (a + b) % 2 = 0
  · rw [if_pos hev]
    by_cases hE : LadderOddAltEvenBlack d (a, b)
    · exact (ladder7_evenBlack_boundary hd1 h0 hbd hE).elim
    · rw [if_neg hE]
      split_ifs
      all_goals omega
  · rw [if_neg hev]
    have hpar : (a + b) % 2 = 1 := by omega
    by_cases hsp : (a = d - 1 ∧ b = 0) ∨ (a = 0 ∧ b = d + 1)
    · have hW : ¬ LadderOddAltOddWhite d (a, b) := by
        rcases hsp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact (ladder7_oddWhite_special d hd1).1
        · exact (ladder7_oddWhite_special d hd1).2
      rw [if_neg hW, if_pos hsp]
    · have hne1 : ¬ (a = d - 1 ∧ b = 0) := fun h => hsp (Or.inl h)
      have hne2 : ¬ (a = 0 ∧ b = d + 1) := fun h => hsp (Or.inr h)
      have hW := ladder7_oddWhite_boundary hd1 hd.2 h0 hbd hpar hne1 hne2
      rw [if_pos hW, if_neg hsp, neg_zero]

set_option maxHeartbeats 400000 in
/-- `lemma:doubled_alt_staircase_laplacian` (`paper/farey_recursion.tex` lines 2530–2568), alternate part. -/
theorem doubled_alt_staircase_laplacian {d : ℤ} (hd : 4 ≤ d ∧ d % 2 = 0) {field : Field}
    {constantU constantV : ℤ}
    (hagree : ∀ x ∈ paperLadderAltTile d, field x = paperLadderAltValue d x)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 d) field constantU constantV) :
    (∀ x, laplacian field (x + (Fraction.mk 1 d).modifiedDeck.kernel) = laplacian field x ∧
      laplacian field (x + (Fraction.mk 1 d).modifiedDeck.transverse) = laplacian field x) ∧
    (∀ x ∈ paperLadderAltTile d \ innerBoundary (paperLadderAltTile d),
      laplacian field x = -(if (x.1 + x.2) % 2 = 1 then 1 else 0) -
        (if (x.1 + x.2) % 2 = 0 ∧ ((x.1 = 0 ∧ -1 ≤ x.2 ∧ x.2 ≤ d - 1) ∨ (x.1 = d - 1 ∧ 2 ≤ x.2 ∧ x.2 ≤ d + 2))
          then 1 else 0) -
        (if x.1 + x.2 = d ∧ 2 ≤ x.2 ∧ x.2 ≤ d - 1 then 1 else 0) +
        (if x.1 + x.2 = d + 1 ∧ 3 ≤ x.2 ∧ x.2 ≤ d then 1 else 0) +
        (if x.1 + x.2 = d - 1 ∧ 1 ≤ x.2 ∧ x.2 ≤ d - 2 then 1 else 0)) ∧
    (∀ x ∈ innerBoundary (paperLadderAltTile d),
      laplacian field x = -(if x = (d - 1, 0) ∨ x = (0, d + 1) then 1 else 0)) := by
  have hd1 : 4 ≤ d := hd.1
  have hden : BaseMask.ladderOddAlt.Valid d := ⟨hd.1, hd.2⟩
  obtain ⟨ref, hrefA, hrefP, -, -, -⟩ := ladderOddAlt_exists_recurrent_extension hden
  have hrefTile := values_of_agrees (mem_paperLadderAltTile_iff d hd1) (ladderOddAlt_height_paper d) hrefA
  have hagreeRef : ∀ x ∈ paperLadderAltTile d, field x = ref x := fun x hx =>
    (hagree x hx).trans (hrefTile x hx).symm
  have hk : (Fraction.mk 1 d).modifiedDeck.kernel = (2 * d, 2) :=
    congrArg PeriodDeck.kernel (reciprocalLadderDeck_eq hd.2)
  have ht : (Fraction.mk 1 d).modifiedDeck.transverse = (1 - d, 1 + d) :=
    congrArg PeriodDeck.transverse (reciprocalLadderDeck_eq hd.2)
  obtain ⟨hU, hV⟩ := constants_eq hperiod hrefP hagreeRef
    (mem_tile_of_ladP7 (a := -2) (b := 1) hd1 (by ladP7_tac))
    (mem_tile_of_ladP7 (a := 2 * d - 2) (b := 3) hd1 (by ladP7_tac))
    (by rw [hk]; exact Prod.ext (show -2 + 2 * d = 2 * d - 2 by ring) (show 1 + 2 = 3 by ring))
    (mem_tile_of_ladP7 (a := d - 1) (b := -1) hd1 (by ladP7_tac))
    (mem_tile_of_ladP7 (a := 0) (b := d) hd1 (by ladP7_tac))
    (by rw [ht]; exact Prod.ext (show d - 1 + (1 - d) = 0 by ring) (show -1 + (1 + d) = d by ring))
  rw [hU, hV] at hperiod
  have hinterval := interval_mk_one d (by omega)
  have hagreeRaw : (BaseMask.ladderOddAlt.raw d).Agrees field 0 :=
    agrees_of_paper (mem_paperLadderAltTile_iff d hd1) (ladderOddAlt_height_paper d) hagree
  have htable : ∀ x ∈ paperLadderAltTile d, laplacian field x =
      if EvenSite x then (if LadderOddAltEvenBlack d x then -1 else 0)
      else (if LadderOddAltOddWhite d x then 0 else -1) := fun x hx =>
    ladderOddAlt_laplacian_on_raw hden hagreeRaw hperiod x ((mem_paperLadderAltTile_iff d hd1 x).mp hx)
  obtain ⟨hpK, hpT⟩ := periodic_of_generatorPeriods hinterval hperiod
  exact ⟨fun x => ⟨hpK x, hpT x⟩, ladder7_interior hd field htable, ladder7_boundary hd field htable⟩

end FLatticePaper.Construction
