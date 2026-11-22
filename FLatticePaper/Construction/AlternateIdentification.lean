import FLatticePaper.Construction.PlaneIdentification
import FLatticePaper.Tiles.AlternateAgreement
import FLatticePaper.Plane.AlternateMidpoint

/-! # The plane target of the ordinary even alternate and its branches (task 46, Lean)

The plane alternate field of a word is the rounded midpoint of the standard even field `F` of the word and its translate
`G(s) = F(s + σ)`, with `σ = 2 ε (D, N)` for the even child `N/D` of the word and `ε` the frame sign (`-1` for even phase).
The numerical check (scripts/alt_plane_check.py, scripts/alt_copy_check.py) finds that the ordinary even alternate outputs of
words of length at most three, and all their copies, agree with this target at zero translation; on every copy the gap
`F(s) - F(s + σ)` lies in `[0, 2]`.

On that window the rounded midpoint is the minimum `min(F, G + 1)` (`roundedMidpoint_eq_min_of_slip` at level zero). So a
tile agrees with the alternate target as soon as each of its heights is `F + g` on the sites where `F ≤ G + 1`, and
`G + 1 + g` on the sites where `G + 1 < F`: these are the two branches, and the copies of the output are sheets of the
standard field, attained on the branch of their sites. -/

namespace FLatticePaper.Construction

open Farey FLatticePaper FLatticePaper.Induction HeightTile

/-- The shift of the alternate midpoint: `σ = 2 ε (D, N)`, with `N / D` the odd parent of the word (the left parent of its
Farey pair, as `parents(w)[0]` in scripts/proto2.py) and `ε` the frame sign. -/
def alternateSigma (word : Word) : Site :=
  (2 * (frameAt word).eps * (parentsAt word).odd.den, 2 * (frameAt word).eps * (parentsAt word).odd.num)

/-- The plane alternate field of a word: the rounded midpoint of the standard even field and its `σ`-translate. -/
noncomputable def alternateTarget (word : Word) : Field :=
  roundedMidpoint (standardField word) (fun s => standardField word (s + alternateSigma word))

/-- On the window `0 ≤ F(s) − G(s) ≤ 2`, the alternate target is the minimum `min(F, G + 1)`. -/
theorem alternateTarget_eq_min {word : Word} (s : Site)
    (hlo : 0 ≤ standardField word s - standardField word (s + alternateSigma word))
    (hhi : standardField word s - standardField word (s + alternateSigma word) ≤ 2) :
    alternateTarget word s =
      min (standardField word s) (standardField word (s + alternateSigma word) + 1) := by
  have h1 : 2 * (0 : ℤ) ≤ standardField word s - standardField word (s + alternateSigma word) := by
    rw [mul_zero]
    exact hlo
  have h2 : standardField word s - standardField word (s + alternateSigma word) ≤ 2 * (0 : ℤ) + 2 := by
    rw [mul_zero, zero_add]
    exact hhi
  have h := roundedMidpoint_eq_min_of_slip (standardField word)
    (fun t => standardField word (t + alternateSigma word)) s 0 h1 h2
  unfold alternateTarget
  rw [h]
  simp

/-- Agreement with a target transfers to a pointwise equal target on the sites of the tile. -/
theorem HeightTile.Agrees.congr_target {α : Type*} {tile : HeightTile α} {target target' : α → ℤ} {gauge : ℤ}
    (h : tile.Agrees target gauge) (hT : ∀ s ∈ tile.sites, target' s = target s) :
    tile.Agrees target' gauge := by
  intro site
  rw [h site, hT site.1 site.2]

/-- **The branch criterion.** A tile on the window `0 ≤ F − G ≤ 2` agrees with the alternate target, with the constant `g`,
when its height is `F + g` on the sites where `F − G ≤ 1` and `G + 1 + g` on the sites where `F − G ≥ 2`. -/
theorem HeightTile.Agrees.alternateTarget_of_branches {word : Word} {tile : HeightTile Site} {gauge : ℤ}
    (hwin : ∀ s ∈ tile.sites, 0 ≤ standardField word s - standardField word (s + alternateSigma word) ∧
      standardField word s - standardField word (s + alternateSigma word) ≤ 2)
    (hF : ∀ s : tile.sites, standardField word s.1 - standardField word (s.1 + alternateSigma word) ≤ 1 →
      tile.height s = standardField word s.1 + gauge)
    (hG : ∀ s : tile.sites, 1 < standardField word s.1 - standardField word (s.1 + alternateSigma word) →
      tile.height s = standardField word (s.1 + alternateSigma word) + 1 + gauge) :
    tile.Agrees (alternateTarget word) gauge := by
  intro s
  have hw := hwin s.1 s.2
  rw [alternateTarget_eq_min s.1 hw.1 hw.2]
  by_cases hgap : standardField word s.1 - standardField word (s.1 + alternateSigma word) ≤ 1
  · have hle : standardField word s.1 ≤ standardField word (s.1 + alternateSigma word) + 1 := by omega
    rw [min_eq_left hle, hF s hgap]
  · have hlt : standardField word (s.1 + alternateSigma word) + 1 ≤ standardField word s.1 := by omega
    rw [min_eq_right hlt, hG s (by omega)]

/-! ## The even ordinary alternate: the first copy, and the identification with the alternate target -/

/-- The slot-zero jet of the even ordinary alternate is the slot-zero jet of the even ordinary standard, in both phases:
both are `0` for phase `0` and `2 • oddKernel` otherwise. -/
theorem alternateJets_even_zero (word : Word) : alternateJets word .even 0 = standardJets word .even 0 := by
  by_cases h : phase word = 0 <;> simp [alternateJets, standardJets, h, doubleFirst, doubleLast]

/-- The first copy of the even ordinary alternate is the first copy of the even ordinary standard of the same word: the
same donor `parents.even` at the same jet. -/
theorem ordinaryAlternate_even_first_eq (parents : TileParents) (beforePush : Word) (digit : Digit) :
    (ordinaryAlternateSchedule parents beforePush digit .even).first =
      ordinaryStandardCopy parents (beforePush ++ [digit]) .even 0 := by
  have hj := alternateJets_even_zero (beforePush ++ [digit])
  have hs : standardSources parents .odd 0 = standardSources parents .even 0 := rfl
  show placedBySlot (alternateJets (beforePush ++ [digit]) .even) (standardSources parents .odd) 0 =
    placedBySlot (standardJets (beforePush ++ [digit]) .even) (standardSources parents .even) 0
  unfold placedBySlot
  rw [hj, hs]

/-- **The first copy of the even ordinary alternate agrees with the alternate target**, from the agreement of the even
ordinary standard copy in slot zero with the standard field, and the window `0 ≤ F − G ≤ 1` on its sites (the first copy is
on the branch where the minimum is the standard field; numerically the window holds for every word of length at most three). -/
theorem ordinaryAlternate_even_first_agrees (parents : TileParents) (beforePush : Word) (digit : Digit)
    (hstd : ∃ g : ℤ, (ordinaryStandardCopy parents (beforePush ++ [digit]) .even 0).val.Agrees
      (standardField (beforePush ++ [digit])) g)
    (hwin : ∀ s ∈ (ordinaryStandardCopy parents (beforePush ++ [digit]) .even 0).val.sites,
      0 ≤ standardField (beforePush ++ [digit]) s -
          standardField (beforePush ++ [digit]) (s + alternateSigma (beforePush ++ [digit])) ∧
        standardField (beforePush ++ [digit]) s -
          standardField (beforePush ++ [digit]) (s + alternateSigma (beforePush ++ [digit])) ≤ 1) :
    ∃ g : ℤ, (ordinaryAlternateSchedule parents beforePush digit .even).first.val.Agrees
      (alternateTarget (beforePush ++ [digit])) g := by
  obtain ⟨g, hg⟩ := hstd
  rw [ordinaryAlternate_even_first_eq]
  refine ⟨g, HeightTile.Agrees.alternateTarget_of_branches (fun s hs => ?_) (fun s _ => hg s) (fun s hs' => ?_)⟩
  · have h := hwin s hs
    exact ⟨h.1, by omega⟩
  · exact absurd (hwin s.1 s.2).2 (not_le.mpr hs')

/-- **The ordinary even alternate agrees with its plane target.** For a word of even output that is not a base word, the
output agrees with `alternateTarget` on the chart of its raw box origin, from:
* the first copy, by `ordinaryAlternate_even_first_agrees` (the standard slot-zero agreement and the window);
* the seventh copy (the restored alternate piece), named, for the non-base word;
* the slots after the seventh, named, one agreement with the target per copy;
* the chronological contacts.
The pure-two base words are not covered: their seventh copy is the base mask, not a plane tile. -/
theorem ordinaryAlternate_even_identifies (parents : TileParents) (beforePush : Word) (digit : Digit)
    (hnb : ¬ FLatticePaper.Tiles.Standard.IsBase (beforePush ++ [digit]))
    (hstd : ∃ g : ℤ, (ordinaryStandardCopy parents (beforePush ++ [digit]) .even 0).val.Agrees
      (standardField (beforePush ++ [digit])) g)
    (hwin : ∀ s ∈ (ordinaryStandardCopy parents (beforePush ++ [digit]) .even 0).val.sites,
      0 ≤ standardField (beforePush ++ [digit]) s -
          standardField (beforePush ++ [digit]) (s + alternateSigma (beforePush ++ [digit])) ∧
        standardField (beforePush ++ [digit]) s -
          standardField (beforePush ++ [digit]) (s + alternateSigma (beforePush ++ [digit])) ≤ 1)
    (context : String)
    (hseventh : ¬ FLatticePaper.Tiles.Standard.IsBase (beforePush ++ [digit]) → ∃ g : ℤ,
      ((seventhAlternateJet beforePush digit .even).place
        (FLatticePaper.Tiles.AlternateOrdinary.oldAlternate parents (beforePush ++ [digit]) .even)).val.Agrees (alternateTarget (beforePush ++ [digit])) g)
    (hslot : ∀ s ∈ afterSeventhAlternate .even, ∃ g : ℤ,
      (placedBySlot (alternateJets (beforePush ++ [digit]) .even) (standardSources parents .odd) s).val.Agrees
        (alternateTarget (beforePush ++ [digit])) g)
    (hcon : HeightTile.OrderedContacts (ordinaryAlternateSchedule parents beforePush digit .even).first.val.sites
      (ordinaryAlternateSchedule parents beforePush digit .even).copies) :
    ∃ result, (ordinaryAlternateSchedule parents beforePush digit .even).eval .tile context = .ok result ∧
      ∃ g : ℤ, result.val.Agrees
        (fun site => alternateTarget (beforePush ++ [digit]) (site +
          ((ordinaryAlternateSchedule parents beforePush digit .even).raw hcon).val.boxOrigin
            ((ordinaryAlternateSchedule parents beforePush digit .even).raw hcon).property)) g := by
  obtain ⟨_, hfirst⟩ := ordinaryAlternate_even_first_agrees parents beforePush digit hstd hwin
  exact FLatticePaper.Tiles.AlternateAgreement.ordinaryAlternate_output_agrees_of_seven parents beforePush digit .even context hfirst (hseventh hnb) hslot hcon

/-- The register form of `ordinaryAlternate_even_identifies`: after the `llCenter` convention, given the chart condition
that the lower-left site of the output sits at the raw origin. -/
theorem ordinaryAlternate_even_identifies_register (parents : TileParents) (beforePush : Word) (digit : Digit)
    (hnb : ¬ FLatticePaper.Tiles.Standard.IsBase (beforePush ++ [digit]))
    (hstd : ∃ g : ℤ, (ordinaryStandardCopy parents (beforePush ++ [digit]) .even 0).val.Agrees
      (standardField (beforePush ++ [digit])) g)
    (hwin : ∀ s ∈ (ordinaryStandardCopy parents (beforePush ++ [digit]) .even 0).val.sites,
      0 ≤ standardField (beforePush ++ [digit]) s -
          standardField (beforePush ++ [digit]) (s + alternateSigma (beforePush ++ [digit])) ∧
        standardField (beforePush ++ [digit]) s -
          standardField (beforePush ++ [digit]) (s + alternateSigma (beforePush ++ [digit])) ≤ 1)
    (context : String)
    (hseventh : ¬ FLatticePaper.Tiles.Standard.IsBase (beforePush ++ [digit]) → ∃ g : ℤ,
      ((seventhAlternateJet beforePush digit .even).place
        (FLatticePaper.Tiles.AlternateOrdinary.oldAlternate parents (beforePush ++ [digit]) .even)).val.Agrees (alternateTarget (beforePush ++ [digit])) g)
    (hslot : ∀ s ∈ afterSeventhAlternate .even, ∃ g : ℤ,
      (placedBySlot (alternateJets (beforePush ++ [digit]) .even) (standardSources parents .odd) s).val.Agrees
        (alternateTarget (beforePush ++ [digit])) g)
    (hcon : HeightTile.OrderedContacts (ordinaryAlternateSchedule parents beforePush digit .even).first.val.sites
      (ordinaryAlternateSchedule parents beforePush digit .even).copies)
    (hzero : ∀ result, (ordinaryAlternateSchedule parents beforePush digit .even).eval .tile context = .ok result →
      result.val.lowerLeft result.property +
        ((ordinaryAlternateSchedule parents beforePush digit .even).raw hcon).val.boxOrigin
          ((ordinaryAlternateSchedule parents beforePush digit .even).raw hcon).property = 0) :
    ∃ result, (ordinaryAlternateSchedule parents beforePush digit .even).eval .tile context = .ok result ∧
      ∃ g : ℤ, (result.val.llCenter result.property).Agrees (alternateTarget (beforePush ++ [digit])) g := by
  obtain ⟨result, hres, g, hagree⟩ :=
    ordinaryAlternate_even_identifies parents beforePush digit hnb hstd hwin context hseventh hslot hcon
  exact ⟨result, hres, g, llCenter_agrees_of_zero result.property hagree (hzero result hres)⟩

end FLatticePaper.Construction
