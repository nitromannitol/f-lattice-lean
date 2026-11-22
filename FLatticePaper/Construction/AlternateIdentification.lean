import FLatticePaper.Construction.PlaneIdentification
import FLatticePaper.Construction.NominalAgreement
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

/-- The lower-left order of the rows (the order of `lowerLeft`): the lower row first, then the leftmost site. -/
def siteLexMin (a b : Site) : Site :=
  if toLex (a.2, a.1) ≤ toLex (b.2, b.1) then a else b

/-- The lower-left site of the raw odd ordinary alternate output, as the minimum of the offsets of its seven copies: the six
alternate jets and the seventh copy, placed at its jet offset plus the restoration. The donors are llCentered registers, so
the lower-left of a placed copy is its offset. -/
def alternateOddLowerLeft (word : Word) : Site :=
  let seventh : Site := match word.getLast? with
    | some d => (seventhAlternateJet word.dropLast d .odd).1 + alternateRestoration word .even
    | none => 0
  List.foldl siteLexMin (alternateJets word .odd 0).1
    (seventh :: List.ofFn fun k : Fin 6 => (alternateJets word .odd k).1)

/-- The llCenter chart of the odd alternate output of odd phase: the translation of its register in the prescribed
coordinates, `δ − LL`, with `δ` the transverse offset of the odd parent minus the kernel offset of the even parent (zero in
phase zero) and `LL` the lower-left of the raw output. The chart is determined modulo the period `2 (D + dq, N + nq)` of the
target (the doubled kernel of the mediant of the two parents). -/
def alternateOddChart (word : Word) : Site :=
  (if phase word = 1 then (transverseJet (parentsAt word).odd).1 - (kernelJet (parentsAt word).even).1 else 0) -
    alternateOddLowerLeft word

/-- The transverse slope of the odd alternate output: `(num, −den)` of the odd parent in phase one, zero in phase zero. -/
def alternateOddSlope (word : Word) : Site :=
  if phase word = 1 then ((parentsAt word).odd.num, -(parentsAt word).odd.den) else 0

/-- **The odd plane target of an ordinary alternate.** The quarter turn of the alternate midpoint of the swapped word, read in
the llCenter chart `alternateOddChart`, plus the transverse slope `alternateOddSlope` of the odd parent in phase one. The
numerical check (scripts/odd_chart_formula.py) finds that every ordinary odd alternate output of length at most three agrees
with this target, with one constant on its sites. -/
noncomputable def alternateOddTarget (word : Word) : Field := fun x =>
  quarterTurnField (alternateTarget (word.map Digit.swapTwoThree)) (x - alternateOddChart word) +
    ((alternateOddSlope word).1 * x.1 + (alternateOddSlope word).2 * x.2)

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

/-! ## The fourth copy of the even ordinary alternate is the third standard copy -/

/-- The fourth alternate jet of the even ordinary alternate is the third standard jet of the even ordinary standard, in both
phases (`evenKernel` for phase `0`, `0` for phase `1`). -/
theorem alternateJets_even_four_eq (word : Word) : alternateJets word .even 4 = standardJets word .even 2 := by
  by_cases h : phase word = 0 <;> simp [alternateJets, standardJets, h, doubleFirst, doubleLast]

/-- The fourth copy of the even ordinary alternate is the third copy of the even ordinary standard of the same word: the
same donor `parents.odd` at the same jet. -/
theorem ordinaryAlternate_even_copy_four_eq (parents : TileParents) (word : Word) :
    placedBySlot (alternateJets word .even) (standardSources parents .odd) 4 =
      ordinaryStandardCopy parents word .even 2 := by
  have hs : standardSources parents .odd 4 = standardSources parents .even 2 := rfl
  unfold ordinaryStandardCopy
  unfold placedBySlot
  rw [alternateJets_even_four_eq, hs]

/-- **The fourth copy of the even ordinary alternate agrees with the alternate target.** Its jet and donor are those of the
third copy of the standard, so `nominal_even_two` (the sheet and period argument of the standard) gives its agreement with
the standard field on its sites, under the same named inputs; the window `0 ≤ F − G ≤ 1` on its sites puts it on the branch
where the alternate target is the standard field. -/
theorem ordinaryAlternate_even_copy_four_agrees (parents : TileParents) (word : Word)
    (hproper : ∃ x ∈ word, x ≠ Digit.three)
    (hodd : ∃ g : ℤ, parents.odd.val.Agrees (quarterTurnField (standardField (conjWord word))) g)
    (hper : RespectsPeriodsOn (frameAt word).child (frameAt word).coherentConstantU
      (frameAt word).coherentConstantV (frameAt word).closedPolygon
      ((frameAt word).sheetMin (quarterTurnField (standardField (conjWord word)))))
    (hE : ∀ s ∈ (ordinaryStandardCopy parents word .even 2).val.sites, s ∈ (frameAt word).closedPolygon)
    (hA : ∀ s ∈ (ordinaryStandardCopy parents word .even 2).val.sites,
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) s ≤
        (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) s)
    (hwin : ∀ s ∈ (ordinaryStandardCopy parents word .even 2).val.sites,
      0 ≤ standardField word s - standardField word (s + alternateSigma word) ∧
        standardField word s - standardField word (s + alternateSigma word) ≤ 1) :
    ∃ g : ℤ, (placedBySlot (alternateJets word .even) (standardSources parents .odd) 4).val.Agrees
      (alternateTarget word) g := by
  rw [ordinaryAlternate_even_copy_four_eq]
  obtain ⟨g, hg⟩ := nominal_even_two parents word hproper hodd hper hE hA
  refine ⟨g, HeightTile.Agrees.alternateTarget_of_branches (fun s hs => ?_) (fun s _ => hg s) (fun s hs' => ?_)⟩
  · have h := hwin s hs
    exact ⟨h.1, by omega⟩
  · exact absurd (hwin s.1 s.2).2 (not_le.mpr hs')

/-- The even ordinary alternate of a word ending in `1` or `2` has the proper letter needed by `nominal_even_two`. -/
theorem exists_proper_of_even_digit (beforePush : Word) (digit : Digit)
    (hd : digit = Digit.one ∨ digit = Digit.two) : ∃ x ∈ beforePush ++ [digit], x ≠ Digit.three :=
  ⟨digit, List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)), by
    rcases hd with rfl | rfl <;> intro h <;> cases h⟩

/-- **The ordinary even alternate agrees with its plane target, with the fourth copy discharged.** As
`ordinaryAlternate_even_identifies`, the first copy is discharged from the standard slot zero and the window; the fourth
copy is discharged from `nominal_even_two` (`ordinaryAlternate_even_copy_four_agrees`). Named: the standard slot-zero and
slot-two inputs, the windows on the first and fourth copies, the seventh copy of a non-base word, the slots other than the
fourth, and the contacts. -/
theorem ordinaryAlternate_even_identifies_four (parents : TileParents) (beforePush : Word) (digit : Digit)
    (hd : digit = Digit.one ∨ digit = Digit.two)
    (hnb : ¬ FLatticePaper.Tiles.Standard.IsBase (beforePush ++ [digit]))
    (hstd : ∃ g : ℤ, (ordinaryStandardCopy parents (beforePush ++ [digit]) .even 0).val.Agrees
      (standardField (beforePush ++ [digit])) g)
    (hwin : ∀ s ∈ (ordinaryStandardCopy parents (beforePush ++ [digit]) .even 0).val.sites,
      0 ≤ standardField (beforePush ++ [digit]) s -
          standardField (beforePush ++ [digit]) (s + alternateSigma (beforePush ++ [digit])) ∧
        standardField (beforePush ++ [digit]) s -
          standardField (beforePush ++ [digit]) (s + alternateSigma (beforePush ++ [digit])) ≤ 1)
    (hodd : ∃ g : ℤ, parents.odd.val.Agrees
      (quarterTurnField (standardField (conjWord (beforePush ++ [digit])))) g)
    (hper : RespectsPeriodsOn (frameAt (beforePush ++ [digit])).child
      (frameAt (beforePush ++ [digit])).coherentConstantU (frameAt (beforePush ++ [digit])).coherentConstantV
      (frameAt (beforePush ++ [digit])).closedPolygon
      ((frameAt (beforePush ++ [digit])).sheetMin (quarterTurnField (standardField (conjWord (beforePush ++ [digit]))))))
    (hE : ∀ s ∈ (ordinaryStandardCopy parents (beforePush ++ [digit]) .even 2).val.sites,
      s ∈ (frameAt (beforePush ++ [digit])).closedPolygon)
    (hA : ∀ s ∈ (ordinaryStandardCopy parents (beforePush ++ [digit]) .even 2).val.sites,
      (frameAt (beforePush ++ [digit])).sheetA (quarterTurnField (standardField (conjWord (beforePush ++ [digit])))) s ≤
        (frameAt (beforePush ++ [digit])).sheetC (quarterTurnField (standardField (conjWord (beforePush ++ [digit])))) s)
    (hwin4 : ∀ s ∈ (ordinaryStandardCopy parents (beforePush ++ [digit]) .even 2).val.sites,
      0 ≤ standardField (beforePush ++ [digit]) s -
          standardField (beforePush ++ [digit]) (s + alternateSigma (beforePush ++ [digit])) ∧
        standardField (beforePush ++ [digit]) s -
          standardField (beforePush ++ [digit]) (s + alternateSigma (beforePush ++ [digit])) ≤ 1)
    (context : String)
    (hseventh : ¬ FLatticePaper.Tiles.Standard.IsBase (beforePush ++ [digit]) → ∃ g : ℤ,
      ((seventhAlternateJet beforePush digit .even).place
        (FLatticePaper.Tiles.AlternateOrdinary.oldAlternate parents (beforePush ++ [digit]) .even)).val.Agrees
        (alternateTarget (beforePush ++ [digit])) g)
    (hslot : ∀ s ∈ afterSeventhAlternate .even, s ≠ 4 → ∃ g : ℤ,
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
  have hslot' : ∀ s ∈ afterSeventhAlternate .even, ∃ g : ℤ,
      (placedBySlot (alternateJets (beforePush ++ [digit]) .even) (standardSources parents .odd) s).val.Agrees
        (alternateTarget (beforePush ++ [digit])) g := by
    intro s hs
    by_cases h4 : s = 4
    · subst h4
      exact ordinaryAlternate_even_copy_four_agrees parents (beforePush ++ [digit])
        (exists_proper_of_even_digit beforePush digit hd) hodd hper hE hA hwin4
    · exact hslot s hs h4
  exact FLatticePaper.Tiles.AlternateAgreement.ordinaryAlternate_output_agrees_of_seven parents beforePush digit .even
    context hfirst (hseventh hnb) hslot' hcon

/-! ## The seventh copy of the even ordinary alternate -/

/-- The seventh copy of the even ordinary alternate: the odd alternate tile of the parent (its donor), restored by
`alternateRestoration` for the odd parity, and placed at the seventh jet of the even output. -/
def alternateSeventhCopy (parents : TileParents) (beforePush : Word) (digit : Digit) : NonemptyTile :=
  (seventhAlternateJet beforePush digit .even).place
    (FLatticePaper.Tiles.AlternateOrdinary.oldAlternate parents (beforePush ++ [digit]) .even)

/-- Restoring and then placing a tile is one placement by the sum of the offsets, with the slope of the jet, since the
restoration has zero slope. -/
theorem HeightTile.Agrees.restore_then_place {tile : HeightTile Site} {target : Field} {gauge : ℤ}
    (h : tile.Agrees target gauge) (R : Site) (J : TileJet) :
    ((tile.place R 0).place J.1 J.2).Agrees
      (fun s => target (s - (J.1 + R)) + (J.2.1 * s.1 + J.2.2 * s.2)) gauge := by
  refine HeightTile.Agrees.congr_target (Agrees.place (Agrees.place h R 0) J.1 J.2) ?_
  intro s _
  simp [sub_sub]

/-- **The seventh copy agrees with the alternate target**, from the induction hypothesis on the donor (the odd alternate tile
of the parent agrees with `alternateOddTarget` of the parent, in the llCenter chart) and the midpoint identity on the sites of
the seventh copy: `alternateTarget w = alternateOddTarget p (s − (offset + restoration)) + slope · s + k`. The midpoint identity is
the sheet argument for this copy (it holds numerically for the non-base words whose donor is in the dump; it fails for the
pure-two words, whose donor is a base mask). -/
theorem alternateSeventhCopy_agrees_of_donor (parents : TileParents) (beforePush : Word) (digit : Digit) {g0 : ℤ}
    (hdonor : parents.alternateOdd.val.Agrees (alternateOddTarget beforePush) g0) (k : ℤ)
    (hmid : ∀ s ∈ (alternateSeventhCopy parents beforePush digit).val.sites,
      alternateTarget (beforePush ++ [digit]) s =
        alternateOddTarget beforePush
            (s - ((seventhAlternateJet beforePush digit .even).1 +
              alternateRestoration (beforePush ++ [digit]) .odd)) +
          ((seventhAlternateJet beforePush digit .even).2.1 * s.1 + (seventhAlternateJet beforePush digit .even).2.2 * s.2) +
          k) :
    (alternateSeventhCopy parents beforePush digit).val.Agrees (alternateTarget (beforePush ++ [digit])) (g0 - k) := by
  have hp := HeightTile.Agrees.restore_then_place hdonor (alternateRestoration (beforePush ++ [digit]) .odd)
    (seventhAlternateJet beforePush digit .even)
  intro s
  have h1 : (alternateSeventhCopy parents beforePush digit).val.height s =
      alternateOddTarget beforePush
          (s.1 - ((seventhAlternateJet beforePush digit .even).1 +
            alternateRestoration (beforePush ++ [digit]) .odd)) +
        ((seventhAlternateJet beforePush digit .even).2.1 * s.1.1 +
          (seventhAlternateJet beforePush digit .even).2.2 * s.1.2) + g0 := hp s
  have h2 := hmid s.1 s.2
  rw [h1, h2]
  ring

/-- **The ordinary even alternate agrees with its plane target, with the fourth and the seventh copies discharged.** As
`ordinaryAlternate_even_identifies_four`, the seventh copy of a non-base word is now the donor placed by the restoration and
the seventh jet, identified by `alternateSeventhCopy_agrees_of_donor`, from the donor's induction hypothesis and the midpoint
identity on the copy (both named). -/
theorem ordinaryAlternate_even_identifies_seventh (parents : TileParents) (beforePush : Word) (digit : Digit)
    (hd : digit = Digit.one ∨ digit = Digit.two)
    (hnb : ¬ FLatticePaper.Tiles.Standard.IsBase (beforePush ++ [digit]))
    (hstd : ∃ g : ℤ, (ordinaryStandardCopy parents (beforePush ++ [digit]) .even 0).val.Agrees
      (standardField (beforePush ++ [digit])) g)
    (hwin : ∀ s ∈ (ordinaryStandardCopy parents (beforePush ++ [digit]) .even 0).val.sites,
      0 ≤ standardField (beforePush ++ [digit]) s -
          standardField (beforePush ++ [digit]) (s + alternateSigma (beforePush ++ [digit])) ∧
        standardField (beforePush ++ [digit]) s -
          standardField (beforePush ++ [digit]) (s + alternateSigma (beforePush ++ [digit])) ≤ 1)
    (hodd : ∃ g : ℤ, parents.odd.val.Agrees
      (quarterTurnField (standardField (conjWord (beforePush ++ [digit])))) g)
    (hper : RespectsPeriodsOn (frameAt (beforePush ++ [digit])).child
      (frameAt (beforePush ++ [digit])).coherentConstantU (frameAt (beforePush ++ [digit])).coherentConstantV
      (frameAt (beforePush ++ [digit])).closedPolygon
      ((frameAt (beforePush ++ [digit])).sheetMin (quarterTurnField (standardField (conjWord (beforePush ++ [digit]))))))
    (hE : ∀ s ∈ (ordinaryStandardCopy parents (beforePush ++ [digit]) .even 2).val.sites,
      s ∈ (frameAt (beforePush ++ [digit])).closedPolygon)
    (hA : ∀ s ∈ (ordinaryStandardCopy parents (beforePush ++ [digit]) .even 2).val.sites,
      (frameAt (beforePush ++ [digit])).sheetA (quarterTurnField (standardField (conjWord (beforePush ++ [digit])))) s ≤
        (frameAt (beforePush ++ [digit])).sheetC (quarterTurnField (standardField (conjWord (beforePush ++ [digit])))) s)
    (hwin4 : ∀ s ∈ (ordinaryStandardCopy parents (beforePush ++ [digit]) .even 2).val.sites,
      0 ≤ standardField (beforePush ++ [digit]) s -
          standardField (beforePush ++ [digit]) (s + alternateSigma (beforePush ++ [digit])) ∧
        standardField (beforePush ++ [digit]) s -
          standardField (beforePush ++ [digit]) (s + alternateSigma (beforePush ++ [digit])) ≤ 1)
    (context : String) {g0 : ℤ}
    (hdonor : parents.alternateOdd.val.Agrees (alternateOddTarget beforePush) g0)
    (hmid : ¬ FLatticePaper.Tiles.Standard.IsBase (beforePush ++ [digit]) → ∃ k : ℤ,
      ∀ s ∈ (alternateSeventhCopy parents beforePush digit).val.sites,
        alternateTarget (beforePush ++ [digit]) s =
          alternateOddTarget beforePush
              (s - ((seventhAlternateJet beforePush digit .even).1 +
                alternateRestoration (beforePush ++ [digit]) .odd)) +
            ((seventhAlternateJet beforePush digit .even).2.1 * s.1 +
              (seventhAlternateJet beforePush digit .even).2.2 * s.2) + k)
    (hslot : ∀ s ∈ afterSeventhAlternate .even, s ≠ 4 → ∃ g : ℤ,
      (placedBySlot (alternateJets (beforePush ++ [digit]) .even) (standardSources parents .odd) s).val.Agrees
        (alternateTarget (beforePush ++ [digit])) g)
    (hcon : HeightTile.OrderedContacts (ordinaryAlternateSchedule parents beforePush digit .even).first.val.sites
      (ordinaryAlternateSchedule parents beforePush digit .even).copies) :
    ∃ result, (ordinaryAlternateSchedule parents beforePush digit .even).eval .tile context = .ok result ∧
      ∃ g : ℤ, result.val.Agrees
        (fun site => alternateTarget (beforePush ++ [digit]) (site +
          ((ordinaryAlternateSchedule parents beforePush digit .even).raw hcon).val.boxOrigin
            ((ordinaryAlternateSchedule parents beforePush digit .even).raw hcon).property)) g :=
  ordinaryAlternate_even_identifies_four parents beforePush digit hd hnb hstd hwin hodd hper hE hA hwin4 context
    (fun hnb' => by
      obtain ⟨k, hk⟩ := hmid hnb'
      exact ⟨g0 - k, alternateSeventhCopy_agrees_of_donor parents beforePush digit hdonor k hk⟩)
    hslot hcon

end FLatticePaper.Construction
