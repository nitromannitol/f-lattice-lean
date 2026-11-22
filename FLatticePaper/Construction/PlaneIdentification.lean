import FLatticePaper.Construction.OrdinaryAgreement
import FLatticePaper.Plane.Induction.StandardField

/-! The identification target of the ordinary standard output (task 42).

The native tile of an ordinary standard at a word `w` agrees, up to one constant and in the plane chart, with the plane
standard field of the output: `standardField w` for the even output, and for the odd output the odd parent of
`w ++ [one]`, which is the quarter turn of the conjugate standard field `standardField (conjWord (w ++ [one]))`. The
numerical check (scripts/ordinary_tile_check.py) finds all 49 ordinary tiles of words of length at most three equal to
their target at zero translation, each with its own constant. -/

namespace FLatticePaper.Construction

open Farey HeightTile

/-- The odd birth prefix of `w ++ [one]` is `w`: the last digit `one` is not three, so it is the birth prefix. -/
theorem oddBirthPrefix_append_one (w : Word) :
    FLatticePaper.Induction.oddBirthPrefix (w ++ [Digit.one]) = w := by
  unfold FLatticePaper.Induction.oddBirthPrefix
  simp [List.reverse_append, List.dropWhile_cons_of_neg]

/-- The conjugate word of `w ++ [one]` is the swapped word `w`. -/
theorem conjWord_append_one (w : Word) :
    (FLatticePaper.Induction.oddBirthPrefix (w ++ [Digit.one])).map Digit.swapTwoThree = w.map Digit.swapTwoThree := by
  rw [oddBirthPrefix_append_one]

/-- The plane field of an output of a word: the even standard field of the word, or the quarter turn of the conjugate
standard field for the odd output (the odd parent of `w ++ [one]`). -/
noncomputable def planeTarget (word : Word) : Parity → (Site → ℤ)
  | .even => FLatticePaper.Induction.standardField word
  | .odd => FLatticePaper.Induction.quarterTurnField
      (FLatticePaper.Induction.standardField
        ((FLatticePaper.Induction.oddBirthPrefix (word ++ [Digit.one])).map Digit.swapTwoThree))

/-- The ordinary standard output, identified with its plane field: under the nominal agreement of its six copies with
the plane field and the chronological contacts, the output agrees with `planeTarget word parity` up to one constant,
on the chart shifted by the box origin of the raw assembly (`ordinaryStandard_output_agrees`). -/
theorem ordinaryStandard_identifies (parents : TileParents) (word : Word) (parity : Parity) (context : String)
    (hnom : ∀ slot : Fin 6,
      ∃ g : ℤ, (ordinaryStandardCopy parents word parity slot).val.Agrees (planeTarget word parity) g)
    (hcon : HeightTile.OrderedContacts (ordinaryStandardSchedule parents word parity).first.val.sites
      (ordinaryStandardSchedule parents word parity).copies) :
    ∃ result, (ordinaryStandardSchedule parents word parity).eval .tile context = .ok result ∧
      ∃ g : ℤ, result.val.Agrees
        (fun site => planeTarget word parity (site + ((ordinaryStandardSchedule parents word parity).raw hcon).val.boxOrigin
          ((ordinaryStandardSchedule parents word parity).raw hcon).property)) g :=
  ordinaryStandard_output_agrees parents word parity context hnom hcon

/-- Comparison 1 against the explicit plane field: the fresh sites of a copy that agrees with `planeTarget` equal the
target up to the copy's constant. -/
theorem freshEquality_planeTarget {incoming : HeightTile FLatticePaper.Site} {occupied : Finset FLatticePaper.Site} {word : Word} {parity : Parity}
    {gauge : ℤ} (h : incoming.Agrees (planeTarget word parity) gauge) :
    FreshEquality incoming occupied (planeTarget word parity) gauge :=
  freshEquality_of_agrees h

/-- The register chart: the `llCenter` normalization of a tile that agrees with `target` after the shift `B` agrees
with `target` itself when the lower-left site of the tile sits at `-B`. The hypothesis `hzero` is the chart condition:
the lower-left site of the output, in the raw chart, is the origin. -/
theorem llCenter_agrees_of_zero {E : HeightTile FLatticePaper.Site} {target : Field} {gauge : ℤ} {B : FLatticePaper.Site}
    (hne : E.sites.Nonempty) (hE : E.Agrees (fun site => target (site + B)) gauge)
    (hzero : E.lowerLeft hne + B = 0) :
    (E.llCenter hne).Agrees target gauge := by
  intro site
  have hmem := (E.mem_place_sites (-E.lowerLeft hne) 0 site.val).mp site.property
  change E.height ⟨site.val - -E.lowerLeft hne, hmem⟩ +
      ((0 : FLatticePaper.Site).1 * site.val.1 + (0 : FLatticePaper.Site).2 * site.val.2) =
    target site.val + gauge
  rw [hE ⟨site.val - -E.lowerLeft hne, hmem⟩]
  dsimp only
  have hpt : site.val - -E.lowerLeft hne + B = site.val := by
    rw [sub_neg_eq_add, add_assoc, hzero, add_zero]
  rw [hpt]
  simp

/-- The register identification: the native register of an ordinary standard output, after the `llCenter` convention,
agrees with the plane field `planeTarget word parity` up to one constant, provided the output's lower-left site sits at
the raw origin (`hzero`). The numerical check finds zero translation for all ordinary tiles of words of length at most
three; `hzero` is the remaining chart fact and is not proved here. -/
theorem ordinaryStandard_identifies_register (parents : TileParents) (word : Word) (parity : Parity) (context : String)
    (hnom : ∀ slot : Fin 6,
      ∃ g : ℤ, (ordinaryStandardCopy parents word parity slot).val.Agrees (planeTarget word parity) g)
    (hcon : HeightTile.OrderedContacts (ordinaryStandardSchedule parents word parity).first.val.sites
      (ordinaryStandardSchedule parents word parity).copies)
    (hzero : ∀ result, (ordinaryStandardSchedule parents word parity).eval .tile context = .ok result →
      result.val.lowerLeft result.property +
        ((ordinaryStandardSchedule parents word parity).raw hcon).val.boxOrigin
          ((ordinaryStandardSchedule parents word parity).raw hcon).property = 0) :
    ∃ result, (ordinaryStandardSchedule parents word parity).eval .tile context = .ok result ∧
      ∃ g : ℤ, (result.val.llCenter result.property).Agrees (planeTarget word parity) g := by
  obtain ⟨result, hres, g, hagree⟩ := ordinaryStandard_identifies parents word parity context hnom hcon
  exact ⟨result, hres, g, llCenter_agrees_of_zero result.property hagree (hzero result hres)⟩

end FLatticePaper.Construction
