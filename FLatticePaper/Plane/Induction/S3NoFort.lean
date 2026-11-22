import FLatticePaper.Plane.Induction.Potentials
import FLatticePaper.Plane.RestrictedBellmanRank

/-! The restricted no-fort premise of S3, from the local inputs of the archive's exit argument (task 31).

The archive excludes a fort bounded below in a half-space `{K ≥ h}`, `K = A P + C J`, by a descent: at a minimal site
of the fort that is not free, a continuing input in the fort is allowed (no larger `P` or `J`, a smaller bulk order);
at a free site the fort is translated so that the free site sits at the endpoint levels, where the endpoint gate
gives a strictly lower target or an earlier free site. The restricted version (ALL_SLOPE_STEP addendum, "restricted
traps") is the same descent in the permitted inputs. `PermitLocal` makes every site of a restricted fort have a
permitted input in the fort, which is what the descent needs. -/

namespace FLatticePaper

open Farey

/-- A restricted fort under `PermitLocal` has, at each of its sites, a permitted input in the fort. -/
theorem exists_permitted_input_mem {field : Field} {permits : Site → Site → Prop} {fort : Set Site}
    (hlocal : PermitLocal field permits) (hfort : IsRestrictedFort field permits fort) {site : Site}
    (hsite : site ∈ fort) : ∃ input ∈ fort, permits site input := by
  rcases hfort site hsite with ⟨hl, hn | hp⟩ | ⟨hl, hn, hp⟩
  · have hperm := hlocal.1 site hl
    rcases hn with hin | hnp
    · exact ⟨_, hin, hperm.1⟩
    · exact absurd hperm.1 hnp
  · have hperm := hlocal.1 site hl
    rcases hp with hin | hnp
    · exact ⟨_, hin, hperm.2⟩
    · exact absurd hperm.2 hnp
  · rcases hlocal.2 site hl with h | h
    · rcases hn with hin | hnp
      · exact ⟨_, hin, h⟩
      · exact absurd h hnp
    · rcases hp with hin | hnp
      · exact ⟨_, hin, h⟩
      · exact absurd h hnp

/-- Translating a restricted fort by an even deck step gives a restricted fort, when the laplacian and the permits are
invariant under the step. -/
theorem isRestrictedFort_translate {field : Field} {permits : Site → Site → Prop} {fort : Set Site}
    (hfort : IsRestrictedFort field permits fort) {step : Site} (heven : EvenSite step)
    (hcharge : ∀ site, laplacian field (site + step) = laplacian field site)
    (hperm : ∀ site input, permits (site + step) (input + step) ↔ permits site input) :
    IsRestrictedFort field permits ((fun site => site + step) '' fort) := by
  rintro _ ⟨site, hsite, rfl⟩
  have hmem : ∀ y : Site, y + step ∈ (fun site => site + step) '' fort ↔ y ∈ fort := by
    intro y
    constructor
    · rintro ⟨x, hx, hxy⟩
      have : x = y := add_right_cancel hxy
      subst this
      exact hx
    · intro hy
      exact ⟨y, hy, rfl⟩
  have key := hfort site hsite
  simp only [hcharge, incomingNeg_add_of_even site step heven, incomingPos_add_of_even site step heven, hmem, hperm]
  exact key

/-- The descent: a nonempty restricted fort cannot lie in a half-space of a positive weighting of the two grades. The
inputs are those of the archive's argument: bulk nonincrease along permitted inputs of non-free sites with a bulk order
decreasing along them (`hbulk`), the translation of a free site to the endpoint levels (`hnormalize`), and the endpoint
gate at free sites of those levels (`hgate`). -/
theorem no_restrictedFort_of_componentwise_exit {field first second : Field} {free : Site → Prop}
    {bulkOrder freeOrder : Site → ℕ} {permits : Site → Site → Prop} {deck : PeriodDeck}
    (firstLevel secondLevel : ℤ)
    (hlocal : PermitLocal field permits)
    (heven : ∀ step ∈ deck.span, EvenSite step)
    (hcharge : ∀ step ∈ deck.span, ∀ site, laplacian field (site + step) = laplacian field site)
    (hperm : ∀ step ∈ deck.span, ∀ site input, permits (site + step) (input + step) ↔ permits site input)
    (hfirst : ∀ step ∈ deck.span, ∃ increment : ℤ, ∀ site, first (site + step) = first site + increment)
    (hsecond : ∀ step ∈ deck.span, ∃ increment : ℤ, ∀ site, second (site + step) = second site + increment)
    (hnormalize : ∀ site, free site → ∃ step ∈ deck.span,
      free (site + step) ∧ first (site + step) = firstLevel ∧ second (site + step) = secondLevel)
    (hbulk : ∀ center, ¬ free center → ∀ input, permits center input →
      first input ≤ first center ∧ second input ≤ second center ∧ bulkOrder input < bulkOrder center)
    (hgate : ∀ fort : Set Site, IsRestrictedFort field permits fort → ∀ site ∈ fort,
      free site → first site = firstLevel → second site = secondLevel → ∃ target ∈ fort,
        (first target ≤ firstLevel ∧ second target ≤ secondLevel ∧
          (first target < firstLevel ∨ second target < secondLevel)) ∨
        (free target ∧ first target = firstLevel ∧ second target = secondLevel ∧ freeOrder target < freeOrder site))
    {a c : ℤ} (ha : 0 < a) (hc : 0 < c) (level : ℤ) (fort : Set Site) (hne : fort.Nonempty)
    (hfort : IsRestrictedFort field permits fort)
    (hbounded : ∀ site ∈ fort, level ≤ a * first site + c * second site) : False := by
  let grade (site : Site) := a * first site + c * second site
  obtain ⟨site, hsite⟩ := hne
  obtain ⟨least, ⟨point, hpoint, hleast⟩, hmin⟩ := Int.exists_least_of_bdd
    (P := fun value => ∃ site ∈ fort, grade site = value)
    ⟨level, by rintro _ ⟨site, hsite, rfl⟩; exact hbounded site hsite⟩
    ⟨grade site, site, hsite, rfl⟩
  have hleast_le (site : Site) (hsite : site ∈ fort) : least ≤ grade site := hmin _ ⟨site, hsite, rfl⟩
  have hreachesFree (n : ℕ) (center : Site) (horder : bulkOrder center = n) (hcenter : center ∈ fort)
      (hgrade : grade center = least) : ∃ point ∈ fort, free point ∧ grade point = least := by
    induction n using Nat.strong_induction_on generalizing center with
    | _ n ih =>
      by_cases hfree : free center
      · exact ⟨center, hcenter, hfree, hgrade⟩
      · obtain ⟨input, hinput, hpermIn⟩ := exists_permitted_input_mem hlocal hfort hcenter
        obtain ⟨hfirstLe, hsecondLe, hdrop⟩ := hbulk center hfree input hpermIn
        have hgradeLe : grade input ≤ grade center := add_le_add
          (mul_le_mul_of_nonneg_left hfirstLe ha.le) (mul_le_mul_of_nonneg_left hsecondLe hc.le)
        exact ih (bulkOrder input) (horder ▸ hdrop) input rfl hinput
          (le_antisymm (hgradeLe.trans hgrade.le) (hleast_le input hinput))
  obtain ⟨freeSite, hfreeMem, hfree, hfreeMin⟩ := hreachesFree (bulkOrder point) point rfl hpoint hleast
  obtain ⟨step, hstep, hfreeShift, hfirstShift, hsecondShift⟩ := hnormalize freeSite hfree
  obtain ⟨dp, hdp⟩ := hfirst step hstep
  obtain ⟨dj, hdj⟩ := hsecond step hstep
  let shifted := (fun site => site + step) '' fort
  have hshifted : IsRestrictedFort field permits shifted :=
    isRestrictedFort_translate hfort (heven step hstep) (hcharge step hstep) (hperm step hstep)
  have hgradeAdd (site : Site) : grade (site + step) = grade site + (a * dp + c * dj) := by
    simp only [grade, hdp, hdj, mul_add]
    ac_rfl
  have hminimal (target : Site) (hmem : target ∈ shifted) : a * firstLevel + c * secondLevel ≤ grade target := by
    rcases hmem with ⟨site, hsite, rfl⟩
    have hle : grade (freeSite + step) ≤ grade (site + step) := by
      rw [hgradeAdd, hgradeAdd, hfreeMin]
      exact add_le_add_left (hleast_le site hsite) _
    simpa only [grade, hfirstShift, hsecondShift] using hle
  have hexclude (n : ℕ) (site : Site) (horder : freeOrder site = n) (hmem : site ∈ shifted)
      (hfree : free site) (hp : first site = firstLevel) (hj : second site = secondLevel) : False := by
    induction n using Nat.strong_induction_on generalizing site with
    | _ n ih =>
      obtain ⟨target, htarget, hdrop | hearlier⟩ := hgate shifted hshifted site hmem hfree hp hj
      · obtain ⟨hfirstLe, hsecondLe, hstrict | hstrict⟩ := hdrop
        · exact (not_lt_of_ge (hminimal target htarget)) (add_lt_add_of_lt_of_le
            (mul_lt_mul_of_pos_left hstrict ha) (mul_le_mul_of_nonneg_left hsecondLe hc.le))
        · exact (not_lt_of_ge (hminimal target htarget)) (add_lt_add_of_le_of_lt
            (mul_le_mul_of_nonneg_left hfirstLe ha.le) (mul_lt_mul_of_pos_left hstrict hc))
      · obtain ⟨hfree', hp', hj', hlt⟩ := hearlier
        exact ih (freeOrder target) (horder ▸ hlt) target rfl htarget hfree' hp' hj'
  exact hexclude (freeOrder (freeSite + step)) (freeSite + step) rfl ⟨freeSite, hfreeMem, rfl⟩
    hfreeShift hfirstShift hsecondShift

end FLatticePaper
namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- The local inputs of the archive's exit argument for S3, for the frame of a word and the field `F`. The first and
second grades are the price `P = cutGrade F 1 0 1` and the rounded slip `J = cutGrade F 0 1 1`; the free sites form a
deck-invariant set, with a bulk order and a free order. `bulk` is the bulk nonincrease of `P` and `J` along the
permitted inputs of a non-free site (with the bulk order decreasing along them). `gate` is the endpoint certificate
at a free site of the endpoint levels. -/
structure S3NoFortInputs (frame : ChildFrame) (F : Field) where
  free : Site → Prop
  bulkOrder : Site → ℕ
  freeOrder : Site → ℕ
  firstLevel : ℤ
  secondLevel : ℤ
  freeInvariant : ∀ step ∈ frame.child.modifiedDeck.span, ∀ site, free (site + step) ↔ free site
  bulk : ∀ center, ¬ free center → ∀ input,
    slipPermits F (fun z => F (z + frame.shortShift)) center input →
    frame.cutGrade F 1 0 1 input ≤ frame.cutGrade F 1 0 1 center ∧
      frame.cutGrade F 0 1 1 input ≤ frame.cutGrade F 0 1 1 center ∧ bulkOrder input < bulkOrder center
  gate : ∀ fort : Set Site, IsRestrictedFort F (slipPermits F (fun z => F (z + frame.shortShift))) fort →
    ∀ site ∈ fort, free site → frame.cutGrade F 1 0 1 site = firstLevel →
      frame.cutGrade F 0 1 1 site = secondLevel → ∃ target ∈ fort,
        (frame.cutGrade F 1 0 1 target ≤ firstLevel ∧ frame.cutGrade F 0 1 1 target ≤ secondLevel ∧
          (frame.cutGrade F 1 0 1 target < firstLevel ∨ frame.cutGrade F 0 1 1 target < secondLevel)) ∨
        (free target ∧ frame.cutGrade F 1 0 1 target = firstLevel ∧
          frame.cutGrade F 0 1 1 target = secondLevel ∧ freeOrder target < freeOrder site)

/-- The restricted no-fort premise of S3 for the grade `cutGrade F 1 1 1`, from the local inputs of the archive's exit
argument. The normalization of a free site to the endpoint levels is derived from the deck increments of `P` and `J`
(`P` shifts by `-i`, `J` by `j` along `i U + j V`), not assumed. -/
theorem restrictedNoFort_S3_of_inputs (frame : ChildFrame) {F : Field} {cU cV : ℤ}
    (hper : HasGeneratorPeriods frame.child F cU cV)
    (hlocal : PermitLocal F (slipPermits F (fun z => F (z + frame.shortShift))))
    (inputs : S3NoFortInputs frame F) :
    RestrictedNoFort F (frame.cutGrade F 1 1 1) (slipPermits F (fun z => F (z + frame.shortShift))) := by
  have hKspan : frame.child.modifiedDeck.kernel ∈ frame.child.modifiedDeck.span :=
    ⟨1, 0, by simp [PeriodDeck.combine]⟩
  have hVspan : frame.child.modifiedDeck.transverse ∈ frame.child.modifiedDeck.span :=
    ⟨0, 1, by simp [PeriodDeck.combine]⟩
  have hKe : EvenSite frame.child.modifiedDeck.kernel :=
    ((frame.child.mem_modifiedDeck_iff _).mp hKspan).2
  have hVe : EvenSite frame.child.modifiedDeck.transverse :=
    ((frame.child.mem_modifiedDeck_iff _).mp hVspan).2
  have heven : ∀ step ∈ frame.child.modifiedDeck.span, EvenSite step := by
    rintro step ⟨i, j, rfl⟩
    rw [combine_eq_smul]
    exact evenSite_smul_add _ _ hKe hVe i j
  have hcharge : ∀ step ∈ frame.child.modifiedDeck.span, ∀ site,
      laplacian F (site + step) = laplacian F site := by
    rintro step ⟨i, j, rfl⟩ site
    exact laplacian_add_combine hper site i j
  have hgσ : ∀ z, frame.child.transverseGrade (z + frame.shortShift) =
      frame.child.transverseGrade z + frame.child.transverseGrade frame.shortShift := by
    intro z
    unfold Fraction.transverseGrade
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  have hgσ2 : frame.child.transverseGrade frame.shortShift = 2 := by
    rw [frame.transverseGrade_child, frame.tGrade_shortShift]
    norm_num
  have hperm : ∀ step ∈ frame.child.modifiedDeck.span, ∀ site input,
      slipPermits F (fun z => F (z + frame.shortShift)) (site + step) (input + step) ↔
        slipPermits F (fun z => F (z + frame.shortShift)) site input := by
    rintro step ⟨i, j, rfl⟩ site input
    rw [combine_eq_smul]
    exact slipPermits_add_deck hper.1 hper.2 hgσ hgσ2 i j site input
  have hfirst : ∀ step ∈ frame.child.modifiedDeck.span, ∃ increment : ℤ,
      ∀ site, frame.cutGrade F 1 0 1 (site + step) = frame.cutGrade F 1 0 1 site + increment := by
    rintro step ⟨i, j, rfl⟩
    exact ⟨-i, fun site => by rw [frame.cutGrade_add_combine F hper 1 0 1 i j site]; ring⟩
  have hsecond : ∀ step ∈ frame.child.modifiedDeck.span, ∃ increment : ℤ,
      ∀ site, frame.cutGrade F 0 1 1 (site + step) = frame.cutGrade F 0 1 1 site + increment := by
    rintro step ⟨i, j, rfl⟩
    exact ⟨j, fun site => by rw [frame.cutGrade_add_combine F hper 0 1 1 i j site]; ring⟩
  have hnormalize : ∀ site, inputs.free site → ∃ step ∈ frame.child.modifiedDeck.span,
      inputs.free (site + step) ∧ frame.cutGrade F 1 0 1 (site + step) = inputs.firstLevel ∧
        frame.cutGrade F 0 1 1 (site + step) = inputs.secondLevel := by
    intro site hfree
    have hmem : frame.child.modifiedDeck.combine (frame.cutGrade F 1 0 1 site - inputs.firstLevel)
        (inputs.secondLevel - frame.cutGrade F 0 1 1 site) ∈ frame.child.modifiedDeck.span := ⟨_, _, rfl⟩
    refine ⟨_, hmem, (inputs.freeInvariant _ hmem site).mpr hfree, ?_, ?_⟩
    · rw [frame.cutGrade_add_combine F hper 1 0 1]
      ring
    · rw [frame.cutGrade_add_combine F hper 0 1 1]
      ring
  have hid : ∀ z, frame.cutGrade F 1 1 1 z = frame.cutGrade F 1 0 1 z + frame.cutGrade F 0 1 1 z := by
    intro z
    unfold ChildFrame.cutGrade
    ring
  intro level fort hne hfort hbounded
  refine no_restrictedFort_of_componentwise_exit (first := frame.cutGrade F 1 0 1)
    (second := frame.cutGrade F 0 1 1) (free := inputs.free) (bulkOrder := inputs.bulkOrder)
    (freeOrder := inputs.freeOrder) (deck := frame.child.modifiedDeck) inputs.firstLevel inputs.secondLevel
    hlocal heven hcharge hperm hfirst hsecond hnormalize inputs.bulk inputs.gate (a := 1) (c := 1)
    one_pos one_pos level fort hne hfort ?_
  intro site hsite
  have h := hbounded site hsite
  rw [hid] at h
  simpa using h

end FLatticePaper.Induction
