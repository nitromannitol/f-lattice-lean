import FLatticePaper.Plane.BellmanRank
import Mathlib.Data.Int.LeastGreatest

namespace FLatticePaper

open Farey

theorem IsIncomingFort.translate {field : Field} {fort : Set Site} (hfort : IsIncomingFort field fort)
    {step : Site} (heven : EvenSite step) (hcharge : ∀ site, laplacian field (site + step) = laplacian field site) :
    IsIncomingFort field ((fun site => site + step) '' fort) := by
  rintro _ ⟨site, hmem, rfl⟩
  simp only [hcharge, incomingNeg_add_of_even _ _ heven, incomingPos_add_of_even _ _ heven]
  rcases hfort site hmem with ⟨hl, hn | hp⟩ | ⟨hl, hn, hp⟩
  · exact Or.inl ⟨hl, Or.inl ⟨_, hn, rfl⟩⟩
  · exact Or.inl ⟨hl, Or.inr ⟨_, hp, rfl⟩⟩
  · exact Or.inr ⟨hl, ⟨_, hn, rfl⟩, ⟨_, hp, rfl⟩⟩

/-- Componentwise bulk decreases and actual fort-contact endpoints rule
out a fort bounded below in any strictly positive weighting of the grades.
The normalization translates one whole fort. The endpoint order is used
only at free sites of the normalized grade pair. -/
theorem no_boundedFort_of_componentwise_exit {field first second : Field} {free : Site → Prop}
    {bulkOrder freeOrder : Site → ℕ} {deck : PeriodDeck} (firstLevel secondLevel : ℤ)
    (heven : ∀ step ∈ deck.span, EvenSite step)
    (hcharge : ∀ step ∈ deck.span, ∀ site, laplacian field (site + step) = laplacian field site)
    (hfirst : ∀ step ∈ deck.span, ∃ increment : ℤ, ∀ site, first (site + step) = first site + increment)
    (hsecond : ∀ step ∈ deck.span, ∃ increment : ℤ, ∀ site, second (site + step) = second site + increment)
    (hnormalize : ∀ site, free site → ∃ step ∈ deck.span,
      free (site + step) ∧ first (site + step) = firstLevel ∧ second (site + step) = secondLevel)
    (hbulk : ∀ center, ¬ free center →
      let allowed (input : Site) := first input ≤ first center ∧ second input ≤ second center ∧
        bulkOrder input < bulkOrder center
      (laplacian field center = -1 ∧ allowed (incomingNeg center) ∧ allowed (incomingPos center)) ∨
      (laplacian field center = 0 ∧ (allowed (incomingNeg center) ∨ allowed (incomingPos center))))
    (hgate : ∀ fort : Set Site, IsIncomingFort field fort → ∀ site ∈ fort,
      free site → first site = firstLevel → second site = secondLevel → ∃ target ∈ fort,
        (first target ≤ firstLevel ∧ second target ≤ secondLevel ∧ (first target < firstLevel ∨ second target < secondLevel)) ∨
        (free target ∧ first target = firstLevel ∧ second target = secondLevel ∧ freeOrder target < freeOrder site))
    {a c : ℤ} (ha : 0 < a) (hc : 0 < c) (level : ℤ) (fort : Set Site) (hne : fort.Nonempty)
    (hfort : IsIncomingFort field fort) (hbounded : ∀ site ∈ fort, level ≤ a * first site + c * second site) : False := by
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
      · have hnext : ∃ input ∈ fort, first input ≤ first center ∧ second input ≤ second center ∧
            bulkOrder input < bulkOrder center := by
          rcases hbulk center hfree with ⟨hl, hn, hp⟩ | ⟨hl, hn | hp⟩ <;>
            rcases hfort center hcenter with ⟨hl', hmem | hmem⟩ | ⟨hl', hneg, hpos⟩
          · exact ⟨_, hmem, hn⟩
          · exact ⟨_, hmem, hp⟩
          · omega
          · omega
          · omega
          · exact ⟨_, hneg, hn⟩
          · omega
          · omega
          · exact ⟨_, hpos, hp⟩
        obtain ⟨input, hmem, hfirstLe, hsecondLe, hdrop⟩ := hnext
        have hgradeLe : grade input ≤ grade center := add_le_add
          (mul_le_mul_of_nonneg_left hfirstLe ha.le) (mul_le_mul_of_nonneg_left hsecondLe hc.le)
        exact ih (bulkOrder input) (horder ▸ hdrop) input rfl hmem
          (le_antisymm (hgradeLe.trans hgrade.le) (hleast_le input hmem))
  obtain ⟨freeSite, hfreeMem, hfree, hfreeMin⟩ := hreachesFree (bulkOrder point) point rfl hpoint hleast
  obtain ⟨step, hstep, hfreeShift, hfirstShift, hsecondShift⟩ := hnormalize freeSite hfree
  obtain ⟨dp, hdp⟩ := hfirst step hstep
  obtain ⟨dj, hdj⟩ := hsecond step hstep
  let shifted := (fun site => site + step) '' fort
  have hshifted : IsIncomingFort field shifted := hfort.translate (heven step hstep) (hcharge step hstep)
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
