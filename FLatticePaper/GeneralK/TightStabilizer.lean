import FLatticePaper.GeneralK.TightGraph
import FLatticePaper.GeneralK.WalkIntersection

namespace FLatticePaper.GeneralK

open Farey

private theorem sub_mem_span_of_residue_eq (deck : PeriodDeck) (hdet : deck.det ≠ 0) {x y : Site}
    (h : residueVertex deck.det.natAbs x = residueVertex deck.det.natAbs y) : x - y ∈ deck.span := by
  apply (deck.mem_span_iff_dvd hdet _).mpr
  have hnat : deck.det ∣ (deck.det.natAbs : ℤ) := by
    rw [← Int.natAbs_dvd_natAbs]
    simp
  have hx : deck.det ∣ x.1 - y.1 := hnat.trans ((ZMod.intCast_eq_intCast_iff_dvd_sub y.1 x.1 _).mp
    (congrArg Prod.fst h.symm))
  have hy : deck.det ∣ x.2 - y.2 := hnat.trans ((ZMod.intCast_eq_intCast_iff_dvd_sub y.2 x.2 _).mp
    (congrArg Prod.snd h.symm))
  exact ⟨Int.dvd_sub (dvd_mul_of_dvd_right hx _) (dvd_mul_of_dvd_right hy _),
    Int.dvd_sub (dvd_mul_of_dvd_right hy _) (dvd_mul_of_dvd_right hx _)⟩

section

variable {deck : PeriodDeck} {k : ℤ} {negative positive : Field} {potential : Site → ℝ} {slopeX slopeY : ℝ}
variable (hslope : HasDeckSlope deck potential slopeX slopeY)
variable (hphase : ∀ step ∈ deck.span, Retained k step)
variable (hneg : ∀ step ∈ deck.span, Function.Periodic negative step)
variable (hpos : ∀ step ∈ deck.span, Function.Periodic positive step)

include hslope hphase hneg hpos

private theorem TightReaches.shift {first last step : Site} (h : TightReaches k negative positive potential first last)
    (hstep : step ∈ deck.span) : TightReaches k negative positive potential (first + step) (last + step) :=
  h.add_of_period (hphase _ hstep) (hslope _ hstep) (hneg _ hstep) (hpos _ hstep)

private theorem TightReaches.zsmul_period {first step : Site} (hstep : step ∈ deck.span)
    (h : TightReaches k negative positive potential first (first + step)) (index : ℤ) :
    TightReaches k negative positive potential first (first + index • step) := by
  refine Int.inductionOn' index 0 (by simpa using (Relation.ReflTransGen.refl :
    TightReaches k negative positive potential first first)) ?_ ?_
  · intro j _ ih
    have hmem : j • step ∈ deck.span := (periodSubgroup deck).zsmul_mem hstep j
    have hshift := h.shift hslope hphase hneg hpos hmem
    rw [show first + step + j • step = first + (j + 1) • step by rw [add_zsmul, one_zsmul]; abel] at hshift
    exact ih.trans hshift
  · intro j _ ih
    have hmem : (j - 1) • step ∈ deck.span := (periodSubgroup deck).zsmul_mem hstep (j - 1)
    have hshift := h.symm.shift hslope hphase hneg hpos hmem
    rw [show first + step + (j - 1) • step = first + j • step by rw [sub_zsmul, one_zsmul]; abel] at hshift
    exact ih.trans hshift

private theorem exists_tight_components_meeting_modulo {first second u v : Site}
    (hu : u ∈ deck.span) (hv : v ∈ deck.span) (hind : u.1 * v.2 - u.2 * v.1 ≠ 0)
    (hfirst : TightReaches k negative positive potential first (first + u))
    (hsecond : TightReaches k negative positive potential second (second + v))
    (modulus : PeriodDeck) (hdet : modulus.det ≠ 0) :
    ∃ x y, TightReaches k negative positive potential first x ∧ TightReaches k negative positive potential second y ∧
      x - y ∈ modulus.span := by
  let n := modulus.det.natAbs
  letI : NeZero n := ⟨(Int.natAbs_pos.mpr hdet).ne'⟩
  have hpath₁ := hfirst.nsmul_period hslope hphase hneg hpos hu n
  have hpath₂ := hsecond.nsmul_period hslope hphase hneg hpos hv n
  obtain ⟨walk₁, he₁, hm₁⟩ := hpath₁.exists_axisWalk
  obtain ⟨walk₂, he₂, hm₂⟩ := hpath₂.exists_axisWalk
  have heq (point : Site) : n • point = ((n : ℤ) * point.1, (n : ℤ) * point.2) := by
    apply Prod.ext <;> simp [nsmul_eq_mul]
  rw [heq] at he₁ he₂
  by_contra! hn
  have hdisjoint (x : Site) (hx : x ∈ walkVertices first walk₁) (y : Site) (hy : y ∈ walkVertices second walk₂) :
      residueVertex n x ≠ residueVertex n y := by
    intro h
    exact hn x y (hm₁ x hx) (hm₂ y hy) (sub_mem_span_of_residue_eq modulus hdet h)
  exact hind (determinant_eq_zero_of_disjoint_squareWalks first second walk₁ walk₂ u.1 u.2 v.1 v.2 he₁ he₂ hdisjoint)

/-- Two independent tight windings imply that the first component reaches
every one of its period translates. First bring the two windings to one
component. Then use their own deck to compare it with any translate. -/
theorem tightReaches_all_periods_of_independent {first second u v : Site} (hdet : deck.det ≠ 0)
    (hu : u ∈ deck.span) (hv : v ∈ deck.span) (hind : u.1 * v.2 - u.2 * v.1 ≠ 0)
    (hfirst : TightReaches k negative positive potential first (first + u))
    (hsecond : TightReaches k negative positive potential second (second + v)) :
    ∀ step ∈ deck.span, TightReaches k negative positive potential first (first + step) := by
  obtain ⟨x, y, hx, hy, hspan⟩ := exists_tight_components_meeting_modulo hslope hphase hneg hpos
    hu hv hind hfirst hsecond deck hdet
  let shift := x - y
  have hys := hy.shift hslope hphase hneg hpos hspan
  have hright : y + shift = x := by dsimp only [shift]; abel
  change TightReaches k negative positive potential (second + shift) (y + shift) at hys
  rw [hright] at hys
  have hjoin : TightReaches k negative positive potential first (second + shift) := hx.trans hys.symm
  have hturn := hsecond.shift hslope hphase hneg hpos hspan
  change TightReaches k negative positive potential (second + shift) (second + v + shift) at hturn
  rw [add_right_comm second v shift] at hturn
  have hvfirst : TightReaches k negative positive potential first (first + v) :=
    hjoin.trans (hturn.trans (hjoin.shift hslope hphase hneg hpos hv).symm)
  let smaller : PeriodDeck := ⟨u, v⟩
  have hsmall : smaller.det ≠ 0 := hind
  have hgen (step : Site) (hstep : step ∈ smaller.span) : step ∈ deck.span ∧
      TightReaches k negative positive potential first (first + step) := by
    obtain ⟨i, j, rfl⟩ := hstep
    have heq : smaller.combine i j = i • u + j • v := by
      apply Prod.ext <;> simp [smaller, PeriodDeck.combine, zsmul_eq_mul]
    rw [heq]
    have hi : i • u ∈ deck.span := (periodSubgroup deck).zsmul_mem hu i
    have hj : j • v ∈ deck.span := (periodSubgroup deck).zsmul_mem hv j
    refine ⟨(periodSubgroup deck).add_mem hi hj, ?_⟩
    have h₁ := hfirst.zsmul_period hslope hphase hneg hpos hu i
    have h₂ := hvfirst.zsmul_period hslope hphase hneg hpos hv j
    have h₂' := h₂.shift hslope hphase hneg hpos hi
    rw [add_right_comm first (j • v) (i • u), add_assoc] at h₂'
    exact h₁.trans h₂'
  intro step hstep
  have hlo := hvfirst.shift hslope hphase hneg hpos hstep
  rw [add_right_comm first v step] at hlo
  obtain ⟨s, t, hs, ht, hdiff⟩ := exists_tight_components_meeting_modulo hslope hphase hneg hpos
    hu hv hind hfirst hlo smaller hsmall
  let delta := s - t
  have hdelta := (hgen delta hdiff).1
  have hnsmall : -delta ∈ smaller.span := (periodSubgroup smaller).neg_mem hdiff
  obtain ⟨hn, hstart⟩ := hgen (-delta) hnsmall
  have ht' := ht.shift hslope hphase hneg hpos hdelta
  rw [show t + delta = s by dsimp only [delta]; abel] at ht'
  have hwalk : TightReaches k negative positive potential first (first + step + delta) := hs.trans ht'.symm
  have hwalk' := hwalk.shift hslope hphase hneg hpos hn
  rw [show first + step + delta + -delta = first + step by abel] at hwalk'
  exact hstart.trans hwalk'

end
end FLatticePaper.GeneralK
