import FLatticePaper.Tiles.BaseTileProps
import FLatticePaper.Tiles.BaseWeakDomains
import FLatticePaper.Tiles.DeckCoverage
import FLatticePaper.Tiles.StandardBaseBridge
import FLatticePaper.Tiles.NearBaseBridges
import FLatticePaper.Construction.PropBaseCases

/-! # The lattice compatibilities of the base odometers (`WeakProps` at base words)

`prop:base_cases` (item (c)) gives, for each base family, a field on `Z^2` with the generator periods of the fraction
(`UniqueRecurrentExtension`, `UniqueNearOneExtension`) that agrees with the paper value on the paper tile. Restricting the
periods to the odometer domain, with the shift `s` of the family (`(0,1)` for the near-one families), gives
`LatticeSelfCompatible` along the kernel of the modified deck (constant `cU`) and along the transverse vector (affine
factor `offsetA`). The fractions of the base words are the current fractions of `parentsAt`. -/

namespace FLatticePaper.Tiles.BaseWeakLattice

open FLatticePaper.Farey
open FLatticePaper.Construction
open FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard
open FLatticePaper.Tiles.BaseTileProps
open FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.DeckCoverage
open FLatticePaper.Tiles.SurgicalWeak

/-- A periodic field restricted to an odometer that reads it at the shift `s` is `LatticeSelfCompatible` along the kernel
(constant `cU`) and along the transverse vector (affine factor `offsetA`). -/
theorem latticeSelf_of_periods (o : PartialOdometer) (F : Fraction) (g : Site → ℤ) (s : Site) (cU cV : ℤ)
    (hg : HasGeneratorPeriods F g cU cV) (hv : ∀ x ∈ o.dom, o.val x = g (x + s)) :
    LatticeSelfCompatible o F.modifiedDeck.kernel 0 ∧
      LatticeSelfCompatible o F.modifiedDeck.transverse (offsetA F.num F.den true) := by
  constructor
  · refine ⟨cU, fun x hx hxv => ?_⟩
    rw [hv _ hxv, hv _ hx]
    have h := hg.1 (x + s)
    have e : x + F.modifiedDeck.kernel + s = x + s + F.modifiedDeck.kernel := by abel
    rw [e, h]
    simp [dotS]
  · refine ⟨cV - F.transverseGrade s, fun x hx hxv => ?_⟩
    rw [hv _ hxv, hv _ hx]
    have h := hg.2 (x + s)
    have e : x + F.modifiedDeck.transverse + s = x + s + F.modifiedDeck.transverse := by abel
    rw [e, h]
    have hg2 : F.transverseGrade (x + s) = F.transverseGrade x + F.transverseGrade s := by
      unfold Fraction.transverseGrade
      simp
      ring
    have hd : dotS (offsetA F.num F.den true) x = -(F.transverseGrade x) := by
      simp [offsetA, dotS, Fraction.transverseGrade]
      ring
    rw [hg2, hd]
    ring

/-- The even stair `stairF d` with `d = 2k+3` (the even tile of `[]` at `k = 0` and of `3^k`). -/
theorem weakProps_stair (k : ℕ) (d : ℤ) (hd : d = 2 * (k : ℤ) + 3) (E : PartialOdometer)
    (hdom : E.dom = stairF d) (hval : ∀ x ∈ E.dom, E.val x = paperStairValue d x) :
    LatticeSelfCompatible E (texV1Even (⟨1, 2 * (k : ℤ) + 3⟩ : Fraction)) 0 ∧
      LatticeSelfCompatible E (texV2 (⟨1, 2 * (k : ℤ) + 3⟩ : Fraction)) (offsetA 1 (2 * (k : ℤ) + 3) true) := by
  subst hd
  obtain ⟨cU, cV, g, hagree, hper, -⟩ := (prop_base_cases_reciprocal_stair k).2.2.1.2.1
  have hv : ∀ x ∈ E.dom, E.val x = g (x + (0, 0)) := by
    intro x hx
    have hmem : x ∈ paperStairTile (2 * (k : ℤ) + 3) :=
      (mem_stairF_iff_paper (d := 2 * (k : ℤ) + 3) (by omega) x).1 (by rw [← hdom]; exact hx)
    rw [show x + ((0 : ℤ), (0 : ℤ)) = x by ext <;> simp, hval x hx]
    exact (hagree x hmem).symm
  have he : Fraction.Even (⟨1, 2 * (k : ℤ) + 3⟩ : Fraction) := by
    show (1 + (2 * (k : ℤ) + 3)) % 2 = 0
    omega
  have key := latticeSelf_of_periods E (⟨1, 2 * (k : ℤ) + 3⟩ : Fraction) g (0, 0) cU cV hper hv
  rw [modifiedDeck_kernel_of_even he, modifiedDeck_transverse] at key
  exact key

/-- The odd near-one stair `nstairN d` with `d = 2k+3` (the odd tile of `[]` at `k = 0` and of `2^k`). -/
theorem lattice_nearStair (k : ℕ) (d : ℤ) (hd : d = 2 * (k : ℤ) + 3) (O : PartialOdometer)
    (hdom : O.dom = nstairN d) (hval : ∀ x ∈ O.dom, O.val x = paperNearStairValue d (x + (0, 1))) :
    LatticeSelfCompatible O (texV1Odd (⟨(k : ℤ) + 1, (k : ℤ) + 2⟩ : Fraction)) 0 ∧
      LatticeSelfCompatible O (texV2 (⟨(k : ℤ) + 1, (k : ℤ) + 2⟩ : Fraction))
        (offsetA ((k : ℤ) + 1) ((k : ℤ) + 2) true) := by
  subst hd
  obtain ⟨cU, cV, g, hagree, hper, -⟩ := (prop_base_cases_near_stair k).2.2.1.2.1
  rw [rotate_stair_fraction k] at hper
  have hv : ∀ x ∈ O.dom, O.val x = g (x + (0, 1)) := by
    intro x hx
    obtain ⟨a, b⟩ := x
    have h1 : (a, b + 1) ∈ nstairF (2 * (k : ℤ) + 3) :=
      (mem_nstairN_ab (2 * (k : ℤ) + 3) a b).1 (by rw [← hdom]; exact hx)
    have hmem : (a, b) + ((0 : ℤ), (1 : ℤ)) ∈ paperNearStairTile (2 * (k : ℤ) + 3) := by
      rw [show (a, b) + ((0 : ℤ), (1 : ℤ)) = (a, b + 1) by ext <;> simp]
      exact (mem_nstairF_iff_paper (d := 2 * (k : ℤ) + 3) (by omega) (a, b + 1)).1 h1
    rw [hval (a, b) hx]
    exact (hagree _ hmem).symm
  have ho : Fraction.Odd (⟨(k : ℤ) + 1, (k : ℤ) + 2⟩ : Fraction) := by
    show ((k : ℤ) + 1 + ((k : ℤ) + 2)) % 2 = 1
    omega
  have key := latticeSelf_of_periods O (⟨(k : ℤ) + 1, (k : ℤ) + 2⟩ : Fraction) g (0, 1) cU cV hper hv
  rw [modifiedDeck_kernel_of_odd ho, modifiedDeck_transverse] at key
  exact key

/-- The odd ladder `ladderF d` with `d = 2k+2` for `k ≥ 1` (the odd tile of `3^k`). -/
theorem lattice_ladder (k : ℕ) (hk : 1 ≤ k) (d : ℤ) (hd : d = 2 * (k : ℤ) + 2) (O : PartialOdometer)
    (hdom : O.dom = ladderF d) (hval : ∀ x ∈ O.dom, O.val x = paperLadderValue d x) :
    LatticeSelfCompatible O (texV1Odd (⟨1, 2 * (k : ℤ) + 2⟩ : Fraction)) 0 ∧
      LatticeSelfCompatible O (texV2 (⟨1, 2 * (k : ℤ) + 2⟩ : Fraction)) (offsetA 1 (2 * (k : ℤ) + 2) true) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 1 := ⟨k - 1, by omega⟩
  have hd' : d = 2 * (m : ℤ) + 4 := by rw [hd]; push_cast; ring
  subst hd'
  obtain ⟨cU, cV, g, hagree, hper, -⟩ := (prop_base_cases_doubled_stair m).2.2.1.2.1
  have e : (2 * ((m + 1 : ℕ) : ℤ) + 2) = 2 * (m : ℤ) + 4 := by push_cast; ring
  rw [e]
  have hv : ∀ x ∈ O.dom, O.val x = g (x + (0, 0)) := by
    intro x hx
    have hmem : x ∈ paperLadderTile (2 * (m : ℤ) + 4) :=
      (mem_ladderF_iff_paper (d := 2 * (m : ℤ) + 4) (by omega) x).1 (by rw [← hdom]; exact hx)
    rw [show x + ((0 : ℤ), (0 : ℤ)) = x by ext <;> simp, hval x hx]
    exact (hagree x hmem).symm
  have ho : Fraction.Odd (⟨1, 2 * (m : ℤ) + 4⟩ : Fraction) := by
    show (1 + (2 * (m : ℤ) + 4)) % 2 = 1
    omega
  have key := latticeSelf_of_periods O (⟨1, 2 * (m : ℤ) + 4⟩ : Fraction) g (0, 0) cU cV hper hv
  rw [modifiedDeck_kernel_of_odd ho, modifiedDeck_transverse] at key
  exact key

/-- The even near-one ladder `nladderN d` with `d = 2k+2` for `k ≥ 1` (the even tile of `2^k`). -/
theorem lattice_nearLadder (k : ℕ) (hk : 1 ≤ k) (d : ℤ) (hd : d = 2 * (k : ℤ) + 2) (E : PartialOdometer)
    (hdom : E.dom = nladderN d) (hval : ∀ x ∈ E.dom, E.val x = paperNearLadderValue d (x + (0, 1))) :
    LatticeSelfCompatible E (texV1Even (⟨2 * (k : ℤ) + 1, 2 * (k : ℤ) + 3⟩ : Fraction)) 0 ∧
      LatticeSelfCompatible E (texV2 (⟨2 * (k : ℤ) + 1, 2 * (k : ℤ) + 3⟩ : Fraction))
        (offsetA (2 * (k : ℤ) + 1) (2 * (k : ℤ) + 3) true) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 1 := ⟨k - 1, by omega⟩
  have hd' : d = 2 * (m : ℤ) + 4 := by rw [hd]; push_cast; ring
  subst hd'
  obtain ⟨cU, cV, g, hagree, hper, -⟩ := (prop_base_cases_near_doubled_stair m).2.2.1.2.1
  rw [rotate_ladder_fraction m] at hper
  have e3 : (2 * ((m + 1 : ℕ) : ℤ) + 1) = 2 * (m : ℤ) + 3 := by push_cast; ring
  have e4 : (2 * ((m + 1 : ℕ) : ℤ) + 3) = 2 * (m : ℤ) + 5 := by push_cast; ring
  rw [e3, e4]
  have hv : ∀ x ∈ E.dom, E.val x = g (x + (0, 1)) := by
    intro x hx
    obtain ⟨a, b⟩ := x
    have h1 : (a, b + 1) ∈ nladderF (2 * (m : ℤ) + 4) :=
      (mem_nladderN_ab (2 * (m : ℤ) + 4) a b).1 (by rw [← hdom]; exact hx)
    have hmem : (a, b) + ((0 : ℤ), (1 : ℤ)) ∈ paperNearLadderTile (2 * (m : ℤ) + 4) := by
      rw [show (a, b) + ((0 : ℤ), (1 : ℤ)) = (a, b + 1) by ext <;> simp]
      exact (mem_nladderF_iff_paper (d := 2 * (m : ℤ) + 4) (by omega) (a, b + 1)).1 h1
    rw [hval (a, b) hx]
    exact (hagree _ hmem).symm
  have he : Fraction.Even (⟨2 * (m : ℤ) + 3, 2 * (m : ℤ) + 5⟩ : Fraction) := by
    show (2 * (m : ℤ) + 3 + (2 * (m : ℤ) + 5)) % 2 = 0
    omega
  have key := latticeSelf_of_periods E (⟨2 * (m : ℤ) + 3, 2 * (m : ℤ) + 5⟩ : Fraction) g (0, 1) cU cV hper hv
  rw [modifiedDeck_kernel_of_even he, modifiedDeck_transverse] at key
  exact key

/-- `WeakProps` at every base word, from the paper base condition alone: the lattice compatibilities of the base
odometers along the two lattice vectors of the current fractions of `parentsAt w`. -/
theorem weakProps_base (w : Word) (hw : IsBase w) (O E : PartialOdometer) (hS : PaperBaseCond w O E) :
    WeakProps w O E := by
  by_cases hnil : w = []
  · subst hnil
    obtain ⟨hOd, hOv, hEd, hEv⟩ := hS.1 rfl
    obtain ⟨hO1, hO2⟩ := lattice_nearStair 0 3 (by norm_num) O hOd hOv
    obtain ⟨hE1, hE2⟩ := weakProps_stair 0 3 (by norm_num) E hEd hEv
    have hcO : (parentsAt ([] : Word)).current .odd = ⟨((0 : ℕ) : ℤ) + 1, ((0 : ℕ) : ℤ) + 2⟩ := by
      show (parentsAt (List.replicate 0 Digit.three)).current .odd = _
      rw [cur_odd_three 0]
      congr 1
    have hcE : (parentsAt ([] : Word)).current .even = ⟨1, 2 * ((0 : ℕ) : ℤ) + 3⟩ := cur_even_three 0
    unfold WeakProps
    dsimp only
    rw [hcO, hcE]
    exact ⟨hO1, hO2, hE1, hE2⟩
  · rcases hw with hnil' | hthree | htwo
    · exact absurd hnil' hnil
    · obtain ⟨k, rfl⟩ : ∃ k, w = List.replicate k Digit.three :=
        ⟨w.length, List.eq_replicate_iff.2 ⟨rfl, hthree⟩⟩
      have hk : 1 ≤ k := by
        by_contra hc
        apply hnil
        have h0 : k = 0 := by omega
        subst h0
        rfl
      obtain ⟨hOd, hOv, hEd, hEv⟩ := hS.2.1 k hk rfl
      obtain ⟨hO1, hO2⟩ := lattice_ladder k hk (2 * (k : ℤ) + 2) rfl O hOd hOv
      obtain ⟨hE1, hE2⟩ := weakProps_stair k (2 * (k : ℤ) + 3) rfl E hEd hEv
      unfold WeakProps
      dsimp only
      rw [cur_odd_three k, cur_even_three k]
      exact ⟨hO1, hO2, hE1, hE2⟩
    · obtain ⟨k, rfl⟩ : ∃ k, w = List.replicate k Digit.two :=
        ⟨w.length, List.eq_replicate_iff.2 ⟨rfl, htwo⟩⟩
      have hk : 1 ≤ k := by
        by_contra hc
        apply hnil
        have h0 : k = 0 := by omega
        subst h0
        rfl
      obtain ⟨hOd, hOv, hEd, hEv⟩ := hS.2.2 k hk rfl
      obtain ⟨hO1, hO2⟩ := lattice_nearStair k (2 * (k : ℤ) + 3) rfl O hOd hOv
      obtain ⟨hE1, hE2⟩ := lattice_nearLadder k hk (2 * (k : ℤ) + 2) rfl E hEd hEv
      unfold WeakProps
      dsimp only
      rw [cur_odd_two k, cur_even_two k]
      exact ⟨hO1, hO2, hE1, hE2⟩

end FLatticePaper.Tiles.BaseWeakLattice
