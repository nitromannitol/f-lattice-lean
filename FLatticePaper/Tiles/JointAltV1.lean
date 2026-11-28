import FLatticePaper.Tiles.JointFamily
import FLatticePaper.Tiles.AltRotStep
import FLatticePaper.Tiles.SeamSymm
import FLatticePaper.Tiles.CornerValues

/-! # The first lattice vector of the alternate tile odometers, from the rotation

(b) of `lemma:weak_alternate_odometer_properties` for an alternate tile odometer along its first lattice vector `v_{n/d,1}`
follows from the property along the second lattice vector of the rotated child, through the rotation identity (c) of
`lemma:tile-odometer-existence`: the rotation `x ↦ i x + c_f` sends `v_{R(n/d),2}` to `-v_{n/d,1}`, and the affine factor
`a_{R(n/d),2}` cancels against the shift of `h_0` (`eq:h0_identities`, `H v_{f,2} = a_{f,2}`). The domains correspond, since the
two alternate tiles are rotations of each other (`AltRotStep.altRot`). -/

namespace FLatticePaper.Tiles.JointAltV1

open FLatticePaper.Farey
open FLatticePaper.Construction (texV1Odd texV1Even texV2)
open FLatticePaper.Tiles
open FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.Standard (swapW shift rot)
open FLatticePaper.Tiles.SurgicalAltTiles (altOddTile altEvenTile)

/-- **The first lattice vector from the rotation.** If `o_R(x) = o(i x + c_f) - h_0(x) + γ^T x + c_0` (normalised), every point of
the domain of `o` is the image of a point of the domain of `o_R`, `o_R` is compatible along `(n - d, n + d)` with affine factor
`(n, -d)`, and `i (n - d, n + d) = -v_1`, then `o` is compatible along `v_1` with affine factor `0`. -/
theorem lattice_v1_of_rot (o oR : PartialOdometer) (cf γ : Site) (h : AltRotation o oR cf γ)
    (hsurj : ∀ y ∈ o.dom, ∃ x ∈ oR.dom, mulI x + cf = y) (n d : ℤ) (v1 : Site)
    (hiv : mulI ((n - d, n + d) : Site) = -v1) (hc : LatticeSelfCompatible oR (n - d, n + d) (n, -d)) :
    LatticeSelfCompatible o v1 0 := by
  obtain ⟨α, β, α', β', c0, -, -, hrot⟩ := h
  obtain ⟨cR, hcR⟩ := hc
  refine ⟨-cR + dotS α' (n - d, n + d) - dotS α (mulI (n - d, n + d)) - h0 (n - d, n + d) + dotS γ (n - d, n + d),
    fun y hy hyv => ?_⟩
  obtain ⟨x, hx, rfl⟩ := hsurj y hy
  obtain ⟨x', hx', hx'e⟩ := hsurj _ hyv
  have hxx : x = x' + (n - d, n + d) := by
    have h1 := congrArg Prod.fst hx'e
    have h2 := congrArg Prod.snd hx'e
    have h3 := congrArg Prod.fst hiv
    have h4 := congrArg Prod.snd hiv
    simp only [mulI, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg] at h1 h2 h3 h4
    ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> linarith
  have hxv : x' + (n - d, n + d) ∈ oR.dom := hxx ▸ hx
  obtain ⟨-, r1⟩ := hrot x' hx'
  obtain ⟨-, r2⟩ := hrot x hx
  have hcomp := hcR x' hx' hxv
  rw [hxx] at r2
  have hsh := CornerValues.h0_shift x' (n - d, n + d) (by simp; omega)
  have hell : CornerValues.ellOf ((n - d, n + d) : Site) = (-n, d) := by
    simp only [CornerValues.ellOf]; ext <;> simp <;> omega
  rw [hell] at hsh
  have hh : ∀ z : Site, h0 z = zoH0 z := fun z => rfl
  rw [← hx'e]
  subst hxx
  simp only [normed, dotS, hh, Prod.fst_add, Prod.snd_add, mulI] at r1 r2 hcomp hsh ⊢
  simp only [Prod.fst_zero, Prod.snd_zero, zero_mul, add_zero]
  linarith

/-- An injective-image argument: a finite set maps into another of the same size only onto it. -/
theorem onto_of_card (A B : Finset Site) (g : Site → Site) (hg : ∀ a b, g a = g b → a = b) (hmap : ∀ x ∈ A, g x ∈ B)
    (hcard : B.card ≤ A.card) : ∀ y ∈ B, ∃ x ∈ A, g x = y := by
  have hsub : A.image g ⊆ B := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    exact hmap x hx
  have hc : (A.image g).card = A.card := Finset.card_image_of_injective _ (fun a b h => hg a b h)
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hc]; exact hcard)
  intro y hy
  rw [← heq] at hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
  exact ⟨x, hx, rfl⟩

theorem card_shift_rot (T : Standard.Tile) (τ : Site) : (shift (rot T) τ).card = T.card := by
  unfold shift rot
  rw [Finset.card_image_of_injective _ (add_left_injective τ), Finset.card_image_of_injective]
  intro a b h
  simp only [mulI, Prod.mk.injEq] at h
  ext <;> linarith [h.1, h.2]

theorem mulI_inj (a b : Site) (h : mulI a = mulI b) : a = b := by
  simp only [mulI, Prod.mk.injEq] at h
  ext <;> linarith [h.1, h.2]

/-- **The full alternate lattice property after the rotation step**: the second-vector halves at `w` and at `swapW w`, the
rotation identities of the alternate tile odometers, and the domains (the printed alternate tiles) give both halves at `w`. -/
theorem altLattice_of_rot (w : Word) (x r : JSlice) (hrot : RotProps w x r)
    (hdO : x.aOdd.dom = altOddTile AltRotStep.B w) (hdE : x.aEven.dom = altEvenTile AltRotStep.B w)
    (hdO' : r.aOdd.dom = altOddTile AltRotStep.B (swapW w)) (hdE' : r.aEven.dom = altEvenTile AltRotStep.B (swapW w))
    (hv : AltLatticeV2 w x.aOdd x.aEven) (hv' : AltLatticeV2 (swapW w) r.aOdd r.aEven) :
    AltLatticeSelfCompat w x.aOdd x.aEven := by
  obtain ⟨-, -, hRo, hRe⟩ := hrot
  obtain ⟨hco, hce⟩ := SeamSymm.current_swap w
  have hV := parentsAt_valid w
  have hpo := hV.current_odd_parity
  have hpe := hV.current_even_parity
  obtain ⟨hrO, hrE⟩ := AltRotStep.altRot w
  refine ⟨⟨?_, hv.1⟩, ⟨?_, hv.2⟩⟩
  · -- the odd alternate child: from the even alternate child of `swapW w`
    have hsurj : ∀ y ∈ x.aOdd.dom, ∃ z ∈ r.aEven.dom, mulI z + (altCf w true).1 = y := by
      obtain ⟨α, β, α', β', c0, -, -, hm⟩ := hRo
      refine onto_of_card _ _ _ (fun a b h => mulI_inj a b (add_right_cancel h)) (fun z hz => (hm z hz).1) ?_
      rw [hdO, hdE', ← hrO, card_shift_rot]
    have hc := hv'.2
    simp only [AltLatticeEvenV2, hco] at hc
    rw [Standard.rotate_eq_of_odd hpo] at hc
    refine lattice_v1_of_rot _ _ _ _ hRo hsurj _ _ _ ?_ hc
    simp only [mulI, texV1Odd]
    ext <;> simp <;> ring
  · -- the even alternate child: from the odd alternate child of `swapW w`
    have hsurj : ∀ y ∈ x.aEven.dom, ∃ z ∈ r.aOdd.dom, mulI z + (altCf w false).1 = y := by
      obtain ⟨α, β, α', β', c0, -, -, hm⟩ := hRe
      refine onto_of_card _ _ _ (fun a b h => mulI_inj a b (add_right_cancel h)) (fun z hz => (hm z hz).1) ?_
      rw [hdE, hdO', ← hrE, card_shift_rot]
    have hc := hv'.1
    simp only [AltLatticeOddV2, hce] at hc
    rw [Standard.rotate_eq_of_even hpe] at hc
    unfold Fraction.Even at hpe
    have e : ((((parentsAt w).current .even).den - ((parentsAt w).current .even).num) / 2 -
        (((parentsAt w).current .even).den + ((parentsAt w).current .even).num) / 2,
        (((parentsAt w).current .even).den - ((parentsAt w).current .even).num) / 2 +
        (((parentsAt w).current .even).den + ((parentsAt w).current .even).num) / 2) =
        ((-((parentsAt w).current .even).num, ((parentsAt w).current .even).den) : Site) := by
      ext <;> simp <;> omega
    refine lattice_v1_of_rot _ _ _ _ hRe hsurj _ _ _ ?_ hc
    simp only [mulI, texV1Even]
    ext <;> simp <;> omega

end FLatticePaper.Tiles.JointAltV1
