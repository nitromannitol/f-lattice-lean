import FLatticePaper.Plane.Induction.W1ZeroPitch
import FLatticePaper.Plane.Induction.StrongResidual
import FLatticePaper.Plane.Induction.SignedPolicy

/-! # Task 84: the tie band of the earlier chain potential (rank bound and sandwich)

The tie band of a sheet pair is the level set `{Φ = K}` of the chain potential `Φ = frame.chainPotential G η` of the earlier field, in the
parent coordinates. Two facts about it are proved here, generically:

* `chainPotential_drift`: `Φ` drifts by `−1` along the child kernel `U` and by `2η` along the child transverse `V` (from the price and slip
  drifts of the strong residual). So `Φ` is invariant under `W = 2η U + V`, and the rank `R` of the policy (drifts `−λ`, `2ηλ`) has the
  same structure.
* `rank_bound_on_band`: on the level set `{Φ = K}`, the rank `R` is bounded above. Every site is `w0 + iU + jV` with `w0` in a finite box
  (the modulus is the determinant `D` of `U, V`, and `D e₁, D e₂` lie in the lattice `ZU + ZV`); on the level set `R = R(w0) − λ(Φ(w0) − K)`.
* `chain_sandwich`: along a retained chain `p₀ → p₁ → p₂ → z` with `Φ` nonincreasing along retained edges, `Φ z = K` and `Φ p₀ = K` force
  `Φ p₁ = K` and `Φ p₂ = K`: the chain stays in the tie band. -/

namespace FLatticePaper.W1TieBand

open FLatticePaper FLatticePaper.Induction FLatticePaper.W1ZeroPitch

/-- **The rank bound on a level set** (task 84): if `Φ` and `R` drift by `(−1, 2η)` and `(−λ, 2ηλ)` along `U` and `V` and the determinant of
`U, V` is nonzero, then `R` is bounded above on `{Φ = K}`. -/
theorem rank_bound_on_band {U V : Site} (hD : U.1 * V.2 - U.2 * V.1 ≠ 0) {Φ R : Site → ℤ} {η lam K : ℤ}
    (hΦU : ∀ x, Φ (x + U) = Φ x - 1) (hΦV : ∀ x, Φ (x + V) = Φ x + 2 * η)
    (hRU : ∀ x, R (x + U) = R x - lam) (hRV : ∀ x, R (x + V) = R x + 2 * η * lam) :
    ∃ B : ℤ, ∀ x, Φ x = K → R x ≤ B := by
  set D := U.1 * V.2 - U.2 * V.1 with hDdef
  have hΦ : ∀ (i j : ℤ) (w : Site), Φ (w + i • U + j • V) = Φ w - i + 2 * η * j := by
    intro i j w
    have h1 := shift_zsmul (f := Φ) (v := U) (c := -1) (fun z => by rw [hΦU z]; ring) i w
    have h2 := shift_zsmul (f := Φ) (v := V) (c := 2 * η) (fun z => by rw [hΦV z]) j (w + i • U)
    rw [h2, h1]
    ring
  have hR : ∀ (i j : ℤ) (w : Site), R (w + i • U + j • V) = R w + i * (-lam) + j * (2 * η * lam) := by
    intro i j w
    have h1 := shift_zsmul (f := R) (v := U) (c := -lam) (fun z => by rw [hRU z]; ring) i w
    have h2 := shift_zsmul (f := R) (v := V) (c := 2 * η * lam) (fun z => by rw [hRV z]) j (w + i • U)
    rw [h2, h1]
  have hD0 : D ≠ 0 := hD
  set box : Finset (ℤ × ℤ) := Finset.Icc (-|D|) |D| ×ˢ Finset.Icc (-|D|) |D| with hbox
  obtain ⟨B, hB⟩ := Finset.exists_le
    (box.image (fun p : ℤ × ℤ => R (p.1, p.2) - lam * (Φ (p.1, p.2) - K)))
  refine ⟨B, fun x htie => ?_⟩
  set w0 : Site := (x.1 % D, x.2 % D) with hw0
  have hw0box : w0 ∈ box := by
    have h1 := Int.emod_nonneg x.1 hD0
    have h2 := Int.emod_lt x.1 hD0
    have h3 := Int.emod_nonneg x.2 hD0
    have h4 := Int.emod_lt x.2 hD0
    rw [hbox]
    simp only [Finset.mem_product, Finset.mem_Icc, hw0]
    have hab := Int.abs_eq_natAbs D
    refine ⟨⟨by linarith [abs_nonneg D], by linarith⟩, ⟨by linarith [abs_nonneg D], by linarith⟩⟩
  set i : ℤ := x.1 / D * V.2 - x.2 / D * V.1 with hi
  set j : ℤ := -(x.1 / D) * U.2 + x.2 / D * U.1 with hj
  have hdec : x = w0 + i • U + j • V := by
    have e1 : x.1 % D = x.1 - D * (x.1 / D) := Int.emod_def x.1 D
    have e2 : x.2 % D = x.2 - D * (x.2 / D) := Int.emod_def x.2 D
    refine Prod.ext ?_ ?_
    · simp only [hw0, hi, hj, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      linear_combination (-1 : ℤ) * e1
    · simp only [hw0, hi, hj, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      linear_combination (-1 : ℤ) * e2
  have hΦx : Φ w0 - i + 2 * η * j = K := by
    have h := hΦ i j w0
    rw [← hdec, htie] at h
    linarith
  have hfin := hB _ (Finset.mem_image_of_mem _ hw0box)
  have hRx : R x = R w0 - lam * (Φ w0 - K) := by
    have h := hR i j w0
    rw [← hdec] at h
    rw [h]
    linear_combination lam * hΦx
  rw [hRx]
  exact hfin

/-- The chain potential drifts along the kernel and the transverse vector: `−1` and `2η`, from the price and slip drifts. -/
theorem chainPotential_drift {frame : ChildFrame} {G : Field} {η : ℤ}
    (hprice : ∀ z, frame.price G (z + frame.child.modifiedDeck.kernel) - frame.price G z = -1 ∧
      frame.price G (z + frame.child.modifiedDeck.transverse) - frame.price G z = 0)
    (hslip : ∀ z, frame.slip G η (z + frame.child.modifiedDeck.kernel) - frame.slip G η z = 0 ∧
      frame.slip G η (z + frame.child.modifiedDeck.transverse) - frame.slip G η z = 2 * η) :
    (∀ x, frame.chainPotential G η (x + frame.child.modifiedDeck.kernel) = frame.chainPotential G η x - 1) ∧
      (∀ x, frame.chainPotential G η (x + frame.child.modifiedDeck.transverse) = frame.chainPotential G η x + 2 * η) := by
  constructor
  · intro x
    unfold ChildFrame.chainPotential
    have e : x + frame.child.modifiedDeck.kernel + η • frame.shortShift =
        (x + η • frame.shortShift) + frame.child.modifiedDeck.kernel := by abel
    rw [e]
    have h1 := (hprice (x + η • frame.shortShift)).1
    have h2 := (hslip x).1
    linarith
  · intro x
    unfold ChildFrame.chainPotential
    have e : x + frame.child.modifiedDeck.transverse + η • frame.shortShift =
        (x + η • frame.shortShift) + frame.child.modifiedDeck.transverse := by abel
    rw [e]
    have h1 := (hprice (x + η • frame.shortShift)).2
    have h2 := (hslip x).2
    linarith

/-- **The chain sandwich** (task 84): along a chain `p₀ → p₁ → p₂ → z` of retained edges, with `Φ` nonincreasing along retained edges,
`Φ z = K` and `Φ p₀ = K` force `Φ p₁ = K` and `Φ p₂ = K`. -/
theorem chain_sandwich {Φ : Site → ℤ} {Rel : Site → Site → Prop} {p0 p1 p2 z : Site} {K : ℤ}
    (hmono : NonincreasingAlong Φ Rel) (h0 : Rel p0 p1) (h1 : Rel p1 p2) (h2 : Rel p2 z)
    (hz : Φ z = K) (hp0 : Φ p0 = K) : Φ p1 = K ∧ Φ p2 = K := by
  have a0 := hmono p0 p1 h0
  have a1 := hmono p1 p2 h1
  have a2 := hmono p2 z h2
  constructor <;> linarith

end FLatticePaper.W1TieBand
