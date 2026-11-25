import FLatticePaper.Plane.Induction.SignedPolicy
import FLatticePaper.Plane.BellmanRank

/-! # The retained-quota core (Q23 step 4): the strict-interior part of a fort is empty

A fort `S` of the field `M` (`IsIncomingFort M S`) lies in a region `P`, and its boundary points (`P` minus the open region `Q`) are
among candidates `C`. The retained relation `R` of the W1 policy (`RetainQuota G R`: a black centre retains both inputs, a white centre at
least one) decreases a rank `Rk` along the retained edges (`hrank`). Then the strict-interior part `{x ∈ S | Q x}` is a retained fort:
every point has a retained input in it. Its points are not candidates (`hcand`), and no interior point has a candidate as an input
(`hnc`, the geometric fact that the candidates are not called from the interior). A finite nonempty retained fort has a point of
least rank, whose retained input has smaller rank: contradiction. So the strict-interior part is empty.

The field `M` agrees with the policy field `G` on `P` (`hagree`): the Laplacian of an interior point uses only `P`. -/

namespace FLatticePaper.RetainedCore

open FLatticePaper

/-- **The strict-interior part of a fort is empty.** -/
theorem interior_empty_of_retained {P : Set Site} {Q : Site → Prop} {M G : Field}
    {R : Site → Site → Prop} {Rk : Site → ℤ} {C : Site → Prop} {S : Set Site}
    (hQfin : {x | Q x}.Finite)
    (hQin : ∀ x, Q x → ∀ i : Site, (i = incomingNeg x ∨ i = incomingPos x) → i ∈ P)
    (hagree : ∀ y ∈ P, M y = G y)
    (hquota : RetainQuota G R)
    (hrank : ∀ c i, R c i → Rk i < Rk c)
    (hfort : IsIncomingFort M S)
    (hsub : ∀ z ∈ S, z ∈ P)
    (hcand : ∀ z ∈ S, z ∈ P → ¬ Q z → C z)
    (hnc : ∀ x, Q x → ∀ k, C k → ¬ (k = incomingNeg x ∨ k = incomingPos x)) :
    ∀ x, x ∈ S → ¬ Q x := by
  have hIfin : {x | x ∈ S ∧ Q x}.Finite := hQfin.subset (fun x hx => hx.2)
  -- every point of the strict-interior part has a retained input in it
  have hret : ∀ x, x ∈ S → Q x → ∃ i, R x i ∧ i ∈ S ∧ Q i := by
    intro x hxS hxQ
    have hxP := hsub x hxS
    have hlap : laplacian M x = laplacian G x := by
      unfold laplacian
      rw [hagree x hxP, hagree _ (hQin x hxQ _ (Or.inl rfl)), hagree _ (hQin x hxQ _ (Or.inr rfl))]
    have key : ∀ j, (j = incomingNeg x ∨ j = incomingPos x) → j ∈ S → R x j → ∃ i, R x i ∧ i ∈ S ∧ Q i := by
      intro j hj hjS hRj
      have hQj : Q j := by
        by_contra hnQ
        exact hnc x hxQ j (hcand j hjS (hQin x hxQ j hj) hnQ) hj
      exact ⟨j, hRj, hjS, hQj⟩
    rcases hfort x hxS with ⟨hl, hsome⟩ | ⟨hl, hn, hp⟩
    · have hG : laplacian G x = -1 := by rw [← hlap]; exact hl
      obtain ⟨hRn, hRp⟩ := hquota.1 x hG
      rcases hsome with hsn | hsp
      · exact key _ (Or.inl rfl) hsn hRn
      · exact key _ (Or.inr rfl) hsp hRp
    · have hG : laplacian G x = 0 := by rw [← hlap]; exact hl
      rcases hquota.2 x hG with hRn | hRp
      · exact key _ (Or.inl rfl) hn hRn
      · exact key _ (Or.inr rfl) hp hRp
  -- a finite nonempty retained fort has a point of least rank, whose retained input has smaller rank
  have hall : ∀ x, x ∈ {x | x ∈ S ∧ Q x} → False := by
    intro x0 hx0
    have hne : hIfin.toFinset.Nonempty := ⟨x0, hIfin.mem_toFinset.mpr hx0⟩
    obtain ⟨x, hxF, hmin⟩ := hIfin.toFinset.exists_min_image Rk hne
    have hxI : x ∈ {x | x ∈ S ∧ Q x} := hIfin.mem_toFinset.mp hxF
    obtain ⟨i, hR, hiS, hiQ⟩ := hret x hxI.1 hxI.2
    have h1 := hmin i (hIfin.mem_toFinset.mpr ⟨hiS, hiQ⟩)
    have h2 := hrank x i hR
    omega
  intro x hxS hxQ
  exact hall x ⟨hxS, hxQ⟩

end FLatticePaper.RetainedCore
