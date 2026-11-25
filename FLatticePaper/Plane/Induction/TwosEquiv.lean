import FLatticePaper.Plane.Induction.TwosEPolicy

/-! Span equivariance of the twos signed policy `TwosSel` (the selection of `e(−1, η)` on `2^(k+1)`).

The alias lattice of `TwosSel` is the span `Λ = ⟨U, V⟩` of the child frame of `2^(k+1)`, with `U = (a+1, a−1)` and `V = (−2, 2a)`.
For `s ∈ Λ`, the aliases of `c + s` are the aliases of `c` (`alias_shift`). The displacements `freeDisp` and `candDisp` depend only
on the alias `u`, so `TwosSel` is equivariant: `TwosSel (c + s) (i + s) ↔ TwosSel c i`, given that the Laplacian is `Λ`-invariant. -/

namespace FLatticePaper.TwosEquiv

open FLatticePaper FLatticePaper.TwosEPolicy

/-- The alias set is invariant under the span translation `s = (I(a+1) − 2J, I(a−1) + 2aJ)`. -/
theorem alias_shift (a I J : ℤ) (s : Site) (hs : s = (I * (a + 1) - 2 * J, I * (a - 1) + 2 * a * J)) (c u : Site) :
    AliasOf a (c + s) u ↔ AliasOf a c u := by
  constructor
  · rintro ⟨i, l, hu⟩
    refine ⟨i - I, l - J, ?_⟩
    rw [hu, hs]
    ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
  · rintro ⟨i, l, hu⟩
    refine ⟨i + I, l + J, ?_⟩
    rw [hu, hs]
    ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring

/-- Cancellation of a span shift on the right. -/
theorem site_add_right_cancel' {x y s : Site} (h : x + s = y + s) : x = y := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [Prod.fst_add, Prod.snd_add] at h1 h2
  exact Prod.ext (by omega) (by omega)

/-- An even shift commutes with the incoming inputs. -/
theorem incomingNeg_add_even {p s : Site} (hs : EvenSite s) : incomingNeg (p + s) = incomingNeg p + s := by
  unfold incomingNeg EvenSite at *
  simp only [Prod.fst_add, Prod.snd_add] at *
  split_ifs <;> ext <;> simp <;> omega

theorem incomingPos_add_even {p s : Site} (hs : EvenSite s) : incomingPos (p + s) = incomingPos p + s := by
  unfold incomingPos EvenSite at *
  simp only [Prod.fst_add, Prod.snd_add] at *
  split_ifs <;> ext <;> simp <;> omega

/-- A span shift cancels in the displacement equation. -/
theorem shift_eq_iff (c i s d : Site) :
    i + s = ((c + s).1 + d.1, (c + s).2 + d.2) ↔ i = (c.1 + d.1, c.2 + d.2) := by
  simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, by omega⟩

/-- The span shifts are even sites. -/
theorem span_even (a I J : ℤ) (s : Site) (hs : s = (I * (a + 1) - 2 * J, I * (a - 1) + 2 * a * J)) :
    EvenSite s := by
  unfold EvenSite
  rw [hs]
  show ((I * (a + 1) - 2 * J) + (I * (a - 1) + 2 * a * J)) % 2 = 0
  have e : (I * (a + 1) - 2 * J) + (I * (a - 1) + 2 * a * J) = 2 * (a * I + J * (a - 1)) := by ring
  rw [e, Int.mul_emod_right]

/-- **Span equivariance of `TwosSel`**: with `Λ`-invariant Laplacian, `TwosSel (c + s) (i + s) ↔ TwosSel c i`. -/
theorem twosSel_shift (a η I J : ℤ) (F : Field) (s : Site) (hs : s = (I * (a + 1) - 2 * J, I * (a - 1) + 2 * a * J))
    (hL : ∀ c, laplacian F (c + s) = laplacian F c) (c i : Site) :
    TwosSel a η F (c + s) (i + s) ↔ TwosSel a η F c i := by
  have hsE := span_even a I J s hs
  have hA : ∀ u, AliasOf a (c + s) u ↔ AliasOf a c u := fun u => alias_shift a I J s hs c u
  unfold TwosSel
  rw [hL c]
  simp only [FreeClass, hA, shift_eq_iff]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · left
      refine ⟨h1, ?_⟩
      unfold Edge at h2 ⊢
      rw [incomingNeg_add_even hsE, incomingPos_add_even hsE] at h2
      rcases h2 with h2 | h2
      · exact Or.inl (site_add_right_cancel' h2)
      · exact Or.inr (site_add_right_cancel' h2)
    · exact Or.inr ⟨h1, h2⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · left
      refine ⟨h1, ?_⟩
      unfold Edge at h2 ⊢
      rw [incomingNeg_add_even hsE, incomingPos_add_even hsE]
      rcases h2 with h2 | h2
      · exact Or.inl (by rw [h2])
      · exact Or.inr (by rw [h2])
    · exact Or.inr ⟨h1, h2⟩

end FLatticePaper.TwosEquiv
