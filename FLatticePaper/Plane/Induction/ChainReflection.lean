import FLatticePaper.Plane.Induction.StrongEstimates

/-! # The chain data is the reflection of the signed policy (task 49)

For the standard field `F` of an earlier word and a phase `η = ±1`, the chain mate's graph is the reflection of the policy
graph under `ξ ↦ K − ξ`, with `K = centre − (η σ − v)` (this is `ReflectedPolicy centre (η σ − v)`). The packet reflection
`F(centre − z) = F z − t z + κ` then gives, with no further input:

* `chainSheet η (K − z) = F z + A(z)` with `A` affine, so the Laplacian of `chainSheet η` at `K − z` is that of `F` at `z`;
* `Φ_η(K − z) + Φ_η(z)` is a constant, so `Φ_η` is nondecreasing along the reflected policy when it is nonincreasing along
  the policy;
* the reflected policy has the quota for `chainSheet η` when the policy has the quota for `F`;
* ranks with increments `(p, q)` on the generators become ranks with increments `(−p, −q)` under `z ↦ K − z`.

Hence the chain fields follow from the F2–F3 field, and `StrongEstimates.chain_data` gives them without a carried field. -/

namespace FLatticePaper.Induction
open Farey FLatticePaper

namespace ChainReflection

/-- The reflection centre `K = centre − (η σ − v)` of the chain mate: its reflection is `ξ ↦ K − ξ`. -/
def reflCentre (frame : ChildFrame) (η : ℤ) : Site :=
  frame.centre - (η • frame.shortShift - frame.parentShift)

theorem evenSite_of_sum (x : Site) (k : ℤ) (h : x.1 + x.2 = 2 * k) : EvenSite x := by
  unfold EvenSite
  rw [h]
  omega

theorem evenSite_shift (frame : ChildFrame) (η : ℤ) :
    EvenSite (η • frame.shortShift - frame.parentShift) := by
  refine evenSite_of_sum _ (η * frame.eps * (frame.parents.odd.den + frame.parents.odd.num) -
    frame.eps * frame.parents.odd.num) ?_
  unfold ChildFrame.shortShift ChildFrame.parentShift
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem evenSite_reflCentre (frame : ChildFrame) (η : ℤ) : EvenSite (reflCentre frame η) :=
  (frame.evenSite_centre_sub _).mpr (evenSite_shift frame η)

/-- Reflection in an even point `K` exchanges the two incoming edges of every site. -/
theorem incomingNeg_reflect_pair {K : Site} (hK : EvenSite K) (z : Site) :
    incomingNeg (K - z) = K - incomingPos z ∧ incomingPos (K - z) = K - incomingNeg z := by
  by_cases hz : EvenSite z
  · have h1 : EvenSite (K - z) := by
      unfold EvenSite at hK hz ⊢
      simp only [Prod.fst_sub, Prod.snd_sub]
      omega
    simp only [incomingNeg, incomingPos, h1, hz, ↓reduceIte]
    constructor <;> ext <;> simp <;> ring
  · have h1 : ¬EvenSite (K - z) := by
      unfold EvenSite at hK hz ⊢
      simp only [Prod.fst_sub, Prod.snd_sub]
      omega
    simp only [incomingNeg, incomingPos, h1, hz, ↓reduceIte]
    constructor <;> ext <;> simp <;> ring

theorem chainPotential_eq_sub (frame : ChildFrame) (F : Field) (η : ℤ) (z : Site) :
    frame.chainPotential F η z = F z - frame.chainSheet F η z := by
  unfold ChildFrame.chainPotential ChildFrame.slip ChildFrame.price ChildFrame.chainSheet
  ring

theorem chainSheet_reflect (frame : ChildFrame) (F : Field) (η : ℤ) (z : Site) :
    frame.chainSheet F η (reflCentre frame η - z) =
      F (frame.centre - z) + frame.eps * frame.parentSlope (frame.centre + frame.parentShift - z) := by
  unfold ChildFrame.chainSheet reflCentre
  have e1 : frame.centre - (η • frame.shortShift - frame.parentShift) - z + η • frame.shortShift -
      frame.parentShift = frame.centre - z := by
    ext <;> simp only [Prod.fst_add, Prod.fst_sub, Prod.snd_add, Prod.snd_sub, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul] <;> ring
  have e2 : frame.centre - (η • frame.shortShift - frame.parentShift) - z + η • frame.shortShift =
      frame.centre + frame.parentShift - z := by
    ext <;> simp only [Prod.fst_add, Prod.fst_sub, Prod.snd_add, Prod.snd_sub, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul] <;> ring
  rw [e1, e2]

/-- The potential is reflected: `Φ_η(K − z) + Φ_η(z)` is independent of `z`. -/
theorem chainPotential_reflect (frame : ChildFrame) (F : Field)
    (hR : ∀ z, F (frame.centre - z) = F z - frame.tGrade z + frame.symmetryConstant) (η : ℤ) (z : Site) :
    frame.chainPotential F η (reflCentre frame η - z) + frame.chainPotential F η z =
      -(frame.eps * frame.parentSlope (frame.centre + frame.parentShift + η • frame.shortShift)) -
        frame.tGrade (η • frame.shortShift - frame.parentShift) := by
  rw [chainPotential_eq_sub, chainPotential_eq_sub, chainSheet_reflect]
  have hK : reflCentre frame η - z = frame.centre - ((η • frame.shortShift - frame.parentShift) + z) := by
    unfold reflCentre
    ext <;> simp only [Prod.fst_add, Prod.fst_sub, Prod.snd_add, Prod.snd_sub] <;> ring
  have hs : F ((η • frame.shortShift - frame.parentShift) + z) =
      frame.chainSheet F η z - frame.eps * frame.parentSlope (z + η • frame.shortShift) := by
    unfold ChildFrame.chainSheet
    rw [show (η • frame.shortShift - frame.parentShift) + z = z + η • frame.shortShift - frame.parentShift from by
      abel]
    ring
  rw [hK, hR, hs, hR z]
  unfold ChildFrame.parentSlope ChildFrame.tGrade
  simp only [Prod.fst_add, Prod.fst_sub, Prod.snd_add, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem chainSheet_reflect_eq (frame : ChildFrame) (F : Field) (η : ℤ)
    (hR : ∀ z, F (frame.centre - z) = F z - frame.tGrade z + frame.symmetryConstant) (w : Site) :
    frame.chainSheet F η (reflCentre frame η - w) =
      F w - frame.tGrade w + frame.symmetryConstant +
        frame.eps * frame.parentSlope (frame.centre + frame.parentShift - w) := by
  rw [chainSheet_reflect, hR w]

/-- The Laplacian of the chain sheet at the reflected point is the Laplacian of `F` (the affine part has zero Laplacian). -/
theorem laplacian_chainSheet_reflect (frame : ChildFrame) (F : Field) (η : ℤ)
    (hR : ∀ z, F (frame.centre - z) = F z - frame.tGrade z + frame.symmetryConstant) (z : Site) :
    laplacian (fun w => frame.chainSheet F η w) (reflCentre frame η - z) = laplacian F z := by
  obtain ⟨h1, h2⟩ := incomingNeg_reflect_pair (evenSite_reflCentre frame η) z
  simp only [laplacian]
  rw [h1, h2]
  simp only [chainSheet_reflect_eq frame F η hR]
  by_cases hz : EvenSite z
  · simp only [incomingNeg, incomingPos, hz, ↓reduceIte, ChildFrame.tGrade, ChildFrame.parentSlope,
      ChildFrame.parentShift, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
    ring
  · simp only [incomingNeg, incomingPos, hz, ↓reduceIte, ChildFrame.tGrade, ChildFrame.parentSlope,
      ChildFrame.parentShift, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
    ring

/-- The quota of the chain sheet along the reflected policy, from the quota of `F` along the policy. -/
theorem retainQuota_chainSheet_reflect (frame : ChildFrame) (F : Field) (η : ℤ)
    (hR : ∀ z, F (frame.centre - z) = F z - frame.tGrade z + frame.symmetryConstant)
    (policy : Site → Site → Prop) (hq : RetainQuota F policy) :
    RetainQuota (fun w => frame.chainSheet F η w)
      (ReflectedPolicy frame.centre (η • frame.shortShift - frame.parentShift) policy) := by
  unfold RetainQuota at hq ⊢
  have hlap : ∀ c, laplacian F (reflCentre frame η - c) =
      laplacian (fun w => frame.chainSheet F η w) c := by
    intro c
    have h := laplacian_chainSheet_reflect frame F η hR (reflCentre frame η - c)
    rw [sub_sub_cancel] at h
    exact h.symm
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · have hz : laplacian F (reflCentre frame η - c) = -1 := by
      rw [hlap c]
      exact hc
    obtain ⟨n1, p1⟩ := incomingNeg_reflect_pair (evenSite_reflCentre frame η) c
    obtain ⟨a, b⟩ := hq.1 _ hz
    constructor
    · show policy (reflCentre frame η - c) (reflCentre frame η - incomingNeg c)
      rw [← p1]
      exact b
    · show policy (reflCentre frame η - c) (reflCentre frame η - incomingPos c)
      rw [← n1]
      exact a
  · have hz : laplacian F (reflCentre frame η - c) = 0 := by
      rw [hlap c]
      exact hc
    obtain ⟨n1, p1⟩ := incomingNeg_reflect_pair (evenSite_reflCentre frame η) c
    rcases hq.2 _ hz with a | b
    · right
      show policy (reflCentre frame η - c) (reflCentre frame η - incomingPos c)
      rw [← n1]
      exact a
    · left
      show policy (reflCentre frame η - c) (reflCentre frame η - incomingNeg c)
      rw [← p1]
      exact b

/-- `Φ_η` is nondecreasing along the reflected policy, from its nonincrease along the policy. -/
theorem nondecreasing_chainPotential_reflect (frame : ChildFrame) (F : Field) (η : ℤ)
    (hR : ∀ z, F (frame.centre - z) = F z - frame.tGrade z + frame.symmetryConstant)
    (policy : Site → Site → Prop) (hmono : NonincreasingAlong (frame.chainPotential F η) policy) :
    NondecreasingAlong (frame.chainPotential F η)
      (ReflectedPolicy frame.centre (η • frame.shortShift - frame.parentShift) policy) := by
  unfold NonincreasingAlong at hmono
  unfold NondecreasingAlong
  intro c i hci
  have hc := chainPotential_reflect frame F hR η c
  have hi := chainPotential_reflect frame F hR η i
  have hm : frame.chainPotential F η (reflCentre frame η - i) ≤
      frame.chainPotential F η (reflCentre frame η - c) := hmono _ _ hci
  show frame.chainPotential F η c ≤ frame.chainPotential F η i
  linarith

/-- Composing with `z ↦ K − z` turns increments `(p, q)` into `(−p, −q)`, with the same `λ` and the reversed order. -/
theorem rankWithIncrements_reflect (K : Site) (policy : Site → Site → Prop) (U V : Site) (p q : ℤ)
    (h : RankWithIncrements policy U V p q) :
    RankWithIncrements (fun c i => policy (K - c) (K - i)) U V (-p) (-q) := by
  obtain ⟨rank, lam, hlam, hret, hU, hV⟩ := h
  refine ⟨fun z => rank (K - z), lam, hlam, ?_, ?_, ?_⟩
  · intro x i hxi
    exact hret _ _ hxi
  · intro z
    have e : K - (z + U) = K - z - U := by abel
    have h1 := hU (K - z - U)
    rw [sub_add_cancel] at h1
    show rank (K - (z + U)) - rank (K - z) = -p * lam
    rw [e]
    linarith
  · intro z
    have e : K - (z + V) = K - z - V := by abel
    have h1 := hV (K - z - V)
    rw [sub_add_cancel] at h1
    show rank (K - (z + V)) - rank (K - z) = -q * lam
    rw [e]
    linarith

/-- The chain fields of a policy for `F` with the quota, nonincreasing `Φ_η`, and the rank increments, reflected. -/
theorem chainData_of_policy (frame : ChildFrame) (F : Field) (η : ℤ)
    (hR : ∀ z, F (frame.centre - z) = F z - frame.tGrade z + frame.symmetryConstant)
    (policy : Site → Site → Prop) (hq : RetainQuota F policy)
    (hmono : NonincreasingAlong (frame.chainPotential F η) policy)
    (hrank : ∀ a c : ℤ, 0 < a → 0 < c →
      RankWithIncrements policy frame.child.modifiedDeck.kernel frame.child.modifiedDeck.transverse (-a) (c * η)) :
    NondecreasingAlong (frame.chainPotential F η)
        (ReflectedPolicy frame.centre (η • frame.shortShift - frame.parentShift) policy) ∧
      RetainQuota (fun z => frame.chainSheet F η z)
        (ReflectedPolicy frame.centre (η • frame.shortShift - frame.parentShift) policy) ∧
      ∀ a c : ℤ, 0 < a → 0 < c →
        RankWithIncrements (ReflectedPolicy frame.centre (η • frame.shortShift - frame.parentShift) policy)
          frame.child.modifiedDeck.kernel frame.child.modifiedDeck.transverse a (-(c * η)) := by
  refine ⟨nondecreasing_chainPotential_reflect frame F η hR policy hmono,
    retainQuota_chainSheet_reflect frame F η hR policy hq, fun a c ha hc => ?_⟩
  have h := rankWithIncrements_reflect (reflCentre frame η) policy _ _ _ _ (hrank a c ha hc)
  rw [neg_neg] at h
  exact h

end ChainReflection

/-- F2 and F4 of `StrongEstimates` for the chain mate, from its F2–F3 field and the packet reflection: no carried chain field. -/
theorem StrongEstimates.chain_data {u : Word} (h : StrongEstimates u) (η : ℤ) (hη : η = 1 ∨ η = -1) :
    ∃ policy : Site → Site → Prop,
      NondecreasingAlong ((frameAt u).chainPotential (standardField u) η)
          (ReflectedPolicy (frameAt u).centre (η • (frameAt u).shortShift - (frameAt u).parentShift) policy) ∧
        RetainQuota (fun z => (frameAt u).chainSheet (standardField u) η z)
          (ReflectedPolicy (frameAt u).centre (η • (frameAt u).shortShift - (frameAt u).parentShift) policy) ∧
        ∀ a c : ℤ, 0 < a → 0 < c →
          RankWithIncrements
            (ReflectedPolicy (frameAt u).centre (η • (frameAt u).shortShift - (frameAt u).parentShift) policy)
            (frameAt u).child.modifiedDeck.kernel (frameAt u).child.modifiedDeck.transverse a (-(c * η)) := by
  obtain ⟨policy, hq, hm, hr⟩ := h.F2F3_policy η hη
  exact ⟨policy, ChainReflection.chainData_of_policy (frameAt u) (standardField u) η h.packet.reflection
    policy hq hm hr⟩

end FLatticePaper.Induction
