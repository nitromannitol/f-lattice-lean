import FLatticePaper.Plane.Induction.WestBridge
import FLatticePaper.Plane.Induction.CapRay
import FLatticePaper.Plane.Induction.SheetMonoChild
import FLatticePaper.Plane.Induction.Q3Field
import FLatticePaper.Plane.Induction.StrongEstimates
import FLatticePaper.Plane.Induction.W1Strips
import FLatticePaper.CanonicalHeadline
import FLatticePaper.Construction.OddShear

/-! # Wiring the covered H-root bridge to the strong estimates (Q32 (iv), named inputs)

The named inputs of `WestBridge.parentSquareOut_covered_H` are discharged from the StrongEstimates fields of the conjugate word:
`hP` (packet), `hslip` (short-slip range), `hsig` (`SheetMonoChild.hsig_of_slip`), `hsym` (the reflection `I − z` and the kernel period
`(d,n)` of the zero kernel constant `Q3Field.coherentConstantU_eq_zero`), `hIsym` (`W1Strips.standardField_iRefl`), and the cap ray
`hAS` (`CapRay.ray_start` and `CapRay.ray_cap`, for `n ≥ 3` and `d − n ≥ 4`).

Genuine inputs that survive: the conjugate `W1Forced` (the induction hypothesis), the even seed `hseed`, the proper-frame condition
`hproper` (`n = 1` or `3 ≤ n`, `4 ≤ d − n`), the base cap `hcapBase` at `n = 1`, and the canonical witness `C`, `W`, `hW`. -/

namespace FLatticePaper.WiredCovered

open FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.W1 FLatticePaper.WestBridge
  FLatticePaper.W1NonfreeOut FLatticePaper.ReflectedFan


/-- Integer division bounds: `m J ≤ X < m (J+1)` for some natural `J`, when `0 < m` and `0 ≤ X`. -/
theorem floor_bounds (X m : ℤ) (hm : 0 < m) (hX : 0 ≤ X) : ∃ J : ℕ, m * (J : ℤ) ≤ X ∧ X < m * ((J : ℤ) + 1) := by
  have hmod := Int.emod_def X m
  have hmnn := Int.emod_nonneg X (ne_of_gt hm)
  have hmlt := Int.emod_lt_of_pos X hm
  obtain ⟨J0, hJ0⟩ : ∃ J0 : ℤ, J0 = X / m := ⟨_, rfl⟩
  have hJ0nn : 0 ≤ J0 := by
    rw [hJ0]
    exact Int.ediv_nonneg hX (le_of_lt hm)
  rw [← hJ0] at hmod
  have hcast : ((J0.toNat : ℕ) : ℤ) = J0 := Int.toNat_of_nonneg hJ0nn
  refine ⟨J0.toNat, ?_, ?_⟩
  · rw [hcast]
    linarith
  · rw [hcast]
    linarith

/-- **The cap ray for a proper frame** (`n ≥ 3`, `d − n ≥ 4`): `CapRay.ray_start` with `CapRay.ray_cap`, the depth `K` with
`2nK ≤ 3d + 3n − 1`. -/
theorem hAS_of_proper {frame : FLatticePaper.Induction.ChildFrame} {G : Field} (hP : frame.Packet G)
    (hsig : ∀ w ∈ frame.closedPolygon, G w - G (w - frame.shortShift) ≤ 0)
    (hN3 : 3 ≤ frame.child.num) (hND : 4 ≤ frame.child.den - frame.child.num) (K : ℕ)
    (hKr : 2 * frame.child.num * (K : ℤ) ≤ 3 * frame.child.den + 3 * frame.child.num - 1) :
    ∃ p q : ℤ, frame.child.num * p - frame.child.den * q = 2 - frame.child.num ∧
      ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ G (p + (k : ℤ), q + (k : ℤ)) := by
  obtain ⟨p, q, hs⟩ := FLatticePaper.CapRay.ray_start frame
  have hX : 0 ≤ frame.child.num + frame.child.den - 2 := by omega
  obtain ⟨J, hJ1, hJ2⟩ := floor_bounds (frame.child.num + frame.child.den - 2) (2 * frame.child.num) (by omega) hX
  exact ⟨p, q, hs, FLatticePaper.CapRay.ray_cap frame hP hsig hN3 hND hs J K hJ1 hJ2 hKr⟩

/-- **The covered H-root bridge from the StrongEstimates fields.** The named inputs are reduced to the genuine ones listed in the
module header. -/
theorem covered_H_wired {frame : FLatticePaper.Induction.ChildFrame} {G : Field} {seed : Site → Site → Prop} {η : ℤ}
    (hP : frame.Packet G)
    (hslipR : ∀ z ∈ frame.closedPolygon, 0 ≤ frame.slip G 1 z ∧ frame.slip G 1 z ≤ 2)
    (hrefl : ∀ z : Site, G (reflectionI - z) = G z)
    (hIs : ∀ z : Site, G (FLatticePaper.W1Strips.iRefl z) = G z)
    (hk : frame.child.modifiedDeck.kernel = (frame.child.den, frame.child.num))
    (hproper : (3 ≤ frame.child.num ∧ 4 ≤ frame.child.den - frame.child.num) ∨ frame.child.num = 1)
    (hcapBase : frame.child.num = 1 → ∀ K : ℕ, 2 ≤ K → frame.child.den + 2 * frame.child.num - 1 ≤ frame.child.num * (K : ℤ) →
      2 * frame.child.num * (K : ℤ) ≤ 3 * frame.child.den + 3 * frame.child.num - 1 →
      ∃ p q : ℤ, frame.child.num * p - frame.child.den * q = 2 - frame.child.num ∧
        ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ G (p + (k : ℤ), q + (k : ℤ)))
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (hseed : ∀ z : Site, EvenSite z → frame.tGrade z = 2 - (frame.child.den + frame.child.num) → G z = 0)
    (C : CanonicalSignedPolicy frame G η)
    (W : FLatticePaper.W1Witness.OldPolicyWitness frame G seed η) (hW : W.retained = C.policy)
    (hs : ∀ y i, ¬ seed y i)
    {z : Site} (hz : z ∈ frame.freeH) (hodd : ¬ EvenSite z) (hne : z ≠ frame.hLast)
    (hbt : frame.child.num + 2 ≤ frame.tGrade z) (hzw : laplacian G z = 0)
    (hzS : laplacian G (z.1, z.2 - 1) = 0) :
    ParentSquareOut G W.retained z := by
  have hslip : ∀ z ∈ frame.closedPolygon, 0 ≤ frame.slip G 1 z := fun z hz' => (hslipR z hz').1
  have hsig2 : ∀ w ∈ frame.closedPolygon, 0 ≤ G w - G (w + frame.shortShift) ∧
      G w - G (w + frame.shortShift) ≤ 2 := by
    intro w hw
    have h := hslipR w hw
    unfold ChildFrame.slip at h
    simp only [one_smul] at h
    exact h
  have hsig := FLatticePaper.SheetMonoChild.hsig_of_slip frame hP hsig2
  have hper : HasGeneratorPeriods frame.child G 0 frame.coherentConstantV := by
    have h := hP.periods
    rw [FLatticePaper.Induction.coherentConstantU_eq_zero frame] at h
    exact h
  have hsym : ∀ y, G (reflH frame y) = G y := by
    intro y
    have e : reflH frame y = (reflectionI - y) + frame.child.modifiedDeck.kernel := by
      rw [hk]
      unfold reflH reflectionI
      refine Prod.ext ?_ ?_
      all_goals simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
      all_goals omega
    have hpd := ChildFrame.periodic_kernel frame hper (reflectionI - y) 1
    rw [one_smul] at hpd
    rw [e, hpd, hrefl]
  have hAS : ∀ K : ℕ, 2 ≤ K → frame.child.den + 2 * frame.child.num - 1 ≤ frame.child.num * (K : ℤ) →
      2 * frame.child.num * (K : ℤ) ≤ 3 * frame.child.den + 3 * frame.child.num - 1 →
      ∃ p q : ℤ, frame.child.num * p - frame.child.den * q = 2 - frame.child.num ∧
        ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ G (p + (k : ℤ), q + (k : ℤ)) := by
    intro K hK2 hKs hKr
    rcases hproper with hp | h1
    · exact hAS_of_proper hP hsig hp.1 hp.2 K hKr
    · exact hcapBase h1 K hK2 hKs hKr
  exact parentSquareOut_covered_H hP hsig hAS hsym hW1 hper hslip hseed hIs C W hW hs hz hodd hne hbt hzw hzS

/-- **The covered H-root bridge for a word, from its strong estimates.** Only the genuine inputs remain: the proper-frame condition,
the base cap at `n = 1`, the conjugate `W1Forced`, the even seed, and the canonical witness. -/
theorem covered_H_of_strong (word : FLatticePaper.Farey.Word) (hS : Induction.StrongEstimates (conjWord word))
    {seed : Site → Site → Prop} {η : ℤ}
    (hproper : (3 ≤ (frameAt (conjWord word)).child.num ∧ 4 ≤ (frameAt (conjWord word)).child.den -
        (frameAt (conjWord word)).child.num) ∨ (frameAt (conjWord word)).child.num = 1)
    (hcapBase : (frameAt (conjWord word)).child.num = 1 → ∀ K : ℕ, 2 ≤ K →
      (frameAt (conjWord word)).child.den + 2 * (frameAt (conjWord word)).child.num - 1 ≤
        (frameAt (conjWord word)).child.num * (K : ℤ) →
      2 * (frameAt (conjWord word)).child.num * (K : ℤ) ≤
        3 * (frameAt (conjWord word)).child.den + 3 * (frameAt (conjWord word)).child.num - 1 →
      ∃ p q : ℤ, (frameAt (conjWord word)).child.num * p - (frameAt (conjWord word)).child.den * q =
          2 - (frameAt (conjWord word)).child.num ∧
        ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤
          standardField (conjWord word) (p + (k : ℤ), q + (k : ℤ)))
    (hW1 : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
      (standardField (conjWord word)))
    (hseed : ∀ z : Site, EvenSite z → (frameAt (conjWord word)).tGrade z =
      2 - ((frameAt (conjWord word)).child.den + (frameAt (conjWord word)).child.num) →
        standardField (conjWord word) z = 0)
    (C : CanonicalSignedPolicy (frameAt (conjWord word)) (standardField (conjWord word)) η)
    (W : FLatticePaper.W1Witness.OldPolicyWitness (frameAt (conjWord word)) (standardField (conjWord word)) seed η)
    (hW : W.retained = C.policy) (hs : ∀ y i, ¬ seed y i)
    {z : Site} (hz : z ∈ (frameAt (conjWord word)).freeH) (hodd : ¬ EvenSite z)
    (hne : z ≠ (frameAt (conjWord word)).hLast)
    (hbt : (frameAt (conjWord word)).child.num + 2 ≤ (frameAt (conjWord word)).tGrade z)
    (hzw : laplacian (standardField (conjWord word)) z = 0)
    (hzS : laplacian (standardField (conjWord word)) (z.1, z.2 - 1) = 0) :
    ParentSquareOut (standardField (conjWord word)) W.retained z :=
  covered_H_wired hS.packet (fun z hz' => hS.slipRange z hz')
    (fun z => FLatticePaper.standardField_reflectI_conj word hS z)
    (fun z => FLatticePaper.W1Strips.standardField_iRefl hS z)
    (FLatticePaper.Construction.child_modifiedDeck_kernel_eq (conjWord word)) hproper hcapBase hW1 hseed C W hW hs
    hz hodd hne hbt hzw hzS

end FLatticePaper.WiredCovered
