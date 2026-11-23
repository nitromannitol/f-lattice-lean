import FLatticePaper.Plane.Induction.CanonicalSigned
import FLatticePaper.Plane.Induction.BothFreeGrades

/-! Task 72 / Q20: the two-rank raw-Φ reduction, the local step (`TWO_RANK_RAW_PHI_AUDIT.md`, "Raw rise reduction").

Fields: `F` the standard field, `g = F(· + ησ)`, `D = F − g` (the raw slip `D_η`, `ChildFrame.slip`), `Ps = P(· + ησ)`
(the shifted price). The chain potential is `Φ = D + Ps` (`ChildFrame.chainPotential`).

`P` is the F-policy (`CanonicalSignedPolicy.policy`), `G` the translated opposite g-policy.

The local step: a rise `Φ(z) < Φ(u)` at a retained edge `z → u` of `P` forces `ΔD = 0`, `ΔPs = 1`; the g-policy then rejects `u`, so
`g` is white and retains the other input `v` with `D(v) ≥ D(z)`; `F` cannot be black (else `ΔLaplacian D = −1`); so both are white,
`Lap D = 0`, and both inputs of `z` have `D = D(z)`. -/

namespace FLatticePaper.TwoRank

open FLatticePaper FLatticePaper.Induction

/-- The Laplacian is additive in the field. -/
theorem laplacian_sub_fields (A B : Field) (c : Site) :
    laplacian (fun x => A x - B x) c = laplacian A c - laplacian B c := by
  unfold laplacian
  ring

/-- An even step (`s₁ + s₂` even) preserves the parity of a site. -/
theorem evenSite_add_iff (x s : Site) (hs : (s.1 + s.2) % 2 = 0) :
    EvenSite (x + s) ↔ EvenSite x := by
  unfold EvenSite
  simp only [Prod.fst_add, Prod.snd_add]
  omega

theorem incomingNeg_add (x s : Site) (hs : (s.1 + s.2) % 2 = 0) :
    incomingNeg (x + s) = incomingNeg x + s := by
  unfold incomingNeg
  simp only [evenSite_add_iff x s hs]
  split_ifs <;> ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring

theorem incomingPos_add (x s : Site) (hs : (s.1 + s.2) % 2 = 0) :
    incomingPos (x + s) = incomingPos x + s := by
  unfold incomingPos
  simp only [evenSite_add_iff x s hs]
  split_ifs <;> ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring

/-- An edge is preserved by an even translation. -/
theorem edge_add_of_even {y x : Site} (s : Site) (hs : (s.1 + s.2) % 2 = 0) (h : FLatticePaper.Edge y x) :
    FLatticePaper.Edge (y + s) (x + s) := by
  unfold FLatticePaper.Edge at h ⊢
  rcases h with h | h
  · exact Or.inl (by rw [incomingNeg_add x s hs, h])
  · exact Or.inr (by rw [incomingPos_add x s hs, h])

/-- The Laplacian of a translate by an even step is the Laplacian at the translated site. -/
theorem laplacian_translate (F : Field) (s : Site) (hs : (s.1 + s.2) % 2 = 0) (c : Site) :
    laplacian (fun x => F (x + s)) c = laplacian F (c + s) := by
  unfold laplacian
  rw [incomingNeg_add c s hs, incomingPos_add c s hs]

/-- The local two-rank step at a retained edge `z → u` of the F-policy `P`, with the translated opposite policy `G` of `g`.
The hypotheses are those of the audit: quotas (black keeps both inputs, white keeps one), the monotonicities of `D` and `Ps`, the
unit bound `Ps u ≤ Ps z + 1` on the edge, and `Laplacian ∈ {−1, 0}` for `F` and `g`. -/
theorem local_two_rank (F g D Ps : Site → ℤ) (P G : Site → Site → Prop)
    (hD : ∀ x, D x = F x - g x)
    (hlapF : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0)
    (hlapg : ∀ c, laplacian g c = -1 ∨ laplacian g c = 0)
    (hPblack : ∀ c, laplacian F c = -1 → P c (incomingNeg c) ∧ P c (incomingPos c))
    (hGblack : ∀ c, laplacian g c = -1 → G c (incomingNeg c) ∧ G c (incomingPos c))
    (hGwhite : ∀ c, laplacian g c = 0 → G c (incomingNeg c) ∨ G c (incomingPos c))
    (hDP : NonincreasingAlong D P) (hDG : NondecreasingAlong D G) (hPsG : NonincreasingAlong Ps G)
    {z u : Site} (hu : P z u) (hin : u = incomingNeg z ∨ u = incomingPos z)
    (hunit : Ps u ≤ Ps z + 1) (hrise : D z + Ps z < D u + Ps u) :
    laplacian g z = 0 ∧ laplacian F z = 0 ∧
      D (incomingNeg z) = D z ∧ D (incomingPos z) = D z ∧ Ps u = Ps z + 1 ∧
      ∃ v, (v = incomingNeg z ∨ v = incomingPos z) ∧ v ≠ u ∧ G z v := by
  have hDu : D u ≤ D z := hDP z u hu
  have hPu : Ps u = Ps z + 1 := by omega
  have hDu' : D u = D z := by omega
  have hnotG : ¬ G z u := fun h => by
    have := hPsG z u h
    omega
  have hlapD : laplacian D z = laplacian F z - laplacian g z := by
    rw [show D = fun x => F x - g x from funext hD]
    exact laplacian_sub_fields F g z
  have hLD : laplacian D z = (D (incomingNeg z) - D z) + (D (incomingPos z) - D z) := rfl
  have hgw : laplacian g z = 0 := by
    rcases hlapg z with h | h
    · exfalso
      obtain ⟨ha, hb⟩ := hGblack z h
      rcases hin with rfl | rfl
      · exact hnotG ha
      · exact hnotG hb
    · exact h
  -- both inputs of `z` have `D ≥ D(z)`: `u` by the rise, the other one by the translated opposite policy (white `g`)
  have hlow : D z ≤ D (incomingNeg z) ∧ D z ≤ D (incomingPos z) := by
    rcases hin with h | h
    · have hGb : G z (incomingPos z) := by
        rcases hGwhite z hgw with h' | h'
        · exact absurd (by rw [h]; exact h') hnotG
        · exact h'
      exact ⟨by rw [← h]; omega, hDG z _ hGb⟩
    · have hGa : G z (incomingNeg z) := by
        rcases hGwhite z hgw with h' | h'
        · exact h'
        · exact absurd (by rw [h]; exact h') hnotG
      exact ⟨hDG z _ hGa, by rw [← h]; omega⟩
  -- `F` is white: a black `F` keeps both inputs, so `D` is flat on the star, and `Lap D = −1 − 0 = −1`, contradicting `Lap D = 0`
  have hF0 : laplacian F z = 0 := by
    rcases hlapF z with h | h
    · exfalso
      obtain ⟨hPa, hPb⟩ := hPblack z h
      have hDa : D (incomingNeg z) ≤ D z := hDP z _ hPa
      have hDb : D (incomingPos z) ≤ D z := hDP z _ hPb
      omega
    · exact h
  have hLDz : laplacian D z = 0 := by omega
  have hD1 : D (incomingNeg z) = D z := by omega
  have hD2 : D (incomingPos z) = D z := by omega
  have hother : ∃ v, (v = incomingNeg z ∨ v = incomingPos z) ∧ v ≠ u ∧ G z v := by
    have hne := FLatticePaper.incomingNeg_ne_incomingPos z
    rcases hin with h | h
    · refine ⟨incomingPos z, Or.inr rfl, by rw [h]; exact hne.symm, ?_⟩
      rcases hGwhite z hgw with h' | h'
      · exact absurd (by rw [h]; exact h') hnotG
      · exact h'
    · refine ⟨incomingNeg z, Or.inl rfl, by rw [h]; exact hne, ?_⟩
      rcases hGwhite z hgw with h' | h'
      · exact h'
      · exact absurd (by rw [h]; exact h') hnotG
  exact ⟨hgw, hF0, hD1, hD2, hPu, hother⟩

/-- Shifting by `(η • σ)` and back by `((−η) • σ)` is the identity. -/
theorem add_neg_smul_cancel (frame : ChildFrame) (η : ℤ) (x : Site) :
    x + η • frame.shortShift + (-η) • frame.shortShift = x := by
  refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

/-- **The local two-rank step on the frame.** For the canonical signed policy `C` (`P = C.policy`), a sign `η = ±1`, and the translated
opposite policy `G c i := opp (c + ησ) (i + ησ)`, where `opp` has quota `RetainQuota F` and its raw slip `D_{−η}` does not increase
along it (`oppRawSlip`, the `ChainPairData` input), a rise `Φ_η(z) < Φ_η(u)` along a retained edge `z → u` forces: `F` white at `z` and at
`z + ησ`, both inputs of `z` tied for `D_η`, and `P(u + ησ) = P(z + ησ) + 1`.

Named inputs (the audit's stated monotonicities and unit bound, not derived here): `hoppPrice` (the price does not increase along
the opposite policy) and `hunit` (the shifted price moves by at most one along an F-policy edge). -/
theorem rise_local_frame (frame : ChildFrame) {F : Field} {η : ℤ} (C : CanonicalSignedPolicy frame F η)
    (hη : η = 1 ∨ η = -1) (opp : Site → Site → Prop)
    (hoppRaw : NonincreasingAlong (fun y => F y - F (y + (-η) • frame.shortShift)) opp)
    (hoppQuota : RetainQuota F opp)
    (hoppPrice : ∀ c i, opp c i → frame.price F i ≤ frame.price F c)
    (hlapF : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0)
    (hunit : ∀ z u, C.policy z u → frame.price F (u + η • frame.shortShift) ≤ frame.price F (z + η • frame.shortShift) + 1)
    {z u : Site} (hu : C.policy z u) (hin : u = incomingNeg z ∨ u = incomingPos z)
    (hrise : frame.chainPotential F η z < frame.chainPotential F η u) :
    laplacian F (z + η • frame.shortShift) = 0 ∧ laplacian F z = 0 ∧
      frame.slip F η (incomingNeg z) = frame.slip F η z ∧ frame.slip F η (incomingPos z) = frame.slip F η z ∧
      frame.price F (u + η • frame.shortShift) = frame.price F (z + η • frame.shortShift) + 1 ∧
      ∃ v, (v = incomingNeg z ∨ v = incomingPos z) ∧ v ≠ u ∧ opp (z + η • frame.shortShift) (v + η • frame.shortShift) := by
  have hs : (frame.shortShift.1 + frame.shortShift.2) % 2 = 0 :=
    FLatticePaper.BothFreeGrades.shortShift_even frame
  have hsη : ((η • frame.shortShift).1 + (η • frame.shortShift).2) % 2 = 0 := by
    obtain ⟨k, hk⟩ : (2 : ℤ) ∣ frame.shortShift.1 + frame.shortShift.2 := Int.dvd_of_emod_eq_zero hs
    rcases hη with rfl | rfl <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> omega
  have hlapg : ∀ c, laplacian (fun x => F (x + η • frame.shortShift)) c = -1 ∨
      laplacian (fun x => F (x + η • frame.shortShift)) c = 0 := by
    intro c
    rw [laplacian_translate F _ hsη]
    exact hlapF _
  have hGblack : ∀ c, laplacian (fun x => F (x + η • frame.shortShift)) c = -1 →
      opp (c + η • frame.shortShift) (incomingNeg c + η • frame.shortShift) ∧
        opp (c + η • frame.shortShift) (incomingPos c + η • frame.shortShift) := by
    intro c h
    have h' : laplacian F (c + η • frame.shortShift) = -1 := by
      rw [← laplacian_translate F _ hsη]
      exact h
    obtain ⟨ha, hb⟩ := hoppQuota.1 _ h'
    rw [incomingNeg_add c _ hsη] at ha
    rw [incomingPos_add c _ hsη] at hb
    exact ⟨ha, hb⟩
  have hGwhite : ∀ c, laplacian (fun x => F (x + η • frame.shortShift)) c = 0 →
      opp (c + η • frame.shortShift) (incomingNeg c + η • frame.shortShift) ∨
        opp (c + η • frame.shortShift) (incomingPos c + η • frame.shortShift) := by
    intro c h
    have h' : laplacian F (c + η • frame.shortShift) = 0 := by
      rw [← laplacian_translate F _ hsη]
      exact h
    rcases hoppQuota.2 _ h' with ha | hb
    · rw [incomingNeg_add c _ hsη] at ha
      exact Or.inl ha
    · rw [incomingPos_add c _ hsη] at hb
      exact Or.inr hb
  have hDP : NonincreasingAlong (frame.slip F η) C.policy := rawSlip_of_canonical C
  have hDG : NondecreasingAlong (frame.slip F η)
      (fun c i => opp (c + η • frame.shortShift) (i + η • frame.shortShift)) := by
    intro c i h
    have h1 := hoppRaw _ _ h
    simp only [add_neg_smul_cancel] at h1
    show F c - F (c + η • frame.shortShift) ≤ F i - F (i + η • frame.shortShift)
    omega
  have hPsG : NonincreasingAlong (fun x => frame.price F (x + η • frame.shortShift))
      (fun c i => opp (c + η • frame.shortShift) (i + η • frame.shortShift)) := by
    intro c i h
    exact hoppPrice _ _ h
  have hrise' : frame.slip F η z + frame.price F (z + η • frame.shortShift) <
      frame.slip F η u + frame.price F (u + η • frame.shortShift) := by
    unfold ChildFrame.chainPotential at hrise
    exact hrise
  obtain ⟨hg, hF, hna, hpa, hPs, hv⟩ := local_two_rank F (fun x => F (x + η • frame.shortShift)) (frame.slip F η)
    (fun x => frame.price F (x + η • frame.shortShift)) C.policy
    (fun c i => opp (c + η • frame.shortShift) (i + η • frame.shortShift))
    (fun x => rfl) hlapF hlapg C.quota.1 hGblack hGwhite hDP hDG hPsG hu hin
    (hunit z u hu) hrise'
  refine ⟨?_, hF, hna, hpa, hPs, hv⟩
  rw [laplacian_translate F _ hsη] at hg
  exact hg

end FLatticePaper.TwoRank
