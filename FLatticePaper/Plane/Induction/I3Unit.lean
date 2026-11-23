import FLatticePaper.Plane.Induction.SignedPolicy

/-! Task 38, (b): unit increments of the chain potential `Φ = F − H` (the I3 fix, the all-input estimate).

Write `S` for the translate `F(· + η σ)` of the earlier field `F`, with `σ` the (even) short shift. The fix's data are the two
summands `D = F − S` (the raw slip) and `Q = S − H` (the shifted primitive price), each with unit increments on every edge, and
`Q` with no-cross stars. Then `Φ = D + Q = F − H`, the chain potential. The signed policies make `Φ` nonincreasing along the
retained edges of `F` and nondecreasing along those of `H`, and the quotas hold for the Laplacians of `F` and `H`.

The finite case analysis at a centre has increments `dF_k = F k − F c`, `dS_k = S k − S c`, `dH_k = H k − H c` at the two inputs
`k ∈ {n, p}`. Each unit bound and each monotonicity is linear, and each quota becomes a conjunction or a disjunction of linear
facts once the Laplacian value is fixed; `omega` closes the four Laplacian cases. -/

namespace FLatticePaper

theorem edge_incomingNeg (c : Site) : Edge (incomingNeg c) c := Or.inl rfl

theorem edge_incomingPos (c : Site) : Edge (incomingPos c) c := Or.inr rfl

/-- The local case analysis at a centre with inputs `n`, `p`, in the increments of `F`, `S`, `H` at `c`. -/
theorem star_unit_summands {dFn dFp dSn dSp dHn dHp : ℤ} {RFn RFp RHn RHp : Prop}
    (hDn : -1 ≤ dFn - dSn ∧ dFn - dSn ≤ 1) (hDp : -1 ≤ dFp - dSp ∧ dFp - dSp ≤ 1)
    (hQn : -1 ≤ dSn - dHn ∧ dSn - dHn ≤ 1) (hQp : -1 ≤ dSp - dHp ∧ dSp - dHp ≤ 1)
    (hnc : ¬((0 < dSn - dHn ∧ dSp - dHp < 0) ∨ (dSn - dHn < 0 ∧ 0 < dSp - dHp)))
    (hlapF : dFn + dFp = -1 ∨ dFn + dFp = 0) (hlapH : dHn + dHp = -1 ∨ dHn + dHp = 0)
    (qF1 : dFn + dFp = -1 → RFn ∧ RFp) (qF2 : dFn + dFp = 0 → RFn ∨ RFp)
    (qH1 : dHn + dHp = -1 → RHn ∧ RHp) (qH2 : dHn + dHp = 0 → RHn ∨ RHp)
    (mFn : RFn → dFn - dHn ≤ 0) (mFp : RFp → dFp - dHp ≤ 0)
    (mHn : RHn → 0 ≤ dFn - dHn) (mHp : RHp → 0 ≤ dFp - dHp) :
    -1 ≤ dFn - dHn ∧ dFn - dHn ≤ 1 := by
  have aF : dFn + dFp = -1 → dFn - dHn ≤ 0 ∧ dFp - dHp ≤ 0 := fun h =>
    ⟨mFn (qF1 h).1, mFp (qF1 h).2⟩
  have bF : dFn + dFp = 0 → dFn - dHn ≤ 0 ∨ dFp - dHp ≤ 0 := fun h =>
    (qF2 h).elim (fun a => Or.inl (mFn a)) (fun b => Or.inr (mFp b))
  have aH : dHn + dHp = -1 → 0 ≤ dFn - dHn ∧ 0 ≤ dFp - dHp := fun h =>
    ⟨mHn (qH1 h).1, mHp (qH1 h).2⟩
  have bH : dHn + dHp = 0 → 0 ≤ dFn - dHn ∨ 0 ≤ dFp - dHp := fun h =>
    (qH2 h).elim (fun a => Or.inl (mHn a)) (fun b => Or.inr (mHp b))
  obtain ⟨hDn1, hDn2⟩ := hDn
  obtain ⟨hDp1, hDp2⟩ := hDp
  obtain ⟨hQn1, hQn2⟩ := hQn
  obtain ⟨hQp1, hQp2⟩ := hQp
  rcases hlapF with h1 | h1 <;> rcases hlapH with h2 | h2
  · obtain ⟨a1, a2⟩ := aF h1
    obtain ⟨b1, b2⟩ := aH h2
    exact ⟨by omega, by omega⟩
  · obtain ⟨a1, a2⟩ := aF h1
    rcases bH h2 with g | g <;> exact ⟨by omega, by omega⟩
  · obtain ⟨b1, b2⟩ := aH h2
    rcases bF h1 with g | g <;> exact ⟨by omega, by omega⟩
  · rcases bF h1 with g | g <;> rcases bH h2 with k | k <;> exact ⟨by omega, by omega⟩

/-- **Unit increments of the chain potential.** For the earlier field `F`, its translate `S`, and the chain mate `H`, with the
summands `F − S` and `S − H` of unit increments, no-cross stars for `S − H`, binary Laplacians, the quotas of two signed
policies, and monotonicity of `Φ = F − H` along them, the potential `Φ` has unit increments along every edge. -/
theorem unit_increments_of_summands {F S H : Site → ℤ}
    (hD : ∀ c i, Edge i c → -1 ≤ (F i - S i) - (F c - S c) ∧ (F i - S i) - (F c - S c) ≤ 1)
    (hQ : ∀ c i, Edge i c → -1 ≤ (S i - H i) - (S c - H c) ∧ (S i - H i) - (S c - H c) ≤ 1)
    (hQno : NoCrossStars (fun z => S z - H z))
    (hFb : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0)
    (hHb : ∀ c, laplacian H c = -1 ∨ laplacian H c = 0)
    {relF relH : Site → Site → Prop}
    (hqF : RetainQuota F relF) (hqH : RetainQuota H relH)
    (hmF : NonincreasingAlong (fun z => F z - H z) relF)
    (hmH : NondecreasingAlong (fun z => F z - H z) relH) :
    ∀ c i, Edge i c → -1 ≤ (F i - H i) - (F c - H c) ∧ (F i - H i) - (F c - H c) ≤ 1 := by
  intro c i hi
  have hFl : (F (incomingNeg c) - F c) + (F (incomingPos c) - F c) = -1 ∨
      (F (incomingNeg c) - F c) + (F (incomingPos c) - F c) = 0 := hFb c
  have hHl : (H (incomingNeg c) - H c) + (H (incomingPos c) - H c) = -1 ∨
      (H (incomingNeg c) - H c) + (H (incomingPos c) - H c) = 0 := hHb c
  have hncS : ¬((0 < (S (incomingNeg c) - S c) - (H (incomingNeg c) - H c) ∧
      (S (incomingPos c) - S c) - (H (incomingPos c) - H c) < 0) ∨
      ((S (incomingNeg c) - S c) - (H (incomingNeg c) - H c) < 0 ∧
      0 < (S (incomingPos c) - S c) - (H (incomingPos c) - H c))) := by
    intro h
    have hq := hQno c
    dsimp only at hq
    apply hq
    rcases h with ⟨a, b⟩ | ⟨a, b⟩
    · exact Or.inl ⟨by linarith, by linarith⟩
    · exact Or.inr ⟨by linarith, by linarith⟩
  have hncP : ¬((0 < (S (incomingPos c) - S c) - (H (incomingPos c) - H c) ∧
      (S (incomingNeg c) - S c) - (H (incomingNeg c) - H c) < 0) ∨
      ((S (incomingPos c) - S c) - (H (incomingPos c) - H c) < 0 ∧
      0 < (S (incomingNeg c) - S c) - (H (incomingNeg c) - H c))) := by
    intro h
    have hq := hQno c
    dsimp only at hq
    apply hq
    rcases h with ⟨a, b⟩ | ⟨a, b⟩
    · exact Or.inr ⟨by linarith, by linarith⟩
    · exact Or.inl ⟨by linarith, by linarith⟩
  have starNeg := star_unit_summands
    (dFn := F (incomingNeg c) - F c) (dFp := F (incomingPos c) - F c)
    (dSn := S (incomingNeg c) - S c) (dSp := S (incomingPos c) - S c)
    (dHn := H (incomingNeg c) - H c) (dHp := H (incomingPos c) - H c)
    (RFn := relF c (incomingNeg c)) (RFp := relF c (incomingPos c))
    (RHn := relH c (incomingNeg c)) (RHp := relH c (incomingPos c))
    (hDn := by obtain ⟨p1, p2⟩ := hD c _ (edge_incomingNeg c); constructor <;> linarith)
    (hDp := by obtain ⟨p1, p2⟩ := hD c _ (edge_incomingPos c); constructor <;> linarith)
    (hQn := by obtain ⟨p1, p2⟩ := hQ c _ (edge_incomingNeg c); constructor <;> linarith)
    (hQp := by obtain ⟨p1, p2⟩ := hQ c _ (edge_incomingPos c); constructor <;> linarith)
    (hnc := hncS) (hlapF := hFl) (hlapH := hHl)
    (qF1 := fun h => hqF.1 c (by unfold laplacian; linarith))
    (qF2 := fun h => hqF.2 c (by unfold laplacian; linarith))
    (qH1 := fun h => hqH.1 c (by unfold laplacian; linarith))
    (qH2 := fun h => hqH.2 c (by unfold laplacian; linarith))
    (mFn := fun h => by
      have h' : F (incomingNeg c) - H (incomingNeg c) ≤ F c - H c := hmF c _ h
      linarith)
    (mFp := fun h => by
      have h' : F (incomingPos c) - H (incomingPos c) ≤ F c - H c := hmF c _ h
      linarith)
    (mHn := fun h => by
      have h' : F c - H c ≤ F (incomingNeg c) - H (incomingNeg c) := hmH c _ h
      linarith)
    (mHp := fun h => by
      have h' : F c - H c ≤ F (incomingPos c) - H (incomingPos c) := hmH c _ h
      linarith)
  have starPos := star_unit_summands
    (dFn := F (incomingPos c) - F c) (dFp := F (incomingNeg c) - F c)
    (dSn := S (incomingPos c) - S c) (dSp := S (incomingNeg c) - S c)
    (dHn := H (incomingPos c) - H c) (dHp := H (incomingNeg c) - H c)
    (RFn := relF c (incomingPos c)) (RFp := relF c (incomingNeg c))
    (RHn := relH c (incomingPos c)) (RHp := relH c (incomingNeg c))
    (hDn := by obtain ⟨p1, p2⟩ := hD c _ (edge_incomingPos c); constructor <;> linarith)
    (hDp := by obtain ⟨p1, p2⟩ := hD c _ (edge_incomingNeg c); constructor <;> linarith)
    (hQn := by obtain ⟨p1, p2⟩ := hQ c _ (edge_incomingPos c); constructor <;> linarith)
    (hQp := by obtain ⟨p1, p2⟩ := hQ c _ (edge_incomingNeg c); constructor <;> linarith)
    (hnc := hncP)
    (hlapF := hFl.imp (fun h => by linarith) (fun h => by linarith))
    (hlapH := hHl.imp (fun h => by linarith) (fun h => by linarith))
    (qF1 := fun h => (hqF.1 c (by unfold laplacian; linarith)).symm)
    (qF2 := fun h => (hqF.2 c (by unfold laplacian; linarith)).symm)
    (qH1 := fun h => (hqH.1 c (by unfold laplacian; linarith)).symm)
    (qH2 := fun h => (hqH.2 c (by unfold laplacian; linarith)).symm)
    (mFn := fun h => by
      have h' : F (incomingPos c) - H (incomingPos c) ≤ F c - H c := hmF c _ h
      linarith)
    (mFp := fun h => by
      have h' : F (incomingNeg c) - H (incomingNeg c) ≤ F c - H c := hmF c _ h
      linarith)
    (mHn := fun h => by
      have h' : F c - H c ≤ F (incomingPos c) - H (incomingPos c) := hmH c _ h
      linarith)
    (mHp := fun h => by
      have h' : F c - H c ≤ F (incomingNeg c) - H (incomingNeg c) := hmH c _ h
      linarith)
  rcases hi with rfl | rfl
  · obtain ⟨s1, s2⟩ := starNeg
    constructor <;> linarith
  · obtain ⟨s1, s2⟩ := starPos
    constructor <;> linarith

end FLatticePaper
