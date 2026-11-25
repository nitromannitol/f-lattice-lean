import FLatticePaper.Construction.EPolicy

/-! Independence of the native representative of the reciprocal policy `ePolicy` (the lemma `ePolicy_indep` cited in
`EPolicy.nativeRep`). Two native points of one deck class differ by one of the five offsets `0, ±U, ±V`
(`native_offset`); the free aliases and the rule of the native centre are invariant under these offsets (`freeAlias_iff`,
`retNat_offset`), and an even native pair with a nonzero offset has a free point (`even_pair_free`). -/

namespace FLatticePaper.EPolicyIndep

open Classical FLatticePaper FLatticePaper.PureRank FLatticePaper.Construction FLatticePaper.Farey FLatticePaper.EPolicy

/-- The box bounds that every native point satisfies (including the two corners). -/
theorem native_bounds {d : ℤ} (hd : 3 ≤ d) {p : Pt} (hp : NativeP d p) :
    2 - d ≤ p.1 ∧ p.1 ≤ d ∧ 0 ≤ p.2 ∧ p.2 ≤ d + 1 := by
  rcases hp with ⟨h1, h2, h3, h4, -, -⟩ | h | h
  · exact ⟨h1, h2, h3, h4⟩
  · subst h; simp; omega
  · subst h; simp; omega

/-- **Lemma A.** Two native points differ by a deck offset `i·U + j·V` with `(i, j)` among the five offsets. -/
theorem native_offset {d : ℤ} (hd : 3 ≤ d) {p q : Pt} {i j : ℤ} (hp : NativeP d p) (hq : NativeP d q)
    (hpq : q = shiftP d p i j) :
    (i = 0 ∧ j = 0) ∨ (i = 1 ∧ j = 0) ∨ (i = -1 ∧ j = 0) ∨ (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = -1) := by
  obtain ⟨p1, p2, p3, p4⟩ := native_bounds hd hp
  obtain ⟨q1, q2, q3, q4⟩ := native_bounds hd hq
  rw [hpq] at q1 q2 q3 q4
  simp only [shiftP] at q1 q2 q3 q4
  obtain ⟨X, hX⟩ : ∃ X, X = i * d + j * (1 - d) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = i + j * (d + 1) := ⟨_, rfl⟩
  have hX1 : X ≤ 2 * d - 2 := by linarith
  have hX2 : 2 - 2 * d ≤ X := by linarith
  have hY1 : Y ≤ d + 1 := by linarith
  have hY2 : -(d + 1) ≤ Y := by linarith
  -- j (d² + 2d − 1) = d Y − X
  have hid : j * (d * d + 2 * d - 1) = d * Y - X := by rw [hX, hY]; ring
  have hj1 : j ≤ 1 := by
    by_contra hc
    have h2 : (2:ℤ) ≤ j := by omega
    nlinarith
  have hj2 : -1 ≤ j := by
    by_contra hc
    have h2 : j ≤ -2 := by omega
    nlinarith
  interval_cases j
  · -- j = -1: Y = i − (d+1) ≥ −(d+1) gives i ≥ 0; X = i d + d − 1 ≤ 2d − 2 gives i ≤ 0
    have hi2 : 0 ≤ i := by linarith
    have hi1 : i ≤ 0 := by
      by_contra hc
      have h2 : (1:ℤ) ≤ i := by omega
      nlinarith [mul_le_mul_of_nonneg_right h2 (by omega : (0:ℤ) ≤ d)]
    have : i = 0 := by omega
    subst this; simp
  · -- j = 0: X = i d ∈ [2 − 2d, 2d − 2] gives i ∈ {−1, 0, 1}
    have hi1 : i ≤ 1 := by
      by_contra hc
      have h2 : (2:ℤ) ≤ i := by omega
      nlinarith [mul_le_mul_of_nonneg_right h2 (by omega : (0:ℤ) ≤ d)]
    have hi2 : -1 ≤ i := by
      by_contra hc
      have h2 : i ≤ -2 := by omega
      nlinarith [mul_le_mul_of_nonneg_right h2 (by omega : (0:ℤ) ≤ d)]
    interval_cases i <;> simp
  · -- j = 1: Y = i + d + 1 ≤ d + 1 gives i ≤ 0; X = i d + 1 − d ≥ 2 − 2d gives i ≥ 0
    have hi1 : i ≤ 0 := by linarith
    have hi2 : 0 ≤ i := by
      by_contra hc
      have h2 : i ≤ -1 := by omega
      nlinarith [mul_le_mul_of_nonneg_right (by omega : (0:ℤ) ≤ -i) (by omega : (0:ℤ) ≤ d)]
    have : i = 0 := by omega
    subst this; simp

/-! ### The offset algebra of `shiftP` -/

theorem shiftP_add (d : ℤ) (p : Pt) (i j k l : ℤ) : shiftP d (shiftP d p i j) k l = shiftP d p (i + k) (j + l) := by
  simp only [shiftP]
  ext <;> simp only <;> ring

theorem shiftP_zero (d : ℤ) (p : Pt) : shiftP d p 0 0 = p := by
  simp only [shiftP]
  ext <;> simp

theorem shiftP_eq_add (d : ℤ) (p : Pt) (i j : ℤ) : shiftP d p i j = p + shiftP d 0 i j := by
  simp only [shiftP]
  ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero] <;> ring

/-- The coordinate sum of a shifted point, for `d = 2m + 1`. -/
theorem shiftP_sum {d m : ℤ} (hd : d = 2 * m + 1) (p : Pt) (i j : ℤ) :
    (shiftP d p i j).1 + (shiftP d p i j).2 = (p.1 + p.2) + 2 * (i * m + i + j) := by
  subst hd
  simp only [shiftP]
  ring

theorem evenSite_shiftP {d m : ℤ} (hd : d = 2 * m + 1) (p : Pt) (i j : ℤ) :
    EvenSite (shiftP d p i j) ↔ EvenSite p := by
  unfold EvenSite
  rw [shiftP_sum hd]
  simp [Int.add_mul_emod_self_left]

theorem incomingNeg_shiftP {d m : ℤ} (hd : d = 2 * m + 1) (p : Pt) (i j : ℤ) :
    incomingNeg (shiftP d p i j) = shiftP d (incomingNeg p) i j := by
  have ht : (shiftP d 0 i j).1 + (shiftP d 0 i j).2 = 0 + 0 + 2 * (i * m + i + j) := shiftP_sum hd 0 i j
  have hte : ((shiftP d 0 i j).1 + (shiftP d 0 i j).2) % 2 = 0 := by
    rw [ht]; simp [Int.mul_emod_right]
  rw [shiftP_eq_add d p i j, shiftP_eq_add d (incomingNeg p) i j]
  exact incomingNeg_add hte

theorem incomingPos_shiftP {d m : ℤ} (hd : d = 2 * m + 1) (p : Pt) (i j : ℤ) :
    incomingPos (shiftP d p i j) = shiftP d (incomingPos p) i j := by
  have ht : (shiftP d 0 i j).1 + (shiftP d 0 i j).2 = 0 + 0 + 2 * (i * m + i + j) := shiftP_sum hd 0 i j
  have hte : ((shiftP d 0 i j).1 + (shiftP d 0 i j).2) % 2 = 0 := by
    rw [ht]; simp [Int.mul_emod_right]
  rw [shiftP_eq_add d p i j, shiftP_eq_add d (incomingPos p) i j]
  exact incomingPos_add hte

/-- The three cases of a native point: the box, and the two corners. -/
theorem native_cases {d : ℤ} {p : Pt} (hp : NativeP d p) :
    (2 - d ≤ p.1 ∧ p.1 ≤ d ∧ 0 ≤ p.2 ∧ p.2 ≤ d + 1 ∧ 1 ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ d + 2) ∨
      (p.1 = 0 ∧ p.2 = 0) ∨ (p.1 = 2 ∧ p.2 = d + 1) := by
  rcases hp with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (by simp [h]))
  · exact Or.inr (Or.inr (by simp [h]))

/-! ### Lemma B: an even native pair with a nonzero offset contains a free point -/

theorem even_pair_free {d : ℤ} (hd : 3 ≤ d) (hodd : d % 2 = 1) {p : Pt} {i j : ℤ} (hp : NativeP d p)
    (hq : NativeP d (shiftP d p i j)) (hev : EvenSite p)
    (hoff : (i = 1 ∧ j = 0) ∨ (i = -1 ∧ j = 0) ∨ (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = -1)) :
    IsFreeP d p ∨ IsFreeP d (shiftP d p i j) := by
  have hp' := native_cases hp
  have hq' := native_cases hq
  unfold EvenSite at hev
  unfold IsFreeP IsHc IsVc
  simp only [shiftP, Prod.ext_iff] at hq' ⊢
  rcases hoff with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases hp' with h1 | h1 | h1 <;> rcases hq' with h2 | h2 | h2 <;> omega

/-! ### Lemma C: the free aliases of two native points of one class coincide -/

theorem freeAliasAt_free {d : ℤ} {p : Pt} (hp : NativeP d p) (hf : IsFreeP d p) : FreeAliasAt d p p :=
  ⟨0, 0, by unfold IsAlias; omega, (shiftP_zero d p).symm, hp, hf⟩

theorem freeAlias_iff {d : ℤ} (hd : 3 ≤ d) {p p' : Pt} {i j : ℤ} (hp : NativeP d p) (hp' : NativeP d p')
    (hpp : p' = shiftP d p i j) (hoff : (i = 0 ∧ j = 0) ∨ (i = 1 ∧ j = 0) ∨ (i = -1 ∧ j = 0) ∨ (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = -1))
    (q : Pt) : FreeAliasAt d p q ↔ FreeAliasAt d p' q := by
  constructor
  · rintro ⟨a, b, hab, hq, hnq, hfq⟩
    -- q is native and a translate of p' by (a − i, b − j)
    have hqp' : q = shiftP d p' (a - i) (b - j) := by
      rw [hq, hpp, shiftP_add, show i + (a - i) = a by ring, show j + (b - j) = b by ring]
    have hoff' := native_offset hd hp' hnq hqp'
    have hab' : IsAlias (a - i) (b - j) := by
      unfold IsAlias
      rcases hoff' with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> unfold IsAlias at hab <;> omega
    exact ⟨a - i, b - j, hab', hqp', hnq, hfq⟩
  · rintro ⟨a, b, hab, hq, hnq, hfq⟩
    have hqp : q = shiftP d p (i + a) (j + b) := by
      rw [hq, hpp, shiftP_add]
    have hoff' := native_offset hd hp hnq hqp
    have hab' : IsAlias (i + a) (j + b) := by
      unfold IsAlias
      rcases hoff with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> unfold IsAlias at hab <;> omega
    exact ⟨i + a, j + b, hab', hqp, hnq, hfq⟩

/-! ### Lemma D: the rule of a native centre is invariant under the offsets -/

theorem shiftP_inj (d : ℤ) (u v : Pt) (i j : ℤ) : shiftP d u i j = shiftP d v i j ↔ u = v := by
  constructor
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [shiftP] at h1 h2
    exact Prod.ext (by linarith) (by linarith)
  · intro h
    rw [h]

theorem shiftP_add_vec (d : ℤ) (p v : Pt) (i j : ℤ) : shiftP d (p + v) i j = shiftP d p i j + v := by
  simp only [shiftP]
  ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring

theorem shiftP_sub (d : ℤ) (u p : Pt) (i j : ℤ) : shiftP d u i j - shiftP d p i j = u - p := by
  simp only [shiftP]
  ext <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> ring

/-- The clause `EvenSite c ∧ ¬∃ free alias ∧ x-rule` is false at a centre with a free alias. -/
theorem retNat_clause_free {d : ℤ} {c : Pt} (hc : ∃ q, FreeAliasAt d c q) (i : Pt) :
    ¬ (EvenSite c ∧ ¬ (∃ q, FreeAliasAt d c q) ∧
        ((c.1 ≤ 0 ∧ i = incomingNeg c) ∨ (2 ≤ c.1 ∧ i = incomingPos c))) := by
  rintro ⟨-, hn, -⟩
  exact hn hc

/-- **Lemma D.** For two native points differing by an offset, the rule is invariant: the input `u` at `p` is retained
iff `shiftP u i j` is retained at `shiftP p i j`. -/
theorem retNat_offset {d m : ℤ} (hd : 3 ≤ d) (hm : d = 2 * m + 1) (η : ℤ) (B : Prop) {p : Pt} {i j : ℤ}
    (hp : NativeP d p) (hq : NativeP d (shiftP d p i j))
    (hoff : (i = 0 ∧ j = 0) ∨ (i = 1 ∧ j = 0) ∨ (i = -1 ∧ j = 0) ∨ (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = -1))
    (u : Pt) : RetNat d η B p u ↔ RetNat d η B (shiftP d p i j) (shiftP d u i j) := by
  by_cases h0 : i = 0 ∧ j = 0
  · obtain ⟨rfl, rfl⟩ := h0
    simp only [shiftP_zero]
  -- the offset is nonzero: the free-alias clause is decided the same way at both centres
  have hoff' : (i = 1 ∧ j = 0) ∨ (i = -1 ∧ j = 0) ∨ (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = -1) := by
    rcases hoff with h | h | h | h | h
    · exact absurd h h0
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  have hIN : (u = incomingNeg p ∨ u = incomingPos p) ↔
      (shiftP d u i j = incomingNeg (shiftP d p i j) ∨ shiftP d u i j = incomingPos (shiftP d p i j)) := by
    rw [incomingNeg_shiftP hm, incomingPos_shiftP hm, shiftP_inj, shiftP_inj]
  -- the clause with a free alias: the aliases of the two centres are the same
  have hFA : ∀ q, FreeAliasAt d p q ↔ FreeAliasAt d (shiftP d p i j) q := fun q =>
    freeAlias_iff hd hp hq rfl (by
      rcases hoff' with h | h | h | h <;> simp [h.1, h.2]) q
  have hodd : d % 2 = 1 := by omega
  have hEx : EvenSite p → ∃ q, FreeAliasAt d p q := fun hev => by
    rcases even_pair_free hd hodd hp hq hev hoff' with hf | hf
    · exact ⟨p, freeAliasAt_free hp hf⟩
    · exact ⟨shiftP d p i j, (hFA _).mpr (freeAliasAt_free hq hf)⟩
  -- the nonfree x-rule clause is false at both centres
  have hnC2 : ∀ X : Prop, ¬ (EvenSite p ∧ ¬ (∃ q, FreeAliasAt d p q) ∧ X) :=
    fun X h => h.2.1 (hEx h.1)
  have hnC2' : ∀ X : Prop, ¬ (EvenSite (shiftP d p i j) ∧ ¬ (∃ q, FreeAliasAt d (shiftP d p i j) q) ∧ X) := by
    intro X h
    have hev : EvenSite p := (evenSite_shiftP hm p i j).mp h.1
    obtain ⟨q, hq'⟩ := hEx hev
    exact h.2.1 ⟨q, (hFA q).mp hq'⟩
  unfold RetNat
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨hIN.mp h1, ?_⟩
    rcases h2 with hB | hC2 | ⟨q, hq1, hq2⟩
    · exact Or.inl hB
    · exact (hnC2 _ hC2).elim
    · refine Or.inr (Or.inr ⟨q, (hFA q).mp hq1, ?_⟩)
      rw [shiftP_sub]
      exact hq2
  · rintro ⟨h1, h2⟩
    refine ⟨hIN.mpr h1, ?_⟩
    rcases h2 with hB | hC2 | ⟨q, hq1, hq2⟩
    · exact Or.inl hB
    · exact (hnC2' _ hC2).elim
    · refine Or.inr (Or.inr ⟨q, (hFA q).mpr hq1, ?_⟩)
      rw [← shiftP_sub d u p i j]
      exact hq2

/-! ### Lemma E: `ePolicy` is invariant under the deck (the independence of the native representative) -/

/-- **`ePolicy_span` (the independence `ePolicy_indep`).** Under a `Λ`-invariant Laplacian, the reciprocal policy is
invariant under every deck vector `s = combine a b`: `ePolicy (c + s) (u + s) ↔ ePolicy c u`. -/
theorem ePolicy_span {d m : ℤ} (hd : 3 ≤ d) (hm : d = 2 * m + 1) (hV : BaseMask.stairEven.Valid d) (η : ℤ)
    (lap : Pt → ℤ) (a b : ℤ) (c u : Pt)
    (hL : lap (c + (Fraction.mk 1 d).modifiedDeck.combine a b) = lap c) :
    ePolicy d η lap (c + (Fraction.mk 1 d).modifiedDeck.combine a b) (u + (Fraction.mk 1 d).modifiedDeck.combine a b) ↔
      ePolicy d η lap c u := by
  have hodd : d % 2 = 1 := by omega
  obtain ⟨hr, i, j, hcr⟩ := nativeRep_spec hV c
  obtain ⟨hr', i', j', hcr'⟩ := nativeRep_spec hV (c + (Fraction.mk 1 d).modifiedDeck.combine a b)
  -- the two native representatives differ by the offset (i + a − i', j + b − j')
  have hdiff : nativeRep d (c + (Fraction.mk 1 d).modifiedDeck.combine a b) =
      shiftP d (nativeRep d c) (i + a - i') (j + b - j') := by
    generalize nativeRep d (c + (Fraction.mk 1 d).modifiedDeck.combine a b) = r' at hcr' ⊢
    generalize nativeRep d c = r at hcr ⊢
    have hc1 := congrArg Prod.fst hcr
    have hc2 := congrArg Prod.snd hcr
    have e1 := congrArg Prod.fst hcr'
    have e2 := congrArg Prod.snd hcr'
    simp only [combine_mk_one hodd, Prod.fst_add, Prod.snd_add] at hc1 hc2 e1 e2
    simp only [shiftP]
    exact Prod.ext (by linear_combination (-1 : ℤ) * e1 + hc1) (by linear_combination (-1 : ℤ) * e2 + hc2)
  have hq2 : NativeP d (shiftP d (nativeRep d c) (i + a - i') (j + b - j')) := by
    rw [← hdiff]
    exact hr'
  have hoff := native_offset hd hr hr' hdiff
  unfold ePolicy
  rw [hL]
  have e1 : u + (Fraction.mk 1 d).modifiedDeck.combine a b -
      (c + (Fraction.mk 1 d).modifiedDeck.combine a b) = u - c := by abel
  rw [e1, hdiff]
  have key := retNat_offset hd hm η (lap c = -1) hr hq2 hoff (nativeRep d c + (u - c))
  rw [key, shiftP_add_vec]

end FLatticePaper.EPolicyIndep
